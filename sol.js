/*
 * Stash: shared Solana helpers.
 * No dependencies. Runs in modern browsers and in Node 20+ (uses WebCrypto).
 *
 * Covers: base58, sha256 PDAs, the ed25519 curve check, v0 transaction
 * compile/parse (with address lookup tables), Ed25519 signing, pump.fun
 * instruction builders (create_v2, buy_exact_quote_in_v2, fee sharing,
 * fee distribution), account decoders, and the Stash launch memo.
 *
 * Instruction layouts follow pump-fun/pump-public-docs (idl/pump.json,
 * idl/pump_fees.json, idl/pump_amm.json).
 */
(function (root, factory) {
  var api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  else root.StashSol = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  /* ------------------------------------------------------------------ bytes */

  const te = new TextEncoder();
  const td = new TextDecoder();

  function concat() {
    let len = 0;
    for (let i = 0; i < arguments.length; i++) len += arguments[i].length;
    const out = new Uint8Array(len);
    let o = 0;
    for (let i = 0; i < arguments.length; i++) { out.set(arguments[i], o); o += arguments[i].length; }
    return out;
  }
  function u8(n) { return Uint8Array.of(n & 0xff); }
  function u16(n) { const b = new Uint8Array(2); new DataView(b.buffer).setUint16(0, n, true); return b; }
  function u32(n) { const b = new Uint8Array(4); new DataView(b.buffer).setUint32(0, n >>> 0, true); return b; }
  function u64(n) {
    const v = BigInt(n);
    if (v < 0n || v > 0xffffffffffffffffn) throw new Error('u64 out of range');
    const b = new Uint8Array(8); new DataView(b.buffer).setBigUint64(0, v, true); return b;
  }
  function borshString(s) { const b = te.encode(s); return concat(u32(b.length), b); }
  function dv(b) { return new DataView(b.buffer, b.byteOffset, b.byteLength); }
  function readU16(b, o) { return dv(b).getUint16(o, true); }
  function readU32(b, o) { return dv(b).getUint32(o, true); }
  function readU64(b, o) { return dv(b).getBigUint64(o, true); }
  function bytesEqual(a, b) {
    if (!a || !b || a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
    return true;
  }
  function toHex(b) { let s = ''; for (let i = 0; i < b.length; i++) s += b[i].toString(16).padStart(2, '0'); return s; }

  function b64encode(bytes) {
    let s = '';
    for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
    return btoa(s);
  }
  function b64decode(str) {
    const s = atob(str);
    const out = new Uint8Array(s.length);
    for (let i = 0; i < s.length; i++) out[i] = s.charCodeAt(i);
    return out;
  }

  /* ----------------------------------------------------------------- base58 */

  const ALPHABET = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  const B58MAP = new Int16Array(128).fill(-1);
  for (let i = 0; i < ALPHABET.length; i++) B58MAP[ALPHABET.charCodeAt(i)] = i;

  function b58encode(bytes) {
    let zeros = 0;
    while (zeros < bytes.length && bytes[zeros] === 0) zeros++;
    const digits = [];
    for (let i = zeros; i < bytes.length; i++) {
      let carry = bytes[i];
      for (let j = 0; j < digits.length; j++) {
        carry += digits[j] << 8;
        digits[j] = carry % 58;
        carry = (carry / 58) | 0;
      }
      while (carry > 0) { digits.push(carry % 58); carry = (carry / 58) | 0; }
    }
    let out = '';
    for (let i = 0; i < zeros; i++) out += '1';
    for (let k = digits.length - 1; k >= 0; k--) out += ALPHABET[digits[k]];
    return out;
  }

  function b58decode(s) {
    if (typeof s !== 'string') throw new Error('base58: expected a string');
    let zeros = 0;
    while (zeros < s.length && s[zeros] === '1') zeros++;
    const bytes = [];
    for (let i = zeros; i < s.length; i++) {
      const c = s.charCodeAt(i);
      const v = c < 128 ? B58MAP[c] : -1;
      if (v < 0) throw new Error('base58: invalid character');
      let carry = v;
      for (let j = 0; j < bytes.length; j++) {
        carry += bytes[j] * 58;
        bytes[j] = carry & 0xff;
        carry >>= 8;
      }
      while (carry > 0) { bytes.push(carry & 0xff); carry >>= 8; }
    }
    const out = new Uint8Array(zeros + bytes.length);
    for (let k = 0; k < bytes.length; k++) out[out.length - 1 - k] = bytes[k];
    return out;
  }

  /** Normalise a public key (base58 string or 32 bytes) to 32 bytes. */
  function pk(x) {
    if (x instanceof Uint8Array) {
      if (x.length !== 32) throw new Error('public key must be 32 bytes');
      return x;
    }
    if (typeof x === 'string') {
      const b = b58decode(x);
      if (b.length !== 32) throw new Error('not a valid address: ' + x);
      return b;
    }
    throw new Error('public key expected');
  }
  function isAddress(s) {
    if (typeof s !== 'string' || s.length < 32 || s.length > 44) return false;
    try { return b58decode(s).length === 32; } catch (e) { return false; }
  }
  function addr(x) { return typeof x === 'string' ? (pk(x), x) : b58encode(pk(x)); }

  /* -------------------------------------------------------- sha256 / curve */

  function subtle() {
    const c = globalThis.crypto;
    if (!c || !c.subtle) throw new Error('WebCrypto is not available in this browser');
    return c.subtle;
  }
  async function sha256(bytes) { return new Uint8Array(await subtle().digest('SHA-256', bytes)); }

  const P = (1n << 255n) - 19n;
  function modp(a) { const r = a % P; return r >= 0n ? r : r + P; }
  function powp(b, e) {
    let r = 1n; b = modp(b);
    while (e > 0n) { if (e & 1n) r = (r * b) % P; b = (b * b) % P; e >>= 1n; }
    return r;
  }
  const D = modp(-121665n * powp(121666n, P - 2n));
  const HALF = (P - 1n) / 2n;

  /**
   * True when 32 bytes decode to a point on ed25519, matching
   * curve25519-dalek's CompressedEdwardsY::decompress().is_some(),
   * which Solana uses to reject PDA candidates.
   */
  function isOnCurve(bytes) {
    let y = 0n;
    for (let i = 31; i >= 0; i--) y = (y << 8n) | BigInt(i === 31 ? bytes[i] & 0x7f : bytes[i]);
    y = modp(y);
    const y2 = (y * y) % P;
    const u = modp(y2 - 1n);
    const v = modp(D * y2 + 1n);
    if (u === 0n) return true;
    const w = (u * powp(v, P - 2n)) % P;
    return powp(w, HALF) === 1n;
  }

  /* ------------------------------------------------------------------- PDAs */

  const PDA_MARKER = te.encode('ProgramDerivedAddress');
  const pdaCache = new Map();

  function seedBytes(s) {
    if (typeof s === 'string') { const b = te.encode(s); if (b.length > 32) throw new Error('seed too long'); return b; }
    if (s instanceof Uint8Array) { if (s.length > 32) throw new Error('seed too long'); return s; }
    throw new Error('seed must be a string or bytes');
  }

  async function createPda(seeds, programId) {
    const h = await sha256(concat.apply(null, seeds.map(seedBytes).concat([pk(programId), PDA_MARKER])));
    if (isOnCurve(h)) throw new Error('seeds produce an on-curve address');
    return h;
  }

  /** Returns [address bytes, bump]. */
  async function findPda(seeds, programId) {
    const s = seeds.map(seedBytes);
    const prog = pk(programId);
    const cacheKey = toHex(prog) + ':' + s.map(toHex).join(':');
    const hit = pdaCache.get(cacheKey);
    if (hit) return hit;
    for (let bump = 255; bump >= 0; bump--) {
      const h = await sha256(concat.apply(null, s.concat([Uint8Array.of(bump), prog, PDA_MARKER])));
      if (!isOnCurve(h)) {
        const res = [h, bump];
        if (pdaCache.size > 5000) pdaCache.clear();
        pdaCache.set(cacheKey, res);
        return res;
      }
    }
    throw new Error('no viable PDA bump');
  }
  async function pda(seeds, programId) { return (await findPda(seeds, programId))[0]; }

  /* -------------------------------------------------------------- programs */

  const PROGRAMS = {
    SYSTEM: '11111111111111111111111111111111',
    TOKEN: 'TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA',
    TOKEN_2022: 'TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb',
    ATA: 'ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL',
    COMPUTE_BUDGET: 'ComputeBudget111111111111111111111111111111',
    MEMO: 'MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr',
    ALT: 'AddressLookupTab1e1111111111111111111111111',
    WSOL: 'So11111111111111111111111111111111111111112',
    PUMP: '6EF8rrecthR5Dkzon8Nwu78hRvfCKubJ14M5uBEwF6P',
    PUMP_FEES: 'pfeeUxB6jkeY1Hxd7CsFCAjcbHA9rWtchMGdZ6VojVZ',
    PUMP_AMM: 'pAMMBay6oceH9fJKBRHGP5D4bD4sWpmSwMn52FMfXEA',
    MAYHEM: 'MAyhSmzXzV1pTf7LsNkrNwkWKTo4ougAJ1PPg47MD4e'
  };

  /** pump.fun FEE_RECIPIENTS.md: normal fee recipients (non-mayhem coins). */
  const FEE_RECIPIENTS = [
    '62qc2CNXwrYqQScmEdiZFFAnJR262PxWEuNQtxfafNgV', '7VtfL8fvgNfhz17qKRMjzQEXgbdpnHHHQRh54R9jP2RJ',
    '7hTckgnGnLQR6sdH7YkqFTAA7VwTfYFaZ6EhEsU3saCX', '9rPYyANsfQZw3DnDmKE3YCQF5E8oD89UXoHn9JFEhJUz',
    'AVmoTthdrX6tKt4nDjco2D775W2YK3sDhxPcMmzUAmTY', 'CebN5WGQ4jvEPvsVU4EoHEpgzq1VV7AbicfhtW4xC9iM',
    'FWsW1xNtWscwNmKv6wVsU1iTzRN6wmmk3MjxRP5tT7hz', 'G5UZAVbAf46s7cKWoyKu8kYTip9DGTpbLZ2qa9Aq69dP'
  ];
  /** pump.fun FEE_RECIPIENTS.md: buyback fee recipients (all coins). */
  const BUYBACK_FEE_RECIPIENTS = [
    '5YxQFdt3Tr9zJLvkFccqXVUwhdTWJQc1fFg2YPbxvxeD', '9M4giFFMxmFGXtc3feFzRai56WbBqehoSeRE5GK7gf7',
    'GXPFM2caqTtQYC2cJ5yJRi9VDkpsYZXzYdwYpGnLmtDL', '3BpXnfJaUTiwXnJNe7Ej1rcbzqTTQUvLShZaWazebsVR',
    '5cjcW9wExnJJiqgLjq7DEG75Pm6JBgE1hNv4B2vHXUW6', 'EHAAiTxcdDwQ3U4bU6YcMsQGaekdzLS3B5SmYo46kJtL',
    '5eHhjP8JaYkz83CWwvGU2uMUXefd3AazWGx4gpcuEEYD', 'A7hAgCzFw14fejgCp387JUJRMNyz4j89JKnhtKU8piqW'
  ];

  /** Anchor instruction discriminators, from the published IDLs. */
  const DISC = {
    create_v2: [214, 144, 76, 236, 95, 139, 49, 180],
    buy_exact_quote_in_v2: [194, 171, 28, 70, 104, 77, 91, 47],
    buy_v2: [184, 23, 238, 97, 103, 197, 211, 61],
    distribute_creator_fees_v2: [255, 203, 19, 79, 244, 68, 8, 159],
    create_fee_sharing_config: [195, 78, 86, 76, 111, 52, 251, 213],
    update_fee_shares_v2: [111, 251, 49, 6, 78, 78, 106, 18],
    transfer_creator_fees_to_pump_v2: [1, 33, 78, 185, 33, 67, 44, 92]
  };
  /** Anchor account discriminators. */
  const ACCOUNT_DISC = {
    BondingCurve: [23, 183, 248, 55, 96, 216, 172, 96],
    SharingConfig: [216, 74, 9, 0, 56, 140, 93, 75],
    Pool: [241, 154, 109, 4, 17, 177, 109, 188],
    Global: [167, 232, 232, 177, 200, 108, 114, 127]
  };

  /** Anchor's sighash: first 8 bytes of sha256("global:<name>"). */
  async function anchorDisc(name) { return (await sha256(te.encode('global:' + name))).subarray(0, 8); }

  /* ------------------------------------------------------------- PDA helpers */

  const P_ = PROGRAMS;
  const derive = {
    global: () => pda(['global'], P_.PUMP),
    mintAuthority: () => pda(['mint-authority'], P_.PUMP),
    pumpEventAuthority: () => pda(['__event_authority'], P_.PUMP),
    feesEventAuthority: () => pda(['__event_authority'], P_.PUMP_FEES),
    ammEventAuthority: () => pda(['__event_authority'], P_.PUMP_AMM),
    bondingCurve: (mint) => pda(['bonding-curve', pk(mint)], P_.PUMP),
    creatorVault: (creator) => pda(['creator-vault', pk(creator)], P_.PUMP),
    ammCreatorVault: (creator) => pda(['creator_vault', pk(creator)], P_.PUMP_AMM),
    sharingConfig: (mint) => pda(['sharing-config', pk(mint)], P_.PUMP_FEES),
    globalVolumeAccumulator: () => pda(['global_volume_accumulator'], P_.PUMP),
    userVolumeAccumulator: (user) => pda(['user_volume_accumulator', pk(user)], P_.PUMP),
    feeConfig: () => pda(['fee_config', pk(P_.PUMP)], P_.PUMP_FEES),
    poolAuthority: (mint) => pda(['pool-authority', pk(mint)], P_.PUMP),
    mayhemGlobalParams: () => pda(['global-params'], P_.MAYHEM),
    mayhemSolVault: () => pda(['sol-vault'], P_.MAYHEM),
    mayhemState: (mint) => pda(['mayhem-state', pk(mint)], P_.MAYHEM),
    async canonicalPool(mint) {
      const creator = await derive.poolAuthority(mint);
      return pda(['pool', u16(0), creator, pk(mint), pk(P_.WSOL)], P_.PUMP_AMM);
    },
    ata: (owner, mint, tokenProgram) => pda([pk(owner), pk(tokenProgram), pk(mint)], P_.ATA)
  };

  /* ----------------------------------------------------------- instructions */

  function meta(pubkey, isSigner, isWritable) { return { pubkey: pk(pubkey), isSigner: !!isSigner, isWritable: !!isWritable }; }
  const R = (k) => meta(k, false, false);
  const W = (k) => meta(k, false, true);
  const WS = (k) => meta(k, true, true);
  function instruction(programId, keys, data) { return { programId: pk(programId), keys: keys, data: data || new Uint8Array(0) }; }

  const ix = {
    computeUnitLimit(units) { return instruction(P_.COMPUTE_BUDGET, [], concat(u8(2), u32(units))); },
    computeUnitPrice(microLamports) { return instruction(P_.COMPUTE_BUDGET, [], concat(u8(3), u64(microLamports))); },
    memo(text) { return instruction(P_.MEMO, [], te.encode(text)); },
    transfer(from, to, lamports) { return instruction(P_.SYSTEM, [WS(from), W(to)], concat(u32(2), u64(lamports))); },

    async createAtaIdempotent({ payer, owner, mint, tokenProgram }) {
      const ata = await derive.ata(owner, mint, tokenProgram);
      return instruction(P_.ATA, [WS(payer), W(ata), R(owner), R(mint), R(P_.SYSTEM), R(tokenProgram)], u8(1));
    },

    /** SPL / Token-2022 BurnChecked. */
    burnChecked({ account, mint, owner, amount, decimals, tokenProgram }) {
      return instruction(tokenProgram, [W(account), W(mint), meta(owner, true, false)], concat(u8(15), u64(amount), u8(decimals)));
    },

    /** pump create_v2, SOL quote, mayhem off, cashback off, standard fee schedule. */
    async createV2({ mint, user, creator, name, symbol, uri }) {
      if (te.encode(name).length > 32) throw new Error('Name is longer than 32 bytes');
      if (te.encode(symbol).length > 13) throw new Error('Ticker is longer than 13 bytes');
      if (te.encode(uri).length > 200) throw new Error('Metadata URI is longer than 200 bytes');
      const bc = await derive.bondingCurve(mint);
      const solVault = await derive.mayhemSolVault();
      const data = concat(
        Uint8Array.from(DISC.create_v2), borshString(name), borshString(symbol), borshString(uri),
        pk(creator || user),
        u8(0),          // is_mayhem_mode
        u8(0),          // is_cashback_enabled: OptionBool [false]
        u64(0)          // creator_fee_bps: OptionU64 0 (standard schedule)
      );
      return instruction(P_.PUMP, [
        meta(mint, true, true),
        R(await derive.mintAuthority()),
        W(bc),
        W(await derive.ata(bc, mint, P_.TOKEN_2022)),
        R(await derive.global()),
        WS(user),
        R(P_.SYSTEM),
        R(P_.TOKEN_2022),
        R(P_.ATA),
        W(P_.MAYHEM),
        R(await derive.mayhemGlobalParams()),
        W(solVault),
        W(await derive.mayhemState(mint)),
        W(await derive.ata(solVault, mint, P_.TOKEN_2022)),
        R(await derive.pumpEventAuthority()),
        R(P_.PUMP)
      ], data);
    },

    /**
     * pump buy_exact_quote_in_v2 for a SOL-quoted coin.
     * curveCreator must be bonding_curve.creator at the time the buy executes.
     */
    async buyExactQuoteInV2({ mint, user, curveCreator, lamportsIn, minTokensOut, baseTokenProgram, feeRecipient, buybackFeeRecipient }) {
      const baseProg = baseTokenProgram || P_.TOKEN_2022;
      const bc = await derive.bondingCurve(mint);
      const creatorVault = await derive.creatorVault(curveCreator);
      const uva = await derive.userVolumeAccumulator(user);
      const fr = feeRecipient || FEE_RECIPIENTS[0];
      const bfr = buybackFeeRecipient || BUYBACK_FEE_RECIPIENTS[0];
      const data = concat(Uint8Array.from(DISC.buy_exact_quote_in_v2), u64(lamportsIn), u64(minTokensOut));
      return instruction(P_.PUMP, [
        R(await derive.global()),
        R(mint),
        R(P_.WSOL),
        R(baseProg),
        R(P_.TOKEN),
        R(P_.ATA),
        W(fr),
        W(await derive.ata(fr, P_.WSOL, P_.TOKEN)),
        W(bfr),
        W(await derive.ata(bfr, P_.WSOL, P_.TOKEN)),
        W(bc),
        W(await derive.ata(bc, mint, baseProg)),
        W(await derive.ata(bc, P_.WSOL, P_.TOKEN)),
        WS(user),
        W(await derive.ata(user, mint, baseProg)),
        W(await derive.ata(user, P_.WSOL, P_.TOKEN)),
        W(creatorVault),
        W(await derive.ata(creatorVault, P_.WSOL, P_.TOKEN)),
        R(await derive.sharingConfig(mint)),
        R(await derive.globalVolumeAccumulator()),
        W(uva),
        W(await derive.ata(uva, P_.WSOL, P_.TOKEN)),
        R(await derive.feeConfig()),
        R(P_.PUMP_FEES),
        R(P_.SYSTEM),
        R(await derive.pumpEventAuthority()),
        R(P_.PUMP)
      ], data);
    },

    /** pump_fees create_fee_sharing_config. Pass graduated pool only for migrated coins. */
    async createFeeSharingConfig({ payer, mint, pool }) {
      const keys = [
        R(await derive.feesEventAuthority()),
        R(P_.PUMP_FEES),
        WS(payer),
        R(await derive.global()),
        R(mint),
        W(await derive.sharingConfig(mint)),
        R(P_.SYSTEM),
        W(await derive.bondingCurve(mint)),
        R(P_.PUMP),
        R(await derive.pumpEventAuthority())
      ];
      if (pool) keys.push(W(pool), R(P_.PUMP_AMM), R(await derive.ammEventAuthority()));
      return instruction(P_.PUMP_FEES, keys, Uint8Array.from(DISC.create_fee_sharing_config));
    },

    /**
     * pump_fees update_fee_shares_v2 (one-time; revokes the admin).
     * currentShareholders: the list stored in sharing_config right now, in order.
     */
    async updateFeeSharesV2({ authority, mint, currentShareholders, shareholders }) {
      if (!shareholders.length || shareholders.length > 10) throw new Error('1 to 10 shareholders');
      let total = 0;
      const parts = [Uint8Array.from(DISC.update_fee_shares_v2), u32(shareholders.length)];
      for (const s of shareholders) {
        if (!(s.bps > 0)) throw new Error('share must be positive');
        total += s.bps;
        parts.push(pk(s.address), u16(s.bps));
      }
      if (total !== 10000) throw new Error('shares must add up to 10,000 bps');
      const sc = await derive.sharingConfig(mint);
      const pumpVault = await derive.creatorVault(sc);
      const ammVault = await derive.ammCreatorVault(sc);
      const keys = [
        R(await derive.feesEventAuthority()),
        R(P_.PUMP_FEES),
        WS(authority),
        R(await derive.global()),
        R(mint),
        W(sc),
        R(await derive.bondingCurve(mint)),
        W(pumpVault),
        W(await derive.ata(pumpVault, P_.WSOL, P_.TOKEN)),
        R(P_.SYSTEM),
        R(P_.PUMP),
        R(await derive.pumpEventAuthority()),
        R(P_.PUMP_AMM),
        R(await derive.ammEventAuthority()),
        R(P_.WSOL),
        R(P_.TOKEN),
        R(P_.ATA),
        W(ammVault),
        W(await derive.ata(ammVault, P_.WSOL, P_.TOKEN))
      ];
      for (const c of currentShareholders) keys.push(W(c));
      return instruction(P_.PUMP_FEES, keys, concat.apply(null, parts));
    },

    /** pump_amm transfer_creator_fees_to_pump_v2 (permissionless sweep of AMM-side fees). */
    async transferCreatorFeesToPumpV2({ payer, coinCreator }) {
      const ammVault = await derive.ammCreatorVault(coinCreator);
      const pumpVault = await derive.creatorVault(coinCreator);
      return instruction(P_.PUMP_AMM, [
        WS(payer),
        R(P_.WSOL),
        R(P_.TOKEN),
        R(P_.SYSTEM),
        R(P_.ATA),
        R(coinCreator),
        W(ammVault),
        W(await derive.ata(ammVault, P_.WSOL, P_.TOKEN)),
        W(pumpVault),
        W(await derive.ata(pumpVault, P_.WSOL, P_.TOKEN)),
        R(await derive.ammEventAuthority()),
        R(P_.PUMP_AMM)
      ], Uint8Array.from(DISC.transfer_creator_fees_to_pump_v2));
    },

    /** pump distribute_creator_fees_v2 (permissionless). shareholders in sharing_config order. */
    async distributeCreatorFeesV2({ payer, mint, shareholders }) {
      const sc = await derive.sharingConfig(mint);
      const vault = await derive.creatorVault(sc);
      const keys = [
        WS(payer),
        R(mint),
        R(await derive.bondingCurve(mint)),
        R(sc),
        W(vault),
        R(P_.SYSTEM),
        R(await derive.pumpEventAuthority()),
        R(P_.PUMP),
        W(await derive.ata(vault, P_.WSOL, P_.TOKEN)),
        R(P_.WSOL),
        R(P_.TOKEN),
        R(P_.ATA)
      ];
      for (const s of shareholders) keys.push(W(s));
      return instruction(P_.PUMP, keys, concat(Uint8Array.from(DISC.distribute_creator_fees_v2), u8(0)));
    },

    /** Address lookup table program: CreateLookupTable. */
    async createLookupTable({ authority, payer, recentSlot }) {
      const [table, bump] = await findPda([pk(authority), u64(recentSlot)], P_.ALT);
      return {
        table: table,
        instruction: instruction(P_.ALT, [W(table), meta(authority, true, false), WS(payer), R(P_.SYSTEM)],
          concat(u32(0), u64(recentSlot), u8(bump)))
      };
    },
    /** Address lookup table program: ExtendLookupTable. */
    extendLookupTable({ table, authority, payer, addresses }) {
      const parts = [u32(2), u64(addresses.length)];
      for (const a of addresses) parts.push(pk(a));
      return instruction(P_.ALT, [W(table), meta(authority, true, false), WS(payer), R(P_.SYSTEM)], concat.apply(null, parts));
    }
  };

  /* ----------------------------------------------------- transaction format */

  function encodeLength(n) {
    const out = [];
    let rem = n;
    for (;;) {
      const elem = rem & 0x7f;
      rem >>= 7;
      if (rem === 0) { out.push(elem); break; }
      out.push(elem | 0x80);
    }
    return Uint8Array.from(out);
  }
  function decodeLength(b, o) {
    let len = 0, size = 0;
    for (;;) {
      if (o + size >= b.length) throw new Error('truncated length');
      const e = b[o + size];
      len |= (e & 0x7f) << (size * 7);
      size++;
      if ((e & 0x80) === 0) break;
      if (size > 3) throw new Error('bad length');
    }
    return [len, size];
  }

  const PACKET_SIZE = 1232;

  /**
   * Compile a v0 message.
   * lookupTables: [{ key, addresses: [pubkey...] }]. Signers and invoked
   * programs always stay static; other keys found in a table are loaded.
   */
  function compileV0(opts) {
    const payer = pk(opts.payer);
    const tables = (opts.lookupTables || []).map((t) => ({ key: pk(t.key), addresses: t.addresses.map(pk) }));
    const entries = new Map();
    const order = [];
    function add(key, signer, writable, invoked) {
      const id = b58encode(key);
      let e = entries.get(id);
      if (!e) { e = { id: id, key: key, signer: false, writable: false, invoked: false }; entries.set(id, e); order.push(e); }
      if (signer) e.signer = true;
      if (writable) e.writable = true;
      if (invoked) e.invoked = true;
      return e;
    }
    add(payer, true, true, false);
    for (const ins of opts.instructions) {
      add(ins.programId, false, false, true);
      for (const k of ins.keys) add(k.pubkey, k.isSigner, k.isWritable, false);
    }

    const where = new Map();
    tables.forEach((t, ti) => t.addresses.forEach((a, ai) => { const id = b58encode(a); if (!where.has(id)) where.set(id, { ti: ti, ai: ai }); }));

    const statics = [];
    const loadedW = tables.map(() => []);
    const loadedR = tables.map(() => []);
    for (const e of order) {
      const loc = where.get(e.id);
      if (loc && !e.signer && !e.invoked) (e.writable ? loadedW : loadedR)[loc.ti].push({ e: e, ai: loc.ai });
      else statics.push(e);
    }
    const payerId = b58encode(payer);
    const rank = (e) => (e.id === payerId ? 0 : e.signer ? (e.writable ? 1 : 2) : (e.writable ? 3 : 4));
    statics.sort((a, b) => rank(a) - rank(b));

    const index = new Map();
    statics.forEach((e, i) => index.set(e.id, i));
    let next = statics.length;
    loadedW.forEach((list) => list.forEach((x) => index.set(x.e.id, next++)));
    loadedR.forEach((list) => list.forEach((x) => index.set(x.e.id, next++)));
    if (next > 256) throw new Error('too many accounts for one transaction');

    const numSigners = statics.filter((e) => e.signer).length;
    const roSigned = statics.filter((e) => e.signer && !e.writable).length;
    const roUnsigned = statics.filter((e) => !e.signer && !e.writable).length;

    const parts = [Uint8Array.of(0x80, numSigners, roSigned, roUnsigned), encodeLength(statics.length)];
    statics.forEach((e) => parts.push(e.key));
    const bh = pk(opts.recentBlockhash);
    parts.push(bh);
    parts.push(encodeLength(opts.instructions.length));
    for (const ins of opts.instructions) {
      const accs = ins.keys.map((k) => index.get(b58encode(k.pubkey)));
      parts.push(u8(index.get(b58encode(ins.programId))), encodeLength(accs.length), Uint8Array.from(accs), encodeLength(ins.data.length), ins.data);
    }
    const used = [];
    tables.forEach((t, ti) => { if (loadedW[ti].length || loadedR[ti].length) used.push(ti); });
    parts.push(encodeLength(used.length));
    for (const ti of used) {
      parts.push(tables[ti].key,
        encodeLength(loadedW[ti].length), Uint8Array.from(loadedW[ti].map((x) => x.ai)),
        encodeLength(loadedR[ti].length), Uint8Array.from(loadedR[ti].map((x) => x.ai)));
    }
    const message = concat.apply(null, parts);
    return {
      message: message,
      numSigners: numSigners,
      signers: statics.slice(0, numSigners).map((e) => e.id),
      staticKeys: statics.map((e) => e.id),
      size: txSize(numSigners, message.length)
    };
  }

  function txSize(numSigners, messageLength) { return encodeLength(numSigners).length + numSigners * 64 + messageLength; }

  function serializeTx(message, signatures) {
    const parts = [encodeLength(signatures.length)];
    for (const s of signatures) parts.push(s || new Uint8Array(64));
    parts.push(message);
    return concat.apply(null, parts);
  }

  function parseMessage(m) {
    let o = 0;
    let version = 'legacy';
    if (m[0] & 0x80) { version = m[0] & 0x7f; o = 1; }
    const header = { numRequiredSignatures: m[o], numReadonlySigned: m[o + 1], numReadonlyUnsigned: m[o + 2] };
    o += 3;
    let n, s;
    [n, s] = decodeLength(m, o); o += s;
    const staticKeys = [];
    for (let i = 0; i < n; i++) { staticKeys.push(b58encode(m.subarray(o, o + 32))); o += 32; }
    const recentBlockhash = b58encode(m.subarray(o, o + 32)); o += 32;
    [n, s] = decodeLength(m, o); o += s;
    const instructions = [];
    for (let i = 0; i < n; i++) {
      const programIdIndex = m[o++];
      let k, ks; [k, ks] = decodeLength(m, o); o += ks;
      const accounts = Array.from(m.subarray(o, o + k)); o += k;
      let dl, dls; [dl, dls] = decodeLength(m, o); o += dls;
      const data = m.slice(o, o + dl); o += dl;
      instructions.push({ programIdIndex: programIdIndex, accounts: accounts, data: data });
    }
    const lookups = [];
    if (version !== 'legacy') {
      [n, s] = decodeLength(m, o); o += s;
      for (let i = 0; i < n; i++) {
        const key = b58encode(m.subarray(o, o + 32)); o += 32;
        let wl, wls; [wl, wls] = decodeLength(m, o); o += wls;
        const writableIndexes = Array.from(m.subarray(o, o + wl)); o += wl;
        let rl, rls; [rl, rls] = decodeLength(m, o); o += rls;
        const readonlyIndexes = Array.from(m.subarray(o, o + rl)); o += rl;
        lookups.push({ key: key, writableIndexes: writableIndexes, readonlyIndexes: readonlyIndexes });
      }
    }
    if (o !== m.length) throw new Error('trailing bytes in message');
    return { version: version, header: header, staticKeys: staticKeys, recentBlockhash: recentBlockhash, instructions: instructions, lookups: lookups };
  }

  function parseTx(bytes) {
    let n, s; [n, s] = decodeLength(bytes, 0);
    let o = s;
    const signatures = [];
    for (let i = 0; i < n; i++) { signatures.push(bytes.slice(o, o + 64)); o += 64; }
    const message = bytes.slice(o);
    return { signatures: signatures, message: message, parsed: parseMessage(message) };
  }

  /**
   * Resolve a parsed message's account list, given the lookup table
   * contents ({ [tableKey]: [addresses] }). Returns [{ key, signer, writable }].
   */
  function resolveAccounts(parsed, tableContents) {
    const h = parsed.header;
    const nStatic = parsed.staticKeys.length;
    const out = parsed.staticKeys.map((key, i) => ({
      key: key,
      signer: i < h.numRequiredSignatures,
      writable: i < h.numRequiredSignatures
        ? i < h.numRequiredSignatures - h.numReadonlySigned
        : i < nStatic - h.numReadonlyUnsigned
    }));
    const w = [], r = [];
    for (const l of parsed.lookups) {
      const list = (tableContents || {})[l.key];
      if (!list) throw new Error('lookup table contents missing: ' + l.key);
      l.writableIndexes.forEach((i) => w.push({ key: addr(list[i]), signer: false, writable: true }));
      l.readonlyIndexes.forEach((i) => r.push({ key: addr(list[i]), signer: false, writable: false }));
    }
    return out.concat(w, r);
  }

  /* ------------------------------------------------------------ signatures */

  const PKCS8_ED25519_PREFIX = Uint8Array.from([0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x04, 0x22, 0x04, 0x20]);

  async function generateKeypair() {
    const kp = await subtle().generateKey({ name: 'Ed25519' }, true, ['sign', 'verify']);
    const pub = new Uint8Array(await subtle().exportKey('raw', kp.publicKey));
    return { publicKey: pub, address: b58encode(pub), privateKey: kp.privateKey };
  }

  /** From a 64-byte Solana secret key (seed || pubkey) or a 32-byte seed. */
  async function keypairFromSecret(secret) {
    if (!(secret instanceof Uint8Array) || (secret.length !== 64 && secret.length !== 32)) throw new Error('secret key must be 64 bytes');
    const seed = secret.subarray(0, 32);
    const privateKey = await subtle().importKey('pkcs8', concat(PKCS8_ED25519_PREFIX, seed), { name: 'Ed25519' }, true, ['sign']);
    const jwk = await subtle().exportKey('jwk', privateKey);
    const pub = b64urlDecode(jwk.x);
    if (secret.length === 64 && !bytesEqual(pub, secret.subarray(32))) throw new Error('secret key and public key do not match');
    return { publicKey: pub, address: b58encode(pub), privateKey: privateKey };
  }
  function b64urlDecode(s) { return b64decode(s.replace(/-/g, '+').replace(/_/g, '/') + '==='.slice((s.length + 3) % 4)); }

  async function sign(keypair, message) { return new Uint8Array(await subtle().sign({ name: 'Ed25519' }, keypair.privateKey, message)); }

  async function verify(publicKey, message, signature) {
    try {
      const key = await subtle().importKey('raw', pk(publicKey), { name: 'Ed25519' }, false, ['verify']);
      return await subtle().verify({ name: 'Ed25519' }, key, signature, message);
    } catch (e) { return false; }
  }

  /** Put signatures for the given keypairs into an existing serialized transaction. */
  async function addSignatures(txBytes, keypairs) {
    const t = parseTx(txBytes);
    const signers = t.parsed.staticKeys.slice(0, t.parsed.header.numRequiredSignatures);
    const sigs = t.signatures.slice();
    for (const kp of keypairs) {
      const i = signers.indexOf(kp.address);
      if (i < 0) throw new Error('keypair is not a signer of this transaction');
      sigs[i] = await sign(kp, t.message);
    }
    return serializeTx(t.message, sigs);
  }

  /** base58 of the first signature, which is the transaction id. */
  function txId(txBytes) { return b58encode(parseTx(txBytes).signatures[0]); }

  /* ---------------------------------------------------------------- decoders */

  function hasDisc(data, disc) {
    if (!data || data.length < 8) return false;
    for (let i = 0; i < 8; i++) if (data[i] !== disc[i]) return false;
    return true;
  }
  const ZERO_KEY = '11111111111111111111111111111111';

  function decodeBondingCurve(data) {
    if (!hasDisc(data, ACCOUNT_DISC.BondingCurve) || data.length < 81) return null;
    const out = {
      virtualTokenReserves: readU64(data, 8),
      virtualQuoteReserves: readU64(data, 16),
      realTokenReserves: readU64(data, 24),
      realQuoteReserves: readU64(data, 32),
      tokenTotalSupply: readU64(data, 40),
      complete: data[48] === 1,
      creator: b58encode(data.subarray(49, 81)),
      isMayhemMode: data.length > 81 ? data[81] === 1 : false,
      quoteMint: ZERO_KEY
    };
    if (data.length >= 115) out.quoteMint = b58encode(data.subarray(83, 115));
    if (data.length >= 125) out.isHolderReward = data[124] === 1;
    return out;
  }

  function decodeSharingConfig(data) {
    if (!hasDisc(data, ACCOUNT_DISC.SharingConfig) || data.length < 80) return null;
    const n = readU32(data, 76);
    if (n > 10 || data.length < 80 + n * 34) return null;
    const shareholders = [];
    for (let i = 0; i < n; i++) {
      const o = 80 + i * 34;
      shareholders.push({ address: b58encode(data.subarray(o, o + 32)), bps: readU16(data, o + 32) });
    }
    return {
      bump: data[8], version: data[9], status: data[10] === 1 ? 'active' : 'paused',
      mint: b58encode(data.subarray(11, 43)), admin: b58encode(data.subarray(43, 75)),
      adminRevoked: data[75] === 1, shareholders: shareholders
    };
  }

  function decodePool(data) {
    if (!hasDisc(data, ACCOUNT_DISC.Pool) || data.length < 243) return null;
    return {
      index: readU16(data, 9),
      creator: b58encode(data.subarray(11, 43)),
      baseMint: b58encode(data.subarray(43, 75)),
      quoteMint: b58encode(data.subarray(75, 107)),
      poolBaseTokenAccount: b58encode(data.subarray(139, 171)),
      poolQuoteTokenAccount: b58encode(data.subarray(171, 203)),
      coinCreator: b58encode(data.subarray(211, 243))
    };
  }

  function decodeGlobal(data) {
    if (!hasDisc(data, ACCOUNT_DISC.Global) || data.length < 162) return null;
    const g = {
      initialVirtualTokenReserves: readU64(data, 73),
      initialVirtualSolReserves: readU64(data, 81),
      initialRealTokenReserves: readU64(data, 89),
      tokenTotalSupply: readU64(data, 97),
      feeBasisPoints: readU64(data, 105),
      creatorFeeBasisPoints: readU64(data, 154),
      buybackBasisPoints: 0n
    };
    if (data.length >= 1005) g.buybackBasisPoints = readU64(data, 997);
    return g;
  }

  function decodeTokenAccount(data) {
    if (!data || data.length < 72) return null;
    return { mint: b58encode(data.subarray(0, 32)), owner: b58encode(data.subarray(32, 64)), amount: readU64(data, 64) };
  }

  /** Mint base fields plus Token-2022 TokenMetadata (extension type 19) when present. */
  function decodeMint(data) {
    if (!data || data.length < 82) return null;
    const out = { supply: readU64(data, 36), decimals: data[44], initialized: data[45] === 1, metadata: null };
    if (data.length > 166 && data[165] === 1) {
      let o = 166;
      while (o + 4 <= data.length) {
        const type = readU16(data, o), len = readU16(data, o + 2);
        const v = data.subarray(o + 4, o + 4 + len);
        if (type === 19 && v.length >= 64 + 12) {
          try {
            let p = 64;
            const rd = () => { const l = readU32(v, p); p += 4; const s = td.decode(v.subarray(p, p + l)); p += l; return s; };
            out.metadata = { name: rd(), symbol: rd(), uri: rd() };
          } catch (e) { out.metadata = null; }
        }
        if (type === 0 && len === 0) break;
        o += 4 + len;
      }
    }
    return out;
  }

  /** Address lookup table account → list of addresses. */
  function decodeLookupTable(data) {
    if (!data || data.length < 56 || readU32(data, 0) !== 1) return null;
    const out = [];
    for (let o = 56; o + 32 <= data.length; o += 32) out.push(b58encode(data.subarray(o, o + 32)));
    return out;
  }

  /* ------------------------------------------------------------ pump maths */

  /** Tokens out for quoteIn (after fees) against virtual reserves. Rounds in the pool's favour. */
  function curveTokensOut(virtualQuote, virtualToken, quoteIn) {
    const vq = BigInt(virtualQuote), vt = BigInt(virtualToken), q = BigInt(quoteIn);
    if (q <= 0n) return 0n;
    const k = vq * vt;
    const newVt = k / (vq + q) + 1n;
    return newVt >= vt ? 0n : vt - newVt;
  }

  /**
   * min_tokens_out for buy_exact_quote_in_v2: deduct the fee estimate, then
   * the slippage allowance.
   */
  function minTokensForQuote(virtualQuote, virtualToken, lamportsIn, feeBps, slippageBps) {
    const fee = BigInt(feeBps == null ? 200 : feeBps);
    const net = (BigInt(lamportsIn) * 10000n) / (10000n + fee);
    const out = curveTokensOut(virtualQuote, virtualToken, net);
    return (out * (10000n - BigInt(slippageBps == null ? 500 : slippageBps))) / 10000n;
  }

  /* -------------------------------------------------------- Stash protocol */

  const MEMO_PREFIX = 'stash:1:';
  const FLOORS = [100000, 1000000, 10000000];
  const BRAND_ID = /^[a-z0-9][a-z0-9-]{0,31}$/;

  function launchMemo(o) {
    if (!BRAND_ID.test(o.brand)) throw new Error('bad brand id');
    if (!(o.floor === 0 || o.floor === 1 || o.floor === 2)) throw new Error('bad floor');
    return MEMO_PREFIX + o.brand + ':' + (o.mode === 'giveaway' ? 'g' : 'd') + ':' + o.floor;
  }
  function parseLaunchMemo(text) {
    if (typeof text !== 'string') return null;
    const i = text.indexOf(MEMO_PREFIX);
    if (i < 0) return null;
    const parts = text.slice(i + MEMO_PREFIX.length).trim().split(':');
    if (parts.length !== 3) return null;
    const brand = parts[0], mode = parts[1], floor = Number(parts[2]);
    if (!BRAND_ID.test(brand) || (mode !== 'd' && mode !== 'g') || !(floor === 0 || floor === 1 || floor === 2)) return null;
    return { brand: brand, mode: mode === 'g' ? 'giveaway' : 'dividends', floor: floor };
  }

  /** Accounts worth putting in the platform lookup table. */
  async function lookupTableAddresses(wallets) {
    const list = [
      P_.SYSTEM, P_.TOKEN, P_.TOKEN_2022, P_.WSOL, P_.MAYHEM, P_.PUMP_AMM,
      await derive.global(), await derive.mintAuthority(), await derive.pumpEventAuthority(),
      await derive.feesEventAuthority(), await derive.ammEventAuthority(),
      await derive.mayhemGlobalParams(), await derive.mayhemSolVault(),
      await derive.globalVolumeAccumulator(), await derive.feeConfig()
    ];
    for (const f of FEE_RECIPIENTS) { list.push(f, await derive.ata(f, P_.WSOL, P_.TOKEN)); }
    for (const f of BUYBACK_FEE_RECIPIENTS) { list.push(f, await derive.ata(f, P_.WSOL, P_.TOKEN)); }
    if (wallets && wallets.vault) list.push(wallets.vault);
    if (wallets && wallets.burn) list.push(wallets.burn);
    return list.map(addr);
  }

  /**
   * Build a launch: create the coin, optional initial buy, lock the fee
   * split to the Stash wallets, record brand/mode/floor in a memo, and ping
   * the vault so the indexer finds it.
   *
   * Returns { plan, memo, txs: [{ label, message, signers, size }] }, sent in order:
   *   single  launch                (lookup table, no initial buy)
   *   pair    create-buy, lock      (lookup table, initial buy)
   *   split   create, [buy], lock   (no lookup table)
   * Each transaction must confirm before the next is sent.
   */
  async function buildLaunch(o) {
    const creator = addr(o.creator), mint = addr(o.mint);
    const shares = [{ address: addr(o.wallets.burn), bps: 2000 }, { address: addr(o.wallets.vault), bps: 8000 }];
    const cuPrice = o.priorityMicroLamports == null ? 100000 : o.priorityMicroLamports;
    const memoText = launchMemo({ brand: o.brand, mode: o.mode, floor: o.floor });
    const pick = (list) => list[Math.floor(Math.random() * list.length)];

    const create = await ix.createV2({ mint: mint, user: creator, creator: creator, name: o.name, symbol: o.symbol, uri: o.uri });
    const lock = [
      await ix.createFeeSharingConfig({ payer: creator, mint: mint }),
      await ix.updateFeeSharesV2({ authority: creator, mint: mint, currentShareholders: [creator], shareholders: shares }),
      ix.memo(memoText),
      ix.transfer(creator, o.wallets.vault, 0)
    ];
    let buy = null;
    const lamportsIn = BigInt(o.devBuyLamports || 0);
    if (lamportsIn > 0n) {
      const g = o.global || {};
      const vq = g.initialVirtualSolReserves || 30000000000n;
      const vt = g.initialVirtualTokenReserves || 1073000000000000n;
      const feeBps = g.feeBasisPoints != null ? Number(g.feeBasisPoints + g.creatorFeeBasisPoints + (g.buybackBasisPoints || 0n)) : 200;
      const minOut = minTokensForQuote(vq, vt, lamportsIn, Math.max(feeBps, 125) + 75, o.slippageBps == null ? 1000 : o.slippageBps);
      if (minOut <= 0n) throw new Error('Initial buy is too small');
      buy = async (curveCreator) => [
        await ix.createAtaIdempotent({ payer: creator, owner: creator, mint: mint, tokenProgram: P_.TOKEN_2022 }),
        await ix.buyExactQuoteInV2({
          mint: mint, user: creator, curveCreator: curveCreator, lamportsIn: lamportsIn, minTokensOut: minOut,
          baseTokenProgram: P_.TOKEN_2022, feeRecipient: pick(FEE_RECIPIENTS), buybackFeeRecipient: pick(BUYBACK_FEE_RECIPIENTS)
        })
      ];
    }

    const compile = (label, ixs, tables) => {
      const c = compileV0({ payer: creator, instructions: ixs, recentBlockhash: o.recentBlockhash, lookupTables: tables || [] });
      return { label: label, message: c.message, signers: c.signers, size: c.size };
    };

    // With the platform lookup table, either everything fits in one
    // transaction (no initial buy), or the coin and the initial buy land
    // together and the fee lock follows straight after.
    if (o.lookupTable && o.lookupTable.addresses && o.lookupTable.addresses.length) {
      const tables = [o.lookupTable];
      if (!buy) {
        const t = compile('launch', [ix.computeUnitLimit(450000), ix.computeUnitPrice(cuPrice), create].concat(lock), tables);
        if (t.size <= PACKET_SIZE) return { plan: 'single', memo: memoText, txs: [t] };
      } else {
        const t1 = compile('create-buy', [ix.computeUnitLimit(500000), ix.computeUnitPrice(cuPrice), create].concat(await buy(creator)), tables);
        const t2 = compile('lock', [ix.computeUnitLimit(300000), ix.computeUnitPrice(cuPrice)].concat(lock), tables);
        if (t1.size <= PACKET_SIZE && t2.size <= PACKET_SIZE) return { plan: 'pair', memo: memoText, txs: [t1, t2] };
      }
    }

    const txs = [];
    const c1 = compileV0({ payer: creator, recentBlockhash: o.recentBlockhash, instructions: [ix.computeUnitLimit(300000), ix.computeUnitPrice(cuPrice), create] });
    txs.push({ label: 'create', message: c1.message, signers: c1.signers, size: c1.size });
    if (buy) {
      const c3 = compileV0({ payer: creator, recentBlockhash: o.recentBlockhash, instructions: [ix.computeUnitLimit(250000), ix.computeUnitPrice(cuPrice)].concat(await buy(creator)) });
      txs.push({ label: 'buy', message: c3.message, signers: c3.signers, size: c3.size });
    }
    const c2 = compileV0({ payer: creator, recentBlockhash: o.recentBlockhash, instructions: [ix.computeUnitLimit(300000), ix.computeUnitPrice(cuPrice)].concat(lock) });
    txs.push({ label: 'lock', message: c2.message, signers: c2.signers, size: c2.size });
    for (const t of txs) if (t.size > PACKET_SIZE) throw new Error('transaction too large: ' + t.label + ' ' + t.size);
    return { plan: 'split', memo: memoText, txs: txs };
  }

  /** Build the lock transaction on its own (used to finish a half-done launch). */
  async function buildLock(o) {
    const creator = addr(o.creator), mint = addr(o.mint);
    const shares = [{ address: addr(o.wallets.burn), bps: 2000 }, { address: addr(o.wallets.vault), bps: 8000 }];
    const ixs = [ix.computeUnitLimit(300000), ix.computeUnitPrice(o.priorityMicroLamports == null ? 100000 : o.priorityMicroLamports)];
    if (!o.configExists) ixs.push(await ix.createFeeSharingConfig({ payer: creator, mint: mint, pool: o.pool || null }));
    ixs.push(
      await ix.updateFeeSharesV2({ authority: creator, mint: mint, currentShareholders: o.currentShareholders || [creator], shareholders: shares }),
      ix.memo(launchMemo({ brand: o.brand, mode: o.mode, floor: o.floor })),
      ix.transfer(creator, o.wallets.vault, 0)
    );
    const c = compileV0({ payer: creator, recentBlockhash: o.recentBlockhash, instructions: ixs });
    return { label: 'lock', message: c.message, signers: c.signers, size: c.size };
  }

  return {
    // bytes
    concat: concat, u8: u8, u16: u16, u32: u32, u64: u64, borshString: borshString,
    readU16: readU16, readU32: readU32, readU64: readU64, bytesEqual: bytesEqual, toHex: toHex,
    b64encode: b64encode, b64decode: b64decode, utf8: te, utf8d: td,
    // keys
    b58encode: b58encode, b58decode: b58decode, pk: pk, addr: addr, isAddress: isAddress,
    sha256: sha256, isOnCurve: isOnCurve, findPda: findPda, createPda: createPda, pda: pda, anchorDisc: anchorDisc,
    // programs
    PROGRAMS: PROGRAMS, FEE_RECIPIENTS: FEE_RECIPIENTS, BUYBACK_FEE_RECIPIENTS: BUYBACK_FEE_RECIPIENTS,
    DISC: DISC, ACCOUNT_DISC: ACCOUNT_DISC, derive: derive, ix: ix, meta: meta, instruction: instruction,
    // transactions
    encodeLength: encodeLength, decodeLength: decodeLength, compileV0: compileV0, serializeTx: serializeTx,
    parseTx: parseTx, parseMessage: parseMessage, resolveAccounts: resolveAccounts, txSize: txSize, PACKET_SIZE: PACKET_SIZE,
    generateKeypair: generateKeypair, keypairFromSecret: keypairFromSecret, sign: sign, verify: verify,
    addSignatures: addSignatures, txId: txId,
    // decoders
    decodeBondingCurve: decodeBondingCurve, decodeSharingConfig: decodeSharingConfig, decodePool: decodePool,
    decodeGlobal: decodeGlobal, decodeTokenAccount: decodeTokenAccount, decodeMint: decodeMint,
    decodeLookupTable: decodeLookupTable, hasDisc: hasDisc,
    // maths + protocol
    curveTokensOut: curveTokensOut, minTokensForQuote: minTokensForQuote,
    MEMO_PREFIX: MEMO_PREFIX, FLOORS: FLOORS, BRAND_ID: BRAND_ID,
    launchMemo: launchMemo, parseLaunchMemo: parseLaunchMemo, lookupTableAddresses: lookupTableAddresses,
    buildLaunch: buildLaunch, buildLock: buildLock
  };
});
