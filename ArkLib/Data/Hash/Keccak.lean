/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Init

/-!
  # Keccak-256 (Ethereum variant)

  This file contains a pure, self-contained implementation of the original Keccak-256 hash
  function, as used by Ethereum. This is the *original* Keccak (with the `0x01` padding domain
  byte), and is **NOT** the NIST-standardized SHA3-256 (which uses the `0x06` padding domain
  byte).

  The implementation follows the Keccak/SHA-3 specification:
  - The permutation is `Keccak-f[1600]` over a state of 25 64-bit lanes (`Array UInt64` of size
    25), with 24 rounds. Each round applies the five step mappings θ (theta), ρ (rho), π (pi),
    χ (chi), ι (iota).
  - The sponge construction has rate `R = 1088` bits (`136` bytes) and capacity `C = 512` bits,
    matching the `256`-bit output (`32` bytes).
  - The padding rule is `pad10*1`: the first byte appended is the domain byte `0x01`, and the
    final byte of the last block has its high bit set (`0x80`). When the message length modulo
    the rate equals `rate - 1`, these two are combined into a single `0x81` byte.

  Lanes are loaded/stored in little-endian byte order, as specified by Keccak.

  ## Validation

  This implementation has been validated against the cross-language KAT vectors in
  `tests/kat/keccak256.kat.json` (Ethereum keccak256). The following are confirmed by `#eval`:

  - `keccak256 (empty)` =
    `c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`
  - `keccak256 ("abc")` =
    `4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45`
  - `keccak256 ("hello world")` =
    `47173285a8d7341e5e972fc677286384f802f8ef42a5ec5f03bbfa254cb01fad`
  - `keccak256 ("Transfer(address,address,uint256)")` =
    `ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef`
  - `keccak256 (single 0x00 byte)` =
    `bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a`
  - `keccak256 (135 bytes, rate - 1)` =
    `cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62`
  - `keccak256 (136 bytes, exactly one rate block)` =
    `81e7ecb492d033f1692e770a6eb874e70aac45ec10da93483fc8d3537805c097`
  - `keccak256 (200 bytes of 0xff)` =
    `3e04329b5f5c0f493dd965957722717ef46ed487733d5f9da932de72d9ac4a51`

  `native_decide` / `decide` are intentionally NOT used (the former is forbidden, the latter is
  too slow for the permutation). Validation is performed via `#eval` in the build/verification
  run.
-/

namespace Keccak

/-- The Keccak-256 sponge rate in bytes (`1088` bits). -/
def rateBytes : Nat := 136

/-- The number of rounds in `Keccak-f[1600]`. -/
def numRounds : Nat := 24

/-- The number of 64-bit lanes in the `Keccak-f[1600]` state. -/
def numLanes : Nat := 25

/-- The 24 round constants for the ι (iota) step of `Keccak-f[1600]`. -/
def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offsets for the ρ (rho) step, indexed by lane position `x + 5 * y`. -/
def rhoOffsets : Array UInt64 := #[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

/-- Left-rotate a 64-bit word by `n` bits (`n` taken modulo 64). -/
@[inline] def rotl64 (x : UInt64) (n : UInt64) : UInt64 :=
  let m := n % 64
  if m == 0 then x else (x <<< m) ||| (x >>> (64 - m))

/-- The θ (theta) step of `Keccak-f[1600]`. -/
def theta (a : Array UInt64) : Array UInt64 := Id.run do
  -- Column parities: c[x] = a[x] ⊕ a[x+5] ⊕ a[x+10] ⊕ a[x+15] ⊕ a[x+20].
  let mut c : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    c := c.set! x (a[x]! ^^^ a[x+5]! ^^^ a[x+10]! ^^^ a[x+15]! ^^^ a[x+20]!)
  -- d[x] = c[x-1] ⊕ rotl(c[x+1], 1).
  let mut d : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    d := d.set! x (c[(x + 4) % 5]! ^^^ rotl64 c[(x + 1) % 5]! 1)
  -- a[x + 5y] ⊕= d[x].
  let mut out := a
  for y in [0:5] do
    for x in [0:5] do
      let i := x + 5 * y
      out := out.set! i (out[i]! ^^^ d[x]!)
  return out

/-- The ρ (rho) and π (pi) steps of `Keccak-f[1600]`, combined.

`ρ` rotates each lane by its offset; `π` permutes lane positions via
`b[y, 2x + 3y] = rotl(a[x, y], r[x,y])`. -/
def rhoPi (a : Array UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.replicate 25 0
  for y in [0:5] do
    for x in [0:5] do
      let src := x + 5 * y
      let dst := y + 5 * ((2 * x + 3 * y) % 5)
      out := out.set! dst (rotl64 a[src]! rhoOffsets[src]!)
  return out

/-- The χ (chi) step of `Keccak-f[1600]`:
`a[x, y] ⊕= (¬a[x+1, y]) ∧ a[x+2, y]`. -/
def chi (a : Array UInt64) : Array UInt64 := Id.run do
  let mut out := a
  for y in [0:5] do
    let r := 5 * y
    let a0 := a[r]!
    let a1 := a[r+1]!
    let a2 := a[r+2]!
    let a3 := a[r+3]!
    let a4 := a[r+4]!
    out := out.set! (r)   (a0 ^^^ ((~~~a1) &&& a2))
    out := out.set! (r+1) (a1 ^^^ ((~~~a2) &&& a3))
    out := out.set! (r+2) (a2 ^^^ ((~~~a3) &&& a4))
    out := out.set! (r+3) (a3 ^^^ ((~~~a4) &&& a0))
    out := out.set! (r+4) (a4 ^^^ ((~~~a0) &&& a1))
  return out

/-- A single round of `Keccak-f[1600]`: θ, then ρπ, then χ, then ι (XOR round constant into
lane 0). -/
def keccakRound (a : Array UInt64) (rc : UInt64) : Array UInt64 :=
  let a := theta a
  let a := rhoPi a
  let a := chi a
  a.set! 0 (a[0]! ^^^ rc)

/-- The `Keccak-f[1600]` permutation: 24 rounds applied to a 25-lane state. -/
def keccakF (a : Array UInt64) : Array UInt64 :=
  Fin.foldl numRounds (fun st (r : Fin numRounds) => keccakRound st roundConstants[r.val]!) a

/-- Read 8 bytes (little-endian) from `bytes` starting at `off` as a `UInt64`.
Out-of-range positions read as `0` (used after the message has been padded into full blocks, so
this never actually happens for in-range lanes). -/
@[inline] def loadLaneLE (bytes : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for j in [0:8] do
    let b : UInt64 := (bytes.get! (off + j)).toUInt64
    v := v ||| (b <<< (UInt64.ofNat (8 * j)))
  return v

/-- XOR a single `rate`-sized block (`136` bytes) of `bytes` (starting at `off`) into the state's
rate lanes, in little-endian lane order. -/
def absorbBlock (state : Array UInt64) (bytes : ByteArray) (off : Nat) : Array UInt64 := Id.run do
  let mut st := state
  -- 136 bytes = 17 lanes of 8 bytes each.
  for i in [0:17] do
    st := st.set! i (st[i]! ^^^ loadLaneLE bytes (off + 8 * i))
  return keccakF st

/-- Apply `pad10*1` padding to `input` for the given `rate`, with domain byte `0x01`
(original Keccak). Produces a byte array whose length is a multiple of `rate`. -/
def padInput (input : ByteArray) : ByteArray := Id.run do
  let r := rateBytes
  let len := input.size
  -- Number of bytes in the final (partial) block.
  let rem := len % r
  -- Pad length: bring up to a full block. At least one padding byte is always added.
  let padLen := r - rem
  let mut pad : ByteArray := ByteArray.emptyWithCapacity padLen
  -- First padding byte is the domain separator 0x01.
  -- If padLen == 1, the single byte carries both 0x01 and the final 0x80 => 0x81.
  if padLen == 1 then
    pad := pad.push 0x81
  else
    pad := pad.push 0x01
    for _ in [0:padLen - 2] do
      pad := pad.push 0x00
    pad := pad.push 0x80
  return input ++ pad

/-- Store the first `n` lanes of `state` as little-endian bytes, concatenated. -/
def squeezeBytes (state : Array UInt64) (numBytes : Nat) : ByteArray := Id.run do
  let mut out : ByteArray := ByteArray.emptyWithCapacity numBytes
  let mut produced := 0
  -- We only ever squeeze ≤ rate bytes (32 ≤ 136), so a single state suffices.
  let mut lane := 0
  while produced < numBytes do
    let v := state[lane]!
    for j in [0:8] do
      if produced < numBytes then
        let b : UInt8 := (v >>> (UInt64.ofNat (8 * j))).toUInt8
        out := out.push b
        produced := produced + 1
    lane := lane + 1
  return out

/-- Keccak-256 (Ethereum variant): hash `input` to a 32-byte digest.

Sponge with rate `136` bytes, capacity `512` bits, `pad10*1` padding with the original-Keccak
domain byte `0x01`, little-endian lane loading, squeezing `32` bytes. -/
def keccak256 (input : ByteArray) : ByteArray := Id.run do
  let padded := padInput input
  let numBlocks := padded.size / rateBytes
  let mut state : Array UInt64 := Array.replicate numLanes 0
  for blk in [0:numBlocks] do
    state := absorbBlock state padded (blk * rateBytes)
  return squeezeBytes state 32

/-- Keccak-256 returning a fixed-length `Vector UInt8 32` digest. Pads/truncates defensively, but
`keccak256` always produces exactly 32 bytes. -/
def keccak256Vector (input : ByteArray) : Vector UInt8 32 :=
  let digest := keccak256 input
  Vector.ofFn (fun i => digest.get! i.val)

@[simp] theorem rateBytes_eq : rateBytes = 136 := rfl

@[simp] theorem numRounds_eq : numRounds = 24 := rfl

@[simp] theorem numLanes_eq : numLanes = 25 := rfl

@[simp] theorem roundConstants_size : roundConstants.size = numRounds := rfl

@[simp] theorem rhoOffsets_size : rhoOffsets.size = numLanes := rfl

/-- The fixed-length Keccak-256 vector API always exposes exactly 32 bytes. -/
@[simp] theorem keccak256Vector_toList_length (input : ByteArray) :
    (keccak256Vector input).toList.length = 32 := by
  simp [keccak256Vector]

end Keccak
