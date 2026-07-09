# A34 — Lacunary cyclotomic resultant maxima: the fixed-`r` Parseval bound opens `s = 128` at `ρ ≤ 1/4` (no Thorner–Zaman)

**Date:** 2026-06-14 · **Thread:** A34 (merged `357-T13 / 334-T15`) · **Verdict: PARTIAL**
(one-rate-bracket gain: `s = 128` prize rows open **unconditionally** at `ρ ∈ {1/4, 1/8, 1/16}`;
`ρ = 1/2` at `s = 128` and all of `s = 256` stay blocked; the asymptotic `s = 2^μ → ∞` rows still
need Thorner–Zaman).

## The question

[KKH26] Lemma 1's counterexample needs, for collision data, `p ∤ N` where
`N = Res_ℤ(R, Φ_{2^m})`, `R = P_{d₁} − P_{d₂}` a `±1,0` polynomial on the window `[0, h)`,
`h := s/2 = 2^{m-1} = φ(2^m) = deg Φ_{2^m}`, `‖R‖₁ ≤ 2r`, `‖R‖₂² ≤ 4r`, `deg R < h`.
A34: chase lacunary cyclotomic resultant / Mahler-measure literature (Myerson, Lehmer-adjacent)
for a sharp `|Res|` bound that opens the `s = 128` rows of the ceiling `δ* ≤ 1 − (r−2)/s` with
field size below the prize cap `q < 2^256`, **without** the Thorner–Zaman PNT-in-APs input.

## The reconstructed in-tree state (all axiom-clean, in `KKH26SumsOfRootsOfUnity.lean`)

| route | bound on `|N|` | worst-case `r=h` log₂ at `s=128` | opens `s` up to |
|-------|----------------|----------------------------------|------------------|
| house / ℓ¹ (`natAbs_resultant_cyclotomic_le`) | `‖R‖₁^h ≤ s^{s/2}` | `448` | `s ≤ 64` |
| Parseval+AM-GM, `r=h` (`cyclotomicLandauSqBound_proved`, via `landauSqEnvelope h = (4h)^h·2^{h-1}`) | `(4h)^{h/2}·2^{(h-1)/2}` | `287.5` | `s ≤ 64` |

Both fail `s = 128` at worst-case `r = h`. The `SharpResultantBound.lean` Mahler-measure route
(`M(R) ≤ ‖R‖₂`, Landau) gives the **same** ℓ² envelope — no improvement below it.

## The lever (probe `scripts/probes/sweep_A34_lacunary_maxima.py`, exact)

Two facts the in-tree `landauSqEnvelope` discards:

1. **The `2^{h-1}` factor is slack.** The clean Parseval+AM-GM step is
   `‖∏_{i<h} R(ζ^{2i+1})‖² = ∏ z_i ≤ ((∑ z_i)/h)^h = (‖R‖₂²)^h`, giving the slack-free
   `|N|² ≤ (‖R‖₂²)^h`. (Probe: worst-case geo/arith ratio of `|R(ζ^{odd})|²` is `≈ 1.0`, so AM-GM
   is essentially **tight on this class** — no constant-factor improvement of `(4r)^{h/2}` exists,
   confirming Landau ℓ² is the sharp lacunary maximum. Myerson AN5 refines the *minimum*
   sum-of-roots-of-unity = wrong direction.)
2. **The `r`-dependence.** `‖R‖₂² ≤ 4r`, so `|N|² ≤ (4r)^h`, i.e. `|N| ≤ (4r)^{s/4}`. The in-tree
   envelope froze `r = h`; the [KKH26] counterexample only needs the *smallest* in-window `r`,
   `r_lo = ⌈2 + ρ·s⌉` (the cheapest below-capacity bad point).

Open `s = 128` unconditionally ⟺ `(4r)^h < (2^{256})²` ⟺ `(s/4)·log₂(4r) < 256`:

| `ρ`   | `r_lo = ⌈2+ρ·128⌉` | `(s/4)·log₂(4 r_lo)` | opens `s=128`? |
|-------|--------------------|----------------------|-----------------|
| `1/2` | `66` | `257.4` | **no** (misses by `≈1.4` bits) |
| `1/4` | `34` | `226.8` | **yes** |
| `1/8` | `18` | `197.4` | **yes** |
| `1/16`| `10` | `170.3` | **yes** |

`s = 256` (`h = 128`): even `r = 4` already saturates the cap (`16^{128} = 2^{512} = (2^{256})²`),
so it is closed for every prize rate (`r_lo ≥ 18`).

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A34_LacunaryResultantS128.lean`
  — axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorry`/`native_decide`):
  - `oddEvalProductSq_le_l2SqOn_pow` — slack-free Parseval+AM-GM product bound.
  - `natAbs_resultant_cyclotomic_sq_le_l2SqOn_pow` — `|Res|² ≤ (l2SqOn h R)^h`.
  - `collisionResultant_sq_le_four_r_pow` — `|N|² ≤ (4r)^{2^{m-1}}` (the fixed-`r` maximum).
  - `s128_rate_quarter_threshold` — `(4·34)^{64} < (2^{256})²` (decidable).
  - `collisionResultant_not_dvd_s128_quarter` — wired through
    `not_dvd_collisionResultant_of_natAbs_sq_lt`: any prime `p ≥ 2^{256}` divides no collision
    resultant at `s = 128`, `r ≤ 34`. This is the `kkh26_lemma1_of_not_dvd` hypothesis, supplied
    unconditionally → the `s = 128`, `ρ = 1/4` ceiling row with field size below the prize cap.
  - `landauSqEnvelope_s128_exceeds_cap`, `s128_rate_half_exceeds_cap`,
    `s256_rate_quarter_exceeds_cap` — the decidable no-go witnesses pinning the lever's boundary.
- `scripts/probes/sweep_A34_lacunary_maxima.py` — the threshold tables + AM-GM tightness.

## Honest scope (PARTIAL — what's left)

Genuine novel gain: the in-tree state opened only `s ≤ 64`; this opens `s = 128` at `ρ ≤ 1/4`,
purely from the `r`-refinement + slack removal of the existing Parseval envelope — no new
literature input needed (Myerson/Lehmer give nothing below Landau ℓ²; the Mahler route is the
same envelope). NOT the prize: `ρ = 1/2` at `s = 128` (off by `≈1.4` bits) and all of `s = 256`
remain blocked, and the prize-proper asymptotic rows `s = 2^μ → ∞` at polynomial field size
`p = Θ(n^β)` still require Thorner–Zaman PNT-in-APs (`KKH26PolyFieldCeiling.lean` /
`Frontier/B3_ThornerZaman_s128.lean`). The wall beyond this bracket is the worst-case
`max_R |Res(R, Φ_{2^m})|` = the √-cancellation / generalized-Paley character-sum object (W2/W4),
unchanged.
