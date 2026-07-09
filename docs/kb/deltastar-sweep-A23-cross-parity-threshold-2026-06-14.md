# Sweep A23 — cross-parity leak `A ≡ −g·B mod q`: threshold law CONFIRMED, leak premise REFUTED at genuine level

**Actionable A23 (merged `407-T09`). Date 2026-06-14. Verdict: PARTIAL** — one clean positive
(the threshold law, proven as a lattice identity + verified exact 11/11), one clean negative (the
"96–100 % leak" premise is FALSE for genuine defects), and the leak-to-bound hope is closed off
structurally. No prize closure fabricated; the count of genuine defects remains the W2 / Pan–Xu
fully-split ideal-SVP open wall, untouched.

## Context — what T09 already did, what A23 left open

The predecessor thread `407-T09` (`WF407_T09Leak.lean`,
`wf407-T09-leak-crossparity-antipodal-verdict.md`) reached a `walled` verdict: the leak's
100 %-reflection feature is the char-0 antipodal (sum-zero) structure; the genuine-defect count is
the additive-energy excess `E₂^{(p)} − E₂^{(0)}` = W2 = Pan–Xu fully-split ideal-SVP. A23 explicitly
flagged **two parts T09 did NOT settle**: (a) re-verify the **threshold law**
`r* = (1/2)·λ₁^{L1,even}(p)` against brute-force shortest-even-L1-vector enumeration; (b) attempt to
turn the leak into a counting bound. This sweep settles both.

## (1) The threshold law `r* = (1/2)·λ₁^{L1,even}` — CONFIRMED EXACTLY (11/11) and PROVEN

`scripts/probes/sweep_A23_cross_parity.py` (EXACT enumeration, no sampling), `n = 8,16,32`,
`β = log_n p ∈ {2, 2.5, 3, 3.5}`:

- **Defect-onset depth** `r*(p) := min { r : E_r^{(p)}(μ_n) > E_r^{(0)}(μ_n) }` — the smallest depth
  with a spurious mod-`p` collision of `μ_n` that is not a char-0 identity. Computed exactly from the
  ordered-`r`-tuple representation counts (char-`p`) vs the power-basis fold counts (char-0).
- **`λ₁^{L1,even}(p)`** — the L1-weight (total number of `±1` terms) of the shortest **even-weight
  (balanced, `|P| = |N| = r`)** `±1` relation `∑_{i∈P} ζ^i − ∑_{j∈N} ζ^j ≡ 0 (mod p)` that does not
  vanish in `ℤ[ζ_n]`. Computed by meet-in-the-middle over both sides. `λ₁^{L1,even} = 2·r` for the
  shortest balanced radius `r`.

| n | β | p | r* (energy onset) | λ₁^{L1,even} | r* = λ₁/2 ? |
|---|---|---|---|---|---|
| 8 | 2.0 | 97 | 3 | 6 | YES |
| 8 | 2.5 | 193 | 4 | 8 | YES |
| 8 | 3.0 | 577 | 5 | 10 | YES |
| 16 | 2.0 | 257 | 2 | 4 | YES |
| 16 | 2.5 | 1153 | 3 | 6 | YES |
| 16 | 3.0 | 4129 | 4 | 8 | YES |
| 16 | 3.5 | 16417 | 5 | 10 | YES |
| 32 | 2.0 | 1153 | 2 | 4 | YES |
| 32 | 2.5 | 5953 | 3 | 6 | YES |
| 32 | 3.0 | 32833 | 4 | 8 | YES |
| 32 | 3.5 | 186049 | 3 | 6 | YES |

**11/11 exact.** The `even` superscript is load-bearing and is exactly A23's notation: at
`n = 32, β = 3.0` there is an *unbalanced* `±1` relation of **odd** total weight `5` (a `2 = 3`
shape) — but that is NOT an additive-energy collision (`|P| ≠ |N|`), so it must be excluded; the
shortest *balanced* even relation there has radius `4`, matching the energy onset `r* = 4`. Naively
taking the shortest L1 over *all* (incl. unbalanced) relations breaks the law (1 miss); restricting
to even-weight makes it exact.

**Proven, axiom-clean** (`Frontier/Sweep_A23_CrossParityThreshold.lean`, audit
`[propext, Classical.choice, Quot.sound]`): the law is the lattice identity
`2·r* = λ₁^{L1,even}` where `r* = sInf R`, `λ₁^{L1,even} = sInf (2·R)` over the balanced-relation
radius set `R`, via `sInf_two_mul_image` (`sInf (2•R) = 2·sInf R` for nonempty `R ⊆ ℕ`). The
mathematical content is the **weight–radius correspondence**: a balanced depth-`r` collision IS an
even `±1` relation of L1-weight exactly `2r`, so the two readings (onset depth / shortest even
L1-weight) are the SAME minimum scaled by `2`. `l1WeightSet_even` proves the weight set contains
only even numbers (the odd unbalanced relations never enter).

## (2) The "96–100 % leak" premise — REFUTED at the genuine (char-`p`-only) level

A23's premise quoted "96–100 % of mod-q additive-energy defects obey `A = −g·B`". Re-measured at the
**genuine defect onset depth `r*`** (`sweep_A23_cross_parity.py`, P3 block):

| n | β | p | depth r* | #genuine defects | leak `A=−gB` % | distinct g |
|---|---|---|---|---|---|---|
| 8 | 2–3 | 97–577 | 3–5 | 24–72 | **0 %** | 0 |
| 16 | 2–2.5 | 257–1153 | 2–3 | 32–80 | **0 %** | 0 |
| 16 | 3.0 | 4129 | 4 | 464 | **3.4 %** | 1 |
| 16 | 3.5 | 16417 | 5 | 1536 | **2.1 %** | 4 |
| 32 | 2–3.5 | 1153–186049 | 2–4 | 96–20000 | **0 %** | 0 |

So the 96–100 % figure is a property of the **full `E₂`-collision set** (overwhelmingly the char-0
antipodal `x₂ = −x₁` matchings), NOT of the genuine spurious defects. At the genuine onset the leak
holds **0–3 %** of the time, and where it does (`n=16, β≥3`), the realizing units `g` stay `O(1)`.
This independently corroborates the prior T09 `genuine_at_onset` probe (genuine defects realize the
setwise reflection `0 %` of the time) and sharpens it to the onset depth across `β`.

**Algebraic reason — proven, axiom-clean** (`genuine_defect_escapes_leak`,
`genuine_defect_escapes_leak_depth`): a genuine balanced collision has nonzero common sum `s ≠ 0`;
a cross-parity reflection `S_A = c·S_B` forces (by summing) `s = c·s`, hence `(c−1)·s = 0`, hence
`c = 1` (over a domain). The leak with `c = −g ≠ 1` therefore **cannot describe a nonzero-sum
genuine defect**. The leak sees only the `s = 0` antipodal char-0 structure.

## (3) Leak-to-bound feasibility — CLOSED OFF

A genuine sub-energy count from the leak would need EITHER the leak fraction high at the onset
(it is `≤ 3 %`) OR the realizing `g` to spread over MANY thin cosets (it stays `O(1)`). Neither
holds. Where the leak does fire (`n=16, β≥3`, ≤4 distinct `g`), the count is `∑_g |μ_n ∩ g·μ_n|`
over `O(1)` units `g`, which Cauchy–Schwarz returns to the additive energy `E₂(μ_n)` — the same W2
wall. The leak is a re-expression of the wall, not a lever below it. Recorded as the named OPEN
`Prop DefectCountLinear` (NOT discharged); it is W2 / Pan–Xu fully-split `N(𝔭)=p` ideal-SVP.

## Verdict: PARTIAL

- **Positive (new):** the threshold law `r* = (1/2)·λ₁^{L1,even}` is exact (11/11) and proven as an
  axiom-clean lattice identity — the defect-onset depth IS half the shortest even balanced-relation
  L1-weight. This is the precise quantitative form the deep-moment validity wall (`r_max ≈ 2 log_n p
  − 3`, `wf407-T389-01`) takes on the lattice side.
- **Negative (corrects the A23 premise):** the cross-parity leak is a char-0 antipodal artifact;
  genuine defects escape it (`0–3 %` at onset, `g` ranges over `O(1)`), so the leak yields NO count
  below the additive-energy / BGK / Pan–Xu wall. The "turn the leak into a bound" hope is closed off
  structurally.

**No prize closure.** The genuine-defect count `E_r^{(p)} − E_r^{(0)}` at the saddle depth remains
the open analytic wall.

## Artifacts

- `scripts/probes/sweep_A23_cross_parity.py` — threshold-law verification (11/11 exact) + leak
  fraction at genuine onset + coset-concentration / leak-to-bound feasibility.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A23_CrossParityThreshold.lean` — axiom-clean
  (`[propext, Classical.choice, Quot.sound]`): `threshold_law` (`2·r* = λ₁^{L1,even}`),
  `threshold_law_div`, `sInf_two_mul_image`, `l1WeightSet_even`, `genuine_defect_escapes_leak`,
  `genuine_defect_escapes_leak_depth`, and the named OPEN `DefectCountLinear`.

Cross-refs: `wf407-T09-leak-crossparity-antipodal-verdict.md` (predecessor `walled` verdict),
`wf407-T389-01-deepmom-defect-wall.md` (`r_max ≈ 2 log_n p − 3`, the depth–prime threshold this
law refines on the lattice side), `WF407_T09Leak.lean`, `CyclotomicNormDefectThreshold.lean`,
`SparseSupportIdealSVPLowerBound.lean`.
