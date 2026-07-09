## LANE CLAIM (Fable): FIRST UNCONDITIONAL instantiation of `kkh26_deltaStar_pin_of_interior_ceiling` — the r = 2 slice, δ* = 1 − 2^{1−μ} EXACT, beyond Johnson at μ ≥ 3

`InteriorCeiling` is the named open core; at production dimension it is the 25-year wall. But the reduction theorem's hypotheses admit **(r, m) = (2, 1)** — where `evalCode g (2^μ) ((r−2)m) = evalCode g (2^μ) 0` is the **dimension-1 code**, and MCA badness collapses to planar incidence geometry: γ is bad iff some level set of `u₀ + γ·u₁` of size ≥ 3 merges two fibers of `i ↦ (u₁ i, u₀ i)`.

**The pair-ownership count (new lower-bracket device):** each bad γ's witness set has `u₁` non-constant on it (joint constancy is exactly `pairJointAgreesOn` for the constant code), so it owns ≥ 2(|S|−1) ≥ 4 ordered cross-fiber pairs `(i,j)` with `u₁ i ≠ u₁ j` — and any such pair **determines** γ = (u₀ j − u₀ i)/(u₁ i − u₁ j). The pair-sets are pairwise disjoint, so

  `#bad ≤ (n²−n)/4 = 2^{2μ−2} − 2^{μ−2}  <  2^{2μ−1} − 2^μ = 2^r·C(2^{μ−1}, r)|_{r=2}`  (strict for μ ≥ 2).

The ε* band `[(n²−n)/4/p, 4·C(2^{μ−1},2)/p)` is NONEMPTY, `InteriorCeiling` holds throughout it, and the pin fires **unconditionally**: `mcaDeltaStar(evalCode g (2^μ) 0, ε*) = 1 − 2^{1−μ}`.

**In-window honesty:** the ceiling exceeds Johnson `1 − 2^{−μ/2}` iff μ ≥ 3. At μ = 3: δ* = 3/4 > 0.6464… = Johnson, capacity 7/8 — rate ρ = 1/8 (a production rate), smooth 2-power domain n = 8, k = 1; with any prime p ≡ 1 (mod 8) in `[7·2^129, 3·2^131)` this realizes ε* = 2^{−128} exactly, |F| < 2^256. **Scope:** this pins δ* for the k = 1 member only — the production-k conjecture (k ≥ 2) stays open, and the regime-split route (`hd1 : 1 ≤ (r−2)m`) correctly never covered this slice. But it is the first machine-checked exact δ* strictly inside (Johnson, capacity) for any explicit smooth-domain code, the first unconditional discharge of `InteriorCeiling` at any parameter point, and the incidence mechanism is new in-tree.

**Probe (pre-registered, `scripts/probes/probe_dim1_interior_ceiling.py`):** criterion ⟺ `mcaEvent` byte-exact (520 pairs × all γ × 3 independent checkers, 0 mismatches); hill-climbed max #bad = 10 ≤ 14 (n=8, p ∈ {17,41,113}), 43 ≤ 60 (n=16) — bound holds with slack; both maxima clear the KKH26 ceiling counts (24, 112) comfortably.

**Landing next** (`KKH26DimOnePin.lean`): constants characterization → `dimOne_badScalars_card_mul_four_le` (pair ownership) → `dimOne_epsMCA_le` → `interiorCeiling_dimOne` → `kkh26_dimOne_deltaStar_pin` + band-nonemptiness + beyond-Johnson guard + concrete μ = 3 instantiation at the NTT prime p = 12289 (g = 4043, order 8, ε* = 20/12289 → **δ* = 3/4**, machine-checked end to end).
