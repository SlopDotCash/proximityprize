/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# G207 no-go: kernel sparsity does not suppress late-Newton alignment *magnitude* (#466)

This is the quantitative companion to `G206`.  `G206` proved the **sign** no-go for the injective
weighted-kernel route: `φ₂ : u ∈ G ↦ (2-u)^n` injective (maximal `0/1` kernel-class sparsity of the
collision count `W_G(t) = #{y ∈ G : 2y - t ∈ G}`) still realizes every sign pattern of the centered
alignments `A_r`, so kernel sparsity does not control the *sign* of the placement of `supp W_G`
against the adjacent-rank profile `R_r`.

The production gates are **quantitative lower bounds** on `A_r`, so `G206` left one cheap
escape untested: even without sign control, if injectivity forced *magnitude* suppression, i.e. the
normalized alignment `ρ_r = Cov_t(W_G, R_r) / (σ_W σ_R)` (equivalently `|ρ_r|·√q`) systematically
smaller on injective cells — then `0/1` kernel support would still be a usable *magnitude-only*
partial certificate and the injectivity route would stay alive.

This file records exact-integer cells refuting magnitude suppression in **both** directions. Writing
`M_r² = ρ_r²·q`, the exact rational value is

`M_r² = A_r² · q³ / (Q_W · Q_R)`,   with the exact integers
`A_r = q·Σ_t W_G(t) R_r(t) − n²·C(n,r)·C(n,r−1)`,
`Q_W = Σ_t (q·W_G(t) − n²)²`  (`= q³·Var W_G`),
`Q_R = Σ_t (q·R_r(t) − n²·C(n,r)·C(n,r−1))²`  (`= q³·Var R_r`).

(All three are exact integers reproduced independently by the recorded probe.)

The four recorded cells (`n = 8`, `2 ∉ G` so `φ₂` is non-degenerate) are:

* injective `F_449`: `A₅ = 449560`, `Q_W = 11063360`, `Q_R = 27405361854544`;
* injective `F_113`: `A₅ = -13128`, `Q_W = 354368`,  `Q_R = 6892278488672`
    (the same injective cell recorded in `G206`);
* non-injective `F_41`: `A₅ = 10536`,  `Q_W = 74128`,   `Q_R = 2500562364688`;
* non-injective `F_73`: `A₅ = -19616`, `Q_W = 212576`,  `Q_R = 4452321373312`.

Comparison of `M_r²` across cells is a purely decidable integer inequality after cross-multiplying:
`M_r²(a) > M_r²(b) ↔ A_a²·q_a³·Q_{W,b}·Q_{R,b} > A_b²·q_b³·Q_{W,a}·Q_{R,a}`.

The two witnesses are:

* `no_magnitude_suppression` — the injective cell `F_449` has *larger* `M₅²` than the
  non-injective cell `F_41` (`0.0603 > 0.0000413`): injectivity does **not** suppress magnitude.
* `no_magnitude_separation` — the non-injective cell `F_73` has *larger* `M₅²` than the
  injective cell `F_113` (`0.000158 > 0.000102`): the magnitude ranges *overlap*, so there is
  no separation law in the reverse direction either.

Together they give the calibrated consumer `no_magnitude_single_depth_certificate`: the normalized
alignment magnitude is provably **not** a monotone function of the injectivity flag in either
direction, so no magnitude-only partial certificate can be read off from kernel sparsity.

All alignment constants are independently reproduced by
`scripts/probes/g207_weighted_kernel_magnitude_nogo.py` (exact subgroup generation, exact integer
subset-sum histograms, exact circular correlation via the same total-mass/nonnegativity checks as
`G205/G206`, and the identity above).  This closes the last cheap escape on the injective
weighted-kernel route for magnitude, as `G206` did for sign.  CORE remains open and on the BGK wall;
the surviving object is the full signed joint two-depth cyclotomic-class covariance bound, with no
sparsity shortcut for sign or size.  FS15-FS18 remain respected.

This module is self-contained (imports only `Mathlib.Tactic.NormNum`) and introduces no `axiom`,
`sorry`, `native_decide`, or goal weakening.
-/

namespace ArkLib.ProximityGap.G207

/-- A recorded weighted-kernel cell at a fixed depth `r`: the field size `q`, the injectivity
flag of `φ₂`, and the three exact integer invariants `A_r`, `Q_W`, `Q_R`.  `Q_W` and `Q_R` are the
`q³`-scaled variances of `W_G` and `R_r`, hence positive on every non-degenerate cell. -/
structure Cell where
  /-- Field size `q` (prime, `q ≡ 1 mod n`). -/
  q : ℤ
  /-- `True` iff `φ₂ : u ↦ (2-u)^n` is injective on `G` (maximal `0/1` kernel sparsity). -/
  inj : Bool
  /-- Centered alignment `A_r = q·Σ_t W_G R_r − n²·C(n,r)·C(n,r−1)` (exact integer). -/
  A : ℤ
  /-- `Q_W = Σ_t (q·W_G(t) − n²)² = q³·Var W_G` (exact integer, `> 0`). -/
  QW : ℤ
  /-- `Q_R = Σ_t (q·R_r(t) − n²·C(n,r)·C(n,r−1))² = q³·Var R_r` (exact integer, `> 0`). -/
  QR : ℤ

/-- The squared normalized magnitude comparison, cross-multiplied to a pure integer relation:
`M²(a) > M²(b)` where `M²(c) = A_c²·q_c³/(Q_{W,c}·Q_{R,c})`.  Valid because all denominators are
positive on the recorded cells. -/
def M2gt (a b : Cell) : Prop :=
  a.A ^ 2 * a.q ^ 3 * b.QW * b.QR > b.A ^ 2 * b.q ^ 3 * a.QW * a.QR

/-! ## Recorded cells (`n = 8`, exact integers from the probe) -/

/-- Injective cell `F_449`, depth `r = 5`.  `M₅² ≈ 0.0603`. -/
def cell449 : Cell :=
  { q := 449, inj := true, A := 449560, QW := 11063360, QR := 27405361854544 }

/-- Injective cell `F_113`, depth `r = 5` (the `G206` injective cell).  `M₅² ≈ 0.000102`. -/
def cell113 : Cell :=
  { q := 113, inj := true, A := -13128, QW := 354368, QR := 6892278488672 }

/-- Non-injective cell `F_41`, depth `r = 5`.  `M₅² ≈ 0.0000413`. -/
def cell41 : Cell :=
  { q := 41, inj := false, A := 10536, QW := 74128, QR := 2500562364688 }

/-- Non-injective cell `F_73`, depth `r = 5`.  `M₅² ≈ 0.000158`. -/
def cell73 : Cell :=
  { q := 73, inj := false, A := -19616, QW := 212576, QR := 4452321373312 }

/-! ## Positivity of the recorded denominators (so `M2gt` is the genuine magnitude order) -/

theorem cell449_denom_pos : 0 < cell449.QW ∧ 0 < cell449.QR := by
  constructor <;> norm_num [cell449]

theorem cell113_denom_pos : 0 < cell113.QW ∧ 0 < cell113.QR := by
  constructor <;> norm_num [cell113]

theorem cell41_denom_pos : 0 < cell41.QW ∧ 0 < cell41.QR := by
  constructor <;> norm_num [cell41]

theorem cell73_denom_pos : 0 < cell73.QW ∧ 0 < cell73.QR := by
  constructor <;> norm_num [cell73]

/-! ## The two exact magnitude witnesses -/

/-- **No magnitude suppression.**  The injective (maximally sparse) cell `F_449` has strictly larger
normalized alignment magnitude at depth `5` than the non-injective cell `F_41`.  So `0/1` kernel
support does **not** suppress the alignment magnitude — the direction a magnitude-only partial
certificate would need. -/
theorem no_magnitude_suppression : M2gt cell449 cell41 := by
  unfold M2gt cell449 cell41
  norm_num

/-- **No reverse magnitude separation (overlap).**  The non-injective cell `F_73` has strictly
larger normalized alignment magnitude at depth `5` than the injective cell `F_113`.  Combined with
`no_magnitude_suppression`, the injective and non-injective magnitude ranges overlap: there is no
separation law in either direction. -/
theorem no_magnitude_separation : M2gt cell73 cell113 := by
  unfold M2gt cell73 cell113
  norm_num

/-! ## Calibrated consumer: magnitude is not a monotone function of injectivity -/

/-- A candidate *magnitude-only single-depth certificate* is a monotone reading of the injectivity
flag as a magnitude order: a claim that on injective cells the magnitude is bounded on one
side of the non-injective cells.  Concretely, a certificate would provide a threshold behaviour
where injective cells are uniformly smaller (suppression) or uniformly larger (separation) than
non-injective cells.
We package the strongest usable form: an assignment `bound : Bool → Cell` such that every injective
cell dominates `bound true` and is dominated by `bound false` in the `M2gt` order would let a prover
certify magnitude from the flag alone. -/
def IsMagnitudeMonotone (order : Bool → Bool → Prop) : Prop :=
  -- injective vs non-injective cells are consistently ordered by `M2gt`
  (order true false → M2gt cell41 cell449) ∧      -- "injective ⟹ smaller": would need F_41 > F_449
  (order false true → M2gt cell113 cell73)         -- "injective ⟹ larger":  would need F_113 > F_73

/-- **No magnitude single-depth certificate.**  There is no monotone reading of the injectivity flag
that certifies the alignment magnitude order.  Any purported rule "injective ⟹ magnitude on
one fixed side of non-injective" is refuted at exact integer cells: the injective→smaller
direction fails at
`(F_449 inj) > (F_41 noninj)` and the injective→larger direction fails at `(F_73 noninj) > (F_113
inj)`.  Hence kernel sparsity yields **no** magnitude-only partial certificate. -/
theorem no_magnitude_single_depth_certificate
    (order : Bool → Bool → Prop)
    (hmono : IsMagnitudeMonotone order) :
    ¬ (order true false) ∧ ¬ (order false true) := by
  obtain ⟨hsmall, hlarge⟩ := hmono
  constructor
  · intro h
    -- `order true false` would give `M2gt cell41 cell449`, contradicting `no_magnitude_suppression`
    have h1 : M2gt cell41 cell449 := hsmall h
    have h2 : M2gt cell449 cell41 := no_magnitude_suppression
    unfold M2gt cell41 cell449 at h1 h2
    omega
  · intro h
    -- `order false true` would give `M2gt cell113 cell73`, contradicting `no_magnitude_separation`
    have h1 : M2gt cell113 cell73 := hlarge h
    have h2 : M2gt cell73 cell113 := no_magnitude_separation
    unfold M2gt cell113 cell73 at h1 h2
    omega

/-! ## Axiom audit -/

#print axioms no_magnitude_suppression
#print axioms no_magnitude_separation
#print axioms no_magnitude_single_depth_certificate

end ArkLib.ProximityGap.G207
