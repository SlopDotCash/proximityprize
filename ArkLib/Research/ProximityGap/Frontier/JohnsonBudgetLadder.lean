/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability

/-!
# Line-MCA safe radii at every field size from weighted Johnson certificates

The weighted Johnson theorem bounds the exceptional challenges of a received line by an
explicit count that is linear in the block length. A certificate is a multiplicity `m` and
a jet cutoff `B` with a positive coefficient surplus. Its four moments are sums over `B + 1`
terms. Here they are put in closed form, so a certificate with a cutoff in the millions is
a constant number of integer operations.

A *rung* is a certificate together with a budget exponent `β`. A valid rung gives 128-bit
line-MCA security at its agreement count over every finite field with at least `2^(128+β)`
elements, on every injective evaluation domain. No hypothesis on the characteristic or on
the structure of the domain is used.

## Main statements

* `johnsonWeightedN_eq`, `johnsonWeightedW_eq`, `johnsonWeightedR_eq`,
  `johnsonWeightedT_eq`, `johnsonWeightedHeight_eq`: closed forms of the moments and of
  the challenge height.
* `Rung.Valid.secure`: a valid rung bounds the affine-line MCA error by `2^-128`.
* `productionRungs_valid`, `production_secure`: fifty-two rungs at length `2^30`, for the
  four prize rates and thirteen budget exponents from `36` to `96`.

The certified error counts at exponent `96` are within `100` of the Johnson counts
`314491699`, `536870913`, `694116762` and `805306370`.
-/

namespace ProximityGap.JohnsonBudgetLadder

open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions Finset

/-! ### Closed forms of the certificate moments -/

private theorem sum_range_succ_id (B : ℕ) : ∑ j ∈ range (B+1), j = B*(B+1)/2 := by
  rw [Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]

private theorem sum_range_succ_sq (B : ℕ) :
    ∑ j ∈ range (B+1), j*j = B*(B+1)*(2*B+1)/6 := by
  have h : 6 * ∑ j ∈ range (B+1), j*j = B*(B+1)*(2*B+1) := by
    induction B with
    | zero => simp
    | succ B ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring
  omega

/-- The zeroth source moment `∑_{j ≤ B} (m A - D j)` without the sum. -/
def closedN (D A m B : ℕ) : ℕ := (B+1)*(m*A) - D*(B*(B+1)/2)

/-- The first source moment `∑_{j ≤ B} j (m A - D j)` without the sum. -/
def closedW (D A m B : ℕ) : ℕ := (m*A)*(B*(B+1)/2) - D*(B*(B+1)*(2*B+1)/6)

/-- The zeroth row moment `∑_{b ≤ u} (m - b)` with `u = min B (m - 1)`, without the sum. -/
def closedR (m B : ℕ) : ℕ :=
  (min B (m-1)+1)*m - min B (m-1)*(min B (m-1)+1)/2

/-- The first row moment `∑_{b ≤ u} b (m - b)` with `u = min B (m - 1)`, without the sum. -/
def closedT (m B : ℕ) : ℕ :=
  m*(min B (m-1)*(min B (m-1)+1)/2) - min B (m-1)*(min B (m-1)+1)*(2*min B (m-1)+1)/6

/-- The challenge height `max B ⌊(W - n T) / (N - n R)⌋` in natural arithmetic. A negative
moment truncates to zero, which the maximum with `B` absorbs. -/
def closedHeight (n D A m B : ℕ) : ℕ :=
  max B ((closedW D A m B - n*closedT m B) / (closedN D A m B - n*closedR m B))

theorem johnsonWeightedN_eq {D A m B : ℕ} (h : D*B ≤ m*A) :
    johnsonWeightedN D A m B = closedN D A m B := by
  unfold johnsonWeightedN closedN
  have hfg : ∀ j ∈ range (B+1), D*j ≤ m*A := fun j hj =>
    (Nat.mul_le_mul_left D (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).trans h
  rw [Finset.sum_tsub_distrib _ hfg, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum, sum_range_succ_id]

theorem johnsonWeightedW_eq {D A m B : ℕ} (h : D*B ≤ m*A) :
    johnsonWeightedW D A m B = closedW D A m B := by
  unfold johnsonWeightedW closedW
  have hfg : ∀ j ∈ range (B+1), D*(j*j) ≤ (m*A)*j := fun j hj => by
    have h₁ : D*j ≤ m*A :=
      (Nat.mul_le_mul_left D (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).trans h
    calc D*(j*j) = (D*j)*j := by ring
      _ ≤ (m*A)*j := Nat.mul_le_mul_right j h₁
  have hterm : ∀ j ∈ range (B+1), j*(m*A - D*j) = (m*A)*j - D*(j*j) := fun j _ => by
    rw [Nat.mul_sub]
    congr 1 <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_tsub_distrib _ hfg, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_range_succ_id, sum_range_succ_sq]

theorem johnsonWeightedR_eq (m B : ℕ) : johnsonWeightedR m B = closedR m B := by
  unfold johnsonWeightedR johnsonWeightedU closedR
  have hfg : ∀ b ∈ range (min B (m-1)+1), b ≤ m := fun b hb => by
    have := Finset.mem_range.mp hb
    omega
  rw [Finset.sum_tsub_distrib _ hfg, Finset.sum_const, Finset.card_range, smul_eq_mul,
    sum_range_succ_id]

theorem johnsonWeightedT_eq (m B : ℕ) : johnsonWeightedT m B = closedT m B := by
  unfold johnsonWeightedT johnsonWeightedU closedT
  have hfg : ∀ b ∈ range (min B (m-1)+1), b*b ≤ m*b := fun b hb => by
    have := Finset.mem_range.mp hb
    exact Nat.mul_le_mul_right b (by omega)
  have hterm : ∀ b ∈ range (min B (m-1)+1), b*(m-b) = m*b - b*b := fun b _ => by
    rw [Nat.mul_sub, Nat.mul_comm b m]
  rw [Finset.sum_congr rfl hterm, Finset.sum_tsub_distrib _ hfg, ← Finset.mul_sum,
    sum_range_succ_id, sum_range_succ_sq]

theorem johnsonWeightedHeight_eq {n D A m B : ℕ} (h : D*B ≤ m*A)
    (hslope : n*closedR m B < closedN D A m B) :
    johnsonWeightedHeight n D A m B = closedHeight n D A m B := by
  unfold johnsonWeightedHeight johnsonWeightedHeightInt johnsonWeightedMoment
    johnsonWeightedSlope closedHeight
  rw [johnsonWeightedN_eq h, johnsonWeightedW_eq h, johnsonWeightedR_eq, johnsonWeightedT_eq]
  generalize closedN D A m B = N at hslope ⊢
  generalize closedW D A m B = W
  generalize closedR m B = R at hslope ⊢
  generalize closedT m B = T
  have hs : ((N:ℤ) - (n:ℤ)*(R:ℤ)) = ((N - n*R : ℕ) : ℤ) := by
    rw [Nat.cast_sub hslope.le]
    push_cast
    ring
  rw [hs]
  rcases le_or_gt (n*T) W with hW | hW
  · have hm : ((W:ℤ) - (n:ℤ)*(T:ℤ)) = ((W - n*T : ℕ) : ℤ) := by
      rw [Nat.cast_sub hW]
      push_cast
      ring
    rw [hm, ← Int.natCast_div, ← Nat.cast_max, Int.toNat_natCast]
  · have hneg : ((W:ℤ) - (n:ℤ)*(T:ℤ)) < 0 := by
      have : (W:ℤ) < (n:ℤ)*(T:ℤ) := by exact_mod_cast hW
      omega
    have hpos : (0:ℤ) < ((N - n*R : ℕ) : ℤ) := by exact_mod_cast Nat.sub_pos_of_lt hslope
    have hq : ((W:ℤ) - (n:ℤ)*(T:ℤ)) / ((N - n*R : ℕ) : ℤ) < 0 :=
      Int.ediv_neg_of_neg_of_pos hneg hpos
    rw [max_eq_left (by omega), Int.toNat_natCast, Nat.sub_eq_zero_of_le hW.le, Nat.zero_div,
      max_eq_left (Nat.zero_le B)]

/-! ### Rungs -/

/-- A weighted Johnson certificate at dimension `k` and agreement `A`, with multiplicity `m`,
jet cutoff `B` and height `H`, together with the exponent `β` of a bound `2^β` on its
exceptional count. -/
structure Rung where
  /-- Dimension of the code. -/
  k : ℕ
  /-- Agreement count. -/
  A : ℕ
  /-- Multiplicity. -/
  m : ℕ
  /-- Jet cutoff. -/
  B : ℕ
  /-- Challenge height. -/
  H : ℕ
  /-- Exponent of the bound on the exceptional count. -/
  β : ℕ

/-- The arithmetic conditions under which a rung certifies its agreement count at length `n`.
The last inequality is the exceptional-count bound `E ≤ 2^β` cleared of its denominator. -/
def Rung.Valid (n : ℕ) (r : Rung) : Prop :=
  2 ≤ r.k ∧ r.k ≤ r.A ∧ r.A ≤ n ∧ 1 ≤ r.m ∧ 1 ≤ r.B ∧ r.B ≤ 2*(r.k-1)+1 ∧
  (r.k-1)*r.B < r.m*r.A ∧
  n*closedR r.m r.B < closedN (r.k-1) r.A r.m r.B ∧
  r.H = closedHeight n (r.k-1) r.A r.m r.B ∧
  ((2*r.B-1)*r.H + (n-(r.k-1)-1)*r.B)*(r.A-(r.k-1)) +
      (n-(r.k-1))*(r.H + r.B + (2*(r.k-1)-1)*r.H*(2*r.B-1)) ≤ 2^r.β*(r.A-(r.k-1))

instance (n : ℕ) (r : Rung) : Decidable (r.Valid n) := by
  unfold Rung.Valid
  infer_instance

/-- A valid rung is a weighted Johnson certificate in the upstream sense. -/
theorem Rung.Valid.certificate {n : ℕ} {r : Rung} (h : r.Valid n) :
    IsJohnsonWeightedCertificate n (r.k-1) r.A r.m r.B r.H := by
  obtain ⟨-, -, -, hm, hB, -, hcut, hslope, hH, -⟩ := h
  refine ⟨hm, hB, hcut, ?_, ?_⟩
  · rw [johnsonWeightedR_eq, johnsonWeightedN_eq hcut.le]
    exact hslope
  · rw [johnsonWeightedHeight_eq hcut.le hslope]
    exact hH

/-- The refined exceptional count of a valid rung is at most `2^β`. -/
theorem Rung.Valid.exception_le {n : ℕ} {r : Rung} (h : r.Valid n) :
    johnsonWeightedRefinedExceptionCount n (r.k-1) r.A r.B r.H ≤ 2^r.β := by
  obtain ⟨hk, hkA, -, -, -, -, -, -, -, hE⟩ := h
  have hpos : (0:ℚ) < ((r.A-(r.k-1) : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < r.A-(r.k-1) by omega)
  have key : johnsonWeightedRefinedExceptionCount n (r.k-1) r.A r.B r.H =
      ((((2*r.B-1)*r.H + (n-(r.k-1)-1)*r.B)*(r.A-(r.k-1)) +
        (n-(r.k-1))*(r.H + r.B + (2*(r.k-1)-1)*r.H*(2*r.B-1)) : ℕ) : ℚ) /
          ((r.A-(r.k-1) : ℕ) : ℚ) := by
    unfold johnsonWeightedRefinedExceptionCount
    push_cast
    field_simp
    ring
  rw [key, div_le_iff₀ hpos]
  exact_mod_cast hE

/-- A valid rung gives 128-bit line-MCA security at closed radius `1 - A/n`, over every
finite field with at least `2^(128+β)` elements and on every injective evaluation domain. -/
theorem Rung.Valid.secure {n : ℕ} {r : Rung} (h : r.Valid n) {F : Type} [Field F] [Fintype F]
    [SampleableType F] (hF : 2^(128+r.β) ≤ Fintype.card F) (dom : Fin n ↪ F) {δ : ℝ}
    (hδ : δ ≤ 1 - (r.A:ℝ)/n) :
    mcaError (AffineLineGenerator F) (code dom r.k) δ ≤ ENNReal.ofReal (1/(2:ℝ)^128) := by
  have hk : 2 ≤ r.k := h.1
  have hkA : r.k ≤ r.A := h.2.1
  have hAn : r.A ≤ n := h.2.2.1
  have hBD : r.B ≤ 2*(r.k-1)+1 := h.2.2.2.2.2.1
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hth : r.A ≤ ⌈(n:ℝ)*(1-δ)⌉₊ := by
    calc r.A = ⌈((r.A:ℕ):ℝ)⌉₊ := (Nat.ceil_natCast (R := ℝ) _).symm
      _ ≤ _ := Nat.ceil_mono (by
        have hA : (r.A:ℝ) ≤ (1-δ)*n := (div_le_iff₀ hnR).mp (by linarith)
        linarith)
  have hmain := mcaError_affineLine_weightedJohnson_le dom h.certificate (by omega) (by omega)
    hBD δ hth
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r.k)] at hmain
  refine hmain.trans ((min_le_right _ _).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have hq : (0:ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ hq (by positivity)]
  have hE : ((johnsonWeightedRefinedExceptionCount n (r.k-1) r.A r.B r.H : ℚ) : ℝ) ≤
      (2:ℝ)^r.β := by exact_mod_cast h.exception_le
  have hF' : (2:ℝ)^128 * (2:ℝ)^r.β ≤ Fintype.card F := by
    rw [← pow_add]
    exact_mod_cast hF
  nlinarith [mul_le_mul_of_nonneg_right hE (by positivity : (0:ℝ) ≤ (2:ℝ)^128)]

/-! ### The ladder at length `2^30` -/

/-- Fifty-two rungs at length `2^30`: for each exponent `β` in
`36, 38, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96`, one rung at each of the dimensions
`2^29`, `2^28`, `2^27` and `2^26`. -/
def productionRungs : List Rung := [
  ⟨536870912, 809436144, 1, 1, 32, 36⟩, ⟨268435456, 632740718, 2, 3, 11, 36⟩,
  ⟨134217728, 483183820, 1, 3, 18, 36⟩, ⟨67108864, 364507091, 1, 4, 20, 36⟩,
  ⟨536870912, 800832444, 3, 4, 17, 38⟩, ⟨268435456, 597588455, 3, 6, 18, 38⟩,
  ⟨134217728, 443740243, 2, 6, 30, 38⟩, ⟨67108864, 326934125, 2, 9, 30, 38⟩,
  ⟨536870912, 787677771, 5, 7, 36, 40⟩, ⟨268435456, 576017749, 4, 8, 51, 40⟩,
  ⟨134217728, 419537945, 4, 12, 53, 40⟩, ⟨67108864, 305133330, 4, 16, 61, 40⟩,
  ⟨536870912, 771039427, 13, 18, 204, 44⟩, ⟨268435456, 552579357, 12, 24, 245, 44⟩,
  ⟨134217728, 395422598, 11, 31, 298, 44⟩, ⟨67108864, 282712840, 10, 41, 345, 44⟩,
  ⟨536870912, 764044098, 34, 48, 1167, 48⟩, ⟨268435456, 543143957, 31, 62, 1453, 48⟩,
  ⟨134217728, 385879738, 29, 82, 1722, 48⟩, ⟨67108864, 274060575, 26, 105, 2062, 48⟩,
  ⟨536870912, 761164849, 85, 120, 7331, 52⟩, ⟨268435456, 539364921, 80, 160, 8846, 52⟩,
  ⟨134217728, 382103221, 73, 207, 10717, 52⟩, ⟨67108864, 270660568, 67, 269, 12634, 52⟩,
  ⟨536870912, 760012142, 218, 308, 45353, 56⟩, ⟨268435456, 537861339, 202, 404, 55643, 56⟩,
  ⟨134217728, 380608005, 188, 532, 66224, 56⟩, ⟨67108864, 269317315, 171, 685, 78775, 56⟩,
  ⟨536870912, 759552892, 551, 779, 286038, 60⟩, ⟨268435456, 537264063, 511, 1022, 350892, 60⟩,
  ⟨134217728, 380015046, 470, 1330, 422581, 60⟩, ⟨67108864, 268785235, 431, 1725, 498973, 60⟩,
  ⟨536870912, 759370333, 1384, 1957, 1819526, 64⟩,
  ⟨268435456, 537026949, 1288, 2576, 2224789, 64⟩,
  ⟨134217728, 379779812, 1186, 3355, 2677136, 64⟩,
  ⟨67108864, 268574235, 1087, 4349, 3162777, 64⟩,
  ⟨536870912, 759269061, 8800, 12445, 73197565, 72⟩,
  ⟨268435456, 536895487, 8170, 16340, 89729468, 72⟩,
  ⟨134217728, 379649432, 7520, 21270, 108031540, 72⟩,
  ⟨67108864, 268457309, 6864, 27457, 128159002, 72⟩,
  ⟨536870912, 759253107, 55397, 78343, 2976353139, 80⟩,
  ⟨268435456, 536874782, 51422, 102844, 3649224462, 80⟩,
  ⟨134217728, 379628900, 47262, 133678, 4399911812, 80⟩,
  ⟨67108864, 268438896, 43530, 174121, 5172783508, 80⟩,
  ⟨536870912, 759250594, 353489, 499909, 119410580657, 88⟩,
  ⟨268435456, 536871521, 321834, 643668, 149239787421, 88⟩,
  ⟨134217728, 379625666, 296500, 838629, 179514362354, 88⟩,
  ⟨67108864, 268435997, 267250, 1069001, 215645934036, 88⟩,
  ⟨536870912, 759250199, 2191876, 3099780, 4789979957073, 96⟩,
  ⟨268435456, 536871008, 2191876, 4383752, 5483610685215, 96⟩,
  ⟨134217728, 379625157, 1772178, 5012477, 7684764909404, 96⟩,
  ⟨67108864, 268435540, 1753501, 7014005, 8231083334507, 96⟩]

/-- Every production rung satisfies the certificate arithmetic at length `2^30`. -/
theorem productionRungs_valid : ∀ r ∈ productionRungs, r.Valid (2^30) := by
  decide +kernel

/-- At length `2^30`, every production rung gives 128-bit line-MCA security at closed radius
`1 - A/2^30` over every finite field with at least `2^(128+β)` elements. -/
theorem production_secure {F : Type} [Field F] [Fintype F] [SampleableType F]
    (dom : Fin (2^30) ↪ F) {r : Rung} (hr : r ∈ productionRungs)
    (hF : 2^(128+r.β) ≤ Fintype.card F) {δ : ℝ} (hδ : δ ≤ 1 - (r.A:ℝ)/2^30) :
    mcaError (AffineLineGenerator F) (code dom r.k) δ ≤ ENNReal.ofReal (1/(2:ℝ)^128) :=
  (productionRungs_valid r hr).secure hF dom (by rw [Nat.cast_pow, Nat.cast_ofNat]; exact hδ)

end ProximityGap.JohnsonBudgetLadder

#print axioms ProximityGap.JohnsonBudgetLadder.johnsonWeightedHeight_eq

#print axioms ProximityGap.JohnsonBudgetLadder.Rung.Valid.secure

#print axioms ProximityGap.JohnsonBudgetLadder.production_secure
