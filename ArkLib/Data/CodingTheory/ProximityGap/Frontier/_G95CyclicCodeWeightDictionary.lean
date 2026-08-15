/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnIndicatorDisjointness

/-!
# G95 — the irreducible-cyclic-code weight-distribution dictionary at the prize shape (#466)

**Lane.** The 60-year coding-theory literature on weight distributions of irreducible cyclic
codes (McEliece 1974 "Irreducible cyclic codes and Gauss sums"; Baumert–McEliece 1972;
Delsarte–Goethals / the semiprimitive two-weight case; Aoki's exact evaluations of Gauss sums
of 2-power order; the Schmidt–White 2002 few-weight classification; Ding–Yang's survey) is a
dictionary: **the weights of the irreducible cyclic code `C(q, N)` are affine functions of the
Gauss periods** of the subgroup `H = μ_{(q^s-1)/N} · F_q^×` of the *extension field* `F_{q^s}`.
The campaign's CORE object is the Gauss-period family `η_b = ∑_{x∈μ_n} ψ(bx)` over the *prime*
field `F_p` (`n = 2^30`, `p ≈ n^4`, index `m = (p-1)/n = 2^128`).

**The orientation finding (this file makes it a theorem).** The literature dictionary requires
the period subgroup to contain `F_q^×` (equivalently: to be Galois/Frobenius-stable), which
forces the periods to be *rational integers* and allows few-valued collapses — the
semiprimitive two-weight distributions, Aoki's clean `p^j ≡ -1` case, and every entry of the
Schmidt–White classification live there. Over the prime field the cyclotomic Galois action is
the *full* dilation action, no collapse is possible, and the value distribution is provably at
the **opposite extreme**:

* `eta_eq_iff_mem_coset` — **the exact dictionary**: `η_b = η_c ⟺ c ∈ b·μ_n`. The value
  multiset `{η_b : b ∈ F_p^×}` is *exactly* the multiplicity-`n` repetition of `m = (p-1)/n`
  **pairwise distinct** values (`value_fiber_card`, `card_values_mul`, `card_values`). At the
  prize point: `2^128` distinct real values. This is the unconditional prime-field form of
  Katz's "generic irreducible cyclic codes are many-valued" — with *exact* count, no
  genericity.
* `few_weight_no_go` — the semiprimitive/two-valued regime `#values ≤ 2` forces
  `p - 1 ≤ 2n`; at the prize shape (`p - 1 = 2^128·n`) it misses by 127 binary orders of
  magnitude. **No exact evaluation from the few-weight literature can apply to the prize
  object** — now a theorem, not a heuristic (this explains the campaign log's `McEliece: 0
  hits`).
* `eta_not_rational` — **the McEliece-quantization no-go**: every nonzero-frequency period is
  irrational (`η_b ∉ ℚ` for `b ≠ 0`, `n + 1 < p`). The literature's integer-lattice
  quantization of weights (`weight ∈ baseline + 2^k·ℤ`, McEliece's divisibility theorem via
  Stickelberger) **cannot transfer to the period values themselves**: they lie in no rational
  lattice. Any "affine integer dictionary" for the prize family is dead on arrival.
* Where the integrality mechanism *does* transfer: the **power sums of the distinct-value
  set** are explicit integers. `card_smul_sum_values_pow` welds the value distribution to the
  in-tree relation-count `N₀` (`SubgroupGaussSumRawMoment`):
  `n · ∑_{v ∈ values} v^r = p·N₀(μ_n, r) - n^r`. Corollaries: `sum_values = -1`
  (`e₁` of the period polynomial), `sum_values_sq = p - n` (the second moment of the
  distinct-value set — the "weight-enumerator" Parseval), and the **dyadic McEliece
  divisibility transfer** `sum_values_pow_of_vanishing`: below the wraparound depth
  (`N₀(μ_n, r) = 0`, e.g. every odd `r < ` char-p onset by Lam–Leung antipodality),
  `∑_v v^r = -n^{r-1}` **exactly** — so `v₂(P_r) = (r-1)·log₂ n`, the exact power of 2, probe-
  confirmed at `n = 8,16,32,64` (`P₃ = -n²` at all four scales).

**Probe** (`probe_g95_cyclic_dictionary.py`, session scratchpad; summary in the DISPROOF_LOG
candidate entry): value multiset verified *exactly* `m` distinct / multiplicity `n` at
`n = 8,16,32` (β=4 prize-representative primes; `n = 64` float-limited but all integer
identities exact); `P₁ = -1`, `P₂ = p-n`, `P₃ = -n²` exact at all scales; the extension-field
contrast `F_16`/index-5 (semiprimitive `2² ≡ -1 mod 5`) collapses to the two values `{-1, 3}`
across 5 cosets — confirming few-valuedness is an extension-field (Frobenius-collapse)
phenomenon, impossible over `F_p`.

**Honest scope.** These are structure theorems for the value *distribution*; they do **not**
bound `M(μ_n) = max_b |η_b|`. Distinctness has no archimedean content (conjugate spacings span
5 orders of magnitude in the probe), and the discriminant/house route is already refuted
(C08/C26/C46). The CORE inequality stays open.

## References
- R.J. McEliece, *Irreducible cyclic codes and Gauss sums*, 1974.
- L.D. Baumert, R.J. McEliece, *Weights of irreducible cyclic codes*, Inform. Control 20, 1972.
- N. Aoki, *On the evaluation of Gauss sums of 2-power order* (semiprimitive case clean).
- B. Schmidt, C. White, *All two-weight irreducible cyclic codes?*, Finite Fields Appl. 8, 2002.
- C. Ding, J. Yang, *The weight distributions of irreducible cyclic codes*, 2013.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset AddChar

namespace ArkLib.ProximityGap.G95CyclicCodeWeightDictionary

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment

variable {p : ℕ} [hp : Fact p.Prime] {ψ : AddChar (ZMod p) ℂ}

/-! ## 1. The bridge: a primitive additive character of `ZMod p` is `e ↦ ζ^e` for a primitive
`p`-th root of unity `ζ = ψ 1`. This wires the substrate object `eta ψ G b` to the prime-root
rigidity engine of `DeBruijnIndicatorDisjointness`. -/

/-- Every additive character of `ZMod p` is determined by its value at `1`:
`ψ x = (ψ 1)^(x.val)`. -/
theorem psi_apply_eq_pow (ψ : AddChar (ZMod p) ℂ) (x : ZMod p) :
    ψ x = ψ 1 ^ x.val := by
  have hx : x = x.val • (1 : ZMod p) := by
    rw [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val x).symm
  conv_lhs => rw [hx]
  rw [AddChar.map_nsmul_eq_pow]

/-- For a primitive `ψ`, the value `ζ = ψ 1` is a primitive `p`-th root of unity. -/
theorem isPrimitiveRoot_psi_one (hψ : ψ.IsPrimitive) : IsPrimitiveRoot (ψ 1) p := by
  constructor
  · rw [← AddChar.map_nsmul_eq_pow]
    have hp1 : p • (1 : ZMod p) = 0 := by
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
    rw [hp1, AddChar.map_zero_eq_one]
  · intro l hl
    have hpsil : ψ ((l : ZMod p)) = 1 := by
      have hcast : ((l : ZMod p)) = l • (1 : ZMod p) := by rw [nsmul_eq_mul, mul_one]
      rw [hcast, AddChar.map_nsmul_eq_pow, hl]
    exact (ZMod.natCast_eq_zero_iff l p).mp ((hψ.zmod_char_eq_one_iff p _).mp hpsil)

/-- Indicator sums of `ψ` over subsets of `ZMod p` are indicator sums of powers of `ζ = ψ 1`
indexed by the `val`-image. -/
theorem sum_psi_eq (ψ : AddChar (ZMod p) ℂ) (A : Finset (ZMod p)) :
    ∑ x ∈ A, ψ x = ∑ e ∈ A.image ZMod.val, ψ 1 ^ e := by
  rw [Finset.sum_image (fun x _ y _ h => ZMod.val_injective p h)]
  exact Finset.sum_congr rfl fun x _ => psi_apply_eq_pow ψ x

/-! ## 2. Prime-field root-sum rigidity: an equal-cardinality pair of subsets of `ZMod p` with
equal `ψ`-sums is *equal*. This is the integrality mechanism of the weight-distribution
literature ("weights are integers") transferred to the prime field: the only ℚ-relation among
`p`-th roots is the all-ones relation. -/

/-- **Root-sum rigidity.** If `A.card = B.card` and `∑_{x∈A} ψ x = ∑_{x∈B} ψ x`, then `A = B`.
Consumes the in-tree indicator dichotomy (`DeBruijnIndicatorDisjointness`); the degenerate
complementary branches are killed by the cardinality hypothesis. -/
theorem sum_psi_inj (hψ : ψ.IsPrimitive) {A B : Finset (ZMod p)}
    (hcard : A.card = B.card) (hsum : ∑ x ∈ A, ψ x = ∑ x ∈ B, ψ x) : A = B := by
  have hzeta := isPrimitiveRoot_psi_one hψ
  have hX : A.image ZMod.val ⊆ Finset.range p := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  have hY : B.image ZMod.val ⊆ Finset.range p := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  have hsum' : ∑ j ∈ A.image ZMod.val, ψ 1 ^ j = ∑ j ∈ B.image ZMod.val, ψ 1 ^ j := by
    rw [← sum_psi_eq, ← sum_psi_eq]; exact hsum
  rcases DeBruijnIndicatorDisjointness.equal_indicator_sums_dichotomy hp.out hzeta hX hY hsum'
    with h | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact Finset.image_injective (ZMod.val_injective p) h
  · exfalso
    have hAcard : A.card = p := by
      have h1 := Finset.card_image_of_injective A (ZMod.val_injective p)
      rw [hA, Finset.card_range] at h1
      omega
    have hBcard : B.card = 0 := by
      have h1 := Finset.card_image_of_injective B (ZMod.val_injective p)
      rw [hB, Finset.card_empty] at h1
      omega
    exact hp.out.ne_zero (by omega)
  · exfalso
    have hAcard : A.card = 0 := by
      have h1 := Finset.card_image_of_injective A (ZMod.val_injective p)
      rw [hA, Finset.card_empty] at h1
      omega
    have hBcard : B.card = p := by
      have h1 := Finset.card_image_of_injective B (ZMod.val_injective p)
      rw [hB, Finset.card_range] at h1
      omega
    exact hp.out.ne_zero (by omega)

/-! ## 3. Dilation cosets and the exact dictionary. -/

/-- `η_b` as an indicator `ψ`-sum over the dilated set `b·G`. -/
theorem eta_eq_sum_image {G : Finset (ZMod p)} {b : ZMod p} (hb : b ≠ 0) :
    eta ψ G b = ∑ y ∈ G.image (fun x => b * x), ψ y := by
  rw [Finset.sum_image (fun x _ y _ h => mul_left_cancel₀ hb h)]
  rfl

/-- **Period equality = dilate equality** (any ground set `G`, no subgroup structure needed):
`η_b = η_c ⟺ b·G = c·G`. -/
theorem eta_eq_iff_image_eq (hψ : ψ.IsPrimitive) {G : Finset (ZMod p)} {b c : ZMod p}
    (hb : b ≠ 0) (hc : c ≠ 0) :
    eta ψ G b = eta ψ G c ↔ G.image (fun x => b * x) = G.image (fun x => c * x) := by
  constructor
  · intro h
    refine sum_psi_inj hψ ?_ ?_
    · rw [Finset.card_image_of_injective G (mul_right_injective₀ hb),
        Finset.card_image_of_injective G (mul_right_injective₀ hc)]
    · rw [← eta_eq_sum_image hb, ← eta_eq_sum_image hc]; exact h
  · intro h
    rw [eta_eq_sum_image hb, eta_eq_sum_image hc, h]

section SubgroupLayer

variable {G : Finset (ZMod p)}

/-- Elements of a `0`-avoiding set are nonzero. -/
theorem ne_zero_of_mem (h0 : (0 : ZMod p) ∉ G) {x : ZMod p} (hx : x ∈ G) : x ≠ 0 :=
  fun h => h0 (h ▸ hx)

/-- Multiplicative closure absorbs dilation by members: `u·G = G` for `u ∈ G`. -/
theorem image_mul_mem (h0 : (0 : ZMod p) ∉ G)
    (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) {u : ZMod p} (hu : u ∈ G) :
    G.image (fun x => u * x) = G := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hmul u hu x hx
  · exact (Finset.card_image_of_injective G
      (mul_right_injective₀ (ne_zero_of_mem h0 hu))).ge

/-- Dilate equality is coset membership: `b·G = c·G ⟺ c ∈ b·G`. -/
theorem coset_eq_iff_mem (h1 : (1 : ZMod p) ∈ G) (h0 : (0 : ZMod p) ∉ G)
    (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) {b c : ZMod p} :
    G.image (fun x => b * x) = G.image (fun x => c * x) ↔ c ∈ G.image (fun x => b * x) := by
  constructor
  · intro h
    rw [h]
    exact Finset.mem_image.mpr ⟨1, h1, mul_one c⟩
  · intro h
    obtain ⟨u, hu, huc⟩ := Finset.mem_image.mp h
    have hcomp : (fun x => c * x) = (fun x => b * x) ∘ (fun x => u * x) := by
      funext x
      simp only [Function.comp_apply]
      rw [← huc, mul_assoc]
    rw [hcomp, ← Finset.image_image, image_mul_mem h0 hmul hu]

/-- **THE DICTIONARY (exact form).** For a multiplicatively closed `G ∌ 0` with `1 ∈ G` (the
subgroup `μ_n` as a finset) and nonzero frequencies `b, c`:
`η_b = η_c ⟺ c ∈ b·G`. The period value determines the coset *exactly* — the prime-field
weight-distribution statement, with no Frobenius collapse possible. -/
theorem eta_eq_iff_mem_coset (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    {b c : ZMod p} (hb : b ≠ 0) (hc : c ≠ 0) :
    eta ψ G b = eta ψ G c ↔ c ∈ G.image (fun x => b * x) := by
  rw [eta_eq_iff_image_eq hψ hb hc, coset_eq_iff_mem h1 h0 hmul]

/-! ## 4. The value distribution: exactly `(p-1)/n` distinct values, each of multiplicity `n`.
This is the "weight distribution" of the prize family, and it is maximally many-valued. -/

/-- The `η`-value fiber through `b ≠ 0` is exactly the coset `b·G`. -/
theorem value_fiber_eq_coset (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    {b : ZMod p} (hb : b ≠ 0) :
    (Finset.univ.filter fun c : ZMod p => c ≠ 0 ∧ eta ψ G c = eta ψ G b)
      = G.image (fun x => b * x) := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc, hval⟩
    exact (eta_eq_iff_mem_coset hψ h1 h0 hmul hb hc).mp hval.symm
  · intro hc
    obtain ⟨u, hu, huc⟩ := Finset.mem_image.mp hc
    have hcne : c ≠ 0 := by
      rw [← huc]
      exact mul_ne_zero hb (ne_zero_of_mem h0 hu)
    exact ⟨hcne, ((eta_eq_iff_mem_coset hψ h1 h0 hmul hb hcne).mpr hc).symm⟩

open scoped Classical in
/-- **Multiplicity is exactly `n`**: each attained value has exactly `G.card` frequencies. -/
theorem value_fiber_card (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    {b : ZMod p} (hb : b ≠ 0) :
    ((Finset.univ.filter fun c : ZMod p => c ≠ 0).filter
        fun c => eta ψ G c = eta ψ G b).card = G.card := by
  rw [Finset.filter_filter, value_fiber_eq_coset hψ h1 h0 hmul hb,
    Finset.card_image_of_injective G (mul_right_injective₀ hb)]

open scoped Classical in
/-- **The value count, exactly**: `#{distinct values} · n = p - 1`. The value multiset of the
prize family is the multiplicity-`n` repetition of exactly `(p-1)/n` pairwise distinct
values. -/
theorem card_values_mul (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) :
    ((Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G)).card * G.card = p - 1 := by
  have hbase := Finset.card_eq_sum_card_image (eta ψ G)
    (Finset.univ.filter fun c : ZMod p => c ≠ 0)
  have hfib : ∀ v ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G),
      ((Finset.univ.filter fun c : ZMod p => c ≠ 0).filter fun c => eta ψ G c = v).card
        = G.card := by
    intro v hv
    obtain ⟨b, hbs, rfl⟩ := Finset.mem_image.mp hv
    exact value_fiber_card hψ h1 h0 hmul (Finset.mem_filter.mp hbs).2
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hbase
  have hscard : (Finset.univ.filter fun c : ZMod p => c ≠ 0).card = p - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  rw [hscard] at hbase
  exact hbase.symm

open scoped Classical in
/-- The distinct-value count is exactly the index `(p-1)/n`. At the prize point: `2^128`
distinct real values — the maximally-many-valued extreme of the weight-distribution
dictionary. -/
theorem card_values (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) :
    ((Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G)).card = (p - 1) / G.card := by
  have h := card_values_mul hψ h1 h0 hmul
  have hpos : 0 < G.card := Finset.card_pos.mpr ⟨1, h1⟩
  exact (Nat.div_eq_of_eq_mul_left hpos h.symm).symm

open scoped Classical in
/-- **The few-weight no-go (anti-Schmidt–White orientation pin).** A two-valued (semiprimitive-
style) distribution forces `p - 1 ≤ 2n`. At the prize shape `p - 1 = 2^128 · n`, the entire
few-weight literature (Baumert–McEliece exact evaluations, Aoki's semiprimitive case, every
Schmidt–White entry) is excluded by 127 binary orders of magnitude. -/
theorem few_weight_no_go (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hshape : 2 * G.card < p - 1) :
    2 < ((Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G)).card := by
  by_contra hle
  have hle' : ((Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G)).card ≤ 2 :=
    Nat.le_of_not_lt hle
  have h := card_values_mul hψ h1 h0 hmul
  have hmulle := Nat.mul_le_mul_right G.card hle'
  omega

/-! ## 5. The McEliece-quantization no-go: every nonzero-frequency period is irrational.
The literature's `weight ∈ baseline + 2^k·ℤ` lattice quantization cannot transfer to the
prime-field period values. -/

/-- **Irrationality of the periods.** For `b ≠ 0` and `G.card + 1 < p`, the period `η_b` is
not a rational number. Hence the value set lies in *no* rational lattice `α + β·ℤ`
(`α, β ∈ ℚ`): the McEliece/Stickelberger integer-quantization mechanism has no prime-field
analogue at the level of individual values. -/
theorem eta_not_rational (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    {b : ZMod p} (hb : b ≠ 0)
    (hsmall : G.card + 1 < p) (q : ℚ) : eta ψ G b ≠ (q : ℂ) := by
  intro heq
  have hzeta := isPrimitiveRoot_psi_one hψ
  set A : Finset (ZMod p) := G.image (fun x => b * x) with hA
  set X : Finset ℕ := A.image ZMod.val with hX
  set a : ℕ → ℚ := fun e => (if e ∈ X then (1 : ℚ) else 0) - (if e = 0 then q else 0) with ha
  have hXsub : X ⊆ Finset.range p := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  have hXcard : X.card = G.card := by
    rw [hX, Finset.card_image_of_injective A (ZMod.val_injective p), hA,
      Finset.card_image_of_injective G (mul_right_injective₀ hb)]
  have hbA : b ∈ A := Finset.mem_image.mpr ⟨1, h1, mul_one b⟩
  have hbX : b.val ∈ X := Finset.mem_image_of_mem _ hbA
  have hbval : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
  -- the vanishing ℚ-relation among the p-th roots
  have hsum : ∑ e ∈ Finset.range p, a e • (ψ 1) ^ e = 0 := by
    have hterm : ∀ e, a e • (ψ 1) ^ e
        = (if e ∈ X then (ψ 1) ^ e else 0) - (if e = 0 then q • (ψ 1) ^ e else 0) := by
      intro e
      rw [ha]
      simp only [sub_smul, ite_smul, one_smul, zero_smul]
    calc ∑ e ∈ Finset.range p, a e • (ψ 1) ^ e
        = (∑ e ∈ Finset.range p, if e ∈ X then (ψ 1) ^ e else 0)
            - ∑ e ∈ Finset.range p, if e = 0 then q • (ψ 1) ^ e else 0 := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun e _ => hterm e
      _ = (q : ℂ) - (q : ℂ) := by
          congr 1
          · rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hXsub, ← sum_psi_eq,
              ← eta_eq_sum_image hb, heq]
          · rw [Finset.sum_ite_eq' (Finset.range p) 0 (fun e => q • (ψ 1) ^ e)]
            rw [if_pos (Finset.mem_range.mpr hp.out.pos)]
            rw [pow_zero, Rat.smul_def, mul_one]
      _ = 0 := sub_self _
  -- a frequency outside X ∪ {0} exists
  have hcard2 : (insert 0 X).card < (Finset.range p).card := by
    calc (insert 0 X).card ≤ X.card + 1 := Finset.card_insert_le 0 X
      _ = G.card + 1 := by rw [hXcard]
      _ < p := hsmall
      _ = (Finset.range p).card := (Finset.card_range p).symm
  obtain ⟨e₂, he₂r, he₂⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard2
  have he₂0 : e₂ ≠ 0 := fun h => he₂ (h ▸ Finset.mem_insert_self 0 X)
  have he₂X : e₂ ∉ X := fun h => he₂ (Finset.mem_insert_of_mem h)
  -- constant coefficients force 1 = 0
  have hkey := DeBruijnIndicatorDisjointness.coeffs_all_eq_of_vanishing_prime hp.out hzeta hsum
    (ZMod.val_lt b) (Finset.mem_range.mp he₂r)
  rw [ha] at hkey
  simp only [if_pos hbX, if_neg hbval, if_neg he₂X, if_neg he₂0, sub_zero] at hkey
  norm_num at hkey

/-! ## 6. The transferred integrality: power sums of the distinct-value set are integers,
welded to the in-tree relation count `N₀`. -/

/-- `η_0 = n` (the DC frequency sees the bare cardinality). -/
theorem eta_zero_eq (ψ : AddChar (ZMod p) ℂ) (G : Finset (ZMod p)) :
    eta ψ G (0 : ZMod p) = (G.card : ℂ) := by
  show ∑ y ∈ G, ψ (0 * y) = (G.card : ℂ)
  simp [AddChar.map_zero_eq_one]

/-- The raw `r`-th moment over the `p - 1` nonzero frequencies:
`∑_{b≠0} η_b^r = p·N₀(G,r) - n^r`. -/
theorem sum_nonzero_eta_pow (hψ : ψ.IsPrimitive) (G : Finset (ZMod p)) (r : ℕ) :
    ∑ b ∈ Finset.univ.filter (fun c : ZMod p => c ≠ 0), eta ψ G b ^ r
      = (p : ℂ) * N0 G r - (G.card : ℂ) ^ r := by
  have hall := subgroup_gaussSum_rawMoment hψ G r
  have hcast : (Fintype.card (ZMod p) : ℂ) = (p : ℂ) := by rw [ZMod.card]
  rw [hcast] at hall
  have hsplit := Finset.sum_erase_add Finset.univ (fun b => eta ψ G b ^ r)
    (Finset.mem_univ (0 : ZMod p))
  rw [Finset.filter_ne']
  have := eq_sub_of_add_eq hsplit
  rw [this, hall]
  congr 1
  show eta ψ G (0 : ZMod p) ^ r = (G.card : ℂ) ^ r
  rw [eta_zero_eq]

open scoped Classical in
/-- **The power-sum dictionary bridge**: `n · ∑_{v ∈ values} v^r = p·N₀(G,r) - n^r`. The
left side is `n` times the `r`-th power sum of the *distinct-value* set (the weight-enumerator
power sums of the dictionary); the right side is exact integer data from the in-tree relation
count. This is the transfer of "weights are integers": the value multiset is quantized at the
level of its symmetric functions, not its individual values. -/
theorem card_smul_sum_values_pow (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) (r : ℕ) :
    (G.card : ℂ) * ∑ v ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G), v ^ r
      = (p : ℂ) * N0 G r - (G.card : ℂ) ^ r := by
  rw [← sum_nonzero_eta_pow hψ G r]
  have hmaps : ∀ b ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0),
      eta ψ G b ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G) :=
    fun b hb => Finset.mem_image_of_mem _ hb
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun v => v ^ r), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨b₀, hb₀s, hb₀v⟩ := Finset.mem_image.mp hv
  rw [Finset.sum_const, ← hb₀v,
    value_fiber_card hψ h1 h0 hmul (Finset.mem_filter.mp hb₀s).2, nsmul_eq_mul]

/-- `N₀(G, 1) = 0` when `0 ∉ G`: no single element vanishes. -/
theorem N0_one_eq_zero (h0 : (0 : ZMod p) ∉ G) : N0 G 1 = 0 := by
  simp only [N0]
  refine Finset.sum_eq_zero fun v hv => ?_
  rw [Fintype.mem_piFinset] at hv
  have hne : v 0 ≠ 0 := ne_zero_of_mem h0 (hv 0)
  simp [hne]

/-- `N₀(G, 2) = n` for negation-closed `G` (dyadic `μ_n`, `n` even): the only vanishing pairs
are the antipodal ones. -/
theorem N0_two_eq (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hneg : (-1 : ZMod p) ∈ G) : N0 G 2 = G.card := by
  have hcard : N0 G 2
      = ((Fintype.piFinset fun _ : Fin 2 => G).filter fun v => ∑ i, v i = 0).card := by
    simp only [N0]
    exact (Finset.card_filter _ _).symm
  rw [hcard]
  refine Finset.card_bij' (fun v _ => v 0) (fun x _ => ![x, -x]) ?_ ?_ ?_ ?_
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    exact (Fintype.mem_piFinset.mp hv'.1) 0
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
    · fin_cases i
      · simpa using hx
      · have : (-1 : ZMod p) * x ∈ G := hmul _ hneg _ hx
        simpa [neg_one_mul] using this
    · rw [Fin.sum_univ_two]
      simp
  · intro v hv
    have hsum := (Finset.mem_filter.mp hv).2
    rw [Fin.sum_univ_two] at hsum
    funext i
    fin_cases i
    · simp
    · simpa using (eq_neg_of_add_eq_zero_right hsum).symm
  · intro x _
    simp

open scoped Classical in
/-- `e₁` of the period polynomial: **the distinct values sum to `-1` exactly.** -/
theorem sum_values (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) :
    ∑ v ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G), v = -1 := by
  have h := card_smul_sum_values_pow hψ h1 h0 hmul 1
  rw [N0_one_eq_zero h0] at h
  have hn : (G.card : ℂ) ≠ 0 := by
    have hpos : 0 < G.card := Finset.card_pos.mpr ⟨1, h1⟩
    exact_mod_cast hpos.ne'
  apply mul_left_cancel₀ hn
  simp only [pow_one] at h
  rw [h]
  ring

open scoped Classical in
/-- The second power sum of the distinct-value set is `p - n` exactly (the value-distribution
Parseval, in weight-enumerator form). -/
theorem sum_values_sq (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hneg : (-1 : ZMod p) ∈ G) :
    ∑ v ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G), v ^ 2
      = (p : ℂ) - (G.card : ℂ) := by
  have h := card_smul_sum_values_pow hψ h1 h0 hmul 2
  rw [N0_two_eq hmul hneg] at h
  have hn : (G.card : ℂ) ≠ 0 := by
    have hpos : 0 < G.card := Finset.card_pos.mpr ⟨1, h1⟩
    exact_mod_cast hpos.ne'
  apply mul_left_cancel₀ hn
  rw [h]
  ring

open scoped Classical in
/-- **The dyadic McEliece-divisibility transfer.** Below the char-`p` wraparound (any depth `r`
with `N₀(G,r) = 0`; by Lam–Leung antipodality this includes every odd `r` before the onset),
the `r`-th power sum of the distinct-value set is `-n^{r-1}` **exactly** — for `n = 2^μ` the
exact 2-power `v₂(P_r) = (r-1)·μ`, probe-confirmed (`P₃ = -n²` at `n = 8, 16, 32, 64`). -/
theorem sum_values_pow_of_vanishing (hψ : ψ.IsPrimitive) (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    {r : ℕ} (hr : 1 ≤ r) (hvan : N0 G r = 0) :
    ∑ v ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G), v ^ r
      = -(G.card : ℂ) ^ (r - 1) := by
  have h := card_smul_sum_values_pow hψ h1 h0 hmul r
  rw [hvan] at h
  have hn : (G.card : ℂ) ≠ 0 := by
    have hpos : 0 < G.card := Finset.card_pos.mpr ⟨1, h1⟩
    exact_mod_cast hpos.ne'
  apply mul_left_cancel₀ hn
  rw [h]
  have hpow : (G.card : ℂ) ^ r = (G.card : ℂ) * (G.card : ℂ) ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 from (Nat.succ_pred_eq_of_pos hr).symm]
    rw [pow_succ]
    ring
  rw [hpow]
  push_cast
  ring

end SubgroupLayer

/-! ## 7. Teeth: the toy prize-shaped instance `p = 17`, `G = μ₄ = {1, 4, 13, 16}` (`m = 4`).
The subgroup hypotheses are discharged by `decide`; the value-distribution and power-sum
theorems then give exact non-vacuous outputs through the general machinery. -/

section Teeth

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `μ₄ ⊂ F₁₇^×` as an explicit finset. -/
def G17 : Finset (ZMod 17) := {1, 4, 13, 16}

theorem G17_one : (1 : ZMod 17) ∈ G17 := by decide
theorem G17_zero : (0 : ZMod 17) ∉ G17 := by decide
theorem G17_mul : ∀ x ∈ G17, ∀ y ∈ G17, x * y ∈ G17 := by decide
theorem G17_neg : (-1 : ZMod 17) ∈ G17 := by decide
theorem G17_card : G17.card = 4 := by decide

open scoped Classical in
/-- Non-vacuity: at `p = 17`, `n = 4` the period family takes exactly `(17-1)/4 = 4` distinct
values — through the general dictionary, for every primitive character. -/
theorem toy_card_values {ψ : AddChar (ZMod 17) ℂ} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter fun c : ZMod 17 => c ≠ 0).image (eta ψ G17)).card = 4 := by
  rw [card_values hψ G17_one G17_zero G17_mul, G17_card]

open scoped Classical in
/-- Non-vacuity for the power-sum dictionary: the four distinct toy values sum to `-1`. -/
theorem toy_sum_values {ψ : AddChar (ZMod 17) ℂ} (hψ : ψ.IsPrimitive) :
    ∑ v ∈ (Finset.univ.filter fun c : ZMod 17 => c ≠ 0).image (eta ψ G17), v = -1 :=
  sum_values hψ G17_one G17_zero G17_mul

open scoped Classical in
/-- Non-vacuity for the second moment: `∑ v² = 17 - 4 = 13` over the four distinct values. -/
theorem toy_sum_values_sq {ψ : AddChar (ZMod 17) ℂ} (hψ : ψ.IsPrimitive) :
    ∑ v ∈ (Finset.univ.filter fun c : ZMod 17 => c ≠ 0).image (eta ψ G17), v ^ 2 = 13 := by
  have h := sum_values_sq hψ G17_one G17_zero G17_mul G17_neg
  rw [h, G17_card]
  norm_num

open scoped Classical in
/-- Non-vacuity for irrationality: every nonzero-frequency toy period is irrational. -/
theorem toy_eta_not_rational {ψ : AddChar (ZMod 17) ℂ} (hψ : ψ.IsPrimitive)
    {b : ZMod 17} (hb : b ≠ 0) (q : ℚ) : eta ψ G17 b ≠ (q : ℂ) :=
  eta_not_rational hψ G17_one hb (by rw [G17_card]; norm_num) q

end Teeth

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.psi_apply_eq_pow
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.isPrimitiveRoot_psi_one
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.sum_psi_inj
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.eta_eq_iff_image_eq
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.eta_eq_iff_mem_coset
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.value_fiber_card
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.card_values_mul
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.card_values
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.few_weight_no_go
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.eta_not_rational
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.card_smul_sum_values_pow
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.N0_one_eq_zero
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.N0_two_eq
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.sum_values
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.sum_values_sq
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.sum_values_pow_of_vanishing
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.toy_card_values
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.toy_sum_values
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.toy_sum_values_sq
#print axioms ArkLib.ProximityGap.G95CyclicCodeWeightDictionary.toy_eta_not_rational

end ArkLib.ProximityGap.G95CyclicCodeWeightDictionary
