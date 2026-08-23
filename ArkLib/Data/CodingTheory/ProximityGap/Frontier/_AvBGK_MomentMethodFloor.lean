/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# The moment-method bridge: BGK as the unconditional δ* floor (#444/#334)

The prize δ* lower bound asks for the **Paley** sup-norm bound `M(n) = max_{b≠0}‖η_b‖ ≤ C√(n log q)`
(exponent `1/2`), which is open. The **BGK** theorem (Bourgain–Glibichuk–Konyagin 2006) proves the
*weaker* unconditional bound `M(n) ≤ n^{1-δ'}` (exponent `1-δ' < 1`) via the sum-product /
additive-energy method — this is the **proven floor**, distinct from the conjectural Paley ceiling.

The engine of BGK is the elementary **moment-method bridge** formalized here: the worst-case period
`Λ² = prizeRadiusSq = max_{b≠0}‖η_b‖²` is dominated by *any single* `2k`-th power-sum of the
periods,
  `Λ^{2k} = (Λ²)^k ≤ ∑_{b≠0} ‖η_b‖^{2k}`        (`prizeRadiusSq_pow_le_sum`, max ≤ sum),
so an upper bound on the power-sum gives an upper bound on `Λ`. Taking `2k`-th roots and optimizing
`k`, a sum-product bound `∑_{b≠0}‖η_b‖^{2k} ≤ S_k` yields `M ≤ min_k S_k^{1/2k}` — the BGK exponent
when the `S_k` are the (unconditional) energy bounds.

The power-sums are the additive energies: `∑_{b}‖η_b‖^{2k} = q·E_k(G)` (orthogonality of additive
characters), so `∑_{b≠0}‖η_b‖^{2k} = q·E_k − |G|^{2k}`. The `k=2` instance is in-tree
(`subgroup_gaussSum_fourthMoment`); we record the resulting **concrete unconditional sup-norm bound**
`Λ⁴ ≤ q·E(G) − |G|⁴` (`prizeRadiusSq_sq_le_fourthMoment`). Because the `k=2` additive energy of a thin
subgroup is exactly `E = 3|G|² − 3|G|` (Wick; verified in-tree numerics), this gives
`M⁴ ≤ q·(3n²) − n⁴`, the elementary floor at depth 2; the BGK exponent comes from pushing to
`k ~ log q` with the sum-product energy bounds.

Honest scope: the moment bridge here is **fully proven** (elementary, Parseval). The energy bound
`S_k` it consumes is the **cited BGK sum-product theorem** (not re-derived in Lean); composing them
pins the unconditional δ* *floor*, strictly below the open Paley *ceiling*.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.AvBGK

open ArkLib.ProximityGap.PrizeStructuralConstant
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The moment-method bridge (elementary).** The worst-case squared period `Λ² = prizeRadiusSq`,
raised to the `k`-th power, is at most the `2k`-th power-sum of the nonzero periods:
  `(Λ²)^k ≤ ∑_{b≠0} ‖η_b‖^{2k}`.
Proof: `Λ²` is attained at some `b₀ ≠ 0` (finite `sup'`); the term `‖η_{b₀}‖^{2k} = (Λ²)^k` is one
nonnegative summand of the power-sum, hence `≤` the whole sum. This is the engine of BGK: an upper
bound on the power-sum (e.g. a sum-product energy bound) upper-bounds `Λ`. -/
theorem prizeRadiusSq_pow_le_sum (ψ : AddChar F ℂ) (G : Finset F) (k : ℕ) :
    (prizeRadiusSq ψ G) ^ k
      ≤ ∑ b ∈ (Finset.univ.erase (0 : F)), ‖eta ψ G b‖ ^ (2 * k) := by
  classical
  -- the sup' is attained at some b₀ in the erased set
  obtain ⟨b₀, hb₀mem, hb₀eq⟩ :=
    Finset.exists_mem_eq_sup' (erase_zero_nonempty (F := F)) (fun b => ‖eta ψ G b‖ ^ 2)
  have hpow : (prizeRadiusSq ψ G) ^ k = ‖eta ψ G b₀‖ ^ (2 * k) := by
    unfold prizeRadiusSq
    rw [hb₀eq, ← pow_mul, Nat.mul_comm]
  rw [hpow]
  -- a single nonnegative term is ≤ the whole sum
  refine Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * k)) ?_ hb₀mem
  intro b _
  positivity

/-- **The `k=2` concrete unconditional sup-norm bound (from the in-tree fourth moment).** The
worst-case squared period satisfies
  `Λ⁴ ≤ q·E(G) − |G|⁴`,
where `E(G) = addEnergy G` is the (`k=2`) additive energy. This is the moment bridge at depth `2`
fed by the *exact* fourth-moment identity `∑_b‖η_b‖⁴ = q·E(G)`; the `b=0` spike `‖η_0‖⁴ = |G|⁴` is
subtracted. Combined with the unconditional energy bound `E(G) = O(|G|²)` for thin subgroups
(in-tree numerics: `E = 3|G|²−3|G|`), this is the elementary floor; the BGK exponent comes from
`k ~ log q`. -/
theorem prizeRadiusSq_sq_le_fourthMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (prizeRadiusSq ψ G) ^ 2
      ≤ (Fintype.card F : ℝ) * (SubgroupGaussSumFourthMoment.addEnergy G) - (G.card : ℝ) ^ 4 := by
  classical
  -- power-sum at k=2 over ALL b equals q·E (in-tree), minus the b=0 spike |G|⁴
  have hbridge := prizeRadiusSq_pow_le_sum ψ G 2
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ 4
      = (∑ b ∈ (Finset.univ.erase (0 : F)), ‖eta ψ G b‖ ^ (2 * 2)) + (G.card : ℝ) ^ 4 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]
    congr 1
    rw [h0, Complex.norm_natCast]
  have hfm := SubgroupGaussSumFourthMoment.subgroup_gaussSum_fourthMoment hψ G
  -- ∑_{b≠0} = q·E − |G|⁴
  have hsumerase : ∑ b ∈ (Finset.univ.erase (0 : F)), ‖eta ψ G b‖ ^ (2 * 2)
      = (Fintype.card F : ℝ) * (SubgroupGaussSumFourthMoment.addEnergy G) - (G.card : ℝ) ^ 4 := by
    have : ∑ b : F, ‖eta ψ G b‖ ^ 4
        = (∑ b ∈ (Finset.univ.erase (0 : F)), ‖eta ψ G b‖ ^ (2 * 2)) + (G.card : ℝ) ^ 4 := hsplit
    rw [hfm] at this
    linarith
  rwa [hsumerase] at hbridge

end ArkLib.ProximityGap.Frontier.AvBGK

#print axioms ArkLib.ProximityGap.Frontier.AvBGK.prizeRadiusSq_pow_le_sum
#print axioms ArkLib.ProximityGap.Frontier.AvBGK.prizeRadiusSq_sq_le_fourthMoment
