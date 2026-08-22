/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (Fable WF2-C1 lane, #389)
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# WF2-C1: the ENERGY half of the cyclotomic-norm excess characterization (#389)

This scratch file proves the *energy ⟺ Sidon* biconditional in full generality — the missing
converse of the in-tree `additiveEnergy_eq_of_sidonModNeg`.  Together with that forward result it
pins the additive energy:

  for a negation-closed `G` with `0 ∉ G`, char `≠ 2`:
    `additiveEnergy G = 3|G|² − 3|G|   ⟺   SidonModNeg G`,
  and  `additiveEnergy G ≥ 3|G|² − 3|G|` ALWAYS,  with the inequality STRICT when `¬ SidonModNeg G`.

This is the first two of the three faces of conjecture WF2-C1
(`E(μ_n) > 3n²−3n  ⟺  ¬SidonModNeg(μ_n)`).  The third face — `¬SidonModNeg ⟺ p ∣ N_{a,b,c,d}` —
is the cyclotomic-norm/resultant link, already half-built in `CyclotomicSidonLift.lean`
(`fourTerm_ne_zero_of_pair_ne`, `resultant_map_eq_zero_of_primitiveRoot`); see the closing
reduction comment.

Numerically WF2-C1 is verified with ZERO violations for `n = 4,8,16` over all primes `p ≡ 1 (mod n)`
up to several thousand, and for `n = 32` over all such primes up to 2.1·10⁷ (probe
`probe389_*`).  The predicted finite bad sets match exactly:
  Bad(4)={5}, Bad(8)={17,41}, Bad(16)={17,97,113,193,257,337}.

All declarations here are axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound Finset

namespace ArkLib.ProximityGap.WF2EnergySidon

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Pointwise rep-count lower bound (always, negation-closed).**  For any `a, b ∈ G` with `G`
negation-closed, the representation count of the shift `a + b` is at least the structured-minimum
value `if a+b=0 then |G| else |{a,b}|`.  This is the per-term floor whose double-sum is `3|G|²−3|G|`.

* zero-sum case: `repCount G 0 = |G|` exactly (the negation pairing), by `repCount_zero_eq_card`;
* nonzero case: `{a, b} ⊆ {y ∈ G : (a+b) − y ∈ G}` (both `a` and `b` are representatives), so the
  rep-count is `≥ |{a,b}|`. -/
theorem repCount_ge_structured {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G)
    {a b : F} (ha : a ∈ G) (hb : b ∈ G) :
    (if a + b = 0 then G.card else ({a, b} : Finset F).card) ≤ repCount G (a + b) := by
  by_cases hab : a + b = 0
  · rw [if_pos hab, hab, repCount_zero_eq_card hneg]
  · rw [if_neg hab]
    unfold repCount
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with rfl | rfl
    · exact ⟨ha, by simpa using hb⟩
    · exact ⟨hb, by simpa using ha⟩

/-- **The structured minimum double-sum equals `3|G|²−3|G|`.**  Re-derives, from the per-pair floor,
that `∑_{a,b∈G} (if a+b=0 then |G| else |{a,b}|) = 3|G|²−3|G|`.  (Identical evaluation to the
in-tree `additiveEnergy_eq_of_sidonModNeg`, extracted as a stand-alone arithmetic fact so it can be
fed to both the lower-bound and the equality direction.) -/
theorem structured_min_eq {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    (∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card))
      = 3 * G.card ^ 2 - 3 * G.card := by
  classical
  have hne0 : ∀ x ∈ G, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  have hinner : ∀ a ∈ G,
      (∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card)) = 3 * G.card - 3 := by
    intro a ha
    have ha0 : a ≠ 0 := hne0 a ha
    have hna : -a ∈ G := hneg a ha
    have haa : a + a ≠ 0 := fun h =>
      ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
    have ha_ne : a ≠ -a := fun h =>
      ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
    have hge2 : 2 ≤ G.card := by
      have hsub : ({a, -a} : Finset F) ⊆ G := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ha
        · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hna
      calc 2 = ({a, -a} : Finset F).card := (Finset.card_pair ha_ne).symm
        _ ≤ G.card := Finset.card_le_card hsub
    rw [Finset.sum_ite]
    have hf0 : G.filter (fun b => a + b = 0) = {-a} := by
      ext b; rw [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => by linear_combination h.2, fun h => ⟨h ▸ hna, by rw [h]; ring⟩⟩
    rw [hf0, Finset.sum_const, Finset.card_singleton, one_smul]
    set S := G.filter (fun b => ¬ a + b = 0) with hSdef
    have haS : a ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨ha, haa⟩
    have hScard : S.card = G.card - 1 := by
      have htot := Finset.card_filter_add_card_filter_not (s := G) (fun b => a + b = 0)
      rw [hf0, Finset.card_singleton] at htot
      rw [hSdef]; omega
    rw [← Finset.add_sum_erase S _ haS]
    have hfa : ({a, a} : Finset F).card = 1 := by simp
    have hrest : (∑ b ∈ S.erase a, ({a, b} : Finset F).card) = (S.card - 1) * 2 := by
      have hc : ∀ b ∈ S.erase a, ({a, b} : Finset F).card = 2 := fun b hb =>
        Finset.card_pair (Ne.symm (Finset.mem_erase.mp hb).1)
      rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_erase_of_mem haS, smul_eq_mul]
    rw [hfa, hrest, hScard]
    omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  rcases Nat.eq_zero_or_pos G.card with h | h
  · rw [h]; simp
  · have h1 : 3 ≤ 3 * G.card := by omega
    have hsq : G.card ≤ G.card ^ 2 := Nat.le_self_pow (by norm_num) _
    have h2' : 3 * G.card ≤ 3 * G.card ^ 2 := by omega
    zify [h1, h2']; ring

/-- **THE LOWER BOUND (always).**  For any negation-closed `G` with `0 ∉ G`, char `≠ 2`, the
additive energy is at least the char-0 minimal value `3|G|²−3|G|`.  Pointwise-floor + monotone sum
+ `structured_min_eq`. -/
theorem additiveEnergy_ge {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    3 * G.card ^ 2 - 3 * G.card ≤ additiveEnergy G := by
  rw [← structured_min_eq h2 h0 hneg]
  unfold additiveEnergy
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  exact repCount_ge_structured hneg ha hb

/-- **The energy as the structured floor PLUS the rep-count surplus.**  Writes
`E(G) = (structured min) + ∑_{a,b} (repCount(a+b) − floor(a,b))`, where every surplus term is `≥ 0`.
This is the bookkeeping that turns one strictly-positive surplus term (a non-Sidon coincidence) into
`E > min`. -/
theorem additiveEnergy_eq_min_add_surplus {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    additiveEnergy G
      = (3 * G.card ^ 2 - 3 * G.card)
        + ∑ a ∈ G, ∑ b ∈ G,
            (repCount G (a + b) - (if a + b = 0 then G.card else ({a, b} : Finset F).card)) := by
  rw [← structured_min_eq h2 h0 hneg]
  unfold additiveEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hle := repCount_ge_structured hneg ha hb
  omega

/-- **A non-Sidon coincidence forces a rep-count `≥ 3` at a nonzero shift.**  If `SidonModNeg` fails
— `∃ a b c d ∈ G` with `a+b=c+d`, neither ordered-pair-equality nor `a+b=0` — then there is a
nonzero shift `t = a+b` whose representation set contains the three *distinct* elements `a, b, c`,
hence `repCount G t ≥ 3 > |{a,b}|`. -/
theorem exists_repCount_ge_three_of_not_sidonModNeg {G : Finset F}
    (hS : ¬ SidonModNeg G) :
    ∃ a ∈ G, ∃ b ∈ G, a + b ≠ 0 ∧ ({a, b} : Finset F).card < repCount G (a + b) := by
  classical
  -- unfold the negated SidonModNeg into a concrete failing quadruple
  rw [SidonModNeg] at hS
  push_neg at hS
  obtain ⟨a, ha, b, hb, c, hc, d, hd, heq, hnac_bd, hnad_bc, hab0⟩ := hS
  refine ⟨a, ha, b, hb, hab0, ?_⟩
  -- `c` is a representative of `a+b` distinct from both `a` and `b`
  have hc_rep : c ∈ G.filter (fun y => (a + b) - y ∈ G) := by
    rw [Finset.mem_filter]
    refine ⟨hc, ?_⟩
    -- (a+b) - c = d ∈ G  (from a+b=c+d)
    have : (a + b) - c = d := by linear_combination heq
    rw [this]; exact hd
  have ha_rep : a ∈ G.filter (fun y => (a + b) - y ∈ G) := by
    rw [Finset.mem_filter]; exact ⟨ha, by simpa using hb⟩
  have hb_rep : b ∈ G.filter (fun y => (a + b) - y ∈ G) := by
    rw [Finset.mem_filter]; exact ⟨hb, by simpa using ha⟩
  -- `c ≠ a` and `c ≠ b`:  if `c = a` then `d = b` (forces ordered eq, contradiction); sym for `c=b`
  have hca : c ≠ a := by
    rintro rfl
    -- a+b=a+d ⟹ b=d ⟹ (a=c=a ∧ b=d) — contradicts hnac_bd
    have hbd : b = d := by linear_combination heq
    exact hnac_bd rfl hbd
  have hcb : c ≠ b := by
    rintro rfl
    -- a+b=c+d with c=b ⟹ a=d ⟹ (a=d ∧ b=c) contradicts hnad_bc
    have had : a = d := by linear_combination heq
    exact hnad_bc had rfl
  -- `c ∉ {a, b}`, so `insert c {a,b} ⊆ rep set`, giving repCount ≥ |{a,b}| + 1 > |{a,b}|
  have hc_notin : c ∉ ({a, b} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hca, hcb⟩
  have hsub : (insert c ({a, b} : Finset F)) ⊆ G.filter (fun y => (a + b) - y ∈ G) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc_rep
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha_rep
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hb_rep
  have hcard_ins : (insert c ({a, b} : Finset F)).card = ({a, b} : Finset F).card + 1 :=
    Finset.card_insert_of_notMem hc_notin
  have hcard3 : ({a, b} : Finset F).card + 1 ≤ (G.filter (fun y => (a + b) - y ∈ G)).card := by
    rw [← hcard_ins]; exact Finset.card_le_card hsub
  unfold repCount
  omega

/-- **THE STRICT CONVERSE (energy half of WF2-C1).**  For negation-closed `G`, `0 ∉ G`, char `≠ 2`:
if `SidonModNeg` FAILS, the additive energy strictly exceeds the char-0 minimum.  Combined with
`additiveEnergy_ge` (and the in-tree `additiveEnergy_eq_of_sidonModNeg`) this pins the energy:
`E(G) = 3|G|²−3|G| ⟺ SidonModNeg G`. -/
theorem additiveEnergy_gt_of_not_sidonModNeg {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G)
    (hS : ¬ SidonModNeg G) :
    3 * G.card ^ 2 - 3 * G.card < additiveEnergy G := by
  classical
  obtain ⟨a, ha, b, hb, hab0, hsurp⟩ := exists_repCount_ge_three_of_not_sidonModNeg hS
  rw [additiveEnergy_eq_min_add_surplus h2 h0 hneg]
  -- the surplus double sum is strictly positive because the (a,b) term is ≥ 1
  have hpos : 0 < ∑ a' ∈ G, ∑ b' ∈ G,
      (repCount G (a' + b') - (if a' + b' = 0 then G.card else ({a', b'} : Finset F).card)) := by
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun j _ => Nat.zero_le _))
    refine ⟨a, ha, ?_⟩
    apply Finset.sum_pos' (fun j _ => Nat.zero_le _)
    refine ⟨b, hb, ?_⟩
    rw [if_neg hab0]
    omega
  omega

/-- **THE ENERGY BICONDITIONAL — `E(G) = 3|G|²−3|G| ⟺ SidonModNeg G`.**  The two-sided pin of the
additive energy at the char-0 minimum, in full generality (negation-closed, `0 ∉ G`, char `≠ 2`).
Forward: the in-tree `additiveEnergy_eq_of_sidonModNeg`.  Backward (contrapositive): the strict
converse above (`E > min` when Sidon fails, so `E = min` forces Sidon). -/
theorem additiveEnergy_eq_iff_sidonModNeg {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card ↔ SidonModNeg G := by
  constructor
  · intro hE
    by_contra hS
    exact absurd hE (additiveEnergy_gt_of_not_sidonModNeg h2 h0 hneg hS).ne'
  · intro hS
    exact additiveEnergy_eq_of_sidonModNeg h2 h0 hneg hS

/-- **EXCESS POSITIVITY ⟺ NON-SIDON (the literal first face of WF2-C1).**
`energyExcess(G) > 0`  i.e.  `E(G) > 3|G|²−3|G|`  IFF  `¬ SidonModNeg G`.  This is the statement
WF2-C1 asserts under the name "energyExcess(μ_n) > 0 ⟺ μ_n is NOT SidonModNeg", here proven for
every negation-closed `G` (`0 ∉ G`, char `≠ 2`), hence in particular for `μ_n` (`n = 2^m`). -/
theorem additiveEnergy_gt_iff_not_sidonModNeg {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    3 * G.card ^ 2 - 3 * G.card < additiveEnergy G ↔ ¬ SidonModNeg G := by
  constructor
  · intro hgt hS
    exact absurd (additiveEnergy_eq_of_sidonModNeg h2 h0 hneg hS) hgt.ne'
  · exact additiveEnergy_gt_of_not_sidonModNeg h2 h0 hneg

end ArkLib.ProximityGap.WF2EnergySidon

/-!
## Reduction of the THIRD face (cyclotomic-norm divisibility) to named substrate

WF2-C1's remaining face is `¬SidonModNeg(μ_n) ⟺ p ∣ N_{a,b,c,d}` for some nontrivial non-zero-sum
config.  With the energy biconditional above, this reduces the whole conjecture to two links, BOTH
already half-present in `CyclotomicSidonLift.lean`:

* **(parallelogram ⟹ p ∣ Res)** is `resultant_map_eq_zero_of_primitiveRoot` (specialized to
  `K = ZMod p`): a coincidence `ω^a+ω^b = ω^c+ω^d` at the primitive root `ω` makes the integer
  `Res(Φ_n, X^a+X^b−X^c−X^d)` vanish mod `p`.
* **(`Res ≠ 0`)**, giving FINITENESS of `Bad(n)`, is exactly `fourTerm_ne_zero_of_pair_ne` lifted
  through the resultant: for a non-zero-sum nontrivial config the ℂ four-term value is nonzero, so
  `Φ_n` and the four-term polynomial are coprime over ℂ, so `Res ≠ 0`.  The probe confirmed the
  *only* zero-resultant nontrivial configs are exactly the (zero-sum pair, zero-sum pair) ones that
  `SidonModNeg` deliberately excludes — so excluding `a+b=0` is precisely what makes every counted
  norm nonzero (and `Bad(n)` finite).

The converse link **(p ∣ Res ⟹ parallelogram exists in F_p)** is the only genuinely new step left
for a *complete* machine-checked third face: `p ∣ Res(Φ_n, f)` means `Φ_n` and `f` share a root mod
`p`; since `p ≡ 1 (mod n)` gives `Φ_n` a root `ω` (a primitive `n`-th root) in `F_p`, and (n=2^m
prime power) `Φ_n` is *separable* with all roots primitive, that shared root is one of the `ω^a`,
realizing the coincidence.  This is a clean resultant-common-root argument but was NOT attempted in
this lane (it would need the separability/root-transfer bookkeeping); it is named here, not asserted.

Numerical status of the FULL three-face IFF: ZERO violations for `n=4,8,16` (all `p≡1 mod n`
< few·10³) and `n=32` (all `p≡1 mod n` < 2.1·10⁷); predicted finite bad sets match exactly.
-/

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WF2EnergySidon.repCount_ge_structured
#print axioms ArkLib.ProximityGap.WF2EnergySidon.structured_min_eq
#print axioms ArkLib.ProximityGap.WF2EnergySidon.additiveEnergy_ge
#print axioms ArkLib.ProximityGap.WF2EnergySidon.additiveEnergy_eq_min_add_surplus
#print axioms ArkLib.ProximityGap.WF2EnergySidon.exists_repCount_ge_three_of_not_sidonModNeg
#print axioms ArkLib.ProximityGap.WF2EnergySidon.additiveEnergy_gt_of_not_sidonModNeg
#print axioms ArkLib.ProximityGap.WF2EnergySidon.additiveEnergy_eq_iff_sidonModNeg
#print axioms ArkLib.ProximityGap.WF2EnergySidon.additiveEnergy_gt_iff_not_sidonModNeg
