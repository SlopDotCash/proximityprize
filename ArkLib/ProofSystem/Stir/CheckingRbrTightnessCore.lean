/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckingVerifier

/-!
# The tightness-fence counting core (#301, K4 part 1)

The quantitative heart of the switch-prover attack on the STIR checking verifier: the
challenge-counting facts behind the acceptance probability `≥ 1 − D/|F|`.  Protocol-free —
the night assembly welds these into the rbr-budget lower bound.

* `pass_count_ge` — for words `f g : ι → F` agreeing at every off-image query point, the
  set of challenges passing the binding check `f (queryPoint φ r) = g (queryPoint φ r)`
  has size `≥ |F| − |disagreement(f, g)|`: only the `φ`-image of the disagreement set can
  fail.
* `fail_subset_image` — the failing challenges embed into the disagreement set.

Why the off-image hypothesis is genuinely available to the ATTACKER: `queryPoint φ r` for
`r ∉ Set.range φ` is `Function.invFun`'s default, a single fixed junk point; the switch
prover picks its echoed codeword to agree with `f` there (or the fence's far-word
construction picks the disagreement support avoiding it), so all `|F| − |ι|` off-image
challenges pass.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

namespace TightnessCore

open Finset

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **The failing challenges embed into the disagreement set**: under off-image agreement,
a failing challenge must be the `φ`-image of a disagreement point. -/
lemma fail_subset_image (φ : ι ↪ F) (f g : ι → F)
    (hoff : ∀ r : F, r ∉ Set.range φ →
      f (queryPoint φ r) = g (queryPoint φ r)) :
    (univ.filter (fun r : F => ¬ f (queryPoint φ r) = g (queryPoint φ r)))
      ⊆ (univ.filter (fun x : ι => ¬ f x = g x)).image φ := by
  intro r hr
  rw [mem_filter] at hr
  obtain ⟨-, hfail⟩ := hr
  by_cases hrange : r ∈ Set.range φ
  · obtain ⟨x, hx⟩ := hrange
    have hqp : queryPoint φ r = x := by
      rw [← hx]
      exact Function.leftInverse_invFun φ.injective x
    rw [mem_image]
    refine ⟨x, ?_, hx⟩
    rw [mem_filter]
    exact ⟨mem_univ x, by rw [← hqp]; exact hfail⟩
  · exact absurd (hoff r hrange) hfail

/-- **The binding-check pass count**: under off-image agreement, at least
`|F| − |disagreement(f, g)|` challenges pass. -/
theorem pass_count_ge (φ : ι ↪ F) (f g : ι → F)
    (hoff : ∀ r : F, r ∉ Set.range φ →
      f (queryPoint φ r) = g (queryPoint φ r)) :
    Fintype.card F - (univ.filter (fun x : ι => ¬ f x = g x)).card
      ≤ (univ.filter (fun r : F => f (queryPoint φ r) = g (queryPoint φ r))).card := by
  classical
  have hfail : (univ.filter (fun r : F => ¬ f (queryPoint φ r) = g (queryPoint φ r))).card
      ≤ (univ.filter (fun x : ι => ¬ f x = g x)).card := by
    calc (univ.filter (fun r : F => ¬ f (queryPoint φ r) = g (queryPoint φ r))).card
        ≤ ((univ.filter (fun x : ι => ¬ f x = g x)).image φ).card :=
          card_le_card (fail_subset_image φ f g hoff)
      _ ≤ (univ.filter (fun x : ι => ¬ f x = g x)).card := card_image_le
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset F)) (p := fun r : F => f (queryPoint φ r) = g (queryPoint φ r))
  have huniv : (univ : Finset F).card = Fintype.card F := Finset.card_univ
  omega

/-- The off-image agreement hypothesis is achievable: all off-image challenges share ONE
query point (`Function.invFun`'s default), so agreement there is a single-point condition. -/
lemma off_image_queryPoint_const (φ : ι ↪ F) {r r' : F}
    (hr : r ∉ Set.range φ) (hr' : r' ∉ Set.range φ) :
    queryPoint φ r = queryPoint φ r' := by
  unfold queryPoint Function.invFun
  rw [dif_neg (by simpa [Set.range] using hr), dif_neg (by simpa [Set.range] using hr')]

/-! ## The far word at exact distance (the attack input) -/

open ReedSolomon in
/-- **A δ-far word at EXACT distance `e+1` from the code, vanishing at any designated junk
point**: the indicator of an `(e+1)`-subset avoiding `x⋆`.  Its distance to `0` is `e+1`;
to any nonzero codeword it is `≥ n − deg − e ≥ e + 2` (nonzero codewords have weight
`≥ n − deg + 1`), so the code distance is exactly `e+1` — the input on which the switch
prover achieves acceptance probability `≥ 1 − (e+1)/|F|`. -/
theorem exists_far_word_at_exact_distance (φ : ι ↪ F) (deg e : ℕ) (xJunk : ι)
    (hgap : deg + (2 * e + 1) < Fintype.card ι) :
    ∃ f : ι → F,
      f xJunk = 0 ∧
      (∀ c ∈ ReedSolomon.code φ deg, e + 1 ≤ hammingDist f c) ∧
      (∃ c₀ ∈ ReedSolomon.code φ deg, hammingDist f c₀ = e + 1) := by
  classical
  -- the support: an `(e+1)`-subset avoiding the junk point
  have hcard : e + 1 ≤ (Finset.univ.erase xJunk).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ xJunk), Finset.card_univ]
    omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨fun x => if x ∈ S then (1 : F) else 0, ?_, ?_, ?_⟩
  · -- vanishes at the junk point
    show (if xJunk ∈ S then (1 : F) else 0) = 0
    rw [if_neg (fun hmem => (Finset.mem_erase.mp (hSsub hmem)).1 rfl)]
  · -- distance ≥ e+1 to EVERY codeword
    intro c hc
    obtain ⟨p, hp, hpc⟩ := Submodule.mem_map.mp hc
    by_cases hp0 : p = 0
    · -- the zero codeword: distance = |S| = e+1
      have hc0 : c = 0 := by
        rw [← hpc, hp0, map_zero]
      subst hc0
      rw [hammingDist_zero_right]
      have : hammingNorm (fun x => if x ∈ S then (1 : F) else 0) = S.card := by
        unfold hammingNorm
        congr 1
        ext x
        by_cases hx : x ∈ S <;> simp [hx]
      omega
    · -- a nonzero codeword: weight ≥ n − (deg − 1), triangle through 0
      -- zero set of `c` injects into the roots of `p`
      have hdeg : p.natDegree < deg := by
        have hlt := Polynomial.mem_degreeLT.mp hp
        exact Polynomial.natDegree_lt_iff_degree_lt hp0 |>.mpr hlt
      have hzeros : (Finset.univ.filter (fun x : ι => c x = 0)).card ≤ p.natDegree := by
        have hinj : ∀ x ∈ Finset.univ.filter (fun x : ι => c x = 0),
            φ x ∈ p.roots.toFinset := by
          intro x hx
          rw [Finset.mem_filter] at hx
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
          have : c x = p.eval (φ x) := by rw [← hpc]; rfl
          rw [this] at hx
          exact hx.2
        calc (Finset.univ.filter (fun x : ι => c x = 0)).card
            ≤ p.roots.toFinset.card := by
              refine Finset.card_le_card_of_injOn φ hinj ?_
              intro a _ b _ hab
              exact φ.injective hab
          _ ≤ p.roots.card := Multiset.toFinset_card_le _
          _ ≤ p.natDegree := Polynomial.card_roots' p
      have hwt : Fintype.card ι - p.natDegree ≤ hammingNorm c := by
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset ι)) (p := fun x : ι => c x = 0)
        have huniv : (Finset.univ : Finset ι).card = Fintype.card ι := Finset.card_univ
        have hnorm : hammingNorm c
            = (Finset.univ.filter (fun x : ι => ¬ c x = 0)).card := rfl
        omega
      -- triangle: d(f, c) ≥ ‖c‖ − ‖f‖
      have htri := hammingDist_triangle (0 : ι → F)
        (fun x => if x ∈ S then (1 : F) else 0) c
      rw [hammingDist_zero_left] at htri
      have hfnorm : hammingNorm (fun x => if x ∈ S then (1 : F) else 0) = S.card := by
        unfold hammingNorm
        congr 1
        ext x
        by_cases hx : x ∈ S <;> simp [hx]
      rw [hfnorm] at htri
      omega
  · -- attained at the zero codeword
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [hammingDist_zero_right]
    have : hammingNorm (fun x => if x ∈ S then (1 : F) else 0) = S.card := by
      unfold hammingNorm
      congr 1
      ext x
      by_cases hx : x ∈ S <;> simp [hx]
    omega

/-! ## The switch prover (the attack object) -/

section SwitchProver

open OracleSpec OracleComp ProtocolSpec OracleInterface WhirIOP.Construction

variable [SampleableType F]

/-- **The switch prover**: ignores its input and every challenge, and sends the packed ZERO
codeword at every message round.  Against the checking verifier on the far word of
`exists_far_word_at_exact_distance` (support avoiding the junk point), every consistency
check compares equal messages, the final message IS a codeword, and the only live check is
the round-2 binding — which passes on `≥ |F| − (e+1)` challenges (`pass_count_ge`).  The
night assembly computes its acceptance probability and derives the budget lower bound. -/
noncomputable def stirSwitchProver (M : ℕ) (deg : ℕ) :
    OracleProver []ₒ Unit (OracleStatement ι F) Unit Bool (fun _ : Empty => Unit) Unit
      ((stirMultiVSpec M ι).toProtocolSpec F) where
  PrvState := fun _ => Unit
  input := fun _ => ()
  receiveChallenge := fun _ _ => pure (fun _ => ())
  sendMessage := fun i _ => pure
    ⟨Vector.cast (stirMultiVSpec_length_msg i)
      (packFiniteFunction ι (fun _ : ι => (0 : F))), ()⟩
  output := fun _ => pure ((true, isEmptyElim), ())

/-- The switch prover's message at every round is the packed zero word. -/
theorem stirSwitchProver_sendMessage (M : ℕ) (deg : ℕ)
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx) (st : Unit) :
    (stirSwitchProver (ι := ι) (F := F) M deg).sendMessage i st = pure
      ⟨Vector.cast (stirMultiVSpec_length_msg i)
        (packFiniteFunction ι (fun _ : ι => (0 : F))), ()⟩ := rfl

/-- The all-zero message family (what the switch prover commits at every round). -/
noncomputable def zeroMsgs (M : ℕ) :
    ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j :=
  fun j => Vector.cast (stirMultiVSpec_length_msg j)
    (packFiniteFunction ι (fun _ : ι => (0 : F)))

/-- Every oracle answer of the all-zero messages is `0`. -/
theorem msgAns_zeroMsgs (M : ℕ)
    (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) :
    msgAns (zeroMsgs M) j k = 0 := by
  unfold msgAns zeroMsgs
  rw [answer_honest_pack]

open scoped Classical in
/-- **The switch-prover acceptance characterization (Boolean level)**: against the all-zero
messages, the checking verifier's decision reduces to the single round-2 binding check
`f (queryPoint φ r₂) = 0` — every consistency check compares `0 = 0`, and the final message
IS the zero codeword. -/
theorem checkingBool_zeroMsgs_iff (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (oStmt : ∀ i, OracleStatement ι F i)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    checkingBool M φ deg oStmt (zeroMsgs M) chals = true ↔
      oStmt () (queryPoint φ (chalFE chals (outChalIdx M 0))) = 0 := by
  unfold checkingBool
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map]
  constructor
  · rintro ⟨⟨hbind, -⟩, -⟩
    rw [show inputAns oStmt (queryPoint φ (chalFE chals (outChalIdx M 0)))
        = oStmt () (queryPoint φ (chalFE chals (outChalIdx M 0))) from rfl,
      msgAns_zeroMsgs] at hbind
    exact hbind
  · intro hf
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [show inputAns oStmt (queryPoint φ (chalFE chals (outChalIdx M 0)))
        = oStmt () (queryPoint φ (chalFE chals (outChalIdx M 0))) from rfl,
        msgAns_zeroMsgs]
      exact hf
    · rintro b ⟨j, -, rfl⟩
      simp only [msgAns_zeroMsgs, Bool.and_eq_true, decide_eq_true_eq, and_self]
    · have hzero : (fun x : ι =>
          (((List.finRange (Fintype.card ι)).map (fun k =>
            msgAns (zeroMsgs M) (msgIdx M (Fin.last M))
              (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))).getD
            ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0)) = fun _ => (0 : F) := by
        funext x
        rw [List.getD_eq_getElem _ _ (by
          simp only [List.length_map, List.length_finRange]
          exact (Fintype.equivFin ι x).isLt)]
        rw [List.getElem_map, msgAns_zeroMsgs]
      rw [hzero]
      exact Submodule.zero_mem _

open TightnessCore in
open scoped Classical in
/-- **THE COUNTING FENCE**: on the far word of `exists_far_word_at_exact_distance` (or any
word vanishing on all off-image query points with `≤ D` nonzero positions), the all-zero
strategy is accepted at `≥ |F| − D` of the `|F|` round-2 challenge values — the Boolean-level
content of the switch-prover attack.  The probability-game lift (every valid rbr budget
family has `Σᵢ εᵢ ≥ 1 − D/|F|`) additionally needs the generic rbr→soundness union-bound
chain rule, which is NOT yet in-tree; this counting core is the unconditional part. -/
theorem accept_count_ge_of_far_word (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    [DecidableEq ι]
    (oStmt : ∀ i, OracleStatement ι F i)
    (hoff : ∀ r : F, r ∉ Set.range φ → oStmt () (queryPoint φ r) = 0)
    (chalsOf : F → ((stirMultiVSpec M ι).toProtocolSpec F).Challenges)
    (hchalsOf : ∀ r, chalFE (chalsOf r) (outChalIdx M 0) = r) :
    Fintype.card F
        - (Finset.univ.filter (fun x : ι => ¬ oStmt () x = 0)).card
      ≤ (Finset.univ.filter (fun r : F =>
          checkingBool M φ deg oStmt (zeroMsgs M) (chalsOf r) = true)).card := by
  have hiff : ∀ r : F,
      (checkingBool M φ deg oStmt (zeroMsgs M) (chalsOf r) = true) ↔
        oStmt () (queryPoint φ r) = (fun _ : ι => (0 : F)) (queryPoint φ r) := by
    intro r
    rw [checkingBool_zeroMsgs_iff, hchalsOf]
  have hcount := pass_count_ge φ (oStmt ()) (fun _ => (0 : F))
    (fun r hr => hoff r hr)
  calc Fintype.card F - (Finset.univ.filter (fun x : ι => ¬ oStmt () x = 0)).card
      = Fintype.card F
          - (Finset.univ.filter (fun x : ι => ¬ oStmt () x = (fun _ : ι => (0:F)) x)).card := rfl
    _ ≤ (Finset.univ.filter (fun r : F =>
          oStmt () (queryPoint φ r) = (fun _ : ι => (0 : F)) (queryPoint φ r))).card := hcount
    _ = (Finset.univ.filter (fun r : F =>
          checkingBool M φ deg oStmt (zeroMsgs M) (chalsOf r) = true)).card := by
        apply Finset.card_nbij' id id <;> intro r hr <;>
          simp_all [Finset.mem_filter, hiff]

end SwitchProver

end TightnessCore

end MultiRound

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.MultiRound.TightnessCore.pass_count_ge
#print axioms StirIOP.MultiRound.TightnessCore.fail_subset_image
#print axioms StirIOP.MultiRound.TightnessCore.off_image_queryPoint_const
#print axioms StirIOP.MultiRound.TightnessCore.exists_far_word_at_exact_distance
#print axioms StirIOP.MultiRound.TightnessCore.stirSwitchProver
#print axioms StirIOP.MultiRound.TightnessCore.checkingBool_zeroMsgs_iff
#print axioms StirIOP.MultiRound.TightnessCore.accept_count_ge_of_far_word
