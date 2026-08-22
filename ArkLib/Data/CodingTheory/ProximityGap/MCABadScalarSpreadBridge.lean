/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
  Round 15, Angle D — MCA-side bad-scalar spread for the proximity-gap prize context
  (Ethereum Proximity Prize / ABF26 / ArkLib #232).

  Self-contained over Mathlib only.  The mutual-correlated-agreement (MCA) structure is
  restated abstractly below; nothing is imported from ArkLib.
-/

/-!
# MCA-side lower-bound bridge: bad-scalar spread on a pencil

Background.  List-size lower bounds for Reed-Solomon proximity gaps do NOT transfer to
the MCA error automatically (in-tree no-go: a large list at one word does not force a
large MCA error).  An MCA lower bound must instead exhibit *bad-scalar spread*: a single
pencil `γ ↦ f₁ + γ·f₂` for which many scalars `γ` give words close to the code, while
the pair `(f₁, f₂)` admits no correlated agreement — no single coordinate set of size
`≥ a` on which both endpoints simultaneously match codewords.

Contents (everything below is fully proved, no placeholders):

1. `mcaBadCount_ge_of_spread` — the definition-level bridge: if every `γ` in a scalar
   set `Γ` gives a close pencil word, and no single agreement set of size `≥ a` serves
   all `γ ∈ Γ` simultaneously (witness inconsistency), then the MCA bad-scalar count of
   the pencil is at least `Γ.card`.  Key point: for a code closed under the pencil
   operation, a correlated-agreement set would serve *every* scalar at once with the
   consistent witness `u + γ·v`, so witness inconsistency refutes correlated agreement,
   and then every close scalar is MCA-bad.
2. `mcaBadFraction_ge_of_spread` — the same bound in fraction (error-probability) form.
3. `closeAt_pencil_of_corrAgree` — the converse sanity direction: correlated agreement
   forces every pencil word to be close with the consistent witness on the same set.
   This is exactly the structure a lower-bound construction must break.
4. A concrete kernel-checked instance over `ZMod 5`: domain of 3 points, code = the
   constant words (Reed-Solomon with `k = 1`), agreement threshold `a = 2 = k + t`,
   explicit `f₁ = ![0,1,2]`, `f₂ = ![0,1,4]`.  Exactly THREE bad scalars `{2, 3, 4}`
   out of five, each with its own explicit codeword witness, the witnesses pairwise
   inconsistent; the pair has no correlated agreement; bad fraction `3/5`.

Honest scope.  The bridge reduces an MCA-error lower bound exactly to constructing
`(f₁, f₂, Γ)` with `|Γ| / |F|` large and no shared agreement set.  The instance here
realizes the full pipeline at toy scale (`n = 3`, `|F| = 5`, spread fraction `3/5`).
What remains open — and is NOT claimed here — is the prize-scale version: smooth-domain
RS with `|F| < 2^256`, `δ*` strictly between `1 - √ρ` and `1 - ρ`, and a pencil whose
bad-scalar fraction exceeds `2^{-128}`.  No statement below asserts anything about that
regime; the general super-polynomial bad-scalar construction is out of reach of this
file and is recorded as the open gap.
-/

namespace R15MCAGap

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [CommRing F]

/-- Number of coordinates on which the word `w` agrees with the word `c`. -/
def agreeCount (w c : ι → F) : ℕ :=
  (Finset.univ.filter fun x => w x = c x).card

/-- The pencil (affine line) of words through `f1` in direction `f2`. -/
def pencil (f1 f2 : ι → F) (γ : F) : ι → F :=
  fun x => f1 x + γ * f2 x

/-- `w` is close to the code `C` at agreement threshold `a`: some codeword agrees with
`w` on at least `a` coordinates.  (For `a = (1 - δ)·n` this is `δ`-closeness.) -/
def closeAt (C : Finset (ι → F)) (a : ℕ) (w : ι → F) : Prop :=
  ∃ c ∈ C, a ≤ agreeCount w c

/-- Correlated agreement of the pair `(f1, f2)` at threshold `a`: one single coordinate
set `S` of size `≥ a` on which `f1` matches a codeword `u` and `f2` matches a codeword
`v` simultaneously. -/
def corrAgree (C : Finset (ι → F)) (a : ℕ) (f1 f2 : ι → F) : Prop :=
  ∃ S : Finset ι, a ≤ S.card ∧ ∃ u ∈ C, ∃ v ∈ C,
    (∀ x ∈ S, f1 x = u x) ∧ (∀ x ∈ S, f2 x = v x)

/-- The MCA bad event at scalar `γ`: the pencil word `f1 + γ·f2` is close to the code,
yet the pair `(f1, f2)` has no correlated agreement.  This is the per-scalar event whose
probability (over uniform `γ`) the mutual-correlated-agreement error must dominate, so
counting scalars satisfying it is exactly an MCA-error lower bound for the line. -/
def mcaBad (C : Finset (ι → F)) (a : ℕ) (f1 f2 : ι → F) (γ : F) : Prop :=
  closeAt C a (pencil f1 f2 γ) ∧ ¬ corrAgree C a f1 f2

instance (C : Finset (ι → F)) (a : ℕ) (w : ι → F) : Decidable (closeAt C a w) :=
  inferInstanceAs (Decidable (∃ c ∈ C, a ≤ agreeCount w c))

instance (C : Finset (ι → F)) (a : ℕ) (f1 f2 : ι → F) : Decidable (corrAgree C a f1 f2) :=
  inferInstanceAs (Decidable (∃ S : Finset ι, a ≤ S.card ∧ ∃ u ∈ C, ∃ v ∈ C,
    (∀ x ∈ S, f1 x = u x) ∧ (∀ x ∈ S, f2 x = v x)))

instance (C : Finset (ι → F)) (a : ℕ) (f1 f2 : ι → F) : DecidablePred (mcaBad C a f1 f2) :=
  fun γ => inferInstanceAs (Decidable (closeAt C a (pencil f1 f2 γ) ∧ ¬ corrAgree C a f1 f2))

/-- The number of MCA-bad scalars on the pencil through `f1` in direction `f2`. -/
def mcaBadCount (C : Finset (ι → F)) (a : ℕ) (f1 f2 : ι → F) : ℕ :=
  (Finset.univ.filter (mcaBad C a f1 f2)).card

omit [DecidableEq ι] [Fintype F] in
/-- Converse sanity direction: if the pair `(f1, f2)` has correlated agreement on `S`
with codewords `u, v`, and the code is closed under the pencil operation, then EVERY
pencil word is close, with the *consistent* witness `u + γ·v` on the same set `S`.
Hence any lower-bound construction must destroy exactly this shared-set structure. -/
theorem closeAt_pencil_of_corrAgree
    (C : Finset (ι → F)) (a : ℕ) (f1 f2 : ι → F)
    (hclosed : ∀ u ∈ C, ∀ v ∈ C, ∀ γ : F, (fun x => u x + γ * v x) ∈ C)
    (h : corrAgree C a f1 f2) (γ : F) :
    closeAt C a (pencil f1 f2 γ) := by
  obtain ⟨S, hS, u, hu, v, hv, h1, h2⟩ := h
  refine ⟨fun x => u x + γ * v x, hclosed u hu v hv γ, hS.trans ?_⟩
  unfold agreeCount
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp [pencil, h1 x hx, h2 x hx]

/-- **Bad-scalar spread bridge** (the definition-level combinatorial core).

If every scalar `γ` in the set `Γ` makes the pencil word `f1 + γ·f2` close to the code,
and the closeness witnesses are inconsistent — no single agreement set `S` of size `≥ a`
carries a codeword for ALL `γ ∈ Γ` simultaneously — then the MCA bad-scalar count of the
pencil is at least `Γ.card`.

Proof shape: correlated agreement of `(f1, f2)` would hand every scalar the consistent
witness `u + γ·v` on one shared set (code closure), contradicting the inconsistency
hypothesis; so correlated agreement fails, and then each close scalar is MCA-bad. -/
theorem mcaBadCount_ge_of_spread
    (C : Finset (ι → F)) (a : ℕ) (f1 f2 : ι → F) (Γ : Finset F)
    (hclosed : ∀ u ∈ C, ∀ v ∈ C, ∀ γ : F, (fun x => u x + γ * v x) ∈ C)
    (hclose : ∀ γ ∈ Γ, closeAt C a (pencil f1 f2 γ))
    (hincons : ¬ ∃ S : Finset ι, a ≤ S.card ∧
        ∀ γ ∈ Γ, ∃ c ∈ C, ∀ x ∈ S, pencil f1 f2 γ x = c x) :
    Γ.card ≤ mcaBadCount C a f1 f2 := by
  have hnc : ¬ corrAgree C a f1 f2 := by
    rintro ⟨S, hS, u, hu, v, hv, h1, h2⟩
    exact hincons ⟨S, hS, fun γ _ =>
      ⟨fun x => u x + γ * v x, hclosed u hu v hv γ,
        fun x hx => by simp [pencil, h1 x hx, h2 x hx]⟩⟩
  unfold mcaBadCount
  refine Finset.card_le_card fun γ hγ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hclose γ hγ, hnc⟩

/-- Fraction (error-probability) form of the bridge: the MCA bad fraction of the pencil
is at least `|Γ| / |F|`. -/
theorem mcaBadFraction_ge_of_spread
    (C : Finset (ι → F)) (a : ℕ) (f1 f2 : ι → F) (Γ : Finset F)
    (hclosed : ∀ u ∈ C, ∀ v ∈ C, ∀ γ : F, (fun x => u x + γ * v x) ∈ C)
    (hclose : ∀ γ ∈ Γ, closeAt C a (pencil f1 f2 γ))
    (hincons : ¬ ∃ S : Finset ι, a ≤ S.card ∧
        ∀ γ ∈ Γ, ∃ c ∈ C, ∀ x ∈ S, pencil f1 f2 γ x = c x) :
    (Γ.card : ℚ) / (Fintype.card F : ℚ) ≤ (mcaBadCount C a f1 f2 : ℚ) / (Fintype.card F : ℚ) := by
  have h := mcaBadCount_ge_of_spread C a f1 f2 Γ hclosed hclose hincons
  gcongr

/-! ## Concrete instance over `ZMod 5`

Domain: 3 points (`Fin 3`).  Code: the five constant words — Reed-Solomon with `k = 1`
on a 3-point domain.  Agreement threshold `a = 2 = k + t` with `t = 1`.

`f₁ = (0, 1, 2)` and `f₂ = (0, 1, 4)`; the pencil word at `γ` is `(0, 1 + γ, 2 + 4γ)`.
Coordinate collisions happen at `γ = 4` (coords 0,1), `γ = 2` (coords 0,2), and `γ = 3`
(coords 1,2), so exactly the three scalars `{2, 3, 4}` give close words, each witnessed
by a different constant on a different 2-point set, while `f₁` itself is injective, so
the pair has no correlated agreement at threshold 2. -/

/-- Constant words: Reed-Solomon with `k = 1` over a 3-point domain. -/
def C5 : Finset (Fin 3 → ZMod 5) :=
  Finset.univ.image fun c : ZMod 5 => fun _ => c

def g1 : Fin 3 → ZMod 5 := ![0, 1, 2]

def g2 : Fin 3 → ZMod 5 := ![0, 1, 4]

/-- The three bad scalars. -/
def Gam5 : Finset (ZMod 5) := {2, 3, 4}

/-- The constants code is closed under the pencil operation:
`(const a) + γ·(const b) = const (a + γ·b)`. -/
theorem C5_closed : ∀ u ∈ C5, ∀ v ∈ C5, ∀ γ : ZMod 5, (fun x => u x + γ * v x) ∈ C5 := by
  intro u hu v hv γ
  simp only [C5, Finset.mem_image, Finset.mem_univ, true_and] at hu hv ⊢
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  exact ⟨a + γ * b, rfl⟩

/-- Each scalar in `Gam5` gives a close pencil word (agreement `≥ 2` of 3). -/
theorem g_close : ∀ γ ∈ Gam5, closeAt C5 2 (pencil g1 g2 γ) := by decide

/-- No single 2-point agreement set carries codeword witnesses for all three bad
scalars simultaneously. -/
theorem g_incons : ¬ ∃ S : Finset (Fin 3), 2 ≤ S.card ∧
    ∀ γ ∈ Gam5, ∃ c ∈ C5, ∀ x ∈ S, pencil g1 g2 γ x = c x := by decide

/-- Stronger: the witnesses are PAIRWISE inconsistent — no shared 2-point agreement set
even for any two distinct bad scalars. -/
theorem g_pairwise_inconsistent :
    ∀ γ₁ ∈ Gam5, ∀ γ₂ ∈ Gam5, γ₁ ≠ γ₂ →
      ¬ ∃ S : Finset (Fin 3), 2 ≤ S.card ∧
        (∃ c ∈ C5, ∀ x ∈ S, pencil g1 g2 γ₁ x = c x) ∧
        (∃ c ∈ C5, ∀ x ∈ S, pencil g1 g2 γ₂ x = c x) := by decide

/-- The pair `(g1, g2)` has no correlated agreement at threshold 2 (directly). -/
theorem g_not_corrAgree : ¬ corrAgree C5 2 g1 g2 := by decide

/-- Explicit witness at `γ = 2`: the pencil word `(0, 3, 0)` matches the constant `0`
on the 2-point set `{0, 2}`. -/
theorem witness_two : agreeCount (pencil g1 g2 2) (fun _ => (0 : ZMod 5)) = 2 := by decide

/-- Explicit witness at `γ = 3`: the pencil word `(0, 4, 4)` matches the constant `4`
on `{1, 2}`. -/
theorem witness_three : agreeCount (pencil g1 g2 3) (fun _ => (4 : ZMod 5)) = 2 := by decide

/-- Explicit witness at `γ = 4`: the pencil word `(0, 0, 3)` matches the constant `0`
on `{0, 1}`. -/
theorem witness_four : agreeCount (pencil g1 g2 4) (fun _ => (0 : ZMod 5)) = 2 := by decide

/-- The bridge instantiated: at least three MCA-bad scalars on this pencil. -/
theorem concrete_badCount_ge_three : 3 ≤ mcaBadCount C5 2 g1 g2 := by
  have h := mcaBadCount_ge_of_spread C5 2 g1 g2 Gam5 C5_closed g_close g_incons
  have hc : Gam5.card = 3 := by decide
  omega

/-- Exact bad-scalar count: precisely the three scalars `{2, 3, 4}` are MCA-bad
(`γ = 0, 1` give pencil words `(0,1,2)`, `(0,2,1)` with all coordinates distinct, hence
agreement at most 1 with any constant). -/
theorem concrete_badCount_exact : mcaBadCount C5 2 g1 g2 = 3 := by decide

/-- The MCA bad fraction of this pencil is `3/5`: an MCA-error lower bound of `3/5`
for the constants code at agreement threshold 2 on a 3-point domain. -/
theorem concrete_badFraction :
    (mcaBadCount C5 2 g1 g2 : ℚ) / (Fintype.card (ZMod 5) : ℚ) = 3 / 5 := by
  have h5 : Fintype.card (ZMod 5) = 5 := by decide
  rw [concrete_badCount_exact, h5]
  norm_num

/-- Anti-degeneracy guard: the scalar set is nonempty and the code has all five
constants, so the instance exercises the bridge with genuine content. -/
theorem instance_nondegenerate : Gam5.card = 3 ∧ C5.card = 5 ∧ mcaBad C5 2 g1 g2 2 := by
  decide

end R15MCAGap

#print axioms R15MCAGap.mcaBadCount_ge_of_spread
#print axioms R15MCAGap.mcaBadFraction_ge_of_spread
#print axioms R15MCAGap.closeAt_pencil_of_corrAgree
#print axioms R15MCAGap.concrete_badCount_ge_three
#print axioms R15MCAGap.concrete_badCount_exact
#print axioms R15MCAGap.concrete_badFraction
#print axioms R15MCAGap.g_pairwise_inconsistent
#print axioms R15MCAGap.instance_nondegenerate
