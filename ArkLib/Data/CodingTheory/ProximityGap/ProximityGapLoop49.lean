/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors

================================================================================
  ⚠️  DRAFT — NOT YET BUILD-VERIFIED  ⚠️
  Written while the shared `.lake/packages/mathlib` was being `rm -rf`'d and
  re-cloned at v4.7.0 by a concurrent agent (toolchain is v4.30.0). The algebra
  below is hand-checked and the mathlib lemma names are best-effort; this file
  must be run through `lake env lean` once the tree is restored before any claim
  of verification. Do NOT treat as axiom-clean until then.
================================================================================
-/
import Mathlib.Tactic

/-!
# Loop 49 (CLAIM 6.2 core, DRAFT) — the rational-function bridge of BCHKS §6.

This is the one residual cited by Loop47 (`hMany_bridge`). BCHKS Claim 6.2: at a point `α`, a value
`z = H(α)` of a codeword `H` that is `γ`-close to the received word `c` makes the combination
`f + z·g`  (`f(x) = c(x)/(x−α)`, `g(x) = −1/(x−α)`)  itself `γ`-close to the RS code — so every
`z ∈ L(α)` is a "bad" combining scalar. The algebraic heart is the quotient
`Q := (H − z)/(X − α)`, a codeword of strictly smaller degree, which agrees with `f + z·g` exactly on
`H`'s agreement set with `c`.

The pure-counting Hamming wrapper (`|disagree(f+z·g, Q)| ≤ |disagree(H,c)| ≤ γn`) over the repo's
`hammingDist`/`code` API is the remaining packaging; the algebraic core is here.
-/

namespace ArkLib.ProximityGap.Claim62Loop49

open Polynomial

variable {F : Type*} [Field F]

/-- **Claim 6.2 quotient.** If `H(α) = z` then `H = (X − C α)·Q + C z` for some `Q` — i.e.
`Q = (H − z)/(X − α)` is an honest polynomial (codeword). -/
theorem claim62_quotient (H : F[X]) {α z : F} (hH : H.eval α = z) :
    ∃ Q : F[X], H = (X - C α) * Q + C z := by
  have hroot : (H - C z).IsRoot α := by simp [Polynomial.IsRoot, hH]
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hroot
  exact ⟨Q, by rw [← hQ]; ring⟩

/-- **Quotient evaluation.** With `H = (X−Cα)·Q + C z` and `x ≠ α`, the quotient evaluates to the
rational function `(H(x) − z)/(x − α)`. -/
theorem claim62_eval {H Q : F[X]} {α z : F} (hHQ : H = (X - C α) * Q + C z)
    {x : F} (hx : x ≠ α) :
    Q.eval x = (H.eval x - z) / (x - α) := by
  have hxα : x - α ≠ 0 := sub_ne_zero.mpr hx
  have hev : H.eval x = (x - α) * Q.eval x + z := by
    rw [hHQ]; simp [eval_mul, eval_sub, eval_add, eval_C, eval_X]
  rw [eq_div_iff hxα]
  linear_combination -hev

/-- **The bridge identity.** At `x ≠ α` where the received word value `c` agrees with the codeword
`H` (`H(x) = c`), the codeword `Q` matches `f x + z · g x` with `f x = c/(x−α)`, `g x = −1/(x−α)`.
So `z ∈ L(α)` ⟹ `f + z·g` agrees with the codeword `Q` on all of `H`'s agreement set with `c`. -/
theorem claim62_bridge {H Q : F[X]} {α z c : F} (hHQ : H = (X - C α) * Q + C z)
    {x : F} (hx : x ≠ α) (hagree : H.eval x = c) :
    Q.eval x = c / (x - α) + z * (-1 / (x - α)) := by
  have hxα : x - α ≠ 0 := sub_ne_zero.mpr hx
  rw [claim62_eval hHQ hx, hagree]
  field_simp
  ring

/-
REMAINING (not drafted here, to add once the tree is restored):
* `claim62_degree` — `Q.natDegree < H.natDegree`, so `Q` is a codeword of the same `degreeLT k`
  code. Math: `H = (X−Cα)Q + Cz`, `natDegree (X−Cα) = 1` ⟹ `natDegree H = natDegree Q + 1`
  (when `Q ≠ 0`), via `natDegree_mul`, `natDegree_X_sub_C`, `natDegree_add_C`.
* The Hamming wrapper over the repo's `ReedSolomon.code` / `hammingDist`: from `claim62_bridge`,
  `disagree(f+z·g, eval Q) ⊆ disagree(eval H, c)`, and `H` is `γ`-close to `c`, so `f+z·g` is
  `γ`-close to the codeword `eval Q`; hence every `z ∈ L(α)` is a bad scalar — exactly Loop47's
  `hMany_bridge`. Pure `Finset.card_le_card` counting; needs the repo's distance API.
-/

end ArkLib.ProximityGap.Claim62Loop49

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Claim62Loop49.claim62_quotient
#print axioms ArkLib.ProximityGap.Claim62Loop49.claim62_eval
#print axioms ArkLib.ProximityGap.Claim62Loop49.claim62_bridge
