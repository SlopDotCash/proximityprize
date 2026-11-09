/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-!
# The newest-first compatibility view of Binary Basefold challenges

Canonical statements and `getFoldingChallenges` use chronological indices. Historical downstream
statements used newest-first indices. This adapter converts that explicit input convention before
delegating to the canonical slice; it does not change canonical statement storage or folding.
-/

namespace Binius.BinaryBasefold.Compatibility

/-- Read a chronological folding slice from an explicitly newest-first challenge vector. -/
def newestFirstFoldingChallenges {r ℓ 𝓡 ϑ : ℕ} {L : Type} (i : Fin (ℓ + 1))
    (challenges : Fin i → L) (k : ℕ) (h : k + ϑ ≤ i) : Fin ϑ → L :=
  getFoldingChallenges (r := r) (𝓡 := 𝓡) i (fun j => challenges j.rev) k h

/-- Reversing a canonical vector supplies the compatibility adapter's newest-first input. -/
theorem newestFirstFoldingChallenges_reverse {r ℓ 𝓡 ϑ : ℕ} {L : Type} (i : Fin (ℓ + 1))
    (challenges : Fin i → L) (k : ℕ) (h : k + ϑ ≤ i) :
    newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
        i (fun j => challenges j.rev) k h =
      getFoldingChallenges (r := r) (𝓡 := 𝓡) i challenges k h := by
  funext j
  simp only [newestFirstFoldingChallenges, getFoldingChallenges, Fin.rev_rev]

end Binius.BinaryBasefold.Compatibility

#print axioms Binius.BinaryBasefold.Compatibility.newestFirstFoldingChallenges_reverse
