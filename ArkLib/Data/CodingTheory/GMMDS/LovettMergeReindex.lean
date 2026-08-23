/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettCoordMerge
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeIdentity
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Lovett's GM-MDS proof: the merge reindexing isomorphism (#389)

The first of the two sub-ingredients of the merge-branch contradiction (`MergeContradiction`):
the **reindexing** that transports the `Fin (n−1)`-side merged family to the `Fin n`-side
`substVarP` image.

The reindex coordinate map `mergeRho j : Fin (n−1) → Fin n` sends:
* the new last coordinate (`n−2`) ↦ `j` (the surviving merge coordinate), and
* an interior new coordinate `t` ↦ `mergeIdx j t` (its order-preserving lift).

It is **injective** (`mergeRho_injective`), so `MvPolynomial.rename (mergeRho j)` is an injective
`F`-algebra map `MvPolynomial (Fin (n−1)) F →ₐ[F] MvPolynomial (Fin n) F`
(`MvPolynomial.rename_injective`), and its coefficient lift carries the merged vanishing
polynomial to the collapsed one:

* `renameP_pVanish_mergeVec` — `renameP (mergeRho j) (pVanish (mergeVec j v)) = pVanish (collapseVec j v)`.

Composed with the collapse identity `substVarP_pVanish`, this is the transport identity

> `renameP (mergeRho j) (pVanish (mergeVec j v)) = substVarP last↦j (pVanish v)`,

i.e. the renamed merged family equals the substitution image of the original family.  This is the
bridge that lets the `n−1`-IH independence of the merged system be used inside the original ring.

Issue #389.
-/

open Finset Polynomial MvPolynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- The reindex coordinate map for the merge: the new last coordinate maps to the surviving
merge coordinate `j`, every interior new coordinate maps via its order-preserving lift. -/
def mergeRho {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (t : Fin (n - 1)) : Fin n :=
  if (t : ℕ) = n - 1 - 1 then j else mergeIdx hn j t

/-- `mergeRho` is injective. -/
theorem mergeRho_injective {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) :
    Function.Injective (mergeRho hn j) := by
  intro a b hab
  unfold mergeRho at hab
  by_cases ha : (a : ℕ) = n - 1 - 1 <;> by_cases hb : (b : ℕ) = n - 1 - 1
  · apply Fin.ext; omega
  · -- a is last-new, b interior: mergeRho a = j = mergeIdx b → contradiction (mergeIdx ≠ j)
    rw [if_pos ha, if_neg hb] at hab
    exact absurd hab.symm (mergeIdx_ne_j hn j b)
  · rw [if_neg ha, if_pos hb] at hab
    exact absurd hab (mergeIdx_ne_j hn j a)
  · rw [if_neg ha, if_neg hb] at hab
    exact mergeIdx_injective hn j hab

/-- The coefficient-lifted reindex `MvPolynomial (Fin (n−1)) F)[X] →ₐ[F] (MvPolynomial (Fin n) F)[X]`. -/
noncomputable def renameP (F : Type*) [Field F] {n : ℕ} (ρ : Fin (n - 1) → Fin n) :
    (MvPolynomial (Fin (n - 1)) F)[X] →ₐ[F] (MvPolynomial (Fin n) F)[X] :=
  Polynomial.mapAlgHom (MvPolynomial.rename ρ)

@[simp] theorem renameP_X {n : ℕ} (ρ : Fin (n - 1) → Fin n) :
    renameP F ρ Polynomial.X = Polynomial.X := by simp [renameP]

theorem renameP_C {n : ℕ} (ρ : Fin (n - 1) → Fin n) (a : MvPolynomial (Fin (n - 1)) F) :
    renameP F ρ (Polynomial.C a) = Polynomial.C (MvPolynomial.rename ρ a) := by
  simp [renameP]

/-- The image of a linear factor `x − a_t` under the reindex. -/
theorem renameP_xSubA {n : ℕ} (ρ : Fin (n - 1) → Fin n) (t : Fin (n - 1)) :
    renameP F ρ (xSubA t) = xSubA (ρ t) := by
  unfold xSubA
  rw [map_sub, renameP_X, renameP_C, MvPolynomial.rename_X]

/-- **The reindex transports the merged vanishing polynomial to the collapsed one.**
`renameP (mergeRho j) (pVanish (mergeVec j v)) = pVanish (collapseVec j v)`. -/
theorem renameP_pVanish_mergeVec {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (v : Fin n → ℕ) :
    renameP F (mergeRho (by omega : 1 ≤ n) j) (pVanish (mergeVec (by omega : 1 ≤ n) j v))
      = pVanish (collapseVec (by omega : 1 ≤ n) j v) := by
  classical
  have hn : 1 ≤ n := by omega
  set l := lastCoord n hn with hldef
  have hjl : j ≠ l := by
    intro h
    have : (j : ℕ) = n - 1 := by rw [h, hldef]; simp only [lastCoord]
    omega
  -- LHS: rename the product over Fin (n-1)
  rw [pVanish, map_prod]
  have hLHS : ∀ t : Fin (n - 1),
      renameP F (mergeRho hn j) ((xSubA t) ^ (mergeVec hn j v t))
        = (xSubA (mergeRho hn j t)) ^ (mergeVec hn j v t) := by
    intro t; rw [map_pow, renameP_xSubA]
  rw [Finset.prod_congr rfl (fun t _ => hLHS t)]
  -- Reindex the product over Fin (n-1) along the injection mergeRho into Fin n.
  -- Image = univ \ {l} (mergeRho hits everything except the old last coordinate l).
  rw [pVanish]
  -- Compute via: ∏_{t} (xSubA (ρ t))^{mergeVec t} = ∏_{c ∈ image ρ} (xSubA c)^{...} and the
  -- complement (just {l}) contributes 1 on the RHS (collapseVec l = 0).
  -- Use prod over univ on RHS = (prod over image) * (term at l), with collapseVec l = 0.
  have himg : (Finset.univ : Finset (Fin (n - 1))).image (mergeRho hn j) = Finset.univ \ {l} := by
    apply Finset.ext; intro c
    rw [Finset.mem_sdiff]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨t, rfl⟩
      unfold mergeRho
      by_cases ht : (t : ℕ) = n - 1 - 1
      · rw [if_pos ht]; exact hjl
      · rw [if_neg ht]; exact mergeIdx_ne_last hn j t (by omega)
    · intro hc
      -- c ≠ l; find preimage
      by_cases hcj : c = j
      · exact ⟨⟨n - 1 - 1, by omega⟩, by unfold mergeRho; rw [if_pos rfl, hcj]⟩
      · -- c ≠ j, c ≠ l: it is mergeIdx of some interior t
        have : c ∈ Finset.univ \ {j, l} := by
          rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨Finset.mem_univ _, by push_neg; exact ⟨hcj, hc⟩⟩
        rw [← mergeIdx_image_interior hn j hjlt] at this
        rw [Finset.mem_image] at this
        obtain ⟨t, ht, rfl⟩ := this
        simp only [Finset.mem_filter] at ht
        exact ⟨t, by unfold mergeRho; rw [if_neg (by omega)]⟩
  -- key pointwise identity: collapseVec (ρ t) = mergeVec t
  have hpt : ∀ t : Fin (n - 1), collapseVec hn j v (mergeRho hn j t) = mergeVec hn j v t := by
    intro t
    unfold mergeRho mergeVec collapseVec
    by_cases ht : (t : ℕ) = n - 1 - 1
    · -- merged: ρ t = j, collapseVec j = v j + v l
      rw [if_pos ht, if_pos ht, if_neg hjl, if_pos rfl]
    · -- interior: ρ t = mergeIdx t, which is ≠ j and ≠ l
      rw [if_neg ht, if_neg ht]
      rw [if_neg (mergeIdx_ne_last hn j t (by omega)), if_neg (mergeIdx_ne_j hn j t)]
  -- RHS: drop the {l} term (collapseVec l = 0 ⟹ factor = 1), then reindex via the image
  have hlterm : (xSubA (F := F) l) ^ (collapseVec hn j v l) = 1 := by
    have : collapseVec hn j v l = 0 := by unfold collapseVec; rw [if_pos rfl]
    rw [this, pow_zero]
  have himg' : Finset.univ \ ({l} : Finset (Fin n)) = Finset.univ.erase l := by
    rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.prod_erase (Finset.univ) (a := l) hlterm, ← himg', ← himg,
    Finset.prod_image (fun a _ b _ h => mergeRho_injective hn j hjlt h)]
  -- now: ∏_t (xSubA (ρ t))^{mergeVec t} = ∏_t (xSubA (ρ t))^{collapseVec (ρ t)}
  exact Finset.prod_congr rfl (fun t _ => by rw [hpt t])

/-- The reindex transport lifted to the shifted family `pFam` (`X^e` is fixed by `renameP`). -/
theorem renameP_pFam_mergeVec {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (v : Fin n → ℕ) (e : ℕ) :
    renameP F (mergeRho (by omega : 1 ≤ n) j) (pFam (mergeVec (by omega : 1 ≤ n) j v) e)
      = pFam (collapseVec (by omega : 1 ≤ n) j v) e := by
  unfold pFam
  rw [map_mul, renameP_pVanish_mergeVec hn2 j hjlt, map_pow, renameP_X]

/-- **The merge transport identity.**  The renamed merged family equals the substitution image of
the original family: `renameP (mergeRho j) (pFam (mergeVec j v) e) = substVarP last↦j (pFam v e)`.
This is the bridge that carries the `n−1`-IH independence of the merged system into the original
ring `MvPolynomial (Fin n) F`, where the substitution-divisibility kernel
`sub_X_dvd_of_subst_eq_zero` operates. -/
theorem renameP_pFam_eq_substVarP_pFam {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (v : Fin n → ℕ) (e : ℕ) :
    renameP F (mergeRho (by omega : 1 ≤ n) j) (pFam (mergeVec (by omega : 1 ≤ n) j v) e)
      = substVarP F j (lastCoord n (by omega)) (pFam v e) := by
  have hjl : j ≠ lastCoord n (by omega) := by
    intro h; rw [h] at hjlt; simp only [lastCoord] at hjlt; omega
  rw [renameP_pFam_mergeVec hn2 j hjlt, substVarP_pFam (by omega) j hjl]

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.mergeRho_injective
#print axioms ArkLib.GMMDS.renameP_xSubA
#print axioms ArkLib.GMMDS.renameP_pVanish_mergeVec
#print axioms ArkLib.GMMDS.renameP_pFam_eq_substVarP_pFam
