/-
# The dyadic rigidity engine: divisibility by `Xᵐ + 1` forces ±-pairing (#444, char-0 half)

The unified prize conjecture is `defect = 0`: the char-`p` count of *non-coset* lacunary subsets of
`μ_{2^μ}` vanishes. The **char-0 half is provable** (Lam–Leung: a vanishing sum of `2^μ`-th roots of
unity decomposes into `±`-pairs), and this file formalizes its *engine*, the self-contained step that
makes it work and that **fails in char `p`** — pinpointing exactly where the wall lives.

The mechanism: a vanishing sum `Σ cⱼ ζ^j = 0` of `2^μ`-th roots of unity gives a polynomial
`g = Σ cⱼ Xʲ` with `g(ζ) = 0`. In characteristic `0`, `ζ`'s minimal polynomial is the cyclotomic
`Φ_{2^μ} = X^{2^{μ-1}} + 1` (irreducible over `ℚ`), so `(X^{2^{μ-1}} + 1) ∣ g`. Then — and this is the
engine proved here — **divisibility by `Xᵐ + 1` (with `deg g < 2m`) forces `g.coeff j = g.coeff (j+m)`**:
the multiplicity of `ζ^j` equals that of `ζ^{j+2^{μ-1}} = −ζ^j`, i.e. the roots come in `±`-pairs (a
coset of `μ₂`). Iterating gives the full dyadic-coset (lacunary ⟹ coset) rigidity.

**Why this is the wall, sharply:** in characteristic `p ≡ 1 mod 2^μ` (the prize regime), `Φ_{2^μ}`
*splits* in `F_p`, so `ζ ∈ F_p` and its minimal polynomial is just `X − ζ` (degree 1). Then `g(ζ)=0`
gives only `(X − ζ) ∣ g`, **NOT** `(X^{2^{μ-1}}+1) ∣ g` — the engine's hypothesis fails, the pairing is
not forced, and *non-coset* lacunary subsets (the defect) can appear. Char-0 rigidity is complete;
the char-`p` defect is the open core. This file proves the char-0 engine axiom-clean.

Axiom-clean: polynomial-coefficient algebra only. No `sorry`, no extra axioms.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring

namespace ArkLib.ProximityGap.EvenOddDescent

open Polynomial

variable {F : Type*} [Field F]

/-- **The dyadic rigidity engine.** If `Xᵐ + 1` divides `g` and `deg g < 2m` (with `m > 0`), then the
coefficients of `g` are symmetric under `j ↦ j + m`: `g.coeff j = g.coeff (j + m)` for every `j < m`.

Read on roots of unity (`ζ` a primitive `2^μ`-th root, `m = 2^{μ-1}`, so `ζ^m = −1`): the multiplicity
of `ζ^j` equals that of `ζ^{j+m} = −ζ^j`, i.e. **the roots pair up into `±`-pairs** — the char-0
dyadic-coset rigidity. The divisibility hypothesis holds in char `0` (cyclotomic irreducible) and
*fails* in char `p ≡ 1 mod 2^μ` (cyclotomic splits), which is precisely where the prize defect lives. -/
theorem coeff_symm_of_dvd_X_pow_add_one (m : ℕ) (hm : 0 < m) (g : F[X])
    (hg : (X ^ m + 1 : F[X]) ∣ g) (hdeg : g.natDegree < 2 * m) (j : ℕ) (hj : j < m) :
    g.coeff j = g.coeff (j + m) := by
  obtain ⟨q, rfl⟩ := hg
  -- handle the degenerate `q = 0` case (everything is `0`)
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; simp
  -- `Xᵐ + 1` is monic of degree `m`
  have hmonic : (X ^ m + 1 : F[X]).Monic := by
    have : (X ^ m + C (1 : F)).Monic := monic_X_pow_add_C (1 : F) hm.ne'
    simpa using this
  have hdegXm : (X ^ m + 1 : F[X]).natDegree = m := by
    have : (X ^ m + C (1 : F)).natDegree = m := natDegree_X_pow_add_C
    simpa using this
  -- degree of the product splits, giving `deg q < m`
  have hdegq : q.natDegree < m := by
    have hprod : ((X ^ m + 1 : F[X]) * q).natDegree = m + q.natDegree := by
      rw [hmonic.natDegree_mul' hq, hdegXm]
    rw [hprod] at hdeg; omega
  -- expand `(Xᵐ + 1) * q = q * Xᵐ + q` and read coefficients
  have hexp : (X ^ m + 1 : F[X]) * q = q * X ^ m + q := by ring
  rw [hexp]
  -- coeff at `j < m`: the `q * Xᵐ` part contributes `0`
  have hlo : (q * X ^ m + q).coeff j = q.coeff j := by
    rw [coeff_add, coeff_mul_X_pow', if_neg (by omega), zero_add]
  -- coeff at `j + m`: the `q * Xᵐ` part contributes `q.coeff j`, the bare `q` part `0`
  have hhi : (q * X ^ m + q).coeff (j + m) = q.coeff j := by
    rw [coeff_add, coeff_mul_X_pow', if_pos (by omega)]
    have : q.coeff (j + m) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [this, add_zero, Nat.add_sub_cancel]
  rw [hlo, hhi]

/-- **Iterated form: full antipodal symmetry of a `Xᵐ+1`-divisible polynomial.** Restates the engine
as: every coefficient in the bottom half equals its antipode in the top half. This is the exact
content "`g`'s root multiset is invariant under `ω ↦ −ω`" (char-0 dyadic rigidity), the statement whose
char-`p` failure is the proximity-prize wall. -/
theorem antipodal_coeff_of_dvd_X_pow_add_one (m : ℕ) (hm : 0 < m) (g : F[X])
    (hg : (X ^ m + 1 : F[X]) ∣ g) (hdeg : g.natDegree < 2 * m) :
    ∀ j < m, g.coeff j = g.coeff (j + m) :=
  fun j hj => coeff_symm_of_dvd_X_pow_add_one m hm g hg hdeg j hj

end ArkLib.ProximityGap.EvenOddDescent
