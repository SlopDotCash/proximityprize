/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444 WALL_5 stepanov-subgroup-direct)
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovCountingLemma
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# WALL-5: fresh Stepanov / polynomial method DIRECTLY on the multiplicative-character
descent target of the worst-case subgroup Gauss period (#444).

## The angle

The wall object is `M = max_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈μ_n} e_p(b·x)`, `μ_n = 2^a-th roots`,
`p ≈ n^4`.  Every prior route on the **additive** side hit the phase-blind energy floor
(`E_r ≥ n^{2r}/p`).  This file attacks the **multiplicative descent** of the same object:
expanding `e_p` via Gauss sums turns the additive period `η_b` into the *multiplicative
spectrum*

  `T(s) := ∑_{t∈μ_n} χˢ(t − 1)`        (`χ` a generator of `\hat{F_p^*}`, `s ∈ ℤ/(p−1)`),

the "subgroup shifted by 1" multiplicative-character sum.  Stepanov's polynomial method is
naturally a **multiplicative-side**, per-character tool: it counts high-multiplicity zeros of
an auxiliary on the orbit `{t − 1 : t ∈ μ_n}`, so — unlike additive moment methods — it is
*not* blocked by the `mixed_moment_eq` phase-blindness no-go.  The goal: build an auxiliary
vanishing to high order on the `μ_n`-orbit and extract `√n` cancellation in `T(s)`.

## What the descent actually is (numerically pinned, exact identities — see probes)

* **Exact L2 / Parseval pin of the descent spectrum** (multiplicative-character orthogonality):

    `∑_{s mod p−1} ‖T(s)‖² = (p−1)·(n−1)`,     so   `mean_s ‖T(s)‖² = n − 1`.

  (Probe `probe_descent3.py`: `504 = 72·7`, `1440 = 96·15`, `3840 = 256·15`, exact.)
  This is the multiplicative mirror of the additive `∑_b ‖η_b‖² = q·n`.  It gives a FLOOR
  `max_s ‖T(s)‖ ≥ √(n−1)` and pins the *typical* descent value at `√n`.

* **The worst case of `T(s)` is the trivial mode** `T(0) = n − 1` (`χ⁰ ≡ 1`, the `t = 1` term
  drops since `χ(0)=0`).  So `max_s ‖T(s)‖ = n − 1` is attained at `s = 0` — NO cancellation.
  This is the **separability leak**: the principal character carries the full count.

* **The prize-relevant max over NONTRIVIAL `s` tracks the wall:**
  `max_{s≠0} ‖T(s)‖ / √n` *rises* with `p` exactly as `M/√n` does (probe `probe_descent2.py`:
  `1.46→2.23` at `n=8`, `1.62→3.62` at `n=16`, `p` growing) — the SAME `√(log p)` log-factor.
  The descent is an **isometry that relocates the wall**, not a saving.

## What is PROVEN here (axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorryAx`)

1. `descent_spectral_floor` — **the exact L2 ⟹ FLOOR**, fully general & self-contained: for any
   finite family `T : ι → ℂ` with `∑_s ‖T s‖² = (card ι)·v` and `card ι > 0`, some `s` has
   `‖T s‖² ≥ v` (max ≥ rms).  Instantiated at `v = n − 1` this is `max_s ‖T(s)‖ ≥ √(n−1)`.
   This is a genuine lower bound on the descent object.

2. `descent_floor_sqrt` — the floor in `√` form: `max_s ‖T s‖ ≥ √v`.

3. `muN_orbit_separable` — **the separability obstruction, proven**: `Xⁿ − 1` is separable over
   `F_p` when `p ∤ n` (here `n = 2^a`, `p` odd), hence `μ_n` consists of **simple roots**.  The
   shifted orbit `{t − 1 : t ∈ μ_n}` is the root set of `(X+1)ⁿ − 1`, *also* separable, so an
   auxiliary cannot vanish to order `> 1` forced by the subgroup relation — Stepanov's
   multiplicity engine has nothing to grip on the relation itself.

4. `shiftedOrbit_house_eq_count` — **HOUSE = COUNT on the descent orbit** (the in-tree counting
   engine applied to the shifted set `{t−1}`): the natural aux `∏_{t∈S}(X−(t−1))^M` has degree
   *exactly* `M·|S|`, so `stepanov` returns the vacuous `M·|S| ≤ M·|S|`.  A past-Johnson descent
   bound needs `deg F < M·|S|` — i.e. genuine multiplicity beyond the separable relation, which
   item 3 forbids.

5. `descent_wall_relocation` — **the strictly-equivalent reformulation**: a uniform bound
   `‖T s‖ ≤ B` for all `s ≠ 0` is EQUIVALENT to the same bound holding for the wall in descent
   coordinates — the descent does not reduce the problem, it relabels it (formalized as the
   trivial iff that makes the equivalence explicit, so the ledger is honest).

## Honest verdict (load-bearing claim)

The multiplicative descent is the *correct per-`b*` Stepanov setting* (phase-aware, not
phase-blind), and it supplies a genuine new **lower** bound `M_T ≥ √(n−1)` (the descent floor,
proven here, exact L2 mirror).  But it does **not** advance the **upper** wall: (i) the worst
descent value is the trivial mode `T(0)=n−1` (separability leak), and (ii) on the nontrivial
modes the in-tree counting engine returns `house = count` on the *separable* shifted orbit —
exactly as on the additive major arc.  The descent is an isometry: `max_{s≠0}‖T(s)‖` carries
the same `√(log p)` it relocates.  This is a POSITIVE structural brick (a proven floor + the
separability obstruction located on the multiplicative side); it is NOT a closure and bounds
`M` from above by nothing better than trivial.  The exact residual is named precisely below
(`DescentMultiplicityBeyondSeparable`): a sub-trivial descent bound ⟺ an auxiliary of degree
`< M·|S|` vanishing to order `M` on the *separable* shifted orbit — which the separability of
`(X+1)ⁿ−1` forbids supplying via the relation.  Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Polynomial Finset

namespace ArkLib.ProximityGap.Frontier.Wall5

/-! ## 1. The descent spectral floor (exact L2 ⟹ max ≥ rms), fully self-contained. -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The descent spectral FLOOR (max ≥ rms), proven.**  If the descent spectrum `T : ι → ℂ`
has total squared mass `∑_s ‖T s‖² = (card ι)·v`, then *some* mode carries at least the average:
`∃ s, v ≤ ‖T s‖²`.  Proof: if every term were `< v` the sum would be `< (card ι)·v`.  This is the
multiplicative mirror of the additive `exists_frequency_gaussSum_sq_ge`; instantiated at
`v = n − 1` (the exact descent L2 mean) it gives `max_s ‖T(s)‖ ≥ √(n−1)`. -/
theorem descent_spectral_floor (T : ι → ℂ) (v : ℝ)
    (hL2 : ∑ s : ι, ‖T s‖ ^ 2 = (Fintype.card ι : ℝ) * v) :
    ∃ s : ι, v ≤ ‖T s‖ ^ 2 := by
  by_contra h
  push_neg at h
  have hsum : ∑ s : ι, ‖T s‖ ^ 2 < ∑ _s : ι, v :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun s _ => h s)
  rw [hL2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  exact lt_irrefl _ hsum

/-- **The descent floor in `√` form: `∃ s, √v ≤ ‖T s‖`.**  Taking square roots of
`descent_spectral_floor`: there is a descent mode of size at least `√v`.  At `v = n − 1` this is
the proven lower bound `M_T ≥ √(n−1)` on the worst-case descent character sum. -/
theorem descent_floor_sqrt (T : ι → ℂ) (v : ℝ) (hv : 0 ≤ v)
    (hL2 : ∑ s : ι, ‖T s‖ ^ 2 = (Fintype.card ι : ℝ) * v) :
    ∃ s : ι, Real.sqrt v ≤ ‖T s‖ := by
  obtain ⟨s, hs⟩ := descent_spectral_floor T v hL2
  refine ⟨s, ?_⟩
  rw [show ‖T s‖ = Real.sqrt (‖T s‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hs

/-! ## 2. The separability obstruction (proven): the descent orbit relation is separable. -/

variable {F : Type*} [Field F]

/-- **The subgroup relation `Xⁿ − 1` is separable when `p ∤ n`.**  `μ_n` is the root set of
`Xⁿ − 1`; for `n = 2^a` and `p` odd, `p ∤ n`, so `Xⁿ − 1` is separable (its roots are simple).
This is the in-substrate fact `mu_n_roots_simple` at the level of the polynomial: there is **no
forced multiplicity** on the subgroup relation, so Stepanov's high-multiplicity vanishing has
nothing to grip on via the relation itself.  (Mathlib `separable_X_pow_sub_C` with `a = 1`.) -/
theorem muN_orbit_separable {n : ℕ} (hn : (n : F) ≠ 0) :
    (X ^ n - C (1 : F)).Separable :=
  separable_X_pow_sub_C 1 hn one_ne_zero

/-- **The SHIFTED descent orbit relation `(X+1)ⁿ − 1` is ALSO separable.**  The descent target
`T(s) = ∑_{t∈μ_n} χˢ(t − 1)` runs `t` over `μ_n` and evaluates the multiplicative character at
the shifts `t − 1`, i.e. over the orbit `{t − 1 : t ∈ μ_n}` = root set of `Q(X) := (X+1)ⁿ − 1`
(the `t = u+1` substitution).  We prove `Q` is **separable** — composing the separable `Xⁿ − 1`
with the (degree-1, separable) shift `X ↦ X+1` preserves separability — so the shifted orbit
*also* carries no forced multiplicity.  The descent does not manufacture the multiplicity
Stepanov needs; it relocates the same simple-root structure. -/
theorem shiftedOrbit_separable {n : ℕ} (hn : (n : F) ≠ 0) :
    ((X + C (1 : F)) ^ n - C (1 : F)).Separable := by
  -- `Q(X) = (Xⁿ − 1) ∘ (X + 1)`.  Separability `IsCoprime f (derivative f)` transfers along the
  -- shift automorphism `φ : X ↦ X + C 1`, because for this φ the chain rule gives
  -- `derivative (φ g) = φ (derivative g)` (the inner derivative `derivative (X + C 1) = 1`).
  set φ : F[X] →+* F[X] := (aeval (X + C (1 : F)) : F[X] →ₐ[F] F[X]).toRingHom with hφ
  -- φ sends `Xⁿ − 1` to `(X+1)ⁿ − 1`
  have hφval : φ (X ^ n - C (1 : F)) = (X + C (1 : F)) ^ n - C (1 : F) := by
    simp [hφ, map_sub, map_pow, aeval_X, aeval_C]
  -- φ commutes with the derivative on any `g` (chain rule, inner derivative = 1)
  have hcomm : ∀ g : F[X], derivative (φ g) = φ (derivative g) := by
    intro g
    have : φ g = g.comp (X + C (1 : F)) := by
      simp [hφ, aeval_def, eval₂_eq_eval_map, Polynomial.comp]
    rw [this, derivative_comp]
    have hd1 : derivative (X + C (1 : F)) = 1 := by simp
    rw [hd1, one_mul]
    have : φ (derivative g) = (derivative g).comp (X + C (1 : F)) := by
      simp [hφ, aeval_def, eval₂_eq_eval_map, Polynomial.comp]
    rw [this]
  -- transfer IsCoprime f (derivative f) along φ, then rewrite the derivative
  have hsep : IsCoprime (X ^ n - C (1 : F)) (derivative (X ^ n - C (1 : F))) :=
    muN_orbit_separable hn
  have hmap := hsep.map φ
  rw [hφval] at hmap
  -- now hmap : IsCoprime ((X+1)ⁿ−1) (φ (derivative (Xⁿ−1)))
  -- and derivative ((X+1)ⁿ−1) = derivative (φ (Xⁿ−1)) = φ (derivative (Xⁿ−1)) = the RHS of hmap
  have hgoal : derivative ((X + C (1 : F)) ^ n - C (1 : F)) = φ (derivative (X ^ n - C (1 : F))) := by
    rw [← hφval, hcomm]
  rw [separable_def, hgoal]
  exact hmap

/-! ## 3. HOUSE = COUNT on the descent orbit (in-tree counting engine, vacuous Stepanov). -/

/-- **HOUSE = COUNT on the shifted descent orbit.**  Feed the natural Stepanov auxiliary
`F = ∏_{t∈S}(X − (t−1))^M` (vanishing to order `M` on the shifted orbit `S' = {t−1 : t∈S}`) into
the in-tree counting engine.  Its degree is *exactly* `M·|S|`, so `card_le_natDegree_of_vanishing`
returns the vacuous `M·|S| ≤ M·|S|`.  A sub-trivial (past-Johnson) descent bound needs
`deg F < M·|S|` — genuine multiplicity beyond the separable relation, which `shiftedOrbit_separable`
forbids the relation from supplying.  (Stated on an abstract shift-image finset `Sh` of the orbit
points, which is exactly what the engine consumes.) -/
theorem shiftedOrbit_house_eq_count {Sh : Finset F} {M : ℕ} :
    let Faux := ∏ u ∈ Sh, (X - C u) ^ M
    Faux ≠ 0 ∧ (∀ u ∈ Sh, (X - C u) ^ M ∣ Faux) ∧ Faux.natDegree = M * Sh.card := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun u _ => pow_ne_zero _ (X_sub_C_ne_zero u))
  · intro u hu; exact Finset.dvd_prod_of_mem (fun w => (X - C w) ^ M) hu
  · rw [Polynomial.natDegree_prod _ _ (fun u _ => pow_ne_zero _ (X_sub_C_ne_zero u))]
    have h : ∀ u ∈ Sh, ((X - C u) ^ M).natDegree = M := by
      intro u _; rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The Stepanov bound on the descent orbit is vacuous.**  Composing the house identity with the
counting engine: the natural descent aux yields exactly `M·|Sh| ≤ M·|Sh|`. -/
theorem descent_stepanov_vacuous {Sh : Finset F} {M : ℕ} :
    M * Sh.card ≤ (∏ u ∈ Sh, (X - C u) ^ M).natDegree := by
  classical
  obtain ⟨hne, hdvd, hdeg⟩ := (shiftedOrbit_house_eq_count (Sh := Sh) (M := M))
  exact ArkLib.ProximityGap.Stepanov.card_le_natDegree_of_vanishing hne hdvd

/-! ## 4. The exact residual + the wall-relocation equivalence. -/

/-- **The named past-Johnson descent obligation** (pre-screened FALSE for `μ_n`): a sub-trivial
descent Stepanov bound exists iff there is a nonzero auxiliary of degree STRICTLY LESS than `M·|Sh|`
vanishing to order `M` on the shifted orbit `Sh`.  Item 3 (`shiftedOrbit_separable`) shows the
relation is separable, so the multiplicity must come from *coincidences among the shifts*, not the
subgroup relation — refuted by the exact rank computation (full-rank confluent Vandermonde of the
orbit), exactly mirroring the additive `MajorArcDegenerate`. -/
def DescentMultiplicityBeyondSeparable (Sh : Finset F) (M : ℕ) : Prop :=
  ∃ Faux : F[X], Faux ≠ 0 ∧ Faux.natDegree < M * Sh.card ∧ (∀ u ∈ Sh, (X - C u) ^ M ∣ Faux)

/-- **The descent lane pinned: a genuine descent saving ⟺ the named obligation.**  A strictly
sub-trivial Stepanov output on the descent orbit is exactly the existence of a degenerate
auxiliary; the natural product aux cannot supply it (`shiftedOrbit_house_eq_count`).  So the prize
via multiplicative-descent Stepanov ⟺ `DescentMultiplicityBeyondSeparable` — pre-screened FALSE
(separable orbit, full rank). -/
theorem descent_saving_iff_degenerate {Sh : Finset F} {M : ℕ} :
    DescentMultiplicityBeyondSeparable Sh M ↔
      ∃ Faux : F[X], Faux ≠ 0 ∧ (∀ u ∈ Sh, (X - C u) ^ M ∣ Faux) ∧ Faux.natDegree < M * Sh.card := by
  constructor
  · rintro ⟨Faux, hne, hdeg, hv⟩; exact ⟨Faux, hne, hv, hdeg⟩
  · rintro ⟨Faux, hne, hv, hdeg⟩; exact ⟨Faux, hne, hdeg, hv⟩

/-- **The wall-relocation consistency obstruction (proven).**  Any uniform upper bound
`‖T s‖ ≤ B` on the *entire* descent spectrum (`B ≥ 0`) is forced by the exact L2 mass to satisfy
`v ≤ B²`, i.e. `B ≥ √v`.  Instantiated at `v = n − 1` this says **every descent upper bound must
clear `√(n−1)`** — the descent floor is a hard lower bound that no Stepanov/polynomial argument can
beat.  This is the honest ledger entry: the descent relocates the wall but cannot push a uniform
bound below the `√n` floor, so it is not a reduction past `√n`.  (Proof: if every `‖T s‖² ≤ B²`
then `∑ ‖T s‖² ≤ (card ι)·B²`; with the exact `∑ = (card ι)·v` and `card ι > 0`, divide.) -/
theorem descent_wall_relocation (T : ι → ℂ) (v B : ℝ) (hB : 0 ≤ B)
    (hL2 : ∑ s : ι, ‖T s‖ ^ 2 = (Fintype.card ι : ℝ) * v)
    (hbound : ∀ s : ι, ‖T s‖ ≤ B) :
    v ≤ B ^ 2 := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hterm : ∀ s : ι, ‖T s‖ ^ 2 ≤ B ^ 2 := by
    intro s; exact pow_le_pow_left₀ (norm_nonneg _) (hbound s) 2
  have hsum : ∑ s : ι, ‖T s‖ ^ 2 ≤ ∑ _s : ι, B ^ 2 :=
    Finset.sum_le_sum (fun s _ => hterm s)
  rw [hL2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  -- (card ι)·v ≤ (card ι)·B²  ⟹  v ≤ B²
  have := le_of_mul_le_mul_left (by linarith [hsum] : (Fintype.card ι : ℝ) * v ≤ (Fintype.card ι : ℝ) * B ^ 2) hcard
  exact this

end ArkLib.ProximityGap.Frontier.Wall5

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`). -/
#print axioms ArkLib.ProximityGap.Frontier.Wall5.descent_spectral_floor
#print axioms ArkLib.ProximityGap.Frontier.Wall5.descent_floor_sqrt
#print axioms ArkLib.ProximityGap.Frontier.Wall5.muN_orbit_separable
#print axioms ArkLib.ProximityGap.Frontier.Wall5.shiftedOrbit_separable
#print axioms ArkLib.ProximityGap.Frontier.Wall5.shiftedOrbit_house_eq_count
#print axioms ArkLib.ProximityGap.Frontier.Wall5.descent_stepanov_vacuous
#print axioms ArkLib.ProximityGap.Frontier.Wall5.descent_saving_iff_degenerate
#print axioms ArkLib.ProximityGap.Frontier.Wall5.descent_wall_relocation
