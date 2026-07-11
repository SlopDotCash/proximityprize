/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R301CubicCyclotomyM9
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# LANE B2 (#466, r=3 rung): the trace-formula / point-count reformulation — the
  DIST stratum diagonalizes in the DFT, each mode is a Newton polynomial in
  3-term coset slices, and the rung reduces to POINTWISE FLATNESS of the full
  Jacobi DFT

## The discovery (this session, 2026-07-10; probe
   `scripts/probes/probe_466_r3_trace_formula_point_count.py`, m = 9 AND m = 12,
   63 primes, every identity verified to machine precision)

Write `m = 3u'`.  The `H = {0,u,2u}`-cosets of `ℤ/m` are the fibers of the ring
map `label : ℤ/m → ℤ/u'` — there are `u'` cosets, EACH OF SIZE 3.  Splitting the
coefficients into coset slices `Aᶜ` and taking the DFT over `ℤ/m`:

1. **Slice decomposition** (`distStratum_slice_decomposition`, unconditional):
   `distStratum = ∑_{c⃗ pairwise distinct} conv3(slice c₁, slice c₂, slice c₃)`.
2. **Mode factorization + Newton** (`hatF_distStratum`, unconditional): in every
   DFT mode `a`, with `Âᶜ(a)` the slice transforms and `Ŝ = ∑_c Âᶜ`,
   `D̂(a) = Ŝ(a)³ − 3·Ŝ(a)·P₂(a) + 2·P₃(a)`,  `P_r(a) = ∑_c Âᶜ(a)^r`.
3. **Parseval** (`hatF_parseval`, unconditional): `m·E_DIST = ∑_a ‖D̂(a)‖²`.
4. **3-term slices** (`norm_hatSlice_le`, unconditional): each coset has only 3
   elements, so `‖Âᶜ(a)‖ ≤ 3√q` with NO cancellation input; hence `P₂, P₃` are
   unconditionally at the target scale and the ENTIRE open content of the rung
   collapses onto the single full-spectrum object `Ŝ(a)`:
   **`FullDFTFlat K` (`∀ a, ‖Ŝ(a)‖ ≤ K·√(mq)`) ⟹
     `DistStratumEnergyBound ((K³+9K+18)²)`**
   (`distStratumEnergyBound_of_fullDFTFlat`).  The Prop is calibrated:
   `K = √m` holds unconditionally (`fullDFTFlat_sqrt_m`, recovering the
   baseline), Parseval pins the AVERAGE of `‖Ŝ‖²` at `≤ m·q` exactly
   (`hatSfun_energy_le`, i.e. flat-on-average with `K = 1`), and the probe
   measures `sup_a ‖Ŝ(a)‖²/(mq) ∈ [1, 4.7]`, flat in `q`, at BOTH m = 9 and
   m = 12 — the first open instance.  The reduction is strict: a SEXTIC moment
   problem became a POINTWISE QUADRATIC bound on one exponential sum.

## The point-count side (probe-verified exactly; deliberately NOT named in Lean)

`Ŝ(a) = m·T₋ₐ + 1` with `T_α = ∑_{ind t ≡ α (m)} χ(1−t)` (identity I2), and the
Galois average over the `φ(m)` characters `χ = λ^k` obeys the Fu–Wan-style
trace formula (I3):
  `∑_k ‖T_α⁽ᵏ⁾‖² = ∑_{d∣m} d·μ(m/d)·N_d(α)`,
`N_d(α) = #{(t,s) ∈ C_α² : (1−t)/(1−s) ∈ (F_q^*)^d}` — Möbius-weighted counts
of `F_q`-points on explicit Fermat-type varieties
(`m²·d·N_d(α) = #{(x,y,z) ∈ (F_q^*)³ : 1−g^α x^m = (1−g^α y^m)·z^d}`, identity
I4, verified by direct enumeration).  This is the exact mechanism behind the
m = 9 integer phenomenon (R301), now proved to persist at m = 12.  MECHANISM
CAVEAT (the honest refutation content): the Weil main terms of the `N_d` cancel
IDENTICALLY (`∑_{d∣m} μ(m/d) = 0`), so the point count is PURE error term — no
`polynomial(q)` main term survives, and Weil/Deligne on the varieties alone
cannot discharge `FullDFTFlat` with an absolute `K`: per-mode, Weil gives only
`‖Ŝ(a)‖ ≤ (m−1)√q + O(1)`, i.e. `K = O(√m)`.  The open content is genuine
square-root cancellation ACROSS the `m` Jacobi angles inside each mode —
Katz-style vertical equidistribution, exactly as calibrated in the R300 kb
note.  Naming a sheaf-theoretic surrogate would launder the gap; the honest
Lean-side open object is `FullDFTFlat` (equivalently `DistStratumEnergyBound`).

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount

open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting

/-! ### Generic DFT layer over `ZMod N` -/

section GenericDFT

variable {N : ℕ} [NeZero N]

/-- Triple additive convolution in the R300 index normalization. -/
noncomputable def conv3 (f g h : ZMod N → ℂ) (d : ZMod N) : ℂ :=
  ∑ j : ZMod N, ∑ i : ZMod N, f i * g (d - j - i) * h j

/-- The DFT attached to an additive character `ψ`: `f̂(a) = ∑_x ψ(ax)·f(x)`. -/
noncomputable def hatF (ψ : AddChar (ZMod N) ℂ) (f : ZMod N → ℂ) (a : ZMod N) : ℂ :=
  ∑ x : ZMod N, ψ (a * x) * f x

theorem hatF_sum {ι : Type*} (ψ : AddChar (ZMod N) ℂ) (s : Finset ι)
    (F : ι → ZMod N → ℂ) (a : ZMod N) :
    hatF ψ (fun x => ∑ c ∈ s, F c x) a = ∑ c ∈ s, hatF ψ (F c) a := by
  unfold hatF
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])

/-- **The DFT diagonalizes `conv3`**: `(f⋆g⋆h)^(a) = f̂(a)·ĝ(a)·ĥ(a)`. -/
theorem hatF_conv3 (ψ : AddChar (ZMod N) ℂ) (f g h : ZMod N → ℂ) (a : ZMod N) :
    hatF ψ (conv3 f g h) a = hatF ψ f a * hatF ψ g a * hatF ψ h a := by
  unfold hatF conv3
  calc ∑ d : ZMod N, ψ (a * d) * ∑ j : ZMod N, ∑ i : ZMod N, f i * g (d - j - i) * h j
      = ∑ d : ZMod N, ∑ j : ZMod N, ∑ i : ZMod N,
          ψ (a * d) * (f i * g (d - j - i) * h j) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    _ = ∑ j : ZMod N, ∑ i : ZMod N, ∑ d : ZMod N,
          ψ (a * d) * (f i * g (d - j - i) * h j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = ∑ j : ZMod N, ∑ i : ZMod N, ∑ y : ZMod N,
          (ψ (a * i) * f i) * ((ψ (a * y) * g y) * (ψ (a * j) * h j)) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
        refine (Fintype.sum_bijective (fun y : ZMod N => y + (j + i))
          (Equiv.addRight (j + i)).bijective
          (fun y => (ψ (a * i) * f i) * ((ψ (a * y) * g y) * (ψ (a * j) * h j)))
          (fun d => ψ (a * d) * (f i * g (d - j - i) * h j)) (fun y => ?_)).symm
        show (ψ (a * i) * f i) * ((ψ (a * y) * g y) * (ψ (a * j) * h j))
            = ψ (a * (y + (j + i))) * (f i * g (y + (j + i) - j - i) * h j)
        have hy : (y : ZMod N) + (j + i) - j - i = y := by ring
        have hsplit : a * (y + (j + i)) = a * y + a * j + a * i := by ring
        rw [hy, hsplit, map_add_eq_mul, map_add_eq_mul]
        ring
    _ = (∑ x : ZMod N, ψ (a * x) * f x) * (∑ x : ZMod N, ψ (a * x) * g x)
        * (∑ x : ZMod N, ψ (a * x) * h x) := by
        symm
        calc (∑ x : ZMod N, ψ (a * x) * f x) * (∑ x : ZMod N, ψ (a * x) * g x)
            * (∑ x : ZMod N, ψ (a * x) * h x)
            = ∑ i : ZMod N, ∑ y : ZMod N, ∑ j : ZMod N,
                (ψ (a * i) * f i) * ((ψ (a * y) * g y) * (ψ (a * j) * h j)) := by
              rw [Finset.sum_mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl (fun y _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j _ => by ring)
          _ = ∑ i : ZMod N, ∑ j : ZMod N, ∑ y : ZMod N,
                (ψ (a * i) * f i) * ((ψ (a * y) * g y) * (ψ (a * j) * h j)) := by
              exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
          _ = ∑ j : ZMod N, ∑ i : ZMod N, ∑ y : ZMod N,
                (ψ (a * i) * f i) * ((ψ (a * y) * g y) * (ψ (a * j) * h j)) :=
              Finset.sum_comm

/-- Complex conjugation inverts an additive character on `ZMod N`. -/
theorem conj_psi (ψ : AddChar (ZMod N) ℂ) (z : ZMod N) :
    (starRingEnd ℂ) (ψ z) = ψ (-z) := by
  have h0 : 0 < ringChar (ZMod N) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne N)
  have h := AddChar.starComp_eq_inv h0 (φ := ψ)
  calc (starRingEnd ℂ) (ψ z) = ((starRingEnd ℂ).compAddChar ψ) z := rfl
    _ = ψ⁻¹ z := by rw [h]
    _ = ψ (-z) := AddChar.inv_apply ψ z

/-- Additive character values on `ZMod N` have norm 1. -/
theorem norm_psi (ψ : AddChar (ZMod N) ℂ) (z : ZMod N) : ‖ψ z‖ = 1 := by
  have h0 : 0 < ringChar (ZMod N) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne N)
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (ψ.val_mem_rootsOfUnity z h0)

/-- **Parseval over `ZMod N`** for a primitive character:
`∑_a ‖f̂(a)‖² = N·∑_x ‖f(x)‖²`. -/
theorem hatF_parseval {ψ : AddChar (ZMod N) ℂ} (hψ : ψ.IsPrimitive) (f : ZMod N → ℂ) :
    ∑ a : ZMod N, ‖hatF ψ f a‖ ^ 2 = (N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 := by
  have key : ∑ a : ZMod N, hatF ψ f a * (starRingEnd ℂ) (hatF ψ f a)
      = (N : ℂ) * ∑ x : ZMod N, f x * (starRingEnd ℂ) (f x) := by
    have expand : ∀ a : ZMod N, hatF ψ f a * (starRingEnd ℂ) (hatF ψ f a)
        = ∑ x : ZMod N, ∑ y : ZMod N,
            ψ (a * (x - y)) * (f x * (starRingEnd ℂ) (f y)) := by
      intro a
      unfold hatF
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      rw [map_mul (starRingEnd ℂ) (ψ (a * y)) (f y), conj_psi ψ (a * y)]
      have hsub : a * (x - y) = a * x + -(a * y) := by ring
      rw [hsub, map_add_eq_mul]
      ring
    calc ∑ a : ZMod N, hatF ψ f a * (starRingEnd ℂ) (hatF ψ f a)
        = ∑ a : ZMod N, ∑ x : ZMod N, ∑ y : ZMod N,
            ψ (a * (x - y)) * (f x * (starRingEnd ℂ) (f y)) :=
          Finset.sum_congr rfl (fun a _ => expand a)
      _ = ∑ x : ZMod N, ∑ y : ZMod N,
            (∑ a : ZMod N, ψ (a * (x - y))) * (f x * (starRingEnd ℂ) (f y)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun y _ => by rw [Finset.sum_mul])
      _ = ∑ x : ZMod N, ∑ y : ZMod N,
            (((if x - y = 0 then Fintype.card (ZMod N) else 0 : ℕ)) : ℂ)
              * (f x * (starRingEnd ℂ) (f y)) := by
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
          rw [AddChar.sum_mulShift _ hψ]
      _ = (N : ℂ) * ∑ x : ZMod N, f x * (starRingEnd ℂ) (f x) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          have hcol : ∀ y : ZMod N,
              (((if x - y = 0 then Fintype.card (ZMod N) else 0 : ℕ)) : ℂ)
                * (f x * (starRingEnd ℂ) (f y))
              = if y = x then (N : ℂ) * (f x * (starRingEnd ℂ) (f y)) else 0 := by
            intro y
            by_cases hxy : y = x
            · subst hxy
              simp [ZMod.card]
            · have : x - y ≠ 0 := fun h => hxy (by linear_combination -h)
              simp [this, hxy]
          rw [Finset.sum_congr rfl (fun y _ => hcol y), Finset.sum_ite_eq' Finset.univ x]
          simp
  have cast_eq : ((∑ a : ZMod N, ‖hatF ψ f a‖ ^ 2 : ℝ) : ℂ)
      = (((N : ℝ) * ∑ x : ZMod N, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    calc ∑ a : ZMod N, (‖hatF ψ f a‖ : ℂ) ^ 2
        = ∑ a : ZMod N, hatF ψ f a * (starRingEnd ℂ) (hatF ψ f a) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          push_cast
          ring
      _ = (N : ℂ) * ∑ x : ZMod N, f x * (starRingEnd ℂ) (f x) := key
      _ = (N : ℂ) * ∑ x : ZMod N, (‖f x‖ : ℂ) ^ 2 := by
          refine congrArg _ (Finset.sum_congr rfl (fun x _ => ?_))
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          push_cast
          ring
  exact_mod_cast cast_eq

/-- A primitive additive character on `ZMod N` exists (over `ℂ`). -/
theorem exists_primitive_addChar :
    ∃ ψ : AddChar (ZMod N) ℂ, ψ.IsPrimitive := by
  have hN : N ≠ 0 := NeZero.ne N
  have hroot := Complex.isPrimitiveRoot_exp N hN
  have hpow : (Complex.exp (2 * Real.pi * Complex.I / N)) ^ N = 1 :=
    ((IsPrimitiveRoot.iff_def _ N).mp hroot).1
  exact ⟨AddChar.zmodChar N hpow,
    AddChar.zmodChar_primitive_of_primitive_root N hroot⟩

end GenericDFT

/-! ### The coset-label bridge: `H`-cosets are the fibers of `ℤ/3u' → ℤ/u'` -/

section Labels

variable {u' : ℕ} [NeZero u']

instance : NeZero (3 * u') := ⟨by have := NeZero.ne u'; omega⟩

/-- The coset label: reduction `ℤ/3u' → ℤ/u'`.  Its fibers are exactly the
`H = {0, u', 2u'}`-cosets, each of size 3. -/
def label (x : ZMod (3 * u')) : ZMod u' :=
  ZMod.castHom (dvd_mul_left u' 3) (ZMod u') x

theorem label_zero : label (0 : ZMod (3 * u')) = 0 := by
  unfold label; exact map_zero _

theorem label_sub (x y : ZMod (3 * u')) : label (x - y) = label x - label y := by
  unfold label; exact map_sub _ x y

theorem label_natCast_u' : label ((u' : ℕ) : ZMod (3 * u')) = 0 := by
  unfold label
  rw [map_natCast, ZMod.natCast_self]

/-- **The kernel bridge**: `label x = 0 ↔ x ∈ H = {0, u', 2u'}`. -/
theorem label_eq_zero_iff (x : ZMod (3 * u')) :
    label x = 0 ↔ inH ((u' : ℕ) : ZMod (3 * u')) x := by
  constructor
  · intro h
    have hx : ((x.val : ℕ) : ZMod u') = 0 := by
      have := h
      unfold label at this
      rwa [ZMod.castHom_apply, ← ZMod.natCast_val] at this
    obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hx
    have hlt : x.val < 3 * u' := x.val_lt
    have ht3 : t < 3 := by
      by_contra hge
      push_neg at hge
      have : 3 * u' ≤ u' * t := by
        calc 3 * u' = u' * 3 := by ring
          _ ≤ u' * t := Nat.mul_le_mul_left u' hge
      omega
    have hx' : x = ((u' * t : ℕ) : ZMod (3 * u')) := by
      rw [← ht]
      exact (ZMod.natCast_rightInverse x).symm
    interval_cases t
    · left; rw [hx']; simp
    · right; left; rw [hx']; push_cast; ring
    · right; right; rw [hx']; push_cast; ring
  · intro h
    rcases h with h | h | h
    · rw [h]; exact label_zero
    · rw [h]; exact label_natCast_u'
    · rw [h]
      unfold label
      rw [map_add]
      have hu0 : ZMod.castHom (dvd_mul_left u' 3) (ZMod u')
          ((u' : ℕ) : ZMod (3 * u')) = 0 := label_natCast_u'
      rw [hu0, add_zero]

/-- Labels agree iff the difference is in `H`. -/
theorem label_eq_iff (x y : ZMod (3 * u')) :
    label x = label y ↔ inH ((u' : ℕ) : ZMod (3 * u')) (x - y) := by
  rw [← label_eq_zero_iff, label_sub, sub_eq_zero]

/-- **The distinct-coset bridge**: the R300 predicate is pairwise distinctness of
the labels. -/
theorem allCosetsDistinct_iff_labels (a b c : ZMod (3 * u')) :
    allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) a b c
      ↔ label a ≠ label b ∧ label a ≠ label c ∧ label b ≠ label c := by
  unfold allCosetsDistinct
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => h1 ((label_eq_iff b a).mp h.symm),
           fun h => h2 ((label_eq_iff c a).mp h.symm),
           fun h => h3 ((label_eq_iff c b).mp h.symm)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => h1 ((label_eq_iff b a).mpr h).symm,
           fun h => h2 ((label_eq_iff c a).mpr h).symm,
           fun h => h3 ((label_eq_iff c b).mpr h).symm⟩

end Labels

/-! ### Slices, the decomposition, and the Newton mode identity -/

section Slices

variable {u' : ℕ} [NeZero u']

/-- The `c`-th coset slice of the coefficient sequence (zero index removed). -/
noncomputable def slice (J : ZMod (3 * u') → ℂ) (c : ZMod u') : ZMod (3 * u') → ℂ :=
  fun x => if x ≠ 0 ∧ label x = c then J x else 0

/-- The zero-removed full sequence. -/
noncomputable def Sfun (J : ZMod (3 * u') → ℂ) : ZMod (3 * u') → ℂ :=
  fun x => if x ≠ 0 then J x else 0

theorem slice_eq (J : ZMod (3 * u') → ℂ) (c : ZMod u') (x : ZMod (3 * u')) :
    slice J c x = if c = label x then Sfun J x else 0 := by
  unfold slice Sfun
  by_cases hx : x = 0
  · subst hx
    simp
  · by_cases hc : c = label x
    · subst hc
      simp [hx]
    · have hns : ¬(x ≠ 0 ∧ label x = c) := fun h => hc h.2.symm
      simp [hns, hc]

theorem sum_slices (J : ZMod (3 * u') → ℂ) (x : ZMod (3 * u')) :
    ∑ c : ZMod u', slice J c x = Sfun J x := by
  rw [Finset.sum_congr rfl (fun c _ => slice_eq J c x),
    Finset.sum_ite_eq' Finset.univ (label x)]
  simp

/-- Pointwise collapse of the slice triple sum. -/
theorem slice_triple_sum (J : ZMod (3 * u') → ℂ) (x y z : ZMod (3 * u')) :
    ∑ c₁ : ZMod u', ∑ c₂ : ZMod u', ∑ c₃ : ZMod u',
      (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ then slice J c₁ x * slice J c₂ y * slice J c₃ z else 0)
    = if x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) x y z
        then J x * J y * J z else 0 := by
  have hpt : ∀ c₁ c₂ c₃ : ZMod u',
      (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
        then slice J c₁ x * slice J c₂ y * slice J c₃ z else 0)
      = if c₁ = label x then (if c₂ = label y then (if c₃ = label z then
          (if label x ≠ label y ∧ label x ≠ label z ∧ label y ≠ label z
            then Sfun J x * Sfun J y * Sfun J z else 0) else 0) else 0) else 0 := by
    intro c₁ c₂ c₃
    rw [slice_eq, slice_eq, slice_eq]
    by_cases h1 : c₁ = label x <;> by_cases h2 : c₂ = label y <;>
        by_cases h3 : c₃ = label z <;>
      simp [h1, h2, h3, mul_zero, zero_mul, ite_self]
  calc ∑ c₁ : ZMod u', ∑ c₂ : ZMod u', ∑ c₃ : ZMod u',
        (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
          then slice J c₁ x * slice J c₂ y * slice J c₃ z else 0)
      = ∑ c₁ : ZMod u', (if c₁ = label x then (∑ c₂ : ZMod u', (if c₂ = label y then
          (∑ c₃ : ZMod u', (if c₃ = label z then
            (if label x ≠ label y ∧ label x ≠ label z ∧ label y ≠ label z
              then Sfun J x * Sfun J y * Sfun J z else 0) else 0)) else 0)) else 0) := by
        refine Finset.sum_congr rfl (fun c₁ _ => ?_)
        rw [Finset.sum_congr rfl (fun c₂ _ => Finset.sum_congr rfl (fun c₃ _ => hpt c₁ c₂ c₃))]
        by_cases h1 : c₁ = label x
        · simp only [h1, if_true]
          refine Finset.sum_congr rfl (fun c₂ _ => ?_)
          by_cases h2 : c₂ = label y <;> simp [h2]
        · simp [h1]
    _ = if label x ≠ label y ∧ label x ≠ label z ∧ label y ≠ label z
          then Sfun J x * Sfun J y * Sfun J z else 0 := by
        rw [Finset.sum_ite_eq' Finset.univ (label x), if_pos (Finset.mem_univ _),
            Finset.sum_ite_eq' Finset.univ (label y), if_pos (Finset.mem_univ _),
            Finset.sum_ite_eq' Finset.univ (label z), if_pos (Finset.mem_univ _)]
    _ = if x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) x y z
          then J x * J y * J z else 0 := by
        by_cases hacd : allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) x y z
        · have hlab := (allCosetsDistinct_iff_labels x y z).mp hacd
          rw [if_pos hlab]
          by_cases hx : x = 0
          · rw [if_neg (fun h => h.1 hx)]
            unfold Sfun
            rw [if_neg (fun h => h hx)]
            ring
          · by_cases hy : y = 0
            · rw [if_neg (fun h => h.2.1 hy)]
              unfold Sfun
              rw [if_neg (fun h : y ≠ 0 => h hy)]
              ring
            · by_cases hz : z = 0
              · rw [if_neg (fun h => h.2.2.1 hz)]
                unfold Sfun
                rw [if_neg (fun h : z ≠ 0 => h hz)]
                ring
              · rw [if_pos ⟨hx, hy, hz, hacd⟩]
                unfold Sfun
                rw [if_pos hx, if_pos hy, if_pos hz]
        · have hlab : ¬(label x ≠ label y ∧ label x ≠ label z ∧ label y ≠ label z) :=
            fun h => hacd ((allCosetsDistinct_iff_labels x y z).mpr h)
          rw [if_neg hlab, if_neg (fun h => hacd h.2.2.2)]

/-- `distStratum` as an if-then-else double sum over the full torus. -/
theorem distStratum_eq_ite_sum (J : ZMod (3 * u') → ℂ) (d : ZMod (3 * u')) :
    distStratum J ((u' : ℕ) : ZMod (3 * u')) d
      = ∑ j : ZMod (3 * u'), ∑ i : ZMod (3 * u'),
          (if i ≠ 0 ∧ d - j - i ≠ 0 ∧ j ≠ 0
              ∧ allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) i (d - j - i) j
            then J i * J (d - j - i) * J j else 0) := by
  unfold distStratum
  have hinner : ∀ j : ZMod (3 * u'),
      ∑ i ∈ ((Finset.univ \ {(0 : ZMod (3 * u'))}).filter (fun i => d - j - i ≠ 0)).filter
          (fun i => allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) i (d - j - i) j),
        J i * J (d - j - i) * J j
      = ∑ i : ZMod (3 * u'),
          (if i ≠ 0 ∧ d - j - i ≠ 0
              ∧ allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) i (d - j - i) j
            then J i * J (d - j - i) * J j else 0) := by
    intro j
    rw [show ((Finset.univ \ {(0 : ZMod (3 * u'))}).filter (fun i => d - j - i ≠ 0)).filter
          (fun i => allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) i (d - j - i) j)
        = Finset.univ.filter (fun i : ZMod (3 * u') =>
            i ≠ 0 ∧ d - j - i ≠ 0
              ∧ allCosetsDistinct ((u' : ℕ) : ZMod (3 * u')) i (d - j - i) j) from by
      ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        Finset.mem_singleton, true_and, ne_eq]
      tauto]
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  rw [show (Finset.univ \ {(0 : ZMod (3 * u'))})
      = Finset.univ.filter (fun j : ZMod (3 * u') => j ≠ 0) from by ext j; simp]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j ≠ 0
  · rw [if_pos hj]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> first | rfl | tauto
  · rw [if_neg hj]
    push_neg at hj
    refine (Finset.sum_eq_zero (fun i _ => ?_)).symm
    simp [hj]

/-- **THE SLICE DECOMPOSITION** (unconditional): the DIST stratum is the sum of
triple convolutions of coset slices over pairwise-distinct labels. -/
theorem distStratum_slice_decomposition (J : ZMod (3 * u') → ℂ) (d : ZMod (3 * u')) :
    distStratum J ((u' : ℕ) : ZMod (3 * u')) d
      = ∑ c₁ : ZMod u', ∑ c₂ : ZMod u', ∑ c₃ : ZMod u',
          (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
            then conv3 (slice J c₁) (slice J c₂) (slice J c₃) d else 0) := by
  rw [distStratum_eq_ite_sum]
  have hpush : ∀ c₁ c₂ c₃ : ZMod u',
      (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
        then conv3 (slice J c₁) (slice J c₂) (slice J c₃) d else 0)
      = ∑ j : ZMod (3 * u'), ∑ i : ZMod (3 * u'),
          (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
            then slice J c₁ i * slice J c₂ (d - j - i) * slice J c₃ j else 0) := by
    intro c₁ c₂ c₃
    by_cases h : c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
    · rw [if_pos h]; unfold conv3
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by rw [if_pos h]))
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun i _ => by rw [if_neg h]))
  rw [Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ =>
    Finset.sum_congr rfl (fun c₃ _ => hpush c₁ c₂ c₃)))]
  -- swap the c⃗ sums inside the (j,i) sums
  have swap3 : ∀ (F : ZMod u' → ZMod (3 * u') → ZMod (3 * u') → ℂ),
      (∑ c : ZMod u', ∑ j : ZMod (3 * u'), ∑ i : ZMod (3 * u'), F c j i)
        = ∑ j : ZMod (3 * u'), ∑ i : ZMod (3 * u'), ∑ c : ZMod u', F c j i := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
  rw [Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ =>
    swap3 (fun c₃ j i => if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
      then slice J c₁ i * slice J c₂ (d - j - i) * slice J c₃ j else 0)))]
  rw [Finset.sum_congr rfl (fun c₁ _ =>
    swap3 (fun c₂ j i => ∑ c₃ : ZMod u', if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
      then slice J c₁ i * slice J c₂ (d - j - i) * slice J c₃ j else 0))]
  rw [swap3 (fun c₁ j i => ∑ c₂ : ZMod u', ∑ c₃ : ZMod u',
    if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
      then slice J c₁ i * slice J c₂ (d - j - i) * slice J c₃ j else 0)]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [slice_triple_sum J i (d - j - i) j]

/-- **The Newton identity for pairwise-distinct triples** (generic, over `ℂ`). -/
theorem newton_distinct_triple {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → ℂ) :
    ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι,
        (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ then A c₁ * A c₂ * A c₃ else 0)
      = (∑ c : ι, A c) ^ 3 - 3 * (∑ c : ι, A c) * (∑ c : ι, A c ^ 2)
        + 2 * ∑ c : ι, A c ^ 3 := by
  have hpt : ∀ c₁ c₂ c₃ : ι,
      (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ then A c₁ * A c₂ * A c₃ else 0)
      = A c₁ * A c₂ * A c₃
        - (if c₂ = c₁ then A c₁ * A c₂ * A c₃ else 0)
        - (if c₃ = c₁ then A c₁ * A c₂ * A c₃ else 0)
        - (if c₃ = c₂ then A c₁ * A c₂ * A c₃ else 0)
        + (if c₂ = c₁ then (if c₃ = c₁ then A c₁ * A c₂ * A c₃ else 0) else 0)
        + (if c₂ = c₁ then (if c₃ = c₁ then A c₁ * A c₂ * A c₃ else 0) else 0) := by
    intro c₁ c₂ c₃
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
    · have n12 : ¬(c₂ = c₁) := fun h => hd.1 h.symm
      have n13 : ¬(c₃ = c₁) := fun h => hd.2.1 h.symm
      have n23 : ¬(c₃ = c₂) := fun h => hd.2.2 h.symm
      rw [if_pos hd]
      simp only [n12, n13, n23, if_false, ite_false]
      ring
    · rw [if_neg hd]
      by_cases h12 : c₂ = c₁ <;> by_cases h13 : c₃ = c₁ <;> by_cases h23 : c₃ = c₂
      · simp only [if_pos h12, if_pos h13, if_pos h23]
        ring
      · exact absurd (h13.trans h12.symm) h23
      · exact absurd (h23.trans h12) h13
      · simp only [if_pos h12, if_neg h13, if_neg h23]
        ring
      · exact absurd (h23.symm.trans h13) h12
      · simp only [if_neg h12, if_pos h13, if_neg h23]
        ring
      · simp only [if_neg h12, if_neg h13, if_pos h23]
        ring
      · exact absurd ⟨fun h => h12 h.symm, fun h => h13 h.symm,
          fun h => h23 h.symm⟩ hd
  rw [Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ =>
    Finset.sum_congr rfl (fun c₃ _ => hpt c₁ c₂ c₃)))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have inner_sum : ∀ c₁ c₂ : ι, ∑ c₃ : ι, A c₁ * A c₂ * A c₃
      = A c₁ * A c₂ * ∑ c : ι, A c := fun c₁ c₂ => (Finset.mul_sum _ _ _).symm
  have e0 : ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι, A c₁ * A c₂ * A c₃
      = (∑ c : ι, A c) ^ 3 := by
    calc ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι, A c₁ * A c₂ * A c₃
        = ∑ c₁ : ι, ∑ c₂ : ι, A c₁ * A c₂ * ∑ c : ι, A c :=
          Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl
            (fun c₂ _ => inner_sum c₁ c₂))
      _ = ∑ c₁ : ι, (A c₁ * (∑ c : ι, A c)) * ∑ c : ι, A c := by
          refine Finset.sum_congr rfl (fun c₁ _ => ?_)
          calc ∑ c₂ : ι, A c₁ * A c₂ * ∑ c : ι, A c
              = ∑ c₂ : ι, (A c₁ * (∑ c : ι, A c)) * A c₂ :=
                Finset.sum_congr rfl (fun c₂ _ => by ring)
            _ = (A c₁ * (∑ c : ι, A c)) * ∑ c : ι, A c := (Finset.mul_sum _ _ _).symm
      _ = ∑ c₁ : ι, ((∑ c : ι, A c) * (∑ c : ι, A c)) * A c₁ :=
          Finset.sum_congr rfl (fun c₁ _ => by ring)
      _ = ((∑ c : ι, A c) * (∑ c : ι, A c)) * ∑ c : ι, A c := (Finset.mul_sum _ _ _).symm
      _ = (∑ c : ι, A c) ^ 3 := by ring
  have e12 : ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι, (if c₂ = c₁ then A c₁ * A c₂ * A c₃ else 0)
      = (∑ c : ι, A c ^ 2) * (∑ c : ι, A c) := by
    calc ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι, (if c₂ = c₁ then A c₁ * A c₂ * A c₃ else 0)
        = ∑ c₁ : ι, ∑ c₂ : ι, (if c₂ = c₁ then A c₁ * A c₂ * ∑ c : ι, A c else 0) := by
          refine Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ => ?_))
          split_ifs <;> simp [inner_sum]
      _ = ∑ c₁ : ι, A c₁ * A c₁ * ∑ c : ι, A c := by
          refine Finset.sum_congr rfl (fun c₁ _ => ?_)
          rw [Finset.sum_ite_eq' Finset.univ c₁
            (fun c₂ => A c₁ * A c₂ * ∑ c : ι, A c)]
          simp
      _ = ∑ c₁ : ι, ((∑ c : ι, A c) * A c₁ ^ 2) :=
          Finset.sum_congr rfl (fun c₁ _ => by ring)
      _ = (∑ c : ι, A c) * ∑ c : ι, A c ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = (∑ c : ι, A c ^ 2) * (∑ c : ι, A c) := by ring
  have e13 : ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι, (if c₃ = c₁ then A c₁ * A c₂ * A c₃ else 0)
      = (∑ c : ι, A c ^ 2) * (∑ c : ι, A c) := by
    calc ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι, (if c₃ = c₁ then A c₁ * A c₂ * A c₃ else 0)
        = ∑ c₁ : ι, ∑ c₂ : ι, A c₁ * A c₂ * A c₁ := by
          refine Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ => ?_))
          rw [Finset.sum_ite_eq' Finset.univ c₁ (fun c₃ => A c₁ * A c₂ * A c₃)]
          simp
      _ = ∑ c₁ : ι, ∑ c₂ : ι, (A c₁ ^ 2) * A c₂ :=
          Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ => by ring))
      _ = ∑ c₁ : ι, (A c₁ ^ 2) * ∑ c : ι, A c :=
          Finset.sum_congr rfl (fun c₁ _ => (Finset.mul_sum _ _ _).symm)
      _ = ∑ c₁ : ι, ((∑ c : ι, A c) * A c₁ ^ 2) :=
          Finset.sum_congr rfl (fun c₁ _ => by ring)
      _ = (∑ c : ι, A c) * ∑ c : ι, A c ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = (∑ c : ι, A c ^ 2) * (∑ c : ι, A c) := by ring
  have e23 : ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι, (if c₃ = c₂ then A c₁ * A c₂ * A c₃ else 0)
      = (∑ c : ι, A c) * (∑ c : ι, A c ^ 2) := by
    calc ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι, (if c₃ = c₂ then A c₁ * A c₂ * A c₃ else 0)
        = ∑ c₁ : ι, ∑ c₂ : ι, A c₁ * A c₂ * A c₂ := by
          refine Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ => ?_))
          rw [Finset.sum_ite_eq' Finset.univ c₂ (fun c₃ => A c₁ * A c₂ * A c₃)]
          simp
      _ = ∑ c₁ : ι, ∑ c₂ : ι, A c₁ * (A c₂ ^ 2) :=
          Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ => by ring))
      _ = ∑ c₁ : ι, A c₁ * ∑ c : ι, A c ^ 2 :=
          Finset.sum_congr rfl (fun c₁ _ => (Finset.mul_sum _ _ _).symm)
      _ = ∑ c₁ : ι, ((∑ c : ι, A c ^ 2) * A c₁) :=
          Finset.sum_congr rfl (fun c₁ _ => by ring)
      _ = (∑ c : ι, A c ^ 2) * ∑ c : ι, A c := (Finset.mul_sum _ _ _).symm
      _ = (∑ c : ι, A c) * (∑ c : ι, A c ^ 2) := by ring
  have eee : ∑ c₁ : ι, ∑ c₂ : ι, ∑ c₃ : ι,
      (if c₂ = c₁ then (if c₃ = c₁ then A c₁ * A c₂ * A c₃ else 0) else 0)
      = ∑ c : ι, A c ^ 3 := by
    refine Finset.sum_congr rfl (fun c₁ _ => ?_)
    calc ∑ c₂ : ι, ∑ c₃ : ι,
        (if c₂ = c₁ then (if c₃ = c₁ then A c₁ * A c₂ * A c₃ else 0) else 0)
        = ∑ c₂ : ι, (if c₂ = c₁ then
            ∑ c₃ : ι, (if c₃ = c₁ then A c₁ * A c₂ * A c₃ else 0) else 0) := by
          refine Finset.sum_congr rfl (fun c₂ _ => ?_)
          split_ifs <;> simp
      _ = ∑ c₃ : ι, (if c₃ = c₁ then A c₁ * A c₁ * A c₃ else 0) := by
          rw [Finset.sum_ite_eq' Finset.univ c₁]
          simp
      _ = A c₁ * A c₁ * A c₁ := by
          rw [Finset.sum_ite_eq' Finset.univ c₁ (fun c₃ => A c₁ * A c₁ * A c₃)]
          simp
      _ = A c₁ ^ 3 := by ring
  rw [e0, e12, e13, e23, eee]
  ring

end Slices

/-! ### The trace formula: mode identity, Parseval energy, and the reduction -/

section TraceFormula

variable {u' : ℕ} [NeZero u']

/-- **THE MODE IDENTITY (trace formula, unconditional)**: in every DFT mode the
DIST stratum is the Newton polynomial of the slice transforms:
`D̂(a) = Ŝ(a)³ − 3·Ŝ(a)·P₂(a) + 2·P₃(a)`. -/
theorem hatF_distStratum (ψ : AddChar (ZMod (3 * u')) ℂ) (J : ZMod (3 * u') → ℂ)
    (a : ZMod (3 * u')) :
    hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a
      = (∑ c : ZMod u', hatF ψ (slice J c) a) ^ 3
        - 3 * (∑ c : ZMod u', hatF ψ (slice J c) a)
            * (∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 2)
        + 2 * ∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 3 := by
  have hfun : (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d)
      = fun d => ∑ c₁ : ZMod u', ∑ c₂ : ZMod u', ∑ c₃ : ZMod u',
          (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
            then conv3 (slice J c₁) (slice J c₂) (slice J c₃) d else 0) :=
    funext (fun d => distStratum_slice_decomposition J d)
  rw [hfun]
  rw [hatF_sum]
  have hstep : ∀ c₁ : ZMod u',
      hatF ψ (fun d => ∑ c₂ : ZMod u', ∑ c₃ : ZMod u',
        (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
          then conv3 (slice J c₁) (slice J c₂) (slice J c₃) d else 0)) a
      = ∑ c₂ : ZMod u', ∑ c₃ : ZMod u',
          (if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
            then hatF ψ (slice J c₁) a * hatF ψ (slice J c₂) a * hatF ψ (slice J c₃) a
            else 0) := by
    intro c₁
    rw [hatF_sum]
    refine Finset.sum_congr rfl (fun c₂ _ => ?_)
    rw [hatF_sum]
    refine Finset.sum_congr rfl (fun c₃ _ => ?_)
    by_cases h : c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
    · rw [show (fun d => if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
            then conv3 (slice J c₁) (slice J c₂) (slice J c₃) d else 0)
          = conv3 (slice J c₁) (slice J c₂) (slice J c₃) from
        funext (fun d => if_pos h), if_pos h]
      exact hatF_conv3 ψ _ _ _ a
    · rw [show (fun d => if c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
            then conv3 (slice J c₁) (slice J c₂) (slice J c₃) d else 0)
          = fun _ => (0 : ℂ) from funext (fun d => if_neg h), if_neg h]
      unfold hatF
      simp
  rw [Finset.sum_congr rfl (fun c₁ _ => hstep c₁)]
  exact newton_distinct_triple (fun c => hatF ψ (slice J c) a)

/-- **Parseval for the DIST energy** (unconditional):
`m · E_DIST = ∑_a ‖D̂(a)‖²`. -/
theorem distStratum_energy_spectral {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) (J : ZMod (3 * u') → ℂ) :
    ((3 * u' : ℕ) : ℝ) * ∑ d : ZMod (3 * u'),
        ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      = ∑ a : ZMod (3 * u'),
          ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2 :=
  (hatF_parseval hψ _).symm

/-- The `H`-cosets have at most 3 elements: fiber cardinality bound for `label`. -/
theorem card_label_fiber_le (c : ZMod u') :
    (Finset.univ.filter (fun x : ZMod (3 * u') => label x = c)).card ≤ 3 := by
  classical
  rcases (Finset.univ.filter (fun x : ZMod (3 * u') => label x = c)).eq_empty_or_nonempty with
    he | ⟨x₀, hx₀⟩
  · rw [he]; exact Nat.zero_le _
  · have hx₀c : label x₀ = c := (Finset.mem_filter.mp hx₀).2
    have hinj : (Finset.univ.filter (fun x : ZMod (3 * u') => label x = c)).card
        ≤ (Finset.univ.filter (fun x : ZMod (3 * u') => label x = 0)).card := by
      apply Finset.card_le_card_of_injOn (fun x => x - x₀)
      · intro x hx
        have hxc : label x = c := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [label_sub, hxc, hx₀c, sub_self]
      · intro a _ b _ hab
        have : a - x₀ = b - x₀ := hab
        linear_combination this
    have hker : (Finset.univ.filter (fun x : ZMod (3 * u') => label x = 0))
        ⊆ ({0, ((u' : ℕ) : ZMod (3 * u')),
            ((u' : ℕ) : ZMod (3 * u')) + ((u' : ℕ) : ZMod (3 * u'))} :
              Finset (ZMod (3 * u'))) := by
      intro x hx
      have h0 : label x = 0 := (Finset.mem_filter.mp hx).2
      have := (label_eq_zero_iff x).mp h0
      rcases this with h | h | h <;> simp [h]
    calc (Finset.univ.filter (fun x : ZMod (3 * u') => label x = c)).card
        ≤ (Finset.univ.filter (fun x : ZMod (3 * u') => label x = 0)).card := hinj
      _ ≤ ({0, ((u' : ℕ) : ZMod (3 * u')),
            ((u' : ℕ) : ZMod (3 * u')) + ((u' : ℕ) : ZMod (3 * u'))} :
              Finset (ZMod (3 * u'))).card := Finset.card_le_card hker
      _ ≤ 3 := card_triple_le _ _ _

/-- **The unconditional 3-term slice envelope**: `‖Âᶜ(a)‖ ≤ 3B`. -/
theorem norm_hatSlice_le (ψ : AddChar (ZMod (3 * u')) ℂ) {J : ZMod (3 * u') → ℂ}
    {B : ℝ} (hB0 : 0 ≤ B) (hJ : ∀ x, ‖J x‖ ≤ B) (c : ZMod u') (a : ZMod (3 * u')) :
    ‖hatF ψ (slice J c) a‖ ≤ 3 * B := by
  unfold hatF
  calc ‖∑ x : ZMod (3 * u'), ψ (a * x) * slice J c x‖
      ≤ ∑ x : ZMod (3 * u'), ‖ψ (a * x) * slice J c x‖ := norm_sum_le _ _
    _ = ∑ x : ZMod (3 * u'), ‖slice J c x‖ := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [norm_mul, norm_psi, one_mul]
    _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod (3 * u') => x ≠ 0 ∧ label x = c),
          ‖J x‖ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        unfold slice
        split_ifs <;> simp
    _ ≤ ∑ _x ∈ Finset.univ.filter (fun x : ZMod (3 * u') => x ≠ 0 ∧ label x = c), B :=
        Finset.sum_le_sum (fun x _ => hJ x)
    _ = ((Finset.univ.filter (fun x : ZMod (3 * u') => x ≠ 0 ∧ label x = c)).card : ℝ)
          * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * B := by
        have hsub : (Finset.univ.filter (fun x : ZMod (3 * u') => x ≠ 0 ∧ label x = c))
            ⊆ Finset.univ.filter (fun x : ZMod (3 * u') => label x = c) := by
          intro x hx
          have := (Finset.mem_filter.mp hx).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this.2⟩
        have hcard : (Finset.univ.filter
            (fun x : ZMod (3 * u') => x ≠ 0 ∧ label x = c)).card ≤ 3 :=
          le_trans (Finset.card_le_card hsub) (card_label_fiber_le c)
        have : ((Finset.univ.filter
            (fun x : ZMod (3 * u') => x ≠ 0 ∧ label x = c)).card : ℝ) ≤ 3 := by
          exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right this hB0

/-- **THE MINIMAL NAMED OPEN PROP in the trace-formula coordinates**: pointwise
flatness of the full (zero-removed) DFT at the Parseval scale — square-root
cancellation across the `m` Jacobi angles inside each mode.  Parseval gives it
ON AVERAGE with `K = 1` (`hatSfun_energy_le`); `K = √m` holds pointwise
unconditionally (`fullDFTFlat_sqrt_m`); probe: `sup_a ‖Ŝ‖²/(mq) ∈ [1, 4.7]` at
m = 9 and m = 12, flat in `q`. -/
def FullDFTFlat (ψ : AddChar (ZMod (3 * u')) ℂ) (J : ZMod (3 * u') → ℂ)
    (q : ℕ) (K : ℝ) : Prop :=
  ∀ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ≤ K * Real.sqrt (((3 * u' : ℕ) : ℝ) * q)

/-- Parseval budget (unconditional): the AVERAGE of `‖Ŝ(a)‖²` over modes is at
most `m·q` — the flatness Prop holds on average with `K = 1`. -/
theorem hatSfun_energy_le {ψ : AddChar (ZMod (3 * u')) ℂ} (hψ : ψ.IsPrimitive)
    {J : ZMod (3 * u') → ℂ} {q : ℕ} (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ)) :
    ∑ a : ZMod (3 * u'), ‖hatF ψ (Sfun J) a‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) ^ 2 * q := by
  rw [hatF_parseval hψ]
  have hbound : ∑ x : ZMod (3 * u'), ‖Sfun J x‖ ^ 2 ≤ ((3 * u' : ℕ) : ℝ) * q := by
    calc ∑ x : ZMod (3 * u'), ‖Sfun J x‖ ^ 2
        ≤ ∑ _x : ZMod (3 * u'), (q : ℝ) := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          unfold Sfun
          split_ifs with h
          · exact hJ x
          · have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
            simpa using hq0
      _ = ((3 * u' : ℕ) : ℝ) * q := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.card_univ, ZMod.card]
  calc ((3 * u' : ℕ) : ℝ) * ∑ x : ZMod (3 * u'), ‖Sfun J x‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) * (((3 * u' : ℕ) : ℝ) * q) := by
        have h0 : (0 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hbound h0
    _ = ((3 * u' : ℕ) : ℝ) ^ 2 * q := by ring

/-- Calibration: `FullDFTFlat` holds unconditionally with `K = √m` (the
baseline; the open content is `K = O(1)`). -/
theorem fullDFTFlat_sqrt_m (ψ : AddChar (ZMod (3 * u')) ℂ)
    {J : ZMod (3 * u') → ℂ} {q : ℕ} (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ)) :
    FullDFTFlat ψ J q (Real.sqrt ((3 * u' : ℕ) : ℝ)) := by
  intro a
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) := by positivity
  have hJroot : ∀ x, ‖J x‖ ≤ Real.sqrt (q : ℝ) := by
    intro x
    have h := Real.sqrt_le_sqrt (hJ x)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  calc ‖hatF ψ (Sfun J) a‖
      ≤ ∑ x : ZMod (3 * u'), ‖ψ (a * x) * Sfun J x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ZMod (3 * u'), Real.sqrt (q : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [norm_mul, norm_psi, one_mul]
        unfold Sfun
        split_ifs with h
        · exact hJroot x
        · simp only [norm_zero]
          exact Real.sqrt_nonneg _
    _ = ((3 * u' : ℕ) : ℝ) * Real.sqrt (q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.card_univ, ZMod.card]
    _ = Real.sqrt ((3 * u' : ℕ) : ℝ)
          * Real.sqrt (((3 * u' : ℕ) : ℝ) * q) := by
        rw [Real.sqrt_mul hm0]
        rw [show ((3 * u' : ℕ) : ℝ) * Real.sqrt (q : ℝ)
            = (Real.sqrt ((3 * u' : ℕ) : ℝ) * Real.sqrt ((3 * u' : ℕ) : ℝ))
              * Real.sqrt (q : ℝ) from by rw [Real.mul_self_sqrt hm0]]
        ring

/-- `Ŝ = ∑_c Âᶜ` (slice completeness in the hat domain). -/
theorem hatSfun_eq_sum_hatSlice (ψ : AddChar (ZMod (3 * u')) ℂ)
    (J : ZMod (3 * u') → ℂ) (a : ZMod (3 * u')) :
    hatF ψ (Sfun J) a = ∑ c : ZMod u', hatF ψ (slice J c) a := by
  rw [← hatF_sum ψ Finset.univ (fun c => slice J c) a]
  unfold hatF
  refine Finset.sum_congr rfl (fun x _ => ?_)
  show ψ (a * x) * Sfun J x = ψ (a * x) * ∑ c : ZMod u', slice J c x
  rw [sum_slices]

/-- **THE REDUCTION (main theorem)**: pointwise flatness of the full Jacobi DFT
discharges the r=3 DIST rung with the explicit constant `(K³ + 9K + 18)²`.
The sextic-moment open core has become ONE pointwise quadratic bound. -/
theorem distStratumEnergyBound_of_fullDFTFlat {ψ : AddChar (ZMod (3 * u')) ℂ}
    (hψ : ψ.IsPrimitive) {J : ZMod (3 * u') → ℂ} {q : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hJ : ∀ x, ‖J x‖ ^ 2 ≤ (q : ℝ))
    (hflat : FullDFTFlat ψ J q K) :
    DistStratumEnergyBound J ((u' : ℕ) : ZMod (3 * u')) q ((K ^ 3 + 9 * K + 18) ^ 2) := by
  classical
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hm0 : (0 : ℝ) < ((3 * u' : ℕ) : ℝ) := by
    have := NeZero.ne u'
    positivity
  set R : ℝ := Real.sqrt (((3 * u' : ℕ) : ℝ) * q) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = ((3 * u' : ℕ) : ℝ) * q := Real.sq_sqrt (by positivity)
  have hJroot : ∀ x, ‖J x‖ ≤ Real.sqrt (q : ℝ) := by
    intro x
    have h := Real.sqrt_le_sqrt (hJ x)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hm1 : (1 : ℝ) ≤ ((3 * u' : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ 3 * u' := by have := NeZero.ne u'; omega
    exact_mod_cast h1
  have hsqrtq_le : Real.sqrt (q : ℝ) ≤ R := by
    rw [hR]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [mul_le_mul_of_nonneg_right hm1 hq0]
  -- pointwise mode bound
  have hmode : ∀ a : ZMod (3 * u'),
      ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖
        ≤ (K ^ 3 + 9 * K + 18) * R ^ 3 := by
    intro a
    rw [hatF_distStratum]
    set S : ℂ := ∑ c : ZMod u', hatF ψ (slice J c) a with hS
    set P2 : ℂ := ∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 2 with hP2
    set P3 : ℂ := ∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 3 with hP3
    have hSb : ‖S‖ ≤ K * R := by
      rw [hS, ← hatSfun_eq_sum_hatSlice]
      exact hflat a
    have hslice : ∀ c : ZMod u', ‖hatF ψ (slice J c) a‖ ≤ 3 * Real.sqrt (q : ℝ) :=
      fun c => norm_hatSlice_le ψ (Real.sqrt_nonneg _) hJroot c a
    have hsq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
    have hP2b : ‖P2‖ ≤ ((u' : ℕ) : ℝ) * (9 * q) := by
      rw [hP2]
      calc ‖∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 2‖
          ≤ ∑ c : ZMod u', ‖(hatF ψ (slice J c) a) ^ 2‖ := norm_sum_le _ _
        _ ≤ ∑ _c : ZMod u', 9 * (q : ℝ) := by
            refine Finset.sum_le_sum (fun c _ => ?_)
            rw [norm_pow]
            calc ‖hatF ψ (slice J c) a‖ ^ 2
                ≤ (3 * Real.sqrt (q : ℝ)) ^ 2 :=
                  pow_le_pow_left₀ (norm_nonneg _) (hslice c) 2
              _ = 9 * (q : ℝ) := by rw [mul_pow, hsq]; norm_num
        _ = ((u' : ℕ) : ℝ) * (9 * q) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [Finset.card_univ, ZMod.card]
    have hP3b : ‖P3‖ ≤ ((u' : ℕ) : ℝ) * (27 * (q : ℝ) * Real.sqrt (q : ℝ)) := by
      rw [hP3]
      calc ‖∑ c : ZMod u', (hatF ψ (slice J c) a) ^ 3‖
          ≤ ∑ c : ZMod u', ‖(hatF ψ (slice J c) a) ^ 3‖ := norm_sum_le _ _
        _ ≤ ∑ _c : ZMod u', 27 * (q : ℝ) * Real.sqrt (q : ℝ) := by
            refine Finset.sum_le_sum (fun c _ => ?_)
            rw [norm_pow]
            calc ‖hatF ψ (slice J c) a‖ ^ 3
                ≤ (3 * Real.sqrt (q : ℝ)) ^ 3 :=
                  pow_le_pow_left₀ (norm_nonneg _) (hslice c) 3
              _ = 27 * (q : ℝ) * Real.sqrt (q : ℝ) := by
                  rw [mul_pow]
                  rw [show (Real.sqrt (q : ℝ)) ^ 3
                      = (Real.sqrt (q : ℝ)) ^ 2 * Real.sqrt (q : ℝ) from by ring, hsq]
                  ring
        _ = ((u' : ℕ) : ℝ) * (27 * (q : ℝ) * Real.sqrt (q : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [Finset.card_univ, ZMod.card]
    -- assemble: ‖S³ − 3SP₂ + 2P₃‖ ≤ K³R³ + 9K R³ + 18 R³
    have hmcast : ((3 * u' : ℕ) : ℝ) = 3 * ((u' : ℕ) : ℝ) := by
      push_cast; ring
    have hT2 : 3 * (‖S‖ * ‖P2‖) ≤ 9 * K * R ^ 3 := by
      have h1 : ‖S‖ * ‖P2‖ ≤ (K * R) * (((u' : ℕ) : ℝ) * (9 * q)) :=
        mul_le_mul hSb hP2b (norm_nonneg _) (by positivity)
      have h2 : (K * R) * (((u' : ℕ) : ℝ) * (9 * q)) = 3 * K * (R * (((3 * u' : ℕ) : ℝ) * q)) := by
        rw [hmcast]; ring
      have h3 : R * (((3 * u' : ℕ) : ℝ) * q) = R ^ 3 := by
        rw [← hR2]; ring
      nlinarith [h1, h2, h3]
    have hT3 : 2 * ‖P3‖ ≤ 18 * R ^ 3 := by
      have h1 : ‖P3‖ ≤ ((u' : ℕ) : ℝ) * (27 * (q : ℝ) * Real.sqrt (q : ℝ)) := hP3b
      have h2 : ((u' : ℕ) : ℝ) * (27 * (q : ℝ) * Real.sqrt (q : ℝ))
          = 9 * (((3 * u' : ℕ) : ℝ) * (q : ℝ)) * Real.sqrt (q : ℝ) := by
        rw [hmcast]; ring
      have h3 : 9 * (((3 * u' : ℕ) : ℝ) * (q : ℝ)) * Real.sqrt (q : ℝ)
          ≤ 9 * (((3 * u' : ℕ) : ℝ) * (q : ℝ)) * R :=
        mul_le_mul_of_nonneg_left hsqrtq_le (by positivity)
      have h4 : 9 * (((3 * u' : ℕ) : ℝ) * (q : ℝ)) * R = 9 * R ^ 3 := by
        rw [← hR2]; ring
      nlinarith [h1, h2, h3, h4]
    have hT1 : ‖S‖ ^ 3 ≤ K ^ 3 * R ^ 3 := by
      calc ‖S‖ ^ 3 ≤ (K * R) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hSb 3
        _ = K ^ 3 * R ^ 3 := by ring
    calc ‖S ^ 3 - 3 * S * P2 + 2 * P3‖
        ≤ ‖S ^ 3 - 3 * S * P2‖ + ‖2 * P3‖ := norm_add_le _ _
      _ ≤ (‖S ^ 3‖ + ‖3 * S * P2‖) + ‖2 * P3‖ := by
          have := norm_sub_le (S ^ 3) (3 * S * P2)
          linarith
      _ = (‖S‖ ^ 3 + 3 * (‖S‖ * ‖P2‖)) + 2 * ‖P3‖ := by
          rw [norm_pow, norm_mul, norm_mul, norm_mul]
          simp only [Complex.norm_ofNat]
          ring
      _ ≤ (K ^ 3 * R ^ 3 + 9 * K * R ^ 3) + 18 * R ^ 3 := by
          linarith [hT1, hT2, hT3]
      _ = (K ^ 3 + 9 * K + 18) * R ^ 3 := by ring
  -- Parseval assembly
  unfold DistStratumEnergyBound
  have hpars := distStratum_energy_spectral (u' := u') hψ J
  have hsum : ∑ a : ZMod (3 * u'),
      ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) * ((K ^ 3 + 9 * K + 18) * R ^ 3) ^ 2 := by
    calc ∑ a : ZMod (3 * u'),
        ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
        ≤ ∑ _a : ZMod (3 * u'), ((K ^ 3 + 9 * K + 18) * R ^ 3) ^ 2 := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (hmode a) 2
      _ = ((3 * u' : ℕ) : ℝ) * ((K ^ 3 + 9 * K + 18) * R ^ 3) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.card_univ, ZMod.card]
  have hR6 : (R ^ 3) ^ 2 = (((3 * u' : ℕ) : ℝ) * q) ^ 3 := by
    calc (R ^ 3) ^ 2 = (R ^ 2) ^ 3 := by ring
      _ = (((3 * u' : ℕ) : ℝ) * q) ^ 3 := by rw [hR2]
  have hE : ((3 * u' : ℕ) : ℝ) * ∑ d : ZMod (3 * u'), ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) * ((K ^ 3 + 9 * K + 18) ^ 2 * (((3 * u' : ℕ) : ℝ) * q) ^ 3) := by
    rw [hpars]
    calc ∑ a : ZMod (3 * u'),
        ‖hatF ψ (fun d => distStratum J ((u' : ℕ) : ZMod (3 * u')) d) a‖ ^ 2
        ≤ ((3 * u' : ℕ) : ℝ) * ((K ^ 3 + 9 * K + 18) * R ^ 3) ^ 2 := hsum
      _ = ((3 * u' : ℕ) : ℝ) * ((K ^ 3 + 9 * K + 18) ^ 2 * (R ^ 3) ^ 2) := by ring
      _ = ((3 * u' : ℕ) : ℝ) * ((K ^ 3 + 9 * K + 18) ^ 2 * (((3 * u' : ℕ) : ℝ) * q) ^ 3) := by
          rw [hR6]
  have hfinal := le_of_mul_le_mul_left (by linarith [hE] :
    ((3 * u' : ℕ) : ℝ) * ∑ d : ZMod (3 * u'), ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      ≤ ((3 * u' : ℕ) : ℝ) * ((K ^ 3 + 9 * K + 18) ^ 2 * (((3 * u' : ℕ) : ℝ) * q) ^ 3)) hm0
  calc ∑ d : ZMod (3 * u'), ‖distStratum J ((u' : ℕ) : ZMod (3 * u')) d‖ ^ 2
      ≤ (K ^ 3 + 9 * K + 18) ^ 2 * (((3 * u' : ℕ) : ℝ) * q) ^ 3 := hfinal
    _ = (K ^ 3 + 9 * K + 18) ^ 2 * ((3 * u' : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring

end TraceFormula

end ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms hatF_conv3
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms hatF_parseval
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms exists_primitive_addChar
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms label_eq_zero_iff
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms allCosetsDistinct_iff_labels
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms distStratum_slice_decomposition
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms newton_distinct_triple
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms hatF_distStratum
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms distStratum_energy_spectral
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms norm_hatSlice_le
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms hatSfun_energy_le
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms fullDFTFlat_sqrt_m
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount in
#print axioms distStratumEnergyBound_of_fullDFTFlat
