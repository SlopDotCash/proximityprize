/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.KummerExtension
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# The degree-`t` supply = elementary-symmetric fiber (#389)

The reformulated deep-band supply (`Σ_c C(a_c,t)`) is, for the lowest non-trivial
degree (a word that is the evaluation of a polynomial of degree exactly `t=k+m+1`),
an **exact elementary-symmetric-function fiber count**.

For such a word `w = eval W`, a codeword `c` of `rsCode dom k` agrees with `w` on a
`t`-core `T` iff the forced polynomial `W − W_t·∏_{i∈T}(X−dom i)` has degree `< k`:
`W − c` is divisible by the monic degree-`t` vanishing polynomial of `dom(T)`, and
both have leading coefficient `W_t`, so they are equal up to that scalar; the explainer
is therefore unique and equals that polynomial.  By Vieta the coefficients of
`∏_{i∈T}(X−dom i)` are the elementary symmetric functions of `dom(T)`, so the
degree-`<k` condition reads `e_j(dom(T)) = (−1)^j W_{t−j}/W_t`, `j=1..m+1`.

Hence the explainable `t`-cores of a degree-`t` word are EXACTLY the `t`-subsets of
the domain whose first `m+1` elementary symmetric functions hit the values forced by
`W`'s top coefficients — turning the deep-band supply (for degree-`t` words) into a
pure symmetric-function/subset-sum fiber count.  This isolates the domain-dependence
of the sub-Johnson wall: additively-concentrated domains (arithmetic progressions)
give large fibers, multiplicatively-structured domains (`μ_n`) spread them.

Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.EsymmFiber

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The monic degree-`|T|` vanishing polynomial of the domain image of `T`. -/
noncomputable def coreVanish (dom : Fin n ↪ F) (T : Finset (Fin n)) : Polynomial F :=
  ∏ i ∈ T, (X - C (dom i))

theorem coreVanish_monic (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (coreVanish dom T).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom i))

theorem coreVanish_degree (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (coreVanish dom T).degree = (T.card : WithBot ℕ) := by
  classical
  rw [coreVanish, degree_prod]
  rw [Finset.sum_congr rfl (fun i _ => degree_X_sub_C (dom i))]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem coreVanish_eval_zero (dom : Fin n ↪ F) {T : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ T) : (coreVanish dom T).eval (dom i) = 0 := by
  classical
  rw [coreVanish, eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-- The forced explainer polynomial of a degree-`t` word `W` on a core `T`. -/
noncomputable def forcedPoly (dom : Fin n ↪ F) (k m : ℕ) (W : Polynomial F)
    (T : Finset (Fin n)) : Polynomial F :=
  W - C (W.coeff (k + m + 1)) * coreVanish dom T

/-- **The core identity (#389).**  For a degree-`t` word `w = eval W`
(`W.degree = k+m+1`) and a `t`-core `T`, a codeword of `rsCode dom k` explains `T`
iff the forced explainer polynomial `W − W_t·∏_{i∈T}(X−dom i)` has degree `< k`.  The
explainer is unique and equals that polynomial. -/
theorem explainable_iff_forcedPoly_degree
    (dom : Fin n ↪ F) {k m : ℕ} (W : Polynomial F)
    (hWdeg : W.degree = ((k + m + 1 : ℕ) : WithBot ℕ))
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) :
    (∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ i ∈ T, c i = W.eval (dom i))
      ↔ (forcedPoly dom k m W T).degree < (k : WithBot ℕ) := by
  classical
  have hWne : W ≠ 0 := by
    rintro rfl; rw [degree_zero] at hWdeg; exact absurd hWdeg WithBot.bot_ne_coe
  have hWnat : W.natDegree = k + m + 1 := natDegree_eq_of_degree_eq_some hWdeg
  have hWtne : W.coeff (k + m + 1) ≠ 0 := by
    rw [← hWnat]; exact leadingCoeff_ne_zero.mpr hWne
  have hCVdeg : (coreVanish dom T).degree = ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [coreVanish_degree, hT]
  have hCmuldeg :
      (C (W.coeff (k + m + 1)) * coreVanish dom T).degree
        = ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_C hWtne, hCVdeg, zero_add]
  -- the forced poly has degree < t (leading terms cancel)
  have hForcedlt :
      (forcedPoly dom k m W T).degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [forcedPoly, ← hWdeg]
    refine degree_sub_lt ?_ hWne ?_
    · rw [hWdeg, hCmuldeg]
    · rw [leadingCoeff_mul, leadingCoeff_C, (coreVanish_monic dom T).leadingCoeff, mul_one]
      rw [show W.leadingCoeff = W.coeff (k + m + 1) from by rw [← hWnat]; rfl]
  -- the forced poly agrees with W on dom(T)
  have hForcedeval : ∀ i ∈ T, (forcedPoly dom k m W T).eval (dom i) = W.eval (dom i) := by
    intro i hi
    rw [forcedPoly, eval_sub, eval_mul, eval_C, coreVanish_eval_zero dom hi, mul_zero, sub_zero]
  constructor
  · rintro ⟨c, hc, hagree⟩
    obtain ⟨P, hPdeg, rfl⟩ := hc
    have hsub : (forcedPoly dom k m W T - P).degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt hForcedlt ?_)
      exact lt_of_lt_of_le hPdeg (by exact_mod_cast (show k ≤ k + m + 1 by omega))
    have hvan : ∀ x ∈ T.image dom, (forcedPoly dom k m W T - P).eval x = 0 := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hpa : P.eval (dom i) = W.eval (dom i) := hagree i hi
      rw [eval_sub, hForcedeval i hi, hpa, sub_self]
    have hzero : forcedPoly dom k m W T - P = 0 :=
      Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := T.image dom)
        (by rw [Finset.card_image_of_injective _ dom.injective, hT]; exact hsub) hvan
    rw [sub_eq_zero.mp hzero]; exact hPdeg
  · intro hdeg
    refine ⟨fun i => (forcedPoly dom k m W T).eval (dom i),
      ⟨forcedPoly dom k m W T, hdeg, rfl⟩, fun i hi => hForcedeval i hi⟩

/-! ## The dyadic coset-union construction: exponential supply on smooth domains

If the domain has a `μ_d`-subgroup structure, a union of `μ_d`-cosets `A` has vanishing
polynomial `∏_{i∈A}(X − dom i) = expand_d Q` (a polynomial in `X^d`), so its top `d−1`
sub-leading coefficients vanish.  For the word `w = wt·X^t + (deg<k)` this forces the
explainer to have degree `≤ t − d ≤ k − 1 < k` (using `d ≥ m+2`), so `A` is an
explainable `t`-core.  There are `C(n/d, t/d)` such unions — exponential. -/

open Polynomial in
/-- **Coset-union ⟹ explainable core.**  If `∏_{i∈A}(X − dom i) = expand_d Q` (i.e. `A`
is a union of `μ_d`-cosets) with `|A| = t = k+m+1`, `d ≥ m+2`, and `w = wt·X^t + lowPart`
(`lowPart` of degree `< k`, `wt ≠ 0`), then a codeword of `rsCode dom k` explains `A`. -/
theorem explainable_of_expand
    (dom : Fin n ↪ F) {k m d : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d)
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ))
    {A : Finset (Fin n)} (hAcard : A.card = k + m + 1)
    (Q : Polynomial F)
    (hAexp : (∏ i ∈ A, (X - C (dom i))) = Polynomial.expand F d Q) :
    ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
       ∀ i ∈ A, c i = (C wt * X ^ (k + m + 1) + lowPart).eval (dom i) := by
  classical
  have hd0 : 0 < d := by omega
  set t := k + m + 1 with ht
  set W : Polynomial F := C wt * X ^ t + lowPart with hWdef
  -- degree of `C wt * X^t` is t
  have hCXt : (C wt * X ^ t).degree = (t : WithBot ℕ) := degree_C_mul_X_pow t hwt
  have hlowlt : lowPart.degree < (t : WithBot ℕ) :=
    lt_of_lt_of_le hlow (by exact_mod_cast (show k ≤ t by omega))
  have hWdeg : W.degree = (t : WithBot ℕ) := by
    rw [hWdef, degree_add_eq_left_of_degree_lt (by rw [hCXt]; exact hlowlt), hCXt]
  -- the leading coefficient of W (at t) is wt
  have hWcoeff : W.coeff t = wt := by
    rw [hWdef, coeff_add, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one,
      Polynomial.coeff_eq_zero_of_degree_lt hlowlt, add_zero]
  -- ∏_A is the monic degree-t coreVanish; identify it with `expand_d Q`
  have hCV : (∏ i ∈ A, (X - C (dom i))) = coreVanish dom A := rfl
  have hCVmonic : (coreVanish dom A).Monic := coreVanish_monic dom A
  have hCVdeg2 : (coreVanish dom A).degree = (t : WithBot ℕ) := by
    rw [coreVanish_degree, hAcard]
  have hCVnat : (coreVanish dom A).natDegree = t := natDegree_eq_of_degree_eq_some hCVdeg2
  have hCVexp : coreVanish dom A = Polynomial.expand F d Q := hCV ▸ hAexp
  set s := Q.natDegree with hs
  -- Q is monic (its expand is the monic coreVanish), so s·d = t
  have hQmonic : Q.Monic := (Polynomial.monic_expand_iff hd0).mp (hCVexp ▸ hCVmonic)
  have hsdt : s * d = t := by
    have h := hCVnat; rw [hCVexp, Polynomial.natDegree_expand] at h; exact h
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso; rw [h, Nat.zero_mul] at hsdt; omega
    · exact h
  -- X^t = expand_d (X^s), hence X^t − coreVanish = expand_d (X^s − Q)
  have hXt : (X : Polynomial F) ^ t = Polynomial.expand F d (X ^ s) := by
    rw [map_pow, Polynomial.expand_X, ← pow_mul, mul_comm, hsdt]
  have hdiff : (X : Polynomial F) ^ t - coreVanish dom A
      = Polynomial.expand F d (X ^ s - Q) := by
    rw [map_sub, ← hXt, hCVexp]
  -- natDegree (X^s − Q) ≤ s − 1 (monic minus monic of equal degree)
  have hsubnat : ((X : Polynomial F) ^ s - Q).natDegree ≤ s - 1 := by
    have e2 : Q.degree = (s : WithBot ℕ) := Polynomial.degree_eq_natDegree hQmonic.ne_zero
    have hsublt : ((X : Polynomial F) ^ s - Q).degree < (s : WithBot ℕ) := by
      have hlt := Polynomial.degree_sub_lt (p := (X : Polynomial F) ^ s) (q := Q)
        (by rw [degree_X_pow, e2]) (pow_ne_zero s X_ne_zero)
        (by rw [(monic_X_pow s).leadingCoeff, hQmonic.leadingCoeff])
      rwa [degree_X_pow] at hlt
    by_cases h0 : (X : Polynomial F) ^ s - Q = 0
    · rw [h0, natDegree_zero]; omega
    · have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hsublt; omega
  -- hence natDegree (X^t − coreVanish) ≤ t − d
  have hdiffnat : ((X : Polynomial F) ^ t - coreVanish dom A).natDegree ≤ t - d := by
    rw [hdiff, Polynomial.natDegree_expand]
    calc ((X : Polynomial F) ^ s - Q).natDegree * d ≤ (s - 1) * d :=
          Nat.mul_le_mul hsubnat le_rfl
      _ = s * d - d := by rw [Nat.sub_one_mul]
      _ = t - d := by rw [hsdt]
  -- forcedPoly = lowPart + wt·(X^t − coreVanish), so degree < k
  rw [explainable_iff_forcedPoly_degree dom W hWdeg hAcard]
  have hforced : forcedPoly dom k m W A = lowPart + C wt * (X ^ t - coreVanish dom A) := by
    rw [forcedPoly, hWcoeff, hWdef, coreVanish]; ring
  rw [hforced]
  have hdk : t - d ≤ k - 1 := by omega
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt hlow ?_)
  rw [degree_mul, degree_C hwt, zero_add]
  calc ((X : Polynomial F) ^ t - coreVanish dom A).degree
      ≤ ((t - d : ℕ) : WithBot ℕ) := Polynomial.degree_le_of_natDegree_le hdiffnat
    _ ≤ ((k - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hdk
    _ < (k : WithBot ℕ) := by exact_mod_cast (by omega : k - 1 < k)

open scoped Classical in
open Polynomial in
/-- **Exponential supply on smooth dyadic domains (#389).**  Suppose the domain is
partitioned into `r` blocks, each a `μ_d`-coset — i.e. `(block j).card = d`, the blocks
are pairwise disjoint, and `∏_{i∈block j}(X − dom i) = X^d − C (β j)`.  If `d ≥ m+2` and
`s·d = k+m+1`, then the word `w = wt·X^t + lowPart` (`lowPart` of degree `< k`) has at
least `C(r, s)` explainable `(k+m+1)`-cores — the `s`-fold unions of blocks.

For a 2-adic smooth domain `μ_{2^μ}` (`d = 2^j`, `r = n/d`) and constant rate, `C(r, s) =
C(n/d, t/d)` is **exponential in `n`**: explicit smooth (FFT) Reed–Solomon codes have
exponential sub-Johnson supply / list size — the multiplicative-subgroup analogue of the
Ben-Sasson–Kopparty–Radhakrishnan subspace-polynomial limit, refuting any subexponential
uniform supply bound on such domains. -/
theorem smooth_dyadic_supply_lower_bound
    (dom : Fin n ↪ F) {k m d r : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d)
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ))
    (block : Fin r → Finset (Fin n)) (hbcard : ∀ j, (block j).card = d)
    (hbdisj : ∀ j j', j ≠ j' → Disjoint (block j) (block j'))
    (β : Fin r → F)
    (hbcoset : ∀ j, (∏ i ∈ block j, (X - C (dom i))) = X ^ d - C (β j))
    {s : ℕ} (hsd : s * d = k + m + 1) :
    r.choose s ≤
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
            ∀ i ∈ T, c i = (C wt * X ^ (k + m + 1) + lowPart).eval (dom i))).card := by
  classical
  -- recover membership in S from the union (blocks disjoint and nonempty)
  have hmemiff : ∀ (T : Finset (Fin r)) (j : Fin r),
      j ∈ T ↔ block j ⊆ T.biUnion block := by
    intro T j
    refine ⟨fun hj => Finset.subset_biUnion_of_mem block hj, fun hsub => ?_⟩
    have hne : (block j).Nonempty := by rw [← Finset.card_pos, hbcard]; omega
    obtain ⟨i, hi⟩ := hne
    obtain ⟨j', hj', hij'⟩ := Finset.mem_biUnion.mp (hsub hi)
    by_cases hjj' : j = j'
    · rwa [hjj']
    · exact absurd hij' (Finset.disjoint_left.mp (hbdisj j j' hjj') hi)
  have hcard_ps : ((Finset.univ : Finset (Fin r)).powersetCard s).card = r.choose s := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard_ps]
  refine Finset.card_le_card_of_injOn (fun S => S.biUnion block) ?_ ?_
  · -- the union of `s` blocks is an explainable `t`-core
    intro S hS
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hS
    obtain ⟨-, hScard⟩ := hS
    have hfcard : (S.biUnion block).card = k + m + 1 := by
      rw [Finset.card_biUnion (fun a _ b _ hab => hbdisj a b hab),
        Finset.sum_congr rfl (fun j _ => hbcard j), Finset.sum_const, hScard,
        smul_eq_mul, hsd]
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hfcard⟩, ?_⟩
    have hAexp : (∏ i ∈ S.biUnion block, (X - C (dom i)))
        = Polynomial.expand F d (∏ j ∈ S, (X - C (β j))) := by
      rw [Finset.prod_biUnion (fun a _ b _ hab => hbdisj a b hab), _root_.map_prod]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [hbcoset j, _root_.map_sub, Polynomial.expand_X, Polynomial.expand_C]
    exact explainable_of_expand dom hk hd wt hwt lowPart hlow hfcard _ hAexp
  · -- injectivity: `S` is recoverable from its union of blocks
    intro S _ S' _ heq
    have heq2 : S.biUnion block = S'.biUnion block := heq
    ext j
    rw [hmemiff S j, hmemiff S' j, heq2]


/-! ## Unconditional: the roots-of-unity (smooth 2-adic) domain realizes the construction -/

/-- The roots-of-unity domain `i ↦ ζ^i` for a primitive `n`-th root `ζ`. -/
noncomputable def domRU {ζ : F} (hζ : IsPrimitiveRoot ζ n) : Fin n ↪ F :=
  ⟨fun i => ζ ^ (i : ℕ), by
    intro a b hab
    exact Fin.ext (hζ.pow_inj a.isLt b.isLt hab)⟩

@[simp] theorem domRU_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n) (i : Fin n) :
    domRU hζ i = ζ ^ (i : ℕ) := rfl

open scoped Classical in
open Polynomial in
/-- **Exponential supply for the explicit roots-of-unity domain (#389) — UNCONDITIONAL.**
For `dom = μ_n` (`ζ` a primitive `n`-th root, `n = d·r`), the dyadic block structure is
realized by the cosets of `μ_d` (each `∏(X−dom) = X^d − C(ζ^{jd})`), so the word
`wt·X^t + lowPart` has at least `C(n/d, t/d)` explainable `(k+m+1)`-cores.  For `n = 2^μ`
and constant rate this is exponential — explicit smooth (FFT) RS codes have exponential
sub-Johnson list size. -/
theorem rootsOfUnity_dyadic_supply {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d r : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (hnr : n = d * r)
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F) (hlow : lowPart.degree < (k : WithBot ℕ))
    {s : ℕ} (hsd : s * d = k + m + 1) :
    r.choose s ≤
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∃ c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F)),
            ∀ i ∈ T, c i = (C wt * X ^ (k + m + 1) + lowPart).eval (domRU hζ i))).card := by
  classical
  have hnpos : 0 < n := NeZero.pos n
  have hdpos : 0 < d := by omega
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, Nat.mul_zero] at hnr; omega
    · exact h
  have hg : IsPrimitiveRoot (ζ ^ r) d := IsPrimitiveRoot.pow hnpos hζ (by rw [hnr]; ring)
  -- index bound: j + r·l < n for j < r, l < d
  have hlt : ∀ (j : Fin r) (l : ℕ), l < d → (j : ℕ) + r * l < n := by
    intro j l hl
    have h1 : r * (l + 1) ≤ r * d := Nat.mul_le_mul le_rfl (by omega)
    have h2 : r * (l + 1) = r * l + r := by ring
    have hj : (j : ℕ) < r := j.isLt
    rw [hnr, Nat.mul_comm d r]; omega
  have hmodid : ∀ (j : Fin r) (l : ℕ), l < d → ((j : ℕ) + r * l) % n = (j : ℕ) + r * l :=
    fun j l hl => Nat.mod_eq_of_lt (hlt j l hl)
  set φ : Fin r → ℕ → Fin n :=
    fun j l => (⟨((j : ℕ) + r * l) % n, Nat.mod_lt _ hnpos⟩ : Fin n) with hφ
  set blk : Fin r → Finset (Fin n) := fun j => (Finset.range d).image (φ j) with hblk
  -- φ j injective on range d
  have hinj : ∀ (j : Fin r), Set.InjOn (φ j) ↑(Finset.range d) := by
    intro j a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have heq : (j : ℕ) + r * a = (j : ℕ) + r * b := by
      have := Fin.ext_iff.mp hab
      simp only [hφ] at this
      rw [hmodid j a ha, hmodid j b hb] at this; exact this
    exact Nat.eq_of_mul_eq_mul_left hrpos (by omega : r * a = r * b)
  have hcard : ∀ j, (blk j).card = d := fun j => by
    rw [hblk, Finset.card_image_of_injOn (hinj j), Finset.card_range]
  have hdisj : ∀ j j', j ≠ j' → Disjoint (blk j) (blk j') := by
    intro j j' hjj'
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [hblk, Finset.mem_image, Finset.mem_range] at hx hx'
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, hb2⟩ := hx'
    have heq : (j' : ℕ) + r * b = (j : ℕ) + r * a := by
      have h := Fin.ext_iff.mp hb2
      simp only [hφ] at h
      rw [hmodid j' b hb, hmodid j a ha] at h; exact h
    -- j ≡ j' (mod r), both < r ⟹ j = j'
    have hmod : (j : ℕ) % r = (j' : ℕ) % r := by
      have h := congrArg (· % r) heq
      simp only [Nat.add_mul_mod_self_left] at h
      exact h.symm
    exact hjj' (Fin.ext (by
      rw [← Nat.mod_eq_of_lt j.isLt, hmod, Nat.mod_eq_of_lt j'.isLt]))
  set β : Fin r → F := fun j => (ζ ^ (j : ℕ)) ^ d with hβ
  have hcoset : ∀ j, (∏ i ∈ blk j, (X - C (domRU hζ i))) = X ^ d - C (β j) := by
    intro j
    rw [hblk, Finset.prod_image (hinj j)]
    have step1 : ∀ l ∈ Finset.range d,
        (X - C (domRU hζ (φ j l))) = (X - C ((ζ ^ r) ^ l * ζ ^ (j : ℕ))) := by
      intro l hl
      have hval : ((φ j l : Fin n) : ℕ) = ((j : ℕ) + r * l) % n := by simp [hφ]
      rw [domRU_apply, hval, hmodid j l (Finset.mem_range.mp hl), pow_add, pow_mul, mul_comm]
    rw [Finset.prod_congr rfl step1, hβ,
      ← X_pow_sub_C_eq_prod hg hdpos (show (ζ ^ (j : ℕ)) ^ d = (ζ ^ (j : ℕ)) ^ d from rfl)]
  exact smooth_dyadic_supply_lower_bound (domRU hζ) hk hd wt hwt lowPart hlow blk hcard hdisj β
    hcoset hsd

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
open scoped Classical in
open Polynomial in
/-- **The issue's supply statement is FALSE for `μ_n` at subexponential `B`.**  The
degree-`t` word `wt·X^t + lowPart` already has `≥ C(r,s)` explainable `(k+m+1)`-cores on
the roots-of-unity domain, so `ExplainableCoreSupply` cannot hold with any `B < C(r,s)` —
for `n = 2^μ`, constant rate, `B` must be exponential. -/
theorem not_explainableCoreSupply_rootsOfUnity {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d r : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (hnr : n = d * r)
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F) (hlow : lowPart.degree < (k : WithBot ℕ))
    {s : ℕ} (hsd : s * d = k + m + 1) {B : ℕ} (hB : B < r.choose s) :
    ¬ ProximityGap.Ownership.ExplainableCoreSupply (domRU hζ) k m B := by
  intro hsupply
  have hle := hsupply (fun i => (C wt * X ^ (k + m + 1) + lowPart).eval (domRU hζ i))
  have hge := rootsOfUnity_dyadic_supply hζ hk hd hnr wt hwt lowPart hlow hsd
  have hchain : r.choose s ≤ B := by
    refine le_trans hge ?_
    convert hle using 2
    ext T
    simp only [ProximityGap.Ownership.ExplainableOn, Finset.mem_filter]
  omega

open scoped Classical in
open Polynomial in
/-- **Explicit exponential lower bound for `μ_n` (#389).**  Taking the central split
`r = 2s` (so `n = d·2s`), the explainable-core count exceeds `4^s / s`: the supply is
genuinely exponential in `s = (k+m+1)/d`.  For `n = 2^μ`, constant rate and constant `m`
(`d = O(1)`), `s = Θ(n)`, so this is `2^{Θ(n)}`. -/
theorem rootsOfUnity_dyadic_supply_exp {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d s : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (hs4 : 4 ≤ s) (hnr : n = d * (2 * s))
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F) (hlow : lowPart.degree < (k : WithBot ℕ))
    (hsd : s * d = k + m + 1) :
    4 ^ s < s * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∃ c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F)),
            ∀ i ∈ T, c i = (C wt * X ^ (k + m + 1) + lowPart).eval (domRU hζ i))).card := by
  have hge := rootsOfUnity_dyadic_supply hζ hk hd hnr wt hwt lowPart hlow hsd
  calc 4 ^ s < s * Nat.centralBinom s := Nat.four_pow_lt_mul_centralBinom s hs4
    _ = s * (2 * s).choose s := by rw [Nat.centralBinom]
    _ ≤ s * _ := Nat.mul_le_mul le_rfl hge

end ProximityGap.EsymmFiber

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.EsymmFiber.explainable_iff_forcedPoly_degree
#print axioms ProximityGap.EsymmFiber.explainable_of_expand
#print axioms ProximityGap.EsymmFiber.smooth_dyadic_supply_lower_bound
#print axioms ProximityGap.EsymmFiber.rootsOfUnity_dyadic_supply
#print axioms ProximityGap.EsymmFiber.not_explainableCoreSupply_rootsOfUnity
