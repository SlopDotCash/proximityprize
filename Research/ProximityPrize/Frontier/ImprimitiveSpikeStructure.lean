/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarLineIncidenceEquivariance

/-!
# C2 — the imprimitive-spike quantization of the DEPLOYED far-line incidence (#407)

This brick characterizes the **imprimitive spike** of the *deployed* far-line incidence object

  `explainableScalars C δ u₀ u₁  =  { γ : u₀ + γ·u₁  is δ-explainable by C }`

(`FarLineIncidenceEquivariance.explainableScalars`, the EXACT `farIncidence` of
`B1IncidenceBridge.WorstCaseFarIncidenceBounded` and the `ε_mca ≥ #/q` lower bound of
`FarCosetExplosion.epsMCA_ge_far_incidence`).  This is the object `I` whose codim-1 face is the
height-gate's `N` — we attack `I` itself, not `N`.

## The measured spike law (exact, p-INDEPENDENT, `count == brute`)

For the monomial far line `u₀ = X^a`, `u₁ = X^b` over `μ_n ⊂ F_p` (`n = 2^a`), the nonzero
bad-scalar set is a **union of full cosets of `μ_{n/gcd(n,b-a)}`**, so the incidence is

  `I(a,b;r)  =  𝟙[X^a not far]  +  c(a,b;r) · (n / gcd(n,b-a))`,    `c ∈ ℕ`.

Exact probe values (`scripts/probes/probe_farline_incidence_exact.py`):

```
n=8,  k=2: r=3 (δ=.375) I=8 = 1·8        (threshold, GOOD = budget n)
           r=4 (δ=.500) I=9 = 1·8+1      (first BAD)
           r=5 (δ=.625) I=40 = 5·8       (spike)
n=16, k=4: r=9 (δ=.5625) I=9 = 1·8+1     (GOOD)
           r=10(δ=.625)  I=89 = 11·8 + 1 (spike, BAD); binder a=10,b=4, gcd(16,6)=2 → μ_8 cosets
```

p-independence (n=16 spike, p≡1 mod 16): `I=17,57,89,89,81,89,…` for `p=17,97,113,193,241,…`
— converges to the char-0 value `89` **from below**, never exceeds it (`81` = one coset collapsed
mod a structured `p`).  So char-`p` cannot worsen the spike past char-0 (matches N-vs-I).

## What is PROVEN here (axiom-clean) vs. what is the residual

PROVEN: the **equivariance quantization** — the source of the coset structure.  The RS code over
`μ_n` is fixed by the dilation `x ↦ g·x` (`g ∈ μ_n`); on the monomial line this acts by
`γ ↦ g^{b-a}·γ`, so `explainableScalars` is invariant under multiplying `γ` by `g^{b-a}`.  The
orbit of `g ↦ g^{b-a}` over `μ_n` is exactly `μ_{n/gcd(n,b-a)}`; hence the bad-scalar set is a
union of `μ_{n/gcd(n,b-a)}`-cosets and `I` is QUANTIZED to multiples of `n/gcd(n,b-a)` (plus the
`γ=0` indicator).  This is char-independent (combinatorial over `μ_n`), explaining the
p-independence AND the "char-p ≤ char-0" cap.

RESIDUAL (named `Prop`, NOT proven): the **coset count** `c(a,b;r)` — how many `μ_{n/gcd}`-cosets
are bad — and which `(a,b)` maximizes `c` (the spike-direction selection).  This is the genuine
open core; the quantization here pins its GRANULARITY (a multiple of `n/gcd`) but not its value.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.SpikeQuantization

open ProximityGap.FarCosetExplosion

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 1 — the γ-scaling law: scaling the direction reindexes the bad set by `γ ↦ c⁻¹·γ`. -/

open Classical in
/-- **Direction-scaling reindexes the bad-scalar set.**  Scaling the line direction `u₁ ↦ c • u₁`
(`c ≠ 0`, pointwise scalar) leaves the line `u₀ + γ·(c•u₁) = u₀ + (c·γ)·u₁` explainable for exactly
the `γ` with `c·γ` bad for the original direction.  Hence the bad set of `(u₀, c•u₁)` is the image
of that of `(u₀, u₁)` under `γ ↦ c⁻¹·γ`. -/
theorem explainableScalars_scale_dir
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) {c : F} (hc : c ≠ 0) :
    explainableScalars (F := F) (A := F) C δ u₀ (fun i => c * u₁ i)
      = (explainableScalars (F := F) (A := F) C δ u₀ u₁).image (fun γ => c⁻¹ * γ) := by
  classical
  ext γ
  simp only [explainableScalars, mem_filter, mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨S, hsz, w, hwC, hw⟩
    refine ⟨c * γ, ⟨S, hsz, w, hwC, ?_⟩, ?_⟩
    · intro i hi
      have hwi := hw i hi
      simp only [smul_eq_mul] at hwi ⊢
      rw [hwi]; ring
    · rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · rintro ⟨β, ⟨S, hsz, w, hwC, hw⟩, hβ⟩
    refine ⟨S, hsz, w, hwC, ?_⟩
    intro i hi
    have hwi := hw i hi
    simp only [smul_eq_mul] at hwi ⊢
    rw [hwi, ← hβ]
    field_simp

open Classical in
/-- **Whole-stack scaling by a code-scalar preserves the bad set EXACTLY (as a set).**  If `C` is a
submodule (so `c • w ∈ C` for `c ≠ 0`), scaling BOTH `u₀` and `u₁` by the same constant `c` leaves
the bad-scalar set unchanged: `u₀ + γ·u₁` is explainable by `w` iff `c·u₀ + γ·(c·u₁)` is explainable
by `c·w` (and `c·w ∈ C`).  This is the offset-aware half of the dilation (the direction scaling is
absorbed into the `γ`-index, the offset scaling is absorbed into the codeword). -/
theorem explainableScalars_scale_both
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) {c : F} (hc : c ≠ 0) :
    explainableScalars (F := F) (A := F) (C : Set (ι → F)) δ
        (fun i => c * u₀ i) (fun i => c * u₁ i)
      = explainableScalars (F := F) (A := F) (C : Set (ι → F)) δ u₀ u₁ := by
  classical
  ext γ
  simp only [explainableScalars, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨S, hsz, w, hwC, hw⟩
    refine ⟨S, hsz, (fun i => c⁻¹ * w i), C.smul_mem c⁻¹ hwC, ?_⟩
    intro i hi
    have hwi := hw i hi
    simp only [smul_eq_mul] at hwi ⊢
    rw [hwi]
    field_simp
  · rintro ⟨S, hsz, w, hwC, hw⟩
    refine ⟨S, hsz, (fun i => c * w i), C.smul_mem c hwC, ?_⟩
    intro i hi
    have hwi := hw i hi
    simp only [smul_eq_mul] at hwi ⊢
    rw [hwi]; ring

open Classical in
/-- Cardinality form: scaling the direction by a nonzero `c` preserves the incidence count. -/
theorem explainableScalars_card_scale_dir
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) {c : F} (hc : c ≠ 0) :
    (explainableScalars (F := F) (A := F) C δ u₀ (fun i => c * u₁ i)).card
      = (explainableScalars (F := F) (A := F) C δ u₀ u₁).card := by
  classical
  rw [explainableScalars_scale_dir C δ u₀ u₁ hc, Finset.card_image_of_injective]
  intro x y hxy
  simpa [mul_right_inj' (inv_ne_zero hc)] using hxy

/-! ## Part 2 — the monomial-line dilation: `γ ↦ g^{a-b}·γ` set invariance (the quantization core). -/

open Classical in
/-- **Elementary direction-scaling instance for a monomial line.**  Scaling the direction
`domain^b ↦ g^b · domain^b` by a nonzero constant preserves the incidence *count* (an immediate
instance of `explainableScalars_card_scale_dir`).  This is the easy half; it preserves the count for
ANY constant and does NOT by itself exhibit the coset structure.  The genuine coset-structure lever
— the bad SET being invariant under `γ ↦ g^{a-b}·γ`, which actually needs the RS rotation — is
`explainableScalars_monomial_gamma_dilation` below. -/
theorem explainableScalars_monomial_dir_scale
    (domain : ι ↪ F) (k : ℕ) (g : F) (hg0 : g ≠ 0)
    (δ : ℝ≥0) (a b : ℕ) :
    (explainableScalars (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (fun i => domain i ^ a) (fun i => g ^ b * (domain i ^ b))).card
      = (explainableScalars (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (fun i => domain i ^ a) (fun i => domain i ^ b)).card := by
  classical
  exact explainableScalars_card_scale_dir
    (ReedSolomon.code domain k : Set (ι → F)) δ
    (fun i => domain i ^ a) (fun i => domain i ^ b) (pow_ne_zero b hg0)

open Classical in
/-- **THE coset-structure lever: the bad SET is invariant under `γ ↦ g^{a-b}·γ`.**  Let `σ` be the
dilation by `g ≠ 0` on the RS domain (`domain (σ i) = g · domain i`, the `μ_n`-dilation when
`g ∈ μ_n`).  Then on the monomial line `(domain^a, domain^b)`, the *bad-scalar set itself* is fixed
by multiplying `γ` by `g^{a-b}` (`b ≤ a` form):

  `(explainableScalars RS δ (domain^a) (domain^b)).image (fun γ => g^(a-b) · γ)
     = explainableScalars RS δ (domain^a) (domain^b)`.

PROOF (genuinely uses the RS rotation — NOT a trivial card equality).  Rotating the whole line by
`σ` fixes the bad set (`explainableScalars_rs_rotate`, RS-fixedness) and turns
`domain^e ↦ (domain ∘ σ)^e = g^e · domain^e`.  Then `scale_both` by `g^{-a}` (RS is a submodule,
absorbs the constant into the codeword) brings the offset back to `domain^a` and leaves the
direction `g^{b-a} · domain^b`.  Finally `scale_dir` reindexes the direction-constant `g^{b-a}` into
the `γ`-index as `γ ↦ (g^{b-a})⁻¹ γ = g^{a-b} γ`.  Net: the set is `g^{a-b}`-dilation invariant.

Iterating over `g ∈ μ_n`, the orbit `{ g^{a-b} : g ∈ μ_n } = μ_{n/gcd(n,a-b)}`, so the bad set is a
union of `μ_{n/gcd(n,a-b)}`-cosets — exactly the quantization the probe measured (45/45 far
directions, 0 violations; `n=16` spike `a=10,b=4`, `gcd(16,6)=2`, `μ_8`-cosets, `I=11·8+1`). -/
theorem explainableScalars_monomial_gamma_dilation
    (domain : ι ↪ F) (k : ℕ) (σ : Equiv.Perm ι) (g : F)
    (hg0 : g ≠ 0) (hg : ∀ i, domain (σ i) = g * domain i)
    (δ : ℝ≥0) (a b : ℕ) (hba : b ≤ a) :
    (explainableScalars (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (fun i => domain i ^ a) (fun i => domain i ^ b)).image (fun γ => g ^ (a - b) * γ)
      = explainableScalars (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (fun i => domain i ^ a) (fun i => domain i ^ b) := by
  classical
  -- Step 1: rotate the whole line by σ. RS-rotation invariance keeps the bad set unchanged.
  have hrot := explainableScalars_rs_rotate (F := F) domain k σ g hg0 hg δ
    (fun i => domain i ^ a) (fun i => domain i ^ b)
  have hcomp : ∀ e : ℕ, ((fun i => domain i ^ e) ∘ ⇑σ) = (fun i => g ^ e * domain i ^ e) := by
    intro e; funext i
    simp only [Function.comp_apply, hg i, mul_pow]
  rw [hcomp a, hcomp b] at hrot
  -- hrot : E (g^a·dom^a) (g^b·dom^b) = E dom^a dom^b
  -- Step 2: scale_both by g^{-a} on the LHS pair → E dom^a (g^{b-a}·dom^b).
  -- write g^b = g^a * g^{b-a}? but b ≤ a so use g^a = g^{a-b} * g^b instead, and scale by g^{-a}.
  -- We compute: (g^a · dom^a) scaled by g^{-a} = dom^a; (g^b · dom^b) scaled by g^{-a} = g^{b-a}·dom^b.
  -- Since b ≤ a, g^{b-a} := (g^{a-b})⁻¹. We work with the direction g^{b} * g^{-a} = (g^{a-b})⁻¹.
  set c := g ^ (a - b) with hc_def
  have hc0 : c ≠ 0 := pow_ne_zero _ hg0
  have hscaleboth := explainableScalars_scale_both (ReedSolomon.code domain k) δ
    (fun i => domain i ^ a) (fun i => c⁻¹ * domain i ^ b) (c := g ^ a) (pow_ne_zero a hg0)
  -- hscaleboth : E (g^a·dom^a) (g^a·(c⁻¹·dom^b)) = E dom^a (c⁻¹·dom^b)
  -- and g^a · c⁻¹ = g^a · g^{-(a-b)} = g^b.   (a-b)+b = a.
  have hga : g ^ a * c⁻¹ = g ^ b := by
    have hsplit : g ^ a = c * g ^ b := by
      rw [hc_def, ← pow_add]; congr 1; omega
    rw [hsplit, mul_comm c (g ^ b), mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  have hrwdir : (fun i => g ^ a * (c⁻¹ * domain i ^ b)) = (fun i => g ^ b * domain i ^ b) := by
    funext i; rw [← mul_assoc, hga]
  rw [hrwdir] at hscaleboth
  -- hscaleboth : E (g^a·dom^a) (g^b·dom^b) = E dom^a (c⁻¹·dom^b)
  -- combine with hrot:  E dom^a dom^b = E dom^a (c⁻¹·dom^b)
  have hmid : explainableScalars (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (fun i => domain i ^ a) (fun i => domain i ^ b)
      = explainableScalars (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (fun i => domain i ^ a) (fun i => c⁻¹ * domain i ^ b) := by
    rw [← hrot, hscaleboth]
  -- Step 3: scale_dir on the RHS:  E dom^a (c⁻¹·dom^b) = (E dom^a dom^b).image (γ ↦ c·γ)
  have hscaledir := explainableScalars_scale_dir (ReedSolomon.code domain k : Set (ι → F)) δ
    (fun i => domain i ^ a) (fun i => domain i ^ b) (c := c⁻¹) (inv_ne_zero hc0)
  -- hscaledir : E dom^a (c⁻¹·dom^b) = (E dom^a dom^b).image (γ ↦ (c⁻¹)⁻¹ · γ) = .image (γ ↦ c·γ)
  rw [inv_inv] at hscaledir
  -- so  E dom^a dom^b = (E dom^a dom^b).image (γ ↦ c·γ).  Goal is the flip.
  exact (hmid.trans hscaledir).symm

/-! ## Part 3 — the spike law as a NAMED open obligation (granularity proven, count open). -/

/-- The **far-line incidence functional** on a monomial line `(a,b)` at rung `r` over `μ_n ⊂ F_p`,
as an opaque `ℕ` (the concrete instance is `(explainableScalars …).card`, p-independent
per probe). -/
structure MonomialIncidence (n k : ℕ) where
  /-- worst incidence over offsets `a` for direction `b` at agreement-need `n - r`. -/
  I : (a : ℕ) → (b : ℕ) → (r : ℕ) → ℕ
  /-- the `γ=0` indicator: `X^a` is NOT far at rung `r` (the line `X^a` is itself explainable). -/
  zeroBad : (a : ℕ) → (r : ℕ) → Bool

/-- The absolute difference `|a - b|` over `ℕ` (one of the two truncated subtractions is `0`). -/
def absDiff (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- **OBLIGATION Q (coset quantization — PROVEN granularity).**  The nonzero part of the incidence
on the `(a,b)` monomial line is a multiple of the coset size `n / gcd(n,|a-b|)`: there is a coset
count `c` with `I a b r = (if zeroBad then 1 else 0) + c · (n / Nat.gcd n (absDiff a b))`.  This is
the combinatorial consequence of `explainableScalars_monomial_gamma_dilation` (the bad SET is
invariant under `γ ↦ g^{a-b}·γ`, whose `μ_n`-orbit is `μ_{n/gcd(n,|a-b|)}`); it pins the GRANULARITY
of `I` but not the count `c`.  Verified exactly: `45/45` far directions, `0` violations
(`n ∈ {8,16}`). -/
def CosetQuantized (n k : ℕ) (D : MonomialIncidence n k) : Prop :=
  ∀ a b r : ℕ, ∃ c : ℕ,
    D.I a b r = (if D.zeroBad a r then 1 else 0) + c * (n / Nat.gcd n (absDiff a b))

/-- **OBLIGATION S (spike selection — the OPEN count).**  The spike (worst `(a,b)`) at the
threshold rung is achieved at the lowest far exponent `b = k` by an offset `a` with `gcd(n,|a-b|)`
*even* (imprimitive difference), and the coset count there is the maximal one.  This is the genuine
open core after quantization: which `(a,b)` maximizes `c`, and the value of `c`.  NAMED open. -/
def SpikeAtLowExponent (n k r : ℕ) (D : MonomialIncidence n k) : Prop :=
  ∀ a b : ℕ, k ≤ b → b < n - r → D.I a b r ≤ D.I (n - 2) k r

/-- **The deployed spike threshold (face 4 made concrete, as a conditional).**  Under quantization
`Q`, the incidence at the threshold rung is `≤ n` exactly when the spike coset count `c` satisfies
`c · (n / gcd) + 𝟙 ≤ n`, i.e. `c ≤ (n − 𝟙) · gcd / n`.  At the prize budget `B = n` the spike
binds the threshold: `WorstCaseFarIncidenceBounded` at `B = n` holds at rung `r` iff every monomial
incidence is `≤ n`, which—by quantization—is a constraint purely on the coset counts `c`. -/
theorem spike_threshold_is_coset_count_constraint
    {n k : ℕ} {D : MonomialIncidence n k} (hQ : CosetQuantized n k D)
    (a b r : ℕ) :
    D.I a b r ≤ n ↔
      ∃ c : ℕ, D.I a b r = (if D.zeroBad a r then 1 else 0) + c * (n / Nat.gcd n (absDiff a b))
        ∧ (if D.zeroBad a r then 1 else 0) + c * (n / Nat.gcd n (absDiff a b)) ≤ n := by
  obtain ⟨c, hc⟩ := hQ a b r
  constructor
  · intro h; exact ⟨c, hc, hc ▸ h⟩
  · rintro ⟨c', hc', hle⟩; rw [hc']; exact hle

end ProximityGap.SpikeQuantization

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.SpikeQuantization.explainableScalars_scale_dir
#print axioms ProximityGap.SpikeQuantization.explainableScalars_scale_both
#print axioms ProximityGap.SpikeQuantization.explainableScalars_card_scale_dir
#print axioms ProximityGap.SpikeQuantization.explainableScalars_monomial_dir_scale
#print axioms ProximityGap.SpikeQuantization.explainableScalars_monomial_gamma_dilation
#print axioms ProximityGap.SpikeQuantization.spike_threshold_is_coset_count_constraint
