/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy

/-!
# Attack 2: the DIRECT (Cauchy–Schwarz-free) count of the `e₂ = 0` bad-scalar locus (#407)

ABF26 Thm 5.1 / the W2 second-moment bound carry a square root: `ε_mca` is bounded by
`L²·δn` via a Cauchy–Schwarz `L² → L^∞` step (`T² ≤ |G|·E`). For Reed–Solomon the bad-scalar set
of the two-monomial pencil `x^k + α x^{k+2}` at agreement `k+2` is NOT a random `L²` object: it is
the **rigid algebraic locus** `{S : e₂(S) = 0, e₁(S) ≠ 0}`, with the bad scalar pinned to
`α(S) = −1/e₁(S)` (`E2VanishEnergy.badScalar_of_energy`). Attack 2 asks: does this rigidity give a
*direct* count of bad scalars — linear, with **no Cauchy–Schwarz `√`** — and if so, what is the
residual?

This file lands the **exact algebraic structure of the direct count**: the `e₂ = 0` locus, and its
image under the bad-scalar map `S ↦ −1/e₁(S)`, are **closed under scalar dilation** `S ↦ u • S`
(`u ≠ 0`). Concretely:

* `e1_smul` / `p2_smul` — `e₁(u • S) = u · e₁(S)`, `p₂(u • S) = u² · p₂(S)` (the power sums scale
  homogeneously);
* `e2_smul` — `e₂(u • S) = u² · e₂(S)` (the second elementary symmetric is degree-2 homogeneous);
* `e2_zero_smul` — the locus `e₂ = 0` is **scale-invariant**: `e₂(S) = 0 ⟹ e₂(u • S) = 0`;
* `badScalar_smul` — the bad scalar transforms **multiplicatively**: `α(u • S) = u⁻¹ · α(S)`, i.e.
  the bad-scalar set is **closed under multiplication by `u⁻¹`** for every `u ≠ 0`.

Specialised to dilation by the subgroup `μ_n` (the prize domain; each `u ∈ μ_n` permutes `μ_n`,
mapping `(k+2)`-subsets to `(k+2)`-subsets), this says the bad-scalar set is a **union of full
`μ_n`-cosets**, hence

  > **`#{bad α} = n · K`,  `K := #{dilation-orbits of e₁(S) over the e₂ = 0 locus}`.**

`badScalarSet_card_eq_orbit_mul` formalises the count form (over a finite scalar group `G` acting
freely on the bad-scalar set: `#bad = |G| · #orbits`).
The budget consumers `badScalarSet_card_le_mul_iff_orbitCount_le`,
`badScalarSet_card_le_group_card_iff_orbitCount_le_one`, and
`group_card_lt_badScalarSet_card_of_two_orbits` turn this exact count into the prize-facing
contract: a `C·n` bad-scalar budget is equivalent to at most `C` full `μ_n`-cosets, and at the
`n` budget two cosets are already fatal.

## The honest verdict (the precise obstruction)

The direct count **does remove both square roots** of the W2/ABF chain — it is an *exact* algebraic
cardinality `n · K`, with no `T² ≤ |G|·E` Cauchy–Schwarz step and no Johnson-transform radius `√`.
But the count does **not** collapse to `O(n)`: the residual `K(n)` (the orbit census of the
extremal `e₂ = 0` locus) is **super-linear**, measured (probe `probe_e2_n32.py`, prize-regime prime
`p = n⁴`, extremal width `w = n/2`):

| `n`  | `K` (orbit count) | `#{bad α} = n·K` |
|------|-------------------|------------------|
| 8    | 1                 | 8                |
| 16   | 3                 | 48               |
| 32   | 38                | 1216             |

So Attack 2 **re-collapses to the `e₂ = 0` extremal orbit count `K(n)`**, which is open — it is the
additive-energy / negation-pair excess (the SAME object `E_r(μ_n)` that the BGK route bounds), now
exposed as an *exact combinatorial census* rather than an `L²` energy. The rigidity converts the
analytic `√` (Cauchy–Schwarz) into a **computable-but-large** count; it does NOT make the count
small. This file pins the *exact reduction* `direct count = n · K` and the dilation rigidity that
makes it well-defined; the residual is `K`, the open extremal census (not BGK directly, but its
combinatorial twin).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi.
  *Open Problems in List Decoding and Correlated Agreement*. 2026.
  #407.
- Chai–Fan. *Action–Orbit FRI Soundness Above the Johnson Radius*. eprint 2026/861.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.E2VanishEnergy

namespace ArkLib.ProximityGap.E2DilationDirectCount

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Dilation of a finite node set.** `u • S := S.image (u * ·)`, the image of `S` under
multiplication by `u`. For `u ≠ 0` this is an injective relabelling, so `#(u • S) = #S`. -/
noncomputable def dil (u : F) (S : Finset F) : Finset F := S.image (fun s => u * s)

/-- For `u ≠ 0`, dilation preserves the cardinality: `#(u • S) = #S` (multiplication by a unit is
injective). -/
theorem dil_card {u : F} (hu : u ≠ 0) (S : Finset F) : (dil u S).card = S.card := by
  unfold dil
  rw [Finset.card_image_of_injective _ (mul_right_injective₀ hu)]

/-- For `u ≠ 0`, membership in the dilate: `x ∈ u • S ↔ u⁻¹ x ∈ S`. -/
theorem mem_dil {u : F} (hu : u ≠ 0) (S : Finset F) (x : F) :
    x ∈ dil u S ↔ u⁻¹ * x ∈ S := by
  unfold dil
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rwa [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  · intro h
    exact ⟨u⁻¹ * x, h, by rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]⟩

/-- **`e₁` scales linearly:** `e₁(u • S) = u · e₁(S)`. The first power sum is degree-1 homogeneous.
Needs `u ≠ 0` so that `(u * ·)` is injective on `S` (`Finset.sum_image`). -/
theorem e1_smul {u : F} (hu : u ≠ 0) (S : Finset F) : e1 (dil u S) = u * e1 S := by
  classical
  unfold e1 dil
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hu h), Finset.mul_sum]

/-- **`p₂` scales quadratically:** `p₂(u • S) = u² · p₂(S)`. The second power sum is degree-2
homogeneous. -/
theorem p2_smul {u : F} (hu : u ≠ 0) (S : Finset F) : p2 (dil u S) = u ^ 2 * p2 S := by
  classical
  unfold p2 dil
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hu h), Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **`e₂` scales quadratically:** `e₂(u • S) = u² · e₂(S)`. The second elementary symmetric is
degree-2 homogeneous, via `e₂ = (e₁² − p₂)/2` and the scalings of `e₁`, `p₂`. -/
theorem e2_smul {u : F} (hu : u ≠ 0) (S : Finset F) : e2 (dil u S) = u ^ 2 * e2 S := by
  rw [e2_eq, e2_eq, e1_smul hu, p2_smul hu]
  ring

/-- **The `e₂ = 0` locus is scale-invariant.** If `e₂(S) = 0` then `e₂(u • S) = 0` for every
`u ≠ 0`: dilation preserves the vanishing of the second elementary symmetric. This is the algebraic
fact that makes the bad-scalar set a *union of `μ_n`-cosets*. -/
theorem e2_zero_smul {u : F} (hu : u ≠ 0) {S : Finset F} (hS : e2 S = 0) : e2 (dil u S) = 0 := by
  rw [e2_smul hu, hS, mul_zero]

/-- **`e₁ ≠ 0` is scale-invariant** (for `u ≠ 0`): the nonvanishing of the first power sum
(the eligibility of the bad scalar `α = −1/e₁`) is preserved by dilation. -/
theorem e1_ne_zero_smul {u : F} (hu : u ≠ 0) {S : Finset F} (hS : e1 S ≠ 0) :
    e1 (dil u S) ≠ 0 := by
  rw [e1_smul hu]
  exact mul_ne_zero hu hS

/-- **The bad scalar transforms multiplicatively:** `α(u • S) = u⁻¹ · α(S)`, where
`α(S) := −1/e₁(S)` is the bad scalar of the two-monomial pencil at the `e₂ = 0` locus
(`E2VanishEnergy.badScalar_of_energy`). Hence the bad-scalar SET is **closed under multiplication
by `u⁻¹`** for every `u ≠ 0`: dilating the node set by `u` dilates the bad scalar by `u⁻¹`. -/
theorem badScalar_smul {u : F} (hu : u ≠ 0) (S : Finset F) :
    -(e1 (dil u S))⁻¹ = u⁻¹ * (-(e1 S)⁻¹) := by
  rw [e1_smul hu, mul_inv, mul_comm u⁻¹ _]
  ring

/-! ## The count form: `#{bad α} = n · K`

A finite multiplicative subgroup of `F` (as a `Finset F`) — concretely `μ_n` — acts on the
bad-scalar set by multiplication. The orbit of any nonzero `x` has *exactly* `n` elements (the
action is free since `x ≠ 0`), and orbits partition the set, giving the exact count
`#{bad α} = n · #{orbits}`. We package the subgroup as a `Finset F` with explicit group axioms
(self-contained; instantiate at `μ_n = rootsOfUnity n`). -/

/-- A finite multiplicative subgroup of `F`, recorded as a `Finset F` with the group axioms.
`one_mem`, `mul_mem`, `inv_mem` (closure under the field inverse), and `zero_notMem` (every element
is a unit). The intended instance is `μ_n` (the `n`-th roots of unity). -/
structure FinSubgroup (G : Finset F) : Prop where
  one_mem : (1 : F) ∈ G
  mul_mem : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G
  inv_mem : ∀ a ∈ G, a⁻¹ ∈ G
  zero_notMem : (0 : F) ∉ G

/-- **The concrete prize subgroup `μ_n = nthRootsFinset n 1` is a `FinSubgroup`.** This turns
the abstract orbit-budget lemmas below into statements about the actual smooth-domain
roots-of-unity finset used throughout the δ* cone. -/
theorem nthRootsFinset_finSubgroup {n : ℕ} (hn : 0 < n) :
    FinSubgroup (Polynomial.nthRootsFinset n (1 : F)) where
  one_mem := Polynomial.one_mem_nthRootsFinset hn
  mul_mem := by
    intro a ha b hb
    simpa [one_mul] using Polynomial.mul_mem_nthRootsFinset ha hb
  inv_mem := by
    intro a ha
    rw [Polynomial.mem_nthRootsFinset hn] at ha ⊢
    rw [inv_pow, ha, inv_one]
  zero_notMem := by
    intro hzero
    exact (Polynomial.ne_zero_of_mem_nthRootsFinset one_ne_zero hzero) rfl

/-- **The orbit of `x` under the dilation action of `G`:** `G • x = {u·x : u ∈ G}`. -/
noncomputable def orbit (G : Finset F) (x : F) : Finset F := G.image (fun u => u * x)

/-- **Each orbit has exactly `#G` elements** (free action). For `x ≠ 0`, `u ↦ u·x` is injective on
`G`, so the orbit `G • x` has cardinality `#G`. This is the precise "every bad-`α` value spawns a
full `μ_n`-coset of bad values" structural fact: the orbit is a complete coset of size `n`. -/
theorem orbit_card {G : Finset F} {x : F} (hx : x ≠ 0) : (orbit G x).card = G.card := by
  unfold orbit
  exact Finset.card_image_of_injective _ (mul_left_injective₀ hx)

/-- `x` itself lies in its orbit (`1 ∈ G`). -/
theorem self_mem_orbit {G : Finset F} (hG : FinSubgroup G) (x : F) : x ∈ orbit G x := by
  unfold orbit
  rw [Finset.mem_image]
  exact ⟨1, hG.one_mem, one_mul x⟩

/-- **Orbits are `G`-stable**: if `g ∈ G` then `g · y ∈ orbit G x` whenever `y ∈ orbit G x`. -/
theorem smul_mem_orbit {G : Finset F} (hG : FinSubgroup G) {g x y : F} (hg : g ∈ G)
    (hy : y ∈ orbit G x) : g * y ∈ orbit G x := by
  unfold orbit at hy ⊢
  rw [Finset.mem_image] at hy ⊢
  obtain ⟨u, hu, rfl⟩ := hy
  exact ⟨g * u, hG.mul_mem _ hg _ hu, by ring⟩

/-- **Orbits coincide or are disjoint — equality form.** If `y ∈ orbit G x` then
`orbit G y = orbit G x`. (Standard group-action orbit lemma; uses closure and inverses.) -/
theorem orbit_eq_of_mem {G : Finset F} (hG : FinSubgroup G) {x y : F} (hy : y ∈ orbit G x) :
    orbit G y = orbit G x := by
  unfold orbit at hy ⊢
  rw [Finset.mem_image] at hy
  obtain ⟨u, hu, rfl⟩ := hy
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v * u, hG.mul_mem _ hv _ hu, by ring⟩
  · rintro ⟨v, hv, rfl⟩
    -- z = v * x; write x = u⁻¹ * (u * x),
    -- so z = (v * u⁻¹) * (u * x).
    refine ⟨v * u⁻¹, hG.mul_mem _ hv _ (hG.inv_mem _ hu), ?_⟩
    have hune : u ≠ 0 := fun h => hG.zero_notMem (h ▸ hu)
    field_simp

/-- **The exact direct count: `#B = #G · K`.** Let `B` be a `Finset F` of *nonzero* scalars that is
**closed under dilation by `G`** (the bad-scalar set: closed under `μ_n` by `badScalar_smul`, and
`0 ∉ B` since `α = −1/e₁ ≠ 0`). Then `B` partitions into `G`-orbits, each of size exactly `#G`, so

  `#B = #(orbit representatives) · #G  =  #G · K`.

Here `K := #(B.image (orbit G ·))` is the number of distinct orbits. Specialised to `G = μ_n`
(`#G = n`), this is the exact reduction **`#{bad α} = n · K`** — the Cauchy–Schwarz-free direct
count. The residual `K` is the open extremal orbit census (super-linear in `n`; see the file
header), NOT a closed `O(n)` bound. -/
theorem badScalarSet_card_eq_orbit_mul {G : Finset F} (hG : FinSubgroup G) {B : Finset F}
    (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) :
    B.card = (B.image (fun x => orbit G x)).card * G.card := by
  classical
  -- partition B by orbit, each fiber is the orbit (size #G)
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x => orbit G x) (t := B.image (fun x => orbit G x))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
  -- each fiber {x ∈ B | orbit G x = O} equals the orbit O, hence has card #G
  rw [Finset.sum_congr rfl (g := fun _ => G.card) ?_, Finset.sum_const, smul_eq_mul]
  intro O hO
  rw [Finset.mem_image] at hO
  obtain ⟨x₀, hx₀B, rfl⟩ := hO
  have hx₀ne : x₀ ≠ 0 := fun h => hB0 (h ▸ hx₀B)
  -- the fiber over `orbit G x₀` is exactly `orbit G x₀`
  have hfiber : (B.filter (fun x => orbit G x = orbit G x₀)) = orbit G x₀ := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hz⟩
      rw [← hz]; exact self_mem_orbit hG z
    · intro hz
      have hzB : z ∈ B := by
        -- z = u * x₀ for some u ∈ G, and B is G-stable
        unfold orbit at hz
        rw [Finset.mem_image] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        exact hBstable u hu x₀ hx₀B
      exact ⟨hzB, orbit_eq_of_mem hG hz⟩
  rw [hfiber, orbit_card hx₀ne]

/-- **`#G ∣ #B`** — the divisibility corollary: the size of the bad-scalar set is divisible by the
order of the dilation subgroup. For `G = μ_n` this is `n ∣ #{bad α}`, the clean statement that the
direct count is a multiple of `n` (a union of full `n`-cosets). -/
theorem badScalarSet_card_dvd {G : Finset F} (hG : FinSubgroup G) {B : Finset F}
    (hB0 : (0 : F) ∉ B) (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) :
    G.card ∣ B.card := by
  rw [badScalarSet_card_eq_orbit_mul hG hB0 hBstable]
  exact Dvd.intro_left _ rfl

/-- **Budget iff orbit budget.** For a nonzero bad-scalar set `B` stable under a finite
multiplicative subgroup `G`, the exact orbit decomposition upgrades to the inequality form

  `#B ≤ C · #G  ↔  #(G-orbits in B) ≤ C`.

For `G = μ_n`, this is the direct `O(n)` coset-rigidity consumer: proving that the symmetric
function locus occupies at most `C` `μ_n`-cosets is exactly the same as proving the bad-scalar
budget `≤ C n`. -/
theorem badScalarSet_card_le_mul_iff_orbitCount_le {G : Finset F} (hG : FinSubgroup G)
    {B : Finset F} (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) (C : ℕ) :
    B.card ≤ C * G.card ↔ (B.image (fun x => orbit G x)).card ≤ C := by
  have hcard := badScalarSet_card_eq_orbit_mul hG hB0 hBstable
  have hGpos : 0 < G.card := Finset.card_pos.mpr ⟨1, hG.one_mem⟩
  constructor
  · intro h
    rw [hcard] at h
    exact Nat.le_of_mul_le_mul_right h hGpos
  · intro h
    rw [hcard]
    exact Nat.mul_le_mul_right G.card h

/-- **Prize-budget specialization.** At the natural subgroup budget `#G` (for `G = μ_n`, the
`q·ε* = n` budget), a stable bad-scalar set is within budget iff it has at most one full orbit.
This is the exact formal version of "pinning the R4 direct count at the prize budget means proving
one `μ_n`-coset, not merely a vague linear bound." -/
theorem badScalarSet_card_le_group_card_iff_orbitCount_le_one {G : Finset F}
    (hG : FinSubgroup G) {B : Finset F} (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) :
    B.card ≤ G.card ↔ (B.image (fun x => orbit G x)).card ≤ 1 := by
  simpa [one_mul] using badScalarSet_card_le_mul_iff_orbitCount_le hG hB0 hBstable 1

/-- **Scanner failure form.** A stable bad-scalar set fails the `C · #G` budget exactly when its
orbit count is strictly larger than `C`. This is often the form produced by brute-force or exact
symbolic scans: find `C+1` distinct full cosets, and the direct-count budget is refuted. -/
theorem not_badScalarSet_card_le_mul_iff_orbitCount_gt {G : Finset F} (hG : FinSubgroup G)
    {B : Finset F} (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) (C : ℕ) :
    (¬ B.card ≤ C * G.card) ↔ C < (B.image (fun x => orbit G x)).card := by
  rw [badScalarSet_card_le_mul_iff_orbitCount_le hG hB0 hBstable C]
  omega

/-- **Prize scanner form.** At the subgroup-size budget, failure is exactly the presence of at
least two full orbits. For `G = μ_n`, this is the precise yes/no target for the R4 direct
bad-scalar count: one `μ_n`-coset is budget-compatible; two are not. -/
theorem not_badScalarSet_card_le_group_card_iff_two_orbits {G : Finset F}
    (hG : FinSubgroup G) {B : Finset F} (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) :
    (¬ B.card ≤ G.card) ↔ 2 ≤ (B.image (fun x => orbit G x)).card := by
  rw [badScalarSet_card_le_group_card_iff_orbitCount_le_one hG hB0 hBstable]
  omega

/-- If a stable bad-scalar set is nonempty and fits in the subgroup-size budget, then it is
exactly one full orbit. This is the nonempty form consumed by scanners: once a witness exists, the
`n`-budget can only survive if all bad scalars lie in a single `μ_n`-coset. -/
theorem orbitCount_eq_one_of_nonempty_card_le_group_card {G : Finset F} (hG : FinSubgroup G)
    {B : Finset F} (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B) (hBne : B.Nonempty)
    (hbudget : B.card ≤ G.card) :
    (B.image (fun x => orbit G x)).card = 1 := by
  have hle : (B.image (fun x => orbit G x)).card ≤ 1 :=
    (badScalarSet_card_le_group_card_iff_orbitCount_le_one hG hB0 hBstable).mp hbudget
  have hpos : 0 < (B.image (fun x => orbit G x)).card :=
    Finset.card_pos.mpr (hBne.image _)
  omega

/-- **Two full orbits already break the subgroup-size budget.** If the orbit count is at least two,
then `#B > #G`. For `G = μ_n`, this is the sharp obstruction at the deployed `q·ε* = n` budget:
two distinct `μ_n`-cosets of bad scalars are already too many. -/
theorem group_card_lt_badScalarSet_card_of_two_orbits {G : Finset F} (hG : FinSubgroup G)
    {B : Finset F} (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ G, ∀ x ∈ B, g * x ∈ B)
    (horbits : 2 ≤ (B.image (fun x => orbit G x)).card) :
    G.card < B.card := by
  rw [badScalarSet_card_eq_orbit_mul hG hB0 hBstable]
  have hGpos : 0 < G.card := Finset.card_pos.mpr ⟨1, hG.one_mem⟩
  have hone : 1 < (B.image (fun x => orbit G x)).card := by omega
  simpa [one_mul] using Nat.mul_lt_mul_of_pos_right hone hGpos

/-! ## The `e₂ = 0` bad-scalar image is automatically subgroup-stable -/

/-- The direct-count bad-scalar image of the eligible `e₂ = 0`, `e₁ ≠ 0`, fixed-cardinality
subsets of a finite subgroup `G`. This is the exact finite combinatorial locus exposed by
`badScalar_of_energy`: `S ↦ -1/e₁(S)`. -/
noncomputable def e2BadScalarSet (G : Finset F) (w : ℕ) : Finset F :=
  ((G.powersetCard w).filter (fun S : Finset F => e2 S = 0 ∧ e1 S ≠ 0)).image
    (fun S => -(e1 S)⁻¹)

/-- The `e₂ = 0` bad-scalar image never contains zero, because every eligible subset has
`e₁(S) ≠ 0`. -/
theorem zero_notMem_e2BadScalarSet (G : Finset F) (w : ℕ) :
    (0 : F) ∉ e2BadScalarSet G w := by
  classical
  intro hzero
  unfold e2BadScalarSet at hzero
  rw [Finset.mem_image] at hzero
  obtain ⟨S, hS, hα⟩ := hzero
  rw [Finset.mem_filter] at hS
  have hinv0 : (e1 S)⁻¹ = 0 := by simpa using hα
  exact (inv_ne_zero hS.2.2) hinv0

/-- The `e₂ = 0` bad-scalar image is stable under multiplication by the subgroup.  Mechanism:
for `g ∈ G`, the subset `S` is sent to `g⁻¹ • S`; the subgroup axioms keep it inside `G`, `dil_card`
preserves its cardinality, `e2_zero_smul`/`e1_ne_zero_smul` preserve eligibility, and
`badScalar_smul` sends `-1/e₁(S)` to `g · (-1/e₁(S))`. -/
theorem e2BadScalarSet_stable {G : Finset F} (hG : FinSubgroup G) (w : ℕ) :
    ∀ g ∈ G, ∀ x ∈ e2BadScalarSet G w, g * x ∈ e2BadScalarSet G w := by
  classical
  intro g hg α hα
  have hg0 : g ≠ 0 := fun h => hG.zero_notMem (h ▸ hg)
  have hginv0 : g⁻¹ ≠ 0 := inv_ne_zero hg0
  unfold e2BadScalarSet at hα ⊢
  rw [Finset.mem_image] at hα ⊢
  obtain ⟨S, hS, rfl⟩ := hα
  rw [Finset.mem_filter] at hS
  obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS.1
  let S' := dil g⁻¹ S
  refine ⟨S', ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        unfold S' dil at hx
        rw [Finset.mem_image] at hx
        obtain ⟨s, hs, rfl⟩ := hx
        exact hG.mul_mem _ (hG.inv_mem _ hg) _ (hSsub hs)
      · unfold S'
        rw [dil_card hginv0, hScard]
    · exact ⟨e2_zero_smul hginv0 hS.2.1, e1_ne_zero_smul hginv0 hS.2.2⟩
  · unfold S'
    simpa [inv_inv] using badScalar_smul hginv0 S

/-- Exact orbit decomposition for the concrete `e₂ = 0` direct-count bad-scalar image. -/
theorem e2BadScalarSet_card_eq_orbit_mul {G : Finset F} (hG : FinSubgroup G) (w : ℕ) :
    (e2BadScalarSet G w).card =
      ((e2BadScalarSet G w).image (fun x => orbit G x)).card * G.card :=
  badScalarSet_card_eq_orbit_mul hG
    (zero_notMem_e2BadScalarSet G w)
    (e2BadScalarSet_stable hG w)

/-- Budget iff orbit budget for the concrete `e₂ = 0` bad-scalar image. -/
theorem e2BadScalarSet_card_le_mul_iff_orbitCount_le {G : Finset F}
    (hG : FinSubgroup G) (w C : ℕ) :
    (e2BadScalarSet G w).card ≤ C * G.card ↔
      ((e2BadScalarSet G w).image (fun x => orbit G x)).card ≤ C :=
  badScalarSet_card_le_mul_iff_orbitCount_le hG
    (zero_notMem_e2BadScalarSet G w)
    (e2BadScalarSet_stable hG w) C

/-! ## Concrete `μ_n` consumers

When a primitive `n`-th root exists, `Polynomial.nthRootsFinset n 1` has cardinality exactly `n`.
The next lemmas specialize the abstract direct-count contract to the literal prize-domain budget.
-/

/-- **Concrete `μ_n` budget iff orbit budget.** If `ζ` is a primitive `n`-th root, then a
`μ_n`-stable nonzero bad-scalar set satisfies `#B ≤ C n` exactly when it occupies at most `C`
full `μ_n`-orbits. -/
theorem badScalarSet_card_le_mul_n_iff_muOrbitCount_le {n C : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) {B : Finset F}
    (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ Polynomial.nthRootsFinset n (1 : F), ∀ x ∈ B, g * x ∈ B) :
    B.card ≤ C * n ↔
      (B.image (fun x => orbit (Polynomial.nthRootsFinset n (1 : F)) x)).card ≤ C := by
  simpa [hζ.card_nthRootsFinset] using
    (badScalarSet_card_le_mul_iff_orbitCount_le
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn) hB0 hBstable C)

/-- **Concrete prize-budget specialization.** Under a primitive `n`-th root, the natural
`μ_n` budget `#B ≤ n` is equivalent to at most one full `μ_n`-orbit. -/
theorem badScalarSet_card_le_n_iff_muOrbitCount_le_one {n : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) {B : Finset F}
    (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ Polynomial.nthRootsFinset n (1 : F), ∀ x ∈ B, g * x ∈ B) :
    B.card ≤ n ↔
      (B.image (fun x => orbit (Polynomial.nthRootsFinset n (1 : F)) x)).card ≤ 1 := by
  simpa [one_mul] using
    (badScalarSet_card_le_mul_n_iff_muOrbitCount_le
      (F := F) (n := n) (C := 1) hn hζ hB0 hBstable)

/-- **Concrete prize scanner form.** At the literal `μ_n` budget, failure is exactly the presence
of at least two full `μ_n`-orbits. -/
theorem not_badScalarSet_card_le_n_iff_two_muOrbits {n : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) {B : Finset F}
    (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ Polynomial.nthRootsFinset n (1 : F), ∀ x ∈ B, g * x ∈ B) :
    (¬ B.card ≤ n) ↔
      2 ≤ (B.image (fun x => orbit (Polynomial.nthRootsFinset n (1 : F)) x)).card := by
  rw [badScalarSet_card_le_n_iff_muOrbitCount_le_one hn hζ hB0 hBstable]
  omega

/-- **Two concrete `μ_n`-orbits already exceed the literal `n` budget.** This is the deployed
scanner obstruction in its smooth-domain form. -/
theorem n_lt_badScalarSet_card_of_two_muOrbits {n : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) {B : Finset F}
    (hB0 : (0 : F) ∉ B)
    (hBstable : ∀ g ∈ Polynomial.nthRootsFinset n (1 : F), ∀ x ∈ B, g * x ∈ B)
    (horbits : 2 ≤
      (B.image (fun x => orbit (Polynomial.nthRootsFinset n (1 : F)) x)).card) :
    n < B.card := by
  simpa [hζ.card_nthRootsFinset] using
    (group_card_lt_badScalarSet_card_of_two_orbits
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn) hB0 hBstable horbits)

/-! ## Concrete `e₂ = 0` bad-scalar image consumers over `μ_n` -/

/-- **Concrete `e₂ = 0` image budget iff orbit budget.** For the actual smooth-domain subgroup
`μ_n = nthRootsFinset n 1`, the finite image `S ↦ -1/e₁(S)` from the `e₂ = 0`, `e₁ ≠ 0` locus
satisfies `#bad ≤ C n` exactly when it occupies at most `C` full `μ_n`-orbits. -/
theorem e2BadScalarSet_mu_card_le_mul_n_iff_orbitCount_le {n C : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (w : ℕ) :
    (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w).card ≤ C * n ↔
      ((e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w).image
        (fun x => orbit (Polynomial.nthRootsFinset n (1 : F)) x)).card ≤ C := by
  simpa [hζ.card_nthRootsFinset] using
    (e2BadScalarSet_card_le_mul_iff_orbitCount_le
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn) w C)

/-- **Concrete `e₂ = 0` prize-budget specialization.** The literal `n` budget for the
`e₂ = 0` bad-scalar image over `μ_n` is equivalent to at most one full `μ_n`-orbit. -/
theorem e2BadScalarSet_mu_card_le_n_iff_orbitCount_le_one {n : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (w : ℕ) :
    (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w).card ≤ n ↔
      ((e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w).image
        (fun x => orbit (Polynomial.nthRootsFinset n (1 : F)) x)).card ≤ 1 := by
  simpa [one_mul] using
    (e2BadScalarSet_mu_card_le_mul_n_iff_orbitCount_le
      (F := F) (n := n) (C := 1) hn hζ w)

/-- **Concrete `e₂ = 0` prize scanner form.** The `e₂ = 0` image fails the literal `n` budget
exactly when it contains at least two full `μ_n`-orbits. -/
theorem not_e2BadScalarSet_mu_card_le_n_iff_two_orbits {n : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (w : ℕ) :
    (¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w).card ≤ n) ↔
      2 ≤ ((e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w).image
        (fun x => orbit (Polynomial.nthRootsFinset n (1 : F)) x)).card := by
  rw [e2BadScalarSet_mu_card_le_n_iff_orbitCount_le_one hn hζ w]
  omega

/-- **Two concrete `e₂ = 0` image orbits exceed the literal `n` budget.** This packages the
scanner obstruction directly for the finite image over `μ_n`. -/
theorem n_lt_e2BadScalarSet_mu_card_of_two_orbits {n : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (w : ℕ)
    (horbits : 2 ≤
      ((e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w).image
        (fun x => orbit (Polynomial.nthRootsFinset n (1 : F)) x)).card) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w).card := by
  simpa [hζ.card_nthRootsFinset] using
    (group_card_lt_badScalarSet_card_of_two_orbits
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn)
      (zero_notMem_e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) w)
      (e2BadScalarSet_stable
        (nthRootsFinset_finSubgroup (F := F) hn) w)
      horbits)

end ArkLib.ProximityGap.E2DilationDirectCount

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
namespace ArkLib.ProximityGap.E2DilationDirectCount

#print axioms dil_card
#print axioms mem_dil
#print axioms e1_smul
#print axioms p2_smul
#print axioms e2_smul
#print axioms e2_zero_smul
#print axioms e1_ne_zero_smul
#print axioms badScalar_smul
#print axioms nthRootsFinset_finSubgroup
#print axioms orbit_card
#print axioms self_mem_orbit
#print axioms smul_mem_orbit
#print axioms orbit_eq_of_mem
#print axioms badScalarSet_card_eq_orbit_mul
#print axioms badScalarSet_card_dvd
#print axioms badScalarSet_card_le_mul_iff_orbitCount_le
#print axioms badScalarSet_card_le_group_card_iff_orbitCount_le_one
#print axioms not_badScalarSet_card_le_mul_iff_orbitCount_gt
#print axioms not_badScalarSet_card_le_group_card_iff_two_orbits
#print axioms orbitCount_eq_one_of_nonempty_card_le_group_card
#print axioms group_card_lt_badScalarSet_card_of_two_orbits
#print axioms zero_notMem_e2BadScalarSet
#print axioms e2BadScalarSet_stable
#print axioms e2BadScalarSet_card_eq_orbit_mul
#print axioms e2BadScalarSet_card_le_mul_iff_orbitCount_le
#print axioms badScalarSet_card_le_mul_n_iff_muOrbitCount_le
#print axioms badScalarSet_card_le_n_iff_muOrbitCount_le_one
#print axioms not_badScalarSet_card_le_n_iff_two_muOrbits
#print axioms n_lt_badScalarSet_card_of_two_muOrbits
#print axioms e2BadScalarSet_mu_card_le_mul_n_iff_orbitCount_le
#print axioms e2BadScalarSet_mu_card_le_n_iff_orbitCount_le_one
#print axioms not_e2BadScalarSet_mu_card_le_n_iff_two_orbits
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_orbits

end ArkLib.ProximityGap.E2DilationDirectCount
