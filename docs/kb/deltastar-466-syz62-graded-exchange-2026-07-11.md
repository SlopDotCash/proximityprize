# δ* / #466 — SYZ62: the product-degree grading and the leading-vector exchange (2026-07-11)

**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ62GradedExchange.lean`
**Status:** axiom-clean (`propext, Classical.choice, Quot.sound` only); no `sorry`, no `native_decide`.
**Branch:** `codex/syz62-graded-exchange` (off `fork/research/proximity-prize` @ `9cca95f2a`).

## Where this sits in the two-ramp stack

- **SYZ44** `degree_sum_of_hilbert`: `RankNullity ∧ TwoRamp ⟹ δ₁ + δ₂ = a+b+c` (pure `ℕ` count).
- **SYZ60** `twoRamp_of_muBasisWindowIso`: reduces `TwoRamp` to `MuBasisWindowIso` (the windowed
  finrank iso) and lands `kernel_free` (free ⇒ rank ≤ 3).
- **SYZ61** `syzygyKernel_free_rank_two`: kernel of a coprime triple is **free of rank exactly 2**,
  unconditional.
- **SYZ62 (this file):** builds the *graded* apparatus that the μ-basis needs, and reduces the
  remaining classical content to a **single named residual `GradedExchange`** (the leading-vector
  exchange step). The multi-step windowed generation is *proved* from that one step.

## What SYZ62 proves (axiom-clean)

1. **Product-degree grading** `pdeg d w = maxᵢ (deg(wᵢ) + dᵢ)` on `K[X]³`, valued in `WithBot ℕ`
   (`⊥` for `0`):
   - `pdeg_smul : pdeg d (q • w) = q.degree + pdeg d w` (via `degree_mul`, `⊥`-absorbing).
   - `pdeg_add_le : pdeg d (w + w') ≤ max (pdeg d w) (pdeg d w')`.
   - `pdeg_zero`, `pterm_le_pdeg`, `pdeg_le` (universal property).
2. **Leading-coefficient vector** `lv d D w i = coeff (wᵢ) (D − dᵢ)` (leading coeff on slots that
   attain product-degree `D`, `0` elsewhere):
   - `lv_add`, `lv_smulK` (manifest `K`-linearity, being coefficient extraction),
   - `lv_eq_zero_of_pdeg_lt : pdeg d w < D ⟹ lv d D w = 0` (the leading vector detects the degree).
3. **The reduction (crux deliverable):** `span_of_gradedExchange` — granting the single-step
   `GradedExchange` (every nonzero `w ∈ N` reduces mod `q₁e₁+q₂e₂` to strictly smaller `pdeg`),
   **well-founded recursion on `pdeg` (`WithBot ℕ` is `WellFoundedLT`) shows `e₁,e₂` generate all of
   `N`.** Specialized to the syzygy kernel: `syzygyKernel_eq_span_of_gradedExchange`.

## Honest residual — what is NOT closed

- **`GradedExchange` itself is a hypothesis.** The leading-vector *independence / rank-2
  triangularity* argument that discharges the single exchange step (`lv d D w` lies in the
  `K`-span of the two shifted generator leading vectors, forced ≤-2-dim by SYZ61's rank-2 freeness)
  is **not** formalized here. The `lv` linear structure is in place to support it, but the
  independence + top-cancellation step is open.
- **`MuBasisWindowIso` is NOT discharged.** SYZ62 gives *generation* (`N = span{e₁,e₂}`), not the
  `K`-linear *windowed finrank isomorphism* `K_D ≅ degreeLT(D+1−δ₁) × degreeLT(D+1−δ₂)` that SYZ60's
  residual demands. That still needs (i) `GradedExchange`, (ii) degree-minimal `δ₁≤δ₂` existence,
  (iii) the window-count linear equivalence.
- Therefore **`SYZ44.RankNullity`, `SYZ60.MuBasisWindowIso`, and the degree-sum law remain
  conditional.** No δ* closure claimed.

Net effect: the two-ramp residual is narrowed from "graded μ-basis existence (a-rank-drop + b)" to
**`GradedExchange` (the leading-vector exchange step) alone**, with the multi-step generation now
machine-checked.

## Verbatim key statements

```
theorem pdeg_smul (d : Fin 3 → ℕ) (q : K[X]) (w : Fin 3 → K[X]) :
    pdeg d (q • w) = q.degree + pdeg d w

theorem pdeg_add_le (d : Fin 3 → ℕ) (w w' : Fin 3 → K[X]) :
    pdeg d (w + w') ≤ max (pdeg d w) (pdeg d w')

theorem lv_eq_zero_of_pdeg_lt (d : Fin 3 → ℕ) (D : ℕ) (w : Fin 3 → K[X])
    (hlt : pdeg d w < (D : WithBot ℕ)) : lv d D w = 0

def GradedExchange (N : Submodule K[X] (Fin 3 → K[X])) (e₁ e₂ : Fin 3 → K[X]) : Prop :=
  ∀ w ∈ N, w ≠ 0 → ∃ q₁ q₂ : K[X],
    pdeg d (w - (q₁ • e₁ + q₂ • e₂)) < pdeg d w

theorem span_of_gradedExchange {N : Submodule K[X] (Fin 3 → K[X])} {e₁ e₂ : Fin 3 → K[X]}
    (he₁ : e₁ ∈ N) (he₂ : e₂ ∈ N) (hex : GradedExchange (d := d) N e₁ e₂) :
    ∀ w ∈ N, w ∈ Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X]))

theorem syzygyKernel_eq_span_of_gradedExchange {d : Fin 3 → ℕ} {f g h : K[X]}
    {e₁ e₂ : Fin 3 → K[X]}
    (he₁ : e₁ ∈ LinearMap.ker (SYZ61.syzygyMap f g h))
    (he₂ : e₂ ∈ LinearMap.ker (SYZ61.syzygyMap f g h))
    (hex : GradedExchange (d := d) (LinearMap.ker (SYZ61.syzygyMap f g h)) e₁ e₂) :
    LinearMap.ker (SYZ61.syzygyMap f g h)
      = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X]))
```
