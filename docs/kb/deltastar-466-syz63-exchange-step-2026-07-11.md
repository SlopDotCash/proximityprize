# SYZ63 — the graded leading-vector exchange step, discharged (2026-07-11)

**Issue #466 (Proximity Gap).** Status delta for the syzygy / two-ramp cone.

## Headline

`GradedExchange` — the single named residual SYZ62 left behind — is now **proved
unconditionally and axiom-clean**, for *every* rank-2 submodule of `K[X]³` and every weight
vector `d`. Landed in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ63ExchangeStep.lean`.

Axiom audit (all five public results): `[propext, Classical.choice, Quot.sound]` only — no
`sorryAx`, no `native_decide`.

## What lands (verbatim statements)

```
theorem exists_gradedExchange (d : Fin 3 → ℕ) (N : Submodule K[X] (Fin 3 → K[X]))
    (hrank : Module.rank K[X] N = 2) :
    ∃ e₁ ∈ N, ∃ e₂ ∈ N, GradedExchange (d := d) N e₁ e₂

theorem syzygyKernel_gradedExchange (d : Fin 3 → ℕ) {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    ∃ e₁ ∈ LinearMap.ker (SYZ61.syzygyMap f g h),
      ∃ e₂ ∈ LinearMap.ker (SYZ61.syzygyMap f g h),
        GradedExchange (d := d) (LinearMap.ker (SYZ61.syzygyMap f g h)) e₁ e₂

theorem syzygyKernel_muBasis_span (d : Fin 3 → ℕ) {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    ∃ e₁ e₂ : Fin 3 → K[X],
      LinearMap.ker (SYZ61.syzygyMap f g h)
        = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X]))
```

`syzygyKernel_muBasis_span` chains this with SYZ62's `syzygyKernel_eq_span_of_gradedExchange`:
the syzygy kernel of a coprime triple is the `K[X]`-span of a degree-minimal (μ-)basis, with **no
remaining hypothesis** — the μ-basis generation statement is now a theorem, not a `Prop`.

## The proof (leading-vector exchange, formalized)

Supporting lemmas proved en route (all axiom-clean):

- `coeff_mul_top` — top coefficient of a product: `(q*p).coeff (deg q + m) = leadCoeff q * coeff p m`
  for `m ≥ deg p` (classical `coeff_mul_degree_add_degree` at `m = deg p`; both sides vanish above).
- `pdeg_ne_bot_of_ne_zero`, `lv_ne_zero_of_pdeg_eq`, `pdeg_lt_of_lv_eq_zero` — the grading/leading-
  vector detection facts (a nonzero vector has a nonzero leading vector at its product-degree; the
  converse `pdeg ≤ D ∧ lv_D = 0 ⇒ pdeg < D`).
- `pdeg_neg`, `pdeg_sub_le` — subtraction subadditivity in the product-degree grading.
- `lv_smul_top` — leading vector under `K[X]`-scaling at the top target degree:
  `lv (natDeg q + D) (q • w) = leadCoeff q • lv D w`. This is the linchpin.
- `no_three_independent_lv` — the **rank descent**: three nonzero members of a rank-2 submodule
  with `K`-independent leading vectors are `K[X]`-independent (top-degree cancellation via
  `lv_smul_top`), so `le_rank_iff` gives `3 ≤ rank = 2`, contradiction.

Selection: minimal-`pdeg` nonzero `e₁` and minimal-`pdeg` `e₂ ∈ N \ K[X]·e₁` via
`WellFounded.has_min` on `WithBot ℕ`; `K[X]·e₁ ≠ N` from `rank_span_le`/`Submodule.rank_mono`
(`rank ≤ 1 < 2`). `lc₁, lc₂` independence from `δ₂`-minimality. The exchange: `w ∈ K[X]·e₁`
reduces to 0; otherwise `pdeg w ≥ δ₂` and `lv (pdeg w) w ∈ span_K{lc₁,lc₂}` (else the rank descent
fires), and the matching monomial multiples cancel the leading vector, dropping `pdeg`.

## Honest scope — what is NOT closed

- **`SYZ60.MuBasisWindowIso` / `SYZ44.RankNullity` remain open.** They need the *windowed* finrank
  iso (injectivity + surjectivity of `(q₁,q₂) ↦ q₁e₁+q₂e₂` on the degree windows), a further
  degree-bookkeeping layer on top of the *span* generation landed here. SYZ63 gives span
  generation, not the window count. So the degree-sum law is still conditional on that separate
  bookkeeping.
- No δ* closure is claimed.

## Coercion pitfall (for future agents)

`(n : WithBot ℕ)` elaborates to `Nat.cast`, whereas `WithBot.ne_bot_iff_exists` and
`degree_eq_natDegree` produce the `WithBot.some` coercion. They are **defeq but not syntactically
equal**, so `rw` fails to match across them while `exact`/`.trans`/`le_of_eq` succeed by defeq.
Use `Nat.cast_inj/le/lt` and `Nat.cast_withBot` (or just `.trans`/defeq assignment) rather than
`WithBot.coe_*` lemmas when bridging `pdeg` values (which live in `Nat.cast` form) to nats.

## Build

Lockless iterate: `scripts/pg-iterate.sh <file>` (~8s). Imports only
`_SYZ62GradedExchange` (which pulls SYZ61/SYZ60/SYZ57/SYZ44). Olean built lockless.
