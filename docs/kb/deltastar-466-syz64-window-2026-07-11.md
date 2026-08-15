# SYZ64 — the μ-basis window bookkeeping (2026-07-11)

**Issue:** #466 (Proximity Prize / δ*). **Branch:** `codex/syz64-window-bookkeeping`
(off `fork/research/proximity-prize` tip `6074262f8`).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ64WindowBookkeeping.lean`.

## Headline

The μ-basis **window isomorphism** is discharged. `SYZ60.MuBasisWindowIso` — the last named
residual feeding `SYZ44.TwoRamp` (the two-ramp Hilbert shape) — is now proved unconditionally for
the syzygy kernel of a coprime triple. Consequently **`SYZ44.TwoRamp` is unconditional**, and the
degree-sum law `n₁ + n₂ = d₀ + d₁ + d₂` is proved **conditional on `SYZ44.RankNullity` alone**
(the degree-controlled Bézout surjectivity), which is now the single remaining structural input on
the syzygy side.

## Chain status after SYZ64

- SYZ61: syzygy kernel free of rank exactly 2 — DONE (unconditional).
- SYZ62/SYZ63: graded exchange step + span generation (μ-basis generates the kernel) — DONE.
- **SYZ64 (this): `MuBasisWindowIso` / `TwoRamp` — DONE (unconditional).**  ⇐ new.
- `SYZ44.RankNullity` (Bézout surjectivity onto `{deg ≤ D}` with degree control) — **OPEN**
  (SYZ57 supplies only the *ungraded* Bézout seed `exists_triple_repr`, no degree control).
- Downstream balance input `ι ≤ 1` (gap ≤ 3) — OPEN, unchanged.

So `degree_sum` is no longer double-conditional (was `RankNullity ∧ TwoRamp`); `TwoRamp` is
discharged, leaving `RankNullity` as the lone open input.

## The mathematics (Task A)

The core is the **no-cancellation lemma** `pdeg_combo_eq`:

    pdeg d (q₁ • e₁ + q₂ • e₂) = max (pdeg d (q₁ • e₁)) (pdeg d (q₂ • e₂))

for the degree-minimal μ-basis pair. It holds because the leading vectors `lv d n₁ e₁`,
`lv d n₂ e₂` are `K`-independent (SYZ63's selection), so the top terms of `q₁ • e₁` and `q₂ • e₂`
can never cancel. Two immediate corollaries:

- **Injectivity** `eq_zero_of_combo_eq_zero`: `q₁ • e₁ + q₂ • e₂ = 0 ⟹ q₁ = q₂ = 0`.
- **Degree control**: any window element's representation has `pdeg (qᵢ • eᵢ) ≤ pdeg w ≤ D`.

The `K`-linear map `Φ_D : degreeLT (D+1−n₁) × degreeLT (D+1−n₂) → K_D`,
`(q₁,q₂) ↦ q₁ • e₁ + q₂ • e₂`, is then injective (no-cancellation) with range exactly the window
`K_D := {w ∈ N : pdeg d w ≤ D}` (span generation ⊇, well-definedness ⊆). Via
`LinearMap.finrank_range_of_inj` + `Module.finrank_prod` + `SYZ60.finrank_degreeLT`:

    finrank K K_D = (D+1−n₁) + (D+1−n₂)        (`finrank_windowKD`)

which is `SYZ60.MuBasisWindowIso K (fun D => finrank K K_D) n₁ n₂` verbatim.

`exists_muBasisData` re-runs SYZ63's minimal-selection (well-founded on `pdeg`) but exports the
**full** structural bundle (`e₁,e₂,n₁,n₂`, pdeg values, `n₁≤n₂`, lc-independence, span), which
`exists_gradedExchange` discards.

## Task B (RankNullity) — NOT attempted here, honest scope

`RankNullity` needs the *balanced-window* Bézout surjectivity onto `{p : deg p ≤ D}` for large `D`,
i.e. a degree-controlled cofactor reduction. SYZ57's `exists_triple_repr` gives the ungraded seed
only. This remains a separate named residual; the a-posteriori cofactor-reduction route (subtract
μ-basis elements to bring cofactor degrees into windows) is the natural next SYZ rung.

## Key statements (verbatim)

    theorem pdeg_combo_eq (hpd₁ : pdeg d e₁ = ↑n₁) (hpd₂ : pdeg d e₂ = ↑n₂)
        (hpair : LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂]) (q₁ q₂ : K[X]) :
        pdeg d (q₁ • e₁ + q₂ • e₂) = max (pdeg d (q₁ • e₁)) (pdeg d (q₂ • e₂))

    theorem finrank_windowKD (hpd₁ …) (hpd₂ …) (hpair …)
        (hspan : N = Submodule.span K[X] {e₁, e₂}) (D : ℕ) :
        finrank K (windowKD d N D) = (D + 1 - n₁) + (D + 1 - n₂)

    theorem twoRamp_windowKD (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
        ∃ n₁ n₂ : ℕ, n₁ ≤ n₂ ∧
          SYZ44.TwoRamp (fun D => finrank K (windowKD d (ker (SYZ61.syzygyMap f g h)) D)) n₁ n₂

    theorem degree_sum_of_rankNullity (hfg …) (hfh …) (D₀ : ℕ)
        (hRankNull : SYZ44.RankNullity (fun D => finrank K (windowKD d (ker …) D))
          (d 0) (d 1) (d 2) D₀) :
        ∃ n₁ n₂ : ℕ, n₁ ≤ n₂ ∧ n₁ + n₂ = d 0 + d 1 + d 2

## Axiom audit

All seven theorems: `[propext, Classical.choice, Quot.sound]` only. No `sorry`, no `native_decide`.

## Build

`scripts/pg-iterate.sh <file>` (lockless, SYZ63 oleans present). Coercion pitfall from SYZ63 (pdeg
values in `Nat.cast` form) handled throughout via `Nat.cast_*` and `WithBot.natCast_ne_bot`.
