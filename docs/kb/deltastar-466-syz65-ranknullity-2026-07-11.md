# δ* #466 — SYZ65: degree-controlled Bézout surjectivity ⇒ `RankNullity` unconditional (2026-07-11)

**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ65RankNullity.lean`
**Status:** axiom-clean (`propext, Classical.choice, Quot.sound` only; no `sorry`, no `native_decide`).
**Branch:** `codex/syz65-ranknullity` off `fork/research/proximity-prize` (`d401c974e`).

## What landed

SYZ64 discharged `SYZ44.TwoRamp` for the syzygy kernel of a coprime triple, leaving the μ-basis
degree-sum law `n₁ + n₂ = d₀ + d₁ + d₂` conditional on the **single** remaining structural input
`SYZ44.RankNullity` — the degree-controlled Bézout surjectivity of the balanced-window map plus its
rank–nullity dimension count. **SYZ65 discharges `RankNullity` unconditionally**, so the degree-sum
law is now **unconditional** (given only that `d i` is the degree of generator `i` and that the
triple is coprime). Both structural inputs of `SYZ44.degree_sum_of_hilbert` are proved theory.

## Verbatim headline statements

```lean
theorem rankNullity_windowKD {f g h : K[X]} {d : Fin 3 → ℕ}
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hd0 : d 0 = f.natDegree) (hd1 : d 1 = g.natDegree) (hd2 : d 2 = h.natDegree)
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    ∃ D₀ : ℕ, ArkLib.ProximityGap.SYZ44.RankNullity
      (fun D => finrank K (SYZ64.windowKD d (LinearMap.ker (SYZ61.syzygyMap f g h)) D))
      (d 0) (d 1) (d 2) D₀

theorem degree_sum_unconditional {f g h : K[X]} {d : Fin 3 → ℕ}
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hd0 : d 0 = f.natDegree) (hd1 : d 1 = g.natDegree) (hd2 : d 2 = h.natDegree)
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    ∃ n₁ n₂ : ℕ, n₁ ≤ n₂ ∧ n₁ + n₂ = d 0 + d 1 + d 2
```

`D₀ = n₂` (the larger μ-basis product-degree). `degree_sum_unconditional` chains
`rankNullity_windowKD` into SYZ64's `degree_sum_of_rankNullity` (which already carried the SYZ64
`TwoRamp` half).

## The proof (cofactor-reduction descent + rank–nullity of the window map)

Fix the coprime triple with generator weights and `D ≥ n₂`. The `K`-linear **balanced-window map**

  `Ψ_D : degreeLT(D+1−d₀) × degreeLT(D+1−d₁) × degreeLT(D+1−d₂) → K[X]`,
  `(r₀,r₁,r₂) ↦ r₀·f + r₁·g + r₂·h`  (`psiMap`)

is analysed by rank–nullity (`LinearMap.finrank_range_add_finrank_ker`):

1. **Domain** finrank `= (D+1−d₀)+(D+1−d₁)+(D+1−d₂)` (`Module.finrank_prod` + `finrank_degreeLT`).
2. **Kernel** `≅ windowKD d (ker φ) D` via the coordinate map `jMap p = ![p.1,p.2.1,p.2.2]`
   (injective, range `= windowKD`), so `finrank (ker Ψ_D) = finrank (windowKD …) = hilb D`.
3. **Range** `= degreeLT(D+1)`, so `finrank (range Ψ_D) = D+1`.

The genuine content is **range surjectivity** (`exists_window_repr`): given `p` with `deg p ≤ D`,
take any ungraded Bézout representative `r` with `φ r = p` (SYZ57 `exists_triple_repr`); if
`pdeg d r = M > D` then `deg(φ r) = deg p ≤ D < M`, so the top-degree coefficient of `φ r` vanishes.

- **Top-coefficient identity** (`coeff_phi_eq_leadMap`): for `d i = deg (gen i)` and `pdeg d r ≤ M`,
  `(φ r).coeff M = leadMap (lv d M r)` where `leadMap v = f.lead·v₀+g.lead·v₁+h.lead·v₂` (the
  leading functional `L : K³ → K`). Per slot `coeff (gen·r) M = gen.lead · r.coeff (M−deg gen)`.
- **Leading-space span** (`exists_coeff_of_leadMap_zero`): `L` is a nonzero functional, so
  `finrank (ker L) = 2` (rank–nullity in `K³`); the μ-basis leading vectors `lv d nⱼ eⱼ ∈ ker L`
  (their `L`-image is the top coefficient of `φ eⱼ = 0`) are independent, hence
  `span{lv e₁, lv e₂} = ker L`. So `lv d M r ∈ ker L` ⇒ `lv d M r = c₁·lv e₁ + c₂·lv e₂`.
- **The subtraction:** `r' := r − (C c₁·X^{M−n₁}·e₁ + C c₂·X^{M−n₂}·e₂)` keeps `φ r' = φ r = p`
  (the `eⱼ` are syzygies, `syzygyMap` `K[X]`-linear) and kills `lv d M r'`, dropping `pdeg` below
  `M`. **Well-founded descent** on `pdeg` (`WellFoundedLT.induction` over `WithBot ℕ`) bottoms out at
  `pdeg d r ≤ D`. This is the SYZ64 GradedExchange machinery applied to a **non-kernel**
  representative, with the span membership coming from `ker L` (2-dim) instead of
  `no_three_independent_lv`.

Rank–nullity then reads `(D+1) + hilb D = (D+1−d₀)+(D+1−d₁)+(D+1−d₂)`, i.e. exactly
`SYZ44.RankNullity`.

## Equivalent framing (why this is the whole content)

Given SYZ64's `TwoRamp` (`hilb D = (D+1−n₁)+(D+1−n₂)`), `RankNullity` for large `D` is arithmetically
equivalent to the degree-sum law `n₁+n₂ = d₀+d₁+d₂`. SYZ65 proves the **surjectivity** side directly
via the descent, so it yields `RankNullity` for **every** `D ≥ n₂` (not just asymptotically) and does
not route through the large-`D` arithmetic.

## Scope / honesty

Discharges `RankNullity` (hence the degree-sum law) **unconditionally** for the coprime-triple
syzygy kernel with the generator weights. Does **not** claim δ* closure: the μ-basis **imbalance
bound `ι ≤ 1`** (gap `≤ 3`) remains the sole open mathematical input on the Sylvester side (G172),
and the production wire still needs SYZ33 lemma-1 supports, the general-`D` peel, SYZ22
realizability, and the `MCAThresholdLedger` BGK/incidence bound. CORE remains OPEN / ON-BGK.

## Reusable playbook

- **Rank–nullity of a windowed evaluation map**: model the balanced window as a `product` of
  `degreeLT`'s (finrank trivial), identify the kernel with the geometric window via an injective
  coordinate map (`LinearMap.finrank_range_of_inj`), and pin the range by surjectivity — cleaner than
  building a `LinearEquiv` on the kernel.
- **`degreeLT` window membership `↔` `pdeg` bound**: `SYZ64.mem_degreeLT_of_pdeg_le` (forward) and
  the local `pterm_le_of_mem` (inverse) are the two glue lemmas; `pterm d w i = (w i).degree + d i`.
- **`WithBot ℕ` `ne_bot` extraction pitfall**: `WithBot.ne_bot_iff_exists` gives `↑M = v` with the
  `WithBot.some` coercion; convert to the `Nat.cast` form with `rw [← Nat.cast_withBot]` before using
  `exact_mod_cast` (SYZ63/SYZ64 pattern).
- **Top coefficient of a product**: `coeff_mul_degree_add_degree` + `natDegree_mul`; when the slot is
  strictly below the target both sides vanish (`coeff_eq_zero_of_natDegree_lt`).
