# Issue #466/#505 G123: the triangular moment ladder

Date: 2026-07-10

G121 proved the m = 1 descent identity. G123 proves the whole ladder, welding the G84/G85
slot machinery to the depth-census face for the first time at general marking depth.

## Results (`Frontier/_G123TriangularMomentLadder.lean`, 8 declarations, axiom-clean, 0 sorryAx)

For `matchCountM m (v,w) = #{(e₁,e₂) : (Fin m ↪ Fin r)² | ∀ t, v (e₁ t) = w (e₂ t)}`:

- `card_matchSliceM` / `card_matchSliceM_cube`: at fixed embeddings, the slice bijects
  (coreAt/paddingAt/assemble) onto (common `A`-valued core word) × (rung-`(r−m)` pair).
- `sum_matchCountM_energySet`: `Σ_{eq-sum} matchCountM m = (r)_m² · #A^m · E_{r−m}(A)`.
- `sum_matchCountM_cube`: population analogue `= (r)_m² · #A^m · #A^{2(r−m)}`.
- `ladder_anomaly_transfer` (ℤ): the signed m-moment equals
  `(r)_m² · #A^m · (q·E_{r−m} − #A^{2(r−m)})`.
- `ladder_moment_nonneg`: `≥ 0` for every `m ≤ r`, unconditionally (G95 floor at rung r−m) —
  immune to the (64, 16778497, 5) counterexample.
- `le_commonPart_card_of_matching`: an m-matching forces a common sub-multiset of size m
  (marked values ≤ both bags ≤ their intersection, via nodup-map monotonicity).
- `matchCountM_eq_zero_of_lt_depth`: the m-th moment vanishes on all depths `> r − m`.

## Structural reading

The ladder triangularizes the depth census against the rung hierarchy: row m sees exactly
depths `0..r−m` and is EXACTLY determined by rung `r−m` (identity, not estimate). The entire
rung hierarchy below r therefore acts as an explicit family of positivity/equality
constraints on the rung-r signed depth measure, with weights `(r)_m²·#A^m`. The
fully-disjoint sector is invisible to every row `m ≥ 1` — it alone carries non-descent
information, formally pinning the object the depth-five lanes attack.

Post-counterexample role: since uniform sign laws are dead, exact transfer identities are the
correct instruments — any rung-k result (bound OR counterexample) moves up the ladder with
explicit weights. In particular the (64, 16778497, 5) failure at rung 5 transfers to exact
statements about the weighted rung-6+ censuses of that same subgroup.

## Honest scope

Identities and unconditional inequalities; the fully-disjoint sector is unbounded here (the
wall). CORE remains OPEN.
