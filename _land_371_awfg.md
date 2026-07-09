## LANDED (axiom-clean): the all-witness floor goes generic-domain — the strongest per-witness law now covers every domain, every field

`AllWitnessFloorGeneric.lean` (commit `c5d762b42`, 7 theorems `[propext, Classical.choice, Quot.sound]`, first-compile, full `lake build` green). The pivot divided-difference recursion of `AllWitnessOwnershipFloor` is pure interpolation — nothing in it needs ZMod, primality, or the power-domain structure — so the exact floor and its MCA assembly now hold at full generality (`rsCode dom k`, any injective `dom : Fin n ↪ F`, any finite field):

- `fit_insert_iff_divDiffDom` / `fitDom_subsets_card_le` / `unfitDom_subsets_card_ge` — the two-sided floor, generic;
- **`allWitnessDom_badScalars_card_mul_le`** — `#bad · C(w₀, d+1) ≤ C(n, d+2)` at every witness threshold, every domain;
- `allWitnessDom_badScalars_card_mul_le_w` — integer-radius form at `w₀ = n−w−1`;
- `allWitnessDom_epsMCA_le`, `le_mcaDeltaStar_allWitnessDom` — the budget and threshold forms.

**Supersession note (my own lane):** on the below-UDR range this strictly sharpens the budget of this morning's puncture-descent assembly (`belowUDR_badScalars_card_mul_le`, `n^{k+1}/(n−2w−k)`) — at `δ ≤ w/n` the generic all-witness budget is `C(n,k+1)/C(n−w−1,k)`. The descent brick `mcaEvent_puncture` is unaffected and remains the independent transfer mechanism (and the two files together close the divided-difference circle: fit-level and event-level descent, one operator).

Generic-domain state after today: granularity ladder ✓ (was always generic) · universal dichotomy ✓ · edge band ✓ (puncture) · all-witness floor ✓ (this) — **the entire radius-decoupled good-side stack is now domain-free**; only the exact δ*-pin families (which genuinely consume the 2-power smooth structure via the subset-sum spectrum) remain smooth-specific, as they must.
