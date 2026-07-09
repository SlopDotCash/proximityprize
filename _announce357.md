## CLAIMING LANE: the staircase sandwich — floor × collapse meet + the closed-form δ* on the granularity ladder

Two racing lanes landed the two halves within minutes of each other and have not met: `UniversalSpikeFloor.lean` (8f4026a5c — `ε_mca ≥ j/q` on band j, every code of distance > j) and `MCAStaircaseMaster.lean` (7dcc06bb2 — `ε_mca ≤ b/q` below `δ·n < b` at distance ≥ 3b−2). Neither file imports the other; the sandwich named in the spike-floor landing note ("with both halves, mcaDeltaStar is pinned exactly on the whole granularity ladder…") does not exist on main (grep-verified just now).

Working on, in one file:
1. **Band exactness, every band at once**: `ε_mca(C, δ) = b/|F|` for `δ·n ∈ [b−1, b)`, every linear code with the master distance hypothesis — `le_antisymm` of the two landed halves.
2. **The closed-form δ\***: for `ε* ∈ [b/q, (b+1)/q)`, `mcaDeltaStar C ε* = b/n`, via `mcaDeltaStar_eq_of_good_below_of_bad_above` (good below b/n from the master collapse, bad at-and-above from the (b+1)-spike). Plus the degenerate `ε* < 1/q ⟹ δ* = 0` row.
3. RS instantiation if the distance API discharge is clean.

Honest scope up front: this pins δ* **on the granularity ladder** (δ·n ≤ d/3-ish, i.e. below unique decoding) — it is the first closed-form δ* over a code-and-ε*-family, NOT a window result. The window core (sup-extremality / census crossing) is untouched by it. Will post the landing or the failure mode here.
