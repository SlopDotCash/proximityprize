**THE CUBIC ORCHARD IDENTITY — an EXACT sub-Johnson list size, proven (3ecaa2b18)**

Direct attack on the exact sub-Johnson list-size question at its first slice (`k=2`, agreement `a=3`; strictly sub-Johnson once `n > 9`). New module `ProximityGap/CubicOrchardIdentity.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`:

**`cubic_list_eq_zeroSum`** — for the word `w = x³` on **every** domain `dom : Fin n ↪ F`:

```
#{c ∈ rsCode(dom,2) : |agreeSet(c,w)| ≥ 3}  =  #{T ⊆ dom : |T|=3, Σ T = 0}
```

Mechanism (also proven as standalone lemmas `cubic_collinear_of_sum_zero` / `sum_zero_of_cubic_collinear`): three cubic graph points `(a,a³),(b,b³),(c,c³)` are collinear **iff `a+b+c = 0`** — the slope identity `(a³−b³)/(a−b) = a²+ab+b²` cancels to `(a−c)(a+b+c) = 0`. And no line meets the graph 4 times (two zero-sum triples sharing a pair force equal third points), so listed lines have agreement exactly 3 and the list is in bijection with zero-sum triples.

Consequences:
- **On smooth domains the sub-Johnson list size of `x³` is an exact, closed-form-computable object**: the subgroup zero-sum triple count, a pure character-sum quantity. Probe (`scripts/probes/probe_cubic_orchard_identity.py`, pre-registered): identity verified bit-exactly at `(q,n) = (29,14), (31,15), (41,20), (37,18)` → lists `14, 20, 20, 24`.
- **General cubics sweep the fibers**: `c₃x³+c₂x²+…` has list = `#{T : Σ T = −c₂/c₃}`, so the cubic family's exact extremum is `max_s` of the triple-sum fiber distribution (probe: best fibers `14, 20, 29, 24` at the four instances).
- This is the finite-field **orchard problem**: over ℝ, Green–Tao's `⌊n(n−3)/6⌋+1` maximum is attained exactly by such cubics.

**Honest negative (probe, deep hill-climb)**: over `F_q` cubics are **NOT** globally extremal — measured global maxima `21 > 14` at `(29,14)` and `25 > 20` at `(31,15)` strictly exceed the best cubic fiber. Real-plane Sylvester–Gallai rigidity does not transfer. So the exact answer at this slice is now pinned between the **best cubic fiber** (constructive lower bound, exactly computable on smooth domains) and the **pair bound `⌊n(n−1)/6⌋`** (each listed line burns 3 of the `C(n,2)` pairs; e.g. `25 ∈ [20, 35]` at `(31,15)`). The open extremal core = the `F_q` orchard number for distinct-abscissa point sets; my earlier "matches the global max" reading at `(31,15)` was an under-converged hill-climb — corrected here.

Combined with the deep-band supply theorem (`E·(k+m+1) ≤ 2n·C(2k+m,k+m)`, every rate), the charter statement now has: linear supply on all deep bands + an exact per-word law at the first shallow slice.
