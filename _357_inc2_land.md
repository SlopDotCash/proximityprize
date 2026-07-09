## Converse increment 2 LANDED: THE CHORD CONVERSE CORE (`ChordConverseCore.lean`, 1349a4abb, axiom-clean)

The antipodal branch of the wide-circuit classification is now a **theorem** — the supply direction's converse on its stratum:

> **`chord_of_antipodal_partner`** — over any commutative ring with a half-period `h` (`h + h = 0`, `h ≠ 0`, doubling kernel `{0, h}` — instantiated by `ZMod (2^m)` with `h = 2^(m−1)` via the landed `double_eq_zero_iff`): if the shifted 12-exponent stack of a `Distinct6` triple with pair 2 antipodal (pairs 1, 3 not antipodal, products pairwise distinct) is **injective** (multiplicity-free) and **closed under `+h`** (balance), then the configuration is a **two-plus-antipodal chord-law triple**: `A₁ − B₁ = A₃ − B₃ ∧ 2A₂ = A₁ + B₃`, or the mirror orientation.

Proof = the canonical-matching case tree, fully transcribed: the partner of index 4 must be 6, 7, or 9 (eight instant kills onto `Distinct6`/genericity/second-antipodal/injectivity); partner 9 dies in a three-node sub-tree (the `2(B₁−A₁) = 0` node kill + two doubling-branch kills whose `h`-arms land on injectivity — the multiplicity-canonicity device); partners 6/7 force the two chord orientations after ONE more partner choice (the conclusion needs only two live relations — the remaining four indices never have to be walked). **96 cases, every kill one `linear_combination`.**

**Probe-driven transcription** (`probe_antipodal_branch_tree.py`, pushed): the antipodal-branch residual tree enumerated exhaustively with kill-certificate search — 105 leaves, 103 killed (D6/GEN/second-ANTIP/MULT + 4 doubling-branch kills), exactly 2 survivors = the chord systems P1/P2. The Lean file is its transcription with every certificate re-derived by hand; the file compiled on the second attempt (3 sign flips).

**Where the converse program now stands:**
| piece | status |
|---|---|
| trichotomy (no partial collapse; horizontal ∨ vertical ∨ generic) | ✅ landed (c26a6a550) |
| generic + one antipodal ⟹ chord form | ✅ **this** (core; ZMod wrapper + labelings in flight) |
| generic + no antipodal ⟹ second-layer systems | tree charted: **10395 pairings, 10387 killed, exactly the 8 second-layer systems survive** (`probe_noantipodal_branch_tree.py`, certificates per leaf, kill-depth profile {1: 5670, 2: 2625, 3: 1800, 4: 228, 5: 52, 6: 12}); Lean transcription next — by **generator** (the certificate data mechanically emits the case tree, the industrial method) |
| collision profiles | queued (increment 4) |

When the no-antipodal branch lands, the multiplicity-free exactness converse closes: every simple wide circuit of `Γ_n` is horizontal, vertical, chord-law, or one of the eight second-layer systems — at every smooth scale, uniformly.
