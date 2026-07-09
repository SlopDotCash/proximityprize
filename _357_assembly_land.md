## ✅ Verification complete + THE SIMPLE-STRATUM CONVERSE ASSEMBLY IS LIVE (`simple_wideCircuit_classification`, fix b6ccb63fd, 7/7 axiom-clean)

**Main-health follow-up to the tree-share note:** the swept `ChordConverseWrapper.lean` had 26 compile errors (all one mechanism: the `![...]`-vector index permutations do not reduce under `simp only` at `fin_cases` literals — match-defs do; plus a dead trailing `ring` and one sign flip). **Fixed forward at b6ccb63fd**; the full wrapper now compiles with every theorem axiom-clean. Lesson recorded: match-defs, not `![...]`, for case-bashed `Fin n` functions. (`KKH26RegimeSplit` is the sibling fork's verified weld; its dep cone builds clean per their session.)

**What is now on main, end-to-end (the converse arc, 5 files, all `[propext, Classical.choice, Quot.sound]`):**

> **`simple_wideCircuit_classification`** — for every `m ≥ 2`: every **balanced**, **multiplicity-free**, `Distinct6` exponent-triple over `μ_{2^m}` is
> **horizontal** (all products ≡) ∨ **vertical** (all three pairs antipodal) ∨ a **two-plus-antipodal chord-law triple** (one of the three labelings, with the difference-class equality + chord congruence in `ZMod (2^m)`) ∨ **one of the eight second-layer seed systems** —
> uniformly in the scale, every disjunct in closed congruence form.

Chain: `balanced_trichotomy` (no partial collapses) → antipodality case-split → `chord_form_of_balanced_antipodal₁/₂/₃` (the core's 96-case tree + the swap-transport: odd relabelings act as an index involution ∘ global `+h`-translation, so injectivity/closure transport directly) → `secondLayer_form_of_balanced_no_antipodal` (the 813-kill generated tree). **The wide-circuit classification of `Γ_n` is now a machine-checked theorem in both directions on the simple stratum** — the supply families (chord law, seeds I/II, doubling) are provably the *only* shapes.

**Collision stratum (increment 4) — the chart is complete and clean:**
- one-quartet `(2,2,1⁸)`: 5466 structures — 5148 killed, 270 chord-side, 48 second-layer, **0 open**;
- two-quartet `(2⁴,1⁴)`: 15750 structures — 15026 killed, 724 chord-side, **0 second-layer, 0 open** (`probe_collision_multiquartet.py`);
- `(2⁶)` is contained in the two-quartet bases by row-monotonicity (superset constraints preserve derivability); a direct pass + the chord-form completion of the "chord-side" routes (the collided analogue of the chord tree, certificates in hand) are the remaining emission inputs.

The remaining Lean for the FULL converse (all balanced configs): the collision-branch emission via the same generator — bounded, certificate-driven, no new mathematics. After that, the census closed forms (`n(n−4)²/8` etc.) sit on a complete two-sided classification.

**The converse lane's ledger this session: 5 axiom-clean theorem files landed** (trichotomy · chord core · second-layer core (generated) · wrapper+assembly · the compile repair), 6 probes, 1 Lean-emitting generator, and the closing-audit's item 2 reduced from "specified blueprint" to **one bounded emission from done certificates**.
