# Retained F101 Lean witness validation — 2026-09-05

The [first retention batch](probe-retention-semantic-batch-2026-09-05.md)
verified a finite polynomial census and explicitly left the retained Lean witness
unchecked. This follow-up checks that witness directly. Alongside the
[BGK batch](probe-retention-bgk-batch-2026-09-05.md), the reports now cover sixteen
of the original 92 artifacts without direct filename references.

`_nubs_research/F101Band3BoundaryWitness.lean` compiles successfully under the
repository's pinned Lean 4.30.0-rc2 environment. Its six explicit axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`; neither `sorryAx`
nor a custom axiom appears. The source and dependency-manifest hashes, validation
environment head, command, exit code, and complete audit output are recorded in
the [execution record](probe-retention-f101-lean-2026-09-05.json).

The concrete statement concerns the degree-less-than-four polynomial code on
eight evaluation points over `ZMod 101`. The four certificates establish
`mcaEvent` at distance parameter `1/4` for scalars `0`, `1`, `2`, and `33`.
Each certificate supplies a six-coordinate agreement witness and excludes a
joint explanation on that particular coordinate set. The aggregate theorems
exhibit a four-element set of such scalars and prove a lower bound of four on
the corresponding finite filter count.

This validates the recorded finite four-scalar witness, not every point in the
196-point census, a classification of all bad scalars, or a production-scale
proximity-gap bound. The source remains in the retained research directory;
this check does not add it to the production library or its default CI targets.

To replay from a checkout with the pinned dependencies available:

```sh
lake env lean _nubs_research/F101Band3BoundaryWitness.lean
```

The audit used the unchanged source bytes from the retention branch and the
private, warmed validation environment at `fae76897ba7250a966a06d7e4a5627f38f46398f`.
The dependency manifest is byte-identical between those checkouts. The module's
own six `#print axioms` commands provide the displayed dependency evidence.
