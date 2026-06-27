# Issue #464: permutation-insdel rank transfer gate

Date: 2026-06-26.

Status: **random-domain transfer gate**, not a delta-star proof.

External source: arXiv:2606.22344, "Random Reed--Solomon Codes Correcting Permutations,
Insertions, and Deletions over Polynomial-Size Alphabets" <https://arxiv.org/abs/2606.22344>.

## Thesis

arXiv:2606.22344 is relevant because it improves random Reed-Solomon robustness against
adversarial coordinate permutations followed by insertion/deletion errors over polynomial-size
alphabets.  The method is algebraic-generic: random evaluation points avoid bad rank conditions,
with Schwartz-Zippel style estimates controlling the exceptional set.

For #464, the evaluation domain is not random.  It is the fixed dyadic smooth subgroup `mu_n`.
Therefore the transfer theorem needed by the prize is pointwise:

```text
the smooth domain lies in the generic-good locus,
or every actual smooth-domain extremal configuration is covered by the generic symbolic model.
```

Without one of those two inputs, a random-domain rank theorem is compatible with the smooth domain
being the exceptional point.

## Lean Surface

New file:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D4PermutationInsdelRankTransferGate.lean
```

New declarations:

```lean
smooth_bound_of_generic_locus
generic_bound_does_not_transfer_without_smooth_membership
actual_bound_of_pointwise_model_cover
covered_models_do_not_bound_uncovered_config
```

The positive statements are deliberately minimal.  A generic bound transfers to the smooth domain
if the smooth domain is in the generic locus.  A model/configuration bound transfers if every
actual configuration has a covered symbolic model and the model statistic pointwise dominates the
actual statistic.

The countermodels record the gap:

```text
generic-good domains can all be bounded while the designated smooth domain spikes;
covered symbolic configurations can all be bounded while an uncovered actual configuration spikes.
```

## Verdict

The permutation-insdel/random-RS rank theorem is useful adjacent technology and a good source of
rank/SZ templates.  It does not close the plain-RS floor unless it is upgraded from random-domain
genericity to a pointwise certificate for the fixed dyadic subgroup or its actual extremal
configuration class.

That missing upgrade is exactly where the known smooth-domain non-genericity lives, so this route
currently reduces to a named transfer obligation rather than proving the delta-star floor.
