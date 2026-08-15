# δ* control-plane correction: issue #509 is closed

**Date:** 2026-08-14
**Branch:** `research/proximity-prize`
**Maintenance tracker:** #506

The branch-local campaign guide still describes issue #509 as the live successor CORE issue. That
state is stale.

Issue #509 closed under its honest-closure criterion after G101 landed. The axiom-clean result
reduces the orbit-class mass-profile face to the kernel/deviation normal form and proves
`dcEnergyBound_iff_kernel_deviation_le`; the profile formulation is therefore an exact equivalent
face of `DCEnergyBound`, not a separate weaker route.

This does **not** prove the production δ* inequality. The production CORE remains open and is tracked
by issue #466. In particular:

- #509 is historical/closed, not the live CORE tracker;
- its closure is an equivalence/no-go result, not a production pin;
- #466 remains the canonical open prize tracker;
- #506 remains the state/census/documentation maintenance tracker;
- #507 remains the final completion/audit gate.

This note exists to prevent agents from spending work against a closed control-plane target while the
branch-local guide is being refreshed. It makes no new mathematical claim beyond the verified #509
closure record.

## Provenance

The #509 closure record states that G101 landed the following axiom-clean results:

- `card_orbitClassSet_mul`;
- `sum_pairwise_sub_sq`;
- `centeredShadowMass_deviation_normalForm`;
- `dcEnergyBound_iff_kernel_deviation_le`.

The recorded axiom set is limited to `propext`, `Classical.choice`, and `Quot.sound`.
