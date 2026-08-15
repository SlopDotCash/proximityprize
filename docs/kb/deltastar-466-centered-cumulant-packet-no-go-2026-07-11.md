# Center-first partition cumulants are signed, not positive packet counts (2026-07-11)

Issue #466 lane: direct characteristic-p packet/cumulant repair after the uncentered
Möbius-Mann connected-packet no-go.

## Result

The center-first repair is refuted at the same ordinary partition-cumulant layer.  Subtracting the
uniform finite-field main term before applying the distinguished-block cumulant recurrence still
produces signed Ursell/fluctuation coefficients, not literal nonnegative packet counts.

For `H = μ_8 ⊂ F_41`, the exact raw ordered zero-sum counts through depth four are

```text
M_1 = 0,  M_2 = 8,  M_3 = 0,  M_4 = 200.
```

After centering by `M^c_m = M_m - 8^m / 41`,

```text
M^c_1 = -8/41,
M^c_2 = 264/41,
M^c_3 = -512/41,
M^c_4 = 4104/41.
```

Using the ordinary partition recurrence

```text
K_1 = M_1
K_2 = M_2 - K_1 M_1
K_3 = M_3 - K_1 M_2 - 2 K_2 M_1
K_4 = M_4 - K_1 M_3 - 3 K_2 M_2 - 3 K_3 M_1,
```

the centered connected coefficient is

```text
K^c_4 = -87878392 / 2825761 < 0.
```

So no theorem identifying these center-first connected coefficients with a positive packet census
can be true.  A viable packet route must define a new canonical positive minimal-zero-sum
packetization with controlled overlap; ordinary partition cumulants, centered or uncentered, are
not that object.

## Formal payload

Lean kernel:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G146CenteredCumulantPacketNoGo.lean`
- Main theorem: `mu8_F41_centered_connectedK4_negative`
- Counter-shape theorem: `not_forall_centered_connectedK4_nonnegative`

Executable check:

- `scripts/probes/probe_466_centered_cumulant_packet_no_go.py`

## Honest scope

This closes only the ordinary center-first partition-cumulant repair.  It does not refute the more
ambitious survivor: a genuinely positive canonical minimal-zero-sum packet decomposition.  It says
that such a decomposition must be new structure, not the Rota partition-lattice cumulant transform
applied after DC subtraction.
