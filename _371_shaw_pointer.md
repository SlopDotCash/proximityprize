## Cross-link: the Shaw operator unifies this lane's residual with #389's

Posted in detail on #389 (comment 4699557996). Short version for the #371 record: the WB-window
residual `WindowRationalBounded`, `SplitLocusBound`, and `CensusDomination` are **not distinct
unknowns** — they are *high spectral moments* `E_m` (`m ≈ ρn`) of one explicit object, the **Shaw
operator** `𝖲_D = ` convolution-by-`1_D` on `F_q^+` (adjacency of `Cay(F_q^+, μ_n)`), whose spectrum
is the incomplete-character-sum family `{η_b}` (`shawOp_eigen`, axiom-clean).

The new structural theorem `shaw_offdiag_moment_le` (axiom-clean, pure Hölder) shows a **single**
bound on the spectral gap `B(μ_n) = ‖𝖲_D|_{1^⊥}‖` controls *every* moment at once:
`∑_{b≠0}‖η_b‖^{2M} ≤ B^{2M−2}·(qn−n²)`. So the below-UDR window lane and the deep-band census lane
collapse to the **same scalar** — the gap — and the whole MCA threshold is pinned by the closed-form
`δ* = H_q⁻¹(1 − ρ − log_q(1/ε*)/n)` modulo the one decidable inequality `B(μ_n) ≤ √2·√n` (Shaw
Flatness; constant pinned sharp by the `3n²−3n` energy floor). All in `PROXIMITY_PRIZE_WORKBENCH.lean`,
8 axiom-clean theorems + the lone conjecture. The residual is exactly the classical Shkredov gap wall.
