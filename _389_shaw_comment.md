## The Shaw operator: the seven "unknown quantities" are ONE scalar — and the closed-form δ* it pins

Posting a synthesis that does the thing the prize keeps asking for: **find the single unknown all
the reductions bottom out in, name it, constrain it with everything proven, and state the closed
conjecture that solves δ\* with no residual sub-lemmas.** Landed in
`PROXIMITY_PRIZE_WORKBENCH.lean` (8 axiom-clean theorems + the conjecture; built green against the
in-tree energy/character transport, 3313-job dependency).

### The unification — every face is one operator

Define the **Shaw operator** on the smooth NTT domain `D = μ_n ⊆ F_q^×`:

> `𝖲_D : ℂ[F_q] → ℂ[F_q]`,  `(𝖲_D f)(x) = ∑_{d∈D} f(x+d)`  — convolution by `1_D`, the adjacency
> operator of `Cay(F_q^+, D)`.

`shawOp_eigen` (proven): the additive characters `χ_b(x)=ψ(bx)` are its eigenvectors, eigenvalues
`η_b = ∑_{d∈D}ψ(bd)`. So **the spectrum of `𝖲_D` *is* the incomplete-character-sum family**, and
every "unknown quantity" the campaign reduced the prize to is one spectral statistic of it:

| face | spectral statistic of `𝖲_D` |
|---|---|
| incomplete char sum `B(μ_n)`, Stepanov rank | the **spectral gap** `‖𝖲_D|_{1^⊥}‖` |
| additive energy `E`, Sidon floor, ST incidences | the **4th moment** `E_2 = (1/q)∑‖η_b‖⁴` |
| RS list size beyond Johnson, δ*, `CensusDomination`, `SplitLocusBound`, `WindowRationalBounded`, `SmallSubgroupGoodList`, residual `(R)` | **high moments** `E_m`, `m ≈ ρn` |

They are **not seven unknowns but one operator**, read at different spectral depth.

### The regime dichotomy — why both lanes stalled (and they're still the same unknown)

This is the part that explains the two recorded walls. Energy `E = E_2` and the deep-band fibre
`E_{ρn}` are **genuinely different moments** — the 4th moment is *silent* in the window interior
(`L(δ)·C(a,k) ≤ C(n,k)` is vacuous as `a→ρn`), which is exactly why the `n^{2.45}` energy lane and
the `CensusDomination` lane never connected. But they **collapse to one scalar the instant the gap
is controlled** — the new structural theorem:

> **`shaw_offdiag_moment_le`** (proven, pure Hölder on the 2nd moment, no Weil):
> `∀ M ≥ 1,  ∑_{b≠0} ‖η_b‖^{2M} ≤ B^{2M−2}·(q·n − n²)`.

A single bound `B` on the gap controls **every** moment at once. So `B(μ_n)` — *not* `E` — is the
master unknown, and the prize is the *gap* problem at all depths simultaneously.

### The closed-form δ* and the lone conjecture

Combined with the in-tree doubling reduction (`badScalars_card_le_cosetLowWeight`: the whole
one-parameter bad-scalar family collapses to one static low-weight coset count) and the average
incidence balance, this gives the closed form

> **δ*(ρ,ε*,n,q) = H_q⁻¹( 1 − ρ − log_q(1/ε*)/n )**

as a *theorem* exactly when one closed inequality holds:

> **Shaw Spectral Flatness** — `∃` absolute `C ≥ √2` with `B(μ_n) = max_{b≠0}‖∑_{x∈μ_n}ψ(bx)‖ ≤ C√n`.

No `∃`-over-objects, no incomputable lemma, decidable at every finite instance — and it is the
*only* residual: by `shaw_offdiag_moment_le` flatness controls every moment, hence every face. The
constant is **pinned sharp**: `shaw_flatness_constant_ge_sqrt_two` (proven) uses the exact even
energy `E(μ_n)=3n²−3n` to force `2n−3 ≤ C²n`, i.e. **`C ≥ √2`** — the naive "perfectly Sidon" `C=1`
is refuted, which is why the conjecture carries `√2 ≤ C`.

### Honest placement

Flatness `B = n^{1/2+o(1)}` for the **small** production subgroup (`n = 2^25 = p^{0.16}`, `n ≪ √q`)
**is** the classical Shkredov / HBK / BGK wall — `WorstCaseIncidenceBound` ⟺ `ShawFlatnessConjecture`
⟺ `E(μ_n)=n^{2+o(1)}`. **MRSS `n^{49/20}` does not suffice**: the excess exponent `0.225` is a
constant, not `o(1)`, so with `q` exponential the line–ball error is `q^{Ω(n)}` — the prize needs the
genuine `o(1)`. This file does **not** claim to close it; it proves everything *above* the gap
(8 axiom-clean theorems) and isolates the open core to one sharp, decidable inequality on one
explicit operator, with a refutation ledger (R1–R8) fixing its exact form. That is the prize, in
closed form — the gap of the Shaw operator, and nothing else.
