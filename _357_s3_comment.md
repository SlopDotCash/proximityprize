# S3 LANDED — the eigenstack orbit law: the flat numerator IS one orbit (commit 1ea1629ed)

S3 of the nine-hypothesis queue is decided and landed. Two S3 lanes raced this hour; the sibling's `MCAEquivariance.lean` (the five `mcaEvent` symmetry laws + Pr-level forms + `epsMCA_eq_iSup_subtype_of_reps` + the RS-rotation instance) was adopted as the engine — no fork — and the orbit law landed as layer 2 on top of it: `MCAEigenstackOrbitLaw.lean`, 6 audited theorems, axiom-clean.

## The law

**`mcaEvent_eigenstack_iff`.** If `C` is stable under a domain permutation `σ` and the stack is a *σ-eigenstack* — `u₀∘σ = a•u₀ + b•u₁`, `u₁∘σ = c•u₁` (`a,c ≠ 0`) — its bad-scalar set is invariant under the affine map `T(γ) = a⁻¹b + γ·(a⁻¹c)`. With the orbit arithmetic (`orderOf_le/dvd_card_of_mul_mem`, `orderOf_le/dvd_badScalarSet_card_of_eigenstack`): the bad count is `ε + (#orbits)·ord(a⁻¹c)`, `ε ∈ {0,1}` — **field-independent orbit arithmetic**. Plus a `badScalarSet` Finset-level counting API, and the demo: at `RS[F₅,F₅*,2]` **one** certificate + the orbit law re-derives `ε_mca(C,1/4) ≥ 4/5` (R1 needed four).

## The probe verdicts (`probe_s3_eigenstack_orbit_law.py`, exit 0, pre-registered)

* v1 (pure-frequency extremality) **falsified at the intermediate rungs**, instructively — DISPROOF_LOG entry. The repair is the law's own spectral theory and it is **confirmed**: rotation powers σᵗ have multi-dimensional syndrome eigenspaces, and σᵗ-eigenstacks attain every rung: the (13,12,6) exact profile `1, 2, 3, 12, 13` is **orbit arithmetic** — fixed point / antipodal pairs {γ,−γ} via σ⁶ / ω-triples via σ⁴ / one full order-12 orbit / orbit + fixed point.
* **The flat numerator IS one orbit**: the m=9 plateau value 12 = one full order-12 orbit (attainer `(j₀,j₁)=(9,8)`, ε=0), reproduced by the same construction at p=37 and p=61 where the orbit is a **proper coset** of F*. Field-independence explained, mechanism identified. (Consistent with — and the formal backbone for — the O145/O147 census discoveries of the parallel lanes: "each prime carries exactly one rotation orbit of halo, size n" / "take-over flat-n = ONE rotation orbit".)
* **Honest caveat** tempering N1: at (13,6,3) m=5 only 6 of 300 maximizers are genuinely σ³-eigen — eigenstacks *attain* every tested rung max but do not *exhaust* the maximizers at intermediate rungs. Structured extremality = attainment, not uniqueness.

## Structural consequence

The [KKH26] near-capacity bad stack `(X^{rm}, X^{(r−1)m})` is *itself* a rotation eigenstack (eigenratio `g^{−m}` of order s), and its λ-family is G-equivariant by inspection (`λ_{g'T} = g'·λ_T`). **Every extremal object this campaign has touched — toy plateau maximizers, intermediate-rung attainers, the KKH26 ceiling family — is one object class: rotation-power eigenstacks**, differing only in (power, #orbits). The δ*-relevant question sharpens to: *how many T-orbits can be simultaneously bad at radius δ* — 1 at the plateau, exponential near capacity, the window is the transition. The splitting-locus form (when does `x^{j₀} + γx^{j₁} − β` have ≥ m roots in the domain subgroup) is the finite question this reduces to.

R2 verdict (fold transport) next — probe already decided it (covariance, not shrinkage); Lean brick in verification.
