# WF407 T16-pgl2 — PGL₂ torus-normalizer does NOT transfer a DOF-cut to the char-sum face

**Date:** 2026-06-14 · **Thread:** 407-T16 (HD reduces Gauss-phase DOF to n/4) · **Verdict: WALLED**
(onto W4 / Paley-graph-BGK; the avenue is EXHAUSTED — no new lever).

## The question

The MCA bad event is invariant under rotation `x↦c·x` with `c` in the domain subgroup
(`MCAEquivariance.mcaEvent_rs_rotate`) and inversion `x↦−1/x`
(`MCAMobius.mcaEvent_rs_inversion`, eigendecomposition included). These generate the dihedral
torus-normalizer action preserving the evaluation domain `μ_n`, not all of PGL₂ (a general
Möbius map need not preserve `μ_n`; no full PGL₂ invariance is proved). On the MCA face the
inversion is the **degree-weighted twist** `(T u)(i) = (dom i)^{k−1}·u(σ i)`, an isometry of
the bad event; with reflection it cuts the Gauss-phase DOF by `×4` to the integer-pinned
"Katz floor" `n/4` (the exact-relation set, already EXHAUSTED: census 407-T16, DISPROOF_LOG
O133/A5 — torus-normalizer spike law `{x↦c/x}∪{x↦−x}`).

**The real (item-3) question:** does this torus-normalizer action transfer to the **char-sum face** — the
Gauss periods `η_b = Σ_{x∈μ_n} ψ(b·x)` (Paley-graph `Cay(F_q,μ_n)` eigenvalues), where
`B = max_{b≠0}‖η_b‖` lives — and give a **non-relation concentration** input?

## Verdict: NO. Exact-numerics record (exhaustive, no sampling)

Probes: `scripts/probes/wf407_T16-pgl2_charface.py`, `_orbitlaw.py`, `_concentration.py`.
Cases: n∈{8,16,32}, primes p with n|(p−1), incl. m=(p−1)/n up to 258.

1. **Inversion on the DOMAIN = trivial reindex.** `μ_n` is inversion-, negation-, and
   `−1/x`-closed (all flags `1`). So `x↦−1/x` maps `μ_n` onto `μ_n` *as a set*; the char sum
   over the inverted index set is the **same** `η_b` (probe `dominv==eta` gap ~1e-15,
   `sameSet=True`). The MCA twist's degree weight `x^{k−1}` **vanishes at k=1** (the linear
   char-sum face), so the twist degenerates to this trivial reindex — no relation, no DOF cut.

2. **Inversion on the FREQUENCY = a non-isometric `ℤ/m` involution.** `b↦η_b` factors through
   `F_q^×/μ_n ≅ ℤ/m` (`m=(q−1)/n` periods; `GaussPeriodCosetReduction.eta_image_card_mul_le`).
   On `ℤ/m`:
   - **negation** `b↦−b` is the **IDENTITY on cosets** (`cls(−1)=0` since `−1∈μ_n`, n even):
     `b` and `−b` are the same coset, so `η_{−b}=η_b`, and with `η_{−b}=conj(η_b)` every period
     is real. Conjugation gives **no** further halving after the subgroup quotient: there are `m`
     coset periods, not `m/2`;
   - **inversion** `b↦b⁻¹` acts as the group inversion `x↦−x` on `ℤ/m` (`inv=neg_x=True`
     everywhere) — the ONLY nontrivial coset symmetry the normalizer adds.
   - BUT `‖η_{b⁻¹}‖ ≠ ‖η_b‖` (measured `inv_modgap` 1.6–8.8, vs `neg_modgap` ~1e-15):
     inversion is **NOT a modulus relation**, so the `x↦−x` coset fold does **NOT** reduce
     `max_b‖η_b‖`. Orbit count under `⟨neg,inv⟩` on cosets = `(m+gcd(2,m))/2 ≈ m/2`
     (verified `predOrb=actOrb` every case); these are orbits of the non-isometric inversion,
     so they do **not** reduce the number of periods over which `B` is a maximum (still `m`).

3. **No concentration either.** Geometric-mean-with-inverse `√(‖η_b‖·‖η_{b⁻¹}‖) < B` at the
   spike (5/6 cases; the lone tie is a small-q coincidence). `‖η_{1/bmax}‖` is *tiny* at the
   spike (0.005–0.5·√n vs B≈2·√n): in the probed instances the inverse of the worst coset was
   not worst, so inversion supplied no averaged balancing bound there. This is finite inversion
   data, not a general no-concentration theorem.

## Conclusion

The `×4 → n/4` Katz floor is a **degree-weighted (k≥2) MCA/relation-face** phenomenon. On the
**linear char-sum face** the torus normalizer gives no modulus-preserving fold beyond the
subgroup quotient itself: `B` is a max over the `m = (q−1)/n` coset periods (the source of the
`log(q/n)` rather than `log q` scale); negation/conjugation adds no second halving because `−1 ∈ μ_n`.
The inversion generator degenerates to a non-isometric `ℤ/m` involution that is not a modulus
relation and, in the probed data, not a balancing input. In this sense the avenue is **walled onto
W4** — the residual is the Gauss-period HOUSE over the `m` coset periods = the Paley Graph
Conjecture / BGK wall, **unchanged**.

## Artifacts

- `scripts/probes/wf407_T16-pgl2_charface.py` — full period vector + 4-map normalizer action.
- `scripts/probes/wf407_T16-pgl2_orbitlaw.py` — `inv=x↦−x` on `ℤ/m`, orbit law `~m/2`.
- `scripts/probes/wf407_T16-pgl2_concentration.py` — GM<B + domain-inversion trivial reindex.
- `Research/ProximityPrize/Frontier/WF407_T16PGL2CharFace.lean` — axiom-clean
  brick (`eta_inv_reindex`, `image_inv_eq_self_of_inv_mem`, `eta_dominv_eq_of_inv_mem`, plus the
  compatibility wrappers `eta_image_inv_invariant`, `image_inv_self_of_invClosed`,
  `eta_dominv_eq` that keep a redundant `0 ∉ G` argument): the L2 fact
  that domain-inversion leaves `η` invariant = *why* inversion adds nothing on the char-sum face.

## Cross-refs

DISPROOF_LOG O133 (M3 torus-normalizer spike law), `PencilNormalizerBand.lean` (MCA-face spike
law proven), `MCAMobiusInversion.lean` (the twist + eigendecomposition), 407-T16 census row.
Does NOT touch the relation-hunt (item 2: confirmed exhausted at Katz floor n/4, not redone).
