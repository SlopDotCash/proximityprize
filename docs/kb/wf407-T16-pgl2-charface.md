# WF407 T16-pgl2 — PGL₂ torus-normalizer does NOT transfer a DOF-cut to the char-sum face

**Date:** 2026-06-14 · **Thread:** 407-T16 (HD reduces Gauss-phase DOF to n/4) · **Verdict: WALLED**
(onto W4 / Paley-graph-BGK; the avenue is EXHAUSTED — no new lever).

## The question

The MCA bad event carries the full PGL₂/Möbius symmetry — rotation `x↦c·x`
(`MCAEquivariance.mcaEvent_rs_rotate`) + inversion `x↦−1/x`
(`MCAMobius.mcaEvent_rs_inversion`, eigendecomposition included). On the MCA face the
inversion is the **degree-weighted twist** `(T u)(i) = (dom i)^{k−1}·u(σ i)`, an isometry of
the bad event; with reflection it cuts the Gauss-phase DOF by `×4` to the integer-pinned
"Katz floor" `n/4` (the exact-relation set, already EXHAUSTED: census 407-T16, DISPROOF_LOG
O133/A5 — torus-normalizer spike law `{x↦c/x}∪{x↦−x}`).

**The real (item-3) question:** does this PGL₂ action transfer to the **char-sum face** — the
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
   - **negation** `b↦−b` is the **IDENTITY on cosets** (`cls(−1)=0` since `−1∈μ_n`, n even),
     carrying only the conjugate fold `η_{−b}=conj(η_b)` — the **×2** giving `~m/2` orbits;
   - **inversion** `b↦b⁻¹` acts as the group inversion `x↦−x` on `ℤ/m` (`inv=neg_x=True`
     everywhere) — the ONLY nontrivial coset symmetry the normalizer adds.
   - BUT `‖η_{b⁻¹}‖ ≠ ‖η_b‖` (measured `inv_modgap` 1.6–8.8, vs `neg_modgap` ~1e-15):
     inversion is **NOT a modulus relation**, so the `x↦−x` coset fold does **NOT** reduce
     `max_b‖η_b‖`. Orbit count under `⟨neg,inv⟩` on cosets = `⌈(m+gcd(2,m))/2⌉ ≈ m/2`
     (verified `predOrb=actOrb` every case), i.e. DOF cut is **×2, NOT ×4**.

3. **No concentration either.** Geometric-mean-with-inverse `√(‖η_b‖·‖η_{b⁻¹}‖) < B` at the
   spike (5/6 cases; the lone tie is a small-q coincidence). `‖η_{1/bmax}‖` is *tiny* at the
   spike (0.005–0.5·√n vs B≈2·√n): the inverse of the worst coset is generically NOT worst, so
   inversion supplies no averaged/independence balancing bound.

## Conclusion

The `×4 → n/4` Katz floor is a **degree-weighted (k≥2) MCA/relation-face** phenomenon. On the
**linear char-sum face** the normalizer transfers ONLY as the negation `×2` (already exploited:
`B` is a max over `~m/2` periods — the source of the `log(q/n)` not `log q` scale). The
inversion generator degenerates to a non-isometric `ℤ/m` involution that is **neither a relation
nor a concentration input**. The avenue is **walled onto W4** — the residual is the Gauss-period
HOUSE over the `~m/2` independent periods = the Paley Graph Conjecture / BGK wall, **unchanged**.

## Artifacts

- `scripts/probes/wf407_T16-pgl2_charface.py` — full period vector + 4-map normalizer action.
- `scripts/probes/wf407_T16-pgl2_orbitlaw.py` — `inv=x↦−x` on `ℤ/m`, orbit law `~m/2`.
- `scripts/probes/wf407_T16-pgl2_concentration.py` — GM<B + domain-inversion trivial reindex.
- `Research/ProximityPrize/Frontier/WF407_T16PGL2CharFace.lean` — axiom-clean
  brick (`eta_image_inv_invariant`, `image_inv_self_of_invClosed`, `eta_dominv_eq`): the L2 fact
  that domain-inversion leaves `η` invariant = *why* inversion adds nothing on the char-sum face.

## Cross-refs

DISPROOF_LOG O133 (M3 torus-normalizer spike law), `PencilNormalizerBand.lean` (MCA-face spike
law proven), `MCAMobiusInversion.lean` (the twist + eigendecomposition), 407-T16 census row.
Does NOT touch the relation-hunt (item 2: confirmed exhausted at Katz floor n/4, not redone).
