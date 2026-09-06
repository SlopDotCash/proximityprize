# wf407 / T400-05-defect — the e₂=0 mod-q defect is carrier-finite & O(n)-imaged per q, walled at worst-case-q (2026-06-14)

Thread **T400-05-defect** (#407 prize). Drives the "Θ(n²) e₂=0 count IS the mod-q defect, cheap at
tiny n" actionable (400-T05/T06) to a **verdict: WALLED** — onto the recognized NVM / ideal-SVP /
Paley equidistribution wall — with a sharp new controllability result on the way.

Builds on prior A09 work (`deltastar-407-e2zero-modq-defect.md`,
`issue400-e2zero-singles-decomposition…`, `issue400-smax-law-mu-minus-1…`). This note adds the
**carrier-norm spectrum**, the **saturation-vs-genuine pivot**, and the **per-q image bound**, then
states the wall precisely.

Artifacts (EXACT enumeration, no sampling):
- `scripts/probes/wf407_T400-05-defect_norm_spectrum.py` — carrier-norm spectrum + carrier-prime
  density/finiteness + worst-case-q amplification + norm growth.
- `scripts/probes/wf407_T400-05-defect_saturation.py` — the saturation-vs-genuine-structure pivot.
- `Research/ProximityPrize/Frontier/WF407_T400_05_defect.lean` — axiom-clean
  carrier-prime finiteness (`carrierPrimes_finite`, `carrierPrimes_subset_Icc`).

## 1. Reproduced: the q-spread IS the mod-q defect (the actionable's premise)

Confirmed exactly. For `n=32, w=4` (`N(char0)=224`) the F_q counts over the first 10 primes
`q≡1 mod 32` are `{96,160,192,224}`, i.e. defect `{−128,−64,−32,0}` — the "160/192/224 at n=32"
the actionable cited, a genuinely q-dependent `k_D` fingerprint (NOT a constant offset). Two-signed:
**DROP** (char-0 e₁ collide mod q) + **RISE** (halo carriers: `e₂(S)≠0` char-0 but `=0 mod q`).
Carrier-onset law `S` is a carrier mod q ⟺ `q | N(e₂(S))`, `N(α)=Res(Φ_n,α)`, holds (prior A09).

## 2. NEW — the carrier norms sit structurally BELOW the archimedean ceiling

The archimedean keystone (`CyclotomicNormDefectThreshold`) gives `|N(e₂(S))| ≤ C(w,2)^{φ(n)}` (α a
signed sum of `C(w,2)` roots of unity). The **realized max** is far below it:

| n | w | φ(n) | log₂(max\|N\|) | log₂(ceiling C(w,2)^φ) | ratio |
|---|---|---|---|---|---|
| 16 | 4 | 8 | 10.17 | 20.68 (=6^8) | **0.492** |
| 16 | 6 | 8 | 12.00 | 31.26 (=15^8) | **0.384** |
| 32 | 4 | 16 | 20.35 | 41.36 (=6^16) | **0.492** |

So the C067 synthesis claim "N_max(2r)=(2r)^{φ(n)} TIGHT" holds only for the *generic* extremizer
`α=c·ζ^e` (single term, coeff = 2r) — **NOT** for the `e₂(S)` carriers, which are genuine
distinct-root ±1 sums of *bounded ℓ¹ mass*. The e₂ defect carriers are **structurally special**,
sitting ~half-way (in log) up to the ceiling. (Consistent with C026: e₂'s relation has bounded
explicit degree / ℓ¹ mass independent of r.)

## 3. NEW — the per-q defect IMAGE is O(n), not q: the saturation pivot

The alarming small-prime signal `N(F_q) = q−1` (RISE fills the residue field, seen at n=32,w=6 for
q∈{97,…,577}) is a **pure pigeonhole artifact**: while #candidate-sets ≫ q the count is pinned at
q−1 by the field size, *not* by structure. Escaping saturation (`wf407…_saturation.py`, n=16,w=6,
q up to 3217, #candidate=8008) reveals the **genuine** image:

```
   q=17 :  16 (=q-1)  SATURATED artifact
   q=97 :  32         genuine  (= 2·n)
   q=113:  48         genuine  (= 3·n)   <- the worst genuine q in range
   q=193..1601 (carriers): 16 (= n) each
   q≳1700 : 0 for almost all primes        <- CLEAN, defect dies
```

Two decisive facts:
1. **The genuine per-q image is quantized in units of `n`** — the values are exactly
   `{n, 2n, 3n} = {16,32,48}`, matching the lacunary-rigidity quantization
   (`#bad ≡ 0 mod n/gcd(t,n)`, DISPROOF_LOG 2026-06-13) and the `s_max=μ−1=3` staircase. The
   worst genuine image is `3n = O(n)`, NOT `q`. **The count never fills the field once saturation
   is escaped.**
2. **The carrier-prime set is THIN and dies out**: by q~1700 almost every prime `q≡1 mod 16` is
   clean (defect 0). The carriers are a sparse, finite set (next-to-no carriers above the largest
   norm divisor).

## 4. NEW (Lean, axiom-clean) — carrier-prime finiteness = controllability at fixed (n,w)

`WF407_T400_05_defect.lean` proves (audit `[propext, Classical.choice, Quot.sound]`):
- `carrierPrime_le_bound` : `N≠0, |N|≤B, q∣N  ⟹  q ≤ B` (the norm value form).
- `carrierPrimes_finite` : over a **finite** seed family `α : ι→ℤ` (nonzero, `|α i|≤B`), the set
  `{q : ∃ i, q∣α i}` is **finite** (injects into `Icc 1 B`).
- `carrierPrimes_subset_Icc` : explicit enclosure `⊆ Icc 1 (C(w,2)^{φ(n)})`.

This is the rigorous form of "the carrier-prime set is finite, bounded by max\|N\|" — **the e₂=0
defect is fully controllable at any FIXED (n,w)**.

## 5. The wall (why this does NOT close the prize)

Controllability at fixed `(n,w)` does **NOT** survive the **worst-case-over-q** the grand
challenge demands. The adversary picks the field. The ceiling `B=C(w,2)^{φ(n)}` is astronomically
`> q≈n·2^128` in the prize regime (`φ(n)=2^31`), so there always EXISTS a prime
`q | N(e₂(S))` for the largest realizable carrier norm — and at that adversarial q the defect turns
on. The thread's `t=2` / `w=k+2` direction is exactly the **near-capacity ceiling object**
(DISPROOF_LOG: e₂ at t=2 is the upper bracket `δ* ≤ prizeDeltaStar`, its blow-up CONFIRMS δ* lies
below this band, it is not itself the floor wall). The residual lever is the **magnitude /
distribution of `N(e₂(S))` over window sets** = the cyclotomic-norm collision
`q|N(α)` every #407 lane bottoms out in:

- = the additive-energy CRUX char-p transfer (face 3 of the open core, `Hab25JohnsonPackageSupply`
  ↔ `GaussPeriodMomentBound`);
- = the NVM / fully-split ideal-SVP gap (`arklib-bchks-conj112-reduction`,
  `arklib-407-largesieve-avgq-refuted`: bad primes = `q|N(α)`);
- = the generalized-Paley / BGK equidistribution wall.

**No char-0→F_p transferable certificate of the floor exists at list scale** (DISPROOF_LOG
2026-06-13 height no-go). The e₂=0 count made the defect concrete and cheap — and showed it is
O(n)-imaged and carrier-thin at fixed (n,w) — but the worst-case-q control is unchanged: the same
NVM/ideal-SVP/Paley wall.

## Verdict

**WALLED.** The Θ(n²) e₂=0 count IS a direct, concrete, cheap measurement of the `k_D` mod-q
defect (premise confirmed). NEW: (a) carriers sit structurally below the generic norm ceiling
(ratio 0.38–0.49); (b) the genuine per-q image is O(n) (quantized in units of n, max `3n` in range),
NOT q — the `q−1` saturation was a small-prime artifact; (c) the carrier-prime set is finite &
thin, Lean-proven controllable at fixed (n,w). The prize wall = worst-case-over-q magnitude of
`N(e₂(S))` = the recognized NVM / fully-split ideal-SVP / generalized-Paley equidistribution wall.
No closure.

| axis | score | note |
|---|---|---|
| novelty | 7 | norm-below-ceiling + O(n) per-q image (saturation pivot) + Lean carrier-finiteness are new |
| insight | 8 | settles "predictable/bounded vs structured-prime explosion": bounded O(n) per q, thin carriers, controllable at fixed (n,w); wall localized to worst-case-q norm magnitude |
| proximity | 7 | samples k_D at the count level, calibrates the worst-case-q lever, isolates the exact open residual |
| feasibility | 5 | fixed-(n,w) side closed (Lean); worst-case-q magnitude is the open NVM/ideal-SVP wall |

Cross-refs: `deltastar-407-e2zero-modq-defect.md`, `issue400-e2zero-singles-decomposition…`,
`issue400-smax-law-mu-minus-1…`, `arklib-407-largesieve-avgq-refuted`,
`arklib-bchks-conj112-reduction`, DISPROOF_LOG 2026-06-13 (lacunary small-gap + height no-go).
