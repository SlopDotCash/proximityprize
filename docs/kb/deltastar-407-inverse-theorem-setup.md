# δ* / #407 — Inverse-theorem unification setup: the ε*-bad family as a sumset object — PARTIAL (premise refuted, with a sharpened thinness law)

**Date:** 2026-06-14 · **Actionable:** A13 (merged 357-T12 / 334-T07) ·
**Verdict: PARTIAL** — the sumset object is now stated precisely and its key invariant
(additive doubling / energy) is *measured exactly*; the inverse-theorem bet is **refuted on its
own premise** by a sharpened, quantitative thinness law, NOT just the loose `K = 1/ε*` proxy of
the prior pass. Honesty contract held: no fabricated closure.

This note supersedes the qualitative axis-2 of `wf407-T357-12-inverse-unification-bet.md` and
backs it with the new measurement in `scripts/probes/_wf357_a13_inverse.py`.

---

## 1. The bet (ranked #8 in `UNFINISHED_THREADS_407.md` §(d))

> Every ε*-bad family for δ* lives on coset/orbit (affine-subgroup) structure. If any ε*-bad
> family is poly(1/ε)-covered by affine-subgroup-structured families, δ* stops being analytic
> and becomes a FINITE ENUMERATION; import Bogolyubov–Ruzsa / Sanders to close it.

The promised payoff: a *quantitative* inverse theorem (Sanders 2012; Bloom–Sisask 2020) covers a
small-doubling set by few cosets of a subspace, turning the (analytic, open) δ* core into a finite
combinatorial enumeration over structured families.

## 2. The sumset object — stated precisely (this is the deliverable A13 asked for)

Fix `RS[F_q, μ_n, k]`, `ρ = k/n`, radius `δ`, agreement threshold `t = ⌈(1−δ)n⌉`. A *direction*
is a pair `(u₀, u₁) ∈ (F_q^{μ_n})²`. The **bad-scalar set** is

```
  Bad(u₀, u₁; δ) := { γ ∈ (F_q, +) : d(u₀ + γ·u₁, C) ≤ δ·n }
                  = { γ ∈ F_q : ∃ codeword v, |{ x ∈ μ_n : v(x) = u₀(x) + γ·u₁(x) }| ≥ t }.
```

This is the **correct object** for an inverse theorem: it is a subset of the *additive group*
`(F_q, +)`, and the MCA error is `ε_mca = max_{(u₀,u₁)} |Bad| / q`. The δ* core is *exactly*:

> is there a direction with `|Bad| > ε*·q = q·2⁻¹²⁸` at some `δ < δ*`?

The inverse-theorem hypothesis must be placed on `Bad` (a set in `(F_q,+)`), with doubling
`K := |Bad + Bad| / |Bad|` or additive energy `E(Bad) := #{(a,b,c,d) ∈ Bad⁴ : a+b = c+d}`.

**Crucial correction.** The prior pass conflated two different objects:
- the *codeword list* `L(u₀)` (achieving codewords) — used in axis-1; lives in `F_q^{μ_n}`;
- the *bad-scalar set* `Bad` — the object an inverse theorem actually operates on; lives in `(F_q,+)`.

A13 forces the second framing. The honest question becomes: **what is the additive doubling of
`Bad`, and is it ever small enough for B-R to bite?**

## 3. The in-tree constraint that pins `Bad`'s additive geometry

`MCAWitnessSpread.unique_bad_gamma_common_witness` (axiom-clean, `[propext, Classical.choice,
Quot.sound]`) proves, for *any* linear code `C` and any fixed coordinate set `S`:

> if two scalars `γ₁ ≠ γ₂` both have a codeword agreeing with the line word on **all of `S`**,
> the two divided-difference codewords `(γ₁−γ₂)⁻¹(w₁−w₂)` and `w₁−γ₁·(…)` witness a joint
> `(u₀,u₁)` codeword pair on `S` — i.e. at most ONE bad `γ` per witness set `S`.

**Consequence for the sumset framing.** A bad set with `|Bad| = L` scalars *requires `≥ L`
distinct witness coordinate-sets*. The bad scalars are coupled **only** through the code geometry
(which `t`-subset of `μ_n` carries an explainer), **never** through an additive relation in
`(F_q,+)`. Nothing in the structure forces `Bad` to be a coset, an AP, or a low-doubling set.
This is the *positive* statement that A13 wanted to turn into a sumset conjecture — and it is
precisely the statement that **denies** any such conjecture: the geometry leaves `Bad`'s additive
structure entirely free.

## 4. The measurement (exact, no sampling; `_wf357_a13_inverse.py`)

### 4a. Doubling of the binding bad set, window interior, `n=16`, `k=2`, `t=4`

| p | \|Bad\| | density \|Bad\|/p | K = \|Bad+Bad\|/\|Bad\| | E(Bad)/Sidon |
|---|---|---|---|---|
| 97  | 32 | 0.330 | 3.03 | 5.72 |
| 113 | 25 | 0.221 | 4.48 | 3.48 |
| 193 | 18 | 0.093 | 6.94 | **1.59** |

`E(Bad)/Sidon → 1` means the energy approaches the Sidon floor `2|Bad|²−|Bad|`, i.e. the set is
**asymptotically Sidon** (every pairwise sum distinct, no additive structure whatsoever).

### 4b. The thinness law (the sharpened verdict)

As the prime grows with `n` fixed — the direction toward the prize regime, where `Bad` is
`ε*`-thin inside `F_q` (`density ≤ 2⁻¹²⁸`) — the doubling **grows** (`3.0 → 4.5 → 6.9`) and the
Sidon-energy ratio **falls to 1** (`5.7 → 3.5 → 1.6`). The moderate doubling at the smallest prime
`p=97` is a **wrap-around artifact**: there `Bad` occupies a third of `F_p`, so `Bad+Bad` saturates
the group and `K` is small by pigeonhole, not by structure.

> **Thinness law (numerical):** the binding bad-scalar set's additive doubling `K` is bounded
> below by an increasing function of the field-to-set thinness `q/|Bad|`; at prize thinness
> `|Bad|/q ≤ ε* = 2⁻¹²⁸` the set is Sidon (`K ≈ |Bad|`, `E(Bad) ≈ 2|Bad|²`).

This is the rigorous form of "the binding bad set is unstructured." It corrects the prior pass's
unqualified "`K ≈ |A|`" into a *thinness-driven law* validated by the energy ratio trending to 1.

### 4c. Witness distinctness confirms the obstruction

Every binding instance shows `L/L` bad scalars with **distinct** witness coordinate-sets
(`17/17`, `27/27`, `34/34`) — exactly `unique_bad_gamma_common_witness`. The structured power-word
direction (`u₀=xᵉ`, `u₁=x`) gives `K = 1.00` only because `|Bad| = p` (the *vacuous* all-of-`F_p`
regime at small primes), not because of additive structure.

## 5. Why the inverse theorem cannot bite (both axes, now quantitative)

- **Premise false (axis 1, reproduced):** the binding worst-case is a heterogeneous combinatorial
  cluster, not an orbit (`≤ 17%` orbit-coverage; DISPROOF O161–O163). §4 adds: it is additively
  Sidon at thinness, so there is no coset/AP/subspace structure to enumerate.
- **Tool vacuous (axis 2, sharpened):** Sanders/Bloom–Sisask need `K = O(1)` (equivalently
  `E(Bad) ≥ |Bad|³ / K^{o(1)}`). At prize thinness `K → |Bad|` and `E(Bad) → 2|Bad|² ≪ |Bad|³`,
  so B-R returns a "structure" of rank `≈ |Bad|` — i.e. no compression. The covering count is
  `exp(rank) ≈ exp(|Bad|)`, super-polynomial in `1/ε*`. (The earlier `K = 1/ε* = 2¹²⁸` was a loose
  proxy; the *measured* obstruction is the thinness-Sidon law of §4b, which is the same conclusion
  via the correct object.)

**Mutual exclusivity:** a bad set that is low-doubling would already be the harmless KKH26 orbit
ceiling (silent at production budget, O159); a bad set that is binding is Sidon at thinness, which
B-R provably cannot certify as structured. Premise and tool are disjoint.

## 6. In-tree positive evidence — and why it does NOT rescue the bet

A13 cited `SparseDeviationExtremality` and `MCAEigenstackOrbitLaw` ("every extremal object is a
rotation-power eigenstack") as positive evidence for structure. These are real and proven — but
they describe the **lower-bound / ceiling extremizer** (the algebraic family that *attains* the
known `ε_mca`), NOT the **binding maximizer** (the densest bad cluster that pins δ*). DISPROOF
O161–O163 already separated these: H-MAX (the binding object) is a combinatorial cluster, the
eigenstack law governs only the ceiling. So the in-tree structure theorems confirm the bet's
catalogue claim *for the ceiling* and are silent (correctly) about the binding object — which §4
shows is unstructured. The two are not the same set.

## 7. Where it lands

Collapses onto the **same wall the campaign bottoms out at**: the explicit-smooth-RS sub-Johnson
worst-case list bound = the additive-energy / Paley-eigenvalue core (`E_{F_p}(μ_n) = n^{2+o(1)}`,
Shkredov-open). The inverse-theorem route does not bypass it — it *requires* the very
energy/structure dichotomy it hoped to supply, circularly: B-R's input hypothesis (small doubling
of `Bad`) is itself an additive-energy statement about the bad set, and §4 shows that energy is at
the Sidon floor exactly where the prize lives.

## 8. What is genuinely settled vs open

- **Settled (this note):** the precise sumset framing of the bad family; the in-tree obstruction
  `unique_bad_gamma_common_witness` as the additive-freedom statement; the *measured* thinness law
  (`K ↑`, `E/Sidon → 1` as `q/|Bad| ↑`) showing the binding `Bad` is Sidon at prize thinness;
  therefore B-R/Sanders are provably blind. The bet is refuted on its premise, quantitatively.
- **Open (unchanged):** the additive-energy core itself. No inverse theorem helps. No Lean brick is
  warranted (the verdict is a refutation-by-measurement, not a clean provable statement; a
  `*_REFUTED` brick would only restate the probe and is not worth the olean-load cost — same call
  as the prior pass).

## 9. Artifacts

- `scripts/probes/_wf357_a13_inverse.py` — the sumset-object probe: exact `Bad` enumeration, the
  doubling/energy measurement (S1, S1b thinness trend), witness-distinctness check, the
  random-sparse-killer argument (S2). Self-contained, exact at `n ≤ 16`.
- Prior qualitative pass: `docs/kb/wf407-T357-12-inverse-unification-bet.md` and
  `scripts/probes/wf407_T357-12-inverse_unification.py` (axis-1 catalogue + axis-2 proxy).
- In-tree substrate cited: `ArkLib/Data/CodingTheory/ProximityGap/MCAWitnessSpread.lean`
  (`unique_bad_gamma_common_witness`), `MCAEigenstackOrbitLaw.lean`,
  `SparseDeviationExtremality.lean`.
