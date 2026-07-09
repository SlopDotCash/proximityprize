# #407 wf407-w2/D2-gspec — the genuine-E₂-defect g-spectrum is NOT an O(1) lever (REFUTED)

**Status:** thread D2-gspec (T09 follow-up) driven to a `refuted` verdict by machine-checked exact
enumeration (n=8,16,32,64,128,256) plus an axiom-clean Lean brick for the algebraic core. The hoped
O(1) Galois-coset localization of the genuine defect count does NOT exist; the g-spectrum grows
linearly in n and each per-g dilate incidence is the full n, so the localized sum recovers Θ(n²) =
the additive-energy excess (wall W2). Honesty contract held: no closure, no bound below the wall.
Author: #407 wf407-w2/D2-gspec lane, 2026-06-14.

## The question

Wave-1 T09 observed that the product-unit `g = (x₁·x₂)/(y₁·y₂)` of a **genuine** E₂ defect
(`x₁+x₂ ≡ y₁+y₂ mod p`, `{x₁,x₂}≠{y₁,y₂}`, non-antipodal) lands in only **4–6 clustered values of
μ_n** at n=16,32. The hope: if `|g-spectrum| = O(1)` independent of n, the genuine count
re-localizes to a **bounded** union `Σ_{g∈Gset} |μ_n ∩ g·μ_n|` over a fixed small g-set — a route
*around* the additive-energy wall.

(Note: genuine non-antipodal defects only exist where the char-p energy **excess** `E₂^(p)−E₂^(0)`
is positive, i.e. SUB-prize β, p below the r=2 onset 4^{n/2}. At prize β the excess→0 and there are
no genuine defects. So the g-spectrum is a sub-prize object; we test whether its mechanism, where it
exists, could beat the wall.)

## The decisive measurements (exact, full enumeration)

`scripts/probes/wf407w2_D2-gspec_growth_and_lever.py` and `..._linear_law.py`, β=2.0:

| n | p | excess | #genuine | \|G\| | \|G\|/n | all D(g)=n? | lever=Σ\|μ∩g·μ\| | \|G\|·n | lever/excess |
|---|---|--------|----------|-------|---------|-------------|------------------|---------|--------------|
| 16  | 257   | 192   | 32   | 4  | 0.250 | True | 64    | 64    | 0.333 |
| 32  | 1153  | 768   | 96   | 6  | 0.188 | True | 192   | 192   | 0.250 |
| 64  | 4289  | 1536  | 192  | 6  | 0.094 | True | 384   | 384   | 0.250 |
| 128 | 17921 | 15360 | 1920 | 28 | 0.219 | True | 3584  | 3584  | 0.233 |
| 256 | 65537 | 73728 | 9728 | 60 | 0.234 | True | 15360 | 15360 | 0.208 |

(multiple primes per n confirm: at n=256, |G|∈{50,52,60}; the values move with the prime but stay
Θ(n).)

## Three independent reasons it is NOT a lever

1. **|G| grows linearly in n** (least-squares `|G| ≈ 0.22·n`), NOT O(1). The "4–6 values" at
   n=16,32 was a small-n artifact — at those n the spectrum happened to be a single Galois orbit
   (#galois-orbits = 1–2). By n=128 it spreads to 3–6 orbits, |G|=12–28; at n=256, |G|=50–60.

2. **G ⊆ μ_n at every n** (measured `all D(g)=n? True` throughout). Since g ∈ μ_n is a *group
   element* and μ_n is a *group*, `g·μ_n = μ_n`, so the dilate incidence `|μ_n ∩ g·μ_n| = |μ_n| = n`
   for EVERY g. The "localized incidence" carries **no localization** — each term is the full n.

3. **Hence lever = |G|·n = Θ(n²)** (verified exactly: `lever == |G|·n` every row), a constant
   fraction (≈1/4) of the full excess. `genuine = Θ(lever) = Θ(n²) = Θ(excess)` (`excess/genuine ≈
   8`, constant). The g-localization just re-indexes the energy excess by its dominant dilate
   frequencies, all inside μ_n — exactly the Cauchy–Schwarz floor. **It recovers the wall, it does
   not beat it.**

## Lean brick (axiom-clean)

`Frontier/WF407W2_D2gspec.lean` formalizes the algebraic core of reason (2):
- `Subgroup.smul_self`: `g ∈ H ⟹ g • (H:Set) = H` (a subgroup dilated by its own element is itself).
- `selfDilate_inter_eq` / `selfDilate_card_eq`: the self-dilate incidence `|H ∩ g·H| = |H|`.
- `localizedSum_eq_card_mul_card`: `Σ_{g∈Gset} |s ∩ g·s| = |Gset|·|s|` when every g self-stabilizes
  s. With `G ⊆ μ_n`, `|G|=Θ(n)`, `|s|=n` this is `Θ(n²)`.

Axiom audit: `[propext, Classical.choice, Quot.sound]` (the smul lemmas even cleaner, no
Classical.choice). Validated `scripts/pg-iterate.sh` EXIT 0 (35s).

## Verdict: `refuted`

The O(1) g-localization lever does not exist. Both pillars fail: |G| = Θ(n) (not O(1)), AND each
dilate incidence = n (trivial, since G ⊆ μ_n is a group acting on a group). The localized count is
Θ(n²) = the additive-energy excess. This **confirms the T09 walled verdict from a new angle**: even
the most optimistic reading (bound the count by a fixed g-set) returns the W2 additive-energy wall.

## Artifacts

- `scripts/probes/wf407w2_D2-gspec_genuine_g_spectrum.py` — reproduction + orbit structure n≤64
- `scripts/probes/wf407w2_D2-gspec_growth_and_lever.py` — growth to n=256, per-g incidence = n
- `scripts/probes/wf407w2_D2-gspec_linear_law.py` — |G|=Θ(n) fit + lever=|G|·n identity
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/WF407W2_D2gspec.lean` — axiom-clean core

Cross-refs: `wf407-T09-leak-crossparity-antipodal-verdict.md` (the parent walled verdict),
`WF407_T09Leak.lean` (reflection engine), EnergyDilationReduction (`E = card·incidence`),
AdditiveEnergyFermat. The whole T09 family — reflection, antipodal split, count identity, and now
g-spectrum — bottoms out at W2 (the √n additive-energy loss) / Pan–Xu ideal-SVP.
