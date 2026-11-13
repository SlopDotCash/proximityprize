# A BEYOND-JOHNSON bound for the LIST (#444) — CORRECTED: NOT a δ\* (MCA) floor

*Status: ⚠️ RETRACTED as a δ\* floor — CONFIRMED NO-GO by independent adversarial workflow
(`wf_2d83e328`, 5 agents). The argument bounds the **lacunary count = the LIST** (codewords near a
fixed word, linear `k=2`) for `η > η_crit`; it does NOT bound δ\* (the MCA / far-line incidence).
The axiom-clean kernel `Sweep_A44` (steps-2–4 arithmetic) is correct; the δ\*-floor CONCLUSION is
withdrawn. Workflow synthesis: "NO-GO. Survives only as a beyond-Johnson LIST/energy bound, which
re-confirms the wall rather than breaching it." Precise failure = **Step 1** (incidence ≠ lacunary
count; the binding far-line incidence for a monomial pencil is degenerate 0/q, and the true binding
object is the **c=1, p-DEPENDENT** count — the worst word is a non-symmetric binomial over budget =
Sweep_A10's `o_1=0` wall). The route is also **vacuous exactly at δ\*** (`η_δ* < η_crit`,
`Sweep_A43`). The two "survives" attackers only audited the internal arithmetic of steps 2–4 (the
LIST mechanism), never step 1 or the δ\*-location.*

## §0. ⚠️ The correction (why this is NOT a δ\* floor)

On review against the campaign's far-line proxy (0xSolace: engine `δ*≈17/32≈Johnson` for n=32,
ρ=1/4) and the `Sweep_A42` reunification, three flaws sink the δ\*-floor claim:

1. **List ≠ incidence.** The reunification (`Sweep_A42`) maps **window-LIST members** (codewords
   near a fixed word `x^a+1`) ↔ lacunary subsets. The far-line **MCA incidence** `#bad γ` is a
   *different* object: for a monomial pencil `(x^a, 1)`, the incidence is **degenerate (0 or q)** —
   if any deg-`<k` `g` agrees with `x^a` on `≥s` points, then *every* `γ` is bad via `f=g+γ`. So
   the lacunary count is the LIST, not the incidence. My argument bounds the list, not δ\*.
2. **k=2 only.** `Sweep_A42` is for **linear** codewords (`f=αx+(1−c)`). At prize rates `k=ρn` the
   "incidence = lacunary count with `c=s−k`" identification (my step 1) is **not** established.
3. **B4 is open.** Even a clean beyond-Johnson *list* bound only yields a δ\* (MCA) bound through
   the open `LD ⟹ MCA` collapse (ABF26 §5 = B4). So a list bound is necessary, not sufficient.

Consistency: the engine's far-line proxy `δ*≈17/32≈Johnson` is exactly what one expects if the
*incidence* (not my list object) is the binding object and is NOT bounded beyond Johnson by this
argument. **No contradiction once the objects are kept distinct — and no δ\* floor.**

**What genuinely survives:** (a) `Sweep_A44` — the axiom-clean inequality `η > η_crit ⟹ s^{1/(2η)} < p`
(correct, the positive companion to the η_crit no-go); (b) the statement that the *lacunary count*
(char-0 cosets + char-p defect) is `O(1)` for `η > η_crit` via norm bound + antipodal recursion —
a LIST/energy-side fact, **not a δ\* floor**. This re-confirms the wall from the floor side rather
than breaching it. Honesty contract: the δ\*-floor overreach is retracted, as caught on review.

---

*(Original candidate argument retained below for the record; its CONCLUSION (a δ\*-floor) is
withdrawn per §0 — it is a LIST bound for k=2, consistent with the wall.)*

## Statement

> For explicit 2-power RS (`μ_n`, `n=2^μ`, `p≈n·2^128`), the worst-case far-line incidence is
> `≤ budget = q·ε*` for every radius with gap `η > η_crit`, where
> `η_crit = (log s)/(2 log p) ≈ μ/(2(128+μ)) ≈ 0.09`. Hence
> **`δ* ≥ (1−ρ) − η_crit`, which is `> 1−√ρ` (beyond Johnson) for every prize rate** (`ρ∈{1/2,1/4,1/8,1/16}`),
> with a constant margin `≈ 0.10`.

## The argument

**1. The incidence is the lacunary count (`c = ηn` conditions).** For the binding monomial pencil
`x^a + γ` (general rate `k=ρn`), a bad `γ` corresponds to an agreement set `S` (`|S|=s=(ρ+η)n`)
on which `x^a` is interpolated by a degree-`<k` polynomial. With `a=s`: `x^a − V_S` (`V_S=∏_{x∈S}(X−x)`)
has degree `<k` iff `e₁(S)=⋯=e_{s−k}(S)=0`, i.e. (Newton) the **first `c=s−k=ηn` power sums of `S`
vanish mod `p`**. So `#bad γ = #{size-s subsets S : p_1(S)=⋯=p_c(S)=0 mod p}` (the lacunary count).

**2. No antipodal-free-core defect for `η > η_crit`.** Decompose `S = (antipodal pairs) ⊔ C`, `C`
antipodal-free. The **odd** power sums of the pairs vanish automatically, so the odd conditions fall
on `C`: `p_j(C)≡0 mod p` for the `⌈c/2⌉` odd `j ≤ c`. Each odd `j` is a Galois automorphism of
`ℚ(ζ_n)` (units mod `2^μ` are the odds), so `σ_j(β_C)≡0 mod 𝔭_j` for `⌈c/2⌉` **distinct** primes
above `p` (split completely, `p≡1 mod n`), giving `p^{⌈c/2⌉} ∣ N(β_C)`. The **cyclotomic trace
identity** `Tr(β_C·β̄_C)=φ(n)·|C|` (verified for antipodal-free `C`) + AM-GM gives
`|N(β_C)| ≤ |C|^{φ(n)/2}`. Combining: `p^{c/2} ≤ |C|^{n/4}`, i.e. `p ≤ |C|^{n/(2c)} = |C|^{1/(2η)}`.
A defect needs `|C| ≥ p^{2η}`; but `η > η_crit = (log s)/(2 log p)` ⟹ `p^{2η} > s ≥ |C|` — **contradiction.
No free-core defect exists.**

**3. The antipodal recursion is clean.** With no free core, every surviving `S` is *fully*
antipodal-balanced ⟹ its squared half is a size-`s/2` subset of `μ_{n/2}` with the *even* conditions
(= first `c/2` power sums) vanishing. This is the **same problem on `μ_{n/2}`, same `(ρ,δ,η)`**
(verified: `ρ,δ,η` are all preserved under the squaring descent — `Sweep_A40/A42`). At level `ℓ`
the gap-ratio `c_ℓ/N_ℓ = η` is **preserved**, while `η_crit(ℓ) = (log(s/2^ℓ))/(2 log p)` only
**decreases** (prime fixed, `s` halves). So `η > η_crit(0) ≥ η_crit(ℓ)` ⟹ no free core at any level.
The recursion bottoms out at the **char-0 coset count** = deep `μ_τ`-coset unions, `= C(n/τ, s/τ)`
with `τ ≈ ηn`, `= poly(1/η) = O(1)` (constant in `n`).

**4. The floor.** For `η > η_crit`, `#bad γ = O(1) ≪ budget = q·ε* = n`. So every radius with
`η > η_crit` is "good" ⟹ `δ* ≥ (1−ρ) − η_crit`. Since `η_crit < √ρ−ρ` for every prize rate, this is
**beyond Johnson**.

## What this is and is NOT

- **IS:** an unconditional lower bound `δ* ≥ capacity − η_crit`, strictly beyond Johnson by a
  constant margin (`≈0.10`), reducing only to Galois splitting + the cyclotomic trace identity.
- **IS NOT:** the exact δ\* (the prize). My η_crit no-go (`Sweep_A43`) shows the *exact* `η_δ*` is
  `Θ(1/log n) < η_crit` (deeper), so `δ* ∈ [capacity − η_crit, capacity − Θ(1/log n)]` — a band.
  Pinning the exact value inside the band is the open wall (the norm bound is vacuous for `η < η_crit`).

## Consistency checks (passed)

- ρ=1/4: Johnson `δ_J=0.5`; `η_crit≈0.091`; floor `δ ≥ 0.75−0.091 = 0.659 > 0.5`. Beyond Johnson ✓.
- ρ=1/16: Johnson `0.75`; floor `0.9375−0.086 = 0.8515 > 0.75`. Beyond Johnson ✓.
- Trace identity `Tr(β·β̄)=M·|T|` verified exactly for antipodal-free `T` (n=32, p=97/449).
- Consistent with `Sweep_A43` (η_δ* < η_crit) and Sweep_A10 ("exact δ* q-dependent").

## The risk points (why this is CANDIDATE, not claimed)

- **R-a:** is the worst direction really the monomial pencil `x^a+γ` (so the incidence = the
  lacunary count)? The dossier's dilation-symmetry argument says yes (monomial extremal), but the
  general-word reduction should be re-verified.
- **R-b:** does "antipodal-free-core killed + balanced recurses" capture *all* defects, or can a
  defect be neither (partial antipodal structure that evades both)? The decomposition
  `S = pairs ⊔ free-core` is exhaustive, and the odd conditions fall entirely on the free core —
  but the interaction of even conditions across the split needs a careful re-check.
- **R-c:** novelty vs eprint 2026/858 (RVW Threshold-Halving, "unconditional above Johnson") —
  this floor may overlap; honest comparison needed once 858 is readable.

If R-a/R-b survive independent scrutiny, this is a genuine beyond-Johnson unconditional floor —
the first positive movement on the open floor direction this campaign has produced. It is offered
for refutation, not asserted as closed.
