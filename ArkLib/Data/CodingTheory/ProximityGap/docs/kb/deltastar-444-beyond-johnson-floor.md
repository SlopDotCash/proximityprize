# A BEYOND-JOHNSON unconditional floor for δ\* (#444) — CANDIDATE, under scrutiny

*Status: CANDIDATE POSITIVE RESULT. The argument survives the scrutiny applied here; it reduces
only to two standard cyclotomic theorems (Galois prime-splitting + the cyclotomic trace identity),
both genuine. NOT the full prize (it gives a lower bound on δ\*, not the exact value). Marked for
independent verification before any closure claim. Honesty contract: this is offered as a careful
candidate, explicitly inviting refutation.*

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
