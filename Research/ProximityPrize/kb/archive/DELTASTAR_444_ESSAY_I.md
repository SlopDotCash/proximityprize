# Pinning δ\* in the Prize Regime — Essay I (generation pass)

*#444 δ\* assault. Status: GENERATION (bold/exploratory). Honesty contract holds: nothing
below is claimed proven; every direction is tagged with its reduction risk. This essay is
deliberately maximal and will be shredded in Essay II and rebuilt no-larp in Essay III.*

---

## 0. The wall, stated once, exactly

Let `n = 2^μ`, `p ≡ 1 (mod n)` prime, `q = p`, `μ_n ⊊ F_p^×` the order-`n` subgroup,
`m = (p−1)/n = 2^128` the index, prize point `n ≈ 2^30`, `β = log_n p ≈ 4` (the **Burgess
barrier**). The single open core, in its sharpest form:

> **(WALL).** `M(n) := max_{b≢0} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n log m)`, `C = O(1)`.

Equivalent faces (all in-tree, all reducing here): `M(n) = λ₂(Cay(F_q,μ_n))` (generalized
Paley 2nd eigenvalue); `M(n) = house(θ)` where `θ = Σ_{x∈μ_n} ζ_p^x` is a Gauss period of
degree `m`; char-`p` validity of `A_r = E_r − n^{2r}/q ≤ (2r−1)‼·n^r` at depth `r ≈ ln q ≈ 89`;
`crossCell·q ≤ 2^r|H|^r` = BCHKS Conj 1.12 (s=1). SOTA is `n^{0.989}` (di Benedetto et al.,
Burgess-barrier-stuck); prize is `n^{0.5}`. **A full half-power gap at the single hardest point.**

**The deepest honest reduction (the GoN/ideal-SVP root, c.4b93ac503 / SparseSupportIdealSVP):**
the char-`p` "anomaly" `A_r − A_r^{char-0}` counts non-trivial `α = Σx_i − Σy_j ∈ ℤ[ζ_n]`,
`x_i,y_j ∈ μ_n`, `α ≠ 0`, `𝔭 | α` (𝔭 the prime above `p`), with all archimedean embeddings
`|σ(α)| ≤ 2r`. This is **short-vector counting in a prime ideal of the 2-power cyclotomic
field `ℚ(ζ_n)`** — exactly the lattice-crypto hardness regime. That is *why* the prize is a
prize: a uniform upper bound on the anomaly is an effective ideal-SVP-counting theorem, which
does not exist as of 2026.

**The four facts that constrain any honest attack** (from the §4 meta-theorem + the route-
elimination sweeps, 79+50+50 conjectures, 0 survivors):

1. **No moment/second-order route.** Every certifiable bound on `max|η_b|` from the symmetric
   constraints `Ση_b^r` is a high-moment estimate; the optimal (joint-LP) certificate is
   ~10–13% tighter than textbook but still caps at the floor's *value* without ever proving
   *char-p validity at depth `r*`*. The Wick **value** `√(2/e)·√(n log m)` lands on the prize
   form (`C≈0.858`) — the value is not the barrier, the **char-p transfer at deep `r*`** is.
2. **No probabilistic-EVT route.** The periods are exchangeable white-noise
   (`Cov = −Var/(m−1)`, distance-independent) → Poisson/integrable level spacing, iid-Gumbel
   tail; no level repulsion, no log-correlation, no free-convolution edge. The half-power gap
   lives **only in the single-peak tail**; the bulk is exactly Gaussian.
3. **The off-BGK floor, if it exists, is NOT a far-line construction.** Over-determined
   far-line incidence is Johnson-locked (`c* = k−1`, `δ* = ½ + 1/n`, exact `n ≤ 28`,
   p-independent). Numerics provably cannot separate Johnson from the floor below `n = 256`.
4. **Any winning method must be simultaneously (a) b-sensitive, (b) deterministic-
   archimedean, (c) genuinely L-infinity (sup, not RMS).**

The discipline of this essay: **only propose directions that are not already theorems in the
DEAD ledger, and for each, name the precise reduction risk.** A direction that "reduces to the
wall" is not a direction — it is the wall wearing a hat.

---

## 1. The three structural SEAMS (where the wall might be bypassed, not climbed)

Every dead route tried to *climb* the wall (bound `M(n)` directly). The campaign's own data
points to three places where the operational δ\* might be pinned **without** the uniform BGK
bound — by exploiting structure the worst-case sup-norm throws away.

**SEAM A — The list, not the sup.** The operational object is the worst-case **window list
size** `L*(ρ,η,n)`, and `M(n) ≤ C√(n log m)` is *necessary-but-insufficient* for pinning δ\*
(it overshoots the budget `q·ε* ~ n` by the index factor `√m = 2^64`,
`PrizeConditionalPinCapstone`). The in-regime data is the strongest positive signal in the
entire campaign: at fixed `(ρ,η)`, on **true 2-power `n`**, `L*` is **constant** (4,4,7 at
n=16,32), matching the window-list law `L* = 2^{Θ(1/η)}` (n-independent at fixed η). A constant
list trivially gives the floor. The proof gap is precise and *combinatorial, not analytic*: the
dyadic squaring identity `e_{2ℓ}(±z) = (−1)^ℓ e_ℓ(z²)`, `e_odd = 0`, gives a self-similar count
**only for antipodal-symmetric agreement sets `S = −S`**; the consecutive-exponent worst word
`x^a+x^{a−1}` (ρ<¼) has list members with **non-symmetric** agreement sets that escape the
recursion. **This seam is OPEN and off-BGK.** It is the centerpiece.

**SEAM B — The protocol restricts the direction family.** The grand-MCA challenge is about
proximity for the *specific* linear combinations a verifier forms. FRI/STIR folds by a **single
random challenge** `γ`: the relevant directions are the 1-parameter pencil `u₀ + γ u₁`, not the
full `(u₀,u₁)` space. The worst-case over a 1-parameter algebraic family can be governed by the
*genus/degree* of that family (Weil for a curve, not a high-dim variety) — and that is exactly
the case the dead ledger flagged "dimension-obstructed past r=2" **for the wrong (full-energy)
object.** A protocol-restricted threshold may be pinnable where the unrestricted sup is not.

**SEAM C — The quotient is also a 2-group.** Every dead Fourier-uncertainty attempt worked on
the **domain** `ℤ_{2^μ}` (the `n`-side). But the periods `{η_b}` are indexed by
`F_p^×/μ_n ≅ ℤ/m = ℤ/2^128` — the **quotient is itself a cyclic 2-group of order `2^128`**.
The Gauss period `θ` of degree `m` lives in the 2-power-degree subfield, and the `η_b` are a
function on a `2^128`-cyclic group. No attempt has used DFT/2-adic uncertainty on the
**quotient** side. This is structurally new.

---

## 2. Twenty-five research directions (closed-target intent; reduction risk named)

*Tags: `[A]/[B]/[C]` = which seam; `OFF-BGK` = does not route through the sup-norm wall;
`RISK:` = the precise way it could still collapse. Directions are chosen to be absent from the
DEAD ledger.*

**R1. Non-symmetric dyadic descent for the consecutive word `[A, OFF-BGK]`.** Build the descent
operator that sends a (possibly non-symmetric) agreement set `S ⊆ μ_n` of `x^a+x^{a−1}` to a
pair of agreement sets in `μ_{n/2}` of a *pair* of descended words, accounting for the `(1+x)`
factor as a boundary term. Target: `L*(n) ≤ L*(n/2) + O(1)` ⟹ `L* = O(log n)` (or constant).
*RISK: the boundary term could grow with `n`; must be measured before trusting.*

**R2. Defect-rank perturbation calculus `[A, OFF-BGK]`.** Write the worst word as a rank-1
perturbation of a monomial: `x^{a−1}(1+x) = x^{a−1} + x^a`. The monomial `x^a` has trivial list
(size `gcd(a,n)`-controlled). Treat `+x^a` as a single rank-1 bump and bound how much the list
can grow under one rank-1 perturbation of the received word. *RISK: a single perturbation might
already unlock the full BGK list; needs the perturbation bound to be `O(1)`, not `O(M)`.*

**R3. Sparse-roots-in-a-subgroup for `u−f` `[A, OFF-BGK]`.** A list member `f` makes `u−f`
vanish on the agreement set `S ⊆ μ_n`. When `f` is itself low-weight, `u−f` is a **sparse**
(lacunary) polynomial; the number of its roots in a multiplicative subgroup is bounded by recent
sparse-root theorems (Bi–Cheng–Gabric, Kelley–Owen, Cheng–Gao). Pin `|S|` from sparsity ⟹ pin
the list. *RISK: the dead ledger has Kelley–Owen (Johnson-capped) and Descartes (undershoots);
the 2026 sparse-root results must beat both AND apply to non-sparse `f` — likely the binding
case is non-sparse `f`, where this is silent.*

**R4. The 1-parameter pencil genus bound `[B]`.** For the FRI fold `u₀+γu₁`, the bad-`γ` set is
`{γ : Σ-agreement ≥ s}`. This is a fibre count of the curve `C_s = {(γ, point-set)}`. Compute
its geometric genus and apply Weil to the **curve** (genus is `O(k²)`, not exponential).
*RISK: the relevant count is a sum over `~m` fibres → reintroduces the outer Gauss-sum sum that
Weil cannot bound (the P4 Carlitz failure mode). Must show the protocol uses ONE fibre family.*

**R5. Quotient-side 2-adic uncertainty on `ℤ/2^128` `[C, OFF-BGK]`.** The periods `b ↦ η_b` are
a function on `ℤ/m`, `m = 2^128`. Its DFT over `ℤ/m` is computable from Jacobi sums. Apply a
Donoho–Stark / Tao cyclic-uncertainty principle on the **quotient** group (a clean 2-power
cyclic group) to force a sup-norm/support trade-off. *RISK: the dead ledger says Tao's
uncertainty is "vacuous for `n=2^μ`" — but that was the DOMAIN side; verify the QUOTIENT side is
not also vacuous (it may be: the period function might be spread on `ℤ/m`).*

**R6. Bombieri–Pila determinant method on the anomaly variety `[OFF-BGK?]`.** Count `α ∈ ℤ[ζ_n]`
with `|σ(α)| ≤ 2r` and `𝔭|α` by the **real-analytic determinant method** (Bombieri–Pila,
Heath-Brown), which bounds integral points on a variety *without RH/Weil* via the analytic rank
of a Wronskian. This is genuinely different from the Deligne/Weil route the ledger eliminated.
*RISK: the determinant method gives polynomial savings in the *height*, but the anomaly box has
height `2r = O(log m)` — the savings may be a constant factor, not the `√m` needed.*

**R7. p-adic linear forms in logarithms (Yu's theorem) `[OFF-BGK]`.** The anomaly needs
`v_𝔭(α) ≥ 1` for small `α = Σx_i − Σy_j`. Yu's effective `p`-adic lower bound on linear forms
in logarithms of algebraic numbers bounds `v_𝔭` of such a difference from above unless `α = 0`.
Sum the bound over representations. *RISK: Yu's constants are astronomically large (ineffective
for `n = 2^30`); likely vacuous at scale — but worth confirming the scaling, as it is genuinely
absent from the ledger.*

**R8. Schinzel–Zassenhaus / Dimitrov spread bound `[OFF-BGK]`.** Dimitrov's 2019 proof gives a
**lower** bound on the house of a non-cyclotomic integer; combined with the *trace* constraint
`Σ η_b = −n` and the *norm* (a Jacobi-sum quantity), a spread inequality could upper-bound the
house. *RISK: Dimitrov's bound is `house ≥ 2^{1/(4m)} ≈ 1`, far too weak to constrain a
`√(n log m)` house; the norm/trace constraints are the moment constraints already eliminated.*

**R9. Catalecticant / apolarity rank for the list `[A]`.** The list of deg-`<k` polys agreeing
with `u` on `≥ s` points is the kernel of a structured catalecticant (Hankel-on-`μ_n`) matrix;
its size is a corank. Bound the corank by the matrix's displacement/border rank. *RISK: this is
the slice-rank object the ledger refuted (`μ_n` cyclic, `d=1`); must find a non-cyclic
displacement structure.*

**R10. Lovász Local Lemma on agreement events `[A, OFF-BGK]`.** Model "codeword `f` is in the
list" as a bad event; the events are sparsely dependent (share few agreement points). An LLL /
container-method bound on the number of simultaneously-realizable list members. *RISK: LLL
bounds *existence*, not *count*; the container method may just recover the energy bound.*

**R11. The cross-cell transfer operator's spectral radius `[reframe of a refuted result]`.** The
dyadic split `M(2n)² = 2M(n)² + crossCell` was refuted as a *contraction* (ratios 1.58–1.76 at
β=4). But the **martingale inflation is exactly `√(2 ln m)`** (CumulantOnsetNoGo). Reframe: the
tower is NOT a contraction but a controlled `√(2 ln 2)`-inflation per level; over `μ = log₂ n`
levels this gives precisely `√(2 ln n)·√(base)` — the target log factor. **Prove the per-level
inflation is `≤ √(2 ln 2)·(1+o(1))`** as an operator-norm bound on the cross-cell map. *RISK:
the per-level inflation may exceed `√(2 ln 2)` (the measured 1.58–1.76 > √2 ≈ 1.41); if so the
tower truly diverges. This is the make-or-break measurement.*

**R12. Protocol-restricted δ\* (the "honest FRI threshold") `[B]`.** Formalize the threshold
δ\*_FRI that the *actual* FRI soundness needs (worst over single-fold pencils with verifier-
chosen but structured `u₀,u₁`), and ask whether it is strictly below the unrestricted δ\*. If
the protocol's worst case avoids the binding antipodal direction, δ\*_FRI may be Johnson-pinnable.
*RISK: ABF26's MCA is defined worst-case over ALL directions; need to check the protocol genuinely
restricts (it may not — soundness amplification quantifies over adversarial `u`).*

**R13. Smooth-number / interval concentration of `μ_n` `[OFF-BGK]`.** `M(n)` is large iff the
coset `bμ_n` concentrates in a short interval mod `p`. Bound the maximal concentration of a
2-power subgroup in an interval via the Korobov–Vinogradov / Bourgain–Garaev sum-product
machinery specialized to 2-power orders. *RISK: this IS the BGK/Burgess wall (concentration ⟺
large char sum); reduction-to-wall unless 2-power order gives a special saving.*

**R14. The "second-largest agreement" (plurality) bound `[A, OFF-BGK]`.** MCA needs not the full
list but the gap between the largest and second-largest agreement. Bound the **second** agreement
directly (it controls whether decoding is unique), which may be `< s` even when the list is
nominally large. *RISK: the second agreement is governed by the same incidence; may not separate.*

**R15. Galois-module structure of the list `[A]`.** The window list is `Gal(F_q/F_p)`-stable
(trivial here, `f=1`) but also stable under the **dilation action** `x ↦ gx` of `μ_n` and under
`x ↦ x²` (squaring). Decompose the list as a `ℤ[ℤ/n]`-module; its length is constrained by the
module's socle. *RISK: dilation orbits are the far-line orbits already counted (Johnson-locked).*

**R16. Effective Chabauty on the fibre product `[B, OFF-BGK?]`.** The bad-`γ` set for a fixed
agreement pattern is a rational-point set on a fibre product of `s` copies of the line minus the
RS graph; effective Chabauty–Kim bounds rational points when the Mordell–Weil rank is small.
*RISK: over `F_p` (not `ℚ`) Chabauty does not apply; need the function-field Chabauty (Kim–Coleman
over `F_p(t)`), whose hypotheses (rank < genus) likely fail for this family.*

**R17. Tropical / Newton-polygon degeneration of the period `[OFF-BGK?]`.** Degenerate `p → ∞`
along a 2-adic / Newton-polygon limit; the period's `p`-adic Newton polygon controls its
valuation and hence the anomaly. The ledger tried "p-adic Newton-polygon" but as a *value*
no-go; here use it on the **count**. *RISK: tropicalization linearizes and loses the
cancellation; likely reduces to the energy count.*

**R18. The list as a coding-theoretic *covering* problem `[A, OFF-BGK]`.** Dualize: the list size
is the number of RS codewords in a Hamming ball; bound it via a **list-recovery / local-list-
decoding** capacity argument specialized to the explicit (non-random) RS code on `μ_n`. Recent
explicit-RS list-decoding (Brakensiek–Gopi–Makam, ePrint 2023/...) achieves list-decoding
capacity for *random* evaluation points; the question is the **explicit smooth** points.
*RISK: BGM is for random/generic points; smooth points are exactly the open case (the ledger's
GM-MDS/Lovett "genericity not fixed μ_n" horn).*

**R19. Restriction-estimate for `μ_n` as a Salem-type set `[OFF-BGK?]`.** Treat `μ_n` as a
spectral set and apply a discrete restriction (Stein–Tomas) estimate; the periods are the
restriction's `L^∞` norm. The ledger flagged Stein–Tomas "vacuous" — but specialized discrete
restriction for **2-power-structured** sets (Bourgain–Demeter decoupling) was not tried.
*RISK: decoupling controls `L^p` averages, not the `L^∞` peak (fails criterion (c)).*

**R20. The "two-value spike" rigidity theorem `[OFF-BGK]`.** Since the bulk is Gaussian and the
gap is in ONE peak, prove a **dichotomy**: either `M ≤ √(2n log m)`, or the period polynomial has
a *rational/cyclotomic factor* forcing a degenerate coset (excluded for proper `μ_n`). Target the
spike directly by structure, not moments. *RISK: the spike need not come from a rational factor;
the worst `b` can be generic — this is the crux of why moments fail.*

**R21. Sum-product *expansion* lower bound flipped `[OFF-BGK?]`.** BGK proves `μ_n` expands
(sum-product) ⟹ char sum small; but the **rate** is non-effective. Use a *quantitative*
expansion from the explicit 2-power structure (the subgroup is a geometric progression in
`log`), where Plünnecke–Ruzsa gives effective doubling constants. *RISK: `μ_n` has MAXIMAL
doubling (it's a subgroup); Plünnecke is vacuous — the ledger's PFR refutation.*

**R22. Quadratic-form / theta lift of the anomaly `[OFF-BGK?]`.** The anomaly count is a theta
coefficient of the ideal lattice `𝔭`; its growth is governed by the **Eisenstein vs cusp**
decomposition of the associated modular form. Bound the cusp contribution (the anomaly) by a
Deligne bound on the form's Fourier coefficients. *RISK: this is the effective-equidistribution
route in disguise (the cusp bound at fixed level `p` is the vacuous discrepancy `m/√q`).*

**R23. Additive-energy of the *complement* `[A, OFF-BGK?]`.** Instead of `E_r(μ_n)` (the
ledger's dead object), count energy of the **agreement-set complement** (the `δn` error
positions); for a structured worst word the error pattern is itself structured (consecutive),
giving a non-generic energy. *RISK: the complement energy is dual to the agreement energy;
likely the same wall.*

**R24. Information-theoretic / Kolmogorov bound on the worst word `[A, OFF-BGK]`.** The worst
word is the consecutive-exponent `x^a+x^{a−1}` — an `O(log n)`-bit object. Its window list is a
*computable function of `O(log n)` bits*; if the list were super-polynomial, it would encode
`>log n` bits, contradiction. Make this a rigorous incompressibility argument. *RISK: the ledger
refuted "Bad-Set Kolmogorov Incompressibility" (reduces to char-sum deviation) — but that was for
the SUP; the LIST-of-a-fixed-short-word version is different and may survive.*

**R25. The over-determined cyclotomic root-count growth law, closed `[A, OFF-BGK]`.** Settle the
§6 honest open question in its combinatorial form: does the over-determined incidence
`#{−e₁(S) : e₂(S)=0}` (closed forms `K(n,4)=n/4−1` shallow; the `O(n)∈{11,18,33,…}` law) stay
**deeply over-determined** (p-independent cyclotomic floor) or cross to under-determined?
*RISK: the height gate; counterexamples exist at thin-β primes once `(n/2)^φ > p`. Needs a
structural count bound, which is precisely the open part.*

---

## 3. Twenty-five "brand-new maths" (constructs, not just directions)

*Each is a mathematical object/operation I claim is genuinely new in this context, with a
defense of novelty and tractability, and the precise reason it was not seen before.*

**M1. The Non-Symmetric Dyadic Descent Functor `𝒟`.** A functor on the category of
(word, agreement-set) pairs over `μ_n`, sending `(u, S) ↦ {(u⁺, S⁺), (u⁻, S⁻)}` over `μ_{n/2}`
via the squaring map, with a *correction 2-cocycle* encoding the `(1+x)` boundary. **New
because** prior tower work only used the squaring identity on *symmetric* sets (a partial
functor); making it total requires the cocycle, which is the new object. **Tractable** because
the cocycle is supported on the `O(1)` antipodal-defect positions. **Unseen** because the
campaign always discarded non-symmetric sets rather than tracking their descent.

**M2. Defect-Rank Calculus.** A calculus assigning to each received word `u` a "defect rank"
`δ(u) = ` (number of monomial terms `− 1`), with a sub-additivity law
`L*(u) ≤ L*(monomial)·F(δ(u))` for an explicit `F`. **New** as a list-size analogue of matrix
perturbation theory. **Tractable**: the worst word has `δ = 1`. **Unseen**: list-decoding theory
bounds lists by radius, never by the *algebraic defect* of the received word.

**M3. The Quotient-Side 2-Adic Uncertainty Principle.** An uncertainty inequality for functions
on `ℤ/2^128` (the index group) relating `‖η̂‖_0` (Jacobi-sum support) and `‖η‖_∞ = M(n)`. **New**
because all prior uncertainty work was on the domain `ℤ_{2^μ}`; the quotient is a *different*
2-group of *different* order. **Tractable**: the Jacobi-sum DFT of `{η_b}` is explicitly the
multiplicative Fourier transform, computable. **Unseen**: nobody looked at the period sequence as
a signal on the index group.

**M4. Protocol-Restricted Proximity Threshold δ\*_Π.** A new invariant: the smallest δ such that
*for the specific direction family Π used by a protocol* the list is bad. δ\*_Π ≥ δ\*. **New**
because the literature defines MCA worst-case over all directions; δ\*_Π is protocol-indexed.
**Tractable** for FRI (Π = single-fold pencils, a 1-dim family). **Unseen** because the
prize was always read as the unrestricted threshold.

**M5. The Cross-Cell Inflation Constant `κ`.** The exact operator norm of the dyadic cross-cell
map as a multiplier on the period algebra, conjecturally `κ = √(2 ln 2)`. **New** as the
*spectral* (not contractive) reframing of the tower. **Tractable**: `κ` is a single measurable
constant. **Unseen** because the tower was abandoned once contraction failed — nobody measured
the inflation as a *deliberate* `log`-accumulator.

**M6. Anomaly Theta Series `Θ_𝔭(τ)`.** The generating function `Σ_{α∈𝔭} e^{2πiτ‖α‖²}` of the
prime-ideal lattice, whose `q`-expansion coefficients ARE the anomaly counts. **New** as a direct
bridge from the char-`p` anomaly to a modular object. **Tractable** via the theta-transformation
and the explicit ideal-lattice Gram matrix for 2-power cyclotomics (a tensor of `[[2,1],[1,...]]`
blocks). **Unseen** because the anomaly was framed combinatorially, never as a theta coefficient.

**M7. The Sparse-Difference Subgroup Root Bound.** A theorem: for `u−f` with `u` having `t`
terms and `f` deg `<k`, `#(roots in μ_n) ≤ G(t,k,n)` with `G` *sub-linear in `n`*. **New**: an
interpolation between Descartes (real) and Kelley–Owen (Johnson) tuned to mixed sparse/dense
inputs. **Tractable**: the `t=2` (binomial `u`) case is the worst word. **Unseen**: sparse-root
theory bounds roots of sparse `g`; here `g = u−f` is sparse-plus-dense, a new regime.

**M8. The Plurality Margin Functional `Γ(u)`.** `Γ(u) = ` (largest agreement) `−` (second-largest
agreement). **New** as the operationally-correct object for *unique* vs *list* decoding in MCA.
**Tractable**: bounding `Γ ≥ 1` from below suffices for the floor and may avoid the full list.
**Unseen** because list-decoding fixes the radius and counts; the *margin* is a different cut.

**M9. The 2-Power Subgroup Concentration Modulus.** A new arithmetic invariant `κ_int(μ_n,p) = `
max fraction of `μ_n` in any length-`L` interval mod `p`, with a conjectured 2-power-specific
bound. **New** as a sharpening of Vinogradov for *structured* (not generic) subgroups. **Unseen**
because interval-concentration results are stated for all subgroups uniformly.

**M10. The Window-List Self-Similarity Operad.** An operad encoding how window lists at `(ρ,η,n)`
compose under the dyadic tower; the constant-list phenomenon is an operadic fixed point. **New**
structural language. **Tractable**: the operad is generated by one binary operation (the
squaring split). **Unseen**: the tower was treated as a recursion, never as an algebraic
composition law with its own fixed-point theory.

**M11. Twisted Stickelberger Annihilator for the Anomaly.** Use the Stickelberger ideal to
*annihilate* the anomaly class in the ideal class group, reducing short-vector counting in `𝔭` to
counting in a *principal* (hence efficiently-described) ideal. **New** application of
Cramer–Ducas–Wesolowski "short Stickelberger" to a *counting* (not search) problem. **Tractable**:
2-power cyclotomic Stickelberger is explicit. **Unseen** because the SVP connection was used to
declare hardness, never to *reduce* the count via class-group annihilation.

**M12. The Period Polynomial's Coefficient Recursion.** The degree-`m` Gauss period polynomial
`Ψ_p(X)` has coefficients given by an explicit Jacobi-sum recursion; its largest root is `M(n)`.
**New**: a recursion for `Ψ_p` coefficients *down the 2-power tower* (relating `Ψ` at index `m`
to index `m/2`). **Tractable**: 2-power towers give clean resultant recursions. **Unseen**: the
period polynomial is classical, but its *dyadic-tower coefficient recursion* is not in the
literature.

**M13. Agreement-Set Homology.** Assign to a word `u` a chain complex whose `H_0` counts list
members and whose differentials are the squaring/dilation maps; constant list ⟺ vanishing higher
homology. **New** homological encoding of list-decoding. **Tractable**: the complex is finite and
explicit. **Unseen**: list-decoding has no homological invariants.

**M14. The Anomaly as a Mahler-Measure Defect.** Express `A_r − A_r^{char-0}` as the difference
of Mahler measures of two explicit families, making the anomaly a *height* defect. **New**
because the ledger's Mahler attempt (C22) measured the periods' height; this measures the
*anomaly's* height. **Tractable** via Smyth/Boyd explicit measures. **Unseen**: nobody connected
the char-p anomaly to Mahler measure.

**M15. Decoupling for the Period Exponential Sum.** A Bourgain–Demeter `ℓ²` decoupling inequality
for the exponential sum over `μ_n`, exploiting the 2-power lacunary frequency structure (`μ_n` is
a *geometric* frequency set in `log`). **New** application of decoupling to a *multiplicative*
subgroup. **Tractable**: lacunary decoupling is the cleanest case (Littlewood–Paley). **Unseen**:
decoupling is applied to additive/curved frequency sets, never to a multiplicative subgroup
viewed multiplicatively-lacunarily.

**M16. The Container Method for RS Lists.** A hypergraph-container bound on the number of RS
codewords in a Hamming ball, where the container hypergraph encodes agreement incidences. **New**
container application to algebraic list-decoding. **Tractable**: the incidence hypergraph has
bounded codegree (any `k+1` points determine ≤1 codeword). **Unseen**: containers are used for
extremal counts, not algebraic code lists.

**M17. Effective Igusa Zeta for the Anomaly Density.** The local density of anomaly solutions is
an Igusa local zeta integral over `ℤ_p`; its pole structure gives the count's growth. **New**
use of motivic/`p`-adic integration for the proximity anomaly. **Tractable**: the relevant
integral is over a binomial hypersurface (the worst word). **Unseen** in this context.

**M18. The "Single-Bump Green's Function" of the Tower.** Solve the dyadic-tower recursion with a
single source term (the `(1+x)` defect) via a discrete Green's function; the list size is the
Green's function evaluated at the top. **New** analytic encoding. **Tractable**: the tower
operator is explicit and lower-triangular. **Unseen**: the tower was iterated numerically, never
solved with a Green's function.

**M19. Cyclotomic Matroid of the Agreement Sets.** The agreement sets of list members form a
matroid on `μ_n`; constant list ⟺ bounded matroid rank. **New** matroid encoding leveraging the
`−1 ∈ μ_n` and squaring symmetries. **Tractable**: the matroid is representable over `ℚ(ζ_n)`.
**Unseen**.

**M20. The Berry–Esseen Correction at the Spike.** A *quantitative CLT with explicit tail
correction* for the single extreme period, replacing the failed EVT crown with a
Berry–Esseen-controlled deviation that is `b`-sensitive. **New** because it keeps the
deterministic `b`-dependence inside the error term rather than averaging it out. **Tractable**:
Berry–Esseen constants are explicit. **Unseen**: prior EVT work used limit laws (lost `b`).

**M21. The Folding Cocycle Cohomology Class.** FRI folding defines a 1-cocycle on the tower of
fields; its cohomology class obstructs/permits a uniform threshold. **New** Galois-cohomological
reading of the protocol. **Tractable**: `H^1` of a cyclic group is a quotient, explicit.
**Unseen**: the protocol was never given a cohomological invariant.

**M22. The Anomaly Sieve with Quotient-Group Moduli.** A large-sieve inequality where the moduli
are the *characters of `ℤ/m`* (the quotient), not the primes `q` (the refuted avg-`q` route).
**New** because it sieves on the index group, not the field-size parameter. **Tractable**: `ℤ/m`
characters are explicit `2^128`-th roots. **Unseen**: the avg-`q` sieve was on the wrong group.

**M23. The Pencil Discriminant Stratification.** Stratify the `(u₀,u₁)`-pencil space by the
discriminant of `u₀+γu₁ − f`; the binding antipodal direction is a *positive-codimension*
stratum the protocol may avoid. **New** because it gives a *measure* to the bad directions.
**Tractable**: discriminant strata are explicit. **Unseen**: bad directions were enumerated, never
stratified by codimension.

**M24. The 2-Adic Valuation Spectrum of `{η_b}`.** The multiset `{v_𝔭(η_b − η_{b'})}` of
pairwise valuations is a new invariant; a uniform lower bound on the *minimum* valuation forces
the periods apart `p`-adically and bounds the anomaly. **New** because the ledger measured
archimedean spread; this measures `𝔭`-adic spread. **Tractable**: the valuations are computable.
**Unseen**: the `wf-IWA` no-go was about `v_2(p−1)` *stratification of incidence*, NOT the
`𝔭`-adic spread of the periods themselves.

**M25. The Closed-Form Anomaly Bound via Subgroup-Sum Rigidity at Depth.** Conjecture and target
a *closed* formula `A_r = (2r−1)‼·n^r·(1 + ε_r)` with `|ε_r| ≤ r²/n` *proven for all `r ≤ n/2`*
by a rigidity argument on 2-power-root vanishing sums (an effective, depth-uniform Lam–Leung).
**New**: the ledger proves Lam–Leung in char-0 for all `r` and char-`p` only for `r = O(1)`; the
new object is a *char-`p`, depth-uniform* rigidity with an explicit `r²/n` error. **Tractable IF**
the 2-power vanishing-sum structure is rigid enough; this is the honest crux. **Unseen** as a
*depth-uniform char-p* statement (everyone splits into char-0-then-transfer, which breaks at
`r_max = O(1)`).

---

## 4. Honest self-assessment (pre-shred)

Of the 50, the ones I *defend* as genuinely off-BGK and absent from the dead ledger:
**R1, R2, R5, R11, R12, R14, R24, R25** and constructs **M1, M3, M4, M5, M10, M18, M25**. The
rest carry visible reduction risk that Essay II will make explicit. The centerpiece is **SEAM A**
(the non-symmetric list recursion, R1/R2/M1/M2) — it is combinatorial, data-supported, and the
gap is precisely located. SEAM B (R12/M4) is the highest-*leverage* if the protocol genuinely
restricts directions. SEAM C (R5/M3) is the most *structurally novel*. R11/M5 (the inflation
constant) is the boldest reframe of a refuted result and is decided by a single measurement.

The rest of this campaign: shred this in Essay II, rebuild no-larp in Essay III, then put the
survivors under adversarial computation.
