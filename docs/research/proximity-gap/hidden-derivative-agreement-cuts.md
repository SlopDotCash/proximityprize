# Hidden derivatives and ordinary surfaces on selected witnesses

Let a length-`n` Reed–Solomon evaluation domain have distinct sites in a prime
field, message degree at most `d`, and agreement threshold `d<t≤n`. Select one
literal MCA witness polynomial for each bad scalar. Write `e=n−t`.

## Two kinds of interpolation at length 128

For dimension 32 and 62 agreements, the first-order interpolation parameters
`(multiplicity, derivative cap, total jet degree)=(8,3,16)` give 14,100
columns and at most `128·110=14,080` independent constraints. The challenge
height certificate is 11,264. This works for every received pair on every
prescribed 128-site domain. The strict beyond-Johnson inequality is
`62²<128·31`. A zero received pair also has the ordinary jet interpolant
`Y`. A two-level intercept with at least 62 sites at each level has trivial
ordinary kernels for every multiplicity and monomial cutoff at zero direction.
The certified differential equation has an additional variable for the
derivative of the sought polynomial. [Lean separation and coexistence](../../../ArkLib/Research/ProximityGap/Frontier/HiddenDerivativeSurfaceSeparation.lean)

The zero-direction obstruction persists for every direction with the same
intercept. Read the coefficient of the smallest scalar exponent with a nonzero
coefficient vector. A column whose explicit scalar exponent is larger has
zero coefficient in that row. At the diagonal exponent, the factor
`(u₀+Zu₁)^j` contributes just `u₀^j`. Hence the first nonzero coefficient
vector would itself be in the zero-direction kernel.

In particular the separated pair can carry 67 actual bad scalars. Number the
sites from 0 to 127. Set both rows to zero on the first 61. At site 61 set
`(u₀,u₁)=(0,1)`. At every site `i≥62` put
`z_i=x_i−x₆₁` and `(u₀,u₁)=(1,−1/z_i)`. The intercept has 62 zeros and
66 ones. For each of the 67 distinct labels `z_i=x_i−x₆₁` with `i≥61`,
the zero codeword agrees on the first 61 sites and the corresponding fresh
site. A joint explanation would force the direction polynomial to vanish on
the 61 common sites and hence everywhere, contradicting its nonzero value on
the fresh site. [Lean construction and directional injectivity](../../../ArkLib/Research/ProximityGap/Frontier/DirectionalJetObstruction.lean)

Two competing heads yield **128 distinct bad scalars** on the same domain
when the field has an off-domain element `α`. In particular every prime
field with 128 distinct sites does. Split the sites into blocks of 62 and
66. Take the pair `(0,0)` on the first block and `(1,x−α)` on the second.
The polynomial lines with sections `0` and `1+z(X−α)` meet at site `x_i`
when `z=−1/(x_i−α)`. At this scalar the opposite block's head agrees on
that entire block and on the extra site `i`. A joint explanation of that
support would force its intercept polynomial to equal the opposite
intercept everywhere, contradicting its value at `i`. The labels are
distinct. This obstruction persists above the one-head bound of 67. [Lean
two-head witness](../../../ArkLib/Research/ProximityGap/Frontier/DirectionalJetObstruction.lean)

Coexistence can also have bad scalars. Choose 30 fresh sites and give them
distinct nonzero labels `z_i`. Both words are zero elsewhere, and on the
fresh sites use `(u₀,u₁)=(1,−1/z_i)`. The same root argument with the 98
common zero sites gives 30 bad scalars. The ordinary interpolant
`Y∏_{fresh i}(X−x_i)` has weight `31+30=61<62` and vanishes identically on
every received line. The universal hidden-derivative certificate applies to
this pair as well. This 30-label construction is a written proof.

## Retaining many witnesses in one proper hyperplane

In coefficient space a witness is a point `(z,p₀,…,p_d)` with
`P(X)=Σ p_j X^j`. The received-site hyperplane at `x_i` has equation
`P(x_i)=u₀(i)+zu₁(i)`. For a subfamily of size `M`, let `H` be its common
received sites and put `h=|H|`.

If `h>d`, choose `d+1` common sites. Interpolation on these sites gives two
degree-at-most-`d` polynomials `A,B` such that each selected section equals
`A+zB`. Let `c` count sites where the pair `A,B` agrees jointly with the
received pair. Every site outside this joint set can agree with the head at
at most one scalar. Every selected witness must agree outside it at least
once by the literal MCA condition. This gives
`M·max(1,t−c)+c≤n` and hence `M≤e+1`.

If `h≤d`, count agreements outside `H`. Let `L` count witnesses at the most
popular remaining site. There is such a site since `h≤d<t≤n`. It misses at
least one selected witness and satisfies `M(t−h)≤(n−h)L`. Subtract
`(d−h)M` from the left and `(d−h)L` from the right to get
`M(t−d)≤(n−d)L`. In particular, whenever `M>e+1`, a single proper received
hyperplane retains at least the fraction `(t−d)/(n−d)` of the family. If
the family lies in an irreducible coefficient-space variety, the missed
witness certifies that the hyperplane cuts that variety properly. [Lean proof for literal MCA families](../../../ArkLib/Research/ProximityGap/Frontier/ProperAgreementCuts.lean)

## Consequence of a coefficient-space cover

Work over the algebraic closure. Suppose the selected points outside `E`
exceptional scalars lie in a cover of cumulative degree `Δ` and dimension
at most `s≥1`. Set `R=(n−d)/(t−d)`. Then the total population obeys

$$
 |\mathrm{Bad}|\le |E|+\Delta(e+1)R^{s-1}.
$$

To prove it, assign each nonexceptional point to a single irreducible
component. An irreducible curve of degree `D` with more than `e+1` assigned
points has a proper hyperplane cut retaining at least `M/R` of them.
Its intersection has at most `D` points, so `M≤DR≤D(e+1)`, since
`R=1+e/(t−d)≤e+1`. The same base bound holds for points. Induct on
dimension. For a component with more than `e+1` assigned points, take one
such proper cut. Bézout bounds the sum of the degrees of the child
components by the parent degree, and their dimensions decrease. The
inductive bound on that cut multiplied by `R` bounds the parent. For a
component with at most `e+1` assigned points the bound follows from
`D≥1` and `R≥1`. Sum over the initial components.

Jeronimo's Theorem 5.5 supplies just such a cover for a nonzero primitive
order-`r` symbolic equation when the message degree and total jet degree are
both smaller than the characteristic. Its dimension is at most `r+1`. In
the first-order length-128 example this gives
`|Bad|≤|E|+(6499/31)Δ`, in terms of the actual exceptional set and cover
degree. The paper bounds `|E|+Δ` by a polynomial in the interpolation
degree and message degree with an exponent depending on the order and jet
degree. That estimate does not give the small cover degree required by the
finite sponsor budgets. The preceding Bézout induction is a written proof.
The Lean endpoints prove its proper-cut and head-population inputs. Canonical ArkLib also contains the corresponding agreement ratio and rational Taylor chart machinery.
[Jeronimo, Theorems 5.5 and 1.2 and Lemma 7.1](https://arxiv.org/html/2609.05870v1)

For a first-order equation, one proper cut on each two-dimensional component
leaves curves or points. Each nonvertical irreducible coefficient curve
carries an ordinary surface for its selected sections. Indeed, over the
field of rational functions in `X`, the functions `z` and
`Σp_jX^j` on the curve are algebraically dependent because its function
field has transcendence degree one over that base field. Clear denominators
in a nonzero dependence to obtain `Q(X,Z,Y)`. Substitution of any
coefficient point on the curve makes `Q(X,z,P(X))` the zero polynomial in
`X`, since the identity holds in its coordinate ring after adjoining
`X`. A vertical component carries only one selected scalar. The retained
fractions and component degrees still enter when applying a surface bound
to the original family.

Brakensiek–Chen–Putterman–Zhang–Zheng's Section 3 interpolates a
differential equation for a fixed scalar received word. Their Theorem 2.1
then lists polynomial solutions. Applying that result separately to each
received word does not, on its own, constrain how their coefficient vectors
vary with the scalar. The parametric decomposition used above supplies this
extra input. [Brakensiek et al., Sections 2–3](https://arxiv.org/html/2609.08005v1)

## Explicit first-order bounds using one transcendental Taylor center

A first-order symbolic equation permits a direct count without estimating the
degree of its entire coefficient-space graph. Suppose the characteristic
exceeds `d≥1` and the total jet degree `b≥1`. Write `h` for the challenge
degree, `j` for the maximum exponent of the first derivative, and `D=h+b≥1`.
Let `q=t−d`, `R=(n−d)/q`, and
`L_s=1+max(0,2(d−s)−1)(D−1)` for `s=0,1`. Then a valid bad-scalar bound is

$$
 h+jD R L_1\max(e+1,RL_1)+bD\max(e+1,RL_0).
$$

**Separating the singular cases.** Start with the symbolic differential
polynomial `F(Z,X,Y₀,Y₁)`. A polynomial witness satisfies the equation after
putting `Y₀=P(X)` and `Y₁=P′(X)`. Differentiate in the highest jet
variable actually present. This partial derivative is a nonzero polynomial
since the jet degree is smaller than the characteristic. Put all solutions
on which this derivative specializes to the zero polynomial into the next
equation, given by the derivative. The other solutions belong to the
current nonsingular class. Continue until only a nonzero polynomial in
`Z,X` remains. It can specialize identically to zero for at most `h` scalar
values by taking any nonzero coefficient in `X`. This uses at most `j`
nonsingular classes of order one and at most `b` of order zero.

**Taylor coordinates.** Fix an indeterminate `α` and work over the
algebraic closure of the rational function field in `α`. For a nonsingular
class of order `s`, send a witness to its scalar and its jet of order `s` at
`α`. A nonzero polynomial in `X` stays nonzero on substituting `X=α`.
In particular the separant `S=∂F/∂Y_s` is nonzero at every selected point.
These points lie on the hypersurface `F(Z,α,Y₀,…,Y_s)=0`, which has
dimension at most `s+1` and cumulative degree at most `D`. This equation is
nonzero because substitution of the indeterminate `α` is injective on
coefficient polynomials in `X`. Distinct selected parameters stay distinct.

**Degree of a received equation on the initial jets.** We track total degree
in `Z,Y₀,…,Y_s`, with `X` in the coefficient ring. For `s=1` set

$$
 J=F_X+Y_1F_{Y_0},\quad
 T=S(\partial_X+Y_1\partial_{Y_0})-J\partial_{Y_1}.
$$

For `s=0` take `J=F_X` and `T=S∂_X−J∂_{Y₀}`. Along any nonsingular
solution the derivative of a polynomial `A` after substitution is
`(TA)/S` after substitution, by differentiating the equation.
Here `deg S≤D−1`, `deg J≤D`, and `deg(TA)≤deg A+D−1` for nonzero
terms. Thus `P^{(s+1)}=−J/S` on the solution. If a higher derivative is
represented by `N/S^a`, its successor is represented by
`(S·TN−aN·TS)/S^(a+2)`. The numerator degree increases by at most
`2(D−1)`. Induction represents `P^{(s+l)}` for `l≥1` with denominator
`S^(2l−1)` and numerator degree at most `1+(2l−1)(D−1)`. Canonical ArkLib already proves the corresponding joint total degree bound for the rational Taylor numerators and the padded numerators at a constant center. [Canonical Taylor numerator degree theorems](../../../ArkLib/Data/Polynomial/Differential/RationalTaylorJointDegree.lean)

Expand the degree-`d` polynomial from `α` to any prescribed site. The usual
Taylor coefficients are its ordinary derivatives divided by factorials,
which are invertible since `d<p`. Clear the common denominator
`S^max(0,2(d−s)−1)`. Each Taylor term, and also the affine received
value multiplied by that denominator, has degree at most `L_s`. Thus each
site is tested on the selected initial jets by a polynomial of degree at
most `L_s`. The exponent bound includes lower derivatives by multiplying
their numerators by the missing powers of `S`. All these identities hold
on the entire set of selected points since `S` never vanishes there.

**Counting.** On each irreducible curve of degree `a`, the proper received
cut retains at least `M/R` points whenever `M>e+1`. Bézout bounds its
intersection by `aL_s`, so the curve carries at most
`a·max(e+1,RL_s)` witnesses. On a two-dimensional component, the first
proper cut has cumulative degree at most `aL₁`; the same curve estimate
applies on its components. Multiplying by `R` and summing initial degrees
gives the displayed formula. This uses proper intersections on varieties in
ambient dimension at most three. The reconstructed jet vectors need only
satisfy the equation along the selected witnesses. The larger hypersurface
of formal initial conditions is an admissible cover.

In particular, for a fixed first-order rate choice with bounded `h,b,j`,
`d=O(n)` and a positive fixed lower bound on `(t−d)/n`, the number of
bad scalars is `O(n²)` on arbitrary distinct domains, with the constant
specified above. The canonical finite-length first-order MCA theorem already gives quadratic growth in the block length and a stronger envelope for the numerical applications below. [Canonical finite-length MCA theorem](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/FiniteLengthMca.lean)

## An arbitrary-domain bound in the 237-bit spectral witness field

The 128-bit budget in this field is 370883555463132043592346312614163.
Take `n=1024` and the row-specific multiplicities in the following table.
The agreement bound applies to every received pair on every domain in the
field. The last column floors the stronger canonical retained-squarefree envelope. Lean derives it for the literal worst-pair sponsor MCA error.

| Dimension | Agreements | Safe errors | Improvements in agreements from strict Johnson | Multiplicity | Derivative cap | Total jet degree | Challenge height | Bad scalars at most |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 512 | 706 | 318 | 18 | 565 | 175 | 780 | 2167787 | 26788941909929469439 |
| 256 | 479 | 545 | 32 | 1328 | 606 | 2496 | 10041169 | 687905649896919903388 |
| 128 | 326 | 698 | 35 | 273 | 151 | 701 | 436279 | 790768777796617278 |
| 64 | 222 | 802 | 32 | 232 | 154 | 819 | 398583 | 397398880011593585 |

The four `spectral_field_eps` instances verify the complete implication from
the arbitrary prescribed domain to `ProximityGap.epsMCA ≤ 2⁻¹²⁸` in Lean.
The proof constructs a first-order certificate and uses canonical ArkLib's
squarefree recovery outside the bounded exceptional set. For a literal MCA
witness, an exact correlated pair on its full agreement set restricts to a
joint explanation on the chosen support. Thus every bad scalar is in the
exceptional set, uniformly over both received words. This implementation
uses canonical squarefree recovery, independently of the written proper-cut
argument above. The two production fields at production length require
stronger bounds.
[End-to-end Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/ExplicitFirstOrderCutBudgets.lean) ·
[Canonical squarefree recovery](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/CurveMCA.lean) ·
[Field, subgroup and upper bounds on that subgroup](dyadic-locator-sum-barrier.md)
