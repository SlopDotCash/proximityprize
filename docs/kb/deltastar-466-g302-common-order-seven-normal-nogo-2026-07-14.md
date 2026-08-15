# G302: the only common bounded-order sponsor normal is order seven, and it is sign-decoupled

Date: 2026-07-14
Issue: #466
Branch: `research/proximity-prize` only

## Verdict

The two sponsor quotient orders are

```text
m1 = 2^128 + 192,
m2 = 2^129 + 13,
gcd(m1,m2) = 7.
```

Hence every nonprincipal character order that is fixed and common to both sponsors is exactly
seven. Its canonical generator-independent primitive trace is the Ramanujan aggregate

```text
L7(r) = sum_{j mod m} c7(j) A_{g^j}(R_r),
c7(j) = 6 if 7 divides j, and -1 otherwise.
```

An exact 54-rank-cell census gives sign agreement with the coefficient-two target in exactly
`27/54` cells and realizes all four sign quadrants. The unique common fixed-order normal therefore
does not carry the CORE sign. This is a route no-go, not a sponsor estimate. CORE remains open and
on the BGK/Paley wall.

## 1. Structural reduction to order seven

Let `Q_i = F_{P_i}^*/G` be the cyclic quotient at sponsor `i`. A character of fixed order `d`
exists on both quotients only if `d | m1` and `d | m2`. Lean proves

```text
Nat.gcd m1 m2 = 7,
2 <= d -> d | m1 -> d | m2 -> d = 7.
```

The primitive-order-seven orbit has six characters. Summing that orbit gives the classical
Ramanujan sum

```text
c_7(j) = sum_{a in (Z/7Z)^*} exp(2 pi i a j / 7)
       = 6  when 7 | j,
        -1  otherwise.
```

This is the unique generator-independent nonprincipal trace at the common fixed order. If the
cyclic generator changes by `j -> u*j` with `gcd(u,7)=1`, divisibility by seven is unchanged. The
Lean theorem `ramanujanWeightSeven_mul_of_coprime` kernel-checks that invariance.

References for the standard primitive-root trace and integer formula include Ramanujan's sum
`c_q(j)=mu(q/gcd(q,j))*phi(q)/phi(q/gcd(q,j))`; for prime `q=7` it specializes to the two values
above. This use is only the definition of the canonical trace, not an analytic estimate.

## 2. Exact probe

Run:

```text
python3 scripts/probes/g302_common_order7_normal_nogo.py
```

The probe uses:

- exact primitive-root construction;
- direct enumeration of `mu_n`;
- exact integer subset-sum dynamic programming through ranks five and six;
- direct integer weighted kernels `W_a(t)=#{(y,z):a*y-z=t}`;
- exact centered alignment `A_a=p*sum_t W_a(t)R_r(t)-n^2*sum_t R_r(t)`;
- no FFT, floating-point comparison, or fitted coefficient.

It scans every cell in the declared ranges with `7 | m=(p-1)/n`, `2 notin G`, and
`n in {8,16,32}`. It also recomputes the normal after every quotient-generator change by a unit and
checks exact equality.

Output:

```text
cells=27 rankcells=54 sign_agree=27/54
quadrant=(-1,-1): n=8,  p=113, m=14, r=5, A2=-13128,  L7=-364312
quadrant=(-1,+1): n=16, p=113, m=7,  r=6, A2=-77440,  L7=+1048640
quadrant=(+1,-1): n=8,  p=337, m=42, r=5, A2=+282928, L7=-5712824
quadrant=(+1,+1): n=8,  p=281, m=35, r=5, A2=+189728, L7=+413632
```

The sharpest witness fixes the prime and subgroup and changes only the adjacent rank:

```text
mu_16 <= F_113^*:
r=5: A2=+1,727,120, L7=-20,424,976;
r=6: A2=   -77,440, L7= +1,048,640.
```

Thus both mismatch polarities occur on one proper dyadic subgroup. Neither sign of `L7` yields a
rank-uniform implication for `A2`.

## 3. Asymptotic and literature placement

The structural gain is exact but narrow. The common fixed-order parameter space is `{1,7}`:

- order one is the principal/average direction already localized by G297 and G301;
- order seven is the only common nonprincipal order and is refuted above as a uniform sign normal.

This does not prove that the order-seven value at either production sponsor has either sign. It
proves that no field-uniform theorem can use the canonical common order-seven trace as a sign
surrogate for the coefficient-two target.

The result also explains why existing literature does not fill the gap automatically:

- Shkredov and Vyugin, *On additive shifts of multiplicative subgroups* (arXiv:1102.1172), bound
  nonnegative intersections of shifted subgroup copies. Those estimates do not choose the signed
  placement of the distinguished coefficient-two coset against the rank-labelled row.
- Gross--Koblitz and Stickelberger describe p-adic Gauss-sum data and ideal valuations. They do not
  by themselves compare the required Archimedean real sign of `L7` with `A2`; the exact witness
  shows that no such comparison is field-uniform at fixed order seven.
- Lu--Zheng--Zheng, *On the distribution of Jacobi sums* (arXiv:1305.3405), provides distribution
  results for varying character families. The CORE object is a fixed sponsor, row-labelled weighted
  covariance. Averaging the character family or changing the row loses the quantifier that G297
  isolates.

FS15--FS18 are fully consumed rather than bypassed. They provide the fixed-depth almost-all-prime
Wick ladder, the sharp `(2r)^(n/2)` resultant envelope, a finite-depth simultaneous good set, and the
odd/even zero-sum taxonomy. Their exceptional-set budget cannot select the two explicit sponsors at
the in-window depth `r*=89`; G64 already forces the sponsor exceptional by depth six. They supply no
order-seven-to-target sign transfer.

## 4. What is closed and what survives

Closed:

- every sponsor-uniform nonprincipal fixed character order other than seven, arithmetically;
- the unique canonical generator-independent order-seven trace as a uniform sign normal;
- both possible sign implications from that trace to the coefficient-two target.

Still open:

- a sponsor-specific character order chosen separately at each sponsor before seeing the row;
- a sponsor-specific Gross--Koblitz/Stickelberger normal with a proved positive real margin;
- the full row-labelled covariance at production depth.

Any survivor must be specified before evaluating the gate and must prove both
`ell_89 >= eta > 0` and `|A_89-ell_89| < eta`. Choosing the order or coefficients after inspecting
`R_89` restores the target placement and is circular.

## 5. Artifacts

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G302CommonOrderSevenNormalNoGo.lean`
- Probe: `scripts/probes/g302_common_order7_normal_nogo.py`
- Ledger: `[466-G302-common-order-seven-normal-nogo]`

Theorems use only the accepted standard axioms; exact sign witnesses are axiom-free. No custom
axiom, `sorry`, or `native_decide` is used.
