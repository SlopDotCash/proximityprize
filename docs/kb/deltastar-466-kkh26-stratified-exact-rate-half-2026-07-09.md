# KKH26 at exact rate one half: the missing stratified degree weld

Date: 2026-07-09  
Status: bad-side bridge formalized; the Delta-star core remains open

## The parameter correction

For the degree-decoupled KKH26 endpoint

\[
D=(r-1)m-1,
\]

the Reed--Solomon dimension is `D+1=(r-1)m`.  Since the block length is
`n=2^mu*m`, exact rate `rho` therefore requires

\[
r-1=\rho 2^\mu.
\]

The resulting bad radius is

\[
1-\frac r{2^\mu}=1-\rho-2^{-\mu}.
\]

This is different from the older degree `(r-2)m` parameterization.  Setting
`r-2=rho*2^mu` there gives dimension `rho*n+1`, not exact rate `rho`.

At exact rate `1/2`, write `s=2^mu`.  Then

\[
r=s/2+1,\qquad D=(s/2)m-1,\qquad \delta=1/2-1/s.
\]

This is precisely one step outside the old unstratified range `r<=s/2`.  Its old
numerator `2^r*C(s/2,r)` is zero.

## Why stratification repairs this one missing row

The antipodal stratification in `KKH26StratifiedSpread` applies for every `r<=s`.
At `r=s/2+1`, the stratum `j=1` is feasible:

- the free signed support has size `r-2=s/2-1`;
- it uses `s/2-1` antipodal classes;
- the one cancelling antipodal pair uses the final class.

Consequently this stratum alone supplies

\[
2^{s/2-1}\binom{s/2}{s/2-1}=(s/2)2^{s/2-1}
\]

distinct bad scalars.  The full proved numerator is larger:

\[
N_{\rm strat}(s,s/2+1)
=\sum_{j\in\operatorname{feasSet}(s/2,s/2+1)}
2^{s/2+1-2j}\binom{s/2}{s/2+1-2j}.
\]

## Lean artifact

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_KKH26StratifiedExactRateHalf.lean`
contains:

- `kkh26_stratified_subceiling_epsMCA_lower_bound`: combines the full stratified
  numerator and range `2<=r<=2^mu` with the degree window
  `(r-2)m<=D<(r-1)m`;
- `kkh26_stratified_exactRateHalf_epsMCA_lower_bound`: specializes to
  `r=2^(mu-1)+1`, `D=2^(mu-1)m-1`;
- `one_mem_exactRateHalf_feasSet`: machine-checks that the rescuing `j=1` stratum is
  feasible;
- `kkh26_stratified_exactRateHalf_mcaDeltaStar_le`: converts the bad mass into the
  operational upper ceiling;
- `exactRateHalf_dimension_twice` and `exactRateHalf_evalCode_eq_rsCode`: certify that
  this is genuinely the dimension-`n/2` RS code, not the old `n/2+1` mismatch.

The proof reuses the KKH fibre witness unchanged.  The explaining polynomial still has
degree at most `(r-2)m`, so it belongs to the enlarged endpoint code.  The direction
`X^((r-1)m)` still cannot agree with a degree-`D` polynomial on `rm` points because
`D<(r-1)m<rm`.  Thus degree enlargement and antipodal stratification are independent and
can be welded without changing the bad line.

## What this buys, and what it does not

It buys the previously absent KKH bad-side row for the exact rate-`1/2` code, at radius
`1/2-2^-mu`, whenever the target error is below `N_strat/p`.

It does **not** solve the prize:

1. The theorem currently uses the large-prime separation condition
   `p > s^(s/2)`.  For `s=64`, the full exact-rate-half numerator has about `2^49.72`
   elements while the size condition forces `p>2^192`; hence `N_strat/p<2^-142`, so
   this size-condition version cannot even beat the prize budget `2^-128` in that row.
   A polynomial-field version needs a new cross-stratum nondivisibility/good-prime
   supply; the fixed-support KKH `of_not_dvd` theorem does not provide it.
2. This is only the bad side, hence only an upper bound on operational `mcaDeltaStar`.
   No matching good-side theorem is supplied.
3. The `InteriorCeiling`/field-supply obligation and the central MCA lower-bound wall are
   unchanged.  In particular, this theorem must not be advertised as a Delta-star pin or
   prize closure.

The exact mathematical gain is therefore narrow but real: the former rate-`1/2`
dimension mismatch is removed, and the reason the ordinary KKH count vanished there is
repaired by the first antipodal-pair stratum.  The remaining obstruction is no longer the
degree geometry; it is polynomial-field collision separation plus the still-open good
side.
