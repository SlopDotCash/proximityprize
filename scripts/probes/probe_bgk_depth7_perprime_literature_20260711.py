#!/usr/bin/env python3
"""Exact scale audit for per-prime depth-seven literature inputs.

This probe does not numerically test the production subgroup.  It certifies the
exponent gaps obtained by substituting the production parameters into explicit
published inequalities discussed in

  docs/kb/deltastar-466-depth7-per-prime-literature-audit-2026-07-11.md.

All comparisons carrying a verdict are integer-exact.  Decimal logarithms are
printed only as readable diagnostics.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
from math import isqrt


getcontext().prec = 80


def ceil_sqrt(x: int) -> int:
    root = isqrt(x)
    return root if root * root == x else root + 1


def dlog2(x: int) -> Decimal:
    return Decimal(x).ln() / Decimal(2).ln()


def fmt(x: Decimal, places: int = 12) -> str:
    return f"{x:.{places}f}"


def main() -> None:
    n = 2**30
    q = 365375409332725729550921208179070755120141565953
    m = (q - 1) // n
    a = m - 1
    depth = 7
    flat_constant = 2**18

    beta = Decimal(q).ln() / Decimal(n).ln()
    target = q * flat_constant * n**depth

    # Lu--Zheng, Theorem 4, equation (4), applied to the 13-character
    # all-nontrivial Jacobi family: A1=A2=K*, B=(K*)^11, moment index 1.
    # The real theorem bound is a^12*sqrt(q).  Squaring makes its comparison
    # with the deliberately generous whole-coefficient socket 2^18*m^7 exact.
    jacobi_socket = flat_constant * m**7
    lz_bound_ceil = a**12 * ceil_sqrt(q)
    lz_bound_sq = a**24 * q
    jacobi_socket_sq = jacobi_socket**2

    # Costa's explicit universal contraction can be loosened to this exact
    # rational upper constant, 1 - 2.27e-12.  The centered E7 cap obtained
    # from max r7 is q*C3*n^13 - n^14.
    c3_den = 10**14
    c3_num = c3_den - 227
    costa_centered_num = q * c3_num * n**13 - c3_den * n**14
    costa_target_num = c3_den * target

    # Chang's finite-abelian theorem has r <= 2 eps^-2 log(1/alpha).
    # The infimum of this displayed cap over eps in (0,1) is obtained as
    # eps -> 1.  Compare it to the rank at which 3^r already covers F_q.
    chang_rank_cap_inf = 2 * (Decimal(q) / Decimal(n)).ln()
    ambient_log3 = Decimal(q).ln() / Decimal(3).ln()

    # The monomial estimate |S_q(a X^m)| << sqrt(m) q^(2/3) log(q)^(1/6)
    # becomes |eta| << sqrt(n) q^(1/6) log(q)^(1/6).  Ignoring the log and
    # implied constant, its sixth-power ratio to the trivial eta <= n is q/n^3.
    monomial_ratio_sixth_floor = q // n**3

    # Shkredov Corollary 16: |eta| << n*q^{-delta/2^(7+2/delta)},
    # delta=log_q(n).  These are diagnostics because the theorem is asymptotic
    # and has an implied constant.
    delta = Decimal(n).ln() / Decimal(q).ln()
    denominator = Decimal(2) ** (Decimal(7) + Decimal(2) / delta)
    saving_in_n_exponent = Decimal(1) / denominator
    saving_bits = Decimal(30) * saving_in_n_exponent

    assert q == n * m + 1
    assert m == 2**128 + 192
    assert 2**158 < q < 2**159
    assert Decimal(158) / 30 < beta < Decimal(159) / 30
    assert target.bit_length() == 387

    # The Lu--Zheng theorem misses even the over-generous top-stratum socket
    # by strictly between 2^701 and 2^702.
    assert lz_bound_sq > jacobi_socket_sq * 2 ** (2 * 701)
    assert lz_bound_sq < jacobi_socket_sq * 2 ** (2 * 702)
    assert lz_bound_ceil**2 >= lz_bound_sq

    # Costa's theorem-supplied centered cap is essentially 2^162 targets.
    assert costa_centered_num > costa_target_num * 2**161
    assert costa_centered_num < costa_target_num * 2**162
    # To close from E7 <= C3*n^13, one would need
    # C3 <= n/q + 2^18/n^6, a number of order 2^-128.
    required_c3_num = n**7 + q * flat_constant
    required_c3_den = q * n**6
    assert required_c3_num * 2**129 > required_c3_den
    assert required_c3_num * 2**127 < required_c3_den
    assert c3_num * required_c3_den > c3_den * required_c3_num

    # At every eps<1 the published Chang rank cap is even larger than this
    # infimum, which already exceeds log_3(q).
    assert chang_rank_cap_inf > ambient_log3

    # Shkredov's fourth-energy input followed by |eta|^10 <= n^10 misses by
    # n^(49/9)/2^18 before its implied constant and log n.  The ninth power
    # of that ratio is exactly 2^1308 at n=2^30.
    assert n**49 == 2 ** (30 * 49)
    assert n**49 // 2 ** (18 * 9) == 2**1308

    # The monomial estimate is already worse than eta <= n before its log.
    assert q > n**3
    assert q > n**3 * 2**68
    assert q < n**3 * 2**69
    assert monomial_ratio_sixth_floor == 2**68
    # At the largest allowed epsilon=3/92, Bhakta--Shparlinski Theorem 2.1
    # permits gcd(e_i,q-1) <= (1/2)q^(91/299).  Our monomial exponent m
    # has gcd(m,q-1)=m and already exceeds q^(91/299).
    assert m**299 > q**91

    print("BGK_DEPTH7_PERPRIME_LITERATURE_AUDIT_20260711")
    print(f"n={n}=2^30")
    print(f"q={q}")
    print(f"m=(q-1)/n={m}=2^128+192")
    print(f"beta=log_n(q)={fmt(beta, 18)}")
    print("betaBracket=158/30<beta<159/30 (5.2666...<beta<5.3)")
    print(f"correctedTarget=q*2^18*n^7={target}")
    print(f"correctedTargetBitLength={target.bit_length()} (2^386<target<2^387)")
    print()

    print("LU_ZHENG_THEOREM4_EQ4")
    print("family=13 nontrivial annihilator characters; A1=A2=K*, B=(K*)^11")
    print("theoremBound=(m-1)^12*sqrt(q)")
    print(f"integerCeilingOfTheoremBoundBitLength={lz_bound_ceil.bit_length()}")
    print(f"generousTopStratumSocket=2^18*m^7 (bitLength={jacobi_socket.bit_length()})")
    print("exactGap=2^701*socket < theoremBound < 2^702*socket")
    print("verdict=cancels two character variables but leaves eleven at cardinality cost")
    print()

    print("COSTA_THEOREMS3_3_AND3_5")
    print("lambda=1/n; ell=7; max_x r7(x)/n^7 <= C3/n")
    print("paperExplicitLooseConstant=C3bar=1-2.27e-12")
    print("derivedCenteredCap=q*C3bar*n^13-n^14")
    print("exactGap=2^161*target < derivedCenteredCap < 2^162*target")
    print("requiredForClosure=C3<=n/q+2^18/n^6")
    print("requiredC3Bracket=2^-129 < requiredC3 < 2^-127 (approximately 2^-128)")
    print("verdict=fixed-depth Linfinity anticoncentration does not see uniform 1/q centering")
    print()

    print("CARENINI_FRANCHI_THEOREM4_1")
    print(f"infimumDisplayedRankCap=2*ln(q/n)={fmt(chang_rank_cap_inf, 18)}")
    print(f"ambientRankForThreeSpan=log_3(q)={fmt(ambient_log3, 18)}")
    print("rankCapAlreadyExceedsAmbient=True")
    print("verdict=the guaranteed three-span cardinality bound is vacuous for every epsilon<1")
    print()

    print("SHKREDOV_FOURTH_ENERGY_BASELINE")
    print("E2<<n^(22/9)*ln(n) implies offMoment14<<q*n^(112/9)*ln(n)")
    print("ratioToTargetBeforeConstantsAndLog=n^(49/9)/2^18")
    print("ratioNinthPower=2^1308")
    print("ratioBits=145+1/3")
    print()

    print("BHAKTA_SHPARLINSKI_MONOMIAL_BASELINE")
    print("etaBoundIgnoringLogAndConstant=sqrt(n)*q^(1/6)")
    print("sixthPowerRatioToTrivialN=q/n^3")
    print("ratioToTrivialBitsBracket=68/6 < bits < 69/6")
    print("sparseTheoremExponentThresholdAtEps3over92=91/299")
    print("productionGCDExponent=m; exactFailureCertificate=m^299>q^91")
    print("verdict=already more than 11.33 bits worse than eta<=n, before log")
    print()

    print("SHKREDOV_COROLLARY16_BASELINE")
    print(f"delta=log_q(n)={fmt(delta, 18)}")
    print(f"savingInNExponent=2^(-7-2/delta)={fmt(saving_in_n_exponent, 18)}")
    print(f"productionSavingBitsIgnoringConstant={fmt(saving_bits, 18)}")
    print("verdict=asymptotic BGK saving is effectively zero at this explicit depth-seven point")
    print()

    print("WU_WANG_MATRIX_BRIDGE")
    print(f"matrixDimension=index=m={m}")
    print("exactIdentity=singularValues(A_n)=m*abs(GaussPeriods)")
    print("exactIdentity=Schatten14(A_n)^14=m^14*sum(abs(GaussPeriods)^14)")
    print("verdict=determinant controls only the product; Schatten-14 is the original moment")
    print()

    print("FINAL_VERDICT=no cited per-prime theorem closes the corrected depth-seven target")


if __name__ == "__main__":
    main()
