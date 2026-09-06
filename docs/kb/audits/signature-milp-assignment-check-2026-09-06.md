# Binary signature MILP assignment checking

Before decoding a HiGHS result, the probe now rejects missing dimensions, nonfinite numbers and values farther than 1e-6 from a binary value, then checks every model row on the rounded binary assignment. Current model coefficients and finite bounds are integers, so these post-rounding constraint evaluations are exact. A rounded candidate violating even an auxiliary-variable constraint is rejected before signature reporting.

The solver-independent regression accepts a slightly perturbed valid binary assignment and rejects violated equalities, fractional values, NaN, infinity, out-of-range integers and wrong dimensions. This tests the checker directly; a full solver run remains outstanding. The module description now distinguishes floating-point MILP infeasibility from an independently checked UNSAT certificate. No retention-completion count is advanced by this checker change.
