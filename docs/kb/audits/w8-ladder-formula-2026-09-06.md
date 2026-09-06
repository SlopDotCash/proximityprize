# W8 ladder scan

The dyadic scan now computes the maximum feasible positive integer g directly. For c>0 the original inequalities are equivalent to g <= floor((floor(s/2)-2)/c) and g <= floor((c*floor(s/2)-budget*s-1)/c). Their minimum is the answer if positive; otherwise there is no feasible g. This replaces a descending search that could visit hundreds of millions of rejected values.

The regression compares the formula against exhaustive enumeration in 5000 cells (even s from 8 through 256, c=1 through 20, budgets one and two). All agree. The complete part-four ladder and its assertions pass. Its endpoint decimal now comes from the exact numerator divided by N instead of an inaccurate literal.

Other W8 construction and toy-validation stages have not been replayed by this check. This is an equivalent arithmetic scan and reporting correction, not a completed retention review or proof of the broader construction claims. Retention remains 71 of 92.
