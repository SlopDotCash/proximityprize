# Completed finite searches and unresolved MILP

The mu32 locator search completed its default 64 seeds, testing 215414784 candidate A sets and rejecting 300 characteristic-specific hits. The total equals 64 times binomial(32,7), consistent with exhaustive A enumeration for each selected C. Trial division verifies the two comparison primes 193 and 257, and modular exponentiation verifies that their configured roots have order 32. No hit survived all three fields. This does not exhaust every C or prove nonexistence of another construction.

The exact-jump `97 32 18 all` run completed with 582231 raw normalized cliques and 35 partition signatures. It found no feasible assignment within its encoded four-line architecture. The fixed mode and independent 1875-case DP regression were already checked. The documented `193 64 36 all` case remains outstanding; neither run establishes a bound for arbitrary received stacks.

The default thirteen-signature MILP terminated with HiGHS status 1, time limit reached, and no primal solution. This is unresolved, not infeasible. Its three-signature feasibility check passed separately. Full outputs, exit codes and source hashes are preserved in the companion JSON. No aggregate retention count is advanced here pending completion of the remaining review requirements.
