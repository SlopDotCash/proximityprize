# R387 MILP unresolved outcome

The MILP probe previously returned success when no checked counterexample was found, including solver limits. It now returns exit 2 for unresolved results, exit 1 for a checked MCA witness, and exit 0 only when all requested branches are reported infeasible by the solver. An empty branch set is unresolved. Numerical infeasibility is not an independently verified certificate, and requested pivot subsets do not prove all-direction coverage.

A real pivot-4 run with time limit 0.01 seconds returned HiGHS status limit and exited 2. Controlled limit, infeasible and other statuses produced distinct expected outcomes. No constraint or witness-checking logic changed. This test establishes outcome handling, not a completed finite search or a new retention review; coverage remains 58/92.
