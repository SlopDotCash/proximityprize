# G101F offset quotient regression

`test_g101f_quotient.py` checks every offset in F5^4 for the directions x and x³ on the four nonzero field elements, with constant codewords and agreement threshold two. It independently enumerates all five scalars and all five codewords for each of the 625 offsets per direction. All 1250 bad-scalar counts agree with the G92 fast engine.

For each direction, the G101F pivot routine selects two independent pivot coordinates. Every offset has exactly one representative with zero pivot coordinates after adding a constant codeword and a scalar multiple of the direction. Exhaustive checking confirms the representative preserves its bad-scalar count and the maximum over all offsets equals the maximum over the 25 representatives.

In general, adding a codeword translates the candidate witnesses; adding beta times the direction permutes scalars by gamma -> gamma+beta. The full-rank pivot restriction therefore gives a transversal without changing counts. This finite regression checks the implementation on a small instance. It does not replace the full stage-three replay or prove the general prize theorem. The retention count remains 63 of 92 while that replay is pending.
