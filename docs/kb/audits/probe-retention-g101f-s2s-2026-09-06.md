# G101F spread search archive

Retain `scripts/probes/_out_g101f_s2s.txt` as a reproducible seeded search log. The complete stage s2s replay exited 0 and matched the archive after normalizing newlines and elapsed seconds. The engine self-test passed. Independent trial division verified the selected field prime, recorded in the JSON.

At n=32,k=4,a=11, the search tests coefficient-one directions with exponent pairs (8,10), (8,26), (9,11), (10,24). The producer's agreement calculation is ten for each, so each passes its a-farness filter. The fixed search budget finds bad-scalar count 22 for each direction. The source uses seed 4669102, structured seeds, random offsets and bounded local mutations; it does not exhaust all offsets.

The count 22 is therefore a search lower bound, not an upper bound or a proof that 25 cannot be reached. Even a spread value above 24 would not by itself refute a factor-three bound when the monomial baseline is only known from below. The output does not preserve the offset vectors, so this replay is an algorithm-output reproduction, not an independently portable witness certificate. No production theorem is discharged.

Only the archive is in the original unreferenced group. The corrected retention total is 70 of 92, with 22 remaining. Stage s2 remains under separate replay.
