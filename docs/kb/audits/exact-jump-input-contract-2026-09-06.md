# Exact-jump finite-field and storage preconditions

The integer architecture probe now requires a prime modulus, n >= 32, 16 dividing n, n dividing p-1, and agreement in 1..n. Rejecting n=16 is necessary because m=1 makes the stated degree allowance m-2 negative; clamping that allowance to zero would admit a construction outside the advertised degree constraint. Parsing rejects trailing noninteger characters, and n=0 is rejected before divisibility arithmetic.

The dynamic program rejects dimensions whose maximum four-label-per-coordinate score exceeds int16 storage or whose packed state indices exceed uint32. Primitive-root factorization uses division rather than an overflow-prone squared trial divisor.

The C++20 optimized build succeeded. Six invalid-input cases (zero n, n=16, composite p=289, zero agreement, agreement above n, and a malformed modulus) were rejected. The documented `97 32 18 fixed` run exited 0, examining 31 fixed triangle extensions and three partition signatures; it returned best_abstract_labels=-1, meaning no feasible assignment within that restricted model. Other documented modes and an independent DP correctness audit remain outstanding, so this does not advance the retention-completion count or prove a general bound.
