# W13 moment comparison correction

`probe_w13_wavekernel_trace.py` used proximity thresholds to claim identical bounded-depth moments and an impossibility of distinguishing two instances. The F3 replay exits zero and reports maximum relative moment difference 0.00024377980611763335 through degree six, versus relative spectral-maximum difference 0.04536166777142739. Nonzero differences do not establish equality or indistinguishability.

There is also an exact distinction. For a nonzero subgroup of size n, character orthogonality gives sum over all frequencies of eta_b equal to zero. Removing eta_0=n leaves sum=-n, hence the first normalized moment is -sqrt(n)/p. At n=16 this is -4/p, which differs for p=65617 and p=65633. This identity alone invalidates the claimed indistinguishability; it does not solve the spectral-bound problem.

The F3 reporting and combined verdict now describe the checks without asserting a required depth or ruling out all uses of the cited paper. The matrix experiments F1/F2 and correspondence with the paper have not been replayed or independently audited here. The historical archive remains intact and unverified. This source correction does not increase completed retention coverage beyond 56/92.
