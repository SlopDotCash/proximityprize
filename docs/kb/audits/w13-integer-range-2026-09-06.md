# W13 matrix arithmetic range check

For the four fixed F1 cases of `probe_w13_wavekernel_trace.py`, degree m<=10, conservative absolute-sum bounds remain below 2^53. The companion JSON records integer bounds calculated without floating point.

Adjacency powers have row sum n^m; Hashimoto powers have row sum (n-1)^m and matrix dimension pn. Multiplying the respective row sums by the matrix dimension bounds all entries, positive accumulation intermediates and traces. For the signed K recurrence use U0=1, U1=n, U_m=n*U_(m-1)+(n-1)*U_(m-2). For NB use V1=n, V2=n²+n and the same positive recurrence. These bound absolute row sums including both terms before subtraction; multiplying by p also bounds trace accumulation. All bounds increase over the tested degrees, so the degree-ten check suffices.

The largest bound is 3109298906250000, below 2^53=9007199254740992. Thus standard float64 multiply/add operations on these integer matrices stay exactly representable for these cases. A trace's proximity to an integer alone would not establish this. FFT spectral powers and their comparisons remain approximate; this range argument does not make them exact.

The separate p=13 directed-edge integer regression passes. The complete four-case replay is still running at the time of this record, and no new retention completion is claimed.
