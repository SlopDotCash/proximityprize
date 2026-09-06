# W13 replay and archive retention audit

Retain `scripts/probes/_out_w13_wavekernel_trace.txt` with its producer `scripts/probes/probe_w13_wavekernel_trace.py`. The complete corrected replay exits zero. All 15 numerical rows match the archive exactly: four graph cases, two spectral maxima, their relative difference and eight normalized moments. Both exact-rational coefficient comparisons also pass. Output labels and verdicts differ intentionally after the documented corrections.

The four graph cases are (n,p)=(8,89),(8,233),(16,257),(16,337), all through degree ten. FFT-to-matrix relative discrepancies remain below 1e-9; these are numerical comparisons. The companion integer-range audit bounds the direct matrix operations below 2^53. The separately implemented integer directed-edge test at p=13 passes, but does not independently replay the four larger matrices.

The archive's identification of its K recurrence with the cited paper's forward wave kernel is false. Its close moments are not identical and do not establish indistinguishability, required depth, or an impossibility theorem. The source and the two W13 correction notes supersede those historical interpretations. The actual paper wave kernels are not implemented by this replay. No general spectral or production result is claimed.

The companion JSON records hashes, the exact command and full corrected output. This reviews one additional original unreferenced archive: 57 of 92 reviewed, 35 remaining. The producer already had direct references and does not add another item to that count. The original inventory still retains 420 artifacts after the earlier G104 print-only source removal.
