# Deployment checkpoint provenance

The two retained NumPy files in `scripts/probes/_ckpt_466_deploy/` are floating-point Gaussian-period vectors, not proof certificates. Their historical producer is `scripts/probes/probe_466_deployment_certificates.py` at commit `a9ae35f6f`, whose checkpoint code writes `c_<name>.npy` and whose case list identifies BabyBear as 15*2^27+1 and ctrl27_c17 as 17*2^27+1. That producer is absent from the current tree.

Both files load with pickle disabled, contain finite float64 values, and have the expected 15 and 17 entries. The companion JSON records hashes and numerical residuals against mass and Parseval identities. These necessary consistency checks neither reproduce the underlying billion-point coset sums nor certify floating-point error. Preserve the arrays pending full provenance/reproduction review; no retention-completion increment is claimed.
