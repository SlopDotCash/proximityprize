# Source-root probe interpolation correction

The source-root-coupled search applied inverse Vandermonde matrices with the input and output axes reversed. For evaluation vector y and Vandermonde matrix V, coefficients are V⁻¹y. The former einsum contracted y against rows of V⁻¹, producing its transpose action instead. This affected both outsider classification and global joint-core interpolation.

The correction swaps the inverse axes in all three contractions. A known cubic regression fails before the change and passes afterward for every four-point complement anchor at every scalar. A second regression verifies that the returned joint-core witness attains its reported agreement and includes at least the seven prescribed source coordinates. Both tests pass. Invalid nonpositive sample and batch sizes are also rejected before search.

Previously generated search counts from this producer must not be used as verified evidence without rerunning the corrected implementation. The full default 100000-sample replay has started but is not yet complete; no retention-completion increment or production-bound claim is made here.
