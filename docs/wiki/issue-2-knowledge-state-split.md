# Knowledge-state construction and soundness split

`AppendRbrKnowledgeStateFunction.lean` contains the composite knowledge-state
construction and its projections. `AppendRbrKnowledgeSoundness.lean` imports it
and contains the per-round bounds, phase-two reconciliation, and soundness
keystones. The modules have 916 and 913 lines, respectively.

The original declaration bodies are preserved byte-for-byte on either side of
the existing soundness section boundary. Six consumers import the soundness
module to retain the original transitive API. Names, theorem statements, proof
bodies, and residual conditions are unchanged. A full import-graph traversal
found no cycles. The generated prize umbrella remains unchanged because these
substrate modules enter transitively.

Both split modules passed direct Lean checks against a private compiled state
module and the existing dependency cache. The retained soundness axiom audit
reports no `sorryAx`. All six changed consumers also passed direct Lean checks. Full integration
and hosted validation remain required. This organization change
does not discharge any residual or strengthen the security statements.
