import ReferenceV55Full

/-!
# Final exported targets (V60 consolidated source)

This entrypoint uses the attributed, pinned reference proof through V55.
It is not an independent proof of the paper's intermediate results.
Run `bash verify_final.sh --main-only` to prepare the Lake workspace,
compile the dependencies and audit both exported theorem declarations.
The source is unverified in the packaging environment.
-/
namespace OpenAI086.Final

/-- The original minus-shift principal-value estimate. -/
theorem theorem1_1 : OpenAI086.Theorem1_1_Goal :=
  OpenAI086.ReferenceV55.exact_main

/-- The original estimate together with the unique bounded extension. -/
theorem theorem1_1_full : OpenAI086.V41FullMainGoal :=
  OpenAI086.ReferenceV55.full_main

end OpenAI086.Final

#print axioms OpenAI086.Final.theorem1_1
#print axioms OpenAI086.Final.theorem1_1_full
