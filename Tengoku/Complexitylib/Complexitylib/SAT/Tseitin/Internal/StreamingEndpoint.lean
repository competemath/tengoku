/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Internal.Streaming

/-!
# Successful streaming endpoints

This proof-only module exposes the exact final transducer state reached on a
typed CNF token stream. The endpoint is recovered from the public
`transformFrom?_tokens_internal` result, so the token-level execution proof in
`Internal.Streaming` remains the single source of truth.
-/

public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Streaming

/-- Running a typed CNF token stream reaches the exact state described by
`CNF.to3Aux`, before the final `finish` projection is applied.
@isnad1 id=eq.0h2v.s4.047f091d2668 from=translated src=- shape=3af58489 vocab=d7267480
-/
theorem run_tokens_endpoint_internal (phi : CNF) (next : ℕ) :
    run (initial next) phi.tokens =
      some
        { next := (phi.to3Aux next).2
          pending := .zero
          scan := .boundary
          emitted := (phi.to3Aux next).1.tokens } := by
  have htransform := transformFrom?_tokens_internal phi next
  simp only [transformFrom?] at htransform
  cases hrun : run (initial next) phi.tokens with
  | none =>
      simp [hrun] at htransform
  | some st =>
      rw [hrun] at htransform
      rcases st with ⟨finalNext, pending, scan, emitted⟩
      cases pending <;> cases scan <;> simp [finish] at htransform
      rcases htransform with ⟨hemitted, hnext⟩
      subst emitted
      subst finalNext
      rfl

/-- Exact successful endpoint when the fresh-variable counter starts one past
the concrete source bit length.
@isnad1 id=eq.0h1v.s6.8d74846416d3 from=translated src=- shape=52d71859 vocab=6d568c58
-/
theorem run_tokens_bitLengthStart_internal (phi : CNF) :
    run (initial (phi.encode.length + 1)) phi.tokens =
      some
        { next := (phi.to3Aux (phi.encode.length + 1)).2
          pending := .zero
          scan := .boundary
          emitted := (phi.to3Aux (phi.encode.length + 1)).1.tokens } :=
  run_tokens_endpoint_internal phi (phi.encode.length + 1)

end Streaming

end ThreeSAT

end SAT

end Complexity
