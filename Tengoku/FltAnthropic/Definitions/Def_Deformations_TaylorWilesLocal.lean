import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Module

namespace TaylorWiles

variable {k : Type*} [Field k]

local notation "M₂ " k => Matrix (Fin 2) (Fin 2) k

noncomputable def adAction (M : M₂ k) : Module.End k (M₂ k) :=
  LinearMap.mulLeft k M - LinearMap.mulRight k M

/--
@isnad1 id=eq.0h3v.s9.fe5103833ca0 from=translated src=- shape=881768ca vocab=12b31ae7
-/
@[simp] lemma adAction_apply (M X : M₂ k) : adAction M X = M * X - X * M := rfl

def disc (M : M₂ k) : k := M.trace ^ 2 - 4 * M.det

variable (k) in

noncomputable def traceZero : Submodule k (M₂ k) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)

/--
@isnad1 id=iff.0h2v.s8.748ee3917120 from=translated src=- shape=280c31a1 vocab=9ce44de0
-/
@[simp] lemma mem_traceZero_iff {X : M₂ k} : X ∈ traceZero k ↔ X.trace = 0 :=
  Iff.rfl

end TaylorWiles
