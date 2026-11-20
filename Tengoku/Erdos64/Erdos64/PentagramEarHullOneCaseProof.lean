import Tengoku.Erdos64.Erdos64.Basic
import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

def oneCaseProofRoute (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 1) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 0) <|
        SimpleGraph.Walk.cons (H.ca_adj 1) <|
          SimpleGraph.Walk.cons (H.ab_adj 1) .nil

/--
@isnad1 id=eq.0h3v.s5.e79880141760 from=translated src=- shape=990c9dfd vocab=3fc71edc
-/
theorem oneCaseProofRoute_length (H : PentagramEarHull G) :
    H.oneCaseProofRoute.length = 5 := by
  rfl

/--
@isnad1 id=ispath.0h3v.s5.76bf92182cda from=translated src=- shape=def4ed68 vocab=4340e45a
-/
theorem oneCaseProofRoute_isPath (H : PentagramEarHull G) :
    H.oneCaseProofRoute.IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 1),
      H.vertex (.inr (.inl 1)), H.vertex (.inr (.inr 1))]
  let xs : List (Sum (Fin 5) (Sum (Fin 5) (Fin 5))) :=
    [.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 1,
      .inr (.inl 1), .inr (.inr 1)]
  have hxs : xs.Nodup := by
    decide
  exact List.Nodup.map H.vertex_injective hxs

end PentagramEarHull

end Erdos64
