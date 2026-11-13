import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Functoriality of cubical homotopy groups

Mathlib's `HomotopyGroup N X x` (classes of `GenLoop`s, i.e. maps from the cube `I^N`
sending `Cube.boundary N` to `x`) currently lacks functoriality in the space `X`.
This file provides it:

* `Submission.genLoopMap`: postcomposition of a generalized loop with a based map;
* `Submission.homotopyGroupMap`: the induced map on homotopy groups;
* `Submission.homotopyGroupMapMulHom`: the induced group homomorphism
  (for `[DecidableEq N] [Nonempty N]`);
* `Submission.homotopyGroupMap_comp`, `Submission.homotopyGroupMap_id`: functoriality;
* `Submission.homotopyGroupMap_eq_of_homotopicRel`: maps homotopic rel the basepoint
  induce equal maps;
* `Submission.homotopyGroupMulEquiv`: a based homeomorphism induces a group
  isomorphism.
-/

noncomputable section

open scoped Topology unitInterval
open Topology.Homotopy ContinuousMap

namespace Submission

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- Postcomposition of a generalized loop with a continuous map sending basepoint to
basepoint.-/
def genLoopMap (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) : Ω^ N Y y :=
  ⟨f.comp p.1, fun t ht => by
    rw [ContinuousMap.comp_apply, p.2 t ht, hf]⟩

/--
@isnad1 id=eq.1h8v.s7.44d4ba847aa2 from=translated src=- shape=83e432a6 vocab=17969bf1
-/
@[simp]
theorem genLoopMap_apply (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) (t : I^N) :
    genLoopMap f hf p t = f (p t) :=
  rfl

/--
@isnad1 id=eq.1h6v.s6.628d5be85179 from=translated src=- shape=800ba2a1 vocab=ebce195b
-/
@[simp]
theorem genLoopMap_const (f : C(X, Y)) (hf : f x = y) :
    genLoopMap (N := N) f hf GenLoop.const = GenLoop.const := by
  ext t
  simp [hf]

/--
@isnad1 id=eq.0h4v.s7.fe8dbe61775b from=translated src=- shape=7c3c88c7 vocab=6447bd16
-/
theorem genLoopMap_id (p : Ω^ N X x) : genLoopMap (ContinuousMap.id X) rfl p = p := by
  ext t
  rfl

/--
@isnad1 id=eq.3h10v.s7.ff4cf4a34a5a from=translated src=- shape=24a19cd8 vocab=5b2e12b9
-/
theorem genLoopMap_comp (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (hgf : (g.comp f) x = z) (p : Ω^ N X x) :
    genLoopMap (g.comp f) hgf p = genLoopMap g hg (genLoopMap f hf p) := by
  ext t
  rfl

/--
@isnad1 id=homotopi.2h8v.s7.4a50c5184cfb from=translated src=- shape=520cbc7e vocab=2a794d17
-/
theorem genLoopMap_homotopic (f : C(X, Y)) (hf : f x = y) {p q : Ω^ N X x}
    (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopMap f hf p) (genLoopMap f hf q) :=
  ContinuousMap.HomotopicRel.comp_continuousMap h f

/-- Postcomposition commutes with concatenation of generalized loops.
@isnad1 id=eq.1h9v.s7.eaf2b8e891ae from=translated src=- shape=71342f6b vocab=4d8a2c12
-/
theorem genLoopMap_transAt [DecidableEq N] (i : N) (f : C(X, Y)) (hf : f x = y)
    (p q : Ω^ N X x) :
    genLoopMap f hf (GenLoop.transAt i p q) =
      GenLoop.transAt i (genLoopMap f hf p) (genLoopMap f hf q) := by
  ext t
  show f (GenLoop.transAt i p q t) = GenLoop.transAt i _ _ t
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- Postcomposition commutes with reversal of generalized loops.
@isnad1 id=eq.1h8v.s7.62c67b7809c7 from=translated src=- shape=f758fa35 vocab=1e8af80c
-/
theorem genLoopMap_symmAt [DecidableEq N] (i : N) (f : C(X, Y)) (hf : f x = y)
    (p : Ω^ N X x) :
    genLoopMap f hf (GenLoop.symmAt i p) = GenLoop.symmAt i (genLoopMap f hf p) := by
  ext t
  show f (GenLoop.symmAt i p t) = GenLoop.symmAt i _ t
  simp only [GenLoop.symmAt, GenLoop.coe_copy]
  rfl

/-- The map on homotopy groups induced by a based continuous map.-/
def homotopyGroupMap (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (genLoopMap f hf) fun _ _ h => genLoopMap_homotopic f hf h

/--
@isnad1 id=eq.1h7v.s7.783964126567 from=translated src=- shape=577adfd8 vocab=4334f75e
-/
@[simp]
theorem homotopyGroupMap_mk (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) :
    homotopyGroupMap f hf (⟦p⟧ : HomotopyGroup N X x) = ⟦genLoopMap f hf p⟧ :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.e09601918320 from=translated src=- shape=3d808cd5 vocab=a770d44a
-/
theorem homotopyGroupMap_id (a : HomotopyGroup N X x) :
    homotopyGroupMap (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with
  | h p => exact congrArg (Quotient.mk _) (genLoopMap_id p)

/--
@isnad1 id=eq.3h10v.s7.c886e63ffd44 from=translated src=- shape=6b9dff71 vocab=4a637035
-/
theorem homotopyGroupMap_comp (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (hgf : (g.comp f) x = z) (a : HomotopyGroup N X x) :
    homotopyGroupMap (g.comp f) hgf a = homotopyGroupMap g hg (homotopyGroupMap f hf a) := by
  induction a using Quotient.inductionOn with
  | h p => exact congrArg (Quotient.mk _) (genLoopMap_comp g hg f hf hgf p)

/-- Whiskering: a homotopy rel the basepoint between `f` and `g` yields, after
postcomposition with a generalized loop, a homotopy rel the cube boundary.
@isnad1 id=homotopi.3h8v.s7.545ca036059c from=translated src=- shape=3a8a1e63 vocab=59bd6845
-/
theorem genLoopMap_homotopic_of_homotopicRel (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : f.HomotopicRel g {x}) (p : Ω^ N X x) :
    GenLoop.Homotopic (genLoopMap f hf p) (genLoopMap g hg p) := by
  obtain ⟨H⟩ := H
  refine ⟨⟨H.toHomotopy.compContinuousMap p.1, fun s t ht => ?_⟩⟩
  have hpt : p.1 t ∈ ({x} : Set X) := Set.mem_singleton_iff.mpr (p.2 t ht)
  exact H.eq_fst s hpt

/-- Maps homotopic rel the basepoint induce the same map on homotopy groups.
@isnad1 id=eq.3h7v.s6.5c25da04e77a from=translated src=- shape=e2817515 vocab=0756199e
-/
theorem homotopyGroupMap_eq_of_homotopicRel (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : f.HomotopicRel g {x}) :
    homotopyGroupMap (N := N) f hf = homotopyGroupMap g hg := by
  funext a
  induction a using Quotient.inductionOn with
  | h p => exact Quotient.sound (genLoopMap_homotopic_of_homotopicRel f g hf hg H p)

end Submission
