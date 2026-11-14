import Tengoku.TdaLib.TDA.Reeb.Components
import Tengoku.Seed.Topology.Homotopy.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Path components of homotopic maps and homotopy equivalences

Homotopic continuous maps induce the same map on path components
(`componentMap_eq_of_homotopic`): the track of a point under the homotopy is a path between its
two images. Consequently a homotopy equivalence `A ≃ₕ B` induces an equivalence
`ZerothHomotopy A ≃ ZerothHomotopy B` (`componentEquivOfHomotopyEquiv`) whose forward map is
`componentMap` of the forward map of the homotopy equivalence. No hypothesis on the spaces is
used.
-/

namespace TDA.Reeb

section components

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- Homotopic maps induce the same map on path components.
@isnad1 id=eq.1h4v.s5.276101b74284 from=translated src=- shape=51f25c5f vocab=2a0ea681
-/
theorem componentMap_eq_of_homotopic {f g : C(A, B)} (h : f.Homotopic g) :
    componentMap f = componentMap g := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk x =>
    obtain ⟨H⟩ := h
    exact ZerothHomotopy.sound
      { toFun := fun s => H (s, x)
        continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
        source' := H.apply_zero x
        target' := H.apply_one x }

/-- The path-component bijection of a homotopy equivalence.-/
def componentEquivOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv A B) :
    ZerothHomotopy A ≃ ZerothHomotopy B where
  toFun := componentMap e.toFun
  invFun := componentMap e.invFun
  left_inv c := by
    have := componentMap_eq_of_homotopic e.left_inv
    rw [componentMap_comp, componentMap_id] at this
    exact congrFun this c
  right_inv c := by
    have := componentMap_eq_of_homotopic e.right_inv
    rw [componentMap_comp, componentMap_id] at this
    exact congrFun this c

/--
@isnad1 id=eq.0h4v.s6.d11fdc334294 from=translated src=- shape=39df202e vocab=eac78b76
-/
@[simp] theorem componentEquivOfHomotopyEquiv_mk (e : ContinuousMap.HomotopyEquiv A B) (a : A) :
    componentEquivOfHomotopyEquiv e (ZerothHomotopy.mk a) = ZerothHomotopy.mk (e.toFun a) :=
  rfl

end components

end TDA.Reeb
