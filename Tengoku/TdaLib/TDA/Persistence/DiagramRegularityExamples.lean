import Tengoku.TdaLib.TDA.Persistence.DiagramRegularity
import Tengoku.TdaLib.TDA.Persistence.DiagramCalculusExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Boundary cases for uniform regularity and diagonal restrictions. -/

namespace TDA.Persistence
open scoped ContDiff

/-- The signed endpoint loss is regular through every finite presentation at
every order, including zero, finite orders, and the smooth index `∞`.
@isnad1 id=crthroug.0h2v.s3.3483b0e1c458 from=translated src=- shape=4e893b2d vocab=2c6d6e16
-/
theorem signedFiniteEndpointDifference_cr_all (r : ℕ∞ω) (D : Diagram ℝ) :
    CrThroughAllRepresentatives r signedFiniteEndpointDifference D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, ?_⟩
  apply contDiffOn_univ.mpr
  have hs : ContDiff ℝ r (fun w : DiagramCoordinates m n =>
      ∑ i : Fin m, ((w.1 i).2 - (w.1 i).1)) := by
    apply ContDiff.sum
    intro i _
    fun_prop
  simpa [Function.comp_def, signedFiniteEndpointDifference_orderedQ] using hs

/-- The zero-dimensional ordered coordinate space has a constant lift at
every regularity index.-/
def emptyDiagramCrLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ∞ω) :
    LocalCrDiagramLift r (fun _ : E => orderedQ 0 0 (Fin.elim0, Fin.elim0)) 0 0 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := fun _ => (Fin.elim0, Fin.elim0)
  factorization := by intro _ _; rfl
  regular := contDiff_const.contDiffOn

/-- Two essential coordinates may have the same moving real birth value;
the finite block is empty.-/
def repeatedEssentialCoordinates (t : ℝ) : DiagramCoordinates 0 2 :=
  (Fin.elim0, fun _ => t)

/--
@isnad1 id=contdiff.0h1v.s8.7a79c6e741ea from=translated src=- shape=90c51f56 vocab=ea18f36e
-/
theorem repeatedEssentialCoordinates_contDiff (r : ℕ∞ω) :
    ContDiff ℝ r repeatedEssentialCoordinates := by
  apply ContDiff.prodMk
  · exact contDiff_const
  · apply contDiff_pi.mpr
    intro i
    exact contDiff_id

/--
@isnad1 id=eq.0h1v.s6.7afe2c10b866 from=translated src=- shape=6e76914a vocab=f68e3ba2
-/
theorem repeatedEssentialCoordinates_equal_births (t : ℝ) :
    (repeatedEssentialCoordinates t).2 0 =
      (repeatedEssentialCoordinates t).2 1 := rfl

/-- At order zero the scalar conclusion gives continuity, with no derivative
claim, even for an empty coordinate block.
@isnad1 id=ex.1h2v.s7.735910e1c5f8 from=translated src=- shape=5c9dec75 vocab=dacca79e
-/
theorem emptyDiagram_scalar_continuous (V : Diagram ℝ → ℝ) (x : ℝ)
    (hV : CrThroughAllRepresentatives 0 V
      (orderedQ 0 0 (Fin.elim0, Fin.elim0))) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      ContinuousOn (fun _ : ℝ => V (orderedQ 0 0 (Fin.elim0, Fin.elim0))) U := by
  obtain ⟨U, hU, hx, _, hc⟩ := localLift_scalar_continuousOn
    (fun _ : ℝ => orderedQ 0 0 (Fin.elim0, Fin.elim0)) V 0 0
    (emptyDiagramCrLift 0) x (Set.mem_univ x) hV
  exact ⟨U, hU, hx, hc⟩

/-- The absolute endpoint loss restricts to the constant zero function on
a diagonal coordinate line.
@isnad1 id=eq.0h1v.s11.a5b6cc4d0ec1 from=translated src=- shape=aaead794 vocab=9bd73c0c
-/
theorem absoluteLoss_diagonal_restriction (t : ℝ) :
    absoluteFiniteEndpointDifference
      (orderedQ 1 0 (diagonalInsertion 0 1 0
        ((Fin.elim0, Fin.elim0), fun _ => t))) = 0 := by
  have h : orderedQ 1 0 (diagonalInsertion 0 1 0
      ((Fin.elim0, Fin.elim0), fun _ => t)) =
      orderedQ 0 0 (Fin.elim0, Fin.elim0) := by
    simpa using orderedQ_diagonalInsertion 0 1 0
      ((Fin.elim0, Fin.elim0), fun _ => t)
  rw [h]
  simp [absoluteFiniteEndpointDifference_orderedQ]

/-- Smoothness of that restriction does not certify `C¹` on an ambient
neighborhood of the diagonal representative.
@isnad1 id=and.0h0v.s11.b4af29b25a93 from=translated src=- shape=9952e42c vocab=1bf507af
-/
theorem absoluteLoss_diagonal_not_ambient_c1 :
    (ContDiff ℝ (∞ : ℕ∞ω) (fun t : ℝ =>
      absoluteFiniteEndpointDifference
        (orderedQ 1 0 (diagonalInsertion 0 1 0
          ((Fin.elim0, Fin.elim0), fun _ => t))))) ∧
      ¬ CrThroughAllRepresentatives 1 absoluteFiniteEndpointDifference
        (orderedQ 0 0 (Fin.elim0, Fin.elim0)) := by
  constructor
  · have h : (fun t : ℝ => absoluteFiniteEndpointDifference
        (orderedQ 1 0 (diagonalInsertion 0 1 0
          ((Fin.elim0, Fin.elim0), fun _ => t)))) = fun _ => 0 := by
      funext t
      exact absoluteLoss_diagonal_restriction t
    rw [h]
    exact contDiff_const
  · exact absoluteFiniteEndpointDifference_not_c1_empty

end TDA.Persistence
