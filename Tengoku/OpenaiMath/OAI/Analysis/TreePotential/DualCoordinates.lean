import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.StartComponent

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
namespace ForestCoordinates
open scoped Classical
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]

end ForestCoordinates

/-- Hilbert coefficients of every finite-height linear-cost dual functional,
with its genuine continuous topology. Its norm is p_n, not the Hilbert norm. -/
def blockDualHilbertEquiv (n : ℕ) : StrongDual ℝ (LinearBlock n) ≃L[ℝ] TreeHilbert n :=
  (dualTransport (linearBlockHilbertEquiv n)).trans
    (InnerProductSpace.toDual ℝ (TreeHilbert n)).symm.toContinuousLinearEquiv

abbrev LinearDualPieces := HilbertSum (fun n : ℕ => StrongDual ℝ (LinearBlock (n+1)))

def linearDualCoefficients (φ : StrongDual ℝ LinearOuter) (n : ℕ) : TreeHilbert (n+1) :=
  blockDualHilbertEquiv (n+1) (dualPieces (fun n => LinearBlock (n+1)) φ n)

end BoundedTreePotentials

namespace BoundedTreePotentials.Segments
open scoped Classical

/-- All component coordinates of a literal finite-cost forest vector belong
to the full finite-height Hilbert coordinate set. -/
theorem start_component_coordinates_mem (x : StartSpace) (n : ℕ) :
    Memℓp (fun v : BlockNode n => x.val (componentEmbedding n v)) 2 := by
  have he : (fun v : BlockNode n => x.val (componentEmbedding n v))=
      (fun v => startBlockHilbertEquiv n (startPiecesEquiv x n) v) := by
    funext v
    rw [startBlockHilbertEquiv_coordinate,startPieces_coordinate]
  rw [he]
  exact (startBlockHilbertEquiv n (startPiecesEquiv x n)).property

/-- Equality of the literal forest infimum with the outer Hilbert norm of
the literal finite-height infima, not merely equivalence of these norms. -/
theorem start_outer_norm_sq (x : StartSpace) :
    ‖x‖^2=∑' n,(literalBlockStartNorm n (fun v => x.val (componentEmbedding n v)))^2 := by
  have hh := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (startPiecesEquiv x)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,startPiecesEquiv.norm_map] at hh
  rw [hh]
  apply tsum_congr
  intro n
  rw [startBlock_norm_eq_infimum]
  congr 2
  funext v
  exact startPieces_coordinate x n v

/-- The range of countable finite-cost segment representations is exactly the outer ℓ₂ sum
of Hilbert coordinate sets equipped with their literal infimal component norms. -/

theorem start_coordinate_characterization (z : Node → ℝ) :
    (∃ x : StartSpace,x.val=z) ↔
      (∀ n,Memℓp (fun v : BlockNode n => z (componentEmbedding n v)) 2) ∧
      Summable (fun n => (literalBlockStartNorm n (fun v => z (componentEmbedding n v)))^2) := by
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨start_component_coordinates_mem x,?_⟩
    have hh := (lp.hasSum_norm (p := 2) (by norm_num) (startPiecesEquiv x)).summable
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hh
    have he : (fun n => ‖startPiecesEquiv x n‖^2)=
        (fun n => (literalBlockStartNorm n (fun v => x.val (componentEmbedding n v)))^2) := by
      funext n
      rw [startBlock_norm_eq_infimum]
      congr 2
      funext v
      exact startPieces_coordinate x n v
    rwa [he] at hh
  · rintro ⟨hz,hs⟩
    let b : (n : ℕ) → StartBlock n := fun n =>
      (startBlockHilbertEquiv n).symm ⟨fun v => z (componentEmbedding n v),hz n⟩
    have hb : ∀ n,‖b n‖=literalBlockStartNorm n (fun v => z (componentEmbedding n v)) := by
      intro n
      exact hilbert_coordinates_literal_norm n _
    have hmem : Memℓp b 2 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,hb] using hs
    let B : HilbertSum StartBlock := ⟨b,hmem⟩
    refine ⟨startPiecesEquiv.symm B,?_⟩
    funext v
    obtain ⟨n,v⟩ := v
    change (startPiecesEquiv.symm B).val (componentEmbedding n v)=z (componentEmbedding n v)
    rw [← startPieces_coordinate,startPiecesEquiv.apply_symm_apply]
    change startBlockCoordinate n (b n) v=_
    rw [← startBlockHilbertEquiv_coordinate]
    exact congrFun (congrArg Subtype.val ((startBlockHilbertEquiv n).apply_symm_apply
      (⟨fun v => z (componentEmbedding n v),hz n⟩ : CoordinateHilbert (BlockNode n)))) v

/-- Density refers to finite node support, not merely to finite block support. -/
theorem start_finite_support_dense : Dense {x : StartSpace | (Function.support x.val).Finite} := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨E,hE,he⟩ := start_head_approx x hε
  refine ⟨startHead E x,?_,?_⟩
  · apply E.finite_toSet.subset
    intro v hv
    by_contra hnot
    have hvE : v ∉ E := hnot
    exact hv (by rw [startHead_coordinate,ite_eq_right hvE])
  · simpa only [dist_eq_norm] using he

end BoundedTreePotentials.Segments

end

end OAI
