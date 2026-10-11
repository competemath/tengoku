import Tengoku.OpenaiMath.OAI.Combinatorics.EuclideanRamsey.CorrectionPaths

namespace OAI

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey

end EuclideanRamsey

namespace EuclideanRamsey

theorem full_affine_representative {s D : ℕ} (a : Fin s → Space D)
    (hs : 2 ≤ s) (ha : Function.Injective a) :
    ∃ d : ℕ,1 ≤ d ∧ ∃ b : Fin s → Space d,Function.Injective b ∧
      Congruent a b ∧ affineSpan ℝ (Set.range b)=⊤ := by
  classical
  let i₀ : Fin s := ⟨0,by omega⟩
  let i₁ : Fin s := ⟨1,by omega⟩
  let V : Submodule ℝ (Space D) := Submodule.span ℝ (Set.range (fun i => a i-a i₀))
  have hx (i : Fin s) : a i-a i₀∈V := Submodule.subset_span (Set.mem_range_self i)
  let x (i : Fin s) : V := ⟨a i-a i₀,hx i⟩
  have hxspan : Submodule.span ℝ (Set.range x)=⊤ :=
    (Submodule.span_range_subtype_eq_top_iff V hx).mpr rfl
  have hpos : 0<Module.finrank ℝ V := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨x i₁,?_⟩
    intro he
    have hv := congrArg (fun z : V => (z : Space D)) he
    change a i₁-a i₀=0 at hv
    have hi := ha (sub_eq_zero.mp hv)
    have hi' := congrArg Fin.val hi
    norm_num [i₀,i₁] at hi'
  let E := (stdOrthonormalBasis ℝ V).repr
  let b : Fin s → Space (Module.finrank ℝ V) := fun i => E (x i)
  have hbspan : Submodule.span ℝ (Set.range b)=⊤ := by
    change Submodule.span ℝ (Set.range (E.toLinearEquiv.toLinearMap ∘ x))=⊤
    rw [Set.range_comp,Submodule.span_image,hxspan,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr E.surjective
  have hb0 : b i₀=0 := by
    change E (x i₀)=0
    have hx0 : x i₀=0 := by apply Subtype.ext; exact sub_self _
    rw [hx0,map_zero]
  refine ⟨Module.finrank ℝ V,hpos, b,?_,?_,?_⟩
  · intro i j he
    have hx' := E.injective he
    have hv := congrArg (fun z : V => (z : Space D)) hx'
    change a i-a i₀=a j-a i₀ at hv
    exact ha (sub_left_injective hv)
  · intro i j
    change dist (E (x i)) (E (x j))=dist (a i) (a j)
    rw [dist_eq_norm,dist_eq_norm,← map_sub,LinearIsometryEquiv.norm_map]
    change ‖(a i-a i₀)-(a j-a i₀)‖=‖a i-a j‖
    rw [sub_sub_sub_cancel_right]
  · apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      ⟨b i₀,subset_affineSpan ℝ (Set.range b) (Set.mem_range_self i₀)⟩).mp
    rw [direction_affineSpan,vectorSpan_range_eq_span_range_vsub_right ℝ b i₀]
    simpa only [vsub_eq_sub,hb0,sub_zero] using hbspan
end EuclideanRamsey

namespace EuclideanRamsey

end EuclideanRamsey

end

end OAI
