import Tengoku.OpenaiMath.OAI.Combinatorics.EuclideanRamsey.CornerGroup

namespace OAI

universe uModule uColor

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
open Filter
open scoped BigOperators
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

lemma exists_ultra_color {M : Type uModule} {κ : Type uColor} [Finite κ] (U : Ultrafilter M) (c : M → κ) :
    ∃ k,{x | c x=k}∈U := by
  apply Ultrafilter.eventually_exists_iff.mp
  exact Filter.Eventually.of_forall (fun x => ⟨c x,rfl⟩)
noncomputable def ultraColor {M : Type uModule} {κ : Type uColor} [Finite κ] (c : M → κ) (U : Ultrafilter M) : κ :=
  (exists_ultra_color U c).choose
lemma ultraColor_spec {M : Type uModule} {κ : Type uColor} [Finite κ] (c : M → κ) (U : Ultrafilter M) :
    {x | c x=ultraColor c U}∈U := (exists_ultra_color U c).choose_spec

lemma exists_corner_map : ∃ (p : Ultrafilter Strings) (Ψ : LetterGroup →ₙ* Ultrafilter Strings),
    ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p := by
  let := ultrafilterMonoid (M:=Strings)
  obtain ⟨p,hp,hi⟩ := exists_group_corner (S:=Ultrafilter Strings) Ultrafilter.continuous_mul_left
  let := Corner.group hp hi
  let letter (z : FiniteEuclidean) : Corner p :=
    ⟨p*(pure (FreeMonoid.of z))*p,by
      constructor
      · simp only [← mul_assoc,hp]
      · simp only [mul_assoc,hp]⟩
  let ψ : LetterGroup →* Corner p := FreeGroup.lift letter
  let v : Corner p →ₙ* Ultrafilter Strings := { toFun := Subtype.val, map_mul' _ _ := rfl }
  refine ⟨p,v.comp ψ.toMulHom,?_⟩
  intro z
  change (ψ (FreeGroup.of z)).val=_
  exact congrArg (fun x : Corner p => x.val) (FreeGroup.lift_apply_of (f:=letter) (x:=z))

end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open Filter
open scoped BigOperators
noncomputable def truncate (d : ℕ) (x : FiniteEuclidean) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => coords x i)

end FiniteEuclidean

end EuclideanRamsey

end

end OAI
