import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Circle
import Tengoku.Seed.Analysis.Complex.Circle
import Tengoku.Seed.Topology.Homotopy.Lifting
import Tengoku.Seed.Analysis.Convex.Contractible
import Tengoku.Seed.Topology.Instances.RealVectorSpace
import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.Seed.Topology.Algebra.Module.LocallyConvex
import Tengoku.Seed.Analysis.LocallyConvex.Basic
import Tengoku.Seed.Analysis.LocallyConvex.WithSeminorms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddChar_exists_continuousLinearMap_fourierChar_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddChar_exists_continuousLinearMap_fourierChar_eq

set_option autoImplicit false

open scoped FourierTransform
open Real

/--
@isnad1 id=ex.1h2v.s8.e6547df13f29 from=translated src=- shape=7e7ae69f vocab=01c16826
-/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E Circle) (hχ : Continuous χ) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = 𝐞 (l x) := by

  obtain ⟨F, ⟨hF0, hFlift⟩, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts (⟨χ, hχ⟩ : C(E, Circle)) 0 0
      (by simp)
  have hF : ∀ x, Circle.exp (F x) = χ x := fun x => congrFun hFlift x

  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    let G : C(E, ℝ) := ⟨fun z => F (z + y) - F y, by fun_prop⟩
    have hG : G = F := by
      refine huniq G ⟨by simp [G], ?_⟩
      funext z
      simp only [Function.comp_apply, ContinuousMap.coe_mk, G, Circle.exp_sub, hF,
        AddChar.map_add_eq_mul, mul_div_cancel_right]
    have := congrArg (fun (H : C(E, ℝ)) => H x) hG
    simp only [G, ContinuousMap.coe_mk] at this
    linarith

  let Fhom : E →+ ℝ := { toFun := F, map_zero' := hF0, map_add' := hadd }
  let l₀ : E →L[ℝ] ℝ := Fhom.toRealLinearMap F.continuous
  refine ⟨(2 * π)⁻¹ • l₀, fun x => ?_⟩
  rw [Real.fourierChar_apply', smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]
  exact (hF x).symm
