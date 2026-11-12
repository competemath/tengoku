import Tengoku.AbelFormalization.AbelFormalization.RegularZeroGraphLift
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Substitute the exponential of the final exponent into a lifted system.-/
def exponentialGraphSubstitution (Ftilde : E × ℝ → F) (g : E → ℝ) : E → F :=
  graphSubstitution Ftilde (fun x ↦ Real.exp (g x))

/-- The square graph system used to compare regularity before and after
introducing the last exponential as a variable.-/
def exponentialGraphLiftSystem (Ftilde : E × ℝ → F) (g : E → ℝ) :
    E × ℝ → F × ℝ :=
  graphLiftSystem Ftilde (fun x ↦ Real.exp (g x))

/--
@isnad1 id=eq.0h5v.s5.5856b90c52a7 from=translated src=- shape=601a1039 vocab=0207afbe
-/
@[simp]
theorem exponentialGraphSubstitution_apply
    (Ftilde : E × ℝ → F) (g : E → ℝ) (x : E) :
    exponentialGraphSubstitution Ftilde g x = Ftilde (x, Real.exp (g x)) :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.899d60549069 from=translated src=- shape=cce297dc vocab=f5aac6ed
-/
@[simp]
theorem exponentialGraphLiftSystem_apply
    (Ftilde : E × ℝ → F) (g : E → ℝ) (p : E × ℝ) :
    exponentialGraphLiftSystem Ftilde g p =
      (Ftilde p, p.2 - Real.exp (g p.1)) :=
  rfl

/-- Regular-zero membership is preserved by adjoining the exponential graph
equation.
@isnad1 id=iff.2h6v.s8.92fee3084dbf from=translated src=- shape=f8a1c184 vocab=26e91d6c
-/
theorem mem_regularZeroSet_exponentialGraphLift_iff
    {Omega : Set E} {Ftilde : E × ℝ → F} {g : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : DifferentiableAt ℝ g x) :
    x ∈ regularZeroSet Omega (exponentialGraphSubstitution Ftilde g) ↔
      (x, Real.exp (g x)) ∈ regularZeroSet
        ((fun p : E × ℝ ↦ p.1) ⁻¹' Omega)
        (exponentialGraphLiftSystem Ftilde g) := by
  apply mem_regularZeroSet_graphLift_iff hF
  fun_prop

/-- The logarithmic comparison function; it is used only on the positive
half-space, never as an equation in the lower exponential level.-/
def exponentialGraphComparison (g : E → ℝ) : E × ℝ → ℝ :=
  fun p ↦ Real.log p.2 - g p.1

/--
@isnad1 id=eq.0h3v.s5.0c31f33b9985 from=translated src=- shape=dc6b8ed7 vocab=d9cbafdb
-/
@[simp]
theorem exponentialGraphComparison_on_graph (g : E → ℝ) (x : E) :
    exponentialGraphComparison g (x, Real.exp (g x)) = 0 := by
  simp [exponentialGraphComparison]

/--
@isnad1 id=iff.1h3v.s5.60cc7e36d4f6 from=translated src=- shape=a877f5ac vocab=6d9bb09e
-/
theorem exponentialGraphComparison_eq_zero_iff
    (g : E → ℝ) {p : E × ℝ} (hp : 0 < p.2) :
    exponentialGraphComparison g p = 0 ↔ p.2 = Real.exp (g p.1) := by
  constructor
  · intro h
    have hlog : Real.log p.2 = g p.1 := sub_eq_zero.mp h
    calc
      p.2 = Real.exp (Real.log p.2) := (Real.exp_log hp).symm
      _ = Real.exp (g p.1) := congrArg Real.exp hlog
  · intro h
    rw [exponentialGraphComparison, h, Real.log_exp, sub_self]

/--
@isnad1 id=injectiv.0h2v.s5.b476b023207d from=translated src=- shape=bf7b0858 vocab=2fc526da
-/
theorem exponentialGraphLift_injective (g : E → ℝ) :
    Function.Injective (fun x ↦ (x, Real.exp (g x))) := by
  intro x y h
  exact congrArg Prod.fst h

/-- Finiteness descends along the injective exponential graph lift.
@isnad1 id=finite.3h5v.s8.03f6ebce6f75 from=translated src=- shape=42970d2e vocab=825becc8
-/
theorem finite_regularZeroSet_of_finite_exponentialGraphLift
    {Omega : Set E} {Ftilde : E × ℝ → F} {g : E → ℝ}
    (hF : ∀ x, DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : Differentiable ℝ g)
    (hfinite : (regularZeroSet
      ((fun p : E × ℝ ↦ p.1) ⁻¹' Omega)
      (exponentialGraphLiftSystem Ftilde g)).Finite) :
    (regularZeroSet Omega (exponentialGraphSubstitution Ftilde g)).Finite := by
  apply Set.Finite.of_finite_image (f := fun x ↦ (x, Real.exp (g x)))
  · exact hfinite.subset fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := hy
      exact (mem_regularZeroSet_exponentialGraphLift_iff
        (hF x) (hg x)).mp hx
  · exact (exponentialGraphLift_injective g).injOn

end AbelFormalization
