import Tengoku.Seed.Topology.Algebra.Valued.WithVal
import Tengoku.Seed.Topology.Algebra.UniformRing
import Tengoku.Seed.Topology.Algebra.UniformMulAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

instance continuousConstSMul_withVal : ContinuousConstSMul K (WithVal v) :=
  ⟨fun a => continuous_const_mul (WithVal.toVal v a)⟩

instance uniformContinuousConstSMul_withVal : UniformContinuousConstSMul K (WithVal v) :=
  uniformContinuousConstSMul_of_continuousConstSMul K (WithVal v)

instance algebraCompletion : Algebra K v.Completion := inferInstance

@[simp] theorem algebraMap_completion_apply (a : K) : algebraMap K v.Completion a = (a : v.Completion) := rfl

theorem smul_completion_def (a : K) (x : v.Completion) : a • x = (a : v.Completion) * x :=
  Algebra.smul_def a x

end Valuation

end
