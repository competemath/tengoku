import Tengoku.Seed.Topology.Algebra.Valued.WithVal
import Tengoku.Seed.Topology.Algebra.UniformRing
import Tengoku.Seed.Topology.Algebra.UniformMulAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/--
@isnad1 id=continuo.0h3v.s6.99adb3aca167 from=translated src=- shape=eb06fcf3 vocab=7d25fc9b
-/
instance continuousConstSMul_withVal : ContinuousConstSMul K (WithVal v) :=
  ⟨fun a => continuous_const_mul (WithVal.toVal v a)⟩

/--
@isnad1 id=uniformc.0h3v.s6.185f6ac252c0 from=translated src=- shape=eb06fcf3 vocab=9d48d4c1
-/
instance uniformContinuousConstSMul_withVal : UniformContinuousConstSMul K (WithVal v) :=
  uniformContinuousConstSMul_of_continuousConstSMul K (WithVal v)

instance algebraCompletion : Algebra K v.Completion := inferInstance

/--
@isnad1 id=eq.0h4v.s9.7e39fc224e27 from=translated src=- shape=bb8d1170 vocab=8bcd89ab
-/
@[simp] theorem algebraMap_completion_apply (a : K) : algebraMap K v.Completion a = (a : v.Completion) := rfl

/--
@isnad1 id=eq.0h5v.s9.59f7f3261c94 from=translated src=- shape=a290093d vocab=f21531bd
-/
theorem smul_completion_def (a : K) (x : v.Completion) : a • x = (a : v.Completion) * x :=
  Algebra.smul_def a x

end Valuation

end
