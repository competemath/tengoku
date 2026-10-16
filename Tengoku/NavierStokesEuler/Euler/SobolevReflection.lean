import Tengoku.NavierStokesEuler.Euler.GradientReflection

/-! Joint reflection on the actual complete cylinder Sobolev spaces. -/

noncomputable section

namespace EulerSobolevReflection

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolevSpace
  EulerCylinderReflection EulerGradientReflection EulerCylinderSobolev
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Reflection of a derivative array includes the sign of each derivative word. -/
def reflectionArrayOperator (q : ℕ) :
    SobolevSpace period q →L[ℝ] (SobolevWord q → LiftL2 period) :=
  ContinuousLinearMap.pi fun w => ((-1 : ℝ) ^ w.1.val) •
    ((reflection period).toContinuousLinearMap.comp (wordOperator period w))

/-- The signed derivative array satisfies the actual strong-derivative compatibility. -/
theorem reflectionArray_mem (q : ℕ) (u : SobolevSpace period q) :
    reflectionArrayOperator period q u ∈ (sobolevSubspace period q).toSubmodule := by
  apply ClosedSubmodule.mem_iInf.mpr
  intro e
  have hd := word_hasDerivAt period u e.1.isLt e.2.1 e.2.2
  have hr := (reflection_hasDerivAt period (standardDirection e.2.2) hd).const_smul ((-1 : ℝ) ^ e.1.val)
  change HasDerivAt (fun t => translation period (translationPath period (standardDirection e.2.2) t)
    (((-1 : ℝ) ^ e.1.val) • reflection period (u.val (edgeParent e))))
    (((-1 : ℝ) ^ (e.1.val + 1)) • reflection period (u.val (edgeChild e))) 0
  convert! hr using 1
  · funext t
    rw [map_smul]
    rfl
  · simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]
    rfl

/-- Joint pullback reflection as a genuine bounded map of the complete Sobolev space. -/
def sobolevReflection (q : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  (reflectionArrayOperator period q).codRestrict (sobolevSubspace period q).toSubmodule
    (reflectionArray_mem period q)

/-- The derivative coordinates of reflection have exactly the alternating signs. -/
@[simp] theorem sobolevReflection_apply {q : ℕ} (u : SobolevSpace period q) (w : SobolevWord q) :
    (sobolevReflection period q u).val w = (-1 : ℝ) ^ w.1.val • reflection period (u.val w) := rfl

/-- The underlying field is the actual L² pullback by joint negation. -/
@[simp] theorem value_sobolevReflection {q : ℕ} (u : SobolevSpace period q) :
    value period (sobolevReflection period q u) = reflection period (value period u) := by
  change (-1 : ℝ) ^ 0 • reflection period (value period u) = _
  simp

/-- Joint reflection is involutive on the complete Sobolev space. -/
@[simp] theorem sobolevReflection_involutive {q : ℕ} (u : SobolevSpace period q) :
    sobolevReflection period q (sobolevReflection period q u) = u := by
  apply value_injective period
  rw [value_sobolevReflection, value_sobolevReflection, reflection_involutive]

/-- The symmetry whose fixed points are odd velocity fields. -/
def oddReflection (q : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  -sobolevReflection period q

/-- Odd reflection is represented by minus the field at the reflected point. -/
@[simp] theorem oddReflection_apply {q : ℕ} (u : SobolevSpace period q) :
    oddReflection period q u = -sobolevReflection period q u := rfl

end EulerSobolevReflection
