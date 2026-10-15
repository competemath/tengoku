import Tengoku.NavierStokesEuler.Euler.BoundedFlowContinuity
import Tengoku.NavierStokesEuler.Euler.EulerProof

/-! A lifted flow tangent to the oscillating graph gives an actual
three-dimensional flow, with inverse and the projected differential
equation. Graph invariance follows from a conserved linear functional. -/

noncomputable section

namespace EulerGraphInvariantFlow

open Set InnerProductSpace ContinuousLinearMap EulerLiftedGradientSpace EulerMetricTransport

def graphLinear (k : ℝ) (m : Vector3) : Vector3 →L[ℝ] LiftTangent :=
  (ContinuousLinearMap.id ℝ Vector3).prod (k • toDual ℝ Vector3 m)

/--
@isnad1 id=eq.0h3v.s9.49b92c560a1a from=translated src=- shape=d5a31cae vocab=b395660b
-/
@[simp] theorem graphLinear_apply (k : ℝ) (m x : Vector3) :
    graphLinear k m x = (x,k*inner ℝ m x) := rfl

def graphConstraint (k : ℝ) (m : Vector3) : LiftTangent →L[ℝ] ℝ :=
  snd ℝ Vector3 ℝ - k • (toDual ℝ Vector3 m).comp (fst ℝ Vector3 ℝ)

/--
@isnad1 id=eq.0h3v.s9.4315e9bd52c0 from=translated src=- shape=39100114 vocab=86ef14af
-/
@[simp] theorem graphConstraint_apply (k : ℝ) (m : Vector3) (z : LiftTangent) :
    graphConstraint k m z = z.2-k*inner ℝ m z.1 := rfl

/--
@isnad1 id=eq.0h3v.s10.b55fca6fbda3 from=translated src=- shape=3b2ec663 vocab=b692450f
-/
@[simp] theorem graphConstraint_graph (k : ℝ) (m x : Vector3) :
    graphConstraint k m (graphLinear k m x)=0 := by simp

/--
@isnad1 id=eq.1h4v.s9.67122b131555 from=translated src=- shape=9f1ea8c9 vocab=3ddaef8a
-/
theorem graphConstraint_transport (k κ : ℝ) (hk : k*κ=1) (m v : Vector3) :
    graphConstraint k m (transportDirection κ m v)=0 := by
  change inner ℝ m v-k*inner ℝ m (κ • v)=0
  rw [inner_smul_right]
  simp only [← mul_assoc,hk,one_mul,sub_self]

variable (k : ℝ) (m : Vector3) (V : EulerBoundedLipschitzFlow.Data LiftTangent)
  (hV : ∀ t z, graphConstraint k m (V.velocity t z)=0)

include hV in
/--
@isnad1 id=eq.1h6v.s10.05ce4706a4e8 from=translated src=- shape=579f0deb vocab=37f6ffc5
-/
theorem graphConstraint_flow (s t : ℝ) (z : LiftTangent) :
    graphConstraint k m (V.flow s t z)=graphConstraint k m z := by
  have hd (r : ℝ) : HasDerivAt (fun q => graphConstraint k m (V.flow s q z)) 0 r := by
    have h := (graphConstraint k m).hasFDerivAt.comp_hasDerivAt r (V.flow_hasDerivAt s r z)
    rw [hV] at h
    convert! h using 1
  have he := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t s
  simpa only [V.flow_initial] using he

def graphFlow (s t : ℝ) (x : Vector3) : Vector3 := (V.flow s t (graphLinear k m x)).1

include hV in
/--
@isnad1 id=eq.1h6v.s11.ab75f195599d from=translated src=- shape=cf9a871f vocab=5dd5de6f
-/
theorem graphFlow_invariant (s t : ℝ) (x : Vector3) :
    V.flow s t (graphLinear k m x)=graphLinear k m (graphFlow k m V s t x) := by
  have he := graphConstraint_flow k m V hV s t (graphLinear k m x)
  rw [graphConstraint_graph,graphConstraint_apply,sub_eq_zero] at he
  apply Prod.ext
  · rfl
  · exact he

/--
@isnad1 id=eq.0h5v.s6.5d9bbec67c10 from=translated src=- shape=cccbd057 vocab=8352df76
-/
@[simp] theorem graphFlow_initial (s : ℝ) (x : Vector3) : graphFlow k m V s s x=x := by
  simp [graphFlow]

include hV in
/--
@isnad1 id=eq.1h6v.s9.cf92550d56b1 from=translated src=- shape=816dfa0e vocab=80e88a76
-/
theorem graphFlow_inverse (s t : ℝ) (x : Vector3) :
    graphFlow k m V t s (graphFlow k m V s t x)=x := by
  change (V.flow t s (graphLinear k m (graphFlow k m V s t x))).1=x
  rw [← graphFlow_invariant k m V hV,V.flow_inverse]
  rfl

include hV in
/--
@isnad1 id=hasderiv.1h6v.s10.927ca977910f from=translated src=- shape=d4408e47 vocab=6bdb88ef
-/
theorem graphFlow_hasDerivAt (s t : ℝ) (x : Vector3) :
    HasDerivAt (fun r => graphFlow k m V s r x)
      (V.velocity t (graphLinear k m (graphFlow k m V s t x))).1 t := by
  have hd := (V.flow_hasDerivAt s t (graphLinear k m x)).fst
  rwa [graphFlow_invariant k m V hV] at hd

/--
@isnad1 id=continuo.0h5v.s7.72ad5155f2b1 from=translated src=- shape=b88ac6ee vocab=abbbc5ca
-/
theorem graphFlow_continuous (s t : ℝ) : Continuous (graphFlow k m V s t) :=
  continuous_fst.comp ((V.flowHomeomorph s t).continuous.comp (graphLinear k m).continuous)

/--
@isnad1 id=continuo.0h3v.s7.b5747d08e98f from=translated src=- shape=39c5c305 vocab=0a00bfff
-/
theorem graphFlow_forward_joint_continuous :
    Continuous (fun r : ℝ × Vector3 => graphFlow k m V 0 r.1 r.2) :=
  continuous_fst.comp (V.forward_joint_continuous.comp
    (continuous_fst.prodMk ((graphLinear k m).continuous.comp continuous_snd)))

/--
@isnad1 id=continuo.0h3v.s7.fa6d409b7d6d from=translated src=- shape=e8ce829c vocab=0a00bfff
-/
theorem graphFlow_backward_joint_continuous :
    Continuous (fun r : ℝ × Vector3 => graphFlow k m V r.1 0 r.2) :=
  continuous_fst.comp (V.backward_joint_continuous.comp
    (continuous_fst.prodMk ((graphLinear k m).continuous.comp continuous_snd)))

end EulerGraphInvariantFlow
