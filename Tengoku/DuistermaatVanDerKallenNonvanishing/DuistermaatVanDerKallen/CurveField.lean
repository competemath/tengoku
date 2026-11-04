import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentGeometry
import Tengoku.Seed.Topology.ContinuousMap.Units
import Tengoku.Seed.Topology.ContinuousMap.Compact
import Tengoku.Seed.Topology.ContinuousMap.Star

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Smooth functional calculus for the normalized-gradient field on spaces of
continuous curves. This is infrastructure for smooth ODE dependence, not a
smooth-dependence theorem for the solutions themselves. -/

open scoped BigOperators ComplexConjugate Topology

namespace DuistermaatVanDerKallen

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Inversion in the Banach algebra of continuous scalar functions is smooth
at every nowhere-zero function.
@isnad1 id=contdiff.1h3v.s8.06afa1069213 from=translated src=- shape=cbac5e1c vocab=31f89b45
-/
theorem curveInverse_contDiffAt {𝕜 : Type*} [RCLike 𝕜] {u : C(X, 𝕜)}
    (hu : ∀ t, u t ≠ 0) : ContDiffAt ℝ ⊤ (Ring.inverse : C(X, 𝕜) → C(X, 𝕜)) u := by
  obtain ⟨v, rfl⟩ := (ContinuousMap.isUnit_iff_forall_ne_zero u).2 hu
  exact contDiffAt_ringInverse ℝ v

omit [CompactSpace X] in
/-- At a nowhere-zero curve the Banach-algebra inverse evaluates to the usual
scalar inverse. No pointwise identity is asserted at nonunits.
@isnad1 id=eq.1h4v.s8.efa6d44a1700 from=translated src=- shape=a8ee633e vocab=2bc6b595
-/
theorem curveInverse_apply {𝕜 : Type*} [RCLike 𝕜] {u : C(X, 𝕜)}
    (hu : ∀ t, u t ≠ 0) (t : X) : Ring.inverse u t = (u t)⁻¹ := by
  obtain ⟨v, rfl⟩ := (ContinuousMap.isUnit_iff_forall_ne_zero u).2 hu
  have h := congrArg (fun w : C(X, 𝕜) => w t) v.mul_inv
  simpa only [Ring.inverse_unit, ContinuousMap.mul_apply, ContinuousMap.one_apply] using
    (eq_inv_of_mul_eq_one_right h)

/-- Pointwise squared complex norm, expressed by polynomial and real-linear
operations on the Banach algebra.-/
def curveNormSq (u : C(X, ℂ)) : C(X, ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ X) ((Complex.conjCLE.toContinuousLinearMap.compLeftContinuous ℝ X u) * u)

omit [CompactSpace X] in
/--
@isnad1 id=eq.0h3v.s6.feb3ce74e895 from=translated src=- shape=67c5b7da vocab=1d69bb49
-/
theorem curveNormSq_apply (u : C(X, ℂ)) (t : X) :
    curveNormSq u t = Complex.normSq (u t) := by
  simp [curveNormSq, Complex.normSq, Complex.mul_re, Complex.conj_re, Complex.conj_im]

/--
@isnad1 id=contdiff.0h1v.s7.ea6c5e86fcee from=translated src=- shape=20a0095e vocab=833e75e9
-/
theorem curveNormSq_contDiff : ContDiff ℝ ⊤ (curveNormSq : C(X, ℂ) → C(X, ℝ)) := by
  exact (Complex.reCLM.compLeftContinuous ℝ X).contDiff.comp
    (((Complex.conjCLE.toContinuousLinearMap.compLeftContinuous ℝ X).contDiff).mul contDiff_id)

/-- Polynomial evaluation in the algebra of continuous curves.-/
def curvePolynomial {ι : Type*} (p : MvPolynomial ι ℂ) (z : ι → C(X, ℂ)) : C(X, ℂ) :=
  MvPolynomial.eval₂ (algebraMap ℂ C(X, ℂ)) z p

omit [CompactSpace X] in
/--
@isnad1 id=eq.0h5v.s7.cd7c95db0f2b from=translated src=- shape=b1fc77d0 vocab=0f14b48b
-/
theorem curvePolynomial_apply {ι : Type*} (p : MvPolynomial ι ℂ)
    (z : ι → C(X, ℂ)) (t : X) :
    curvePolynomial p z t = MvPolynomial.eval (fun i => z i t) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [curvePolynomial]
  | add p q hp hq => simpa [curvePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp => simpa [curvePolynomial] using congrArg (· * z i t) hp

/--
@isnad1 id=contdiff.0h3v.s7.370c6b3ba448 from=translated src=- shape=f6ff16ee vocab=3b240841
-/
theorem curvePolynomial_contDiff {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℂ) :
    ContDiff ℝ ⊤ (curvePolynomial (X := X) p) := by
  change ContDiff ℝ ⊤ (fun z : ι → C(X, ℂ) => MvPolynomial.eval₂ (algebraMap ℂ C(X, ℂ)) z p)
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂_C] using
      (contDiff_const (c := algebraMap ℂ C(X, ℂ) c) (𝕜 := ℝ) (E := ι → C(X, ℂ)))
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (contDiff_apply ℝ _ i)

/-- Both halves of the proper affine embedding, lifted to continuous curves.-/
def curveTorusCoordinates {d : ℕ} (z : Fin d → C(X, ℂ)) :
    Fin d ⊕ Fin d → C(X, ℂ) :=
  Sum.elim z (fun i => Ring.inverse (z i))

/--
@isnad1 id=contdiff.1h3v.s8.6989ead9c3a1 from=translated src=- shape=1ef751b9 vocab=83d23a99
-/
theorem curveTorusCoordinates_contDiffAt {d : ℕ} {z : Fin d → C(X, ℂ)}
    (hz : ∀ i t, z i t ≠ 0) : ContDiffAt ℝ ⊤ (curveTorusCoordinates (X := X)) z := by
  apply contDiffAt_pi.2
  intro j
  cases j with
  | inl i => exact contDiffAt_apply ℝ _ i z
  | inr i => exact (curveInverse_contDiffAt (hz i)).comp z (contDiffAt_apply ℝ _ i z)

/-- The induced metric coefficients as real continuous functions.-/
def curveTorusWeight {d : ℕ} (z : Fin d → C(X, ℂ)) (i : Fin d) : C(X, ℝ) :=
  1 + curveNormSq (Ring.inverse (z i)) ^ 2

omit [CompactSpace X] in
/--
@isnad1 id=eq.1h5v.s7.f7eb391e5328 from=translated src=- shape=611a7191 vocab=6248faec
-/
theorem curveTorusWeight_apply {d : ℕ} {z : Fin d → C(X, ℂ)}
    (hz : ∀ i t, z i t ≠ 0) (i : Fin d) (t : X) :
    curveTorusWeight z i t = torusWeight (fun j => z j t) i := by
  simp only [curveTorusWeight, ContinuousMap.add_apply, ContinuousMap.one_apply,
    ContinuousMap.pow_apply, curveNormSq_apply, curveInverse_apply (hz i),
    Complex.normSq_eq_norm_sq, norm_inv, torusWeight]
  ring

/--
@isnad1 id=contdiff.1h4v.s8.0f6dc14a0d1c from=translated src=- shape=53b2b751 vocab=0d3fea6f
-/
theorem curveTorusWeight_contDiffAt {d : ℕ} {z : Fin d → C(X, ℂ)}
    (hz : ∀ i t, z i t ≠ 0) (i : Fin d) :
    ContDiffAt ℝ ⊤ (fun u => curveTorusWeight u i) z := by
  exact contDiffAt_const.add ((curveNormSq_contDiff.contDiffAt.comp z
    ((curveInverse_contDiffAt (hz i)).comp z (contDiffAt_apply ℝ _ i z))).pow 2)

/-- Actual torus-coordinate partial derivatives, lifted to curves.-/
def curveTorusGradient {d : ℕ} (p : AmbientPolynomial d) (z : Fin d → C(X, ℂ))
    (i : Fin d) : C(X, ℂ) :=
  curvePolynomial (torusPartial p i) (curveTorusCoordinates z)

omit [CompactSpace X] in
/--
@isnad1 id=eq.1h6v.s7.1bf5e9a0512d from=translated src=- shape=b191b6f7 vocab=469e304c
-/
theorem curveTorusGradient_apply {d : ℕ} (p : AmbientPolynomial d)
    {z : Fin d → C(X, ℂ)} (hz : ∀ i t, z i t ≠ 0) (i : Fin d) (t : X) :
    curveTorusGradient p z i t = polynomialTorusGradient p (fun j => z j t) i := by
  rw [curveTorusGradient, curvePolynomial_apply]
  congr 2
  funext j
  cases j with
  | inl k => rfl
  | inr k => exact curveInverse_apply (hz k) t

/--
@isnad1 id=contdiff.1h5v.s8.5d1bf097e4ca from=translated src=- shape=c270c3b8 vocab=5190fd60
-/
theorem curveTorusGradient_contDiffAt {d : ℕ} (p : AmbientPolynomial d)
    {z : Fin d → C(X, ℂ)} (hz : ∀ i t, z i t ≠ 0) (i : Fin d) :
    ContDiffAt ℝ ⊤ (fun u => curveTorusGradient p u i) z :=
  (curvePolynomial_contDiff (torusPartial p i)).contDiffAt.comp z
    (curveTorusCoordinates_contDiffAt hz)

/-- The squared restricted operator norm, lifted to real curves.-/
def curveTorusNormSq {d : ℕ} (p : AmbientPolynomial d) (z : Fin d → C(X, ℂ)) : C(X, ℝ) :=
  ∑ i, curveNormSq (curveTorusGradient p z i) * Ring.inverse (curveTorusWeight z i)

omit [CompactSpace X] in
/--
@isnad1 id=eq.1h5v.s7.34af8a0def56 from=translated src=- shape=8b1bb856 vocab=cb814ba0
-/
theorem curveTorusNormSq_apply {d : ℕ} (p : AmbientPolynomial d)
    {z : Fin d → C(X, ℂ)} (hz : ∀ i t, z i t ≠ 0) (t : X) :
    curveTorusNormSq p z t = polynomialTorusNormSq p (fun j => z j t) := by
  have hw (i : Fin d) : ∀ t, curveTorusWeight z i t ≠ 0 := fun t => by
    rw [curveTorusWeight_apply hz]
    exact ne_of_gt (torusWeight_pos _ _)
  simp [curveTorusNormSq, polynomialTorusNormSq, differentialNormSq,
    curveNormSq_apply, curveTorusGradient_apply p hz, curveInverse_apply (hw _),
    curveTorusWeight_apply hz, div_eq_mul_inv]

/--
@isnad1 id=contdiff.1h4v.s8.aaa87eb8055c from=translated src=- shape=ecb54049 vocab=bc5cd867
-/
theorem curveTorusNormSq_contDiffAt {d : ℕ} (p : AmbientPolynomial d)
    {z : Fin d → C(X, ℂ)} (hz : ∀ i t, z i t ≠ 0) :
    ContDiffAt ℝ ⊤ (curveTorusNormSq (X := X) p) z := by
  apply ContDiffAt.sum
  intro i _
  apply (curveNormSq_contDiff.contDiffAt.comp z (curveTorusGradient_contDiffAt p hz i)).mul
  apply (curveInverse_contDiffAt (u := curveTorusWeight z i) ?_).comp z
    (curveTorusWeight_contDiffAt hz i)
  intro t
  rw [curveTorusWeight_apply hz]
  exact ne_of_gt (torusWeight_pos _ _)

/-- Complexification of a real curve, as a bounded real-linear map.-/
def curveOfReal : C(X, ℝ) →L[ℝ] C(X, ℂ) :=
  Complex.ofRealCLM.compLeftContinuous ℝ X

omit [CompactSpace X] in
/--
@isnad1 id=eq.0h3v.s8.a45d24214475 from=translated src=- shape=889d61ea vocab=e4e220ce
-/
@[simp] theorem curveOfReal_apply (u : C(X, ℝ)) (t : X) :
    curveOfReal u t = (u t : ℂ) := rfl

/-- The explicit scalar normalized-gradient field on continuous curves.
The velocity is constant in the curve parameter.-/
def curveVectorField {d : ℕ} (p : AmbientPolynomial d) (a : ℂ)
    (z : Fin d → C(X, ℂ)) : Fin d → C(X, ℂ) := fun i =>
  ContinuousMap.const X a *
    (Complex.conjCLE.toContinuousLinearMap.compLeftContinuous ℝ X (curveTorusGradient p z i)) *
    Ring.inverse (curveOfReal (curveTorusWeight z i) * curveOfReal (curveTorusNormSq p z))

omit [CompactSpace X] in
/-- Evaluation of the lifted field is exactly the original field, along every
curve contained in the regular domain.
@isnad1 id=eq.1h7v.s7.0acb12befb6c from=translated src=- shape=8be2c1f0 vocab=ae4e64e0
-/
theorem curveVectorField_apply {d : ℕ} (p : AmbientPolynomial d) (a : ℂ)
    {z : Fin d → C(X, ℂ)}
    (hz : ∀ t, (fun i => z i t) ∈ polynomialRegularDomain p) (i : Fin d) (t : X) :
    curveVectorField p a z i t = polynomialVectorField p a (fun j => z j t) i := by
  have hnz : ∀ i t, z i t ≠ 0 := fun i t => (hz t).1 i
  have hden : ∀ t, (curveOfReal (curveTorusWeight z i) *
      curveOfReal (curveTorusNormSq p z)) t ≠ 0 := by
    intro t
    change (curveTorusWeight z i t : ℂ) * (curveTorusNormSq p z t : ℂ) ≠ 0
    rw [curveTorusWeight_apply hnz, curveTorusNormSq_apply p hnz]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (torusWeight_pos _ _)))
      (Complex.ofReal_ne_zero.mpr (hz t).2)
  change a * conj (curveTorusGradient p z i t) *
    Ring.inverse (curveOfReal (curveTorusWeight z i) * curveOfReal (curveTorusNormSq p z)) t = _
  rw [curveInverse_apply hden]
  simp only [ContinuousMap.mul_apply, curveOfReal_apply,
    curveTorusGradient_apply p hnz, curveTorusWeight_apply hnz, curveTorusNormSq_apply p hnz,
    polynomialVectorField, scalarLift, polynomialTorusNormSq, div_eq_mul_inv]

/-- Joint real smoothness of the actual vector field as an operator on the
Banach space of continuous curves, at every regular curve.
@isnad1 id=contdiff.1h5v.s9.bbdfb6d6c0d5 from=translated src=- shape=8c0a2527 vocab=d5a6795e
-/
theorem curveVectorField_contDiffAt {d : ℕ} (p : AmbientPolynomial d) {a : ℂ}
    {z : Fin d → C(X, ℂ)}
    (hz : ∀ t, (fun i => z i t) ∈ polynomialRegularDomain p) :
    ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → C(X, ℂ)) => curveVectorField p az.1 az.2)
      (a, z) := by
  have hnz : ∀ i t, z i t ≠ 0 := fun i t => (hz t).1 i
  apply contDiffAt_pi.2
  intro i
  have hg : ContDiffAt ℝ ⊤ (fun u : Fin d → C(X, ℂ) =>
      Complex.conjCLE.toContinuousLinearMap.compLeftContinuous ℝ X (curveTorusGradient p u i)) z :=
    (Complex.conjCLE.toContinuousLinearMap.compLeftContinuous ℝ X).contDiff.contDiffAt.comp z
      (curveTorusGradient_contDiffAt p hnz i)
  have hw : ContDiffAt ℝ ⊤ (fun u => curveOfReal (curveTorusWeight u i)) z :=
    (curveOfReal (X := X)).contDiff.contDiffAt.comp z (curveTorusWeight_contDiffAt hnz i)
  have hn : ContDiffAt ℝ ⊤ (fun u => curveOfReal (curveTorusNormSq p u)) z :=
    (curveOfReal (X := X)).contDiff.contDiffAt.comp z (curveTorusNormSq_contDiffAt p hnz)
  have hden : ∀ t, (curveOfReal (curveTorusWeight z i) *
      curveOfReal (curveTorusNormSq p z)) t ≠ 0 := by
    intro t
    change (curveTorusWeight z i t : ℂ) * (curveTorusNormSq p z t : ℂ) ≠ 0
    rw [curveTorusWeight_apply hnz, curveTorusNormSq_apply p hnz]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (torusWeight_pos _ _)))
      (Complex.ofReal_ne_zero.mpr (hz t).2)
  have hi : ContDiffAt ℝ ⊤ (Ring.inverse : C(X, ℂ) → C(X, ℂ))
      (curveOfReal (curveTorusWeight z i) * curveOfReal (curveTorusNormSq p z)) :=
    curveInverse_contDiffAt hden
  have hd : ContDiffAt ℝ ⊤ (fun u : Fin d → C(X, ℂ) =>
      Ring.inverse (curveOfReal (curveTorusWeight u i) * curveOfReal (curveTorusNormSq p u))) z := by
    exact hi.comp z (hw.mul hn)
  have ha : ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → C(X, ℂ)) => ContinuousMap.const X az.1) (a, z) :=
    (ContinuousLinearMap.const ℝ X : ℂ →L[ℝ] C(X, ℂ)).contDiff.contDiffAt.comp (a, z) contDiffAt_fst
  exact (ha.mul (hg.comp (a, z) (f := Prod.snd) contDiffAt_snd)).mul (hd.comp (a, z) (f := Prod.snd) contDiffAt_snd)

/-- Specialization to the canonical representative of every Laurent polynomial.
@isnad1 id=contdiff.1h5v.s9.3757eecaca25 from=translated src=- shape=c7370fda vocab=3ba4bda0
-/
theorem laurentCurveVectorField_contDiffAt {d : ℕ} (f : MultiLaurent d) {a : ℂ}
    {z : Fin d → C(X, ℂ)}
    (hz : ∀ t, (fun i => z i t) ∈ laurentRegularDomain f) :
    ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → C(X, ℂ)) =>
      curveVectorField (laurentRepresentative f) az.1 az.2) (a, z) :=
  curveVectorField_contDiffAt (laurentRepresentative f) hz

end

end DuistermaatVanDerKallen
