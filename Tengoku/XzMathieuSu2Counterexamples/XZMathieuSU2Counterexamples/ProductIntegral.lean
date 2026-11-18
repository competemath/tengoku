import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.Padding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open MeasureTheory
namespace XZMathieuSU2Counterexamples

def torusMeasure (k : ℕ) : Measure (Fin k → Circle) := Measure.pi (fun _ => normalizedHaar Circle)
instance (k : ℕ) : (torusMeasure k).IsHaarMeasure := by unfold torusMeasure; infer_instance

def torusMonomialHom {k : ℕ} (z : Fin k → Circle) : Multiplicative (Fin k → ℤ) →* ℂ where
  toFun e := ∏ j, (z j : ℂ)^(e.toAdd j)
  map_one' := by simp
  map_mul' e f := by
    change (∏ j, (z j : ℂ)^(e.toAdd j+f.toAdd j)) = _
    simp [zpow_add₀ (Circle.coe_ne_zero _), Finset.prod_mul_distrib]

def multiEval {k l : ℕ} (x : Fin l → ℝ) (z : Fin k → Circle) : MultiLaurent k l →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (MvPolynomial.eval (fun i => (x i : ℂ)))
    (torusMonomialHom z) (fun _ _ => Commute.all _ _)

/--
@isnad1 id=eq.0h6v.s8.dcd938281ce5 from=translated src=- shape=3c4d9f9b vocab=647fce29
-/
theorem multiEval_single {k l : ℕ} (x : Fin l → ℝ) (z : Fin k → Circle)
    (e : Fin k → ℤ) (p : MvPolynomial (Fin l) ℂ) :
    multiEval x z (AddMonoidAlgebra.single e p) =
      MvPolynomial.eval (fun i => (x i : ℂ)) p * ∏ j, (z j : ℂ)^(e j) := by
  rw [multiEval, AddMonoidAlgebra.liftNCRingHom_single]
  rfl

/--
@isnad1 id=continuo.0h4v.s7.d83c547b7f26 from=translated src=- shape=c4c8f77a vocab=963135bb
-/
theorem multiEval_continuous {k l : ℕ} (x : Fin l → ℝ) (f : MultiLaurent k l) :
    Continuous (fun z : Fin k → Circle => multiEval x z f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : Fin k → Circle => (0 : ℂ)))
  | add f g hf hg =>
    have he : (fun z => multiEval x z (f+g)) = (fun z => multiEval x z f) + (fun z => multiEval x z g) := by
      funext z; exact map_add _ _ _
    rw [he]; exact hf.add hg
  | single e p =>
    simp_rw [multiEval_single]
    apply continuous_const.mul
    apply continuous_finsetProd
    intro j _
    exact (continuous_subtype_val.comp (continuous_apply j)).zpow₀ (e j)
      (fun z => Or.inl (Circle.coe_ne_zero (z j)))

/--
@isnad1 id=eq.0h4v.s8.c55f6089c8a8 from=translated src=- shape=d1b8614c vocab=1a71112a
-/
theorem multiCircle_constantTerm {k l : ℕ} (x : Fin l → ℝ) (f : MultiLaurent k l) :
    (∫ z, multiEval x z f ∂torusMeasure k) = MvPolynomial.eval (fun i => (x i : ℂ)) (f.coeff 0) := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [integral_add ((multiEval_continuous x f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) ((multiEval_continuous x g).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), hf, hg]
  | single e p =>
    simp_rw [multiEval_single]
    rw [integral_const_mul]
    unfold torusMeasure
    rw [integral_fintype_prod_eq_prod (fun j (z : Circle) => (z : ℂ)^(e j))
      (μ := fun _ : Fin k => normalizedHaar Circle)]
    simp_rw [circle_zpow_integral]
    by_cases he : e = 0
    · subst e; simp
    · obtain ⟨j,hj⟩ := Function.ne_iff.mp he
      have hp : (∏ i : Fin k, if e i = 0 then (1 : ℂ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simpa using hj)
      rw [hp]
      simp [AddMonoidAlgebra.coeff_single, he]

/-- Padding is the usual inclusion using exactly one interval and torus coordinate.
@isnad1 id=eq.0h7v.s8.65211bf6ea47 from=translated src=- shape=33d63a41 vocab=a9d829d7
-/
theorem pad_eval {k l : ℕ} (j : Fin k) (i : Fin l) (f : Laurent)
    (x : Fin l → ℝ) (z : Fin k → Circle) :
    multiEval x z (pad j i f) = circleEval (z j) (specialize (x i : ℂ) f) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp [hf,hg]
  | C_mul_T n p =>
    rw [pad_monomial, multiEval_single, padCoefficient_eval]
    simp [padExponent, Pi.single_apply, Finset.prod_ite_eq', circleEval_monomial]

end XZMathieuSU2Counterexamples
