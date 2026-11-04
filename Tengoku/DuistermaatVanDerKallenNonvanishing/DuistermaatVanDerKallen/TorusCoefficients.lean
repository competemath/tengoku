import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentEvaluation
import Tengoku.Seed.Analysis.Fourier.AddCircle
import Tengoku.Seed.MeasureTheory.Integral.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Laurent coefficient extraction on products of circles with normalized Haar
measure. This is a measure-theoretic formula; comparison with oriented chain
integration of the logarithmic form is a separate obligation. -/

open MeasureTheory
open scoped BigOperators
namespace DuistermaatVanDerKallen
noncomputable section

abbrev PhaseTorus (d : ℕ) := Fin d → AddCircle (1 : ℝ)

def phaseTorusMeasure (d : ℕ) : Measure (PhaseTorus d) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

instance (d : ℕ) : Measure.IsAddHaarMeasure (phaseTorusMeasure d) := by
  unfold phaseTorusMeasure
  infer_instance

/-- A Laurent monomial restricted to the phase torus.-/
def torusCharacter {d : ℕ} (a : Fin d → ℤ) (x : PhaseTorus d) : ℂ :=
  ∏ i, fourier (a i) (x i)

/--
@isnad1 id=continuo.0h2v.s6.e8c0396ec2bc from=translated src=- shape=4b6c181b vocab=8445d6e0
-/
theorem torusCharacter_continuous {d : ℕ} (a : Fin d → ℤ) : Continuous (torusCharacter a) := by
  unfold torusCharacter
  fun_prop

/--
@isnad1 id=eq.0h1v.s7.821eac2e77d2 from=translated src=- shape=f10a1e53 vocab=bb403f9a
-/
theorem integral_fourier_zero_index (n : ℤ) :
    (∫ x : AddCircle (1 : ℝ), fourier n x ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

/--
@isnad1 id=eq.0h2v.s7.7c8e050eb656 from=translated src=- shape=b350c822 vocab=f3a58afd
-/
theorem integral_torusCharacter {d : ℕ} (a : Fin d → ℤ) :
    (∫ x, torusCharacter a x ∂phaseTorusMeasure d) = if a = 0 then 1 else 0 := by
  classical
  unfold torusCharacter phaseTorusMeasure
  rw [integral_fintype_prod_eq_prod]
  simp only [integral_fourier_zero_index]
  by_cases ha : a = 0
  · simp [ha]
  · have hex : ∃ i, a i ≠ 0 := by
      by_contra! hh
      exact ha (funext hh)
    obtain ⟨i, hi⟩ := hex
    rw [ite_eq_right ha]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The product circle of coordinate radii `r`, parametrized by phases.-/
def torusPoint {d : ℕ} (r : Fin d → ℝ) (x : PhaseTorus d) : Fin d → ℂ :=
  fun i => (r i : ℂ) * AddCircle.toCircle (x i)

/--
@isnad1 id=ne.1h4v.s5.d119deef6774 from=translated src=- shape=3e48d957 vocab=982e2d59
-/
theorem torusPoint_ne_zero {d : ℕ} (r : Fin d → ℝ) (hr : ∀ i, r i ≠ 0)
    (x : PhaseTorus d) (i : Fin d) : torusPoint r x i ≠ 0 := by
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hr i)) (Circle.coe_ne_zero _)

/--
@isnad1 id=continuo.0h2v.s6.601612563dc5 from=translated src=- shape=a3f81172 vocab=497bcc37
-/
theorem torusPoint_continuous {d : ℕ} (r : Fin d → ℝ) : Continuous (torusPoint r) := by
  unfold torusPoint
  fun_prop

/--
@isnad1 id=eq.0h4v.s6.81f4b96d2af6 from=translated src=- shape=e6d6e5c0 vocab=f7e8711c
-/
theorem torusPoint_monomial {d : ℕ} (r : Fin d → ℝ) (a : Fin d → ℤ) (x : PhaseTorus d) :
    (∏ i, torusPoint r x i ^ a i) = (∏ i, (r i : ℂ) ^ a i) * torusCharacter a x := by
  simp only [torusPoint, mul_zpow, Finset.prod_mul_distrib, torusCharacter,
    fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]

/--
@isnad1 id=eq.0h4v.s7.96da8a322959 from=translated src=- shape=977c1c1f vocab=2822e85b
-/
theorem torusLaurent_expansion {d : ℕ} (f : MultiLaurent d) (r : Fin d → ℝ)
    (x : PhaseTorus d) : laurentEval f (torusPoint r x) =
      ∑ a ∈ f.coeff.support, (f.coeff a * ∏ i, (r i : ℂ) ^ a i) * torusCharacter a x := by
  simp only [laurentEval, Finsupp.sum, torusPoint_monomial, mul_assoc]

/--
@isnad1 id=continuo.0h3v.s6.5daff791a5d8 from=translated src=- shape=184c8fed vocab=1d0abbdb
-/
theorem torusLaurent_continuous {d : ℕ} (f : MultiLaurent d) (r : Fin d → ℝ) :
    Continuous (fun x : PhaseTorus d => laurentEval f (torusPoint r x)) := by
  simp_rw [torusLaurent_expansion]
  exact continuous_finsetSum _ (fun _ _ => continuous_const.mul (torusCharacter_continuous _))

/--
@isnad1 id=integrab.1h2v.s7.6ae175b0e8d1 from=translated src=- shape=3806d375 vocab=c89d2a4d
-/
theorem phaseTorus_integrable_of_continuous {d : ℕ} {F : PhaseTorus d → ℂ}
    (hF : Continuous F) : Integrable F (phaseTorusMeasure d) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

/-- Exact coefficient extraction with normalized product Haar measure.
@isnad1 id=eq.0h3v.s6.c146de6f3d95 from=translated src=- shape=234a1328 vocab=5ac55243
-/
theorem integral_torusLaurent_eq_constantTerm {d : ℕ} (f : MultiLaurent d) (r : Fin d → ℝ) :
    (∫ x, laurentEval f (torusPoint r x) ∂phaseTorusMeasure d) = constantTerm f := by
  classical
  simp_rw [torusLaurent_expansion]
  rw [integral_finsetSum _ (by
    intro a _
    exact phaseTorus_integrable_of_continuous
      (continuous_const.mul (torusCharacter_continuous a)))]
  simp only [integral_const_mul, integral_torusCharacter]
  by_cases hzero : (0 : Fin d → ℤ) ∈ f.coeff.support
  · rw [Finset.sum_eq_single 0]
    · simp [constantTerm]
    · intro a _ ha
      simp [ha]
    · exact fun hn => (hn hzero).elim
  · rw [Finset.sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.mp hzero).symm
    · intro a ha
      have hne : a ≠ 0 := fun he => hzero (he ▸ ha)
      simp [hne]

/-- Exact power coefficient extraction on every product of nonzero-radius circles.
@isnad1 id=eq.1h4v.s7.b2ac2d090a58 from=translated src=- shape=676bc390 vocab=be305ffb
-/
theorem integral_torusLaurent_pow {d : ℕ} (f : MultiLaurent d) (r : Fin d → ℝ)
    (hr : ∀ i, r i ≠ 0) (n : ℕ) :
    (∫ x, laurentEval f (torusPoint r x) ^ n ∂phaseTorusMeasure d) = constantTerm (f ^ n) := by
  have he (x : PhaseTorus d) := laurentEval_pow f n (torusPoint_ne_zero r hr x)
  simp_rw [← he]
  exact integral_torusLaurent_eq_constantTerm (f ^ n) r

/-- An explicit bound for Laurent evaluation on the chosen product circle.-/
def weightedCoefficientMass {d : ℕ} (f : MultiLaurent d) (r : Fin d → ℝ) : ℝ :=
  ∑ a ∈ f.coeff.support, ‖f.coeff a * ∏ i, (r i : ℂ) ^ a i‖

/--
@isnad1 id=le.0h3v.s4.39c57cc8f192 from=translated src=- shape=c4040d18 vocab=64a89421
-/
theorem weightedCoefficientMass_nonneg {d : ℕ} (f : MultiLaurent d) (r : Fin d → ℝ) :
    0 ≤ weightedCoefficientMass f r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

end
end DuistermaatVanDerKallen
