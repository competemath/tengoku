import Tengoku.SingularityCompleteLean.Singularity.MobiusMeasureAction
import Tengoku.SingularityCompleteLean.Singularity.CyclicOrbits
import Tengoku.SingularityCompleteLean.Singularity.MobiusBoundaryAnalysis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Diagonal hyperbolic elements and lattice orbit measures

An explicit one-parameter subgroup of SL(2,ℝ) acts on the boundary by positive
dilation. Its integer powers give exactly the translations nτ after the
logarithmic change of coordinates. Pushforward composition is justified by
the almost-everywhere Möbius action law.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

/-- The diagonal special linear matrix whose boundary dilation is exp(t).-/
def dilationMatrix (t : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp (t / 2), 0; 0, (Real.exp (t / 2))⁻¹], by simp⟩

/--
@isnad1 id=eq.0h0v.s6.c46439511d30 from=translated src=- shape=98680116 vocab=de51431e
-/
theorem dilationMatrix_zero : dilationMatrix 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [dilationMatrix]

/-- These matrices form a one-parameter subgroup.
@isnad1 id=eq.0h2v.s7.4ea4efe827a2 from=translated src=- shape=ff03d487 vocab=74227b48
-/
theorem dilationMatrix_add (s t : ℝ) : dilationMatrix (s + t) = dilationMatrix s * dilationMatrix t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [dilationMatrix, add_div, Real.exp_add, mul_inv_rev, mul_comm]

/-- The one-parameter subgroup as a multiplicative homomorphism.-/
def dilationMatrixHom : Multiplicative ℝ →* SL(2, ℝ) where
  toFun t := dilationMatrix t.toAdd
  map_one' := dilationMatrix_zero
  map_mul' s t := dilationMatrix_add s.toAdd t.toAdd

/-- Positive and negative integer powers correspond to the parameter n t.
@isnad1 id=eq.0h2v.s7.53ba17c767ac from=translated src=- shape=3a4aed62 vocab=956237fc
-/
theorem dilationMatrix_zpow (t : ℝ) (n : ℤ) : dilationMatrix ((n : ℝ) * t) = dilationMatrix t ^ n := by
  have h := dilationMatrixHom.map_zpow (Multiplicative.ofAdd t) n
  change dilationMatrix ((Multiplicative.ofAdd t ^ n).toAdd) = dilationMatrix t ^ n at h
  simpa only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul] using h

/-- The real boundary action is dilation by exp(t), with no finite pole.
@isnad1 id=eq.0h1v.s4.d371f426eb14 from=translated src=- shape=c762875f vocab=5b3be987
-/
theorem realBoundaryMobius_dilationMatrix (t : ℝ) :
    realBoundaryMobius (dilationMatrix t) = (fun u => Real.exp t * u) := by
  funext u
  have he : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp [realBoundaryMobius, dilationMatrix]
  rw [mul_right_comm, he]

/-- The one-parameter subgroup is injective; positive τ therefore gives an
infinite-order element for the cyclic strip-orbit construction.
@isnad1 id=injectiv.0h0v.s4.5c9c852bb1af from=translated src=- shape=8c4e1e81 vocab=a56cb4a3
-/
theorem dilationMatrix_injective : Function.Injective dilationMatrix := by
  intro s t h
  have he := congrArg (fun g : SL(2, ℝ) => realBoundaryMobius g 1) h
  simpa only [realBoundaryMobius_dilationMatrix, mul_one, Real.exp_eq_exp] using he

/-- A nonzero dilation parameter gives an infinite-order special linear matrix.
@isnad1 id=not.1h1v.s5.d3cfa41595fd from=translated src=- shape=8b749564 vocab=da336b23
-/
theorem dilationMatrix_infinite_order {t : ℝ} (ht : t ≠ 0) : ¬IsOfFinOrder (dilationMatrix t) := by
  apply injective_zpow_iff_not_isOfFinOrder.mp
  intro m n h
  change dilationMatrix t ^ m = dilationMatrix t ^ n at h
  rw [← dilationMatrix_zpow, ← dilationMatrix_zpow] at h
  have he := mul_right_cancel₀ ht (dilationMatrix_injective h)
  exact_mod_cast he

/-- The orbit measure for a^n b is exactly the dilation pushforward of b_*ν.
@isnad1 id=eq.1h4v.s8.e296da745e41 from=translated src=- shape=b4606824 vocab=1a9cd208
-/
theorem dilationOrbit_map (ν : Measure ℝ) (hac : ν ≪ volume) (τ : ℝ) (n : ℤ) (b : SL(2, ℝ)) :
    Measure.map (realBoundaryMobius (dilationMatrix τ ^ n * b)) ν =
      Measure.map (fun u : ℝ => Real.exp ((n : ℝ) * τ) * u)
        (Measure.map (realBoundaryMobius b) ν) := by
  rw [← dilationMatrix_zpow, map_realBoundaryMobius_mul ν hac, realBoundaryMobius_dilationMatrix]

end Singularity
