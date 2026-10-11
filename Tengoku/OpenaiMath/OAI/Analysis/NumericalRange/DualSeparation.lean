import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.MetricFeasibility

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_184 u_185 u_186 u_187

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n]

local instance : ZeroLEOneClass (HermitianMatrix n) where
  zero_le_one := (zero_le_one : (0 : Matrix n n ℂ) ≤ 1)

local instance : PosSMulMono ℝ (HermitianMatrix n) where
  smul_le_smul_of_nonneg_left a ha b c hbc :=
    show a • (b : Matrix n n ℂ) ≤ a • (c : Matrix n n ℂ) from
      smul_le_smul_of_nonneg_left hbc ha

def StrictPositive (H : HermitianMatrix n) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r • (1 : HermitianMatrix n) ≤ H

lemma hermitian_smul_one_le_iff (a b : ℝ) :
    a • (1 : HermitianMatrix n) ≤ b • (1 : HermitianMatrix n) ↔ a ≤ b := by
  change a • (1 : Matrix n n ℂ) ≤ b • (1 : Matrix n n ℂ) ↔ a ≤ b
  simpa only [Algebra.algebraMap_eq_smul_one] using scalarMatrix_le_iff (n := n) a b

lemma hermitian_lower_norm
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (H : HermitianMatrix n) :
    (-‖H‖) • (1 : HermitianMatrix n) ≤ H := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self
    (-(H : Matrix n n ℂ)) H.property.neg
  rw [norm_neg] at h
  have hn := neg_le_neg h
  change (-‖(H : Matrix n n ℂ)‖) • (1 : Matrix n n ℂ) ≤ (H : Matrix n n ℂ)
  simpa only [map_neg, neg_neg, Algebra.algebraMap_eq_smul_one, neg_smul] using hn

lemma StrictPositive.nonneg
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H : HermitianMatrix n}
    (hH : StrictPositive H) : 0 ≤ H := by
  obtain ⟨r, hr, h⟩ := hH
  exact (smul_nonneg hr.le (zero_le_one : (0 : HermitianMatrix n) ≤ 1)).trans h

lemma strictPositive_one
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] :
    StrictPositive (1 : HermitianMatrix n) := by
  exact ⟨1, zero_lt_one, by simp⟩

lemma StrictPositive.add_nonneg
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H K : HermitianMatrix n}
    (hH : StrictPositive H) (hK : 0 ≤ K) : StrictPositive (H + K) := by
  obtain ⟨r, hr, h⟩ := hH
  exact ⟨r, hr, h.trans (le_add_of_nonneg_right hK)⟩

lemma StrictPositive.smul
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H : HermitianMatrix n}
    (hH : StrictPositive H)
    {a : ℝ} (ha : 0 < a) : StrictPositive (a • H) := by
  obtain ⟨r, hr, h⟩ := hH
  refine ⟨a*r, mul_pos ha hr, ?_⟩
  simpa only [mul_smul] using smul_le_smul_of_nonneg_left h ha.le

lemma strictPositive_isOpen : IsOpen {H : HermitianMatrix n | StrictPositive H} := by
  rw [Metric.isOpen_iff]
  intro H hH
  obtain ⟨r, hr, h⟩ := hH
  refine ⟨r/2, by positivity, ?_⟩
  intro J hJ
  have hδ : ‖J-H‖ < r/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hJ
  refine ⟨r/2, by positivity, ?_⟩
  have hb := add_le_add h (hermitian_lower_norm (J-H))
  have he : H + (J-H) = J := by abel
  rw [he, ← add_smul] at hb
  apply le_trans _ hb
  apply (hermitian_smul_one_le_iff _ _).mpr
  linarith

lemma strictPositive_convex
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] :
    Convex ℝ {H : HermitianMatrix n | StrictPositive H} := by
  intro H hH K hK a b ha hb hab
  obtain ⟨r, hr, hH⟩ := hH
  obtain ⟨s, hs, hK⟩ := hK
  refine ⟨a*r+b*s, ?_, ?_⟩
  · have h₁ : 0 ≤ a*r := mul_nonneg ha hr.le
    have h₂ : 0 ≤ b*s := mul_nonneg hb hs.le
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith
      simpa [hb1]
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hr) h₂
  · simpa only [add_smul, mul_smul] using
      add_le_add (smul_le_smul_of_nonneg_left hH ha) (smul_le_smul_of_nonneg_left hK hb)

def metricStein (T : Matrix n n ℂ) : HermitianMatrix n →ₗ[ℝ] HermitianMatrix n where
  toFun J := ⟨(J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T,
    J.property.sub (Matrix.isHermitian_conjTranspose_mul_mul T J.property)⟩
  map_add' J K := by
    apply Subtype.ext
    change (J : Matrix n n ℂ) + K - Tᴴ * ((J : Matrix n n ℂ) + K) * T =
      ((J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T) +
      ((K : Matrix n n ℂ) - Tᴴ * (K : Matrix n n ℂ) * T)
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a J := by
    apply Subtype.ext
    change a • (J : Matrix n n ℂ) - Tᴴ * (a • (J : Matrix n n ℂ)) * T =
      a • ((J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T)
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

abbrev MetricDualSpace (n : Type u_185) [Fintype n] [DecidableEq n] :=
  ℝ × HermitianMatrix n × HermitianMatrix n × HermitianMatrix n

def metricLinear (T : Matrix n n ℂ) :
    (ℝ × HermitianMatrix n) →ₗ[ℝ] MetricDualSpace n where
  toFun x := (x.1, x.2, x.1 • 1-x.2, metricStein T x.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk]
    congr 2
    abel_nf
  map_smul' a x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, smul_smul,
      smul_eq_mul, Prod.smul_mk, RingHom.id_apply]

def metricOffset : MetricDualSpace n := (0,-1,0,0)
def metricAffine (T : Matrix n n ℂ) (x : ℝ × HermitianMatrix n) : MetricDualSpace n :=
  metricOffset + metricLinear T x

def metricOpen (τ : ℝ) : Set (MetricDualSpace n) :=
  {x | x.1 < τ ∧ StrictPositive x.2.1 ∧ StrictPositive x.2.2.1 ∧ StrictPositive x.2.2.2}

def metricAxis0 : ℝ →ₗ[ℝ] MetricDualSpace n where
  toFun s := (s,0,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis1 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun U := (0,U,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis2 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun V := (0,0,V,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis3 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun W := (0,0,0,W)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp] lemma hermTrace_zero_right
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (B : HermitianMatrix n) :
    hermTrace B 0 = 0 := by
  change (Matrix.trace ((B : Matrix n n ℂ) * 0)).re = 0
  simp
@[simp] lemma hermTrace_zero_left (B : HermitianMatrix n) : hermTrace 0 B = 0 := by
  rw [hermTrace_symm, hermTrace_zero_right]

def metricPush (T : Matrix n n ℂ) (Z : HermitianMatrix n) : HermitianMatrix n :=
  ⟨T * (Z : Matrix n n ℂ) * Tᴴ, Matrix.isHermitian_mul_mul_conjTranspose T Z.property⟩

end CompleteCrouzeix

end

end OAI
