import Tengoku.NegativePowerMeans.BoundaryProofs.GeometricMeanOrder
import Tengoku.Seed.Topology.MetricSpace.Contracting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Thompson's metric on the positive-definite cone

This file constructs the metric used in the standalone fixed-point proof.
The carrier is a fresh wrapper, so its topology is exactly the metric
topology constructed below.
-/

namespace HiaiLimPowerMeans

open Matrix Set Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

noncomputable local instance : CStarAlgebra (Matrix n n ℂ) where

omit [Nonempty n] in
/-- A self-adjoint element lying in the order interval `[-r 1, r 1]`
has norm at most `r`.-/
theorem norm_le_of_order_interval
    {X : Matrix n n ℂ} (hX : IsSelfAdjoint X) {r : ℝ} (hr : 0 ≤ r)
    (hlower : -(r • (1 : Matrix n n ℂ)) ≤ X)
    (hupper : X ≤ r • (1 : Matrix n n ℂ)) :
    ‖X‖ ≤ r := by
  have hscalar :
      algebraMap ℝ (Matrix n n ℂ) r = r • (1 : Matrix n n ℂ) := by
    rw [Algebra.algebraMap_eq_smul_one]
  have hupper' : X ≤ algebraMap ℝ (Matrix n n ℂ) r := by
    simpa only [hscalar] using hupper
  have hlower' : algebraMap ℝ (Matrix n n ℂ) (-r) ≤ X := by
    rw [map_neg, hscalar]
    simpa only [neg_smul] using hlower
  have hsU := (le_algebraMap_iff_spectrum_le hX).mp hupper'
  have hsL := (algebraMap_le_iff_le_spectrum hX).mp hlower'
  rw [← cfc_id' ℝ X hX]
  apply norm_cfc_le hr
  intro x hx
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by simpa using hsL x hx, hsU x hx⟩

/-- Positive-definite complex matrices, wrapped for the Thompson metric.-/
structure ThompsonPD (n : Type*) [Fintype n] [DecidableEq n] where
  val : Matrix n n ℂ
  posDef : val.PosDef

namespace ThompsonPD

instance : Coe (ThompsonPD n) (Matrix n n ℂ) := ⟨val⟩

omit [Nonempty n] in
@[ext]
theorem ext {A B : ThompsonPD n} (h : A.val = B.val) : A = B := by
  cases A
  cases B
  simp_all

/-- The positive relative matrix `A⁻¹⁄² B A⁻¹⁄²`.-/
def relative (A B : ThompsonPD n) : Matrix n n ℂ :=
  A.val ^ (-(1 / 2 : ℝ)) * B.val * A.val ^ (-(1 / 2 : ℝ))

omit [Nonempty n] in
theorem relative_posDef (A B : ThompsonPD n) : (relative A B).PosDef := by
  let S : Matrix n n ℂ := A.val ^ (-(1 / 2 : ℝ))
  have hS : S.PosDef := Matrix.PosDef.rpow A.posDef _
  simpa only [relative, S, hS.isHermitian.eq] using
    B.posDef.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hS.isUnit)

/-- The least order factor carrying `A` above `B`.-/
def ratio (A B : ThompsonPD n) : ℝ := ‖relative A B‖

theorem ratio_pos (A B : ThompsonPD n) : 0 < ratio A B := by
  rw [ratio, norm_pos_iff]
  exact (relative_posDef A B).isUnit.ne_zero

theorem ratio_nonneg (A B : ThompsonPD n) : 0 ≤ ratio A B :=
  (ratio_pos A B).le

omit [Nonempty n] in
/-- The norm definition of `ratio` is equivalent to its order-theoretic
characterization.-/
theorem ratio_le_iff (A B : ThompsonPD n) {r : ℝ} (hr : 0 ≤ r) :
    ratio A B ≤ r ↔ B.val ≤ r • A.val := by
  let S : Matrix n n ℂ := A.val ^ (-(1 / 2 : ℝ))
  let R : Matrix n n ℂ := A.val ^ (1 / 2 : ℝ)
  have hS : S.PosDef := Matrix.PosDef.rpow A.posDef _
  have hR : R.PosDef := Matrix.PosDef.rpow A.posDef _
  have hrel : relative A B = S * B.val * S := rfl
  have hscalar :
      algebraMap ℝ (Matrix n n ℂ) r = r • (1 : Matrix n n ℂ) := by
    rw [Algebra.algebraMap_eq_smul_one]
  rw [ratio, CStarAlgebra.norm_le_iff_le_algebraMap
    (relative A B) hr (relative_posDef A B).posSemidef.nonneg]
  constructor
  · intro h
    have hc := compress_mono R h
    rw [hscalar] at hc
    have hRS : R * S = 1 := Matrix.PosDef.half_mul_invHalf A.posDef
    have hSR : S * R = 1 := Matrix.PosDef.invHalf_mul_half A.posDef
    have hRR : R * R = A.val := Matrix.PosDef.sqrt_mul_sqrt A.posDef
    have hleft : compress R (relative A B) = B.val := by
      rw [compress, hR.isHermitian.eq, relative]
      calc
        R * (S * B.val * S) * R = (R * S) * B.val * (S * R) := by
          noncomm_ring
        _ = B.val := by rw [hRS, hSR, Matrix.one_mul, Matrix.mul_one]
    have hright : compress R (r • (1 : Matrix n n ℂ)) = r • A.val := by
      rw [compress, hR.isHermitian.eq]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hRR]
    simpa only [hleft, hright] using hc
  · intro h
    have hc := compress_mono S h
    rw [hscalar]
    have hSA : S * A.val * S = 1 :=
      Matrix.PosDef.invHalf_conjugate_self A.posDef
    simpa only [relative, compress, hS.isHermitian.eq, Matrix.mul_smul,
      Matrix.smul_mul, hSA, Matrix.mul_one] using hc

omit [Nonempty n] in
@[simp]
theorem relative_self (A : ThompsonPD n) : relative A A = 1 :=
  Matrix.PosDef.invHalf_conjugate_self A.posDef

@[simp]
theorem ratio_self (A : ThompsonPD n) : ratio A A = 1 := by
  simp [ratio]

/-- Submultiplicativity of the order ratios.-/
theorem ratio_triangle (A B C : ThompsonPD n) :
    ratio A C ≤ ratio A B * ratio B C := by
  have hAB : B.val ≤ ratio A B • A.val :=
    (ratio_le_iff A B (ratio_nonneg A B)).mp le_rfl
  have hBC : C.val ≤ ratio B C • B.val :=
    (ratio_le_iff B C (ratio_nonneg B C)).mp le_rfl
  apply (ratio_le_iff A C (mul_nonneg (ratio_nonneg A B)
    (ratio_nonneg B C))).mpr
  calc
    C.val ≤ ratio B C • B.val := hBC
    _ ≤ ratio B C • (ratio A B • A.val) := by
      exact smul_le_smul_of_nonneg_left hAB (ratio_nonneg B C)
    _ = (ratio A B * ratio B C) • A.val := by
      rw [smul_smul, mul_comm]

/-- Thompson distance, expressed through the two directed order ratios.-/
def tdist (A B : ThompsonPD n) : ℝ :=
  max (Real.log (ratio A B)) (Real.log (ratio B A))

@[simp]
theorem tdist_self (A : ThompsonPD n) : tdist A A = 0 := by
  simp [tdist]

omit [Nonempty n] in
theorem tdist_comm (A B : ThompsonPD n) : tdist A B = tdist B A := by
  simp only [tdist]
  exact max_comm _ _

omit [Nonempty n] in
theorem log_ratio_le_tdist (A B : ThompsonPD n) :
    Real.log (ratio A B) ≤ tdist A B :=
  le_max_left _ _

theorem ratio_le_exp_tdist (A B : ThompsonPD n) :
    ratio A B ≤ Real.exp (tdist A B) :=
  (Real.log_le_iff_le_exp (ratio_pos A B)).mp (log_ratio_le_tdist A B)

theorem order_le_exp_tdist (A B : ThompsonPD n) :
    B.val ≤ Real.exp (tdist A B) • A.val :=
  (ratio_le_iff A B (Real.exp_pos _).le).mp (ratio_le_exp_tdist A B)

theorem order_le_exp_of_dist_lt
    (A B : ThompsonPD n) {e : ℝ} (h : tdist A B < e) :
    B.val ≤ Real.exp e • A.val := by
  calc
    B.val ≤ Real.exp (tdist A B) • A.val := order_le_exp_tdist A B
    _ ≤ Real.exp e • A.val := by
      exact smul_le_smul_of_nonneg_right
        (Real.exp_le_exp.mpr h.le) A.posDef.posSemidef.nonneg

theorem tdist_le_of_order_exp
    (A B : ThompsonPD n) {e : ℝ}
    (hBA : B.val ≤ Real.exp e • A.val)
    (hAB : A.val ≤ Real.exp e • B.val) :
    tdist A B ≤ e := by
  have hrAB : ratio A B ≤ Real.exp e :=
    (ratio_le_iff A B (Real.exp_pos e).le).mpr hBA
  have hrBA : ratio B A ≤ Real.exp e :=
    (ratio_le_iff B A (Real.exp_pos e).le).mpr hAB
  apply max_le
  · exact (Real.log_le_iff_le_exp (ratio_pos A B)).mpr hrAB
  · exact (Real.log_le_iff_le_exp (ratio_pos B A)).mpr hrBA

/-- On an order-bounded part of the cone, a Thompson-distance bound gives
an ordinary operator-norm bound.-/
theorem norm_sub_le_of_dist_lt_of_upper
    (A B : ThompsonPD n) {e M : ℝ} (he : 0 ≤ e) (hM : 0 ≤ M)
    (hA : A.val ≤ M • (1 : Matrix n n ℂ))
    (hB : B.val ≤ M • (1 : Matrix n n ℂ))
    (hd : tdist A B < e) :
    ‖B.val - A.val‖ ≤ (Real.exp e - 1) * M := by
  let c : ℝ := Real.exp e - 1
  have hc : 0 ≤ c := by
    dsimp [c]
    exact sub_nonneg.mpr (Real.one_le_exp he)
  have hBA : B.val ≤ Real.exp e • A.val :=
    order_le_exp_of_dist_lt A B hd
  have hAB : A.val ≤ Real.exp e • B.val :=
    order_le_exp_of_dist_lt B A (by simpa [tdist_comm] using hd)
  have hu : B.val - A.val ≤ (c * M) • (1 : Matrix n n ℂ) := by
    calc
      B.val - A.val ≤ Real.exp e • A.val - A.val :=
        sub_le_sub_right hBA A.val
      _ = c • A.val := by
        dsimp [c]
        module
      _ ≤ c • (M • (1 : Matrix n n ℂ)) :=
        smul_le_smul_of_nonneg_left hA hc
      _ = (c * M) • (1 : Matrix n n ℂ) := by rw [smul_smul]
  have hl : -((c * M) • (1 : Matrix n n ℂ)) ≤ B.val - A.val := by
    have hdiff : A.val - B.val ≤ (c * M) • (1 : Matrix n n ℂ) := by
      calc
        A.val - B.val ≤ Real.exp e • B.val - B.val :=
          sub_le_sub_right hAB B.val
        _ = c • B.val := by
          dsimp [c]
          module
        _ ≤ c • (M • (1 : Matrix n n ℂ)) :=
          smul_le_smul_of_nonneg_left hB hc
        _ = (c * M) • (1 : Matrix n n ℂ) := by rw [smul_smul]
    simpa only [neg_sub] using neg_le_neg hdiff
  exact norm_le_of_order_interval
    (B.posDef.isHermitian.sub A.posDef.isHermitian)
    (mul_nonneg hc hM) hl hu

theorem tdist_triangle (A B C : ThompsonPD n) :
    tdist A C ≤ tdist A B + tdist B C := by
  have hforward : Real.log (ratio A C) ≤
      tdist A B + tdist B C := by
    calc
      Real.log (ratio A C) ≤
          Real.log (ratio A B * ratio B C) :=
        Real.log_le_log (ratio_pos A C)
          (ratio_triangle A B C)
      _ = Real.log (ratio A B) + Real.log (ratio B C) := by
        rw [Real.log_mul (ratio_pos A B).ne' (ratio_pos B C).ne']
      _ ≤ tdist A B + tdist B C :=
        add_le_add (log_ratio_le_tdist A B) (log_ratio_le_tdist B C)
  have hreverse : Real.log (ratio C A) ≤
      tdist A B + tdist B C := by
    calc
      Real.log (ratio C A) ≤
          Real.log (ratio C B * ratio B A) :=
        Real.log_le_log (ratio_pos C A)
          (ratio_triangle C B A)
      _ = Real.log (ratio C B) + Real.log (ratio B A) := by
        rw [Real.log_mul (ratio_pos C B).ne' (ratio_pos B A).ne']
      _ ≤ tdist B C + tdist A B := by
        have hCB := log_ratio_le_tdist C B
        have hBA := log_ratio_le_tdist B A
        rw [tdist_comm C B] at hCB
        rw [tdist_comm B A] at hBA
        exact add_le_add hCB hBA
      _ = tdist A B + tdist B C := add_comm _ _
  exact max_le hforward hreverse

theorem eq_of_tdist_eq_zero {A B : ThompsonPD n} (h : tdist A B = 0) :
    A = B := by
  have hABlog : Real.log (ratio A B) ≤ 0 := by
    rw [← h]
    exact log_ratio_le_tdist A B
  have hBAlog : Real.log (ratio B A) ≤ 0 := by
    rw [← h]
    simpa [tdist_comm] using log_ratio_le_tdist B A
  have hABratio : ratio A B ≤ 1 :=
    (Real.log_nonpos_iff (ratio_nonneg A B)).mp hABlog
  have hBAratio : ratio B A ≤ 1 :=
    (Real.log_nonpos_iff (ratio_nonneg B A)).mp hBAlog
  have hBA : B.val ≤ A.val := by
    simpa using (ratio_le_iff A B zero_le_one).mp hABratio
  have hAB : A.val ≤ B.val := by
    simpa using (ratio_le_iff B A zero_le_one).mp hBAratio
  exact ext (le_antisymm hAB hBA)

/-- The metric-space structure generated by Thompson distance.-/
noncomputable instance instMetricSpace : MetricSpace (ThompsonPD n) where
  dist := tdist
  dist_self := tdist_self
  dist_comm := tdist_comm
  dist_triangle := tdist_triangle
  eq_of_dist_eq_zero := fun h ↦ eq_of_tdist_eq_zero h

@[simp]
theorem dist_eq_tdist (A B : ThompsonPD n) : dist A B = tdist A B := rfl

end ThompsonPD

end

end HiaiLimPowerMeans
