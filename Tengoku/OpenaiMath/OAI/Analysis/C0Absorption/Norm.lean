import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Molecules

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section SelectedNorm

variable {S : Type*} [MetricSpace S]

def triple (n : ℕ) : ℕ × ℕ × ℕ :=
  ((Nat.unpair n).1, Nat.unpair (Nat.unpair n).2)

/--
@isnad1 id=surjecti.0h0v.s3.b89c8fa25853 from=translated src=- shape=3fbceb73 vocab=56d4c383
-/
theorem triple_surjective : Function.Surjective triple := by
  rintro ⟨h, C, k⟩
  exact ⟨Nat.pair h (Nat.pair C k), by simp [triple]⟩

def listConstant (n : ℕ) : ℝ≥0 := (triple n).2.1 + 1

/--
@isnad1 id=lt.0h1v.s4.f4bdb700a3bc from=translated src=- shape=b9369acb vocab=4e0ee342
-/
theorem listConstant_pos (n : ℕ) : 0 < listConstant n := by
  dsimp [listConstant]
  positivity

def listExponent (n : ℕ) : ℝ≥0∞ := 1 + ((triple n).2.2 + 1 : ℝ≥0∞)⁻¹

instance (n : ℕ) : Fact (1 ≤ listExponent n) := ⟨by simp [listExponent]⟩

/--
@isnad1 id=ne.0h1v.s3.2e2756bd2661 from=translated src=- shape=d551a7c0 vocab=c564a362
-/
theorem listExponent_ne_top (n : ℕ) : listExponent n ≠ ∞ := by
  simp [listExponent]

/--
@isnad1 id=eq.0h1v.s5.c1333adb27aa from=translated src=- shape=6b3f81ae vocab=eb37a096
-/
theorem listExponent_toReal (n : ℕ) :
    (listExponent n).toReal = 1 + 1 / ((triple n).2.2 + 1 : ℝ) := by
  simp [listExponent, ENNReal.toReal_add, one_div]

def alpha (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1) / (listConstant n : ℝ) ^ 2

/--
@isnad1 id=lt.0h1v.s3.1b56a7d02907 from=translated src=- shape=b9369acb vocab=82f84864
-/
theorem alpha_pos (n : ℕ) : 0 < alpha n := by
  have hC : 0 < (listConstant n : ℝ) := by exact_mod_cast listConstant_pos n
  dsimp [alpha]
  positivity

def squareWeight (n : ℕ) : ℝ≥0 :=
  ⟨Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) / (listConstant n : ℝ), by positivity⟩

/--
@isnad1 id=eq.0h1v.s4.9a1572e6ac66 from=translated src=- shape=eadf6046 vocab=eea5be2f
-/
theorem squareWeight_sq (n : ℕ) : (squareWeight n : ℝ) ^ 2 = alpha n := by
  change (Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) / (listConstant n : ℝ)) ^ 2 =
    (1 / 2 : ℝ) ^ (n + 1) / (listConstant n : ℝ) ^ 2
  rw [div_pow, Real.sq_sqrt (by positivity)]

/--
@isnad1 id=lt.0h1v.s3.d4236a712d11 from=translated src=- shape=25e12683 vocab=81659dc1
-/
theorem squareWeight_pos (n : ℕ) : 0 < (squareWeight n : ℝ) := by
  have h := alpha_pos n
  rw [← squareWeight_sq] at h
  have hn := (squareWeight n).coe_nonneg
  nlinarith

def selectedCoordinate (L : ℕ → Set (S → ℝ)) (n : ℕ) : Seminorm ℝ (Molecule S) :=
  squareWeight n • sigma (L (triple n).1) (listConstant n) (listExponent n)

/--
@isnad1 id=eq.0h4v.s10.63a107101b28 from=translated src=- shape=e160f7fb vocab=cd03aea1
-/
theorem selectedCoordinate_apply (L : ℕ → Set (S → ℝ)) (n : ℕ) (m : Molecule S) :
    selectedCoordinate L n m = (squareWeight n : ℝ) *
      sigma (L (triple n).1) (listConstant n) (listExponent n) m := rfl

/--
@isnad1 id=le.1h3v.s6.72b8b2b41c2a from=translated src=- shape=05c301e5 vocab=6059d696
-/
theorem weighted_bound (n : ℕ) (a b : ℝ) (h : a ≤ (listConstant n : ℝ) * b) :
    (squareWeight n : ℝ) * a ≤ Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) * b := by
  have hC : (listConstant n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast listConstant_pos n)
  have h' := mul_le_mul_of_nonneg_left h (squareWeight n).coe_nonneg
  calc
    (squareWeight n : ℝ) * a ≤
      (Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) / (listConstant n : ℝ)) *
        ((listConstant n : ℝ) * b) := h'
    _ = Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) * b := by field_simp

/--
@isnad1 id=le.0h5v.s10.7308df3c6481 from=translated src=- shape=aacb1238 vocab=138ab617
-/
theorem selectedCoordinate_bound (L : ℕ → Set (S → ℝ)) (o : S) (n : ℕ) (m : Molecule S) :
    selectedCoordinate L n m ≤ Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) *
      ∑ s ∈ m.val.support, |m.val s| * dist s o := by
  exact weighted_bound n _ _
    (sigma_le (L (triple n).1) (listConstant n) (listExponent n) o m)

/--
@isnad1 id=summable.0h0v.s5.f5d5aed05eae from=translated src=- shape=787c57b3 vocab=c914dd5b
-/
theorem geometric_summable : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
  simpa only [pow_succ] using
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)

/--
@isnad1 id=eq.0h0v.s6.7f9f289ce2f8 from=translated src=- shape=348a0c16 vocab=e7f7fdb7
-/
theorem geometric_tsum : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/--
@isnad1 id=summable.0h4v.s9.cc16ed2d29d6 from=translated src=- shape=f5cd1499 vocab=8f2a6107
-/
theorem selectedCoordinate_summable (L : ℕ → Set (S → ℝ)) (o : S) (m : Molecule S) :
    Summable (fun n => (selectedCoordinate L n m) ^ 2) := by
  classical
  let b := ∑ s ∈ m.val.support, |m.val s| * dist s o
  have hb : 0 ≤ b := Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) dist_nonneg)
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (geometric_summable.mul_right (b ^ 2))
  intro n
  calc
    (selectedCoordinate L n m) ^ 2 ≤ (Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) * b) ^ 2 := by
      apply pow_le_pow_left₀ (apply_nonneg _ _) (selectedCoordinate_bound L o n m)
    _ = (1 / 2 : ℝ) ^ (n + 1) * b ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]

def selectedNorm (L : ℕ → Set (S → ℝ)) (o : S) : Seminorm ℝ (Molecule S) :=
  squareSeminorm (selectedCoordinate L) (selectedCoordinate_summable L o)

/--
@isnad1 id=eq.0h4v.s10.eb3f9ca128af from=translated src=- shape=68cec539 vocab=90e9dadc
-/
theorem selectedNorm_sq (L : ℕ → Set (S → ℝ)) (o : S) (m : Molecule S) :
    (selectedNorm L o m) ^ 2 = ∑' n, alpha n *
      (sigma (L (triple n).1) (listConstant n) (listExponent n) m) ^ 2 := by
  rw [selectedNorm, squareSeminorm_sq]
  apply tsum_congr
  intro n
  rw [selectedCoordinate_apply, mul_pow, squareWeight_sq]

/--
@isnad1 id=le.0h5v.s9.17884498c1ed from=translated src=- shape=458e5db3 vocab=ee604474
-/
theorem selectedNorm_molecule_le (L : ℕ → Set (S → ℝ)) (o s t : S) :
    selectedNorm L o (molecule s t) ≤ dist s t := by
  have hh : ∀ n, (selectedCoordinate L n (molecule s t)) ^ 2 ≤
      (1 / 2 : ℝ) ^ (n + 1) * (dist s t) ^ 2 := by
    intro n
    have h := weighted_bound n _ _
      (sigma_molecule_le (L (triple n).1) (listConstant n) (listExponent n) s t)
    calc
      (selectedCoordinate L n (molecule s t)) ^ 2
          ≤ (Real.sqrt ((1 / 2 : ℝ) ^ (n + 1)) * dist s t) ^ 2 :=
        pow_le_pow_left₀ (apply_nonneg _ _) h 2
      _ = (1 / 2 : ℝ) ^ (n + 1) * dist s t ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsq : (selectedNorm L o (molecule s t)) ^ 2 ≤ dist s t ^ 2 := by
    rw [selectedNorm, squareSeminorm_sq]
    calc
      ∑' n, (selectedCoordinate L n (molecule s t)) ^ 2
          ≤ ∑' n, (1 / 2 : ℝ) ^ (n + 1) * dist s t ^ 2 :=
        Summable.tsum_le_tsum hh (selectedCoordinate_summable L o _)
          (geometric_summable.mul_right _)
      _ = dist s t ^ 2 := by rw [tsum_mul_right, geometric_tsum, one_mul]
  nlinarith [apply_nonneg (selectedNorm L o) (molecule s t), dist_nonneg (x := s) (y := t)]

end SelectedNorm

end
end C0Absorption

end OAI
