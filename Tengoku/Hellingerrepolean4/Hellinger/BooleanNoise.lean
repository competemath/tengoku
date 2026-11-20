import Tengoku.Hellingerrepolean4.Hellinger.FiniteChannel
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms character_eigenfunction` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms antipodal_mean_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bsc_dictator_equality` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bsc_signed_dictator_equality` (it only prints; the queue checks the axioms of every declaration). -/

/-! Concrete binary symmetric channels and their finite products. -/

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace Hellinger

def boolSign (b : Bool) : ℝ := if b then -1 else 1

/--
@isnad1 id=eq.0h1v.s4.3f0ebee64136 from=translated src=- shape=d9ef4337 vocab=b88f46df
-/
theorem boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by
  cases b <;> norm_num [boolSign]

/--
@isnad1 id=eq.0h1v.s3.13f31f9a02fb from=translated src=- shape=d2189a58 vocab=5b654c6a
-/
theorem boolSign_neg (b : Bool) : boolSign (!b) = -boolSign b := by
  cases b <;> norm_num [boolSign]

noncomputable def bsc (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : UniformChannel Bool where
  weight x y := if x = y then (1 + ρ) / 2 else (1 - ρ) / 2
  nonneg x y := by split_ifs <;> linarith [hρ.1, hρ.2]
  row_sum x := by cases x <;> simp <;> ring
  column_sum y := by cases y <;> simp <;> ring

/--
@isnad1 id=eq.1h2v.s5.84ac458b37af from=translated src=- shape=b9630d28 vocab=3fed7dc9
-/
theorem bsc_apply_one (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Bool) :
    (bsc ρ hρ).apply (fun _ => 1) x = 1 := by
  simp only [UniformChannel.apply, mul_one]
  exact (bsc ρ hρ).row_sum x

/--
@isnad1 id=eq.1h2v.s5.ee1cf25e7467 from=translated src=- shape=bdf22281 vocab=bca59536
-/
theorem bsc_apply_sign (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Bool) :
    (bsc ρ hρ).apply boolSign x = ρ * boolSign x := by
  cases x <;> simp [UniformChannel.apply, bsc, boolSign] <;> ring

namespace UniformChannel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

noncomputable def product (K : ∀ i, UniformChannel (Ω i)) : UniformChannel (∀ i, Ω i) where
  weight x y := ∏ i, (K i).weight (x i) (y i)
  nonneg x y := Finset.prod_nonneg fun i _ => (K i).nonneg (x i) (y i)
  row_sum x := by
    rw [← Fintype.prod_sum]
    simp only [UniformChannel.row_sum, Finset.prod_const_one]
  column_sum y := by
    calc
      (∑ x : (∀ i, Ω i), ∏ i, (K i).weight (x i) (y i)) =
          ∏ i, ∑ z, (K i).weight z (y i) :=
        (Fintype.prod_sum (fun i z => (K i).weight z (y i))).symm
      _ = 1 := by simp only [UniformChannel.column_sum, Finset.prod_const_one]

/--
@isnad1 id=eq.0h5v.s6.8d7e4b867efa from=translated src=- shape=1a3bfa1b vocab=e1f59a26
-/
theorem product_apply (K : ∀ i, UniformChannel (Ω i)) (f : ∀ i, Ω i → ℝ) (x : ∀ i, Ω i) :
    (product K).apply (fun y => ∏ i, f i (y i)) x = ∏ i, (K i).apply (f i) (x i) := by
  simp only [apply, product]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i y => (K i).weight (x i) y * f i y)).symm

end UniformChannel

def antipode (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

/--
@isnad1 id=eq.1h3v.s5.0553797f31d1 from=translated src=- shape=5913839e vocab=97335a5f
-/
theorem mean_eq_zero_of_sign_reversing {Ω : Type*} [Fintype Ω]
    (e : Ω ≃ Ω) (f : Ω → ℝ) (hf : ∀ x, f (e x) = - f x) : mean f = 0 := by
  have hsum := e.sum_comp f
  simp_rw [hf, Finset.sum_neg_distrib] at hsum
  have hz : ∑ x, f x = 0 := by linarith
  simp [mean, hz]

/--
@isnad1 id=eq.1h2v.s6.4b226d24524c from=translated src=- shape=0fe93ffc vocab=c157d7cd
-/
theorem antipodal_mean_zero (n : ℕ) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f (antipode n x) = -f x) : mean f = 0 :=
  mean_eq_zero_of_sign_reversing (antipode n) f hf

noncomputable def cubeBSC (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    UniformChannel (Fin n → Bool) := UniformChannel.product (fun _ => bsc ρ hρ)

def character (n : ℕ) (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ i, if i ∈ S then boolSign (x i) else 1

/--
@isnad1 id=eq.1h4v.s6.4e22349630dc from=translated src=- shape=19ab6ddc vocab=117adf2d
-/
theorem character_eigenfunction (n : ℕ) (S : Finset (Fin n))
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Fin n → Bool) :
    (cubeBSC n ρ hρ).apply (character n S) x = ρ ^ S.card * character n S x := by
  classical
  unfold cubeBSC character
  rw [UniformChannel.product_apply (fun _ : Fin n => bsc ρ hρ)
    (fun i y => if i ∈ S then boolSign y else 1) x]
  have hfactor (i : Fin n) :
      (bsc ρ hρ).apply (fun y => if i ∈ S then boolSign y else 1) (x i) =
      (if i ∈ S then ρ else 1) * (if i ∈ S then boolSign (x i) else 1) := by
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, bsc_apply_sign]
    · simp only [hi, ite_false, bsc_apply_one, mul_one]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp

/--
@isnad1 id=eq.1h3v.s7.603ab9bd88c8 from=translated src=- shape=81137a8e vocab=2890cbde
-/
theorem bsc_dictator_equality (n : ℕ) (i : Fin n)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC n ρ hρ).apply (fun x => boolSign (x i))) =
      1 - Real.sqrt (1 - ρ ^ 2) := by
  have hchar : character n {i} = (fun x => boolSign (x i)) := by
    funext x
    simp [character]
  have hnoise (x : Fin n → Bool) :
      (cubeBSC n ρ hρ).apply (fun x => boolSign (x i)) x = ρ * boolSign (x i) := by
    simpa [hchar] using character_eigenfunction n {i} ρ hρ x
  have hm : mean (fun x : Fin n → Bool => boolSign (x i)) = 0 := by
    apply antipodal_mean_zero
    intro x
    exact boolSign_neg (x i)
  unfold objective
  rw [UniformChannel.mean_apply, hm]
  simp_rw [hnoise, root, mul_pow, boolSign_sq, mul_one]
  rw [mean_const]
  norm_num

/-- Both output signs attain the dictator value; this is an attainment result,
not the classification of every equality case.
@isnad1 id=eq.1h4v.s7.a90c0eec3b56 from=translated src=- shape=322b4925 vocab=b783d3da
-/
theorem bsc_signed_dictator_equality (n : ℕ) (i : Fin n) (negative : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC n ρ hρ).apply
      (fun x => if negative then -boolSign (x i) else boolSign (x i))) =
      1 - Real.sqrt (1 - ρ ^ 2) := by
  cases negative
  · simpa using bsc_dictator_equality n i ρ hρ
  · simp only [ite_true, UniformChannel.apply_neg, objective_neg]
    exact bsc_dictator_equality n i ρ hρ

end Hellinger
