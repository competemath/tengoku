import Tengoku.WasowAsymptoticsLean.WasowRamifiedGauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_pole_free` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.value_constant` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_add` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_sum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_neg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_sub` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_inv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_pow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_zpow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRationalEvaluation.eventually_value_matrix_mul` (it only prints; the queue checks the axioms of every declaration). -/

/-! Genuine rational evaluation commutes with finite algebraic operations on
a common tail. Poles of every intermediate expression are excluded by the
proved rational-denominator theorem, not by treating totalized evaluation as a homomorphism. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace WasowRationalEvaluation
open CRGNormalFormGoal

def value (θ r : ℝ) (f : RatFunc ℂ) : ℂ := RatFunc.eval (RingHom.id ℂ) (ray θ r) f

/--
@isnad1 id=eventual.0h2v.s5.212e12fb4c44 from=translated src=- shape=735e09ba vocab=786cf541
-/
theorem eventually_pole_free (f : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r : ℝ in atTop, f.denom.eval (ray θ r) ≠ 0 := by
  obtain ⟨_, _, R, hR, hb⟩ := WasowRational.exists_polynomial_part_tail f
  filter_upwards [eventually_gt_atTop R] with r hr
  exact (hb (ray θ r) (by rw [WasowRational.norm_ray θ (zero_le_one.trans (hR.trans hr.le))]; exact hr)).1

/--
@isnad1 id=eq.0h3v.s6.cad11bf4d229 from=translated src=- shape=3eed310a vocab=f5aa7c1a
-/
@[simp] theorem value_constant (θ r : ℝ) (c : ℂ) :
    value θ r (algebraMap ℂ (RatFunc ℂ) c) = c := by
  simp [value]

/--
@isnad1 id=eventual.0h3v.s5.996b1837cca1 from=translated src=- shape=c4cb29cf vocab=f94e26ba
-/
theorem eventually_value_add (f g : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (f + g) = value θ r f + value θ r g := by
  filter_upwards [eventually_pole_free f θ, eventually_pole_free g θ] with r hf hg
  exact RatFunc.eval_add (RingHom.id ℂ) (ray θ r) (by simpa using hf) (by simpa using hg)

/--
@isnad1 id=eventual.0h3v.s5.8c2fc9fc9b6a from=translated src=- shape=c4cb29cf vocab=4a0b9499
-/
theorem eventually_value_mul (f g : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (f * g) = value θ r f * value θ r g := by
  filter_upwards [eventually_pole_free f θ, eventually_pole_free g θ] with r hf hg
  exact RatFunc.eval_mul (RingHom.id ℂ) (ray θ r) (by simpa using hf) (by simpa using hg)

/--
@isnad1 id=eventual.0h4v.s6.aece0e48c2ec from=translated src=- shape=11c212f6 vocab=0da70dba
-/
theorem eventually_value_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (∑ i ∈ s, f i) = ∑ i ∈ s, value θ r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [value]
  | @insert i s hi ih =>
    filter_upwards [ih, eventually_value_add (f i) (∑ j ∈ s, f j) θ] with r hr ha
    simpa only [Finset.sum_insert hi, hr] using ha

/--
@isnad1 id=eventual.0h2v.s5.5478e9156760 from=translated src=- shape=47222feb vocab=d05e532d
-/
theorem eventually_value_neg (f : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (-f) = -value θ r f := by
  filter_upwards [eventually_value_mul (algebraMap ℂ (RatFunc ℂ) (-1)) f θ] with r hr
  rw [value_constant] at hr
  simpa only [map_neg, map_one, neg_one_mul] using hr

/--
@isnad1 id=eventual.0h3v.s5.54667f93feb7 from=translated src=- shape=c4cb29cf vocab=6314cb19
-/
theorem eventually_value_sub (f g : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r (f - g) = value θ r f - value θ r g := by
  filter_upwards [eventually_value_add f (-g) θ, eventually_value_neg g θ] with r ha hn
  simpa only [sub_eq_add_neg, hn] using ha

/--
@isnad1 id=eventual.0h2v.s5.4697b138e415 from=translated src=- shape=47222feb vocab=127b07c3
-/
theorem eventually_value_inv (f : RatFunc ℂ) (θ : ℝ) :
    ∀ᶠ r in atTop, value θ r f⁻¹ = (value θ r f)⁻¹ := by
  by_cases hf : f = 0
  · simp [hf, value]
  filter_upwards [eventually_value_mul f f⁻¹ θ] with r hr
  have hh : value θ r f * value θ r f⁻¹ = 1 := by
    rw [← hr, mul_inv_cancel₀ hf]
    simp [value]
  exact eq_inv_of_mul_eq_one_right hh

/--
@isnad1 id=eventual.0h3v.s6.a3a1d67bb7a6 from=translated src=- shape=97ee0994 vocab=40c661d6
-/
theorem eventually_value_pow (f : RatFunc ℂ) (θ : ℝ) (n : ℕ) :
    ∀ᶠ r in atTop, value θ r (f ^ n) = (value θ r f) ^ n := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    filter_upwards [ih, eventually_value_mul (f ^ n) f θ] with r hn hm
    simpa only [pow_succ, hn] using hm

/--
@isnad1 id=eventual.0h3v.s6.27b002488ab0 from=translated src=- shape=97ee0994 vocab=ed7b0d0d
-/
theorem eventually_value_zpow (f : RatFunc ℂ) (θ : ℝ) (n : ℤ) :
    ∀ᶠ r in atTop, value θ r (f ^ n) = (value θ r f) ^ n := by
  cases n with
  | ofNat n =>
    change ∀ᶠ r in atTop, value θ r (f ^ (n : ℤ)) = (value θ r f) ^ (n : ℤ)
    simpa only [zpow_natCast] using eventually_value_pow f θ n
  | negSucc n =>
    filter_upwards [eventually_value_pow f θ (n + 1),
      eventually_value_inv (f ^ (n + 1)) θ] with r hn hi
    simpa only [zpow_negSucc, hn] using hi

/-- Finite matrix multiplication is evaluated exactly on a genuine tail.
@isnad1 id=eventual.0h4v.s7.f3a6dbdc6de4 from=translated src=- shape=ddcde343 vocab=6267614f
-/
theorem eventually_value_matrix_mul {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) (RatFunc ℂ)) (θ : ℝ) :
    ∀ᶠ r in atTop, (A * B).map (value θ r) = A.map (value θ r) * B.map (value θ r) := by
  have hs : ∀ᶠ r in atTop, ∀ i j, value θ r (∑ k, A i k * B k j) =
      ∑ k, value θ r (A i k * B k j) := by
    simp only [Filter.eventually_all]
    intro i j
    exact eventually_value_sum Finset.univ _ θ
  have hm : ∀ᶠ r in atTop, ∀ i j k,
      value θ r (A i k * B k j) = value θ r (A i k) * value θ r (B k j) := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_value_mul _ _ θ
  filter_upwards [hs, hm] with r hs hm
  ext i j
  exact (hs i j).trans (Finset.sum_congr rfl (fun k _ => hm i j k))

end WasowRationalEvaluation
