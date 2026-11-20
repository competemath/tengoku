import Tengoku.Hellingerrepolean4.Hellinger.TranslationEquality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms odd_dual_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms odd_dual_equality_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms odd_dual_bound_all` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms odd_dual_equality_iff_all` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms endpoint_one_approach` (it only prints; the queue checks the axioms of every declaration). -/

/-! Sharp finite-noise dual inequality on odd real functions. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.OddDual

open Hellinger.Fourier Hellinger.ChannelSections

/--
@isnad1 id=le.1h2v.s6.3c9c7d933e1a from=translated src=- shape=0a730dd5 vocab=e61100ef
-/
theorem scalar_dual (u t : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    root u + t * u ≤ Real.sqrt (1 + t ^ 2) := by
  have hr : (root u) ^ 2 = 1 - u ^ 2 :=
    Real.sq_sqrt (by nlinarith [hu.1, hu.2])
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (t * root u - u)]

/--
@isnad1 id=eq.2h2v.s6.fc1126c857f5 from=translated src=- shape=afe94c13 vocab=5ad473e2
-/
theorem scalar_dual_equality (u t : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (heq : root u + t * u = Real.sqrt (1 + t ^ 2)) : t * root u = u := by
  have hr : (root u) ^ 2 = 1 - u ^ 2 :=
    Real.sq_sqrt (by nlinarith [hu.1, hu.2])
  have hs : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  rw [← heq] at hs
  have hid : (t * root u - u) ^ 2 = 0 := by nlinarith
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hid)

/--
@isnad1 id=eq.1h3v.s5.cf6f75695101 from=translated src=- shape=d57c08bb vocab=7f3f07ff
-/
theorem bsc_weight_symm (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : Bool) :
    (bsc ρ hρ).weight x y = (bsc ρ hρ).weight y x := by
  change (if x = y then _ else _) = (if y = x then _ else _)
  simp only [eq_comm]

/--
@isnad1 id=eq.1h4v.s6.4c0ece992f32 from=translated src=- shape=73cd272c vocab=cad44345
-/
theorem cube_weight_symm (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (x y : Cube n) : (cubeBSC n ρ hρ).weight x y = (cubeBSC n ρ hρ).weight y x := by
  change (∏ i, (bsc ρ hρ).weight (x i) (y i)) = ∏ i, (bsc ρ hρ).weight (y i) (x i)
  simp only [bsc_weight_symm]

/--
@isnad1 id=eq.1h3v.s5.826edfb6d635 from=translated src=- shape=a80ab394 vocab=968ee098
-/
theorem bsc_weight_antipode (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : Bool) :
    (bsc ρ hρ).weight (!x) (!y) = (bsc ρ hρ).weight x y := by
  cases x <;> cases y <;> rfl

/--
@isnad1 id=eq.1h4v.s7.3ff2ea574599 from=translated src=- shape=316612be vocab=0ce2985a
-/
theorem cube_weight_antipode (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (x y : Cube n) : (cubeBSC n ρ hρ).weight (antipode n x) (antipode n y) =
      (cubeBSC n ρ hρ).weight x y := by
  change (∏ i, (bsc ρ hρ).weight (!(x i)) (!(y i))) = ∏ i, (bsc ρ hρ).weight (x i) (y i)
  simp only [bsc_weight_antipode]

/--
@isnad1 id=eq.2h4v.s7.244e6f418037 from=translated src=- shape=ba5102e8 vocab=9ba7de2c
-/
theorem noise_odd (n : ℕ) (h : Cube n → ℝ)
    (hodd : ∀ x, h (antipode n x) = -h x) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (y : Cube n) : (cubeBSC n ρ hρ).apply h (antipode n y) = -(cubeBSC n ρ hρ).apply h y := by
  unfold UniformChannel.apply
  rw [← (antipode n).sum_comp (fun x => (cubeBSC n ρ hρ).weight (antipode n y) x * h x)]
  simp only [cube_weight_antipode, hodd, mul_neg, Finset.sum_neg_distrib]

/--
@isnad1 id=eq.1h4v.s7.c47dbfa10a38 from=translated src=- shape=d877ae2c vocab=0ea978fb
-/
theorem noise_selfadjoint (n : ℕ) (f g : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun y => f y * (cubeBSC n ρ hρ).apply g y) =
      mean (fun x => g x * (cubeBSC n ρ hρ).apply f x) := by
  unfold mean UniformChannel.apply
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [cube_weight_symm n ρ hρ y x]
  ring

def oddSign {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube (n + 1)) : ℝ :=
  if 0 < g x then 1 else if g x < 0 then -1 else boolSign (x 0)

/--
@isnad1 id=or.0h3v.s5.bee845894f26 from=translated src=- shape=efa62e6f vocab=0fcfa75e
-/
theorem oddSign_boolean {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube (n + 1)) :
    oddSign g x = -1 ∨ oddSign g x = 1 := by
  unfold oddSign
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl
  · cases x 0 <;> norm_num [boolSign]

/--
@isnad1 id=eq.1h3v.s8.9a00edd64f4e from=translated src=- shape=022d307b vocab=b451f0ff
-/
theorem oddSign_odd {n : ℕ} (g : Cube (n + 1) → ℝ)
    (hodd : ∀ x, g (antipode (n + 1) x) = -g x) (x : Cube (n + 1)) :
    oddSign g (antipode (n + 1) x) = -oddSign g x := by
  unfold oddSign
  rw [hodd]
  change (if 0 < -g x then 1 else if -g x < 0 then -1 else boolSign (!(x 0))) = _
  rw [boolSign_neg]
  split_ifs <;> norm_num at * <;> linarith

/--
@isnad1 id=eq.0h3v.s5.47919b98a5fe from=translated src=- shape=4d7ab5f7 vocab=526f510d
-/
theorem oddSign_mul {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube (n + 1)) :
    oddSign g x * g x = |g x| := by
  unfold oddSign
  split_ifs with hp hn
  · rw [one_mul, abs_of_pos hp]
  · rw [neg_one_mul, abs_of_neg hn]
  · have hz : g x = 0 := by linarith
    rw [hz, mul_zero, abs_zero]

def dualFunctional {n : ℕ} (h : Cube n → ℝ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : ℝ :=
  mean (fun x => Real.sqrt (1 + h x ^ 2)) - mean (fun y => |(cubeBSC n ρ hρ).apply h y|)

/--
@isnad1 id=le.1h3v.s8.694ad4272eb4 from=translated src=- shape=135ca410 vocab=03cbdaa6
-/
theorem root_mean_le_dual (n : ℕ) (h : Cube (n + 1) → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun y => root ((cubeBSC (n + 1) ρ hρ).apply
      (oddSign ((cubeBSC (n + 1) ρ hρ).apply h)) y)) ≤ dualFunctional h ρ hρ := by
  let f := oddSign ((cubeBSC (n + 1) ρ hρ).apply h)
  have hf (x) : f x ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases oddSign_boolean ((cubeBSC (n + 1) ρ hρ).apply h) x with hx | hx <;> simp [f, hx]
  have hle := mean_mono
    (fun y => root ((cubeBSC (n + 1) ρ hρ).apply f y) +
      h y * (cubeBSC (n + 1) ρ hρ).apply f y)
    (fun y => Real.sqrt (1 + h y ^ 2))
    (fun y => scalar_dual _ _ ((cubeBSC (n + 1) ρ hρ).apply_mem_Icc f hf y))
  rw [Fourier.mean_add, noise_selfadjoint] at hle
  have hsign : mean (fun x => f x * (cubeBSC (n + 1) ρ hρ).apply h x) =
      mean (fun x => |(cubeBSC (n + 1) ρ hρ).apply h x|) := by
    congr 1
    funext x
    exact oddSign_mul _ x
  rw [hsign] at hle
  exact le_sub_iff_add_le.mpr hle

/--
@isnad1 id=le.2h3v.s8.b92cd170425b from=translated src=- shape=f71c293d vocab=1cf515ed
-/
theorem odd_dual_bound (n : ℕ) (h : Cube (n + 1) → ℝ)
    (hodd : ∀ x, h (antipode (n + 1) x) = -h x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : root ρ ≤ dualFunctional h ρ hρ := by
  exact (ParityBlocks.antipodal_hellinger n _ (oddSign_boolean _)
    (oddSign_odd _ (noise_odd _ h hodd ρ hρ)) ρ hρ).trans (root_mean_le_dual n h ρ hρ)

/--
@isnad1 id=eq.1h5v.s6.4ff5abdafaac from=translated src=- shape=e831abc1 vocab=6c736ce4
-/
theorem noise_signed_coordinate (n : ℕ) (i : Fin n) (negative : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    (cubeBSC n ρ hρ).apply
        (fun y => if negative then -boolSign (y i) else boolSign (y i)) x =
      ρ * (if negative then -boolSign (x i) else boolSign (x i)) := by
  have hbase : (cubeBSC n ρ hρ).apply (fun y => boolSign (y i)) x = ρ * boolSign (x i) := by
    have hchar : character n {i} = (fun y => boolSign (y i)) := by
      funext y
      simp [character]
    simpa only [hchar, Finset.card_singleton, pow_one] using character_eigenfunction n {i} ρ hρ x
  cases negative
  · exact hbase
  · simp only [ite_true, UniformChannel.apply_neg, hbase]
    ring

/--
@isnad1 id=ex.5h3v.s8.7b8707a49ab0 from=translated src=- shape=c6eec3a4 vocab=418b9875
-/
theorem odd_dual_equality_form (n : ℕ) (h : Cube (n + 1) → ℝ)
    (hodd : ∀ x, h (antipode (n + 1) x) = -h x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (heq : dualFunctional h ρ hρ = root ρ) :
    ∃ i : Fin (n + 1), ∃ negative : Bool,
      h = fun x => (ρ / root ρ) * (if negative then -boolSign (x i) else boolSign (x i)) := by
  let K := cubeBSC (n + 1) ρ hρ
  let f := oddSign (K.apply h)
  have hf := oddSign_boolean (K.apply h)
  have hfc (x) : f x ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases hf x with hx | hx <;> simp [f, hx]
  have hfo := oddSign_odd (K.apply h) (noise_odd _ h hodd ρ hρ)
  have hrl := ParityBlocks.antipodal_hellinger n f hf hfo ρ hρ
  have hru := root_mean_le_dual n h ρ hρ
  have hr : mean (fun y => root (K.apply f y)) = root ρ := by
    rw [heq] at hru
    exact le_antisymm hru hrl
  obtain ⟨i, negative, hform⟩ :=
    (AntipodalEquality.root_mean_equality_iff_signed_dictator
      n f hf hfo ρ hρ hρpos hρlt).mp hr
  have hnoise (y : Cube (n + 1)) : K.apply f y =
      ρ * (if negative then -boolSign (y i) else boolSign (y i)) := by
    rw [hform]
    exact noise_signed_coordinate _ i negative ρ hρ y
  have hroots (y : Cube (n + 1)) : root (K.apply f y) = root ρ := by
    rw [hnoise]
    cases negative <;> simp [root, mul_pow, boolSign_sq]
  have hsign : mean (fun x => f x * K.apply h x) = mean (fun x => |K.apply h x|) := by
    congr 1
    funext x
    exact oddSign_mul _ x
  have hscalar : mean (fun y => root (K.apply f y) + h y * K.apply f y) =
      mean (fun y => Real.sqrt (1 + h y ^ 2)) := by
    rw [Fourier.mean_add, noise_selfadjoint, hsign, hr]
    unfold dualFunctional at heq
    linarith
  have hpoint := eq_of_mean_eq_of_le _ _
    (fun y => scalar_dual (K.apply f y) (h y) (K.apply_mem_Icc f hfc y)) hscalar
  have hc : root ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hρ.1]))
  refine ⟨i, negative, ?_⟩
  funext x
  have hmul := scalar_dual_equality _ _ (K.apply_mem_Icc f hfc x) (hpoint x)
  rw [hroots, hnoise] at hmul
  apply (eq_div_iff hc).mpr at hmul
  rw [hmul]
  ring

/--
@isnad1 id=eq.0h5v.s5.0a71be19cfa7 from=translated src=- shape=5646c569 vocab=283d1e00
-/
theorem apply_const_mul {Ω : Type*} [Fintype Ω] (K : UniformChannel Ω)
    (a : ℝ) (f : Ω → ℝ) (y : Ω) : K.apply (fun x => a * f x) y = a * K.apply f y := by
  unfold UniformChannel.apply
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/--
@isnad1 id=eq.2h4v.s6.674364561347 from=translated src=- shape=12a4823a vocab=c2ad0570
-/
theorem scaled_coordinate_attains (n : ℕ) (i : Fin n) (negative : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1) :
    dualFunctional
      (fun x : Cube n => (ρ / root ρ) * (if negative then -boolSign (x i) else boolSign (x i)))
      ρ hρ = root ρ := by
  have hcpos : 0 < root ρ := Real.sqrt_pos.mpr (by nlinarith [hρ.1])
  have hcsq : (root ρ) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith [hρ.1])
  have hcamp : 0 ≤ ρ / root ρ := div_nonneg hρ.1 (le_of_lt hcpos)
  have hsq (x : Cube n) :
      ((ρ / root ρ) * (if negative then -boolSign (x i) else boolSign (x i))) ^ 2 =
        (ρ / root ρ) ^ 2 := by
    cases negative <;> simp [mul_pow, boolSign_sq]
  have habs (x : Cube n) :
      |(cubeBSC n ρ hρ).apply
        (fun y => (ρ / root ρ) * (if negative then -boolSign (y i) else boolSign (y i))) x| =
        (ρ / root ρ) * ρ := by
    rw [apply_const_mul, noise_signed_coordinate, abs_mul, abs_of_nonneg hcamp,
      abs_mul, abs_of_nonneg hρ.1]
    cases negative <;> cases x i <;> norm_num [boolSign]
  have hsqrt : Real.sqrt (1 + (ρ / root ρ) ^ 2) = 1 / root ρ := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity : 0 ≤ 1 + (ρ / root ρ) ^ 2)
      (by positivity : 0 ≤ 1 / root ρ)).mpr
    field_simp [ne_of_gt hcpos]
    nlinarith
  unfold dualFunctional
  simp_rw [hsq, habs]
  rw [mean_const, mean_const, hsqrt]
  field_simp [ne_of_gt hcpos]
  nlinarith

/--
@isnad1 id=iff.4h3v.s8.8b9ff1100a5c from=translated src=- shape=3e20daeb vocab=418b9875
-/
theorem odd_dual_equality_iff (n : ℕ) (h : Cube (n + 1) → ℝ)
    (hodd : ∀ x, h (antipode (n + 1) x) = -h x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    dualFunctional h ρ hρ = root ρ ↔
      ∃ i : Fin (n + 1), ∃ negative : Bool,
        h = fun x => (ρ / root ρ) * (if negative then -boolSign (x i) else boolSign (x i)) := by
  constructor
  · exact odd_dual_equality_form n h hodd ρ hρ hρpos hρlt
  · rintro ⟨i, negative, rfl⟩
    exact scaled_coordinate_attains _ i negative ρ hρ hρlt

/--
@isnad1 id=le.2h3v.s6.48091d2f28ae from=translated src=- shape=0818a979 vocab=c01c5cdf
-/
theorem odd_dual_bound_all (n : ℕ) (h : Cube n → ℝ)
    (hodd : ∀ x, h (antipode n x) = -h x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : root ρ ≤ dualFunctional h ρ hρ := by
  cases n with
  | zero =>
    have hh : h = fun _ => 0 := by
      funext x
      have ha : antipode 0 x = x := Subsingleton.elim _ _
      have hx := hodd x
      rw [ha] at hx
      linarith
    rw [hh]
    have hr : root ρ ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])
    simpa [dualFunctional, UniformChannel.apply, mean_const] using hr
  | succ n => exact odd_dual_bound n h hodd ρ hρ

/--
@isnad1 id=iff.4h3v.s7.2c243b7a1052 from=translated src=- shape=8196967a vocab=a787bc31
-/
theorem odd_dual_equality_iff_all (n : ℕ) (h : Cube n → ℝ)
    (hodd : ∀ x, h (antipode n x) = -h x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    dualFunctional h ρ hρ = root ρ ↔
      ∃ i : Fin n, ∃ negative : Bool,
        h = fun x => (ρ / root ρ) * (if negative then -boolSign (x i) else boolSign (x i)) := by
  cases n with
  | zero =>
    have hh : h = fun _ => 0 := by
      funext x
      have ha : antipode 0 x = x := Subsingleton.elim _ _
      have hx := hodd x
      rw [ha] at hx
      linarith
    rw [hh]
    have hr : root ρ < 1 := by
      have hs : (root ρ) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith [hρ.1])
      nlinarith [Real.sqrt_nonneg (1 - ρ ^ 2)]
    simp only [IsEmpty.exists_iff]
    simp only [dualFunctional, UniformChannel.apply, mul_zero, Finset.sum_const_zero,
      zero_pow (by omega : 2 ≠ 0), add_zero, Real.sqrt_one, abs_zero, mean_const, sub_zero]
    exact iff_false_intro (ne_of_gt hr)
  | succ n => exact odd_dual_equality_iff n h hodd ρ hρ hρpos hρlt

/--
@isnad1 id=eq.0h1v.s4.9e151069f93e from=translated src=- shape=45c01c4a vocab=fded7e98
-/
theorem zero_attains_at_zero (n : ℕ) :
    dualFunctional (fun _ : Cube n => 0) 0 (by norm_num) = root 0 := by
  simp [dualFunctional, UniformChannel.apply, root, mean_const]

/--
@isnad1 id=eq.1h5v.s6.3d1fd3d37798 from=translated src=- shape=7db95d60 vocab=b51278e7
-/
theorem coordinate_functional (n : ℕ) (i : Fin n) (negative : Bool) (t ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    dualFunctional (fun x : Cube n => t * (if negative then -boolSign (x i) else boolSign (x i)))
      ρ hρ = Real.sqrt (1 + t ^ 2) - |t| * ρ := by
  have hsq (x : Cube n) :
      (t * (if negative then -boolSign (x i) else boolSign (x i))) ^ 2 = t ^ 2 := by
    cases negative <;> simp [mul_pow, boolSign_sq]
  have habs (x : Cube n) :
      |(cubeBSC n ρ hρ).apply
        (fun y => t * (if negative then -boolSign (y i) else boolSign (y i))) x| = |t| * ρ := by
    rw [apply_const_mul, noise_signed_coordinate, abs_mul, abs_mul, abs_of_nonneg hρ.1]
    cases negative <;> cases x i <;> norm_num [boolSign]
  unfold dualFunctional
  simp_rw [hsq, habs]
  rw [mean_const, mean_const]

/--
@isnad1 id=ex.1h3v.s6.3b4fb61340fb from=translated src=- shape=178d9295 vocab=50b2bfb5
-/
theorem endpoint_one_approach (n : ℕ) (i : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧
      0 < dualFunctional (fun x : Cube n => t * boolSign (x i)) 1 (by norm_num) ∧
      dualFunctional (fun x : Cube n => t * boolSign (x i)) 1 (by norm_num) < ε := by
  let t := 1 / ε
  have ht : 0 < t := one_div_pos.mpr hε
  have hte : t * ε = 1 := one_div_mul_cancel (ne_of_gt hε)
  refine ⟨t, le_of_lt ht, ?_, ?_⟩
  all_goals
    have hformula := coordinate_functional n i false t 1 (by norm_num)
    simp only [Bool.false_eq_true, ite_false, abs_of_pos ht, mul_one] at hformula
    rw [hformula]
    have hs : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
    have hs0 := Real.sqrt_nonneg (1 + t ^ 2)
    nlinarith

end Hellinger.OddDual
