import Tengoku.Hellingerrepolean4.Hellinger.BooleanNoise
import Tengoku.Hellingerrepolean4.Hellinger.Rigidity
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Tactic.FunProp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms inversion` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms parseval` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms walsh_noise` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms noise_second_moment` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# The normalized Walsh transform on the actual Boolean cube

All sums are over every point of Fin n → Bool. Orthogonality, inversion,
Parseval, and noise identities are proved from the finite product definitions.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.Fourier

abbrev Cube (n : ℕ) := Fin n → Bool

def support {n : ℕ} (s : Cube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s i = true)

def degree {n : ℕ} (s : Cube n) : ℕ := (support s).card

def phase {n : ℕ} (s x : Cube n) : ℝ :=
  ∏ i, boolSign (s i && x i)

def walsh {n : ℕ} (f : Cube n → ℝ) (s : Cube n) : ℝ :=
  mean (fun x => f x * phase s x)

/--
@isnad1 id=eq.0h1v.s5.5a41cc7e1493 from=translated src=- shape=5b09d1d5 vocab=3c1d983f
-/
theorem cube_card (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by simp [Cube]

/--
@isnad1 id=eq.0h3v.s4.16e671124261 from=translated src=- shape=7a5478ec vocab=7745ccf7
-/
theorem phase_symm {n : ℕ} (s x : Cube n) : phase s x = phase x s := by
  simp only [phase, Bool.and_comm]

/--
@isnad1 id=eq.0h3v.s5.17d31f05a7c4 from=translated src=- shape=f8527af6 vocab=1b2b07d6
-/
theorem phase_sq {n : ℕ} (s x : Cube n) : phase s x ^ 2 = 1 := by
  simp only [phase, ← Finset.prod_pow, boolSign_sq, Finset.prod_const_one]

/--
@isnad1 id=eq.0h3v.s4.9f0c94f4a0a1 from=translated src=- shape=dbb63bdc vocab=4e38551b
-/
theorem phase_character {n : ℕ} (s x : Cube n) :
    phase s x = character n (support s) x := by
  apply Finset.prod_congr rfl
  intro i hi
  cases h : s i <;> simp [support, h, boolSign]

/--
@isnad1 id=eq.0h2v.s5.4d334cdf1ef2 from=translated src=- shape=c884364c vocab=fe565f00
-/
theorem coordinate_orthogonality (a b : Bool) :
    (∑ x : Bool, boolSign (a && x) * boolSign (b && x)) =
      if a = b then (2 : ℝ) else 0 := by
  cases a <;> cases b <;> norm_num [boolSign]

/--
@isnad1 id=eq.0h3v.s6.e20d568657a3 from=translated src=- shape=188fc59a vocab=43f7cba4
-/
theorem sum_phase_mul {n : ℕ} (s t : Cube n) :
    (∑ x, phase s x * phase t x) =
      if s = t then (2 : ℝ) ^ n else 0 := by
  simp only [phase, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    boolSign (s i && b) * boolSign (t i && b))]
  simp_rw [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
      by_contra! heq
      exact h (funext heq)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/--
@isnad1 id=eq.0h3v.s6.2e943a502f4c from=translated src=- shape=afae830a vocab=d6db8453
-/
theorem orthogonality {n : ℕ} (s t : Cube n) :
    mean (fun x => phase s x * phase t x) = if s = t then 1 else 0 := by
  rw [mean, cube_card, sum_phase_mul]
  split_ifs <;> simp

/--
@isnad1 id=eq.0h2v.s5.220a234ab99a from=translated src=- shape=3e114db1 vocab=e083a2e3
-/
theorem walsh_zero {n : ℕ} (f : Cube n → ℝ) :
    walsh f (fun _ => false) = mean f := by
  simp [walsh, phase, boolSign]

/--
@isnad1 id=eq.0h3v.s5.e88e31c7768d from=translated src=- shape=7ac07487 vocab=58260ae7
-/
theorem inversion {n : ℕ} (f : Cube n → ℝ) (x : Cube n) :
    f x = ∑ s, walsh f s * phase s x := by
  have hexpand : (∑ s, walsh f s * phase s x) =
      (Fintype.card (Cube n) : ℝ)⁻¹ *
        ∑ y, f y * (∑ s, phase s y * phase s x) := by
    unfold walsh mean
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hk (y : Cube n) :
      (∑ s, phase s y * phase s x) =
        if y = x then (2 : ℝ) ^ n else 0 := by
    simpa only [phase_symm] using sum_phase_mul y x
  rw [hexpand]
  simp only [hk]
  simp [mul_left_comm]

/--
@isnad1 id=eq.0h3v.s6.4f31a845cfce from=translated src=- shape=65faa79c vocab=780e73dc
-/
theorem mean_mul_expansion {n : ℕ} (f : Cube n → ℝ) (a : Cube n → ℝ) :
    mean (fun x => f x * (∑ s, a s * phase s x)) =
      ∑ s, a s * walsh f s := by
  unfold walsh mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Parseval for every real function on every finite Boolean cube.
@isnad1 id=eq.0h2v.s6.b33b5bfdccc1 from=translated src=- shape=87287e5e vocab=565ff4a1
-/
theorem parseval {n : ℕ} (f : Cube n → ℝ) :
    mean (fun x => f x ^ 2) = ∑ s, walsh f s ^ 2 := by
  calc
    mean (fun x => f x ^ 2) =
        mean (fun x => f x * (∑ s, walsh f s * phase s x)) := by
      congr 1
      funext x
      rw [← inversion f x, pow_two]
    _ = ∑ s, walsh f s * walsh f s := mean_mul_expansion f (walsh f)
    _ = ∑ s, walsh f s ^ 2 := by simp only [pow_two]

/--
@isnad1 id=eq.0h3v.s5.0c6f315c24e4 from=translated src=- shape=fc186200 vocab=5b737036
-/
theorem walsh_phase {n : ℕ} (s t : Cube n) :
    walsh (phase s) t = if s = t then 1 else 0 := orthogonality s t

/--
@isnad1 id=eq.0h3v.s5.5d57caa688f6 from=translated src=- shape=47868e8e vocab=58260ae7
-/
theorem walsh_expansion {n : ℕ} (a : Cube n → ℝ) (s : Cube n) :
    walsh (fun x => ∑ t, a t * phase t x) s = a s := by
  unfold walsh
  simp only [mul_comm (∑ t, a t * phase t _) (phase s _)]
  rw [mean_mul_expansion]
  simp [walsh_phase]

/--
@isnad1 id=eq.1h4v.s6.c13a877bff2e from=translated src=- shape=f3c2e5dc vocab=04bbbde3
-/
theorem noise_phase {n : ℕ} (s : Cube n)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    (cubeBSC n ρ hρ).apply (phase s) x = ρ ^ degree s * phase s x := by
  have hp : phase s = character n (support s) := funext (phase_character s)
  rw [hp]
  exact character_eigenfunction n (support s) ρ hρ x

/-- The actual product BSC has the Walsh multiplier rho to the frequency degree.
@isnad1 id=eq.1h4v.s6.a4387ada820a from=translated src=- shape=f7097839 vocab=6c248c16
-/
theorem noise_expansion {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Cube n) :
    (cubeBSC n ρ hρ).apply f x =
      ∑ s, (ρ ^ degree s * walsh f s) * phase s x := by
  have hf : f = fun y => ∑ s, walsh f s * phase s y := by
    funext y
    exact inversion f y
  calc
    (cubeBSC n ρ hρ).apply f x =
        (cubeBSC n ρ hρ).apply (fun y => ∑ s, walsh f s * phase s y) x := by
      exact congrArg (fun g => (cubeBSC n ρ hρ).apply g x) hf
    _ = ∑ s, walsh f s * (cubeBSC n ρ hρ).apply (phase s) x := by
      unfold UniformChannel.apply
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ s, (ρ ^ degree s * walsh f s) * phase s x := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [noise_phase]
      ring

/--
@isnad1 id=eq.1h4v.s6.34993a3d67eb from=translated src=- shape=8a619b86 vocab=11862e7e
-/
theorem walsh_noise {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (s : Cube n) :
    walsh ((cubeBSC n ρ hρ).apply f) s = ρ ^ degree s * walsh f s := by
  have hn : (cubeBSC n ρ hρ).apply f =
      fun x => ∑ t, (ρ ^ degree t * walsh f t) * phase t x := by
    funext x
    exact noise_expansion f ρ hρ x
  rw [hn, walsh_expansion]

/--
@isnad1 id=eq.1h3v.s7.912bad8eae4b from=translated src=- shape=e4460bd3 vocab=862e98f8
-/
theorem noise_second_moment {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) =
      ∑ s, ρ ^ (2 * degree s) * walsh f s ^ 2 := by
  rw [parseval]
  simp only [walsh_noise, mul_pow, ← pow_mul, Nat.mul_comm]

/--
@isnad1 id=eq.1h2v.s6.a47e9a2cb05e from=translated src=- shape=1d34d24a vocab=aedfc2a9
-/
theorem boolean_parseval {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) :
    (∑ s, walsh f s ^ 2) = 1 := by
  rw [← parseval]
  have hs : (fun x => f x ^ 2) = fun _ => (1 : ℝ) := by
    funext x
    rcases hf x with h | h <;> simp [h]
  rw [hs, mean_const]

/--
@isnad1 id=eq.0h3v.s4.d7fc7d5a0a4e from=translated src=- shape=4ffe586d vocab=8a4855c2
-/
theorem phase_abs {n : ℕ} (s x : Cube n) : |phase s x| = 1 := by
  rw [← Real.sqrt_sq_eq_abs, phase_sq]
  norm_num

/--
@isnad1 id=eq.0h3v.s5.6513c89ecbd5 from=translated src=- shape=e65f855c vocab=c51a012e
-/
theorem pow_degree {n : ℕ} (t : ℝ) (s : Cube n) :
    t ^ degree s = ∏ i, if s i = true then t else 1 := by
  rw [← Finset.prod_filter]
  simp [degree, support]

/--
@isnad1 id=eq.0h2v.s6.a360b90e6c33 from=translated src=- shape=eb53b010 vocab=76b0825b
-/
theorem sum_pow_degree (n : ℕ) (t : ℝ) :
    (∑ s : Cube n, t ^ degree s) = (1 + t) ^ n := by
  simp_rw [pow_degree]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) =>
    if b = true then t else (1 : ℝ))]
  simp [add_comm]

def translate {n : ℕ} (v x : Cube n) : Cube n :=
  fun i => Bool.xor (x i) (v i)

/--
@isnad1 id=involuti.0h2v.s3.38661553645b from=translated src=- shape=8e4ef8bc vocab=f136e9be
-/
theorem translate_involutive {n : ℕ} (v : Cube n) :
    Function.Involutive (translate v) := by
  intro x
  funext i
  cases hxi : x i <;> cases hvi : v i <;> simp [translate, hxi, hvi]

def translationEquiv {n : ℕ} (v : Cube n) : Cube n ≃ Cube n :=
  (translate_involutive v).toPerm

/--
@isnad1 id=eq.0h3v.s4.bb22d5f62b40 from=translated src=- shape=a1f2d8cb vocab=f17b6118
-/
theorem translate_twice {n : ℕ} (v x : Cube n) :
    translate v (translate v x) = x := translate_involutive v x

/--
@isnad1 id=eq.0h3v.s5.3bd0a3913342 from=translated src=- shape=c1a52133 vocab=6f10d2ea
-/
theorem mean_translate {n : ℕ} (f : Cube n → ℝ) (v : Cube n) :
    mean (fun x => f (translate v x)) = mean f := by
  unfold mean
  rw [show (∑ x, f (translate v x)) = ∑ x, f x from (translationEquiv v).sum_comp f]

/--
@isnad1 id=eq.0h3v.s4.7d48a2852154 from=translated src=- shape=5a50c0d6 vocab=7bfbc203
-/
theorem coordinate_phase_translate (s x v : Bool) :
    boolSign (s && Bool.xor x v) =
      boolSign (s && x) * boolSign (s && v) := by
  cases s <;> cases x <;> cases v <;> norm_num [boolSign]

/--
@isnad1 id=eq.0h4v.s5.33c026a30f7e from=translated src=- shape=1b7067fe vocab=f9bd635b
-/
theorem phase_translate {n : ℕ} (s v x : Cube n) :
    phase s (translate v x) = phase s x * phase s v := by
  simp only [phase, translate, coordinate_phase_translate, Finset.prod_mul_distrib]

def autocorrelation {n : ℕ} (f : Cube n → ℝ) (v : Cube n) : ℝ :=
  mean (fun x => f x * f (translate v x))

/-- The autocorrelation formula follows from actual Fourier inversion.
@isnad1 id=eq.0h3v.s6.1cc4fa8b83e5 from=translated src=- shape=bc65f3cb vocab=188bd633
-/
theorem autocorrelation_formula {n : ℕ} (f : Cube n → ℝ) (v : Cube n) :
    autocorrelation f v = ∑ s, walsh f s ^ 2 * phase s v := by
  have he (x : Cube n) : f (translate v x) =
      ∑ s, (walsh f s * phase s v) * phase s x := by
    rw [inversion f (translate v x)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [phase_translate]
    ring
  unfold autocorrelation
  simp_rw [he]
  rw [mean_mul_expansion]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/--
@isnad1 id=eq.0h2v.s4.641098136c70 from=translated src=- shape=3f084210 vocab=e0a97b0b
-/
theorem phase_zero {n : ℕ} (x : Cube n) : phase (fun _ => false) x = 1 := by
  simp [phase, boolSign]

/--
@isnad1 id=eq.0h2v.s6.65cb0072c613 from=translated src=- shape=a03b3d7d vocab=798b91ed
-/
theorem sum_phase {n : ℕ} (v : Cube n) :
    (∑ s : Cube n, phase s v) =
      if v = (fun _ => false) then (2 : ℝ) ^ n else 0 := by
  have h := sum_phase_mul v (fun _ => false)
  simp only [phase_zero, mul_one] at h
  simpa only [phase_symm] using h

/--
@isnad1 id=eq.0h3v.s5.4f53a46142c7 from=translated src=- shape=f9e647ab vocab=95060fba
-/
theorem mean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, mul_add]

/--
@isnad1 id=eq.0h3v.s5.c2deea11ce1a from=translated src=- shape=f9e647ab vocab=4bfa3951
-/
theorem mean_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, mul_sub]

/--
@isnad1 id=eq.0h3v.s5.2c52cbe6f712 from=translated src=- shape=d1a0213d vocab=fcb3915a
-/
theorem mean_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c := by
  simp [mean, Finset.sum_mul, mul_assoc]

/--
@isnad1 id=eq.0h3v.s5.c295e38dc05c from=translated src=- shape=adf02c15 vocab=fcb3915a
-/
theorem mean_const_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  simp [mean, Finset.mul_sum, mul_left_comm]

/--
@isnad1 id=eq.0h3v.s5.11b6de4ccc6c from=translated src=- shape=f48f0e7b vocab=4148da91
-/
theorem mean_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (f : ι → Ω → ℝ) :
    mean (fun x => ∑ i, f i x) = ∑ i, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.mul_sum]

/--
@isnad1 id=le.1h2v.s5.7a4a8f858c26 from=translated src=- shape=92c325ac vocab=3b642aae
-/
theorem mean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  unfold mean
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun x _ => hf x))

/--
@isnad1 id=le.1h3v.s5.d81e0584d3cc from=translated src=- shape=6f600fa3 vocab=3b642aae
-/
theorem mean_le_mean {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ)
    (hfg : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  unfold mean
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun x _ => hfg x)) (by positivity)

/-- A normalized finite Cauchy-Schwarz inequality with an explicit pointwise
factorization, useful without fractional real powers.
@isnad1 id=le.3h4v.s6.093934470b49 from=translated src=- shape=a195760c vocab=21649a6e
-/
theorem mean_sq_le_mean_mul {Ω : Type*} [Fintype Ω] (r f g : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (he : ∀ x, r x ^ 2 = f x * g x) :
    mean r ^ 2 ≤ mean f * mean g := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => hf x) (fun x _ => hg x) (fun x _ => (he x).le)
  have hc := mul_le_mul_of_nonneg_left h (sq_nonneg ((Fintype.card Ω : ℝ)⁻¹))
  unfold mean
  simpa only [mul_pow, pow_two, mul_assoc, mul_left_comm] using hc

def unit {n : ℕ} (i : Fin n) : Cube n :=
  fun j => if j = i then true else false

/--
@isnad1 id=ne.0h2v.s3.c816ec117162 from=translated src=- shape=fad827db vocab=3311d527
-/
theorem unit_ne_zero {n : ℕ} (i : Fin n) : unit i ≠ (fun _ => false) := by
  intro h
  have hi := congrFun h i
  simp [unit] at hi

/--
@isnad1 id=eq.0h4v.s4.bb2e4f18d0d8 from=translated src=- shape=0e3065b9 vocab=f17b6118
-/
theorem translate_comp {n : ℕ} (u v x : Cube n) :
    translate u (translate v x) = translate (translate u v) x := by
  funext i
  cases hxi : x i <;> cases hui : u i <;> cases hvi : v i <;>
    simp [translate, hxi, hui, hvi]

/--
@isnad1 id=eq.0h3v.s5.10ee28e8e5a4 from=translated src=- shape=ca5dc5f0 vocab=88afea63
-/
theorem translate_unit {n : ℕ} (i : Fin n) (x : Cube n) :
    translate (unit i) x = Function.update x i (!(x i)) := by
  funext j
  by_cases h : j = i
  · subst j
    cases hxi : x i <;> simp [translate, unit, hxi]
  · simp [translate, unit, h]

/--
@isnad1 id=ne.1h3v.s4.55c6c735d4f7 from=translated src=- shape=2357762e vocab=9bb05a7b
-/
theorem unit_pair_ne_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    translate (unit j) (unit i) ≠ (fun _ => false) := by
  intro h
  have hi := congrFun h i
  simp [translate, unit, hij] at hi

/--
@isnad1 id=eq.0h4v.s5.74e344953a6b from=translated src=- shape=72f94321 vocab=77f02f8f
-/
theorem mean_translated_product {n : ℕ} (f : Cube n → ℝ) (u v : Cube n) :
    mean (fun x => f (translate u x) * f (translate v x)) =
      autocorrelation f (translate v u) := by
  have h := mean_translate
    (fun x => f (translate u x) * f (translate v x)) u
  simp only [translate_twice, translate_comp] at h
  exact h.symm

end Hellinger.Fourier
