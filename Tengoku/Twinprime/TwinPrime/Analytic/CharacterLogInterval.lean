import Tengoku.Twinprime.TwinPrime.Analytic.CharacterInterval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmically weighted primitive-character sums

Finite Abel summation transfers the proved Pólya--Vinogradov estimate to a
logarithmic weight. The variation of `log n` is its final value, giving a
factor of two. Natural endpoint zero is included, and the resulting bound
also controls the logarithmically weighted Type I inner sums.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- Finite Abel summation with complex coefficients, retaining the boundary term.-/
theorem discrete_abel_Ioc_complex (a b : ℕ) (hab : a ≤ b) (w e : ℕ → ℂ) :
    (∑ n ∈ Ioc a b, w n * e n) =
      w b * (∑ n ∈ Ioc a b, e n) -
      ∑ t ∈ Ico a b, (w (t + 1) - w t) * (∑ n ∈ Ioc a t, e n) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [sum_Ioc_succ_top hab (fun n => w n * e n),
        sum_Ioc_succ_top hab e,
        sum_Ico_succ_top hab (fun t => (w (t + 1) - w t) * (∑ n ∈ Ioc a t, e n)), ih]
      ring

/-- Nonnegative increasing real weights cost at most twice the endpoint weight.-/
theorem norm_sum_Ioc_real_mul_le_of_partial_sums (a b : ℕ) (hab : a ≤ b)
    (w : ℕ → ℝ) (e : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw0 : 0 ≤ w a)
    (hw : MonotoneOn w (Set.Icc a b))
    (hE : ∀ t ∈ Icc a b, ‖∑ n ∈ Ioc a t, e n‖ ≤ C) :
    ‖∑ n ∈ Ioc a b, (w n : ℂ) * e n‖ ≤ 2 * C * w b := by
  have hwb : 0 ≤ w b := hw0.trans (hw ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  have hvar : (∑ t ∈ Ico a b, |w (t + 1) - w t|) = w b - w a := by
    calc
      _ = ∑ t ∈ Ico a b, (w (t + 1) - w t) := by
        apply sum_congr rfl
        intro t ht
        obtain ⟨hat, htb⟩ := mem_Ico.mp ht
        apply abs_of_nonneg
        exact sub_nonneg.mpr (hw ⟨hat, htb.le⟩ ⟨by omega, by omega⟩ (Nat.le_succ t))
      _ = _ := sum_Ico_sub w hab
  rw [discrete_abel_Ioc_complex a b hab (fun n => (w n : ℂ)) e]
  calc
    _ ≤ ‖(w b : ℂ) * (∑ n ∈ Ioc a b, e n)‖ +
        ‖∑ t ∈ Ico a b, ((w (t + 1) : ℂ) - w t) * (∑ n ∈ Ioc a t, e n)‖ :=
      norm_sub_le _ _
    _ ≤ |w b| * C + ∑ t ∈ Ico a b, |w (t + 1) - w t| * C := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hE b (mem_Icc.mpr ⟨hab, le_rfl⟩)) (abs_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro t ht
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (hE t (mem_Icc.mpr ⟨(mem_Ico.mp ht).1, (mem_Ico.mp ht).2.le⟩)) (abs_nonneg _)
    _ = C * (w b + (w b - w a)) := by
      rw [← sum_mul, hvar, abs_of_nonneg hwb]
      ring
    _ ≤ _ := by nlinarith

/-- The totalized real logarithm is nondecreasing on natural-number casts.-/
theorem log_natCast_mono : Monotone (fun n : ℕ => Real.log (n : ℝ)) := by
  intro m n hmn
  rcases m.eq_zero_or_pos with rfl | hm
  · simpa using Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn)

theorem norm_sum_primitive_character_Ioc_le {q : ℕ} (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℕ) :
    ‖∑ n ∈ Ioc 0 T, χ (n : ZMod q)‖ ≤ Real.sqrt q * (1 + Real.log q) := by
  have hI : Ioc 0 T = Ico 1 (T + 1) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hI]
  exact norm_sum_primitive_character_Ico_le hq χ hχ 1 (T + 1)

/-- The logarithmically weighted prefix bound also holds at `T=0`.-/
theorem norm_sum_primitive_character_log_Ioc_le {q : ℕ} (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℕ) :
    ‖∑ n ∈ Ioc 0 T, (Real.log (n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
      2 * Real.sqrt q * (1 + Real.log q) * Real.log T := by
  have hC : 0 ≤ Real.sqrt (q : ℝ) * (1 + Real.log q) := by
    have := Real.log_natCast_nonneg q
    positivity
  have h := norm_sum_Ioc_real_mul_le_of_partial_sums 0 T (Nat.zero_le T)
    (fun n => Real.log (n : ℝ)) (fun n => χ (n : ZMod q))
    (Real.sqrt q * (1 + Real.log q)) hC (by simp) (log_natCast_mono.monotoneOn _)
    (fun t _ => norm_sum_primitive_character_Ioc_le hq χ hχ t)
  simpa only [mul_assoc] using h

/-- A common endpoint controls all shorter logarithmically weighted prefixes.-/
theorem norm_sum_primitive_character_log_Ioc_le_uniform {q : ℕ} (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℕ) {t : ℕ} (ht : t ≤ T) :
    ‖∑ n ∈ Ioc 0 t, (Real.log (n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
      2 * Real.sqrt q * (1 + Real.log q) * Real.log T := by
  apply (norm_sum_primitive_character_log_Ioc_le hq χ hχ t).trans
  apply mul_le_mul_of_nonneg_left (log_natCast_mono ht)
  have := Real.log_natCast_nonneg q
  positivity

/-- A finite Type I estimate with independently clipped inner endpoints.-/
theorem norm_sum_typeI_log_character_le_uniform {q : ℕ} (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : Finset ℕ)
    (a : ℕ → ℂ) (T : ℕ) (t : ℕ → ℕ) (ht : ∀ m ∈ s, t m ≤ T) :
    ‖∑ m ∈ s, a m * χ (m : ZMod q) *
      ∑ n ∈ Ioc 0 (t m), (Real.log (n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
      (2 * Real.sqrt q * (1 + Real.log q) * Real.log T) * ∑ m ∈ s, ‖a m‖ := by
  calc
    _ ≤ ∑ m ∈ s, ‖a m * χ (m : ZMod q) *
        ∑ n ∈ Ioc 0 (t m), (Real.log (n : ℝ) : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ s, ‖a m‖ * (2 * Real.sqrt q * (1 + Real.log q) * Real.log T) := by
      apply sum_le_sum
      intro m hm
      rw [norm_mul, norm_mul]
      apply mul_le_mul
      · exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      · exact norm_sum_primitive_character_log_Ioc_le_uniform hq χ hχ T (ht m hm)
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = _ := by rw [← sum_mul]; ring

/-- The usual Type I cutoff `n ≤ T/m`; zero quotients need no exception.-/
theorem norm_sum_typeI_log_character_le {q : ℕ} (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (U T : ℕ) (a : ℕ → ℂ) :
    ‖∑ m ∈ Ioc 0 U, a m * χ (m : ZMod q) *
      ∑ n ∈ Ioc 0 (T / m), (Real.log (n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
      (2 * Real.sqrt q * (1 + Real.log q) * Real.log T) *
        ∑ m ∈ Ioc 0 U, ‖a m‖ :=
  norm_sum_typeI_log_character_le_uniform hq χ hχ (Ioc 0 U) a T (fun m => T / m)
    (fun m _ => Nat.div_le_self T m)

end TwinPrime.Analytic
