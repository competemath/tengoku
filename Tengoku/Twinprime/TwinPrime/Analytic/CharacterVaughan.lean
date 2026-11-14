import Tengoku.Twinprime.TwinPrime.Analytic.CharacterSums
import Tengoku.Twinprime.TwinPrime.Analytic.Vaughan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact finite Vaughan character identities

The Type II character sum has an exact positive-factor domain with its
integer product cutoff retained. The full finite Vaughan identity includes
the low von Mangoldt term, also when the endpoint lies below the cutoff.
No distribution or maximal estimate is assumed.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

/-- The Type II convolution twisted by a Dirichlet character.-/
def characterVaughanII {q : ℕ} (U V t : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Ioc 0 t, ((moebiusHigh U * vaughanBeta V) n : ℂ) * χ n

/-- Reindex the convolution by its two positive factors and unique product.
The ambient bound T may exceed the selected endpoint t.-/
theorem characterVaughanII_eq_pair_sum {q : ℕ} (U V t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    characterVaughanII U V t χ =
      ∑ dr ∈ ((Ioc U T).product (Ioc V T)).filter (fun dr => dr.1 * dr.2 ≤ t),
        ((μ dr.1 : ℝ) : ℂ) * (vaughanBeta V dr.2 : ℂ) * χ (dr.1 * dr.2) := by
  have hexpand : characterVaughanII U V t χ =
      ∑ n ∈ Ioc 0 t,
        ∑ dr ∈ n.divisorsAntidiagonal with U < dr.1 ∧ V < dr.2,
          ((μ dr.1 : ℝ) : ℂ) * (vaughanBeta V dr.2 : ℂ) * χ n := by
    unfold characterVaughanII
    apply sum_congr rfl
    intro n _
    rw [vaughanBilinear_apply, Complex.ofReal_sum, sum_mul, sum_filter]
    apply sum_congr rfl
    intro dr _
    split_ifs <;> simp [Complex.ofReal_mul]
  rw [hexpand, sum_sigma']
  apply sum_bij (fun nr _ => nr.2)
  · rintro ⟨n, dr⟩ hnr
    obtain ⟨hnI, hdr⟩ := mem_sigma.mp hnr
    obtain ⟨hanti, hU, hV⟩ := mem_filter.mp hdr
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hanti).1
    change dr.1 * dr.2 = n at hprod
    have hdpos : 0 < dr.1 := Nat.pos_of_ne_zero
      (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hanti)
    have hrpos : 0 < dr.2 := Nat.pos_of_ne_zero
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hanti)
    have hdle : dr.1 ≤ n := hprod ▸ Nat.le_mul_of_pos_right dr.1 hrpos
    have hrle : dr.2 ≤ n := hprod ▸ Nat.le_mul_of_pos_left dr.2 hdpos
    have hn := mem_Ioc.mp hnI
    refine mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Ioc.mpr ⟨hU, hdle.trans (hn.2.trans ht)⟩,
        mem_Ioc.mpr ⟨hV, hrle.trans (hn.2.trans ht)⟩⟩, ?_⟩
    simpa only [hprod] using hn.2
  · rintro ⟨n, dr⟩ hnr ⟨m, er⟩ hmr h
    dsimp only at h
    subst er
    have hnprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hnr).2).1).1
    have hmprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hmr).2).1).1
    have hnm : n = m := hnprod.symm.trans hmprod
    subst m
    rfl
  · intro dr hdr
    obtain ⟨hdrange, hprodle⟩ := mem_filter.mp hdr
    have hU := (mem_Ioc.mp (mem_product.mp hdrange).1).1
    have hV := (mem_Ioc.mp (mem_product.mp hdrange).2).1
    have hpos : 0 < dr.1 * dr.2 :=
      Nat.mul_pos ((Nat.zero_le U).trans_lt hU) ((Nat.zero_le V).trans_lt hV)
    refine ⟨⟨dr.1 * dr.2, dr⟩, ?_, rfl⟩
    exact mem_sigma.mpr ⟨mem_Ioc.mpr ⟨hpos, hprodle⟩,
      mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hpos.ne'⟩, hU, hV⟩⟩
  · rintro ⟨n, dr⟩ hnr
    have hprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hnr).2).1).1
    change dr.1 * dr.2 = n at hprod
    dsimp only
    rw [← Nat.cast_mul, hprod]

/-- The same exact factorization as an iterated sum, retaining `m*n ≤ t`.-/
theorem characterVaughanII_eq_double_sum {q : ℕ} (U V t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    characterVaughanII U V t χ =
      ∑ m ∈ Ioc U T, ∑ n ∈ Ioc V T with m * n ≤ t,
        ((μ m : ℝ) : ℂ) * (vaughanBeta V n : ℂ) * χ (m * n) := by
  rw [characterVaughanII_eq_pair_sum U V t T χ ht, sum_filter]
  calc
    _ = ∑ m ∈ Ioc U T, ∑ n ∈ Ioc V T,
        if m * n ≤ t then ((μ m : ℝ) : ℂ) * (vaughanBeta V n : ℂ) * χ (m * n) else 0 :=
      sum_finset_product _ _ _ (fun _ => mem_product)
    _ = _ := by simp only [sum_filter]

/-- A global positive square domain with the two cutoff masks made explicit.
This form is ready for partition into fixed dyadic boxes.-/
theorem characterVaughanII_eq_masked_double_sum {q : ℕ} (U V t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    characterVaughanII U V t χ =
      ∑ m ∈ Ioc 0 T, ∑ n ∈ Ioc 0 T with m * n ≤ t,
        (if U < m ∧ m ≤ T then ((μ m : ℝ) : ℂ) else 0) *
          (if V < n ∧ n ≤ T then (vaughanBeta V n : ℂ) else 0) * χ (m * n) := by
  have hfilter (L : ℕ) : (Ioc 0 T).filter (fun n => L < n) = Ioc L T := by
    ext n
    simp only [mem_filter, mem_Ioc]
    omega
  rw [characterVaughanII_eq_double_sum U V t T χ ht, ← hfilter U, ← hfilter V]
  simp only [sum_filter]
  apply sum_congr rfl
  intro m hm
  have hmT := (mem_Ioc.mp hm).2
  by_cases hUm : U < m
  · simp only [hUm, true_and, hmT, ite_true]
    apply sum_congr rfl
    intro n hn
    have hnT := (mem_Ioc.mp hn).2
    by_cases hVn : V < n <;> by_cases hprod : m * n ≤ t <;> simp [hVn, hnT, hprod]
  · simp [hUm]

/-- The low von Mangoldt convolution is the original character sum with
the endpoint truncated at V.-/
theorem sum_mangoldtLow_character_eq {q : ℕ} (V t : ℕ) (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Ioc 0 t, (mangoldtLow V n : ℂ) * χ n) = characterPsi (min t V) χ := by
  have hfilter : (Ioc 0 t).filter (fun n => n ≤ V) = Ioc 0 (min t V) := by
    ext n
    simp only [mem_filter, mem_Ioc, le_min_iff]
    omega
  unfold characterPsi
  rw [← hfilter, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : n ≤ V <;> simp [mangoldtLow, cutoffLow_apply, hn]

/-- Full finite Vaughan identity for the character sum. The low term is
retained, so the result applies to every natural endpoint and both cutoffs.-/
theorem characterPsi_eq_vaughan {q : ℕ} (U V t : ℕ) (χ : DirichletCharacter ℂ q) :
    characterPsi t χ =
      (∑ n ∈ Ioc 0 t, ((moebiusLow U * ArithmeticFunction.log) n : ℂ) * χ n) -
      (∑ n ∈ Ioc 0 t, ((vaughanCoefficient U V * ζ) n : ℂ) * χ n) +
        characterPsi (min t V) χ + characterVaughanII U V t χ := by
  have hpoint (n : ℕ) : (vonMangoldt n : ℂ) =
      ((moebiusLow U * ArithmeticFunction.log) n : ℂ) -
        ((vaughanCoefficient U V * ζ) n : ℂ) + (mangoldtLow V n : ℂ) +
          ((moebiusHigh U * vaughanBeta V) n : ℂ) := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughanIdentity U V)
    have hreal : (vonMangoldt n : ℝ) =
        (moebiusLow U * ArithmeticFunction.log) n - (vaughanCoefficient U V * ζ) n +
          mangoldtLow V n + (moebiusHigh U * vaughanBeta V) n := by
      simpa only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
        vaughanCoefficient, vaughanBeta, mul_assoc] using h
    exact_mod_cast hreal
  rw [← sum_mangoldtLow_character_eq V t χ]
  unfold characterPsi characterVaughanII
  rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  rw [hpoint n]
  ring

end TwinPrime.Analytic
