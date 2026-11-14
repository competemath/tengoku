import Tengoku.Twinprime.TwinPrime.Analytic.CharacterVaughan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact finite Type I character factorizations

A supported Dirichlet convolution can be reindexed by its positive first
factor and the exact natural quotient of the endpoint. The two Type I
terms in Vaughan's identity are special cases. All cutoffs, endpoints,
and moduli are allowed; these identities assume no character estimates.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

/-- A finite convolution with its first factor supported at most `K`.
Natural division retains the product cutoff exactly, including empty sums.
@isnad1 id=eq.1h6v.s8.1434c62590f0 from=translated src=- shape=b4d5a717 vocab=121097e3
-/
theorem sum_character_convolution_eq_factor_sum {q : ℕ}
    (f g : ArithmeticFunction ℝ) (K t : ℕ) (χ : DirichletCharacter ℂ q)
    (hf : ∀ d, K < d → f d = 0) :
    (∑ n ∈ Ioc 0 t, ((f * g) n : ℂ) * χ n) =
      ∑ d ∈ Ioc 0 K, (f d : ℂ) * χ d *
        ∑ r ∈ Ioc 0 (t / d), (g r : ℂ) * χ r := by
  have hexpand :
      (∑ n ∈ Ioc 0 t, ((f * g) n : ℂ) * χ n) =
        ∑ n ∈ Ioc 0 t, ∑ dr ∈ n.divisorsAntidiagonal with dr.1 ≤ K,
          (f dr.1 : ℂ) * (g dr.2 : ℂ) * χ n := by
    apply sum_congr rfl
    intro n _
    rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, sum_mul, sum_filter]
    apply sum_congr rfl
    intro dr _
    by_cases hd : dr.1 ≤ K
    · simp [hd, Complex.ofReal_mul]
    · simp [hd, hf dr.1 (Nat.lt_of_not_ge hd)]
  rw [hexpand]
  simp_rw [mul_sum]
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun nr _ => (⟨nr.2.1, nr.2.2⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨n, dr⟩ hnr
    obtain ⟨hn, hdr⟩ := mem_sigma.mp hnr
    obtain ⟨hanti, hdK⟩ := mem_filter.mp hdr
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hanti).1
    change dr.1 * dr.2 = n at hprod
    have hdpos : 0 < dr.1 := Nat.pos_of_ne_zero
      (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hanti)
    have hrpos : 0 < dr.2 := Nat.pos_of_ne_zero
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hanti)
    refine mem_sigma.mpr ⟨mem_Ioc.mpr ⟨hdpos, hdK⟩, mem_Ioc.mpr ⟨hrpos, ?_⟩⟩
    apply (Nat.le_div_iff_mul_le hdpos).mpr
    simpa only [mul_comm dr.2 dr.1, hprod] using (mem_Ioc.mp hn).2
  · rintro ⟨n, dr⟩ hnr ⟨m, er⟩ hmr h
    have hd : dr.1 = er.1 := congrArg Sigma.fst h
    have hr : dr.2 = er.2 := congrArg (fun p : Σ _ : ℕ, ℕ => p.2) h
    have hdr : dr = er := Prod.ext hd hr
    subst er
    have hnprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hnr).2).1).1
    have hmprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hmr).2).1).1
    have hnm : n = m := hnprod.symm.trans hmprod
    subst m
    rfl
  · rintro ⟨d, r⟩ hdr
    obtain ⟨hdI, hrI⟩ := mem_sigma.mp hdr
    obtain ⟨hdpos, hdK⟩ := mem_Ioc.mp hdI
    obtain ⟨hrpos, hrt⟩ := mem_Ioc.mp hrI
    have hpos : 0 < d * r := Nat.mul_pos hdpos hrpos
    have hle : d * r ≤ t := by
      simpa only [mul_comm r d] using (Nat.le_div_iff_mul_le hdpos).mp hrt
    refine ⟨⟨d * r, (d, r)⟩, ?_, rfl⟩
    exact mem_sigma.mpr ⟨mem_Ioc.mpr ⟨hpos, hle⟩,
      mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hpos.ne'⟩, hdK⟩⟩
  · rintro ⟨n, dr⟩ hnr
    have hprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hnr).2).1).1
    change dr.1 * dr.2 = n at hprod
    dsimp only
    rw [← hprod, Nat.cast_mul, map_mul]
    ring

/-- The logarithmically weighted Type I convolution.-/
def characterVaughanI1 {q : ℕ} (U t : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Ioc 0 t, ((moebiusLow U * ArithmeticFunction.log) n : ℂ) * χ n

/-- The compactly supported coefficient convolved with the zeta function.-/
def characterVaughanI2 {q : ℕ} (U V t : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Ioc 0 t, ((vaughanCoefficient U V * ζ) n : ℂ) * χ n

/-- The exact logarithmically weighted first-factor formula.
@isnad1 id=eq.0h4v.s7.f3dd63b50cb1 from=translated src=- shape=034786d0 vocab=6073baf6
-/
theorem characterVaughanI1_eq_factor_sum {q : ℕ} (U t : ℕ)
    (χ : DirichletCharacter ℂ q) :
    characterVaughanI1 U t χ =
      ∑ d ∈ Ioc 0 U, ((μ d : ℝ) : ℂ) * χ d *
        ∑ r ∈ Ioc 0 (t / d), (Real.log (r : ℝ) : ℂ) * χ r := by
  unfold characterVaughanI1
  rw [sum_character_convolution_eq_factor_sum (moebiusLow U)
    ArithmeticFunction.log U t χ (fun d hd => by
      simp [moebiusLow, cutoffLow_apply, Nat.not_le.mpr hd])]
  apply sum_congr rfl
  intro d hd
  simp only [moebiusLow, cutoffLow_apply, (mem_Ioc.mp hd).2, ite_true,
    ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply]

/-- The coefficient support is exactly bounded by `U*V`; the quotient keeps
the original endpoint, even when an outer factor exceeds it.
@isnad1 id=eq.0h5v.s7.702ccf491e16 from=translated src=- shape=aecc27a4 vocab=ef54ee85
-/
theorem characterVaughanI2_eq_factor_sum {q : ℕ} (U V t : ℕ)
    (χ : DirichletCharacter ℂ q) :
    characterVaughanI2 U V t χ =
      ∑ d ∈ Ioc 0 (U * V), (vaughanCoefficient U V d : ℂ) * χ d *
        ∑ r ∈ Ioc 0 (t / d), χ r := by
  unfold characterVaughanI2
  rw [sum_character_convolution_eq_factor_sum (vaughanCoefficient U V)
    ζ (U * V) t χ (vaughanCoefficient_eq_zero_of_lt U V)]
  apply sum_congr rfl
  intro d _
  congr 1
  apply sum_congr rfl
  intro r hr
  have hr0 : r ≠ 0 := (mem_Ioc.mp hr).1.ne'
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hr0]

/-- The full finite identity in terms of the named Type I and Type II sums.
@isnad1 id=eq.0h5v.s6.3cceafd3e67f from=translated src=- shape=4b05fc3a vocab=f6e69ab4
-/
theorem characterPsi_eq_vaughan_types {q : ℕ} (U V t : ℕ)
    (χ : DirichletCharacter ℂ q) :
    characterPsi t χ = characterVaughanI1 U t χ - characterVaughanI2 U V t χ +
      characterPsi (min t V) χ + characterVaughanII U V t χ :=
  characterPsi_eq_vaughan U V t χ

end TwinPrime.Analytic
