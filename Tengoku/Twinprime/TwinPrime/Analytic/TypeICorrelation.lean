import Tengoku.Twinprime.TwinPrime.Analytic.PrimeDistribution
import Tengoku.Twinprime.TwinPrime.Analytic.GrowthBounds
import Tengoku.Twinprime.TwinPrime.Analytic.EvenAsymptotics
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusTotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Type I correlation and its classical inputs

Finite reindexing identifies the odd-modulus main coefficient with the exact
two-factor sum `totientTypeIMain`, including its shared-prime correction.
The finite error separates odd progression errors and even-modulus exceptions.
The limiting results retain Bombieri–Vinogradov and main-coefficient decay as
separate explicit hypotheses.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- The convolution main coefficient is exactly the two-factor totient sum.
No multiplicativity of the totient at noncoprime factors is used.
@isnad1 id=eq.0h2v.s6.a14bc1a217ed from=translated src=- shape=54e5e21e vocab=345287f5
-/
theorem vaughanCoefficient_odd_totient_sum_eq (U V : ℕ) :
    (∑ q ∈ range (U * V + 1) with Odd q,
      vaughanCoefficient U V q / Nat.totient q) = totientTypeIMain U V := by
  have hexpand :
      (∑ q ∈ range (U * V + 1) with Odd q,
        vaughanCoefficient U V q / Nat.totient q) =
      ∑ q ∈ range (U * V + 1) with Odd q,
        ∑ db ∈ q.divisorsAntidiagonal with db.1 ≤ U ∧ db.2 ≤ V,
          (μ db.1 : ℝ) * vonMangoldt db.2 / Nat.totient q := by
    apply sum_congr rfl
    intro q _
    rw [vaughanCoefficient_apply, sum_div, sum_filter]
    apply sum_congr rfl
    intro db _
    split_ifs <;> simp
  rw [hexpand, sum_sigma']
  unfold totientTypeIMain
  rw [← sum_product' (oddCutoff U) (oddCutoff V)
    (fun d b => (μ d : ℝ) * vonMangoldt b / Nat.totient (d * b))]
  apply sum_bij (fun qdb _ => qdb.2)
  · rintro ⟨q, db⟩ hqdb
    obtain ⟨hq, hdb⟩ := mem_sigma.mp hqdb
    obtain ⟨hanti, hdU, hbV⟩ := mem_filter.mp hdb
    have hprod : db.1 * db.2 = q := (Nat.mem_divisorsAntidiagonal.mp hanti).1
    have hodd : Odd (db.1 * db.2) := by rw [hprod]; exact (mem_filter.mp hq).2
    apply mem_product.mpr
    constructor
    · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero
        (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hanti), hdU⟩,
        Nat.Odd.of_mul_left hodd⟩
    · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero
        (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hanti), hbV⟩,
        Nat.Odd.of_mul_right hodd⟩
  · rintro ⟨q, db⟩ hqdb ⟨r, ec⟩ hrec heq
    dsimp only at heq
    subst ec
    have hq := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hqdb).2).1).1
    have hr := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hrec).2).1).1
    have hqr : q = r := hq.symm.trans hr
    subst r
    rfl
  · intro db hdb
    obtain ⟨hd, hb⟩ := mem_product.mp hdb
    obtain ⟨hdI, hdodd⟩ := mem_filter.mp hd
    obtain ⟨hbI, hbodd⟩ := mem_filter.mp hb
    have hdU := mem_Icc.mp hdI
    have hbV := mem_Icc.mp hbI
    have hprod := Nat.mul_le_mul hdU.2 hbV.2
    refine ⟨⟨db.1 * db.2, db⟩, mem_sigma.mpr ⟨?_, ?_⟩, rfl⟩
    · exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hprod), hdodd.mul hbodd⟩
    · exact mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr
        ⟨rfl, (Nat.mul_pos hdU.1 hbV.1).ne'⟩, hdU.2, hbV.2⟩
  · rintro ⟨q, db⟩ hqdb
    have hprod := (Nat.mem_divisorsAntidiagonal.mp
      (mem_filter.mp (mem_sigma.mp hqdb).2).1).1
    dsimp only
    rw [hprod]

/--
@isnad1 id=eq.0h3v.s8.a19f2adcdbb0 from=translated src=- shape=53e894bf vocab=497a8aeb
-/
theorem typeITerm_eq_odd_add_even (U V X : ℕ) :
    typeITerm U V X =
      (∑ q ∈ range (U * V + 1) with Odd q, vaughanCoefficient U V q *
        ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2)) +
      ∑ q ∈ range (U * V + 1) with Even q, vaughanCoefficient U V q *
        ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2) := by
  rw [typeITerm_eq_progressions]
  simpa only [Nat.not_odd_iff_even] using
    (sum_filter_add_sum_filter_not (range (U * V + 1)) Odd
      (fun q => vaughanCoefficient U V q *
        ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2))).symm

/--
@isnad1 id=le.1h3v.s6.c9e434cdb532 from=translated src=- shape=4669af87 vocab=cc417530
-/
theorem abs_vaughanCoefficient_le_log_cutoff (U V q : ℕ) (hq : q ≤ U * V) :
    |vaughanCoefficient U V q| ≤ Real.log (U * V + 1) := by
  by_cases hq0 : q = 0
  · subst q
    simp only [ArithmeticFunction.map_zero, abs_zero]
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) (U * V)
    push_cast at this
    linarith
  · apply (abs_vaughanCoefficient_le_log U V q).trans
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hq0)
    exact_mod_cast (show q ≤ U * V + 1 by omega)

end TwinPrime.Analytic
