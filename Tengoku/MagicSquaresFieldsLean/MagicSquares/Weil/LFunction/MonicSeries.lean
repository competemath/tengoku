import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.EulerFactors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- All monic polynomials of a fixed degree, enumerated without choosing
an ordering on the finite field.-/
noncomputable def monicPolynomials (n : ℕ) : Finset (Polynomial F) :=
  Finset.univ.image (monicOfCoeffs n)

/--
@isnad1 id=iff.0h3v.s6.1fb94c81e8c5 from=translated src=- shape=48cac884 vocab=7e98904d
-/
@[simp]
theorem mem_monicPolynomials (n : ℕ) (g : Polynomial F) :
    g ∈ monicPolynomials n ↔ g.Monic ∧ g.natDegree = n := by
  constructor
  · intro hg
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨monicOfCoeffs_monic n v, monicOfCoeffs_natDegree n v⟩
  · intro hg
    obtain ⟨v, hv⟩ := (monicOfCoeffsEquiv (F := F) n).surjective ⟨g, hg⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, congrArg Subtype.val hv⟩

/--
@isnad1 id=eq.0h3v.s6.4abe8eac398c from=translated src=- shape=101c2df8 vocab=b3c97372
-/
theorem sum_monicPolynomials (n : ℕ) (f : Polynomial F → ℂ) :
    ∑ g ∈ monicPolynomials n, f g = ∑ v : Fin n → F, f (monicOfCoeffs n v) := by
  apply Finset.sum_image
  intro v _ w _ h
  apply (monicOfCoeffsEquiv n).injective
  exact Subtype.ext h

/--
@isnad1 id=eq.0h1v.s6.6f2443335683 from=translated src=- shape=5f989be4 vocab=e8cd1860
-/
@[simp]
theorem monicPolynomials_zero : monicPolynomials (F := F) 0 = {1} := by
  ext g
  rw [mem_monicPolynomials, Finset.mem_singleton]
  constructor
  · rintro ⟨hm, hd⟩
    exact eq_one_of_monic_natDegree_zero hm hd
  · rintro rfl
    exact ⟨monic_one, natDegree_one⟩

/-- The degree generating series after excluding a finite set of prime
polynomial divisors.-/
noncomputable def avoidingSeries (w : Polynomial F → ℂ) (S : Finset (Polynomial F)) :
    PowerSeries ℂ :=
  PowerSeries.mk (fun n =>
    ∑ g ∈ (monicPolynomials n).filter (fun g => ∀ p ∈ S, ¬ p ∣ g), w g)

/--
@isnad1 id=eq.0h4v.s9.a26f3592a7ff from=translated src=- shape=ccac73a9 vocab=7968a132
-/
@[simp]
theorem avoidingSeries_coeff (w : Polynomial F → ℂ) (S : Finset (Polynomial F)) (n : ℕ) :
    PowerSeries.coeff n (avoidingSeries w S) =
      ∑ g ∈ (monicPolynomials n).filter (fun g => ∀ p ∈ S, ¬ p ∣ g), w g := by
  simp [avoidingSeries, PowerSeries.coeff_mk]

omit [Fintype F] in
private theorem prime_not_dvd_distinct_monic {p q : Polynomial F}
    (hp : p.Monic) (hq : q.Monic) (hi : Irreducible p) (hj : Irreducible q)
    (hne : p ≠ q) : ¬ p ∣ q := by
  intro hd
  have ha : Associated p q := hi.associated_of_dvd hj hd
  have he := normalize_eq_normalize_iff_associated.mpr ha
  rw [hp.normalize_eq_self, hq.normalize_eq_self] at he
  exact hne he

omit [Fintype F] in
private theorem avoiding_mul_iff (S : Finset (Polynomial F)) (p h : Polynomial F)
    (hS : ∀ q ∈ S, q.Monic ∧ Irreducible q)
    (hp : p.Monic) (hi : Irreducible p) (hnot : p ∉ S) :
    (∀ q ∈ S, ¬ q ∣ p * h) ↔ ∀ q ∈ S, ¬ q ∣ h := by
  constructor
  · intro hav q hq hd
    exact hav q hq (dvd_mul_of_dvd_right hd p)
  · intro hav q hq hd
    rcases (hS q hq).2.prime.dvd_or_dvd hd with hqp | hqh
    · exact prime_not_dvd_distinct_monic (hS q hq).1 hp (hS q hq).2 hi
        (fun he => hnot (he ▸ hq)) hqp
    · exact hav q hq hqh

/-- Multiplication by a new irreducible identifies the excluded terms
with the same weighted monic enumeration in a lower degree.
@isnad1 id=eq.5h5v.s10.a8e052b17f96 from=translated src=- shape=8478508d vocab=acb9def3
-/
theorem sum_monic_divisible_avoiding
    (w : Polynomial F → ℂ)
    (hw : ∀ g h : Polynomial F, g.Monic → h.Monic → w (g * h) = w g * w h)
    (S : Finset (Polynomial F)) (hS : ∀ q ∈ S, q.Monic ∧ Irreducible q)
    (p : Polynomial F) (hp : p.Monic) (hi : Irreducible p) (hnot : p ∉ S) (n : ℕ) :
    (∑ g ∈ (monicPolynomials n).filter (fun g =>
      (∀ q ∈ S, ¬ q ∣ g) ∧ p ∣ g), w g) =
      if p.natDegree ≤ n then
        w p * PowerSeries.coeff (n - p.natDegree) (avoidingSeries w S) else 0 := by
  by_cases hdn : p.natDegree ≤ n
  · rw [ite_eq_left hdn, avoidingSeries_coeff, Finset.mul_sum]
    symm
    apply Finset.sum_bij (fun h _ => p * h)
    · intro h hh
      obtain ⟨⟨hm, hd⟩, hav⟩ := (Finset.mem_filter.mp hh).imp_left (mem_monicPolynomials _ h).mp
      apply Finset.mem_filter.mpr
      refine ⟨(mem_monicPolynomials _ _).mpr ⟨hp.mul hm, ?_⟩, ?_⟩
      · rw [hp.natDegree_mul hm, hd, Nat.add_sub_of_le hdn]
      · exact ⟨(avoiding_mul_iff S p h hS hp hi hnot).mpr hav, dvd_mul_right p h⟩
    · intro h _ k _ he
      exact mul_left_cancel₀ hp.ne_zero he
    · intro g hg
      obtain ⟨⟨gm, gd⟩, hav, hdvd⟩ :=
        (Finset.mem_filter.mp hg).imp_left (mem_monicPolynomials _ g).mp
      obtain ⟨h, rfl⟩ := hdvd
      have hm : h.Monic := hp.of_mul_monic_left gm
      refine ⟨h, Finset.mem_filter.mpr ⟨(mem_monicPolynomials _ _).mpr ⟨hm, ?_⟩,
        (avoiding_mul_iff S p h hS hp hi hnot).mp hav⟩, rfl⟩
      rw [hp.natDegree_mul hm] at gd
      omega
    · intro h hh
      exact (hw p h hp ((mem_monicPolynomials _ _).mp (Finset.mem_filter.mp hh).1).1).symm
  · rw [ite_eq_right hdn]
    apply Finset.sum_eq_zero
    intro g hg
    have hgmon := (mem_monicPolynomials _ _).mp (Finset.mem_filter.mp hg).1
    have hdvd := (Finset.mem_filter.mp hg).2.2
    exact (hdn (hgmon.2 ▸ natDegree_le_of_dvd hdvd hgmon.1.ne_zero)).elim

/-- Removing one irreducible divisor multiplies the generating series
by its Euler denominator.
@isnad1 id=eq.5h4v.s8.84f3f68de46e from=translated src=- shape=f8ffd6ff vocab=9e447ccc
-/
theorem avoidingSeries_insert
    (w : Polynomial F → ℂ)
    (hw : ∀ g h : Polynomial F, g.Monic → h.Monic → w (g * h) = w g * w h)
    (S : Finset (Polynomial F)) (hS : ∀ q ∈ S, q.Monic ∧ Irreducible q)
    (p : Polynomial F) (hp : p.Monic) (hi : Irreducible p) (hnot : p ∉ S) :
    avoidingSeries w (insert p S) = eulerFactor p.natDegree (w p) * avoidingSeries w S := by
  ext n
  rw [eulerFactor, sub_mul, one_mul]
  have hreorder : PowerSeries.C (w p) * PowerSeries.X ^ p.natDegree * avoidingSeries w S =
      PowerSeries.C (w p) * (avoidingSeries w S * PowerSeries.X ^ p.natDegree) := by ring
  rw [hreorder, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((monicPolynomials n).filter (fun g => ∀ q ∈ S, ¬ q ∣ g)) (fun g => p ∣ g) w
  simp only [Finset.filter_filter] at hsplit
  have hins : PowerSeries.coeff n (avoidingSeries w (insert p S)) =
      ∑ g ∈ (monicPolynomials n).filter (fun g =>
        (∀ q ∈ S, ¬ q ∣ g) ∧ ¬ p ∣ g), w g := by
    simp only [avoidingSeries_coeff, Finset.mem_insert, forall_eq_or_imp]
    congr 2
    ext g
    tauto
  rw [hins]
  rw [sum_monic_divisible_avoiding w hw S hS p hp hi hnot n] at hsplit
  rw [avoidingSeries_coeff]
  by_cases hd : p.natDegree ≤ n
  · rw [ite_eq_left hd] at hsplit ⊢
    linear_combination hsplit
  · rw [ite_eq_right hd] at hsplit ⊢
    simpa only [mul_zero, sub_zero, zero_add] using hsplit

/-- Simultaneously remove a finite collection of irreducibles.
@isnad1 id=eq.2h3v.s8.2c30aa6bf6bc from=translated src=- shape=02d37a8a vocab=d3556d85
-/
theorem avoidingSeries_eq_prod_mul
    (w : Polynomial F → ℂ)
    (hw : ∀ g h : Polynomial F, g.Monic → h.Monic → w (g * h) = w g * w h)
    (S : Finset (Polynomial F)) (hS : ∀ q ∈ S, q.Monic ∧ Irreducible q) :
    avoidingSeries w S =
      (∏ p ∈ S, eulerFactor p.natDegree (w p)) * avoidingSeries w ∅ := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hp' := hS p (Finset.mem_insert_self _ _)
    have hS' := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [avoidingSeries_insert w hw S hS' p hp'.1 hp'.2 hp,
      ih hS', Finset.prod_insert hp, mul_assoc]

/-- The constant coefficient survives every prime exclusion.
@isnad1 id=eq.2h3v.s7.de03bafb39c4 from=translated src=- shape=ba1d9b3d vocab=3e6662c4
-/
theorem avoidingSeries_constantCoeff (w : Polynomial F → ℂ) (hw1 : w 1 = 1)
    (S : Finset (Polynomial F)) (hS : ∀ q ∈ S, Irreducible q) :
    PowerSeries.constantCoeff (avoidingSeries w S) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, avoidingSeries_coeff, monicPolynomials_zero]
  have hav : ∀ q ∈ S, ¬ q ∣ (1 : Polynomial F) := by
    intro q hq hd
    exact (hS q hq).not_isUnit (isUnit_of_dvd_one hd)
  rw [Finset.filter_singleton, ite_eq_left hav, Finset.sum_singleton, hw1]

/-- All monic irreducibles up to a specified degree.-/
noncomputable def monicIrreduciblesThrough (n : ℕ) : Finset (Polynomial F) :=
  ((Finset.range (n + 1)).biUnion (fun d => monicPolynomials d)).filter Irreducible

/--
@isnad1 id=iff.0h3v.s7.ac116ddc7e3b from=translated src=- shape=6928c397 vocab=ee9bf93c
-/
@[simp]
theorem mem_monicIrreduciblesThrough (n : ℕ) (p : Polynomial F) :
    p ∈ monicIrreduciblesThrough n ↔ p.Monic ∧ Irreducible p ∧ p.natDegree ≤ n := by
  simp only [monicIrreduciblesThrough, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_range, mem_monicPolynomials]
  constructor
  · rintro ⟨⟨d, hd, hm, he⟩, hi⟩
    exact ⟨hm, hi, by omega⟩
  · rintro ⟨hm, hi, hd⟩
    exact ⟨⟨p.natDegree, by omega, hm, rfl⟩, hi⟩

/-- No positive-degree monic polynomial of degree at most `n` survives
exclusion of all irreducibles through degree `n`.
@isnad1 id=eq.2h4v.s7.1cb16486e164 from=translated src=- shape=8b33d507 vocab=d9bcc3b8
-/
theorem avoidingSeries_coeff_eq_zero (w : Polynomial F → ℂ) {n k : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) :
    PowerSeries.coeff k (avoidingSeries w (monicIrreduciblesThrough n)) = 0 := by
  rw [avoidingSeries_coeff]
  apply Finset.sum_eq_zero
  intro g hg
  obtain ⟨hgm, hgd⟩ := (mem_monicPolynomials _ _).mp (Finset.mem_filter.mp hg).1
  have hunit : ¬ IsUnit g := by
    intro hu
    have he := hgm.eq_one_of_isUnit hu
    simp only [he, natDegree_one] at hgd
    omega
  obtain ⟨p, hp⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hgm.ne_zero hunit
  obtain ⟨hirr, hmon, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hgm.ne_zero).mp hp
  have hpn : p.natDegree ≤ n := (natDegree_le_of_dvd hdvd hgm.ne_zero).trans (hgd ▸ hkn)
  exact ((Finset.mem_filter.mp hg).2 p
    ((mem_monicIrreduciblesThrough n p).mpr ⟨hmon, hirr, hpn⟩) hdvd).elim

/-- Vanishing through degree `n` forces the first `n` logarithmic
 derivative coefficients to vanish.
@isnad1 id=eq.2h2v.s7.f89a8a19ea59 from=translated src=- shape=c37fe25a vocab=2d730490
-/
theorem logDerivative_coeff_eq_zero_of_initial_vanishing (P : PowerSeries ℂ)
    {n : ℕ} (hn : 0 < n) (hP : ∀ k, 0 < k → k ≤ n → PowerSeries.coeff k P = 0) :
    PowerSeries.coeff (n - 1) (formalLogDerivative P) = 0 := by
  rw [formalLogDerivative, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [PowerSeries.coeff_derivative, hP (ij.1 + 1) (by omega) (by omega), zero_mul, zero_mul]

end MagicSquares.LN97
