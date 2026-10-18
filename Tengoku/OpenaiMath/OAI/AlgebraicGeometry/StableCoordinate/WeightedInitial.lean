import Tengoku.Seed.RingTheory.MvPolynomial.WeightedHomogeneous
import Tengoku.Seed.Algebra.MvPolynomial.NoZeroDivisors
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# Highest components for integer-weighted polynomials

The weights may be negative. These lemmas give the top-product identity needed
in §3 for the initial ideal of a principal hypersurface relation.
-/

namespace StableCoordinate
namespace WeightedInitial

open MvPolynomial

variable {σ K : Type*} [CommSemiring K]

/-- Every monomial appearing in `p` has integer weight at most `d`. -/
def Bounded (w : σ → ℤ) (p : MvPolynomial σ K) (d : ℤ) : Prop :=
  ∀ m : σ →₀ ℕ, p.coeff m ≠ 0 → Finsupp.weight w m ≤ d

lemma bounded_zero (w : σ → ℤ) (d : ℤ) : Bounded w (0 : MvPolynomial σ K) d := by
  intro m hm
  simp at hm

lemma Bounded.mono {w : σ → ℤ} {p : MvPolynomial σ K} {d e : ℤ}
    (hp : Bounded w p d) (hde : d ≤ e) : Bounded w p e :=
  fun m hm => (hp m hm).trans hde

lemma Bounded.mul {w : σ → ℤ} {p q : MvPolynomial σ K} {d e : ℤ}
    (hp : Bounded w p d) (hq : Bounded w q e) : Bounded w (p * q) (d + e) := by
  classical
  intro m hm
  rw [coeff_mul] at hm
  obtain ⟨⟨a,b⟩, hab, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have ha : p.coeff a ≠ 0 := left_ne_zero_of_mul hterm
  have hb : q.coeff b ≠ 0 := right_ne_zero_of_mul hterm
  have hab' : a + b = m := Finset.mem_antidiagonal.mp hab
  rw [← hab', map_add]
  exact add_le_add (hp a ha) (hq b hb)

/-- A monomial has the expected weight bound, with arbitrary coefficient. -/
lemma bounded_monomial (w : σ → ℤ) (m : σ →₀ ℕ) (c : K) {d : ℤ}
    (hm : Finsupp.weight w m ≤ d) : Bounded w (monomial m c) d := by
  intro a ha
  have hw := isWeightedHomogeneous_monomial w m c rfl ha
  exact hw.le.trans hm

/-- The highest possible component of a product is the product of the respective
highest possible components. This does not assume their nonvanishing. -/
theorem component_mul_of_bounded {w : σ → ℤ} {p q : MvPolynomial σ K} {d e : ℤ}
    (hp : Bounded w p d) (hq : Bounded w q e) :
    weightedHomogeneousComponent w (d + e) (p * q) =
      weightedHomogeneousComponent w d p * weightedHomogeneousComponent w e q := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  rw [Finset.ite_sum_zero]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ hab
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
  have hab' : a + b = m := Finset.mem_antidiagonal.mp hab
  by_cases ha : p.coeff a = 0
  · simp [ha]
  by_cases hb : q.coeff b = 0
  · simp [hb]
  have hap := hp a ha
  have hbq := hq b hb
  have hweight : Finsupp.weight w a + Finsupp.weight w b = Finsupp.weight w m := by
    rw [← map_add, hab']
  have hiff : Finsupp.weight w m = d + e ↔
      Finsupp.weight w a = d ∧ Finsupp.weight w b = e := by omega
  by_cases hma : Finsupp.weight w a = d <;>
    by_cases hmb : Finsupp.weight w b = e <;> simp [hiff, hma, hmb]

/-- Every nonzero polynomial has a highest integer-weight component. -/
theorem exists_top {w : σ → ℤ} {p : MvPolynomial σ K} (hp : p ≠ 0) :
    ∃ d : ℤ, Bounded w p d ∧ weightedHomogeneousComponent w d p ≠ 0 := by
  classical
  have hs : p.support.Nonempty := support_nonempty.mpr hp
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image p.support (Finsupp.weight w) hs
  refine ⟨Finsupp.weight w m, ?_, ?_⟩
  · intro a ha
    exact hmax a (mem_support_iff.mpr ha)
  · intro h
    have heq := congrArg (fun q : MvPolynomial σ K => q.coeff m) h
    simp only [coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero] at heq
    exact (mem_support_iff.mp hm) heq

/-- A bound with a nonzero component is exactly the weighted total degree. -/
theorem degree_eq_of_top {w : σ → ℤ} {p : MvPolynomial σ K} {d : ℤ}
    (hb : Bounded w p d) (ht : weightedHomogeneousComponent w d p ≠ 0) :
    weightedTotalDegree' w p = (d : WithBot ℤ) := by
  apply le_antisymm
  · rw [weightedTotalDegree', Finset.sup_le_iff]
    intro m hm
    exact WithBot.coe_le_coe.mpr (hb m (mem_support_iff.mp hm))
  · obtain ⟨m, hm⟩ := exists_coeff_ne_zero ht
    rw [coeff_weightedHomogeneousComponent] at hm
    split_ifs at hm with hmd
    · have hb' := Finset.le_sup (f := fun a => (Finsupp.weight w a : WithBot ℤ))
        (mem_support_iff.mpr hm)
      simpa only [weightedTotalDegree', hmd] using hb'
    · exact (hm rfl).elim

section Domain
variable [NoZeroDivisors K]

/-- Nonzero top components multiply to a nonzero top component over a domain. -/
theorem top_mul {w : σ → ℤ} {p q : MvPolynomial σ K} {d e : ℤ}
    (hp : Bounded w p d) (hq : Bounded w q e)
    (htp : weightedHomogeneousComponent w d p ≠ 0)
    (htq : weightedHomogeneousComponent w e q ≠ 0) :
    Bounded w (p * q) (d + e) ∧
      weightedHomogeneousComponent w (d + e) (p * q) ≠ 0 := by
  refine ⟨hp.mul hq, ?_⟩
  rw [component_mul_of_bounded hp hq]
  exact mul_ne_zero htp htq

/-- Weighted total degree is additive under multiplication, even with negative weights. -/
theorem degree_mul (w : σ → ℤ) (p q : MvPolynomial σ K) :
    weightedTotalDegree' w (p * q) = weightedTotalDegree' w p + weightedTotalDegree' w q := by
  by_cases hp : p = 0
  · simp [hp, weightedTotalDegree'_zero]
  by_cases hq : q = 0
  · simp [hq, weightedTotalDegree'_zero]
  obtain ⟨d, hd, htd⟩ := exists_top (w := w) hp
  obtain ⟨e, he, hte⟩ := exists_top (w := w) hq
  obtain ⟨hbound, htop⟩ := top_mul hd he htd hte
  rw [degree_eq_of_top hbound htop, degree_eq_of_top hd htd, degree_eq_of_top he hte]
  rfl

end Domain

section Ring
variable {A : Type*} [CommRing A]

lemma Bounded.neg {w : σ → ℤ} {p : MvPolynomial σ A} {d : ℤ}
    (hp : Bounded w p d) : Bounded w (-p) d := by
  intro m hm
  rw [coeff_neg, neg_ne_zero] at hm
  exact hp m hm

/-- Removing the top component lowers an integer weight bound by at least one. -/
theorem bounded_sub_top {w : σ → ℤ} {p : MvPolynomial σ A} {d : ℤ}
    (hp : Bounded w p d) :
    Bounded w (p - weightedHomogeneousComponent w d p) (d - 1) := by
  classical
  intro m hm
  rw [coeff_sub, coeff_weightedHomogeneousComponent] at hm
  by_cases hmd : Finsupp.weight w m = d
  · simp [hmd] at hm
  · simp only [ite_eq_right hmd, sub_zero] at hm
    have hle := hp m hm
    omega

end Ring

end WeightedInitial
end StableCoordinate

end OAI
