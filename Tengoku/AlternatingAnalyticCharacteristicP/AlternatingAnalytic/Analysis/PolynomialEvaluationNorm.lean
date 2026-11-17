import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteFieldNorm
import Tengoku.Seed.Algebra.Polynomial.Degree.TrailingDegree
import Tengoku.Seed.Algebra.Polynomial.Eval.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norms of polynomials evaluated at a small element

If `K` is ultrametric, `κ` is a finite field mapped into `K`, and `0 < ‖t‖ < 1`, then
`‖p(t)‖ = ‖t‖^(trailing degree of p)` for every nonzero `p ∈ κ[X]`. In particular `t` is
transcendental over `κ`. This is used for the Laurent subfield of Lemma D.2.
-/

open scoped BigOperators

namespace AlternatingAnalytic

open IsUltrametricDist

/-- In an ultrametric group a uniquely largest summand determines the norm.-/
theorem norm_sum_eq_of_strictly_largest {V ι : Type*} [NormedAddCommGroup V]
    [IsUltrametricDist V] (s : Finset ι) (f : ι → V) (i : ι) (hi : i ∈ s)
    (hpos : 0 < ‖f i‖) (hmax : ∀ j ∈ s, j ≠ i → ‖f j‖ < ‖f i‖) :
    ‖∑ j ∈ s, f j‖ = ‖f i‖ := by
  classical
  have hrest : ‖∑ j ∈ s.erase i, f j‖ < ‖f i‖ := by
    rcases (s.erase i).eq_empty_or_nonempty with h | h
    · simpa [h] using hpos
    · obtain ⟨j, hj, hjnorm⟩ := exists_norm_finsetSum_le_of_nonempty h f
      exact hjnorm.trans_lt (hmax j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1)
  rw [← Finset.add_sum_erase _ _ hi, norm_add_eq_max_of_norm_ne_norm hrest.ne']
  exact max_eq_left hrest.le

variable {κ K : Type*} [Field κ] [Finite κ] [NormedField K] [IsUltrametricDist K]

/-- `‖p(t)‖ = ‖t‖ ^ natTrailingDegree p` for nonzero `p`.-/
theorem norm_polynomial_eval₂ (f : κ →+* K) (t : K) (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1)
    (p : Polynomial κ) (hp : p ≠ 0) :
    ‖p.eval₂ f t‖ = ‖t‖ ^ p.natTrailingDegree := by
  classical
  have hterm (n : ℕ) (hn : n ∈ p.support) :
      ‖f (p.coeff n) * t ^ n‖ = ‖t‖ ^ n := by
    rw [norm_mul, norm_finiteField_map f _ (Polynomial.mem_support_iff.mp hn),
      one_mul, norm_pow]
  have hm := p.natTrailingDegree_mem_support_of_nonzero hp
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [norm_sum_eq_of_strictly_largest p.support (fun n => f (p.coeff n) * t ^ n)
    p.natTrailingDegree hm]
  · exact hterm _ hm
  · rw [hterm _ hm]
    exact pow_pos (norm_pos_iff.mpr ht0) _
  · intro n hn hne
    rw [hterm _ hn, hterm _ hm]
    exact (pow_lt_pow_iff_right_of_lt_one₀ (norm_pos_iff.mpr ht0) ht1).2
      (lt_of_le_of_ne (p.natTrailingDegree_le_of_mem_supp n hn) hne.symm)

/-- Evaluation at `t` is injective on `κ[X]`.-/
theorem polynomial_eval₂_injective (f : κ →+* K) (t : K)
    (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1) :
    Function.Injective (Polynomial.eval₂RingHom f t) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro p hp
  by_contra hne
  have h := norm_polynomial_eval₂ f t ht0 ht1 p hne
  have hz : p.eval₂ f t = 0 := hp
  rw [hz, norm_zero] at h
  exact (pow_pos (norm_pos_iff.mpr ht0) p.natTrailingDegree).ne' h.symm

end AlternatingAnalytic
