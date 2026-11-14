import Tengoku.Twinprime.TwinPrime.Analytic.AdditiveKernel
import Tengoku.Twinprime.TwinPrime.Analytic.SelbergCoefficientBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reciprocal sums over separated real points

Ordering a finite separated set controls its reciprocal mass by a harmonic
sum. This is the counting step for bounding additive Gram rows.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The j-th positive point is at least `(j+1)δ` when the first point and
every successive gap are at least δ.
@isnad1 id=le.2h3v.s7.0cfc7e2d472a from=translated src=- shape=ab6d30a6 vocab=74153dad
-/
theorem orderEmbOfFin_ge_mul_of_separated (s : Finset ℝ) (δ : ℝ)
    (hbase : ∀ x ∈ s, δ ≤ x)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x < y → δ ≤ y - x) :
    ∀ j : Fin s.card, ((j.val : ℝ) + 1) * δ ≤ s.orderEmbOfFin rfl j := by
  have h : ∀ n : ℕ, ∀ hn : n < s.card,
      ((n : ℝ) + 1) * δ ≤ s.orderEmbOfFin rfl ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa only [Nat.cast_zero, zero_add, one_mul] using
          hbase _ (s.orderEmbOfFin_mem rfl ⟨0, hn⟩)
    | succ n ih =>
        intro hn
        have hn' : n < s.card := by omega
        have hprev := ih hn'
        have hgap := hsep _ (s.orderEmbOfFin_mem rfl ⟨n, hn'⟩)
          _ (s.orderEmbOfFin_mem rfl ⟨n + 1, hn⟩)
          ((s.orderEmbOfFin rfl).strictMono (by exact Nat.lt_succ_self n))
        push_cast
        nlinarith
  intro j
  exact h j.val j.isLt

/-- Reciprocal mass of finitely many positive separated points.
@isnad1 id=le.3h2v.s7.b64e970460b2 from=translated src=- shape=d005e34e vocab=df18a882
-/
theorem sum_reciprocal_le_harmonic_of_separated (s : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hbase : ∀ x ∈ s, δ ≤ x)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x < y → δ ≤ y - x) :
    (∑ x ∈ s, 1 / x) ≤ (harmonic s.card : ℝ) / δ := by
  have hsum : (∑ x ∈ s, 1 / x) =
      ∑ j : Fin s.card, 1 / s.orderEmbOfFin rfl j := by
    conv_lhs => rw [← s.map_orderEmbOfFin_univ rfl]
    rw [sum_map]
    rfl
  rw [hsum]
  calc
    _ ≤ ∑ j : Fin s.card, 1 / (((j.val : ℝ) + 1) * δ) := by
      apply sum_le_sum
      intro j _
      exact one_div_le_one_div_of_le (by positivity)
        (orderEmbOfFin_ge_mul_of_separated s δ hbase hsep j)
    _ = _ := by
      rw [show (∑ j : Fin s.card, 1 / (((j.val : ℝ) + 1) * δ)) =
        ∑ j ∈ range s.card, 1 / (((j : ℝ) + 1) * δ) from
          Fin.sum_univ_eq_sum_range (fun j => 1 / (((j : ℝ) + 1) * δ)) s.card]
      simp only [div_mul_eq_div_div, ← sum_div]
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one, div_eq_mul_inv, one_mul]

/--
@isnad1 id=monotone.0h0v.s3.9a19cc72471f from=translated src=- shape=f0959ba1 vocab=ad7c2cf9
-/
theorem harmonic_real_mono : Monotone (fun n : ℕ => (harmonic n : ℝ)) := by
  intro m n hmn
  change (harmonic m : ℝ) ≤ harmonic n
  rw [← sum_one_div_Ioc_eq_harmonic, ← sum_one_div_Ioc_eq_harmonic]
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, (mem_Ioc.mp hk).2.trans hmn⟩
  · intro k _ _
    positivity

/-- Split a separated set on the real line into its positive and negative
parts. Each part contributes at most one harmonic reciprocal sum.
@isnad1 id=le.3h2v.s7.c2005f341d3e from=translated src=- shape=24760f1f vocab=ad0ece8d
-/
theorem sum_reciprocal_abs_le_of_separated (s : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hbase : ∀ x ∈ s, δ ≤ |x|)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ s, 1 / |x|) ≤ 2 * (harmonic s.card : ℝ) / δ := by
  classical
  let sp := s.filter (fun x => 0 < x)
  let sn := s.filter (fun x => ¬0 < x)
  have hp : (∑ x ∈ sp, 1 / |x|) ≤ (harmonic s.card : ℝ) / δ := by
    have hb : ∀ x ∈ sp, δ ≤ x := by
      intro x hx
      simpa only [abs_of_pos (mem_filter.mp hx).2] using hbase x (mem_filter.mp hx).1
    have hs : ∀ x ∈ sp, ∀ y ∈ sp, x < y → δ ≤ y - x := by
      intro x hx y hy hxy
      have h := hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy.ne
      simpa only [abs_of_neg (sub_neg.mpr hxy), neg_sub] using h
    calc
      _ = ∑ x ∈ sp, 1 / x := sum_congr rfl fun x hx => by
        rw [abs_of_pos (mem_filter.mp hx).2]
      _ ≤ (harmonic sp.card : ℝ) / δ := sum_reciprocal_le_harmonic_of_separated sp δ hδ hb hs
      _ ≤ _ := div_le_div_of_nonneg_right (harmonic_real_mono (card_filter_le _ _)) hδ.le
  have hn : (∑ x ∈ sn, 1 / |x|) ≤ (harmonic s.card : ℝ) / δ := by
    let t := sn.image (fun x => -x)
    have hb : ∀ x ∈ t, δ ≤ x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      simpa only [abs_of_nonpos (le_of_not_gt (mem_filter.mp hy).2)] using
        hbase y (mem_filter.mp hy).1
    have hs : ∀ x ∈ t, ∀ y ∈ t, x < y → δ ≤ y - x := by
      intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
      have huv : v < u := by linarith
      have h := hsep u (mem_filter.mp hu).1 v (mem_filter.mp hv).1 huv.ne'
      rw [abs_of_pos (sub_pos.mpr huv)] at h
      linarith
    calc
      _ = ∑ x ∈ t, 1 / x := by
        rw [sum_image (by intro x _ y _ hxy; exact neg_injective hxy)]
        apply sum_congr rfl
        intro x hx
        rw [abs_of_nonpos (le_of_not_gt (mem_filter.mp hx).2)]
      _ ≤ (harmonic t.card : ℝ) / δ := sum_reciprocal_le_harmonic_of_separated t δ hδ hb hs
      _ ≤ _ := div_le_div_of_nonneg_right
        (harmonic_real_mono ((card_image_le).trans (card_filter_le _ _))) hδ.le
  have hsplit : (∑ x ∈ sp, 1 / |x|) + (∑ x ∈ sn, 1 / |x|) = ∑ x ∈ s, 1 / |x| :=
    sum_filter_add_sum_filter_not s (fun x => 0 < x) (fun x => 1 / |x|)
  calc
    _ = (∑ x ∈ sp, 1 / |x|) + (∑ x ∈ sn, 1 / |x|) := hsplit.symm
    _ ≤ (harmonic s.card : ℝ) / δ + (harmonic s.card : ℝ) / δ := add_le_add hp hn
    _ = _ := by ring

end TwinPrime.Analytic
