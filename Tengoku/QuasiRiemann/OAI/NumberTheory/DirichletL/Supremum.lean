import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

namespace SevenEighths.Supremum

noncomputable section

def continuationMargin (β ω σ : ℝ) : ℝ := min (β - 7 / 8 - ω) σ

/--
@isnad1 id=lt.2h3v.s6.8a82f3ebaaa1 from=translated src=- shape=80d802ad vocab=8c39f9af
-/
theorem continuationMargin_pos {β ω σ : ℝ}
    (hω : ω < β - 7 / 8) (hσ : 0 < σ) :
    0 < continuationMargin β ω σ := by
  exact lt_min (sub_pos.mpr hω) hσ

/--
@isnad1 id=le.0h3v.s5.3f3e5d34a922 from=translated src=- shape=5856737c vocab=044fc089
-/
theorem continuationMargin_le_gap (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ β - 7 / 8 - ω :=
  min_le_left _ _

/--
@isnad1 id=le.0h3v.s3.718596e8e1f1 from=translated src=- shape=a80dfe9e vocab=d3f55d71
-/
theorem continuationMargin_le_sigma (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ σ :=
  min_le_right _ _

/--
@isnad1 id=lt.1h3v.s5.4807958c2531 from=translated src=- shape=9bd9a76b vocab=8c39f9af
-/
theorem continuation_boundary_gt {β ω σ : ℝ} (hω : 0 < ω) :
    7 / 8 < β - continuationMargin β ω σ := by
  have h := continuationMargin_le_gap β ω σ
  linarith

/--
@isnad1 id=eq.0h4v.s6.e0f0facdce17 from=translated src=- shape=31241778 vocab=f31c29d7
-/
theorem max_signal_exponents (β ω σ c : ℝ) :
    max (7 / 8 + c + ω) (β + c - σ) =
      β + c - continuationMargin β ω σ := by
  unfold continuationMargin
  rcases le_total (β - 7 / 8 - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith)]

/--
@isnad1 id=eq.0h3v.s7.bb73cd4cbda1 from=translated src=- shape=fe20d2c8 vocab=f31c29d7
-/
theorem max_normalized_signal_exponents (β ω σ : ℝ) :
    max (3 / 16 + ω) (β - 11 / 16 - σ) =
      β - 11 / 16 - continuationMargin β ω σ := by
  have h : (7 / 8 : ℝ) + -(11 / 16) = 3 / 16 := by norm_num
  simpa only [sub_eq_add_neg, h] using max_signal_exponents β ω σ (-(11 / 16))

/--
@isnad1 id=ex.3h2v.s5.768a890fc2f8 from=translated src=- shape=4dd10d98 vocab=c5225610
-/
theorem exists_gt_supremum_sub {S : Set ℝ} (hne : S.Nonempty)
    (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  apply (lt_csSup_iff hbounded hne).mp
  linarith

/--
@isnad1 id=false.4h2v.s5.00959cdd06ab from=translated src=- shape=de85f4d5 vocab=1ca60b42
-/
theorem uniform_bound_below_supremum_false {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ x ∈ S, x ≤ sSup S - ε) : False := by
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub hne hbounded hε
  exact (not_lt_of_ge (hbound x hx)) hlt

/--
@isnad1 id=ex.3h3v.s6.e9b070d062d4 from=translated src=- shape=4e08711e vocab=273bdd8a
-/
theorem exists_gt_supremum_sub_of_insert {S : Set ℝ} {a ε : ℝ}
    (hbounded : BddAbove (insert a S)) (hε : 0 < ε)
    (ha : a ≤ sSup (insert a S) - ε) :
    ∃ x ∈ S, sSup (insert a S) - ε < x := by
  obtain ⟨x, hx, hlt⟩ :=
    exists_gt_supremum_sub (Set.insert_nonempty a S) hbounded hε
  rcases Set.mem_insert_iff.mp hx with hxa | hxS
  · subst x
    exact False.elim ((not_lt_of_ge ha) hlt)
  · exact ⟨x, hxS, hlt⟩

/--
@isnad1 id=le.3h1v.s7.fec23270a53c from=translated src=- shape=d06e04a2 vocab=409558d7
-/
theorem seven_eighths_of_uniform_margin {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S)
    (hbound : 7 / 8 < sSup S →
      ∃ ω σ : ℝ, ω < sSup S - 7 / 8 ∧ 0 < σ ∧
        ∀ x ∈ S, x ≤ sSup S - continuationMargin (sSup S) ω σ) :
    sSup S ≤ 7 / 8 := by
  by_contra h
  obtain ⟨ω, σ, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  exact uniform_bound_below_supremum_false hne hbounded
    (continuationMargin_pos hω hσ) hbound

/--
@isnad1 id=le.2h1v.s8.42bf90272c82 from=translated src=- shape=94684503 vocab=0f9e8e42
-/
theorem seven_eighths_of_uniform_margin_with_sentinel {S : Set ℝ}
    (hbounded : BddAbove (insert (1 / 2 : ℝ) S))
    (hbound : 7 / 8 < sSup (insert (1 / 2 : ℝ) S) →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < sSup (insert (1 / 2 : ℝ) S) - 7 / 8 ∧
        0 < σ ∧ ∀ x ∈ S, x ≤ sSup (insert (1 / 2 : ℝ) S) -
          continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ) :
    sSup (insert (1 / 2 : ℝ) S) ≤ 7 / 8 := by
  by_contra h
  obtain ⟨ω, σ, hω0, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  have hε := continuationMargin_pos hω hσ
  have hboundary := continuation_boundary_gt (β := sSup (insert (1 / 2 : ℝ) S))
    (σ := σ) hω0
  have hsentinel : (1 / 2 : ℝ) ≤ sSup (insert (1 / 2 : ℝ) S) -
      continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ := by
    linarith
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub_of_insert hbounded hε hsentinel
  exact (not_lt_of_ge (hbound x hx)) hlt

end

end SevenEighths.Supremum

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
