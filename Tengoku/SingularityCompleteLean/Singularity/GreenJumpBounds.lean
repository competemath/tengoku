import Tengoku.SingularityCompleteLean.Singularity.JumpDistance
import Tengoku.SingularityCompleteLean.Singularity.GreenHarnack
import Tengoku.SingularityCompleteLean.Singularity.KilledGreenDecay

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exponential Green bounds in the minimum jump distance

A shortest permitted word gives the lower bound. No transition can arrive
before the minimum length, so the spectral geometric tail gives the upper
bound. This is valid for nonsymmetric finite laws and needs no geometric
compactness or Martin-boundary identification.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- No positive-length contribution exists below the shortest possible path length.
@isnad1 id=eq.2h6v.s6.c4708b938c14 from=translated src=- shape=a4e18833 vocab=f8976ff3
-/
theorem transitionWeight_zero_of_lt_jumpDistance (s : Finset Γ) (μ : Γ → ℝ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) (n : ℕ)
    (hn : n < jumpDistance s hgen x y) : transitionWeight s μ n x y = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  apply ite_eq_right
  intro hw
  exact (Nat.not_le_of_gt hn) (jumpDistance_le_length s hgen n w x y hw)

omit [Group Γ] in
/-- A positive finite probability support has a common positive lower bound smaller than one.
@isnad1 id=ex.2h3v.s6.3f4f8db7d42d from=translated src=- shape=66c6275e vocab=773b9a97
-/
theorem exists_positive_jumpWeight_lower (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ g ∈ s, p ≤ μ g := by
  have hne : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hs
    simp [hs] at hmass
  obtain ⟨g, hg, hmin⟩ := s.exists_min_image μ hne
  refine ⟨min 1 (μ g) / 2, div_pos (lt_min zero_lt_one (hpos g hg)) (by norm_num), ?_, ?_⟩
  · have h := min_le_left (1 : ℝ) (μ g)
    linarith
  · intro a ha
    have h := min_le_right (1 : ℝ) (μ g)
    have hp := hpos g hg
    have hh := hmin a ha
    linarith

omit [Group Γ] in
/-- A lower bound for each jump probability gives the corresponding product lower bound.
@isnad1 id=le.2h6v.s6.1c67f90192e6 from=translated src=- shape=cf679359 vocab=cfa761aa
-/
theorem walkWeight_ge_pow (s : Finset Γ) (μ : Γ → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hμ : ∀ g ∈ s, p ≤ μ g) (n : ℕ) (w : WalkWord s n) : p ^ n ≤ walkWeight s μ n w := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    change p ^ (n + 1) ≤ μ w.1 * walkWeight s μ n w.2
    rw [pow_succ']
    exact mul_le_mul (hμ w.1 w.1.property) (ih w.2) (pow_nonneg hp n)
      (hp.trans (hμ w.1 w.1.property))

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]

end Singularity
