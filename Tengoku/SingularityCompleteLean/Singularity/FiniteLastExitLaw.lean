import Tengoku.SingularityCompleteLean.Singularity.WalkLastExit
import Tengoku.SingularityCompleteLean.Singularity.MartinCompactness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite last-exit law and its exact Martin density

Almost-sure escape makes the last-exit events a partition for a finite set
containing the starting point. This constructs a probability mass function.
Changing the starting vertex multiplies its masses by the actual finite
Martin quotient, without dividing by the possibly zero escape probability.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical
namespace Singularity

/-- A sequence starting in A and eventually avoiding A has a last visit.
@isnad1 id=ex.2h3v.s6.fefb04a064fb from=translated src=- shape=8f7512c5 vocab=4f26754d
-/
theorem exists_last_visit_of_eventually_avoid {X : Type*} (f : ℕ → X) (A : Set X)
    (hzero : f 0 ∈ A) (havoid : ∀ᶠ n in atTop, f n ∉ A) :
    ∃ n, f n ∈ A ∧ ∀ k, n < k → f k ∉ A := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 havoid
  have hex : ∃ n, ∀ k, n < k → f k ∉ A := ⟨N, fun k hk => hN k hk.le⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_contra hn
  cases he : Nat.find hex with
  | zero => exact hn (he ▸ hzero)
  | succ m =>
    have hp : ∀ k, m < k → f k ∉ A := by
      intro k hk
      by_cases hkm : k = m + 1
      · subst k
        simpa only [he] using hn
      · exact Nat.find_spec hex k (by omega)
    exact (Nat.find_min hex (show m < Nat.find hex by omega)) hp

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ] [Countable Γ]

/-- Almost every path starting in a finite A has a last exit at a vertex of A.
@isnad1 id=eventual.4h5v.s12.d110e496186d from=translated src=- shape=09ebaae7 vocab=65ac6bea
-/
theorem walkLastExitEver_ae_cover (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x : Γ) (hx : x ∈ A) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, ω ∈ ⋃ a : A, walkLastExitEver s (A : Set Γ) x a := by
  filter_upwards [walkPosition_ae_escape_finite s μ hμ hmass hgap x] with ω hω
  obtain ⟨n, hn, ht⟩ := exists_last_visit_of_eventually_avoid (fun n => walkPosition s x n ω)
    (A : Set Γ) hx (hω A)
  exact mem_iUnion.mpr ⟨⟨walkPosition s x n ω, hn⟩, mem_iUnion.mpr ⟨n, rfl, hn, ht⟩⟩

/-- The last-exit masses sum to one for every finite set containing the start.
@isnad1 id=eq.4h5v.s12.0c5e1a1c1d3e from=translated src=- shape=2f58adea vocab=811655bb
-/
theorem finiteLastExit_mass (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x : Γ) (hx : x ∈ A) :
    (∑ a : A, infiniteWalkLaw s μ hμ hmass (walkLastExitEver s (A : Set Γ) x a)) = 1 := by
  have hm (a : A) := measurableSet_walkLastExitEver s (A : Set Γ) A.measurableSet x a
  have hd : Pairwise (fun a b : A => Disjoint (walkLastExitEver s (A : Set Γ) x a)
      (walkLastExitEver s (A : Set Γ) x b)) := by
    intro a b hab
    exact walkLastExitEver_disjoint s (A : Set Γ) x (fun he => hab (Subtype.ext he))
  have hp := (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hm)).mp
    (walkLastExitEver_ae_cover s μ hμ hmass hgap A x hx)
  rw [measure_iUnion hd hm, tsum_fintype] at hp
  exact hp

/-- The actual finite last-exit distribution as a probability mass function.-/
def finiteLastExitLaw (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x : Γ) (hx : x ∈ A) : PMF A :=
  PMF.ofFintype (fun a => infiniteWalkLaw s μ hμ hmass (walkLastExitEver s (A : Set Γ) x a))
    (finiteLastExit_mass s μ hμ hmass hgap A x hx)

end Singularity
