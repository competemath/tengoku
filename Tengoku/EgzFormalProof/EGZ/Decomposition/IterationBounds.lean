import Tengoku.EgzFormalProof.EGZ.Decomposition.IterationEvents
import Tengoku.EgzFormalProof.EGZ.Decomposition.NormalizedOperations
import Tengoku.EgzFormalProof.EGZ.Decomposition.Initialization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numerical invariants of finite refinement runs

The state at stage `i` has at most `2^i` nodes, lies within the predetermined
radius horizon, and has lost at most the first `i` explicit mass budgets.
-/

open scoped BigOperators

namespace EGZ.FlagDecomposition.Iteration

open DecompositionParameters

noncomputable def stageScale (d : ℕ) (ε : ℝ) (i : ℕ) : ℝ :=
  scale d (initialScale d ε) (i + 1)

noncomputable def prefixBudget (d : ℕ) (ε : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, lossBudget d ε (initialScale d ε) (j + 1)

/--
@isnad1 id=eq.0h2v.s4.1e2ff2e9a7b9 from=translated src=- shape=c1a5d958 vocab=d3d85d76
-/
@[simp] theorem prefixBudget_zero (d : ℕ) (ε : ℝ) : prefixBudget d ε 0 = 0 := by
  simp [prefixBudget]

/--
@isnad1 id=eq.0h3v.s6.ac97ee816104 from=translated src=- shape=78e162d3 vocab=ddd4ff4f
-/
theorem prefixBudget_succ (d : ℕ) (ε : ℝ) (i : ℕ) :
    prefixBudget d ε (i + 1) = prefixBudget d ε i +
      (ε * stageScale d ε i ^ 2 + (3 : ℝ) ^ (d + 1) * stageScale d ε i) := by
  simp [prefixBudget, Finset.sum_range_succ, lossBudget, stageScale, refinementConstant]

/--
@isnad1 id=le.3h3v.s6.4d2da5166167 from=translated src=- shape=6a5148ab vocab=1635b80c
-/
theorem prefixBudget_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (i : ℕ) : prefixBudget d ε i ≤ ε ^ 2 / 8 := by
  simpa [prefixBudget] using initialScale_sum_tail_le hd hε hεhalf 0 (Finset.range i)

/--
@isnad1 id=lt.1h3v.s4.c8c01e6005d2 from=translated src=- shape=144bfabc vocab=7959d855
-/
theorem stageScale_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    0 < stageScale d ε i := scale_pos d (initialScale_pos d hε) (i + 1)

/--
@isnad1 id=antitone.2h2v.s5.9bf87921da5b from=translated src=- shape=d56dd863 vocab=566cf1e5
-/
theorem stageScale_antitone {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Antitone (stageScale d ε) :=
  fun _ _ h ↦ scale_antitone hd (initialScale_pos d hε).le (Nat.add_le_add_right h 1)

/--
@isnad1 id=and.3h3v.s7.1d4bd3cfd3cf from=translated src=- shape=e3693427 vocab=0dadb92e
-/
theorem stageScale_small {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (i : ℕ) :
    (3 : ℝ) ^ (d + 1) * stageScale d ε i < 1 ∧
      ε * stageScale d ε i ^ 2 < 1 := by
  have hle : stageScale d ε i ≤ initialScale d ε := by
    simpa [stageScale] using scale_antitone hd (initialScale_pos d hε).le (Nat.zero_le (i + 1))
  have hbase := initialScale_bounds d hε hεhalf
  have hδ := (stageScale_pos d hε i).le
  have hδone := hle.trans hbase.2.1
  constructor
  · exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_lt hbase.1
  · have hs : stageScale d ε i ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hε.le]

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    {g : ℕ → ℕ} (P : NormalizedOperationParameters d g) (ε : ℝ)

structure BoundedState (i : ℕ) extends State p d f where
  card_bound : Fintype.card decomposition.flag.Node ≤ 2 ^ i
  radius_bound : radius ≤ P.radiusHorizon 1 i
  mass_loss_bound : (natMass f : ℝ) - decomposition.retainedMass ≤
    prefixBudget d ε i * natMass f

namespace BoundedState

variable {P ε} {i : ℕ} (s : BoundedState (f := f) P ε i)

/--
@isnad1 id=le.0h8v.s6.ac4742edb54b from=translated src=- shape=e92bdbd0 vocab=cb5b7556
-/
theorem mass_le_input : s.decomposition.retainedMass ≤ natMass f :=
  natMass_mono s.decomposition.retained_le

/--
@isnad1 id=and.3h8v.s7.87fed20c64b3 from=translated src=- shape=cae0258a vocab=a8bfc4d0
-/
theorem mass_bounds (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    (natMass f : ℝ) / 2 ≤ s.decomposition.retainedMass ∧
      (1 - ε) * (natMass f : ℝ) ≤ s.decomposition.retainedMass := by
  have hM := Nat.cast_nonneg (α := ℝ) (natMass f)
  have hbudget := mul_le_mul_of_nonneg_right (prefixBudget_le hd hε hεhalf i) hM
  have hhalf : ε ^ 2 / 8 ≤ 1 / 2 := by nlinarith
  have heps : ε ^ 2 / 8 ≤ ε := by nlinarith
  have hhalfM := mul_le_mul_of_nonneg_right hhalf hM
  have hepsM := mul_le_mul_of_nonneg_right heps hM
  constructor <;> nlinarith [s.mass_loss_bound]

noncomputable def initial (hf : f ≠ 0) : BoundedState (f := f) P ε 0 where
  decomposition := FlagDecomposition.initial f hf
  radius := 1
  radius_pos := le_rfl
  minimal := initial_isMinimal f hf
  reduced := initial_isReduced f hf
  bounded := initial_isKBounded f hf _
  card_bound := by rw [initial_card]; norm_num
  radius_bound := le_rfl
  mass_loss_bound := by rw [initial_retainedMass, prefixBudget_zero]; simp

noncomputable def advance {t : State p d f} (hε : 0 < ε)
    (D : Progress s.toState t ε (stageScale d ε i) g)
    (hR : t.radius ≤ P.radiusGrowth s.radius) : BoundedState (f := f) P ε (i + 1) where
  toState := t
  card_bound := D.card_le.trans (by simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 s.card_bound)
  radius_bound := by
    change t.radius ≤ P.radiusGrowth^[i + 1] 1
    rw [Function.iterate_succ_apply']
    exact hR.trans (P.radiusGrowth_growing.1 s.radius_bound)
  mass_loss_bound := by
    rw [prefixBudget_succ]
    have hcoef : 0 ≤ ε * stageScale d ε i ^ 2 + (3 : ℝ) ^ (d + 1) * stageScale d ε i := by
      have := (stageScale_pos d hε i).le
      positivity
    have hM : (s.decomposition.retainedMass : ℝ) ≤ natMass f := by exact_mod_cast s.mass_le_input
    have hs := mul_le_mul_of_nonneg_left hM hcoef
    have hl := D.mass_loss_le
    change (s.decomposition.retainedMass : ℝ) - t.decomposition.retainedMass ≤ _ at hl
    nlinarith [s.mass_loss_bound]

noncomputable def keep (hε : 0 < ε) : BoundedState (f := f) P ε (i + 1) where
  toState := s.toState
  card_bound := s.card_bound.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ i))
  radius_bound := s.radius_bound.trans (P.radiusHorizon_monotone 1 (Nat.le_succ i))
  mass_loss_bound := by
    rw [prefixBudget_succ]
    have hcoef : 0 ≤ ε * stageScale d ε i ^ 2 + (3 : ℝ) ^ (d + 1) * stageScale d ε i := by
      have := (stageScale_pos d hε i).le
      positivity
    have hM := Nat.cast_nonneg (α := ℝ) (natMass f)
    nlinarith [s.mass_loss_bound, mul_nonneg hcoef hM]

end BoundedState
end EGZ.FlagDecomposition.Iteration
