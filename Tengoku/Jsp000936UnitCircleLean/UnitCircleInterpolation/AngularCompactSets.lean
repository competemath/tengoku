/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapWidths
import Tengoku.Seed.Order.Fin.Basic
import Tengoku.Seed.Topology.Order.Compact
import Tengoku.Seed.Topology.MetricSpace.Bounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compact subsets of the actual normalized angular simplex

Requiring every literal cyclic gap width to be at least a fixed positive
number gives a closed set inside the open node domain. Its free coordinates
lie in the explicit compact box `[ε, 2π - ε]`. This is purely the geometry of
the actual chart; no properness statement for the height map is asserted.
The empty set and the chart with no free coordinates are both included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- The width of an ordinary gap is the literal successive angle difference.
@isnad1 id=eq.0h3v.s5.955fe0d1c64b from=translated src=- shape=ade4073c vocab=8fb599e7
-/
lemma parameterGapWidth_succ (u : Fin d → ℝ) (i : Fin d) :
    parameterGapWidth i.succ u = angularParameterAngles u i.succ -
      angularParameterAngles u i.castSucc := by
  have hpred : gapLeftNodeIndex (Nat.succ_pos d) i.succ = i.castSucc := by
    apply Fin.ext
    simp [gapLeftNodeIndex, gapPredecessor]
  simp only [parameterGapWidth, Fin.val_succ, Nat.succ_ne_zero, ite_false, hpred]

/-- The final width uses the lifted first angle at `2π`.
@isnad1 id=eq.0h2v.s6.ab2b79d17e01 from=translated src=- shape=c3281da1 vocab=f52ee236
-/
lemma parameterGapWidth_zero (u : Fin d → ℝ) :
    parameterGapWidth (0 : Fin (d + 1)) u =
      2 * Real.pi - angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) := by
  simp [parameterGapWidth, gapLeftNodeIndex]

/-- Every actual cyclic gap is separated by at least `ε`.-/
def shrunkenAngularSimplex (d : ℕ) (ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∀ cut : Fin (d + 1), ε ≤ parameterGapWidth cut u}

/--
@isnad1 id=iff.0h3v.s5.d34cddc41ec9 from=translated src=- shape=76ce6f7f vocab=87437994
-/
lemma mem_shrunkenAngularSimplex (u : Fin d → ℝ) (ε : ℝ) :
    u ∈ shrunkenAngularSimplex d ε ↔ ∀ cut, ε ≤ parameterGapWidth cut u :=
  Iff.rfl

/--
@isnad1 id=isclosed.0h2v.s4.2ef966e98fd6 from=translated src=- shape=663d86fd vocab=5b233260
-/
lemma isClosed_shrunkenAngularSimplex (d : ℕ) (ε : ℝ) :
    IsClosed (shrunkenAngularSimplex d ε) := by
  have heq : shrunkenAngularSimplex d ε =
      ⋂ cut : Fin (d + 1), {u : Fin d → ℝ | ε ≤ parameterGapWidth cut u} := by
    ext u
    simp only [shrunkenAngularSimplex, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun cut => isClosed_le continuous_const (continuous_parameterGapWidth cut))

/-- Positive literal width at every cut forces strictly increasing full angles.
@isnad1 id=strictmo.2h3v.s6.89a01ae5d6ec from=translated src=- shape=ac18bcec vocab=e4b1601f
-/
lemma shrunkenAngularSimplex_strictMono {ε : ℝ} (hε : 0 < ε)
    {u : Fin d → ℝ} (hu : u ∈ shrunkenAngularSimplex d ε) :
    StrictMono (angularParameterAngles u) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hwidth := hu i.succ
  rw [parameterGapWidth_succ] at hwidth
  exact sub_pos.mp (hε.trans_le hwidth)

/--
@isnad1 id=le.1h3v.s6.3c31d9c1959e from=translated src=- shape=c5375de6 vocab=545c9994
-/
lemma shrunkenAngularSimplex_last_le {ε : ℝ} {u : Fin d → ℝ}
    (hu : u ∈ shrunkenAngularSimplex d ε) :
    angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) ≤ 2 * Real.pi - ε := by
  have hlast := hu 0
  rw [parameterGapWidth_zero] at hlast
  linarith

/-- The closed shrunken simplex lies inside the actual open chart.
@isnad1 id=le.1h2v.s4.9f19ae44d3df from=translated src=- shape=44c74513 vocab=e2e2b40f
-/
lemma shrunkenAngularSimplex_subset_domain {ε : ℝ} (hε : 0 < ε) :
    shrunkenAngularSimplex d ε ⊆ angularParameterDomain d := by
  intro u hu
  have hmono := shrunkenAngularSimplex_strictMono hε hu
  refine ⟨hmono, ?_⟩
  intro i
  have hlast := shrunkenAngularSimplex_last_le hu
  have hi : angularParameterAngles u i.succ ≤
      angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) :=
    hmono.monotone (show i.succ ≤ lastNodeIndex (Nat.succ_pos d) from Fin.le_last _)
  change u i < 2 * Real.pi
  change u i ≤ angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) at hi
  linarith

/-- The free coordinates lie in a closed box with a literal `ε` margin at both ends.
@isnad1 id=and.2h4v.s6.9abcf3b0f86f from=translated src=- shape=01fa2602 vocab=63208762
-/
lemma shrunkenAngularSimplex_coordinate_bounds {ε : ℝ} (hε : 0 < ε)
    {u : Fin d → ℝ} (hu : u ∈ shrunkenAngularSimplex d ε) (i : Fin d) :
    ε ≤ u i ∧ u i ≤ 2 * Real.pi - ε := by
  have hmono := shrunkenAngularSimplex_strictMono hε hu
  have hwidth := hu i.succ
  rw [parameterGapWidth_succ, angularParameterAngles_succ] at hwidth
  have hnonneg : 0 ≤ angularParameterAngles u i.castSucc := by
    have h := hmono.monotone (show (0 : Fin (d + 1)) ≤ i.castSucc from Fin.zero_le _)
    simpa only [angularParameterAngles_zero] using h
  have hi : angularParameterAngles u i.succ ≤
      angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) :=
    hmono.monotone (show i.succ ≤ lastNodeIndex (Nat.succ_pos d) from Fin.le_last _)
  exact ⟨by linarith, hi.trans (shrunkenAngularSimplex_last_le hu)⟩

/--
@isnad1 id=le.1h2v.s6.a64a096d14ea from=translated src=- shape=7a0b2a26 vocab=4906a8ed
-/
lemma shrunkenAngularSimplex_subset_box {ε : ℝ} (hε : 0 < ε) :
    shrunkenAngularSimplex d ε ⊆ Set.Icc (fun _ : Fin d => ε) (fun _ => 2 * Real.pi - ε) := by
  intro u hu
  exact ⟨fun i => (shrunkenAngularSimplex_coordinate_bounds hε hu i).1,
    fun i => (shrunkenAngularSimplex_coordinate_bounds hε hu i).2⟩

/-- Uniformly positive literal circular gap widths define a compact actual parameter set.
@isnad1 id=iscompac.1h2v.s5.f7d9299bbedb from=translated src=- shape=d2237b8a vocab=20fed41f
-/
theorem isCompact_shrunkenAngularSimplex {ε : ℝ} (hε : 0 < ε) :
    IsCompact (shrunkenAngularSimplex d ε) :=
  (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : Fin d => ε) (fun _ => 2 * Real.pi - ε))).of_isClosed_subset
    (isClosed_shrunkenAngularSimplex d ε) (shrunkenAngularSimplex_subset_box hε)

/--
@isnad1 id=isbounde.1h2v.s5.2b26f194cff7 from=translated src=- shape=d2237b8a vocab=19111ad2
-/
lemma isBounded_shrunkenAngularSimplex {ε : ℝ} (hε : 0 < ε) :
    Bornology.IsBounded (shrunkenAngularSimplex d ε) :=
  (isCompact_shrunkenAngularSimplex hε).isBounded

/-- Inside the actual chart the shrunken condition is precisely a bound on its actual minimum.
@isnad1 id=iff.1h3v.s6.fd8aa05f7b99 from=translated src=- shape=b2958358 vocab=b479c187
-/
lemma mem_shrunkenAngularSimplex_iff_minimumGapWidth (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (ε : ℝ) :
    u ∈ shrunkenAngularSimplex d ε ↔ ε ≤ minimumGapWidth (cyclicAnglesOfParameters u hu) := by
  constructor
  · intro h
    obtain ⟨cut, heq⟩ := exists_gapWidth_eq_minimum (cyclicAnglesOfParameters u hu)
    rw [← heq, ← parameterGapWidth_of_mem_domain u hu]
    exact h cut
  · intro h cut
    rw [parameterGapWidth_of_mem_domain u hu]
    exact h.trans (minimumGapWidth_le (cyclicAnglesOfParameters u hu) cut)

end

end UnitCircleInterpolation
