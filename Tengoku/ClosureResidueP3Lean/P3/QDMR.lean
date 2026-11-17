import Tengoku.ClosureResidueP3Lean.P3.SaturatedStabilizer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace P3

section QDMR

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## I1: stabilized finite core -/

/-- The stabilized residue space: the join of all finite-depth residue spaces.
Because the filtration is finite-dimensional and monotone, this join is
attained at a finite depth.-/
def stableResidue
    (φ : Dynamics V) :
    Submodule ℂ (DiagZero (V := V)) :=
  ⨆ k : ℕ, residue φ k

/-- The stabilized hidden-flow space.-/
def stableHiddenFlow
    (φ : Dynamics V) :
    Submodule ℂ (EdgeSpace V) :=
  ⨆ k : ℕ, hiddenFlow φ k

theorem residue_le_stableResidue
    (φ : Dynamics V) (k : ℕ) :
    residue φ k ≤ stableResidue (V := V) φ := by
  exact le_iSup (fun n : ℕ => residue φ n) k

theorem hiddenFlow_le_stableHiddenFlow
    (φ : Dynamics V) (k : ℕ) :
    hiddenFlow φ k ≤ stableHiddenFlow (V := V) φ := by
  exact le_iSup (fun n : ℕ => hiddenFlow φ n) k

/-- If the residue filtration is constant from `s` onward, then the stable
join is exactly the finite space `R_s`.-/
theorem stableResidue_eq_of_eventually_constant
    (φ : Dynamics V) (s : ℕ)
    (hs : ∀ k : ℕ, s ≤ k → residue φ k = residue φ s) :
    stableResidue (V := V) φ = residue φ s := by
  apply le_antisymm
  · apply iSup_le
    intro k
    rcases le_total k s with hks | hsk
    · exact residue_mono φ hks
    · rw [hs k hsk]
  · exact residue_le_stableResidue (V := V) φ s

/-- The analogous finite-attainment statement for the hidden-flow join.-/
theorem stableHiddenFlow_eq_of_eventually_constant
    (φ : Dynamics V) (s : ℕ)
    (hs : ∀ k : ℕ, s ≤ k → hiddenFlow φ k = hiddenFlow φ s) :
    stableHiddenFlow (V := V) φ = hiddenFlow φ s := by
  apply le_antisymm
  · apply iSup_le
    intro k
    rcases le_total k s with hks | hsk
    · exact hiddenFlow_mono φ hks
    · rw [hs k hsk]
  · exact hiddenFlow_le_stableHiddenFlow (V := V) φ s

/-- A chosen common stabilization depth for the finite P3 core.-/
noncomputable def coreStabilizationDepth
    (φ : Dynamics V) : ℕ :=
  Classical.choose (finite_core_eventually_constant (V := V) φ)

/-- The chosen depth really stabilizes hidden defects, hidden flows and
residues simultaneously.-/
theorem coreStabilizationDepth_spec
    (φ : Dynamics V) :
    ∀ k : ℕ, coreStabilizationDepth (V := V) φ ≤ k →
      hidden φ k =
          hidden φ (coreStabilizationDepth (V := V) φ) ∧
      hiddenFlow φ k =
          hiddenFlow φ (coreStabilizationDepth (V := V) φ) ∧
      residue φ k =
          residue φ (coreStabilizationDepth (V := V) φ) := by
  exact Classical.choose_spec
    (finite_core_eventually_constant (V := V) φ)

/-- The infinite-looking residue join is attained at the chosen finite
stabilization depth.-/
theorem stableResidue_eq_core
    (φ : Dynamics V) :
    stableResidue (V := V) φ =
      residue φ (coreStabilizationDepth (V := V) φ) := by
  apply stableResidue_eq_of_eventually_constant
  intro k hk
  exact (coreStabilizationDepth_spec (V := V) φ k hk).2.2

/-- The infinite-looking hidden-flow join is likewise attained at that same
finite depth.-/
theorem stableHiddenFlow_eq_core
    (φ : Dynamics V) :
    stableHiddenFlow (V := V) φ =
      hiddenFlow φ (coreStabilizationDepth (V := V) φ) := by
  apply stableHiddenFlow_eq_of_eventually_constant
  intro k hk
  exact (coreStabilizationDepth_spec (V := V) φ k hk).2.1

/-! ## I2: stable support and saturation -/

/-- The finite support graph at a common stabilization depth.  By the
previous theorem it represents the support of the stabilized hidden-flow
space without introducing any infinite-dimensional graph object.-/
def stableSupportGraph
    (φ : Dynamics V) : SimpleGraph V :=
  supportGraph (V := V) φ (coreStabilizationDepth (V := V) φ)

/-- Coordinate image of the stabilized residue space.-/
def stableResidueCoordinateSpace
    (φ : Dynamics V) :
    Submodule ℂ (GraphVertexSpace V) :=
  (stableResidue (V := V) φ).map
    (diagZeroCoordinates (V := V))

/-- Graph saturation at the stabilized finite core.  This is the only
saturation hypothesis used by the QDMR connectivity theorem.-/
def graphSaturatedAtInfinity
    (φ : Dynamics V) : Prop :=
  stableResidueCoordinateSpace (V := V) φ =
    incidenceSpace (V := V) (stableSupportGraph (V := V) φ)

/-- Stable saturation is exactly ordinary graph saturation at the chosen
common stabilization depth.-/
theorem graphSaturatedAtInfinity_iff_core
    (φ : Dynamics V) :
    graphSaturatedAtInfinity (V := V) φ ↔
      graphSaturated (V := V) φ
        (coreStabilizationDepth (V := V) φ) := by
  unfold graphSaturatedAtInfinity stableResidueCoordinateSpace
    stableSupportGraph graphSaturated residueCoordinateSpace
  rw [stableResidue_eq_core (V := V) φ]

/-! ## I3: QDMR -/

/-- Quadratic Diagonal Memory Rank: the complex dimension of the stabilized
quadratic residue sector.-/
def QDMR
    (φ : Dynamics V) : ℕ :=
  Module.finrank ℂ ↥(stableResidue (V := V) φ)

theorem QDMR_eq_core_residue_finrank
    (φ : Dynamics V) :
    QDMR (V := V) φ =
      Module.finrank ℂ
        ↥(residue φ (coreStabilizationDepth (V := V) φ)) := by
  unfold QDMR
  rw [stableResidue_eq_core (V := V) φ]

/-- Final stabilized Incidence Rank correspondence:
if the stabilized residue fills the incidence space of the stabilized hidden
support graph, then QDMR is the vertex count minus the number of connected
components.-/
theorem QDMR_eq_card_sub_components
    (φ : Dynamics V)
    (hsat : graphSaturatedAtInfinity (V := V) φ) :
    QDMR (V := V) φ =
      Fintype.card V -
        componentCount (V := V) (stableSupportGraph (V := V) φ) := by
  rw [QDMR_eq_core_residue_finrank (V := V) φ]
  unfold stableSupportGraph
  exact residue_finrank_of_graphSaturated
    (V := V) φ (coreStabilizationDepth (V := V) φ)
    ((graphSaturatedAtInfinity_iff_core (V := V) φ).mp hsat)

/-! ## I4: primitive-defect realization of QDMR -/

/-- The stabilized span generated directly from primitive defect pairs.
At finite depth `k`, `primitiveResidueSpan φ k` is generated by
`quadraticReturn (primitiveDefect φ m d) (primitiveDefect φ n e)`
with total depth `m+n ≤ k`.-/
def stablePrimitiveResidueSpan
    (φ : Dynamics V) :
    Submodule ℂ (DiagZero (V := V)) :=
  ⨆ k : ℕ, primitiveResidueSpan (V := V) φ k

/-- The stabilized residue sector is exactly the stabilized primitive-defect
quadratic-return span.  This is the stable form of D4
`residue_eq_span_primitive`.-/
theorem stableResidue_eq_stablePrimitiveResidueSpan
    (φ : Dynamics V) :
    stableResidue (V := V) φ =
      stablePrimitiveResidueSpan (V := V) φ := by
  apply le_antisymm
  · apply iSup_le
    intro k
    rw [residue_eq_span_primitive (V := V) φ k]
    exact le_iSup
      (fun n : ℕ => primitiveResidueSpan (V := V) φ n) k
  · apply iSup_le
    intro k
    rw [← residue_eq_span_primitive (V := V) φ k]
    exact le_iSup
      (fun n : ℕ => residue φ n) k

/-- The primitive-defect stable span is also attained at the same finite
core stabilization depth.-/
theorem stablePrimitiveResidueSpan_eq_core
    (φ : Dynamics V) :
    stablePrimitiveResidueSpan (V := V) φ =
      primitiveResidueSpan (V := V) φ
        (coreStabilizationDepth (V := V) φ) := by
  rw [← stableResidue_eq_stablePrimitiveResidueSpan (V := V) φ,
      stableResidue_eq_core (V := V) φ,
      residue_eq_span_primitive (V := V) φ
        (coreStabilizationDepth (V := V) φ)]

/-- QDMR is equivalently the dimension of the stabilized span of quadratic
returns of primitive defects `z_m(d)=Q Φ^m(d)`.-/
theorem QDMR_eq_stablePrimitiveResidue_finrank
    (φ : Dynamics V) :
    QDMR (V := V) φ =
      Module.finrank ℂ
        ↥(stablePrimitiveResidueSpan (V := V) φ) := by
  unfold QDMR
  rw [stableResidue_eq_stablePrimitiveResidueSpan (V := V) φ]

/-- Fully primitive finite-core form of QDMR.-/
theorem QDMR_eq_core_primitiveResidue_finrank
    (φ : Dynamics V) :
    QDMR (V := V) φ =
      Module.finrank ℂ
        ↥(primitiveResidueSpan (V := V) φ
          (coreStabilizationDepth (V := V) φ)) := by
  rw [QDMR_eq_stablePrimitiveResidue_finrank (V := V) φ,
      stablePrimitiveResidueSpan_eq_core (V := V) φ]

end QDMR

end P3
