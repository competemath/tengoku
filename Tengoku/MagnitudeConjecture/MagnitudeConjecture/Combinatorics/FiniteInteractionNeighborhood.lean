import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.FiniteWindowOrbitQuotient
import Tengoku.Seed.Algebra.Group.Action.Pointwise.Set.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite interaction neighborhoods

The covering argument enlarges a finite seed window three times by adjoining
all objects having a nonzero Hom in either direction with an object already
present.  This file isolates the relation-theoretic content of that
construction.  Locally finite interaction neighborhoods remain finite under
iteration, and an invariant interaction relation makes every iterated window
equivariant under the deck-group action.  The resulting three-step window can
therefore be passed directly to finite residual quotient separation.
-/

set_option autoImplicit false

open scoped Pointwise

namespace MagnitudeConjecture.CoveringSeparation

universe u v w

variable {X : Type v}

/-- Enlarge a set by taking every point interacting with one of its points.-/
def interactionNeighborhood (R : X → X → Prop) (W : Set X) : Set X :=
  {y | ∃ x ∈ W, R x y}

/--
@isnad1 id=iff.0h4v.s5.8015958616ce from=translated src=- shape=e3e77be7 vocab=df54620c
-/
@[simp]
theorem mem_interactionNeighborhood_iff
    (R : X → X → Prop) (W : Set X) (y : X) :
    y ∈ interactionNeighborhood R W ↔ ∃ x ∈ W, R x y :=
  Iff.rfl

/-- A reflexive interaction relation makes each window lie in its first
enlargement.
@isnad1 id=le.0h4v.s4.cd7116b19edd from=translated src=- shape=e7014483 vocab=3a50b246
-/
theorem subset_interactionNeighborhood
    (R : X → X → Prop) (reflexive : ∀ x : X, R x x) (W : Set X) :
    W ⊆ interactionNeighborhood R W := by
  intro x hx
  exact ⟨x, hx, reflexive x⟩

/-- Interaction-neighborhood enlargement is monotone in the seed set.
@isnad1 id=monotone.0h2v.s5.5d91f2c61170 from=translated src=- shape=dc84b615 vocab=bcacf6fd
-/
theorem interactionNeighborhood_mono
    (R : X → X → Prop) :
    Monotone (interactionNeighborhood R) := by
  intro U W hUW y
  rintro ⟨x, hx, hxy⟩
  exact ⟨x, hUW hx, hxy⟩

/-- A finite set has finite interaction neighborhood when every point has only
finitely many interaction neighbors.
@isnad1 id=finite.2h3v.s5.dd515945b552 from=translated src=- shape=75ff3a80 vocab=f5daf664
-/
theorem interactionNeighborhood_finite
    (R : X → X → Prop)
    (locallyFinite : ∀ x : X, {y : X | R x y}.Finite)
    (W : Set X) (hW : W.Finite) :
    (interactionNeighborhood R W).Finite := by
  apply (hW.biUnion fun x _ ↦ locallyFinite x).subset
  intro y
  rintro ⟨x, hx, hxy⟩
  exact Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx hxy)

/-- Iteration of interaction-neighborhood enlargement.  In the manuscript,
`iterateInteractionNeighborhood R i U₀` is the control window `Uᵢ`.-/
def iterateInteractionNeighborhood (R : X → X → Prop) :
    ℕ → Set X → Set X
  | 0, W => W
  | n + 1, W =>
      interactionNeighborhood R (iterateInteractionNeighborhood R n W)

/--
@isnad1 id=eq.0h3v.s4.6324ae7a9a5e from=translated src=- shape=8ebe66fe vocab=c9f9f592
-/
@[simp]
theorem iterateInteractionNeighborhood_zero
    (R : X → X → Prop) (W : Set X) :
    iterateInteractionNeighborhood R 0 W = W :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.fd20d0f8093d from=translated src=- shape=f1c82554 vocab=4913e5e3
-/
@[simp]
theorem iterateInteractionNeighborhood_succ
    (R : X → X → Prop) (n : ℕ) (W : Set X) :
    iterateInteractionNeighborhood R (n + 1) W =
      interactionNeighborhood R (iterateInteractionNeighborhood R n W) :=
  rfl

/-- Every finite seed has finite iterated neighborhoods.
@isnad1 id=finite.2h4v.s5.badaaf3001d2 from=translated src=- shape=1244932b vocab=9d1f1c2a
-/
theorem iterateInteractionNeighborhood_finite
    (R : X → X → Prop)
    (locallyFinite : ∀ x : X, {y : X | R x y}.Finite)
    (W : Set X) (hW : W.Finite) :
    ∀ n : ℕ, (iterateInteractionNeighborhood R n W).Finite
  | 0 => hW
  | n + 1 => interactionNeighborhood_finite R locallyFinite _
      (iterateInteractionNeighborhood_finite R locallyFinite W hW n)

/-- For a reflexive relation the control windows form an increasing sequence.
@isnad1 id=le.0h5v.s5.18ff17b964b9 from=translated src=- shape=a159b187 vocab=f87410f0
-/
theorem iterateInteractionNeighborhood_subset_succ
    (R : X → X → Prop) (reflexive : ∀ x : X, R x x)
    (W : Set X) (n : ℕ) :
    iterateInteractionNeighborhood R n W ⊆
      iterateInteractionNeighborhood R (n + 1) W :=
  subset_interactionNeighborhood R reflexive _

variable {G : Type u} [Group G] [MulAction G X]

/-- Invariance of the interaction relation makes one neighborhood enlargement
commute with the group action.
@isnad1 id=eq.1h5v.s7.e39e99187e00 from=translated src=- shape=a310926a vocab=a31a03d0
-/
theorem interactionNeighborhood_smul
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (g : G) (W : Set X) :
    interactionNeighborhood R (g • W) =
      g • interactionNeighborhood R W := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
    exact ⟨g⁻¹ • x, hx, (invariant g⁻¹ x y).mpr hxy⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨g • x, ?_, ?_⟩
    · exact Set.smul_mem_smul_set hx
    · have := (invariant g x (g⁻¹ • y)).mpr hxy
      simpa only [smul_smul, mul_inv_cancel, one_smul] using this

/-- Every iterated control window commutes with the group action.
@isnad1 id=eq.1h6v.s7.ffef05695edc from=translated src=- shape=e839a567 vocab=39294f5b
-/
theorem iterateInteractionNeighborhood_smul
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (g : G) (W : Set X) :
    ∀ n : ℕ,
      iterateInteractionNeighborhood R n (g • W) =
        g • iterateInteractionNeighborhood R n W
  | 0 => rfl
  | n + 1 => by
      change
        interactionNeighborhood R
            (iterateInteractionNeighborhood R n (g • W)) =
          g • interactionNeighborhood R
            (iterateInteractionNeighborhood R n W)
      rw [iterateInteractionNeighborhood_smul R invariant g W n,
        interactionNeighborhood_smul R invariant]

/-- The manuscript's control window after three successive Hom-neighborhood
enlargements.-/
def threeStepControlWindow (R : X → X → Prop) (W : Set X) : Set X :=
  iterateInteractionNeighborhood R 3 W

/-- The three-step control window of a finite seed is finite.
@isnad1 id=finite.2h3v.s5.3900c3991891 from=translated src=- shape=75ff3a80 vocab=73aca635
-/
theorem threeStepControlWindow_finite
    (R : X → X → Prop)
    (locallyFinite : ∀ x : X, {y : X | R x y}.Finite)
    (W : Set X) (hW : W.Finite) :
    (threeStepControlWindow R W).Finite :=
  iterateInteractionNeighborhood_finite R locallyFinite W hW 3

/-- The three-step control-window construction is equivariant.
@isnad1 id=eq.1h5v.s7.3de7a55bc964 from=translated src=- shape=a310926a vocab=f8d40571
-/
theorem threeStepControlWindow_smul
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (g : G) (W : Set X) :
    threeStepControlWindow R (g • W) =
      g • threeStepControlWindow R W :=
  iterateInteractionNeighborhood_smul R invariant g W 3

variable {O : Type w} [MulAction G O] [IsCancelSMul G O]

end MagnitudeConjecture.CoveringSeparation
