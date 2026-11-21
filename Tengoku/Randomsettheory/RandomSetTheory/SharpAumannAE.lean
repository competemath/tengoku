/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AEModification
import Tengoku.Randomsettheory.RandomSetTheory.SharpAumannRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Almost-everywhere sharp Aumann representation

The sharp kernel representation is insensitive to changes of the feasible
correspondence on a null set.  Combining this fact with
`correspondenceOn` upgrades the pointwise compactness/nonemptiness hypotheses
of the measurable lifting theorem to the almost-sure hypotheses customary in
random-set models.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory Set

noncomputable section

namespace RandomSetTheory

/-- Kernel support is invariant under almost-everywhere equality of the
supporting correspondences.-/
theorem KernelSupportedOn.congr_ae
    {O X : Type*} [MeasurableSpace O] [MeasurableSpace X]
    {μ : Measure O} {S T : O → Set X}
    {κ : ProbabilityTheory.Kernel O X}
    (hκ : KernelSupportedOn μ S κ) (hST : S =ᵐ[μ] T) :
    KernelSupportedOn μ T κ := by
  filter_upwards [hκ, hST] with o hκo hSTo
  rwa [← hSTo]

/-- The set of attainable kernel moments depends only on the almost-sure
class of the feasible correspondence.-/
theorem kernelAttainableMoments_congr_ae
    {O X E : Type*} [MeasurableSpace O] [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure O} {S T : O → Set X} {φ : O × X → E}
    (hST : S =ᵐ[μ] T) :
    kernelAttainableMoments μ S φ = kernelAttainableMoments μ T φ := by
  apply Set.Subset.antisymm
  · rintro y ⟨κ, hκmarkov, hκsupp, hφint, hφeq⟩
    exact ⟨κ, hκmarkov, hκsupp.congr_ae hST, hφint, hφeq⟩
  · rintro y ⟨κ, hκmarkov, hκsupp, hφint, hφeq⟩
    exact ⟨κ, hκmarkov, hκsupp.congr_ae hST.symm, hφint, hφeq⟩

/-- Sharp Aumann representation when compactness and nonemptiness of the
feasible correspondence hold only on a measurable full-measure set.

The purification equality is stated for the original correspondence; null
set regularization transports it automatically to the everywhere-regular
representative used by the measurable lifting theorem.-/
theorem kernelAttainableMoments_eq_aumannExpectation_of_purification_ae
    {O X E : Type*} [MeasurableSpace O] [MeasurableSpace X]
    [MetricSpace X] [CompleteSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure O} [SFinite μ]
    {A : Set O} (hAmeas : MeasurableSet A) (hA : ∀ᵐ o ∂μ, o ∈ A)
    {S : O → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ o ∈ A, IsCompact (S o))
    (hne : ∀ o ∈ A, (S o).Nonempty)
    (x₀ : X)
    {φ : O × X → E} (hφMeas : Measurable φ)
    (hφCont : ∀ o, Continuous fun x => φ (o, x))
    (hpurify :
      aumannExpectation μ (fun o => (fun x => φ (o, x)) '' S o) =
        aumannExpectation μ
          (fun o => closedConvexHull ℝ ((fun x => φ (o, x)) '' S o))) :
    kernelAttainableMoments μ S φ =
      aumannExpectation μ (fun o => (fun x => φ (o, x)) '' S o) := by
  classical
  letI : Nonempty X := ⟨x₀⟩
  let T : O → Set X := correspondenceOn A S {x₀}
  have hT : RandomSet.IsEffrosMeasurable T :=
    effrosMeasurable_correspondenceOn hAmeas hS {x₀}
  have hTcompact : ∀ o, IsCompact (T o) := fun o =>
    correspondenceOn_isCompact hcompact isCompact_singleton o
  have hTne : ∀ o, (T o).Nonempty := fun o =>
    correspondenceOn_nonempty hne (Set.singleton_nonempty x₀) o
  have hST : T =ᵐ[μ] S := correspondenceOn_ae_eq hA
  have hPhi :
      (fun o => (fun x => φ (o, x)) '' T o) =ᵐ[μ]
        (fun o => (fun x => φ (o, x)) '' S o) :=
    hST.mono fun o h => congrArg (fun K => (fun x => φ (o, x)) '' K) h
  have hPhiConv :
      (fun o => closedConvexHull ℝ ((fun x => φ (o, x)) '' T o)) =ᵐ[μ]
        (fun o => closedConvexHull ℝ ((fun x => φ (o, x)) '' S o)) :=
    hPhi.mono fun _ h => congrArg (closedConvexHull ℝ) h
  have hRaw :
      aumannExpectation μ (fun o => (fun x => φ (o, x)) '' T o) =
        aumannExpectation μ (fun o => (fun x => φ (o, x)) '' S o) :=
    aumannExpectation_congr_ae hPhi
  have hConv :
      aumannExpectation μ
          (fun o => closedConvexHull ℝ ((fun x => φ (o, x)) '' T o)) =
        aumannExpectation μ
          (fun o => closedConvexHull ℝ ((fun x => φ (o, x)) '' S o)) :=
    aumannExpectation_congr_ae hPhiConv
  have hpurifyT :
      aumannExpectation μ (fun o => (fun x => φ (o, x)) '' T o) =
        aumannExpectation μ
          (fun o => closedConvexHull ℝ ((fun x => φ (o, x)) '' T o)) :=
    hRaw.trans (hpurify.trans hConv.symm)
  have hTmeas : ∀ o, MeasurableSet (T o) := fun o =>
    (hTcompact o).isClosed.measurableSet
  have hsharpT :=
    kernelAttainableMoments_eq_aumannExpectation_of_purification
      hT hTmeas hTcompact hTne hφMeas hφCont hpurifyT
  calc
    kernelAttainableMoments μ S φ = kernelAttainableMoments μ T φ :=
      kernelAttainableMoments_congr_ae hST.symm
    _ = aumannExpectation μ (fun o => (fun x => φ (o, x)) '' T o) := hsharpT
    _ = aumannExpectation μ (fun o => (fun x => φ (o, x)) '' S o) := hRaw

/-- Almost-everywhere version of the automatic atomless sharp
representation.  Compactness, nonemptiness, and the norm envelope are only
required on a measurable full-measure set.  The correspondence is replaced
by a singleton off that set, and finite-dimensional binary purification is
then applied to this everywhere-regular representative.-/
theorem kernelAttainableMoments_eq_aumannExpectation_of_atomless_ae
    {O X H : Type*} [MeasurableSpace O] [MeasurableSpace X]
    [MetricSpace X] [CompleteSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [FiniteDimensional ℝ H]
    {μ : Measure O} [IsFiniteMeasure μ]
    (hμ : IsAtomlessMeasure μ)
    {A : Set O} (hAmeas : MeasurableSet A) (hA : ∀ᵐ o ∂μ, o ∈ A)
    {S : O → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ o ∈ A, IsCompact (S o))
    (hne : ∀ o ∈ A, (S o).Nonempty)
    (x₀ : X)
    {φ : O × X → H} (hφMeas : Measurable φ)
    (hφCont : ∀ o, Continuous fun x => φ (o, x))
    {g : O → ℝ} (hg : Integrable g μ)
    (hdom : ∀ o ∈ A, ∀ x ∈ S o, ‖φ (o, x)‖ ≤ g o) :
    kernelAttainableMoments μ S φ =
      aumannExpectation μ (fun o => (fun x => φ (o, x)) '' S o) := by
  classical
  letI : Nonempty X := ⟨x₀⟩
  let T : O → Set X := correspondenceOn A S {x₀}
  let G : O → ℝ := fun o => if o ∈ A then g o else ‖φ (o, x₀)‖
  have hT : RandomSet.IsEffrosMeasurable T :=
    effrosMeasurable_correspondenceOn hAmeas hS {x₀}
  have hTcompact : ∀ o, IsCompact (T o) := fun o =>
    correspondenceOn_isCompact hcompact isCompact_singleton o
  have hTne : ∀ o, (T o).Nonempty := fun o =>
    correspondenceOn_nonempty hne (Set.singleton_nonempty x₀) o
  have hTmeas : ∀ o, MeasurableSet (T o) := fun o =>
    (hTcompact o).isClosed.measurableSet
  have hST : T =ᵐ[μ] S := correspondenceOn_ae_eq hA
  have hPhi :
      (fun o => (fun x => φ (o, x)) '' T o) =ᵐ[μ]
        (fun o => (fun x => φ (o, x)) '' S o) :=
    hST.mono fun o h => congrArg (fun K => (fun x => φ (o, x)) '' K) h
  have hGae : G =ᵐ[μ] g := hA.mono fun o ho => by simp [G, ho]
  have hGint : Integrable G μ := hg.congr hGae.symm
  have hTdom : ∀ o, ∀ x ∈ T o, ‖φ (o, x)‖ ≤ G o := by
    intro o x hx
    by_cases ho : o ∈ A
    · have hxS : x ∈ S o := by
        simpa [T, correspondenceOn, ho] using hx
      simpa [G, ho] using hdom o ho x hxS
    · have hx0 : x = x₀ := by
        simpa [T, correspondenceOn, ho] using hx
      subst x
      simp [G, ho]
  have hsharpT :=
    kernelAttainableMoments_eq_aumannExpectation_of_atomless
      hμ hT hTmeas hTcompact hTne hφMeas hφCont hGint hTdom
  calc
    kernelAttainableMoments μ S φ = kernelAttainableMoments μ T φ :=
      kernelAttainableMoments_congr_ae hST.symm
    _ = aumannExpectation μ (fun o => (fun x => φ (o, x)) '' T o) := hsharpT
    _ = aumannExpectation μ (fun o => (fun x => φ (o, x)) '' S o) :=
      aumannExpectation_congr_ae hPhi

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
