/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CastaingRepresentation
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableSupportJoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Carathéodory images of Effros-measurable correspondences

A jointly measurable map which is continuous in the state variable sends a
nonempty closed-valued Effros correspondence to an Effros correspondence.
The key point is that a Castaing representation remains fibrewise dense after
applying the continuous map.  Consequently every open hitting event is a
countable union of ordinary measurable inverse images.

This is the random-set version of the measurable Carathéodory image theorem
used when an observation or a criterion depends measurably on the outcome and
continuously on the latent state.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory TopologicalSpace

noncomputable section

namespace RandomSetTheory

/-- **Effros--Carathéodory image theorem.**  If `S` has nonempty closed values
in a Polish space and `φ` is jointly measurable and continuous in its second
variable, then the fibrewise image `φ(ω, ·) '' S(ω)` is Effros measurable.

The image itself need not be closed; Effros measurability only concerns open
hitting events.-/
theorem effrosMeasurable_caratheodoryImage
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x)) :
    RandomSet.IsEffrosMeasurable
      (fun ω => (fun x => φ (ω, x)) '' S ω) := by
  let c : ℕ → Ω → X := castaingRepresentation hS hclosed hne
  have hcmeas : ∀ n, Measurable (c n) :=
    castaingRepresentation_measurable hS hclosed hne
  have hcmem : ∀ n ω, c n ω ∈ S ω :=
    castaingRepresentation_mem hS hclosed hne
  have hcclosure : ∀ ω, closure (Set.range fun n => c n ω) = S ω :=
    closure_range_castaingRepresentation hS hclosed hne
  intro U hU
  have hevalMeas : ∀ n, Measurable (fun ω => φ (ω, c n ω)) := by
    intro n
    exact hφmeas.comp (measurable_id.prodMk (hcmeas n))
  have hEq :
      {ω | (((fun x => φ (ω, x)) '' S ω) ∩ U).Nonempty} =
        ⋃ n : ℕ, (fun ω => φ (ω, c n ω)) ⁻¹' U := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨y, ⟨x, hxS, rfl⟩, hφxU⟩
      have hopen : IsOpen ((fun z => φ (ω, z)) ⁻¹' U) :=
        (hφcont ω).isOpen_preimage U hU
      have hhit :
          (closure (Set.range fun n => c n ω) ∩
            (fun z => φ (ω, z)) ⁻¹' U).Nonempty := by
        refine ⟨x, ?_, hφxU⟩
        rw [hcclosure ω]
        exact hxS
      rw [closure_inter_open_nonempty_iff hopen] at hhit
      rcases hhit with ⟨z, ⟨n, rfl⟩, hnU⟩
      exact ⟨n, hnU⟩
    · rintro ⟨n, hnU⟩
      exact ⟨φ (ω, c n ω), ⟨c n ω, hcmem n ω, rfl⟩, hnU⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun n => hevalMeas n hU.measurableSet

/-- Parameterized Effros--Carathéodory theorem.  A correspondence `S(ω)` can
be transported by a map depending additionally on a measurable parameter
`θ`; the resulting correspondence on `Ω × Θ` remains Effros measurable.-/
theorem effrosMeasurable_caratheodoryImage_param
    {Ω Θ X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : (Ω × Θ) × X → Y} (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x)) :
    RandomSet.IsEffrosMeasurable
      (fun p : Ω × Θ => (fun x => φ (p, x)) '' S p.1) := by
  have hSlift : RandomSet.IsEffrosMeasurable
      (fun p : Ω × Θ => S p.1) := by
    intro U hU
    have hEq :
        {p : Ω × Θ | (S p.1 ∩ U).Nonempty} =
          Prod.fst ⁻¹' {ω | (S ω ∩ U).Nonempty} := by
      ext p
      rfl
    rw [hEq]
    exact measurable_fst (hS U hU)
  exact effrosMeasurable_caratheodoryImage hSlift
    (fun p => hclosed p.1) (fun p => hne p.1) hφmeas hφcont

/-- Joint measurability of the support function of a compact-valued
Carathéodory image in a separable Hilbert space.-/
theorem measurable_supportFunction_caratheodoryImage_joint
    {Ω X H : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : Ω × X → H} (hφmeas : Measurable φ)
    (hφcont : ∀ ω, Continuous fun x => φ (ω, x)) :
    Measurable (fun p : Ω × H =>
      supportFunction ((fun x => φ (p.1, x)) '' S p.1) p.2) := by
  apply measurable_supportFunction_joint
    (effrosMeasurable_caratheodoryImage hS
      (fun ω => (hcompact ω).isClosed) hne hφmeas hφcont)
  · exact fun ω => (hcompact ω).image (hφcont ω)
  · exact fun ω => (hne ω).image (fun x => φ (ω, x))

/-- Parameterized joint support-function measurability.  Both the external
parameter and the support direction are measurable variables.-/
theorem measurable_supportFunction_caratheodoryImage_param_joint
    {Ω Θ X H : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : (Ω × Θ) × X → H} (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x)) :
    Measurable (fun q : (Ω × Θ) × H =>
      supportFunction ((fun x => φ (q.1, x)) '' S q.1.1) q.2) := by
  have hEffros := effrosMeasurable_caratheodoryImage_param
    hS (fun ω => (hcompact ω).isClosed) hne hφmeas hφcont
  apply measurable_supportFunction_joint hEffros
  · exact fun p => (hcompact p.1).image (hφcont p)
  · exact fun p => (hne p.1).image (fun x => φ (p, x))

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
