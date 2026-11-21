/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CastaingRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Operations on Effros-measurable correspondences

Singleton correspondences and products are the basic constructors needed to
assemble observation correspondences such as `X(ω) × {Y(ω)} × {M(ω)}`.
Minkowski addition and deterministic scalar multiplication provide the
standard algebra of random closed sets.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory TopologicalSpace
open scoped Pointwise

noncomputable section

namespace Tengoku.Randomsettheory.RandomSet

open RandomSetTheory

/-- A measurable function, viewed as a singleton-valued correspondence, is
Effros measurable.-/
theorem isEffrosMeasurable_singleton
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {f : Ω → X} (hf : Measurable f) :
    IsEffrosMeasurable (fun ω => ({f ω} : Set X)) := by
  intro U hU
  have hEq : {ω | (({f ω} : Set X) ∩ U).Nonempty} = f ⁻¹' U := by
    ext ω
    simp
  rw [hEq]
  exact hf hU.measurableSet

/-- Products of nonempty closed-valued Effros correspondences are Effros
measurable.  The proof pairs their two Castaing representations using the
canonical enumeration of `ℕ × ℕ`.-/
theorem IsEffrosMeasurable.prod
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [MetricSpace Y] [CompleteSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [Nonempty Y]
    {S : Ω → Set X} {T : Ω → Set Y}
    (hS : IsEffrosMeasurable S) (hT : IsEffrosMeasurable T)
    (hSclosed : ∀ ω, IsClosed (S ω)) (hTclosed : ∀ ω, IsClosed (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty) :
    IsEffrosMeasurable (fun ω => S ω ×ˢ T ω) := by
  let f : ℕ → Ω → X := castaingRepresentation hS hSclosed hSne
  let g : ℕ → Ω → Y := castaingRepresentation hT hTclosed hTne
  let q : ℕ → Ω → X × Y := fun n ω =>
    (f (Nat.unpair n).1 ω, g (Nat.unpair n).2 ω)
  have hqmeas : ∀ n, Measurable (q n) := by
    intro n
    exact (castaingRepresentation_measurable hS hSclosed hSne
      (Nat.unpair n).1).prodMk
        (castaingRepresentation_measurable hT hTclosed hTne
          (Nat.unpair n).2)
  apply effrosMeasurable_of_closure_range hqmeas
  intro ω
  have hrange : Set.range (fun n => q n ω) =
      Set.range (fun n => f n ω) ×ˢ Set.range (fun n => g n ω) := by
    ext z
    rcases z with ⟨x, y⟩
    constructor
    · rintro ⟨n, hn⟩
      rw [← hn]
      exact ⟨⟨(Nat.unpair n).1, rfl⟩, ⟨(Nat.unpair n).2, rfl⟩⟩
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      refine ⟨Nat.pair i j, ?_⟩
      simp [q, f, g, hi, hj]
  rw [hrange, closure_prod_eq,
    closure_range_castaingRepresentation hS hSclosed hSne ω,
    closure_range_castaingRepresentation hT hTclosed hTne ω]

/-- The pointwise Minkowski sum of two nonempty closed-valued Effros
correspondences in a separable Banach space is Effros measurable.-/
theorem IsEffrosMeasurable.add
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E}
    (hS : IsEffrosMeasurable S) (hT : IsEffrosMeasurable T)
    (hSclosed : ∀ ω, IsClosed (S ω)) (hTclosed : ∀ ω, IsClosed (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty) :
    IsEffrosMeasurable (fun ω => S ω + T ω) := by
  have hprod := hS.prod hT hSclosed hTclosed hSne hTne
  have himage := hprod.image (continuous_fst.add continuous_snd)
  simpa only [Pi.add_apply, Set.add_image_prod] using himage

/-- Deterministic scalar multiplication preserves Effros measurability.-/
theorem IsEffrosMeasurable.const_smul
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Ω → Set E} (hS : IsEffrosMeasurable S) (c : ℝ) :
    IsEffrosMeasurable (fun ω => c • S ω) := by
  simpa only [Set.image_smul] using
    hS.image (continuous_const_smul c : Continuous (fun x : E => c • x))

end Tengoku.Randomsettheory.RandomSet
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
