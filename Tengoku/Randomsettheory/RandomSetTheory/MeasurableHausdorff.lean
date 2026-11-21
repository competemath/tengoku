/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CastaingRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurability of Hausdorff distance

Castaing representations reduce Hausdorff edistance to a countable
supremum of countable infima of pairwise distances.  This gives measurability
without introducing a measurable hyperspace of closed sets.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace

noncomputable section

namespace RandomSetTheory

/-- The extended Hausdorff distance between two nonempty closed-valued
Effros correspondences is measurable.-/
theorem measurable_hausdorffEDist_correspondence
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hSclosed : ∀ ω, IsClosed (S ω)) (hTclosed : ∀ ω, IsClosed (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty) :
    Measurable (fun ω => hausdorffEDist (S ω) (T ω)) := by
  let f : ℕ → Ω → E := castaingRepresentation hS hSclosed hSne
  let g : ℕ → Ω → E := castaingRepresentation hT hTclosed hTne
  have hf : ∀ n, Measurable (f n) :=
    castaingRepresentation_measurable hS hSclosed hSne
  have hg : ∀ n, Measurable (g n) :=
    castaingRepresentation_measurable hT hTclosed hTne
  have hEq : (fun ω => hausdorffEDist (S ω) (T ω)) =
      fun ω =>
        (⨆ n : ℕ, ⨅ m : ℕ, edist (f n ω) (g m ω)) ⊔
          (⨆ m : ℕ, ⨅ n : ℕ, edist (g m ω) (f n ω)) := by
    funext ω
    calc
      hausdorffEDist (S ω) (T ω) =
          hausdorffEDist
            (closure (Set.range fun n => f n ω))
            (closure (Set.range fun n => g n ω)) := by
              rw [closure_range_castaingRepresentation hS hSclosed hSne ω,
                closure_range_castaingRepresentation hT hTclosed hTne ω]
      _ = hausdorffEDist
          (Set.range fun n => f n ω) (Set.range fun n => g n ω) :=
        hausdorffEDist_closure
      _ = (⨆ n : ℕ, ⨅ m : ℕ, edist (f n ω) (g m ω)) ⊔
          (⨆ m : ℕ, ⨅ n : ℕ, edist (g m ω) (f n ω)) := by
        simp only [hausdorffEDist_def, ← Set.image_univ, iSup_image,
          infEDist, iInf_image, Set.mem_univ, iSup_true, iInf_true]
  rw [hEq]
  exact (Measurable.iSup fun n => Measurable.iInf fun m =>
    (hf n).edist (hg m)).sup
      (Measurable.iSup fun m => Measurable.iInf fun n =>
        (hg m).edist (hf n))

/-- The real Hausdorff distance between two nonempty closed-valued Effros
correspondences is measurable.-/
theorem measurable_hausdorffDist_correspondence
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S T : Ω → Set E}
    (hS : RandomSet.IsEffrosMeasurable S)
    (hT : RandomSet.IsEffrosMeasurable T)
    (hSclosed : ∀ ω, IsClosed (S ω)) (hTclosed : ∀ ω, IsClosed (T ω))
    (hSne : ∀ ω, (S ω).Nonempty) (hTne : ∀ ω, (T ω).Nonempty) :
    Measurable (fun ω => hausdorffDist (S ω) (T ω)) := by
  exact (measurable_hausdorffEDist_correspondence
    hS hT hSclosed hTclosed hSne hTne).ennreal_toReal

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
