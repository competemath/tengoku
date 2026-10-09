module
public import Tengoku.Causalean.Causalean.Mathlib.MeasureTheory.WithDensityTransport
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection.Main

/-!
# Positive-density intersection for finite coordinate blocks

This module specializes graphoid intersection to coordinate projections on the union of four
finite index blocks.  All six pairwise-disjointness facts are explicit hypotheses; in particular,
the API cannot be applied to overlap degeneracies in which a conditioned coordinate is repeated
inside another block.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection

universe uM uΩ

open Causalean.Mathlib.MeasureTheory

private noncomputable def fourBlockValuesEquiv
    {M : Type uM} [DecidableEq M]
    {Ω : M → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (I J K L : Finset M)
    (hKL : Disjoint K L) (hJ_KL : Disjoint J (K ∪ L))
    (hI_JKL : Disjoint I (J ∪ (K ∪ L))) :
    FourBlock (ValuesOn I Ω) (ValuesOn J Ω) (ValuesOn K Ω) (ValuesOn L Ω) ≃ᵐ
      ValuesOn (fourBlockIndices I J K L) Ω := by
  let eKL := MeasurableEquiv.piFinsetUnion Ω hKL
  let eJKL :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ValuesOn J Ω)) eKL).trans
      (MeasurableEquiv.piFinsetUnion Ω hJ_KL)
  let e0 :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ValuesOn I Ω)) eJKL).trans
      (MeasurableEquiv.piFinsetUnion Ω hI_JKL)
  have hu : I ∪ (J ∪ (K ∪ L)) = fourBlockIndices I J K L := by
    simp only [fourBlockIndices, Finset.union_assoc]
  exact e0.trans (valuesEquivOfEq hu)

end Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection
