/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.FlagRankedSequence
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.ShufflePathBinomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shuffling finite maximal chains without an ambient grading

Maximal chains of prescribed cardinalities in two finite bounded orders
inject into maximal chains of the product.  The binomial coefficient counts
the choices of left-step positions.
-/

namespace HansenCograph

universe u v

/-- The product-chain construction, expressed directly on sized maximal
chains and ordinary interleavings.-/
noncomputable def sizedFlagProductEmbedding
    {P : Type u} {Q : Type v}
    [PartialOrder P] [BoundedOrder P] [Finite P]
    [PartialOrder Q] [BoundedOrder Q] [Finite Q]
    (n m : ℕ) :
    SizedFlag P n × SizedFlag Q m × Interleaving n m ↪ Flag (P × Q) where
  toFun x := (RankedFlag.prodOfShuffle
    (sizedFlagRankedEmbedding n x.1)
    (sizedFlagRankedEmbedding m x.2.1)
    (Interleaving.embedding n m x.2.2)).toFlag
  inj' := by
    rintro ⟨f, g, s⟩ ⟨f', g', s'⟩ h
    have hranked := RankedFlag.toFlag_injective h
    have hinj : Function.Injective
        (fun x : RankedFlag P n × RankedFlag Q m × ShufflePath n m ↦
          RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2) :=
      RankedFlag.prodOfShuffle_injective
    have hranked' :
        (fun x : RankedFlag P n × RankedFlag Q m × ShufflePath n m ↦
          RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2)
            (sizedFlagRankedEmbedding n f,
              sizedFlagRankedEmbedding m g, Interleaving.embedding n m s) =
        (fun x : RankedFlag P n × RankedFlag Q m × ShufflePath n m ↦
          RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2)
            (sizedFlagRankedEmbedding n f',
              sizedFlagRankedEmbedding m g', Interleaving.embedding n m s') :=
      hranked
    have hcode := hinj hranked'
    apply Prod.ext
    · exact (sizedFlagRankedEmbedding n).injective (congrArg Prod.fst hcode)
    · apply Prod.ext
      · exact (sizedFlagRankedEmbedding m).injective
          (congrArg (Prod.fst ∘ Prod.snd) hcode)
      · exact (Interleaving.embedding n m).injective
          (congrArg (Prod.snd ∘ Prod.snd) hcode)

/-- If the two factor chains have `n + 1` and `m + 1` elements, their
binomially many interleavings give distinct product maximal chains.
@isnad1 id=le.0h4v.s6.659f56895864 from=translated src=- shape=a916e6ad vocab=4647473a
-/
theorem sizedFlag_product_choose_lower_bound
    {P : Type u} {Q : Type v}
    [PartialOrder P] [BoundedOrder P] [Finite P]
    [PartialOrder Q] [BoundedOrder Q] [Finite Q]
    (n m : ℕ) :
    Nat.card (SizedFlag P n) * Nat.card (SizedFlag Q m) *
        Nat.choose (n + m) n ≤ Nat.card (Flag (P × Q)) := by
  have h := Nat.card_le_card_of_injective
    (sizedFlagProductEmbedding (P := P) (Q := Q) n m)
    (sizedFlagProductEmbedding (P := P) (Q := Q) n m).injective
  rw [Nat.card_prod, Nat.card_prod, Set.powersetCard.card, Nat.card_fin] at h
  simpa only [Nat.mul_assoc] using h

end HansenCograph
