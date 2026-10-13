/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture.Internal

/-!
# Statistical distance under finite mixtures

Retaining a finite mixture tag gives exact averaging of component total
variation distances. Forgetting the tag gives the corresponding upper
bound. Uniform retained-seed families therefore have distance equal to
the average of their conditional distances, including empty seed types.

The component weights need not be probability distributions. Only the
mixture coefficients in the distance identities must be nonnegative;
the pushforward and seed-family linearity identities hold for all real
coefficients. These are finite algebraic identities, with no claim about
computing arbitrary real weights.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A deterministic pushforward commutes with arbitrary scalar multiplication.
@isnad1 id=eq.0h5v.s5.5fb367bb7982 from=translated src=- shape=b5fb9624 vocab=ec127fe3
-/
theorem mapWeight_mul {α β : Type*} [Fintype α]
    (f : α → β) (c : ℝ) (p : α → ℝ) :
    mapWeight f (fun x => c * p x) = fun y => c * mapWeight f p y :=
  Internal.mapWeight_mul f c p

/-- A deterministic pushforward commutes with finite sums of arbitrary weights.
@isnad1 id=eq.0h5v.s6.b0f50c199ecd from=translated src=- shape=8404d144 vocab=22ea630d
-/
theorem mapWeight_sum {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : α → β) (p : ι → α → ℝ) :
    mapWeight f (fun x => ∑ i, p i x) = fun y => ∑ i, mapWeight f (p i) y :=
  Internal.mapWeight_sum f p

/-- Finite mixtures commute with deterministic maps, without sign or mass assumptions.
@isnad1 id=eq.0h6v.s6.d42e7c346eff from=translated src=- shape=2879ee5d vocab=3c94f349
-/
theorem mapWeight_mixture {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : α → β) (w : ι → ℝ) (p : ι → α → ℝ) :
    mapWeight f (fun x => ∑ i, w i * p i x) =
      fun y => ∑ i, w i * mapWeight f (p i) y :=
  Internal.mapWeight_mixture f w p

/-- A map that keeps the mixture tag pushes each component forward separately.
@isnad1 id=eq.0h6v.s7.00addbd7ecb0 from=translated src=- shape=53c38b5a vocab=fda8b667
-/
theorem mapWeight_tagged {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : ι → α → β) (w : ι → ℝ) (p : ι → α → ℝ) :
    mapWeight (fun ix : ι × α => (ix.1, f ix.1 ix.2))
      (fun ix => w ix.1 * p ix.1 ix.2) =
        fun iz => w iz.1 * mapWeight (f iz.1) (p iz.1) iz.2 :=
  Internal.mapWeight_tagged f w p

/-- Keeping the seed commutes with pushing forward its conditional output family.
@isnad1 id=eq.0h5v.s6.669a727c913c from=translated src=- shape=25adb408 vocab=2f6bf3b4
-/
theorem mapWeight_seedFamilyWeight {Seed α β : Type*}
    [Fintype Seed] [Fintype α] (f : Seed → α → β) (p : Seed → α → ℝ) :
    mapWeight (fun yz : Seed × α => (yz.1, f yz.1 yz.2)) (seedFamilyWeight p) =
      seedFamilyWeight (fun y => mapWeight (f y) (p y)) :=
  Internal.mapWeight_seedFamilyWeight f p

/-- Retained-seed weights are linear in arbitrary finite mixtures of conditional laws.
@isnad1 id=eq.0h5v.s6.17710d5f296c from=translated src=- shape=5d7bd96d vocab=b01bb0b6
-/
theorem seedFamilyWeight_mixture {ι Seed Ω : Type*} [Fintype ι] [Fintype Seed]
    (w : ι → ℝ) (p : ι → Seed → Ω → ℝ) :
    seedFamilyWeight (fun y z => ∑ i, w i * p i y z) =
      fun yz => ∑ i, w i * seedFamilyWeight (p i) yz :=
  Internal.seedFamilyWeight_mixture w p

/-- Retaining the tag makes mixture distance exactly the weighted sum of component distances.
@isnad1 id=eq.1h5v.s7.d9a19687b33b from=translated src=- shape=347b6131 vocab=27fb71ca
-/
theorem weightDist_tagged_mixture {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p q : ι → α → ℝ) (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist (fun ix : ι × α => w ix.1 * p ix.1 ix.2)
      (fun ix => w ix.1 * q ix.1 ix.2) = ∑ i, w i * weightDist (p i) (q i) :=
  Internal.weightDist_tagged_mixture w p q nonnegative

/-- Retained-seed distance is the average conditional distance, also for an empty seed type.
@isnad1 id=eq.0h4v.s6.efafd389a607 from=translated src=- shape=4742043f vocab=7d82f136
-/
theorem weightDist_seedFamilyWeight {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (p q : Seed → Ω → ℝ) :
    weightDist (seedFamilyWeight p) (seedFamilyWeight q) =
      (∑ y, weightDist (p y) (q y)) / (Fintype.card Seed : ℝ) :=
  Internal.weightDist_seedFamilyWeight p q

/-- An actual retained-seed output is compared with its witness by averaging fiber distances.
@isnad1 id=eq.0h6v.s6.35fb79be5268 from=translated src=- shape=adfa2a29 vocab=5ac0f4e2
-/
theorem weightDist_weightedSeededOutput_seedFamilyWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    (p : α → ℝ) (C : α → Seed → Ω) (q : Seed → Ω → ℝ) :
    weightDist (weightedSeededOutput p C) (seedFamilyWeight q) =
      (∑ y, weightDist (mapWeight (fun x => C x y) p) (q y)) /
        (Fintype.card Seed : ℝ) :=
  Internal.weightDist_weightedSeededOutput_seedFamilyWeight p C q

end Algebraic.Cutwidth.Extractor
