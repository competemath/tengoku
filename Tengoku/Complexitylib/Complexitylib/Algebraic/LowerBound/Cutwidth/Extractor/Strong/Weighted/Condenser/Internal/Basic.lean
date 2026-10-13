/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
public import Tengoku

/-!
# Probability identities for seed-indexed output families

The retained-seed weighting is a deterministic image of a source and seed
pair. Its finite tests agree with weighted seeded tests, including repeated
output values. Normalized conditional distributions give a normalized joint
distribution whenever the seed type is nonempty.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

/--
@isnad1 id=eq.0h5v.s6.ecdd5e03e85e from=translated src=- shape=4805df38 vocab=ef46c379
-/
theorem weightedSeededOutput_eq_mapWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (p : α → ℝ) (C : α → Seed → Ω) :
    weightedSeededOutput p C = mapWeight (fun xy : α × Seed => (xy.2, C xy.1 xy.2))
      (fun xy => p xy.1 / (Fintype.card Seed : ℝ)) := by
  funext yz
  rcases yz with ⟨y, z⟩
  simp only [weightedSeededOutput, mapWeight, Fintype.sum_prod_type, Prod.mk.injEq,
    ite_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_div, ite_div, zero_div]

/--
@isnad1 id=isprobab.1h3v.s5.4c1c0fdb2d18 from=translated src=- shape=cbd250a6 vocab=3e7f3a5e
-/
theorem probabilityWeight_seedFamilyWeight {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed]
    (q : Seed → Ω → ℝ) (probability : ∀ y, IsProbabilityWeight (q y)) :
    IsProbabilityWeight (seedFamilyWeight q) := by
  have nonzero : (Fintype.card Seed : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun yz => div_nonneg ((probability yz.1).1 yz.2) (Nat.cast_nonneg _), ?_⟩
  have mass (y : Seed) : ∑ z, q y z = 1 := (probability y).2
  simp only [seedFamilyWeight, Fintype.sum_prod_type, ← Finset.sum_div, mass]
  simp [nonzero]

/--
@isnad1 id=isprobab.1h5v.s5.0cdeae426f57 from=translated src=- shape=c45f3f10 vocab=75a53368
-/
theorem probabilityWeight_weightedSeededOutput {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed]
    {p : α → ℝ} (probability : IsProbabilityWeight p) (C : α → Seed → Ω) :
    IsProbabilityWeight (weightedSeededOutput p C) :=
  probabilityWeight_seedFamilyWeight (fun y => mapWeight (fun x => C x y) p)
    (fun y => probability.map (fun x => C x y))

/--
@isnad1 id=eq.0h6v.s5.962417f1ae43 from=translated src=- shape=d7d20028 vocab=1d157a36
-/
theorem weightTestProb_weightedSeededOutput {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (p : α → ℝ) (C : α → Seed → Ω)
    (T : Finset (Seed × Ω)) :
    weightTestProb (weightedSeededOutput p C) T = weightedSeededTestProb p C T := by
  rw [weightedSeededOutput_eq_mapWeight, weightTestProb_map, Fintype.sum_prod_type]
  have inner (x : α) :
      (∑ y, if (y, C x y) ∈ T then p x / (Fintype.card Seed : ℝ) else 0) =
        p x * ((Finset.univ.filter fun y => (y, C x y) ∈ T).card : ℝ) /
          (Fintype.card Seed : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  simp_rw [inner]
  exact (Finset.sum_div _ _ _).symm

/--
@isnad1 id=eq.0h4v.s6.4e475ec67a56 from=translated src=- shape=9faad81a vocab=cee4fae9
-/
theorem weightTestProb_seedFamilyWeight {Seed Ω : Type*} [Fintype Seed]
    (q : Seed → Ω → ℝ) (T : Finset (Seed × Ω)) :
    weightTestProb (seedFamilyWeight q) T =
      (∑ yz ∈ T, q yz.1 yz.2) / (Fintype.card Seed : ℝ) := by
  simp only [weightTestProb, seedFamilyWeight, Finset.sum_div]

/--
@isnad1 id=eq.0h3v.s5.5b49fe440062 from=translated src=- shape=92334a3b vocab=6152aa2b
-/
theorem weightTestProb_seedFamilyWeight_uniform {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] (T : Finset (Seed × Ω)) :
    weightTestProb (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) T =
      uniformSeededTestProb T := by
  rw [weightTestProb_seedFamilyWeight]
  simp only [uniformWeight, Finset.sum_const, nsmul_eq_mul, uniformSeededTestProb,
    div_eq_mul_inv, mul_inv_rev]
  ring

/--
@isnad1 id=eq.0h6v.s6.bffecd2d1e6f from=translated src=- shape=d43094e9 vocab=eec7d109
-/
theorem weightTestProb_seedFamilyWeight_mixture {ι Seed Ω : Type*}
    [Fintype ι] [Fintype Seed] (w : ι → ℝ) (q : ι → Seed → Ω → ℝ)
    (T : Finset (Seed × Ω)) :
    weightTestProb (seedFamilyWeight (fun y z => ∑ i, w i * q i y z)) T =
      ∑ i, w i * weightTestProb (seedFamilyWeight (q i)) T := by
  simp only [weightTestProb_seedFamilyWeight]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, mul_div_assoc]

/--
@isnad1 id=cappedwe.2h5v.s5.8935396c0879 from=translated src=- shape=0f5cb558 vocab=56fd417b
-/
theorem cappedWeight_map_injective {α β : Type*} [Fintype α]
    {p : α → ℝ} {K : Nat} (cap : CappedWeight p K)
    (f : α → β) (injective : Function.Injective f) : CappedWeight (mapWeight f p) K := by
  intro y
  by_cases occurs : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := occurs
    simpa only [mapWeight, injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] using cap x
  · have missing (x : α) : f x ≠ y := fun same => occurs ⟨x, same⟩
    simp [mapWeight, missing]

end Algebraic.Cutwidth.Extractor.Internal
