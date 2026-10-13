/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Attaching an unchanged conditional tail to a repaired head

Attaching the same normalized tail law to two head/latent-state laws
preserves their total variation exactly. Prepending the head then forgets
only the latent state. The coordinate formulas retain every source
occurrence and apply also to zero-mass rows.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

/--
@isnad1 id=isprobab.2h5v.s6.250013a42179 from=translated src=- shape=8cfe6473 vocab=ed272a6d
-/
theorem attachTail_probability {α Ω β : Type*} [Fintype α] [Fintype Ω] [Fintype β]
    (c : Ω × α → ℝ) (tail : α → β → ℝ) (hc : IsProbabilityWeight c)
    (htail : ∀ a, IsProbabilityWeight (tail a)) :
    IsProbabilityWeight (fun z : (Ω × α) × β => c z.1 * tail z.1.2 z.2) := by
  refine ⟨fun z => mul_nonneg (hc.1 z.1) ((htail z.1.2).1 z.2), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, fun a => (htail a).2, mul_one, hc.2]

/--
@isnad1 id=eq.1h6v.s7.487e413850fc from=translated src=- shape=4c3f59ce vocab=071e82e0
-/
theorem attachTail_dist {α Ω β : Type*} [Fintype α] [Fintype Ω] [Fintype β]
    (c d : Ω × α → ℝ) (tail : α → β → ℝ)
    (htail : ∀ a, IsProbabilityWeight (tail a)) :
    weightDist (fun z : (Ω × α) × β => c z.1 * tail z.1.2 z.2)
      (fun z => d z.1 * tail z.1.2 z.2) = weightDist c d := by
  simp only [weightDist, Fintype.sum_prod_type, ← sub_mul, abs_mul,
    fun a z => abs_of_nonneg ((htail a).1 z), ← Finset.mul_sum,
    fun a => (htail a).2, mul_one]

/--
@isnad1 id=eq.1h5v.s6.9b1228c18f6f from=translated src=- shape=e5c1760d vocab=3973fc1d
-/
theorem attachTail_fst {α Ω β : Type*} [Fintype α] [Fintype Ω] [Fintype β]
    (c : Ω × α → ℝ) (tail : α → β → ℝ)
    (htail : ∀ a, IsProbabilityWeight (tail a)) :
    mapWeight Prod.fst (fun z : (Ω × α) × β => c z.1 * tail z.1.2 z.2) = c := by
  funext z
  rw [mapWeight_fst]
  simp only [firstWeight, ← Finset.mul_sum, (htail z.2).2, mul_one]

/--
@isnad1 id=eq.0h7v.s7.4d77f5559d3a from=translated src=- shape=0cebdb8a vocab=46840d04
-/
theorem prependWeight_apply {α Ω : Type*} [Fintype α] [Fintype Ω] {t : Nat}
    (c : Ω × α → ℝ) (tail : α → (Fin t → Ω) → ℝ)
    (h : Ω) (z : Fin t → Ω) :
    mapWeight (fun az : (Ω × α) × (Fin t → Ω) =>
      (Fin.cons az.1.1 az.2 : Fin (t + 1) → Ω))
      (fun az => c az.1 * tail az.1.2 az.2) (Fin.cons h z) =
        ∑ a, c (h, a) * tail a z := by
  simp [mapWeight, Fintype.sum_prod_type, Fin.cons_inj, ite_and]

/--
@isnad1 id=eq.1h5v.s8.58e4e445239d from=translated src=- shape=028f0edf vocab=cabb8bb9
-/
theorem prependWeight_head {α Ω : Type*} [Fintype α] [Fintype Ω] {t : Nat}
    (c : Ω × α → ℝ) (tail : α → (Fin t → Ω) → ℝ)
    (htail : ∀ a, IsProbabilityWeight (tail a)) :
    mapWeight (fun z : Fin (t + 1) → Ω => z 0)
      (mapWeight (fun az : (Ω × α) × (Fin t → Ω) =>
        (Fin.cons az.1.1 az.2 : Fin (t + 1) → Ω))
        (fun az => c az.1 * tail az.1.2 az.2)) = firstWeight c := by
  calc
    _ = mapWeight Prod.fst
        (mapWeight Prod.fst
          (fun az : (Ω × α) × (Fin t → Ω) => c az.1 * tail az.1.2 az.2)) := by
      rw [mapWeight_comp, mapWeight_comp]
      rfl
    _ = _ := by rw [attachTail_fst c tail htail, mapWeight_fst]

/--
@isnad1 id=eq.0h6v.s8.2d5aa2bb845e from=translated src=- shape=4b54b4c5 vocab=e9a1a0b8
-/
theorem prependWeight_deterministic {α Ω : Type*} [Fintype α] [Fintype Ω] {t : Nat}
    (w : α → ℝ) (tail : α → (Fin t → Ω) → ℝ) (f : α → Ω) :
    mapWeight (fun az : (Ω × α) × (Fin t → Ω) =>
      (Fin.cons az.1.1 az.2 : Fin (t + 1) → Ω))
      (fun az => mapWeight (fun a => (f a, a)) w az.1 * tail az.1.2 az.2) =
      mapWeight (fun az : α × (Fin t → Ω) =>
        (Fin.cons (f az.1) az.2 : Fin (t + 1) → Ω))
        (fun az => w az.1 * tail az.1 az.2) := by
  funext z
  obtain ⟨⟨h, z⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (t + 1) => Ω)).surjective z
  change mapWeight _ _ (Fin.cons h z : Fin (t + 1) → Ω) =
    mapWeight _ _ (Fin.cons h z : Fin (t + 1) → Ω)
  rw [prependWeight_apply]
  have pair (h : Ω) (a : α) :
      mapWeight (fun a => (f a, a)) w (h, a) = if f a = h then w a else 0 := by
    simp [mapWeight, Prod.mk.injEq, and_comm, ite_and]
  simp only [pair]
  simp [mapWeight, Fintype.sum_prod_type, Fin.cons_inj, ite_and, ite_mul]

end Algebraic.Cutwidth.Extractor.Internal
