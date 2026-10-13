/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.MeasureTheory.StandardBorelSpace
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.MeasureTheory.Sum

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Option

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Option`.
-/

@[expose] public section

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

namespace MeasureTheory.Option

instance instMeasurableSpaceOptionLeanPool : MeasurableSpace (Option A) :=
  MeasurableSpace.comap (Option.elim' (Sum.inl ()) Sum.inr) inferInstance

@[simp, fun_prop]
lemma measurable_some : Measurable (some : A → Option A) := by
  rw [measurable_comap_iff]
  simp +unfoldPartialApp only [Function.comp, Option.elim'_some]
  fun_prop

@[fun_prop]
lemma measurable_elim (g : C) {h : B → C} (hh : Measurable h) : Measurable (Option.elim · g h) := by
  have : (Option.elim · g h) = Sum.elim (fun _ ↦ g) h ∘ Option.elim' (Sum.inl ()) Sum.inr := by
    ext x
    cases x <;> rfl
  simp only [this]
  apply Measurable.comp ?_ (comap_measurable _)
  fun_prop

@[fun_prop]
lemma measurable_elim' (g : C) {h : B → C} (hh : Measurable h) : Measurable (Option.elim' g h) := by
  have : Option.elim' g h = (Option.elim · g h) := by
    ext x
    cases x <;> rfl
  simp only [this]
  fun_prop

@[simp, fun_prop]
lemma measurable_isSome : Measurable (fun x : Option A ↦ x.isSome) := by
  have (x : Option A) : x.isSome = x.elim false (fun _ ↦ true) := by
    cases x <;> rfl
  simp only [this]
  fun_prop

end MeasureTheory.Option
