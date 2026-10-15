/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic

/-!
# Small Products of Quasi-Borel Spaces

This file defines small products of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· → ·` type.

See [HeunenKSY17], Proposition 16.
-/

@[expose] public section

namespace QuasiBorelSpace.Pi

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}
  {I : Type*} {P : I → Type*} {_ : ∀ i, QuasiBorelSpace (P i)}

instance [∀ i, QuasiBorelSpace (P i)] : QuasiBorelSpace (∀i : I, P i) where
  IsVar φ := ∀ i, IsHom (φ · i)
  isVar_const f i := by simp only [isHom_const']
  isVar_comp hf hφ i := by
    rw [←isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' hix hφ i := by
    exact isHom_cases (by simp only [isHom_ofMeasurableSpace, hix]) (hφ · i)

/--
@isnad1 id=iff.0h4v.s5.94615f63d6ac from=translated src=- shape=1b16c2c6 vocab=45ea852a
-/
@[local simp]
lemma isHom_def (φ : ℝ → ∀ i, P i) : IsHom φ ↔ ∀ i, IsHom (φ · i) := by
  rw [←isVar_iff_isHom]
  rfl

/--
@isnad1 id=ishom.0h4v.s5.5cbaf89286fc from=translated src=- shape=a9f7658e vocab=3fa53d2d
-/
@[fun_prop]
lemma isHom_apply (i : I) : IsHom (fun (f : (i : I) → P i) ↦ f i) := by
  rw [QuasiBorelSpace.isHom_def]
  simp_all

/--
@isnad1 id=ishom.1h6v.s5.0a2294c7f5bb from=translated src=- shape=9cc5cda7 vocab=3fa53d2d
-/
@[fun_prop]
lemma isHom_pi {f : A → ∀ i, P i} (hf : ∀ i, IsHom (f · i)) : IsHom f := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  fun_prop

/--
@isnad1 id=iff.0h6v.s5.0603d5d68257 from=translated src=- shape=07b1ddd5 vocab=3fa53d2d
-/
@[simp]
lemma isHom_iff {f : A → (i : I) → P i} : IsHom f ↔ ∀i, IsHom (f · i) := by
  apply Iff.intro
  · fun_prop
  · exact isHom_pi

/--
@isnad1 id=ishom.0h4v.s5.be7d8b995b5b from=translated src=- shape=639edbfb vocab=c9508439
-/
@[simp, fun_prop]
lemma isHom_eval (i) : IsHom (Function.eval i : (∀ i, P i) → P i) := by
  unfold Function.eval
  fun_prop

instance
    [∀ i, MeasurableSpace (P i)]
    [∀ i, MeasurableQuasiBorelSpace (P i)]
    : MeasurableQuasiBorelSpace (∀i, P i) where
  isHom_iff_measurable φ := by
    apply Iff.intro <;>
    · simp only [isHom_iff, isHom_iff_measurable]
      fun_prop

end QuasiBorelSpace.Pi

namespace OmegaQuasiBorelSpace.Pi

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {I : Type*} {P : I → Type*} [∀ i, OmegaQuasiBorelSpace (P i)]

instance : OmegaQuasiBorelSpace (∀i, P i) where
  isHom_ωSup := by
    simp only [ωSup, Pi.isHom_iff]
    intro i
    apply isHom_ωSup'
    simp only [
      Chain.isHom_iff, Chain.coe_map, Pi.evalOrderHom_coe,
      Function.comp_apply, Function.eval]
    fun_prop

end OmegaQuasiBorelSpace.Pi
