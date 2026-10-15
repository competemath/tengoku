/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic

/-!
# LeanPool.QuasiBorelSpaces.ENNReal

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.ENNReal`.
-/

@[expose] public section

namespace QuasiBorelSpace.ENNReal

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} [Countable B]

/--
@isnad1 id=ishom.2h4v.s5.c35adc8651e9 from=translated src=- shape=11826004 vocab=9c7c8588
-/
@[fun_prop]
lemma isHom_add
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    : IsHom (fun x ↦ f x + g x) := by
  rw [isHom_def] at ⊢ hf hg
  intro φ hφ
  specialize hg hφ
  specialize hf hφ
  simp only [isHom_ofMeasurableSpace] at ⊢ hg hf
  exact Measurable.add hf hg

/--
@isnad1 id=ishom.2h4v.s5.cf447c1b40fb from=translated src=- shape=11826004 vocab=2c5f25aa
-/
@[fun_prop]
lemma isHom_mul
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    : IsHom (fun x ↦ f x * g x) := by
  rw [isHom_def] at ⊢ hf hg
  intro φ hφ
  specialize hg hφ
  specialize hf hφ
  simp only [isHom_ofMeasurableSpace] at ⊢ hg hf
  exact Measurable.mul hf hg

/--
@isnad1 id=ishom.1h4v.s5.98e8d652cc5e from=translated src=- shape=fc8654cd vocab=23f485a1
-/
@[fun_prop]
lemma isHom_iSup {f : A → B → ENNReal} (hf : ∀ b, IsHom (f · b)) : IsHom fun x ↦ ⨆i, f x i := by
  rw [isHom_def]
  intro φ hφ
  apply isHom_of_measurable
  apply Measurable.iSup fun b ↦ ?_
  apply measurable_of_isHom
  fun_prop

end QuasiBorelSpace.ENNReal

namespace OmegaQuasiBorelSpace.ENNReal

open QuasiBorelSpace

/-- ωQBS structure on `ENNReal` -/
noncomputable instance : OmegaQuasiBorelSpace ENNReal where
  isHom_ωSup := by
    change IsHom fun c : OmegaCompletePartialOrder.Chain ENNReal ↦ ⨆ n, c n
    fun_prop

end OmegaQuasiBorelSpace.ENNReal
