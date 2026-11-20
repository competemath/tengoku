/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.DerivedResidual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

structure Derived45Iso {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (E : Derived45 P) (F : Derived45 Q) where

  point : P ≃ Q

  index : Equiv.Perm (Fin 45)

  map_block : ∀ i, (E.block i).image point = F.block (index i)

namespace Derived45Iso

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {E : Derived45 P} {F : Derived45 Q}

theorem block_eq_image (iso : Derived45Iso E F) (i : Fin 45) :
    F.block i = (E.block (iso.index.symm i)).image iso.point := by
  rw [iso.map_block, Equiv.apply_symm_apply]

end Derived45Iso

namespace Residual165

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {E : Derived45 P} {F : Derived45 Q}

def transport (iso : Derived45Iso E F) (R : Residual165 E) : Residual165 F where
  res n := (R.res n).image iso.point
  res_card n := by
    rw [Finset.card_image_of_injective _ iso.point.injective, R.res_card]
  res_meet m n hmn := by
    rw [← Finset.image_inter _ _ iso.point.injective,
      Finset.card_image_of_injective _ iso.point.injective]
    exact R.res_meet m n hmn
  cross_meet i n := by
    rw [iso.block_eq_image i, ← Finset.image_inter _ _ iso.point.injective,
      Finset.card_image_of_injective _ iso.point.injective]
    exact R.cross_meet _ n
  res_rep q := by
    classical
    have hset : (Finset.univ.filter fun n => q ∈ (R.res n).image iso.point) =
        Finset.univ.filter fun n => iso.point.symm q ∈ R.res n := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        simpa using hp
      · intro h
        exact ⟨iso.point.symm q, h, by simp⟩
    rw [hset, R.res_rep]
  res_inj m n hmn := by
    refine R.res_inj ?_
    have h := congrArg (Finset.image iso.point.symm) hmn
    simpa [Finset.image_image] using h

end Residual165

theorem isEmpty_residual165_of_iso {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] {E : Derived45 P} {F : Derived45 Q}
    (iso : Derived45Iso E F) (h : IsEmpty (Residual165 F)) : IsEmpty (Residual165 E) :=
  ⟨fun R => h.elim (R.transport iso)⟩

end SRG266.QuasiSymmetric
