/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Tengoku.LeanPool.LeanPool.Kurosh.KuroshRawPathValue
public import Tengoku

/-!
# Kurosh Cover Action

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshCoverActionDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

theorem Internal.rightCosetMk_mul_out_mk {P : Type u} [Group P]
    (K : Subgroup P) (p r : P) :
    rightCosetMk K (p * Quotient.out (rightCosetMk K r)) =
      rightCosetMk K (p * r) := by
  have hc : rightCosetMk K (Quotient.out (rightCosetMk K r)) =
      rightCosetMk K r := Quotient.out_eq _
  rcases (rightCosetMk_eq_iff K _ _).1 hc with ⟨k, hk⟩
  apply (rightCosetMk_eq_iff K _ _).2
  refine ⟨k, ?_⟩
  calc
    p * Quotient.out (rightCosetMk K r) * (k : P) =
        p * (Quotient.out (rightCosetMk K r) * (k : P)) := by
          rw [mul_assoc]
    _ = p * r := by rw [hk]

end GraphCoveringTheory.Kurosh
