/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
module

public import Tengoku

/-!
# LeanPool.LowDimSolvClassification.QuotientSolvable
-/

@[expose] public section

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A reformulation of `LieIdeal.comap_incl_eq_bot` under the additional hypothesis `J ≤ I`.
@isnad1 id=iff.1h4v.s9.b322cefa8634 from=translated src=- shape=26750ef4 vocab=0ac43c2c
-/
theorem comap_incl_eq_bot_of_le {I J : LieIdeal R L} (h : J ≤ I) :
    comap I.incl J = ⊥ ↔ J = ⊥ := by
  rw [comap_incl_eq_bot, disjoint_iff, inf_of_le_right h]

end LieIdeal

namespace LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- TODO. -/
def _root_.LieAlgebra.Quotient.mk' (I : LieIdeal R L) : L →ₗ⁅R⁆ L ⧸ I := {
  toFun := LieSubmodule.Quotient.mk (N := I)
  map_add' := by simp only [Submodule.Quotient.mk_add, implies_true]
  map_smul' := by simp only [Submodule.Quotient.mk_smul, RingHom.id_apply, implies_true]
  map_lie' := by simp only [LieSubmodule.Quotient.mk_bracket, implies_true]
}

/--
@isnad1 id=surjecti.0h3v.s7.76d5f554735b from=translated src=- shape=fa655038 vocab=8ec2bd0e
-/
theorem surjective_mk' (I : LieIdeal R L) : Function.Surjective (Quotient.mk' I)
    := Quot.mk_surjective

/--
@isnad1 id=issolvab.2h3v.s6.bf34db442ada from=translated src=- shape=00b97c42 vocab=ed8cd38e
-/
theorem solvable_of_ideal_and_quot_solvable {I : LieIdeal R L} (quotsol : LieAlgebra.IsSolvable
    (L ⧸ I))
     (Isol : LieAlgebra.IsSolvable I) :
    LieAlgebra.IsSolvable L := by
  rw [LieAlgebra.isSolvable_iff R] at *
  obtain ⟨k₁, hk₁⟩ := quotsol
  obtain ⟨k₂, hk₂⟩ := Isol
  use k₂ + k₁
  have : derivedSeries R L k₁ ≤ I := by
    rw [← LieIdeal.derivedSeries_map_eq k₁ (surjective_mk' I), eq_bot_iff, LieIdeal.map_le] at hk₁
    intro x hx
    rw [← LieSubmodule.Quotient.mk_eq_zero']
    apply hk₁
    use x, hx
    rfl
  rw [derivedSeries_def, derivedSeriesOfIdeal_add, ← derivedSeries_def R L k₁, eq_bot_iff]
  have h₁ : derivedSeriesOfIdeal R L k₂ (derivedSeries R L k₁) ≤ derivedSeriesOfIdeal R L k₂ I := by
    apply derivedSeriesOfIdeal_le this
    apply le_refl
  rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap,
    LieIdeal.comap_incl_eq_bot_of_le (derivedSeriesOfIdeal_le_self I k₂)] at hk₂
  simp_all

end LieAlgebra
