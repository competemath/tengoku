import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace Tengoku.FltAnthropic.MvFormalGroup

variable {n : ℕ} {R : Type*} [CommRing R]

def addCoboundary (F : MvFormalGroup n R) (g : MvPowerSeries (Fin n) R) :
    MvPowerSeries (Fin n ⊕ Fin n) R :=
  subst F.toPowerSeries g
    - subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R)) g
    - subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) R)) g

structure IsSymmTwoCocycle (F : MvFormalGroup n R) (Γ : MvPowerSeries (Fin n ⊕ Fin n) R) : Prop where

  constantCoeff_eq_zero : Γ.constantCoeff = 0

  symm :
    subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) R))
        fun j => X (Sum.inl j))
      Γ = Γ

  cocycle :
    subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
              fun l => X (Sum.inr (Sum.inl l)))
            (F.toPowerSeries j))
          fun j => X (Sum.inr (Sum.inr j)))
        Γ
      + subst
        (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun l => X (Sum.inr (Sum.inl l)))
        Γ
      =
    subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
              fun l => X (Sum.inr (Sum.inr l)))
            (F.toPowerSeries j))
        Γ
      + subst
        (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun l => X (Sum.inr (Sum.inr l)))
        Γ

/--
@isnad1 id=eq.1h4v.s6.29410a64e58d from=translated src=- shape=537c16ee vocab=ff478025
-/
theorem subst_zero_of_hasSubst {σ τ : Type*} {a : σ → MvPowerSeries τ R} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← coe_substAlgHom ha, map_zero]

/--
@isnad1 id=issymmtw.0h3v.s5.bb98705bad89 from=translated src=- shape=ee104113 vocab=f0829640
-/
theorem IsSymmTwoCocycle.zero (F : MvFormalGroup n R) : F.IsSymmTwoCocycle 0 where
  constantCoeff_eq_zero := map_zero _
  symm := subst_zero_of_hasSubst (hasSubst_of_constantCoeff_zero (by
      rintro (j | j) <;> exact constantCoeff_X _))
  cocycle := by
    have h1 : HasSubst (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
            fun l => X (Sum.inr (Sum.inl l)))
          (F.toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _))
          (by rintro (l | l) <;> exact constantCoeff_X _) (F.constantCoeff_eq_zero j)
      · exact constantCoeff_X _
    have h2 : HasSubst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
        fun l => X (Sum.inr (Sum.inl l))) :=
      hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)
    have h3 : HasSubst (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
            fun l => X (Sum.inr (Sum.inr l)))
          (F.toPowerSeries j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _))
          (by rintro (l | l) <;> exact constantCoeff_X _) (F.constantCoeff_eq_zero j)
    have h4 : HasSubst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
        fun l => X (Sum.inr (Sum.inr l))) :=
      hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)
    rw [subst_zero_of_hasSubst h1, subst_zero_of_hasSubst h2, subst_zero_of_hasSubst h3,
      subst_zero_of_hasSubst h4]

end Tengoku.FltAnthropic.MvFormalGroup

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
