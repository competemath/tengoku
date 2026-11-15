import Tengoku.Seed.LinearAlgebra.Matrix.SpecialLinearGroup
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Ihara

open Matrix

open scoped MatrixGroups

section CongruenceQuotient

variable (N M : ℕ)

def Gamma0Fin : Subgroup SL(2, ZMod M) where
  carrier := {g | (N : ZMod M) ∣ g 1 0}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul] at ha hb ⊢
    rw [(Matrix.two_mul_expl a.1 b.1).2.2.1]
    exact dvd_add (ha.mul_right _) (hb.mul_left _)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact dvd_neg.mpr ha

variable {N M}

/--
@isnad1 id=iff.0h3v.s8.6cc03b2800b8 from=translated src=- shape=e0ca6b72 vocab=61fdf3c0
-/
theorem mem_Gamma0Fin {g : SL(2, ZMod M)} : g ∈ Gamma0Fin N M ↔ (N : ZMod M) ∣ g 1 0 := Iff.rfl

variable (N M)

/--
@isnad1 id=eq.1h3v.s9.56ba734f95f9 from=translated src=- shape=429a60f9 vocab=883fca5e
-/
theorem castHom_apply_one_zero (hNM : N ∣ M) (g : Gamma0Fin N M) :
    ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 0) = 0 := by
  obtain ⟨r, hr⟩ := g.2
  rw [hr, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

def gamma0FinMap (hNM : N ∣ M) : Gamma0Fin N M →* ZMod N where
  toFun g := ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1)
  map_one' := by
    have h : ((1 : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 = 1 := rfl
    rw [h, map_one]
  map_mul' a b := by
    have h : ((a * b : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 =
        (a : SL(2, ZMod M)) 1 0 * (b : SL(2, ZMod M)) 0 1 +
          (a : SL(2, ZMod M)) 1 1 * (b : SL(2, ZMod M)) 1 1 :=
      (Matrix.two_mul_expl (a : SL(2, ZMod M)).1 (b : SL(2, ZMod M)).1).2.2.2
    rw [h, map_add, map_mul, map_mul, castHom_apply_one_zero N M hNM a, zero_mul, zero_add]

/--
@isnad1 id=eq.1h3v.s11.ce378890034e from=translated src=- shape=ab435481 vocab=0357d59d
-/
@[simp]
theorem gamma0FinMap_apply (hNM : N ∣ M) (g : Gamma0Fin N M) :
    gamma0FinMap N M hNM g = ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1) := rfl

def gamma0FinUnitsChar (hNM : N ∣ M) : Gamma0Fin N M →* (ZMod N)ˣ :=
  (gamma0FinMap N M hNM).toHomUnits

/--
@isnad1 id=eq.1h3v.s11.459b04b53b53 from=translated src=- shape=cc6876fb vocab=1f55980d
-/
@[simp]
theorem gamma0FinUnitsChar_coe (hNM : N ∣ M) (g : Gamma0Fin N M) :
    (gamma0FinUnitsChar N M hNM g : ZMod N) = ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1) :=
  rfl

end CongruenceQuotient

end Ihara
