import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups
import Tengoku.Seed.GroupTheory.Transfer
import Tengoku.Seed.Algebra.Module.Hom
import Tengoku.Seed.Data.ZMod.Units
import Tengoku.Seed.Algebra.BigOperators.GroupWithZero.Action

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CohCarrier

section TransferAdd

variable {G : Type*} [Group G] {K : Subgroup G} {C : Type*} [CommGroup C]

end TransferAdd

section Level

variable (M : ℕ)

/--
@isnad1 id=eq.0h2v.s9.9346628d0be2 from=translated src=- shape=51d4439d vocab=57b7694e
-/
theorem Gamma0_d_mul_a (γ : Gamma0 M) :
    ((γ.1 1 1 : ℤ) : ZMod M) * ((γ.1 0 0 : ℤ) : ZMod M) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ.1
  rw [Matrix.det_fin_two] at hdet
  have hc : ((γ.1 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ.2
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at h
  rw [mul_comm]
  exact h

def gamma0Units : Gamma0 M →* (ZMod M)ˣ where
  toFun γ :=
    { val := Gamma0Map M γ
      inv := ((γ.1 0 0 : ℤ) : ZMod M)
      val_inv := Gamma0_d_mul_a M γ
      inv_val := by rw [mul_comm]; exact Gamma0_d_mul_a M γ }
  map_one' := by ext; simp
  map_mul' γ δ := by ext; exact map_mul (Gamma0Map M) γ δ

def GammaH (H : Subgroup (ZMod M)ˣ) : Subgroup SL(2, ℤ) :=
  (H.comap (gamma0Units M)).map (Gamma0 M).subtype

variable {M}

end Level

section Carrier

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type*) [AddCommGroup A]

end Carrier

section Operators

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

variable (A : Type*) [AddCommGroup A]

end Operators

section LevelMaps

variable (M M' : ℕ) (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ) (d : ℕ)

variable {M M' H H' d}

variable (M M' H H' d)

variable (A : Type*) [AddCommGroup A]

end LevelMaps

end CohCarrier
