import Tengoku.FltAnthropic.Definitions.Def_Gamma0Away
import Tengoku.FltAnthropic.Definitions.Def_Gamma0UnitsChar
import Tengoku.FltAnthropic.Definitions.Def_IharaAmalgamMap
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Ihara

open Matrix

open scoped MatrixGroups

variable (N q : ℕ)

/--
@isnad1 id=isunit.1h2v.s5.f870f9481c8f from=translated src=- shape=a6d0bedf vocab=668be4be
-/
theorem isUnit_intCast_q (hNq : Nat.Coprime N q) : IsUnit (((q : ℤ) : ZMod N)) := by
  have h : ((ZMod.unitOfCoprime q hNq.symm : (ZMod N)ˣ) : ZMod N) = (((q : ℤ)) : ZMod N) := by
    rw [ZMod.coe_unitOfCoprime, Int.cast_natCast]
  exact h ▸ (ZMod.unitOfCoprime q hNq.symm).isUnit

noncomputable def zAwayToZMod (hNq : Nat.Coprime N q) : ZAway q →+* ZMod N :=
  IsLocalization.Away.lift (S := ZAway q) (g := Int.castRingHom (ZMod N)) (q : ℤ)
    (by rw [eq_intCast]; exact isUnit_intCast_q N q hNq)

/--
@isnad1 id=eq.1h3v.s8.08484a68b780 from=translated src=- shape=a7009726 vocab=9e8f5314
-/
@[simp]
theorem zAwayToZMod_algebraMap (hNq : Nat.Coprime N q) (a : ℤ) :
    zAwayToZMod N q hNq (algebraMap ℤ (ZAway q) a) = (a : ZMod N) := by
  rw [zAwayToZMod, IsLocalization.Away.lift_eq, eq_intCast]

/--
@isnad1 id=eq.1h2v.s7.70c6f60e6afa from=translated src=- shape=60d12504 vocab=4ed29395
-/
theorem zAwayToZMod_natCast_self (hNq : Nat.Coprime N q) :
    zAwayToZMod N q hNq (N : ZAway q) = 0 := by
  have h : ((N : ℕ) : ZAway q) = algebraMap ℤ (ZAway q) ((N : ℕ) : ℤ) := by simp
  rw [h, zAwayToZMod_algebraMap, Int.cast_natCast, ZMod.natCast_self]

/--
@isnad1 id=eq.1h3v.s10.ebdec38d99d6 from=translated src=- shape=f8236357 vocab=d599ba66
-/
theorem zAwayToZMod_apply_one_zero (hNq : Nat.Coprime N q) (g : Gamma0Away N q) :
    zAwayToZMod N q hNq ((g : SL(2, ZAway q)) 1 0) = 0 := by
  obtain ⟨r, hr⟩ := g.2
  rw [hr, map_mul, zAwayToZMod_natCast_self, zero_mul]

noncomputable def gamma0AwayMap (hNq : Nat.Coprime N q) : Gamma0Away N q →* ZMod N where
  toFun g := zAwayToZMod N q hNq ((g : SL(2, ZAway q)) 1 1)
  map_one' := by
    have h : ((1 : Gamma0Away N q) : SL(2, ZAway q)) 1 1 = 1 := rfl
    rw [h, map_one]
  map_mul' a b := by
    have h : ((a * b : Gamma0Away N q) : SL(2, ZAway q)) 1 1
        = (a : SL(2, ZAway q)) 1 0 * (b : SL(2, ZAway q)) 0 1
          + (a : SL(2, ZAway q)) 1 1 * (b : SL(2, ZAway q)) 1 1 :=
      (Matrix.two_mul_expl (a : SL(2, ZAway q)).1 (b : SL(2, ZAway q)).1).2.2.2
    rw [h, map_add, map_mul, map_mul, zAwayToZMod_apply_one_zero N q hNq a, zero_mul,
      zero_add]

noncomputable def gamma0AwayUnitsChar (hNq : Nat.Coprime N q) :
    Gamma0Away N q →* (ZMod N)ˣ :=
  (gamma0AwayMap N q hNq).toHomUnits

/--
@isnad1 id=eq.1h3v.s13.468342be788c from=translated src=- shape=48933c74 vocab=8eec6722
-/
@[simp]
theorem gamma0AwayUnitsChar_coe (hNq : Nat.Coprime N q) (g : Gamma0Away N q) :
    (gamma0AwayUnitsChar N q hNq g : ZMod N) = gamma0AwayMap N q hNq g :=
  rfl

noncomputable def vertexZeroAway : CongruenceSubgroup.Gamma0 N →* Gamma0Away N q :=
  (vertexZero N q).codRestrict (Gamma0Away N q) (vertexZero_mem N q)

noncomputable def vertexOneAway : CongruenceSubgroup.Gamma0 N →* Gamma0Away N q :=
  (vertexOne N q).codRestrict (Gamma0Away N q) (vertexOne_mem N q)

/--
@isnad1 id=eq.1h2v.s12.73057325b57d from=translated src=- shape=16ebef77 vocab=c79566da
-/
theorem gamma0AwayUnitsChar_comp_vertexZeroAway (hNq : Nat.Coprime N q) :
    (gamma0AwayUnitsChar N q hNq).comp (vertexZeroAway N q) = gamma0UnitsHom N := by
  ext g
  show zAwayToZMod N q hNq ((vertexZero N q g : SL(2, ZAway q)) 1 1)
      = CongruenceSubgroup.Gamma0Map N g
  have h : (vertexZero N q g : SL(2, ZAway q)) 1 1
      = algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1) := rfl
  rw [h, zAwayToZMod_algebraMap]
  rfl

/--
@isnad1 id=eq.1h2v.s12.6e06da2013f6 from=translated src=- shape=16ebef77 vocab=11d667b2
-/
theorem gamma0AwayUnitsChar_comp_vertexOneAway (hNq : Nat.Coprime N q) :
    (gamma0AwayUnitsChar N q hNq).comp (vertexOneAway N q) = gamma0UnitsHom N := by
  ext g
  show zAwayToZMod N q hNq ((vertexOne N q g : SL(2, ZAway q)) 1 1)
      = CongruenceSubgroup.Gamma0Map N g
  have h : (vertexOne N q g : SL(2, ZAway q)) 1 1
      = algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1) := by
    rw [coe_vertexOne_eq]
    rfl
  rw [h, zAwayToZMod_algebraMap]
  rfl

end Ihara
