import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

noncomputable def gamma0NebenChar (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ) :
    Gamma0 M →* κ :=
  (powMonoidHom e).comp
    ((ZMod.castHom (dvd_refl p) κ).toMonoidHom.comp
      ((ZMod.castHom hpM (ZMod p)).toMonoidHom.comp (Gamma0Map M)))

/--
@isnad1 id=eq.1h5v.s11.712a76bbae09 from=translated src=- shape=81787db6 vocab=a76ae30b
-/
theorem gamma0NebenChar_apply (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ)
    (γ : Gamma0 M) :
    gamma0NebenChar p M hpM κ e γ =
      (ZMod.castHom (dvd_refl p) κ (ZMod.castHom hpM (ZMod p) (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M))) ^ e :=
  rfl

noncomputable def gamma0NebenRep (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ) :
    Representation κ (Gamma0 M) κ :=
  (DistribMulAction.toModuleEnd κ κ).comp (gamma0NebenChar p M hpM κ e)

/--
@isnad1 id=eq.1h6v.s12.896b8908b717 from=translated src=- shape=c9bdc4b3 vocab=22fc965b
-/
@[simp]
theorem gamma0NebenRep_apply (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ)
    (γ : Gamma0 M) (v : κ) :
    gamma0NebenRep p M hpM κ e γ v = gamma0NebenChar p M hpM κ e γ * v :=
  rfl

/--
@isnad1 id=eq.1h3v.s11.3cd1fb65fe5d from=translated src=- shape=33b2765d vocab=580bb055
-/
theorem gamma0NebenRep_zero (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] :
    gamma0NebenRep p M hpM κ 0 = 1 := by
  refine MonoidHom.ext fun γ => LinearMap.ext fun v => ?_
  simp [gamma0NebenChar]

end HeckeEis
