import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Ihara

def gamma0UnitsHom (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

/--
@isnad1 id=eq.0h2v.s12.d336b2751d3e from=translated src=- shape=f82cfa18 vocab=544bfd5c
-/
@[simp]
theorem gamma0UnitsHom_coe (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    (gamma0UnitsHom N g : ZMod N) = CongruenceSubgroup.Gamma0Map N g :=
  rfl

def gamma0UnitsChar (N : ℕ) :
    Additive (CongruenceSubgroup.Gamma0 N) →+ Additive (ZMod N)ˣ :=
  MonoidHom.toAdditive (gamma0UnitsHom N)

/--
@isnad1 id=eq.0h2v.s13.70fec9553b3e from=translated src=- shape=460d7df7 vocab=bd8e6296
-/
@[simp]
theorem gamma0UnitsChar_apply (N : ℕ) (g : Additive (CongruenceSubgroup.Gamma0 N)) :
    gamma0UnitsChar N g = Additive.ofMul (gamma0UnitsHom N g.toMul) :=
  rfl

end Ihara
