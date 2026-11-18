import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Hecke.Family
import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.ResidueCharacter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

def Character.product (χ ψ : Character) : Character :=
  Character.ofResidue (χ.modulus ⊓ ψ.modulus)
    (Ideal.inf_ne_bot_of_ne_bot χ.modulus_ne_bot ψ.modulus_ne_bot)
    (ResidueCharacter.product χ.modulus ψ.modulus χ.residue ψ.residue)
    (ResidueCharacter.product_global_units _ _ _ _ χ.unit_trivial ψ.unit_trivial)

/--
@isnad1 id=eq.0h3v.s4.103edd460d42 from=translated src=- shape=46c14041 vocab=7903afcd
-/
theorem elementCoeff_product (χ ψ : Character) (z : O) :
    elementCoeff (χ.product ψ) z = elementCoeff χ z * elementCoeff ψ z :=
  ResidueCharacter.product_mk _ _ _ _ z

def Character.inverse (χ : Character) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue⁻¹
  unit_trivial u := by simp [MulChar.inv_apply_eq_inv', χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

/--
@isnad1 id=eq.0h2v.s4.e616b7c5606b from=translated src=- shape=6f752268 vocab=e2b9ff2b
-/
theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

def Character.power (χ : Character) (n : ℕ) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue ^ n
  unit_trivial u := by
    let v := Units.map (Ideal.Quotient.mk χ.modulus).toMonoidHom u
    change (χ.residue ^ n) (v : O ⧸ χ.modulus) = 1
    rw [MulChar.pow_apply_coe]
    change χ.residue (Ideal.Quotient.mk χ.modulus u) ^ n = 1
    simp [χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

/--
@isnad1 id=eq.1h3v.s8.f29e50f43d07 from=translated src=- shape=536744ef vocab=b391984e
-/
theorem elementCoeff_power_of_unit (χ : Character) (n : ℕ) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk χ.modulus z)) :
    elementCoeff (χ.power n) z = elementCoeff χ z ^ n := by
  change (χ.residue ^ n) (Ideal.Quotient.mk χ.modulus z) = _
  obtain ⟨u, hu⟩ := hz
  rw [← hu, MulChar.pow_apply_coe, hu]
  rfl

end SevenEighths.HeckeFamily

end

end OAI
