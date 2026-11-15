import Tengoku.FltAnthropic.Definitions.Def_RatIdele_Normalizer
import Tengoku.Seed.NumberTheory.Padics.RingHoms
import Tengoku.Seed.NumberTheory.DirichletCharacter.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Rat.HeightOneSpectrum NumberField.AdelicLevel

namespace RatIdele

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

section Residue

def unitPadicAt (p : ℕ) [hp : Fact p.Prime] (x : (𝔸ℚ)ˣ) : ℤ_[p] :=
  (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, hp.out⟩).symm.toAlgEquiv.toRingEquiv
    (unitIntAt ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x)

theorem unitPadicAt_mul (p : ℕ) [Fact p.Prime] (x y : (𝔸ℚ)ˣ) :
    unitPadicAt p (x * y) = unitPadicAt p x * unitPadicAt p y := by
  unfold unitPadicAt
  rw [unitIntAt_mul, map_mul]

theorem unitPadicAt_one (p : ℕ) [Fact p.Prime] : unitPadicAt p 1 = 1 := by
  unfold unitPadicAt
  rw [unitIntAt_one, map_one]

theorem natCast_mul_unitPadicAt_eq_one (p : ℕ) [hp : Fact p.Prime] {x : (𝔸ℚ)ˣ} {n : ℕ}
    (h : ((n : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩).adicCompletion ℚ)
      * unitAt ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x = 1) :
    ((n : ℕ) : ℤ_[p]) * unitPadicAt p x = 1 := by
  unfold unitPadicAt
  rw [← map_natCast (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, hp.out⟩).symm.toAlgEquiv.toRingEquiv n,
    ← map_mul, natCast_mul_unitIntAt_eq_one h, map_one]

theorem unitPadicAt_eq_neg_one (p : ℕ) [hp : Fact p.Prime] {x : (𝔸ℚ)ˣ}
    (h : unitAt ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x = -1) : unitPadicAt p x = -1 := by
  unfold unitPadicAt
  rw [show unitIntAt ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x = -1 from
    Subtype.ext (by rw [coe_unitIntAt, h, NegMemClass.coe_neg, OneMemClass.coe_one]), map_neg, map_one]

theorem fact_prime_of_mem_primeFactors {N : ℕ} (p : N.primeFactors) : Fact (p : ℕ).Prime :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

attribute [local instance] fact_prime_of_mem_primeFactors

variable (N : ℕ)

def unitResidues (x : (𝔸ℚ)ˣ) : (p : N.primeFactors) → ZMod ((p : ℕ) ^ N.factorization p) :=
  fun p => PadicInt.toZModPow (N.factorization p) (unitPadicAt p x)

theorem unitResidues_mul (x y : (𝔸ℚ)ˣ) : unitResidues N (x * y) = unitResidues N x * unitResidues N y := by
  funext p
  show PadicInt.toZModPow (N.factorization p) (unitPadicAt p (x * y))
    = PadicInt.toZModPow (N.factorization p) (unitPadicAt p x)
      * PadicInt.toZModPow (N.factorization p) (unitPadicAt p y)
  rw [unitPadicAt_mul, map_mul]

theorem unitResidues_one : unitResidues N 1 = 1 := by
  funext p
  show PadicInt.toZModPow (N.factorization p) (unitPadicAt p 1) = 1
  rw [unitPadicAt_one, map_one]

variable [NeZero N]

def unitResidue : (𝔸ℚ)ˣ →* ZMod N where
  toFun x := (ZMod.equivPi N (NeZero.ne N)).symm (unitResidues N x)
  map_one' := by rw [unitResidues_one, map_one]
  map_mul' x y := by rw [unitResidues_mul, map_mul]

theorem unitResidue_apply (x : (𝔸ℚ)ˣ) : unitResidue N x = (ZMod.equivPi N (NeZero.ne N)).symm (unitResidues N x) := rfl

theorem equivPi_unitResidue (x : (𝔸ℚ)ˣ) : ZMod.equivPi N (NeZero.ne N) (unitResidue N x) = unitResidues N x := by
  rw [unitResidue_apply, RingEquiv.apply_symm_apply]

end Residue

end RatIdele

namespace DirichletCharacter

open RatIdele

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

def dirichletIdeleChar : (𝔸ℚ)ˣ →* ℂˣ :=
  (χ.toUnitHom.comp (unitResidue N).toHomUnits)⁻¹

theorem coe_dirichletIdeleChar_apply (x : (𝔸ℚ)ˣ) :
    ((dirichletIdeleChar χ x : ℂˣ) : ℂ) = (χ (unitResidue N x))⁻¹ := by
  rw [dirichletIdeleChar, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
    MonoidHom.coe_toHomUnits]

theorem dirichletIdeleChar_eq_one_of_unitResidue_eq_one {x : (𝔸ℚ)ˣ} (h : unitResidue N x = 1) :
    dirichletIdeleChar χ x = 1 := by
  refine Units.ext ?_
  rw [coe_dirichletIdeleChar_apply, h, map_one, inv_one, Units.val_one]

theorem norm_coe_dirichletIdeleChar_apply (x : (𝔸ℚ)ˣ) : ‖((dirichletIdeleChar χ x : ℂˣ) : ℂ)‖ = 1 := by
  rw [coe_dirichletIdeleChar_apply, norm_inv, ← MonoidHom.coe_toHomUnits (unitResidue N) x, χ.unit_norm_eq_one,
    inv_one]

end DirichletCharacter

end
