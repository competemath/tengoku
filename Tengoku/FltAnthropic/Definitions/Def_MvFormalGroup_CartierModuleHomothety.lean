import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_CartierModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

noncomputable section

universe u

namespace Tengoku.FltAnthropic.MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

def teichFam (a : R) : ℕ → MvPowerSeries ℕ R := fun n => (a ^ p ^ n) • X n

variable {p}

omit hp in
/--
@isnad1 id=eq.0h4v.s6.a2046c7acba1 from=translated src=- shape=4bdd84ab vocab=af88e140
-/
@[simp] theorem teichFam_apply (a : R) (n : ℕ) : teichFam p a n = (a ^ p ^ n) • X n := rfl

omit hp in
/--
@isnad1 id=eq.0h4v.s6.9888d922e4c2 from=translated src=- shape=fad0cebe vocab=33bfe44c
-/
theorem constantCoeff_teichFam (a : R) (n : ℕ) : (teichFam p a n).constantCoeff = 0 := by
  rw [teichFam_apply, smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]

omit hp in
/--
@isnad1 id=hassubst.0h3v.s4.5d9b354ecc1b from=translated src=- shape=aacfbd2f vocab=22b22f86
-/
theorem hasSubst_teichFam (a : R) : HasSubst (teichFam p a) := HasSubst.smul_X _

omit hp in

/--
@isnad1 id=eq.0h3v.s8.f11292b3ab6f from=translated src=- shape=bf2591ac vocab=8336cb84
-/
theorem pairFam_teichFam (a : R) :
    pairFam (teichFam p a) = (fun im : Fin 2 × ℕ => a ^ p ^ im.2) • X := by
  funext ⟨i, m⟩
  rw [pairFam_apply, teichFam_apply, subst_smul (hasSubst_blk i), subst_X (hasSubst_blk i)]
  rfl

/--
@isnad1 id=isendo.0h3v.s4.f765f03da494 from=translated src=- shape=987540c4 vocab=57a7155f
-/
theorem isEndo_teichFam (a : R) : IsEndo p (teichFam p a) := by
  refine ⟨hasSubst_teichFam a, constantCoeff_teichFam a, fun n => ?_⟩
  rw [teichFam_apply, subst_smul (hasSubst_addFam p R), subst_X (hasSubst_addFam p R),
    pairFam_teichFam, ← rescale_eq_subst]
  ext e
  rw [coeff_smul, coeff_rescale]
  by_cases he : coeff e (addFam p R n) = 0
  · rw [he, mul_zero, mul_zero]
  · congr 1
    rw [← weight_eq_of_coeff_addFam_ne_zero p R he, Finsupp.weight_apply, Finsupp.prod,
      Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun im _ => ?_
    rw [← pow_mul, weight_apply, one_mul, smul_eq_mul, mul_comm]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

def homothety [Φ.IsComm] (a : R) : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_teichFam a)

/--
@isnad1 id=eq.0h6v.s8.b887eadc0d0a from=translated src=- shape=e5a7b305 vocab=6d9c99a1
-/
@[simp] theorem toPowerSeries_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    (homothety a f).toPowerSeries = fun j => subst (WittLaw.teichFam p a) (f.toPowerSeries j) := rfl

namespace Examples

end Examples

end CartierModule

end Tengoku.FltAnthropic.MvFormalGroup

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
