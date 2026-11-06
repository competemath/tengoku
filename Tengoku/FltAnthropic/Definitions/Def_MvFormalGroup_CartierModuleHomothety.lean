import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_CartierModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

def teichFam (a : R) : ℕ → MvPowerSeries ℕ R := fun n => (a ^ p ^ n) • X n

variable {p}

omit hp in
@[simp] theorem teichFam_apply (a : R) (n : ℕ) : teichFam p a n = (a ^ p ^ n) • X n := rfl

omit hp in
theorem constantCoeff_teichFam (a : R) (n : ℕ) : (teichFam p a n).constantCoeff = 0 := by
  rw [teichFam_apply, smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]

omit hp in
theorem hasSubst_teichFam (a : R) : HasSubst (teichFam p a) := HasSubst.smul_X _

omit hp in

theorem pairFam_teichFam (a : R) :
    pairFam (teichFam p a) = (fun im : Fin 2 × ℕ => a ^ p ^ im.2) • X := by
  funext ⟨i, m⟩
  rw [pairFam_apply, teichFam_apply, subst_smul (hasSubst_blk i), subst_X (hasSubst_blk i)]
  rfl

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

@[simp] theorem toPowerSeries_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    (homothety a f).toPowerSeries = fun j => subst (WittLaw.teichFam p a) (f.toPowerSeries j) := rfl

namespace Examples

end Examples

end CartierModule

end MvFormalGroup

end
