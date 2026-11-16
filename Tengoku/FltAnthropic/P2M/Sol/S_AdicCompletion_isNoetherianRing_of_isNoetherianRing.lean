import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing

set_option autoImplicit false

universe u

namespace AdicCompletionNoetherian

open MvPolynomial MvPowerSeries

variable {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} (f : Fin n → R)

noncomputable abbrev XI : Ideal (MvPolynomial (Fin n) R) := MvPolynomial.idealOfVars (Fin n) R

noncomputable abbrev ev : MvPolynomial (Fin n) R →+* R := (MvPolynomial.aeval f).toRingHom

lemma map_XI_eq : Ideal.map (ev f) (XI) = Ideal.span (Set.range f) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp [ev]

variable (hf : Ideal.span (Set.range f) = I)
include hf

lemma XI_le_comap : (XI : Ideal (MvPolynomial (Fin n) R)) ≤ I.comap (ev f) := by
  rw [← Ideal.map_le_iff_le_comap, map_XI_eq, hf]

lemma XI_pow_le_comap (k : ℕ) :
    (XI : Ideal (MvPolynomial (Fin n) R)) ^ k ≤ (I ^ k).comap (ev f) :=
  (Ideal.pow_right_mono (XI_le_comap I f hf) k).trans (Ideal.le_comap_pow _ k)

noncomputable def phi (k : ℕ) : MvPowerSeries (Fin n) R →+* R ⧸ I ^ k :=
  (Ideal.quotientMap (I ^ k) (ev f) (XI_pow_le_comap I f hf k)).comp
    (MvPowerSeries.truncTotalAlgHom (Fin n) R k).toRingHom

lemma phi_apply (k : ℕ) (p : MvPowerSeries (Fin n) R) :
    phi I f hf k p = Ideal.Quotient.mk (I ^ k) (ev f (truncTotal k p)) := by
  simp [phi, Ideal.quotientMap_mk]

lemma phi_compat {k l : ℕ} (hkl : k ≤ l) :
    (Ideal.Quotient.factorPow I hkl).comp (phi I f hf l) = phi I f hf k := by
  ext p
  simp only [RingHom.coe_comp, Function.comp_apply, phi_apply, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact XI_pow_le_comap I f hf k
    (truncTotal_sub_truncTotal_mem_pow_idealOfVars hkl le_rfl _)

noncomputable def Phi : MvPowerSeries (Fin n) R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (fun k => phi I f hf k) (fun hkl => phi_compat I f hf hkl)

end AdicCompletionNoetherian
