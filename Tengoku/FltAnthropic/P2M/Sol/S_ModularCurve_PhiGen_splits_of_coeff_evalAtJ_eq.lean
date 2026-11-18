import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq

noncomputable section

open Polynomial

namespace ModularCurve
export _root_.ModularCurve (qExpand evalAtJ ModularPolynomialData coeffEmb)
open _root_.ModularCurve
namespace PhiGen
export _root_.ModularCurve.PhiGen (conj phiProd PhiGenDescends)
open _root_.ModularCurve.PhiGen

section Splitting

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
variable (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ}

private theorem splits_of_coeff_evalAtJ_eq (hc : PhiGenDescends ℓ ζ c)
    (data : ModularPolynomialData ℓ)
    (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := by
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map, RingHom.comp_apply, RingHom.comp_apply, hcoeff k, hc k]

end Splitting

end PhiGen
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.ModularCurve _root_.ModularCurve.PhiGen _root_.P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.ModularCurve.PhiGen in

theorem solution {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) :=
  ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq ζ hc data hcoeff

