import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_KatzLevelP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_IsLevelPStructure_isUnit_xP_sub_xQ.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_IsLevelPStructure_isUnit_xP_sub_xQ

set_option autoImplicit false

/--
@isnad1 id=isunit.2h4v.s6.87f3b01881f1 from=translated src=- shape=ed883e33 vocab=79f72447
-/
theorem solution
    {T : Type*} [CommRing T] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve T) (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    IsUnit (D.xP - D.xQ) := by
  have h1 : 1 ∈ Finset.Icc 1 ((ℓ - 1) / 2) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hdvd : (D.xQ * (W.ΨSq ((1 : ℕ) : ℤ)).eval D.xP - (W.Φ ((1 : ℕ) : ℤ)).eval D.xP) ∣
      ModularCurve.indepElt W ℓ D.xP D.xQ :=
    Finset.dvd_prod_of_mem (fun a : ℕ => D.xQ * (W.ΨSq a).eval D.xP - (W.Φ a).eval D.xP) h1
  have hu := isUnit_of_dvd_unit hdvd hD.isUnit_indepElt_PQ
  simp only [Nat.cast_one, WeierstrassCurve.ΨSq_one, WeierstrassCurve.Φ_one, Polynomial.eval_one,
    Polynomial.eval_X, mul_one] at hu
  rw [← neg_sub]
  exact hu.neg

