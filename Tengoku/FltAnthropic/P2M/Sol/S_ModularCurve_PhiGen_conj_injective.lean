import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms ModularCurve.PhiGen.conj_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_PhiGen_conj_injective.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_PhiGen_conj_injective

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve
export _root_.ModularCurve (qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeff_jq_neg_one qTwist_coeff cosetSubst coeffEmb coeffEmb_coeff)
open _root_.ModularCurve
namespace PhiGen
export _root_.ModularCurve.PhiGen (cosetA conj conj_zero conj_succ)
open _root_.ModularCurve.PhiGen

section CoeffEmbJq

variable (K : Type*) [Field K] [Algebra ℚ K]

private theorem coeff_coeffEmb_jq_neg_one : (coeffEmb K jq).coeff (-1 : ℤ) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

end CoeffEmbJq

/--
@isnad1 id=eq.0h3v.s6.54a2fe437ef8 from=translated src=- shape=dac1777f vocab=c9eba9e6
-/
theorem conj_zero_coeff_neg_one {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) :
    (conj ℓ ζ (0 : Fin (ℓ + 1))).coeff (-1 : ℤ) = 0 := by
  rw [conj_zero]
  refine qExpand_coeff_of_not_dvd _ _ ?_
  intro h
  have h1 : ((ℓ * ℓ : ℕ) : ℤ) ∣ 1 := dvd_neg.mp h
  have h2 : (ℓ * ℓ : ℕ) ∣ 1 := by exact_mod_cast h1
  have h3 : ℓ * ℓ = 1 := Nat.dvd_one.mp h2
  have h4 : 2 ≤ ℓ := hℓ.out.two_le
  nlinarith

/--
@isnad1 id=eq.0h4v.s7.31d59e2bbd07 from=translated src=- shape=e89baae2 vocab=1fc126be
-/
theorem conj_succ_coeff_neg_one {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (b : Fin ℓ) :
    (conj ℓ ζ b.succ).coeff (-1 : ℤ) = (((ζ ^ (b : ℕ))⁻¹ : Kˣ) : K) := by
  rw [conj_succ, qTwist_coeff, coeff_coeffEmb_jq_neg_one, mul_one, zpow_neg_one]

private theorem conj_injective {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    Function.Injective (conj ℓ ζ (K := K)) := by
  have hne : ∀ b : Fin ℓ, (conj ℓ ζ (0 : Fin (ℓ + 1))).coeff (-1 : ℤ) ≠
      (conj ℓ ζ b.succ).coeff (-1 : ℤ) := by
    intro b
    rw [conj_zero_coeff_neg_one, conj_succ_coeff_neg_one]
    exact fun h => Units.ne_zero _ h.symm
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ b => exact absurd (congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij) (hne b)
  | succ b =>
    induction j using Fin.cases with
    | zero => exact absurd (congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij.symm) (hne b)
    | succ b' =>
      have hcoeff := congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij
      simp only [conj_succ_coeff_neg_one] at hcoeff
      have hu : (ζ ^ (b : ℕ))⁻¹ = (ζ ^ (b' : ℕ))⁻¹ := Units.ext hcoeff
      have hpow : (ζ : K) ^ (b : ℕ) = (ζ : K) ^ (b' : ℕ) := by
        have hv := congrArg Units.val (inv_injective hu)
        push_cast at hv
        exact hv
      exact congrArg Fin.succ (Fin.ext (hζ.pow_inj b.isLt b'.isLt hpow))

end PhiGen
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_conj_injective.ModularCurve _root_.ModularCurve.PhiGen _root_.P2MW.S_ModularCurve_PhiGen_conj_injective.ModularCurve.PhiGen in

/--
@isnad1 id=injectiv.1h3v.s6.b32f18ba97f7 from=translated src=- shape=6c746522 vocab=1db2a0c5
-/
theorem solution {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) : Function.Injective (conj ℓ ζ (K := K)) :=
  ModularCurve.PhiGen.conj_injective ℓ ζ hζ

