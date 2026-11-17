import Tengoku.PaperCLean.PaperC.Probability.PoissonLaplaceFunctional
import Tengoku.Seed.Data.Fin.Tuple.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 800000

/-!
# Finite products of Poisson mass functions

This file supplies the literal probability mass and transform identities for
a finite vector of independent Poisson variables.
-/

open scoped BigOperators NNReal
open ProbabilityTheory

namespace PaperC
namespace PoissonVectorMass

noncomputable section

/--
@isnad1 id=hassum.2h3v.s6.8825c632a7cd from=translated src=- shape=20a26f3a vocab=e51a0534
-/
theorem hasSum_pi_prod_general
    (d : ℕ) (f : Fin d → ℕ → ℝ) (a : Fin d → ℝ)
    (hf0 : ∀ e k, 0 ≤ f e k)
    (hf : ∀ e, HasSum (f e) (a e)) :
    HasSum
      (fun k : Fin d → ℕ ↦ ∏ e : Fin d, f e (k e))
      (∏ e : Fin d, a e) := by
  induction d with
  | zero =>
      let z : Fin 0 → ℕ := fun i ↦ Fin.elim0 i
      have hfun :
          (fun k : Fin 0 → ℕ ↦ ∏ e : Fin 0, f e (k e)) =
            fun k ↦ if k = z then 1 else 0 := by
        funext k
        have hk : k = z := by
          funext i
          exact Fin.elim0 i
        simp [hk]
      rw [hfun]
      exact hasSum_ite_eq z 1
  | succ d ih =>
      let head : ℕ → ℝ := f 0
      let tail : Fin d → ℕ → ℝ := fun e ↦ f e.succ
      have hhead0 : ∀ k, 0 ≤ head k := fun k ↦ hf0 0 k
      have htail0 : ∀ e k, 0 ≤ tail e k :=
        fun e k ↦ hf0 e.succ k
      let tailSum : Fin d → ℝ := fun e ↦ a e.succ
      have hhead : HasSum head (a 0) := hf 0
      let tailMass : (Fin d → ℕ) → ℝ :=
        fun k ↦ ∏ e : Fin d, tail e (k e)
      have htailMass0 : ∀ k, 0 ≤ tailMass k :=
        fun k ↦ Finset.prod_nonneg fun e _ ↦ htail0 e (k e)
      have htail :
          HasSum tailMass (∏ e : Fin d, tailSum e) := by
        simpa only [tailMass] using
          ih tail tailSum htail0 (fun e ↦ hf e.succ)
      have hprodSummable :
          Summable
            (fun x : ℕ × (Fin d → ℕ) ↦
              head x.1 * tailMass x.2) :=
        hhead.summable.mul_of_nonneg
          htail.summable hhead0 htailMass0
      have hpair :
          HasSum
            (fun x : ℕ × (Fin d → ℕ) ↦
              head x.1 * tailMass x.2)
            (a 0 * ∏ e : Fin d, tailSum e) := by
        simpa using hhead.mul htail hprodSummable
      rw [← (Fin.consEquiv (fun _ : Fin (d + 1) ↦ ℕ)).hasSum_iff]
      convert hpair using 1
      · funext x
        simp only [Function.comp_apply, Fin.consEquiv,
          Equiv.coe_fn_mk,
          Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ,
          head, tail, tailMass]
      · simp only [Fin.prod_univ_succ, tailSum]

/--
@isnad1 id=hassum.2h2v.s6.7e1b34d7b140 from=translated src=- shape=9ed48d64 vocab=e51a0534
-/
theorem hasSum_pi_prod
    (d : ℕ) (f : Fin d → ℕ → ℝ)
    (hf0 : ∀ e k, 0 ≤ f e k)
    (hf : ∀ e, HasSum (f e) 1) :
    HasSum
      (fun k : Fin d → ℕ ↦ ∏ e : Fin d, f e (k e))
      1 := by
  simpa using
    hasSum_pi_prod_general d f (fun _ ↦ 1) hf0 hf

end

end PoissonVectorMass
end PaperC
