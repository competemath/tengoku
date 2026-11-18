import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent

set_option autoImplicit false

open ModularCurve

/--
@isnad1 id=linearin.1h4v.s8.9f26f6421a14 from=translated src=- shape=1dc509d4 vocab=ed989c74
-/
theorem solution
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by
  classical
  set g : κ →+* k := algebraMap κ k with hg
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc i₀

  let B := Module.Basis.ofVectorSpace κ k

  have hcomb : ∀ j, ∑ i, (B.repr (c i) j) • f i = 0 := by
    intro j
    ext m

    have hm : ∑ i, ((f i).coeff m) • c i = 0 := by
      have h0 := congrArg (fun x : LaurentSeries k => x.coeff m) hc
      simp only [HahnSeries.coeff_zero, HahnSeries.coeff_sum, Function.comp_apply, HahnSeries.coeff_smul, coeffMap_coeff,
        smul_eq_mul] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]

    have hj := congrArg (fun x : k => B.repr x j) hm
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hj
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    rw [← hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzero : ∀ j, B.repr (c i₀) j = 0 := fun j => hf _ (hcomb j) i₀
  have hrepr : B.repr (c i₀) = 0 := Finsupp.ext hzero
  simpa using congrArg B.repr.symm hrepr

