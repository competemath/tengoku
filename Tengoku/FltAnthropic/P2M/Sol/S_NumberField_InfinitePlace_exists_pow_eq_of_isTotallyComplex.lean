import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex

set_option autoImplicit false

open NumberField

open NumberField in

/--
@isnad1 id=ex.1h4v.s8.33850dc48b73 from=translated src=- shape=daec7d52 vocab=251398f7
-/
theorem solution
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (w : InfinitePlace K) (u : (w.Completion)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ v : (w.Completion)ˣ, v ^ n = u := by

  let e : w.Completion ≃+* ℂ :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)

  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (u : w.Completion)) hn
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hz
    exact (e.map_ne_zero_iff.2 u.ne_zero) hz.symm
  have hv0 : e.symm z ≠ 0 := fun h => hz0 (by simpa using congrArg e h)
  refine ⟨Units.mk0 (e.symm z) hv0, Units.ext ?_⟩
  change (e.symm z) ^ n = (u : w.Completion)
  apply e.injective
  rw [map_pow, e.apply_symm_apply, hz]
