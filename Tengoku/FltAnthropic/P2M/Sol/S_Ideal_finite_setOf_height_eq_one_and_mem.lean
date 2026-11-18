import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_finite_setOf_height_eq_one_and_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_finite_setOf_height_eq_one_and_mem

set_option autoImplicit false

/--
@isnad1 id=finite.1h2v.s7.8b4f3058a0f8 from=translated src=- shape=737d9665 vocab=0fd97f24
-/
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {b : R} (hb : b ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ b ∈ p}.Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).subset ?_
  rintro p ⟨hp, hh, hbp⟩
  haveI := hp
  have hle : Ideal.span {b} ≤ p := (Ideal.span_singleton_le_iff_mem _).mpr hbp
  refine ⟨⟨hp, hle⟩, fun q ⟨hq, hbq⟩ hqp => ?_⟩

  set S := Localization.AtPrime p
  have hdim : ringKrullDim S = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S, hh]
    norm_cast
  have hKDL : Ring.KrullDimLE 1 S :=
    Ring.krullDimLE_iff.mpr (le_of_eq (by rw [hdim, Nat.cast_one]))
  have hmax : ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime → P.IsMaximal :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hKDL
  have hdisj : Disjoint (p.primeCompl : Set R) q :=
    Set.disjoint_left.mpr fun x hx hxq => hx (hqp hxq)
  have hqS : (Ideal.map (algebraMap R S) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q hq hdisj
  have hqS0 : Ideal.map (algebraMap R S) q ≠ ⊥ := by
    intro hbot
    have hbS : algebraMap R S b ∈ Ideal.map (algebraMap R S) q :=
      Ideal.mem_map_of_mem _ (hbq (Ideal.subset_span rfl))
    rw [hbot, Ideal.mem_bot] at hbS
    exact hb ((IsLocalization.injective S p.primeCompl_le_nonZeroDivisors) (by rw [hbS, map_zero]))
  have hqmax : Ideal.map (algebraMap R S) q = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (hmax _ hqS0 hqS)
  have hq' : q = p := by
    rw [← IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hq hdisj, hqmax,
      Localization.AtPrime.under_maximalIdeal]
  exact hq'.ge
