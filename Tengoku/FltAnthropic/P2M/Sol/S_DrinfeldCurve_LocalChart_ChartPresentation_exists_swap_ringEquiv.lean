import Tengoku.Seed.RingTheory.MvPowerSeries.Rename
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_DrinfeldCurve_LocalChart_ChartPresentation_exists_swap_ringEquiv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_DrinfeldCurve_LocalChart_ChartPresentation_exists_swap_ringEquiv

set_option autoImplicit false

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

namespace S7Swap

variable {q : ℕ} {O : Type} [CommRing O]

abbrev sw : Fin 2 ≃ Fin 2 := Equiv.swap (0 : Fin 2) 1

/--
@isnad1 id=eq.0h1v.s8.b11287dc7efd from=translated src=- shape=bb3dded3 vocab=f57fa76b
-/
lemma rename_X0 : rename (⇑sw) (X 0 : MvPowerSeries (Fin 2) O) = X 1 := by
  rw [rename_X]; simp [sw]

/--
@isnad1 id=eq.0h1v.s8.9ac8b32e7fdf from=translated src=- shape=bb3dded3 vocab=f57fa76b
-/
lemma rename_X1 : rename (⇑sw) (X 1 : MvPowerSeries (Fin 2) O) = X 0 := by
  rw [rename_X]; simp [sw]

variable (q) in
/--
@isnad1 id=eq.0h2v.s8.e9accb34824c from=translated src=- shape=62d90b25 vocab=d541fd7e
-/
lemma rename_drinfeldForm :
    rename (⇑sw) (drinfeldForm q O) = -drinfeldForm q O := by
  unfold drinfeldForm
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, rename_X0, rename_X1]
  ring

/--
@isnad1 id=eq.0h1v.s9.df3506767831 from=translated src=- shape=c8fd7783 vocab=75269d9b
-/
lemma map_span_X :
    Ideal.map (rename (R := O) (⇑sw)).toRingHom
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) =
      Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1} := by
  rw [Ideal.map_span]
  have : (⇑(rename (R := O) (⇑sw)).toRingHom '' {(X 0 : MvPowerSeries (Fin 2) O), X 1}) =
      {(X 1 : MvPowerSeries (Fin 2) O), X 0} := by
    rw [Set.image_pair]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X0, rename_X1]
  rw [this, Set.pair_comm]

/--
@isnad1 id=mem.1h3v.s10.ae7a5d3f874f from=translated src=- shape=eacfd9b3 vocab=7ff434f6
-/
lemma rename_mem_pow {g : MvPowerSeries (Fin 2) O} {n : ℕ}
    (hg : g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ n) :
    rename (⇑sw) g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ n := by
  have h := Ideal.mem_map_of_mem (rename (R := O) (⇑sw)).toRingHom hg
  rw [Ideal.map_pow, map_span_X] at h
  exact h

variable {ϖ : O}

noncomputable def swapPres (pr : ChartPresentation q O ϖ) : ChartPresentation q O ϖ where
  f := -rename (⇑sw) pr.f
  u := -rename (⇑sw) pr.u
  v := rename (⇑sw) pr.v
  isUnit_u := (pr.isUnit_u.map (rename (R := O) (⇑sw))).neg
  isUnit_v := pr.isUnit_v.map (rename (R := O) (⇑sw))
  f_sub_mem := by
    have h := rename_mem_pow pr.f_sub_mem (n := q + 2)
    rw [map_sub, rename_drinfeldForm q] at h
    have : -rename (⇑sw) pr.f - drinfeldForm q O = -(rename (⇑sw) pr.f - -drinfeldForm q O) := by ring
    rw [this]
    exact neg_mem h

/--
@isnad1 id=eq.0h4v.s8.8fd3e2d89886 from=translated src=- shape=469816c5 vocab=7af57ab0
-/
lemma swapPres_rel (pr : ChartPresentation q O ϖ) :
    (swapPres pr).rel = rename (⇑sw) pr.rel := by
  simp only [ChartPresentation.rel, swapPres, map_sub, map_mul, rename_C]
  ring

noncomputable def swapEquiv (pr : ChartPresentation q O ϖ) : pr.Ring ≃+* (swapPres pr).Ring :=
  Ideal.quotientEquiv (Ideal.span {pr.rel}) (Ideal.span {(swapPres pr).rel})
    (renameEquiv O sw).toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton, swapPres_rel]
      congr 2
      )

/--
@isnad1 id=eq.0h5v.s11.626eabdb6d92 from=translated src=- shape=43d862c5 vocab=57230a04
-/
lemma swapEquiv_mk (pr : ChartPresentation q O ϖ) (g : MvPowerSeries (Fin 2) O) :
    swapEquiv pr (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (rename (⇑sw) g) := by
  simp [swapEquiv]

end S7Swap

open S7Swap in
/--
@isnad1 id=ex.0h4v.s13.9ff3432993c7 from=translated src=- shape=e96e8c9b vocab=8f2d953a
-/
theorem solution
    (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] (ϖ : O) (pr : ChartPresentation q O ϖ) :
    ∃ (pr' : ChartPresentation q O ϖ) (e : pr.Ring ≃+* pr'.Ring),
      (∀ o : O, e (Ideal.Quotient.mk _ (C o)) = Ideal.Quotient.mk _ (C o)) ∧
      e (Ideal.Quotient.mk _ (X 0)) = Ideal.Quotient.mk _ (X 1) ∧
      e (Ideal.Quotient.mk _ (X 1)) = Ideal.Quotient.mk _ (X 0) ∧
      pr'.v = MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.v ∧
      pr'.u = -MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.u ∧
      pr'.f = -MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.f := by
  refine ⟨swapPres pr, swapEquiv pr, fun o => ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [swapEquiv_mk, rename_C]
  · rw [swapEquiv_mk, rename_X0]
  · rw [swapEquiv_mk, rename_X1]
