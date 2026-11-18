import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ModuliPoint
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_ModuliPoint_mk_eq_mk_iff_step
import Tengoku.FltAnthropic.Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Tengoku.FltAnthropic.Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

universe u

namespace ClassJ

variable {L : Type u} [Field L] [DecidableEq L]

noncomputable def vcAddEquiv (γ : VariableChange L) (E : WeierstrassCurve L) :
    E.toAffine.Point ≃+ (γ • E).toAffine.Point where
  toFun := Point.vcInvFun γ E.toAffine
  invFun := Point.vcFun γ E.toAffine
  left_inv := Point.vcFun_rightInverse
  right_inv := Point.vcFun_leftInverse
  map_add' := Point.vcInvFun_add γ E.toAffine

/--
@isnad1 id=eq.0h4v.s8.e7f096070fbf from=translated src=- shape=09b7a146 vocab=41ee72c6
-/
@[scoped simp] theorem vcAddEquiv_symm_apply (γ : VariableChange L) (E : WeierstrassCurve L) (R : (γ • E).toAffine.Point) :
    (vcAddEquiv γ E).symm R = Point.vcFun γ E.toAffine R := rfl

/--
@isnad1 id=eq.1h3v.s5.1fe5e25457d7 from=translated src=- shape=dfb595f3 vocab=a5bc0377
-/
theorem zmultiples_nsmul_eq_of_coprime {A : Type*} [AddGroup A] (a : A) {k : ℕ} (hk : k.Coprime (addOrderOf a)) :
    AddSubgroup.zmultiples (k • a) = AddSubgroup.zmultiples a := by
  apply le_antisymm
  · exact AddSubgroup.zmultiples_le_of_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples a) k)
  · obtain ⟨m, hm⟩ := exists_nsmul_eq_self_of_coprime hk
    apply AddSubgroup.zmultiples_le_of_mem
    have h3 : m • (k • a) ∈ AddSubgroup.zmultiples (k • a) := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples (k • a)) m
    rwa [hm] at h3

end ClassJ
open scoped _root_.P2MW.S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk.ClassJ

open ClassJ in
/--
@isnad1 id=eq.3h5v.s8.db40e0f1ad19 from=translated src=- shape=e7cbf33c vocab=9b15ef45
-/
theorem solution
    {L : Type u} [Field L] [DecidableEq L] {N : ℕ} [NeZero N] (hN : (N : L) ≠ 0)
    (P Q : ModularCurve.Gamma0Pair N L)
    (h : (Quot.mk _ P : ModularCurve.ModuliPoint N L) = Quot.mk _ Q)
    (d : ℕ) (hd : d ∣ N) :
    P.toCurve.cyclicQuotientJ (AddSubgroup.zmultiples ((N / d) • P.gen)) d =
      Q.toCurve.cyclicQuotientJ (AddSubgroup.zmultiples ((N / d) • Q.gen)) d := by
  classical
  rw [ModuliPoint.mk_eq_mk_iff_step] at h
  obtain ⟨γ, hγ, k, hk, hgen⟩ := h
  obtain ⟨cQ, eQ, gQ, oQ⟩ := Q
  simp only at hγ hgen ⊢
  subst hγ
  have hgQ : gQ = k • Point.vcInvFun γ P.toCurve.toAffine P.gen := eq_of_heq hgen
  subst hgQ
  have hdL : (d : L) ≠ 0 := by
    intro h0
    apply hN
    obtain ⟨m, rfl⟩ := hd
    rw [Nat.cast_mul, h0, zero_mul]
  symm
  apply cyclicQuotientJ_variableChange_eq γ P.toCurve (AddSubgroup.zmultiples ((N / d) • P.gen)) _ ?_ d hdL

  intro R
  set e := vcAddEquiv γ P.toCurve with he
  have h1 : (N / d) • (k • Point.vcInvFun γ P.toCurve.toAffine P.gen) = e (k • ((N / d) • P.gen)) := by
    rw [smul_comm k (N / d) P.gen, map_nsmul, map_nsmul]
    rfl
  have hcop : k.Coprime (addOrderOf ((N / d) • P.gen)) :=
    Nat.Coprime.coprime_dvd_right ((addOrderOf_smul_dvd (N / d)).trans (dvd_of_eq P.addOrderOf_gen)) hk
  have h2 : R ∈ AddSubgroup.zmultiples (e (k • ((N / d) • P.gen))) ↔
      e.symm R ∈ AddSubgroup.zmultiples (k • ((N / d) • P.gen)) := by
    simp only [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [← hz, map_zsmul, AddEquiv.symm_apply_apply]⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [← map_zsmul, hz, AddEquiv.apply_symm_apply]⟩
  rw [h1, h2, zmultiples_nsmul_eq_of_coprime _ hcop, he, vcAddEquiv_symm_apply]
