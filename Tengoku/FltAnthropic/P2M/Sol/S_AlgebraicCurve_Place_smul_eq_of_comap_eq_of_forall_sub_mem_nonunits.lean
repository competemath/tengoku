import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_smul_eq_of_comap_eq_of_forall_sub_mem_nonunits.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_smul_eq_of_comap_eq_of_forall_sub_mem_nonunits

set_option autoImplicit false

open _root_.AlgebraicCurve
open scoped Pointwise

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.eq_of_comap_eq_of_forall_mem_nonunits_iff)
namespace Place
export _root_.AlgebraicCurve.Place (ext smul_toValuationSubring algebraMap_mem' toValuationSubring eq_of_comap_eq_of_forall_mem_nonunits_iff)
open _root_.AlgebraicCurve.Place open _root_.AlgebraicCurve

variable {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
  {κ' : Type*} [Field κ'] [Algebra κ κ']
  {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
  [IsScalarTower κ F F'] [IsScalarTower κ κ' F']

variable (κ') in

def constantBaseRing (P : Place κ F) : Subring F' :=
  Subring.closure ((algebraMap F F') '' (P.toValuationSubring : Set F) ∪ Set.range (algebraMap κ' F'))

variable (κ') in

def constantBaseIdeal (P : Place κ F) : AddSubgroup F' :=
  AddSubgroup.closure {y | ∃ m ∈ P.toValuationSubring.nonunits, ∃ r ∈ constantBaseRing κ' (F' := F') P,
    y = algebraMap F F' m * r}

/--
@isnad1 id=mem.1h6v.s8.96b0dfa76483 from=translated src=- shape=4024ad8d vocab=e2cf6e0e
-/
theorem algebraMap_mem_constantBaseRing (P : Place κ F) {f : F} (hf : f ∈ P.toValuationSubring) :
    algebraMap F F' f ∈ constantBaseRing κ' P :=
  Subring.subset_closure (Or.inl ⟨f, hf, rfl⟩)

/--
@isnad1 id=mem.0h6v.s8.f2fc2fe0919b from=translated src=- shape=4c08b387 vocab=3cc30dc6
-/
theorem algebraMap_const_mem_constantBaseRing (P : Place κ F) (c : κ') :
    algebraMap κ' F' c ∈ constantBaseRing κ' (F := F) P :=
  Subring.subset_closure (Or.inr ⟨c, rfl⟩)

/--
@isnad1 id=mem.2h7v.s8.a62c0e6060f8 from=translated src=- shape=298ae43c vocab=25d771d0
-/
theorem mul_mem_constantBaseIdeal (P : Place κ F) {m : F} (hm : m ∈ P.toValuationSubring.nonunits) {r : F'}
    (hr : r ∈ constantBaseRing κ' P) : algebraMap F F' m * r ∈ constantBaseIdeal κ' P :=
  AddSubgroup.subset_closure ⟨m, hm, r, hr, rfl⟩

/--
@isnad1 id=mem.2h7v.s8.8673034df456 from=translated src=- shape=9d83a1f9 vocab=9e23b134
-/
theorem constantBaseIdeal_mul_mem (P : Place κ F) {y : F'} (hy : y ∈ constantBaseIdeal κ' P) {r : F'}
    (hr : r ∈ constantBaseRing κ' P) : y * r ∈ constantBaseIdeal κ' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
      obtain ⟨m, hm, s, hs, rfl⟩ := hz
      rw [mul_assoc]
      exact mul_mem_constantBaseIdeal P hm (Subring.mul_mem _ hs hr)
  | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [neg_mul]; exact AddSubgroup.neg_mem _ ha

/--
@isnad1 id=mem.2h7v.s8.270f94323eb7 from=translated src=- shape=11a2aa8c vocab=9e23b134
-/
theorem mul_constantBaseIdeal_mem (P : Place κ F) {y : F'} (hy : y ∈ constantBaseIdeal κ' P) {r : F'}
    (hr : r ∈ constantBaseRing κ' P) : r * y ∈ constantBaseIdeal κ' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
      obtain ⟨m, hm, s, hs, rfl⟩ := hz
      rw [mul_left_comm]
      exact mul_mem_constantBaseIdeal P hm (Subring.mul_mem _ hr hs)
  | zero => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

/--
@isnad1 id=mem.2h5v.s7.296786b1a1d8 from=translated src=- shape=b97658a5 vocab=524b999d
-/
theorem smul_mem_of_smul_eq {σ : F ≃ₐ[κ] F} {P : Place κ F} (hP : σ • P = P) {f : F} (hf : f ∈ P.toValuationSubring) :
    σ f ∈ P.toValuationSubring := by
  have h : σ • f ∈ σ • P.toValuationSubring := ValuationSubring.smul_mem_pointwise_smul σ f _ hf
  rw [← smul_toValuationSubring, hP] at h
  exact h

/--
@isnad1 id=and.4h8v.s9.b523c37122aa from=translated src=- shape=d05c751f vocab=e1417869
-/
theorem smul_mem_constantBaseRing_and_sub_mem_of_forall_sub_mem_nonunits
    (σ : F ≃ₐ[κ] F) (σ' : F' ≃ₐ[κ'] F')
    (hσ : ∀ f : F, σ' (algebraMap F F' f) = algebraMap F F' (σ f))
    (P : Place κ F) (hP : σ • P = P)
    (hI : ∀ e : F, e ∈ P.toValuationSubring → σ e - e ∈ P.toValuationSubring.nonunits)
    (x : F') (hx : x ∈ constantBaseRing κ' P) :
    σ' x ∈ constantBaseRing κ' P ∧ σ' x - x ∈ constantBaseIdeal κ' P := by
  induction hx using Subring.closure_induction with
  | mem z hz =>
      rcases hz with ⟨f, hf, rfl⟩ | ⟨c, rfl⟩
      · refine ⟨?_, ?_⟩
        · rw [hσ]; exact algebraMap_mem_constantBaseRing P (smul_mem_of_smul_eq hP hf)
        · rw [hσ, ← map_sub, ← mul_one (algebraMap F F' (σ f - f))]
          exact mul_mem_constantBaseIdeal P (hI f hf) (Subring.one_mem _)
      · refine ⟨?_, ?_⟩
        · rw [AlgEquiv.commutes]; exact algebraMap_const_mem_constantBaseRing P c
        · rw [AlgEquiv.commutes, sub_self]; exact AddSubgroup.zero_mem _
  | zero => simp only [map_zero, sub_self]; exact ⟨Subring.zero_mem _, AddSubgroup.zero_mem _⟩
  | one => simp only [map_one, sub_self]; exact ⟨Subring.one_mem _, AddSubgroup.zero_mem _⟩
  | add a b ha hb iha ihb =>
      refine ⟨by rw [map_add]; exact Subring.add_mem _ iha.1 ihb.1, ?_⟩
      have : σ' (a + b) - (a + b) = (σ' a - a) + (σ' b - b) := by rw [map_add]; ring
      rw [this]; exact AddSubgroup.add_mem _ iha.2 ihb.2
  | neg a ha iha =>
      refine ⟨by rw [map_neg]; exact Subring.neg_mem _ iha.1, ?_⟩
      have : σ' (-a) - -a = -(σ' a - a) := by rw [map_neg]; ring
      rw [this]; exact AddSubgroup.neg_mem _ iha.2
  | mul a b ha hb iha ihb =>
      refine ⟨by rw [map_mul]; exact Subring.mul_mem _ iha.1 ihb.1, ?_⟩
      have : σ' (a * b) - a * b = σ' a * (σ' b - b) + (σ' a - a) * b := by rw [map_mul]; ring
      rw [this]
      exact AddSubgroup.add_mem _ (mul_constantBaseIdeal_mem P ihb.2 iha.1) (constantBaseIdeal_mul_mem P iha.2 hb)

/--
@isnad1 id=iff.1h7v.s8.46f8b0141331 from=translated src=- shape=b813cf10 vocab=fd3a47b0
-/
theorem mem_of_comap_eq {P : Place κ F} {P' : Place κ' F'}
    (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) (f : F) :
    f ∈ P.toValuationSubring ↔ algebraMap F F' f ∈ P'.toValuationSubring := by
  rw [← hP']; rfl

/--
@isnad1 id=le.1h6v.s8.5f01b59f275c from=translated src=- shape=44f363e8 vocab=8b26e189
-/
theorem constantBaseRing_le {P : Place κ F} {P' : Place κ' F'}
    (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    constantBaseRing κ' P ≤ P'.toValuationSubring.toSubring := by
  refine Subring.closure_le.mpr ?_
  rintro z (⟨f, hf, rfl⟩ | ⟨c, rfl⟩)
  · exact (mem_of_comap_eq hP' f).mp hf
  · exact P'.algebraMap_mem' c

/--
@isnad1 id=mem.2h7v.s8.53f89de78226 from=translated src=- shape=3efcc6fd vocab=7fd0f809
-/
theorem algebraMap_mem_nonunits {P : Place κ F} {P' : Place κ' F'}
    (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) {m : F}
    (hm : m ∈ P.toValuationSubring.nonunits) : algebraMap F F' m ∈ P'.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hm ⊢
  rcases hm with rfl | hm
  · exact Or.inl (map_zero _)
  · right
    rw [← map_inv₀, ← mem_of_comap_eq hP']
    exact hm

/--
@isnad1 id=mem.2h7v.s8.f7210c485ad6 from=translated src=- shape=e8202d3b vocab=b42da35e
-/
theorem constantBaseIdeal_le_nonunits {P : Place κ F} {P' : Place κ' F'}
    (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) {y : F'}
    (hy : y ∈ constantBaseIdeal κ' P) : y ∈ P'.toValuationSubring.nonunits := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
      obtain ⟨m, hm, r, hr, rfl⟩ := hz
      have h1 := algebraMap_mem_nonunits (κ' := κ') (F' := F') hP' hm
      have h2 : r ∈ P'.toValuationSubring := constantBaseRing_le hP' hr
      rw [ValuationSubring.mem_nonunits_iff] at h1 ⊢
      rw [map_mul]
      calc P'.toValuationSubring.valuation (algebraMap F F' m) * P'.toValuationSubring.valuation r
          ≤ P'.toValuationSubring.valuation (algebraMap F F' m) * 1 :=
            mul_le_mul_right ((P'.toValuationSubring.valuation_le_one_iff r).mpr h2) _
        _ < 1 := by rwa [mul_one]
  | zero => exact (P'.toValuationSubring.nonunits).zero_mem
  | add a b _ _ ha hb => exact (P'.toValuationSubring.nonunits).add_mem ha hb
  | neg a _ ha => exact (P'.toValuationSubring.nonunits).neg_mem ha

/--
@isnad1 id=iff.5h9v.s9.e8a18600d1a2 from=translated src=- shape=6fc615c3 vocab=5aabfcb1
-/
theorem mem_nonunits_iff_smul_mem (σ : F ≃ₐ[κ] F) (σ' : F' ≃ₐ[κ'] F')
    (hσ : ∀ f : F, σ' (algebraMap F F' f) = algebraMap F F' (σ f))
    (P : Place κ F) (hP : σ • P = P)
    (hI : ∀ e : F, e ∈ P.toValuationSubring → σ e - e ∈ P.toValuationSubring.nonunits)
    {P' : Place κ' F'} (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    {x : F'} (hx : x ∈ constantBaseRing κ' P) :
    x ∈ P'.toValuationSubring.nonunits ↔ σ' x ∈ P'.toValuationSubring.nonunits := by
  have h := (smul_mem_constantBaseRing_and_sub_mem_of_forall_sub_mem_nonunits σ σ' hσ P hP hI x hx).2
  have hd : σ' x - x ∈ P'.toValuationSubring.nonunits := constantBaseIdeal_le_nonunits hP' h
  constructor
  · intro hx'
    have : σ' x = (σ' x - x) + x := by ring
    rw [this]; exact (P'.toValuationSubring.nonunits).add_mem hd hx'
  · intro hx'
    have : x = σ' x - (σ' x - x) := by ring
    rw [this]; exact (P'.toValuationSubring.nonunits).sub_mem hx' hd

/--
@isnad1 id=iff.0h5v.s8.523304d83ae7 from=translated src=- shape=759c5907 vocab=8008f3d5
-/
theorem mem_nonunits_smul_iff (σ' : F' ≃ₐ[κ'] F') (P' : Place κ' F') (x : F') :
    x ∈ (σ' • P').toValuationSubring.nonunits ↔ σ'.symm x ∈ P'.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, map_eq_zero_iff _ σ'.symm.injective, AlgEquiv.smul_def,
    AlgEquiv.aut_inv, map_inv₀]

end AlgebraicCurve.Place

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_smul_eq_of_comap_eq_of_forall_sub_mem_nonunits.AlgebraicCurve.Place in

/--
@isnad1 id=eq.5h8v.s10.b054f83f3ce7 from=translated src=- shape=095e8a22 vocab=c77b9868
-/
theorem solution
    {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
    {κ' : Type*} [Field κ'] [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
    {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
    [IsScalarTower κ F F'] [IsScalarTower κ κ' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤)
    (σ : F ≃ₐ[κ] F) (σ' : F' ≃ₐ[κ'] F')
    (hσ : ∀ f : F, σ' (algebraMap F F' f) = algebraMap F F' (σ f))
    (P : Place κ F) (hP : σ • P = P)
    (hI : ∀ e : F, e ∈ P.toValuationSubring → σ e - e ∈ P.toValuationSubring.nonunits)
    (P' : Place κ' F')
    (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    σ' • P' = P' := by

  haveI : Algebra.IsIntegral F F' := by
    have hint : ∀ c : κ', IsIntegral F (algebraMap κ' F' c) := fun c =>
      (((Algebra.IsAlgebraic.isAlgebraic (R := κ) c).isIntegral).map (IsScalarTower.toAlgHom κ κ' F')).tower_top
    have hle : Algebra.adjoin F (Set.range (algebraMap κ' F')) ≤ integralClosure F F' :=
      Algebra.adjoin_le (by rintro _ ⟨c, rfl⟩; exact hint c)
    exact ⟨fun x => hle (hgen ▸ Algebra.mem_top : x ∈ Algebra.adjoin F (Set.range (algebraMap κ' F')))⟩

  have hσ_inv : ∀ f : F, σ'.symm (algebraMap F F' f) = algebraMap F F' (σ.symm f) := by
    intro f
    apply σ'.injective
    rw [AlgEquiv.apply_symm_apply, hσ, AlgEquiv.apply_symm_apply]
  have hP_inv : σ.symm • P = P := by
    rw [← AlgEquiv.aut_inv, inv_smul_eq_iff, hP]
  have hI_inv : ∀ e : F, e ∈ P.toValuationSubring → σ.symm e - e ∈ P.toValuationSubring.nonunits := by
    intro e he
    have h := hI (σ.symm e) (smul_mem_of_smul_eq hP_inv he)
    rw [AlgEquiv.apply_symm_apply] at h
    have : σ.symm e - e = -(e - σ.symm e) := by ring
    rw [this]; exact (P.toValuationSubring.nonunits).neg_mem h

  have h₁ : (σ' • P').toValuationSubring.comap (algebraMap F F') = P.toValuationSubring := by
    ext f
    show algebraMap F F' f ∈ (σ' • P').toValuationSubring ↔ f ∈ P.toValuationSubring
    rw [smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    show σ'⁻¹ (algebraMap F F' f) ∈ P'.toValuationSubring ↔ _
    rw [AlgEquiv.aut_inv, hσ_inv, ← mem_of_comap_eq hP']
    exact ⟨fun h => by simpa using smul_mem_of_smul_eq hP h, fun h => smul_mem_of_smul_eq hP_inv h⟩

  refine AlgebraicCurve.Place.eq_of_comap_eq_of_forall_mem_nonunits_iff (κ := κ) hgen P (σ' • P') P' h₁ hP' fun x hx => ?_
  rw [mem_nonunits_smul_iff]
  exact (mem_nonunits_iff_smul_mem σ.symm σ'.symm hσ_inv P hP_inv hI_inv hP' hx).symm
