import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.RingTheory.Flat.Equalizer
import Tengoku.Seed.LinearAlgebra.TensorProduct.Prod
import Tengoku.Seed.LinearAlgebra.TensorProduct.RightExactness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_TwoChartCech_Mumford_bijective_kerMapBaseChange.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_TwoChartCech_Mumford_bijective_kerMapBaseChange

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u

namespace TwoChartCech
export _root_.TwoChartCech (Mumford.dK Mumford.ι0 Mumford.ι1 Mumford.comm kerMapBaseChange)
namespace Mumford
export _root_.TwoChartCech.Mumford (rank lift surjective_coprod K0 dK ι0 ι1 comm)
open _root_.TwoChartCech.Mumford open _root_.TwoChartCech

variable {R : Type u} [CommRing R]
variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
variable (A : Type u) [CommRing A] [Algebra R A]

/--
@isnad1 id=injectiv.0h5v.s13.545d4b7f2d5f from=translated src=- shape=fbe75203 vocab=5f9fff4b
-/
theorem subtype_baseChange_injective [Module.Flat R C1] :
    Function.Injective ((K0 d).subtype.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_injective_of_exact_of_flat (d.coprod (lift d))
    (surjective_coprod d) _ (K0 d).subtype_injective (LinearMap.exact_subtype_ker_map _) A

/--
@isnad1 id=iff.0h6v.s14.11d586ef91bf from=translated src=- shape=99464242 vocab=286dcb47
-/
theorem mem_range_subtype_baseChange (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w = 0 ↔ ∃ z, ((K0 d).subtype.baseChange A) z = w := by
  have heqι : ⇑((K0 d).subtype.baseChange A) = ⇑((K0 d).subtype.lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  have heqc : ⇑((d.coprod (lift d)).baseChange A) = ⇑((d.coprod (lift d)).lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  rw [heqc]
  simp only [heqι]
  exact lTensor_exact A (LinearMap.exact_subtype_ker_map _) (surjective_coprod d) w

/--
@isnad1 id=eq.0h5v.s11.8bdb99bc4044 from=translated src=- shape=083ed500 vocab=a59133d6
-/
theorem prodRight_apply_eq_baseChange {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (w : A ⊗[R] (M × N)) :
    (TensorProduct.prodRight R A A M N) w
      = (((LinearMap.fst R M N).baseChange A) w, ((LinearMap.snd R M N).baseChange A) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact rfl
  | tmul a x => simp [TensorProduct.prodRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

/--
@isnad1 id=eq.0h6v.s15.75076cd43bad from=translated src=- shape=e2910bba vocab=fbea74f4
-/
theorem prodRight_subtype_baseChange (z : A ⊗[R] K0 d) :
    (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) (((K0 d).subtype.baseChange A) z)
      = (((ι0 d).baseChange A) z, ((dK d).baseChange A) z) := by
  rw [prodRight_apply_eq_baseChange]
  refine Prod.ext ?_ ?_
  · show ((LinearMap.fst R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A) z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl
  · show ((LinearMap.snd R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A) z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl

/--
@isnad1 id=injectiv.0h5v.s17.7002f77a1109 from=translated src=- shape=cdd7330f vocab=12fea19c
-/
theorem kerMapBaseChange_injective [Module.Flat R C1] :
    Function.Injective (kerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A) := by
  rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz'
  apply Subtype.ext
  apply subtype_baseChange_injective d A
  apply (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)).injective
  rw [prodRight_subtype_baseChange d A z, prodRight_subtype_baseChange d A z']
  have h1 : ((dK d).baseChange A) z = 0 := hz
  have h2 : ((dK d).baseChange A) z' = 0 := hz'
  rw [h1, h2]
  exact congrArg (·, (0 : A ⊗[R] (Fin (rank d) → R))) (congrArg Subtype.val hzz')

/--
@isnad1 id=surjecti.0h5v.s17.3b912ef187da from=translated src=- shape=24a5ceb1 vocab=3948cf8b
-/
theorem kerMapBaseChange_surjective :
    Function.Surjective (kerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A) := by
  rintro ⟨w, hw⟩
  set w' : A ⊗[R] (C0 × (Fin (rank d) → R)) :=
    ((LinearMap.inl R C0 (Fin (rank d) → R)).baseChange A) w with hw'def
  have hker : ((d.coprod (lift d)).baseChange A) w' = 0 := by
    rw [hw'def, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.coprod_inl]
    exact hw
  obtain ⟨z, hz⟩ := (mem_range_subtype_baseChange d A w').mp hker
  have hpr : (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w' = (w, 0) := by
    rw [prodRight_apply_eq_baseChange, hw'def, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      LinearMap.fst_comp_inl R C0 (Fin (rank d) → R),
      LinearMap.snd_comp_inl R C0 (Fin (rank d) → R),
      LinearMap.baseChange_id, LinearMap.baseChange_zero, LinearMap.id_apply,
      LinearMap.zero_apply]
  have hpair : (((ι0 d).baseChange A) z, ((dK d).baseChange A) z) = (w, 0) := by
    rw [← prodRight_subtype_baseChange d A z, hz, hpr]
  refine ⟨⟨z, (Prod.ext_iff.mp hpair).2⟩, ?_⟩
  exact Subtype.ext (Prod.ext_iff.mp hpair).1

end TwoChartCech.Mumford

open _root_.TwoChartCech.Mumford _root_.P2MW.S_TwoChartCech_Mumford_bijective_kerMapBaseChange.TwoChartCech.Mumford in
/--
@isnad1 id=bijectiv.0h5v.s17.aafa82f7719b from=translated src=- shape=ea4bb07d vocab=3c7b2571
-/
theorem solution
    {R : Type u} [CommRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective
      (TwoChartCech.kerMapBaseChange (TwoChartCech.Mumford.dK d) d (TwoChartCech.Mumford.ι0 d)
        (TwoChartCech.Mumford.ι1 d) (TwoChartCech.Mumford.comm d) A) :=
  ⟨kerMapBaseChange_injective d A, kerMapBaseChange_surjective d A⟩

end
