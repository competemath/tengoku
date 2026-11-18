import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb

set_option autoImplicit false

open scoped BigOperators

namespace SpanE96

open ModularCurve

variable {L : Type} [Field L] [CharZero L]
  {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ L)
  (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

noncomputable def φ : ↥F₀ →+* LaurentSeries L := (coeffEmb L).comp F₀.toSubfield.subtype

@[reducible] noncomputable def modF₀ : Module ↥F₀ (LaurentSeries L) := Module.compHom _ (φ F₀ (L := L))

noncomputable def T : @Submodule ↥F₀ (LaurentSeries L) _ _ (modF₀ F₀) :=
  @Submodule.span ↥F₀ (LaurentSeries L) _ _ (modF₀ F₀) (Set.range fun i => HahnSeries.C (b i))

/--
@isnad1 id=eq.0h4v.s12.9f6e21006b1d from=translated src=- shape=2fe18b0a vocab=88dbb44b
-/
theorem smul_def' (a : ↥F₀) (x : LaurentSeries L) :
    @HSMul.hSMul ↥F₀ (LaurentSeries L) (LaurentSeries L) (@instHSMul _ _ (modF₀ F₀).toSMul) a x
      = coeffEmb L (a : LaurentSeries ℚ) * x := rfl

/--
@isnad1 id=iff.0h5v.s11.5f0e33f1a467 from=translated src=- shape=0c50b9ec vocab=49a8312a
-/
theorem mem_T_iff (f : LaurentSeries L) :
    f ∈ T b F₀ ↔ ∃ h : ι → ↥F₀, f = ∑ i, (b i) • coeffEmb L ((h i : ↥F₀) : LaurentSeries ℚ) := by
  letI := modF₀ F₀ (L := L)
  unfold T
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_def', mul_comm, HahnSeries.C_mul_eq_smul]
  · rintro ⟨h, rfl⟩
    refine ⟨h, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [smul_def', mul_comm, HahnSeries.C_mul_eq_smul]

/--
@isnad1 id=eq.0h2v.s8.4aa3b5789ca3 from=translated src=- shape=e95e0eae vocab=25266c1b
-/
theorem algebraMap_eq_C (ℓ : L) : algebraMap L (LaurentSeries L) ℓ = HahnSeries.C ℓ := by
  rw [HahnSeries.algebraMap_apply']; simp

/--
@isnad1 id=eq.0h2v.s8.3088c86e974c from=translated src=- shape=526588b1 vocab=13f1c04f
-/
theorem coeffEmb_C (q : ℚ) : coeffEmb L (HahnSeries.C q) = HahnSeries.C (algebraMap ℚ L q) := by
  ext n; simp

/--
@isnad1 id=eq.0h1v.s7.ac1c95e48b05 from=translated src=- shape=e7341219 vocab=2f82c998
-/
theorem algebraMap_eq_C_rat (q : ℚ) : algebraMap ℚ (LaurentSeries ℚ) q = HahnSeries.C q := by
  rw [HahnSeries.algebraMap_apply']; simp

noncomputable def cst (q : ℚ) : ↥F₀ := ⟨HahnSeries.C q, by rw [← algebraMap_eq_C_rat]; exact F₀.algebraMap_mem q⟩

/--
@isnad1 id=eq.0h2v.s8.13423d8a3965 from=translated src=- shape=ac321b37 vocab=fff021d5
-/
@[scoped simp] theorem coe_cst (q : ℚ) : ((cst F₀ q : ↥F₀) : LaurentSeries ℚ) = HahnSeries.C q := rfl

/--
@isnad1 id=mem.0h5v.s11.d2995a0dde16 from=translated src=- shape=80109509 vocab=6036fcef
-/
theorem C_mem_T (ℓ : L) : HahnSeries.C ℓ ∈ T b F₀ := by
  letI := modF₀ F₀ (L := L)
  have e1 : ∀ i, (cst F₀ (b.repr ℓ i)) • (HahnSeries.C (b i) : LaurentSeries L) = HahnSeries.C ((b.repr ℓ i) • b i) := by
    intro i
    rw [smul_def', coe_cst, coeffEmb_C, ← map_mul, Algebra.smul_def]
  have hℓ : (HahnSeries.C ℓ : LaurentSeries L) = ∑ i, (cst F₀ (b.repr ℓ i)) • (HahnSeries.C (b i) : LaurentSeries L) := by
    simp_rw [e1]
    rw [← map_sum (HahnSeries.C : L →+* LaurentSeries L) (fun i => b.repr ℓ i • b i) Finset.univ, b.sum_repr]
  rw [hℓ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/--
@isnad1 id=mem.0h4v.s11.654187a3412c from=translated src=- shape=2362d83b vocab=613f83fa
-/
theorem one_mem_T : (1 : LaurentSeries L) ∈ T b F₀ := by
  simpa using C_mem_T b F₀ (1 : L)

/--
@isnad1 id=mem.2h6v.s12.4ba22db9a6ee from=translated src=- shape=76bb3d72 vocab=acbd782b
-/
theorem mul_mem_T {s t : LaurentSeries L} (hs : s ∈ T b F₀) (ht : t ∈ T b F₀) : s * t ∈ T b F₀ := by
  letI := modF₀ F₀ (L := L)
  unfold T at hs ht ⊢
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction ht using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [← map_mul]
      exact C_mem_T b F₀ _
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      rw [smul_def', mul_left_comm, ← smul_def']
      exact Submodule.smul_mem _ _ hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_def', mul_assoc, ← smul_def']
    exact Submodule.smul_mem _ _ hx

/--
@isnad1 id=mem.1h5v.s12.600df0e6a2e1 from=translated src=- shape=ed25e62a vocab=9fe20533
-/
theorem inv_mem_T {s : LaurentSeries L} (hs : s ∈ T b F₀) : s⁻¹ ∈ T b F₀ := by
  classical
  letI := modF₀ F₀ (L := L)
  by_cases hs0 : s = 0
  · rw [hs0, inv_zero]; exact Submodule.zero_mem _

  letI instT : Module ↥F₀ ↥(T b F₀) := (T b F₀).module
  haveI : FiniteDimensional ↥F₀ ↥(T b F₀) := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  let m : ↥(T b F₀) →ₗ[↥F₀] ↥(T b F₀) :=
    { toFun := fun x => ⟨s * x, mul_mem_T b F₀ hs x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add _ _ _)
      map_smul' := fun a x => by
        apply Subtype.ext
        show s * (coeffEmb L (a : LaurentSeries ℚ) * (x : LaurentSeries L)) =
          coeffEmb L (a : LaurentSeries ℚ) * (s * x)
        ring }
  have hinj : Function.Injective m := by
    intro x y hxy
    have : s * x = s * y := congrArg (fun z : ↥(T b F₀) => (z : LaurentSeries L)) hxy
    exact Subtype.ext (mul_left_cancel₀ hs0 this)
  obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinj ⟨1, one_mem_T b F₀⟩
  have hx' : s * x = 1 := congrArg (fun z : ↥(T b F₀) => (z : LaurentSeries L)) hx
  rw [inv_eq_of_mul_eq_one_right hx']
  exact x.2

/--
@isnad1 id=ex.0h4v.s11.4cd713b4d1df from=translated src=- shape=e6bc9038 vocab=5456cef2
-/
theorem exists_intermediateField : ∃ S : IntermediateField L (LaurentSeries L), (S : Set (LaurentSeries L)) = T b F₀ := by
  letI := modF₀ F₀ (L := L)
  refine ⟨{ carrier := T b F₀, mul_mem' := mul_mem_T b F₀, one_mem' := one_mem_T b F₀,
            add_mem' := fun hx hy => Submodule.add_mem _ hx hy, zero_mem' := Submodule.zero_mem _,
            algebraMap_mem' := fun ℓ => by rw [algebraMap_eq_C]; exact C_mem_T b F₀ ℓ,
            inv_mem' := fun _ hx => inv_mem_T b F₀ hx }, rfl⟩

/--
@isnad1 id=eq.0h4v.s10.bd7e2506c6d4 from=translated src=- shape=a261e1ea vocab=db97fb50
-/
theorem laurentBaseChange_eq : (laurentBaseChange L F₀ : Set (LaurentSeries L)) = T b F₀ := by
  letI := modF₀ F₀ (L := L)
  obtain ⟨S, hS⟩ := exists_intermediateField b F₀
  apply le_antisymm
  ·
    have hle : laurentBaseChange L F₀ ≤ S := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [hS]

      have h1 := Submodule.smul_mem (T b F₀) (⟨x, hx⟩ : ↥F₀) (one_mem_T b F₀)
      rw [smul_def', mul_one] at h1
      exact h1
    intro f hf
    have := hle hf
    rwa [← SetLike.mem_coe, hS] at this
  ·
    intro f hf
    rw [SetLike.mem_coe, mem_T_iff] at hf
    obtain ⟨h, rfl⟩ := hf
    refine IntermediateField.sum_mem _ fun i _ => ?_
    rw [← HahnSeries.C_mul_eq_smul, ← algebraMap_eq_C]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (coeffEmb_mem_laurentBaseChange L (h i).2)

end SpanE96
open scoped _root_.P2MW.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb.SpanE96

/--
@isnad1 id=iff.0h5v.s10.bed9c1792b16 from=translated src=- shape=2b314c24 vocab=2b7f8b1f
-/
theorem solution
    (L : Type) [Field L] [CharZero L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ L)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (f : LaurentSeries L) :
    f ∈ ModularCurve.laurentBaseChange L F₀ ↔
      ∃ h : ι → ↥F₀, f = ∑ i, (b i) • ModularCurve.coeffEmb L ((h i : ↥F₀) : LaurentSeries ℚ) := by
  have h := SpanE96.laurentBaseChange_eq b F₀
  rw [← SetLike.mem_coe, h]
  exact SpanE96.mem_T_iff b F₀ f
