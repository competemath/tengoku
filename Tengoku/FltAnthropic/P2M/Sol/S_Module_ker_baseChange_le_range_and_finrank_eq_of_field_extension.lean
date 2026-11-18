import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoChartCech

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension

set_option autoImplicit false

universe u

open TensorProduct

namespace K4EDescendGood

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K] (K' : Type u) [Field K'] [Algebra R K']
  [Algebra K K'] [IsScalarTower R K K']

noncomputable def incl : K →ₗ[R] K' := (Algebra.linearMap K K').restrictScalars R

/--
@isnad1 id=ex.0h2v.s8.a44b8a55380d from=translated src=- shape=24987af7 vocab=bbd66c43
-/
theorem exists_retraction : ∃ r : K' →ₗ[K] K, r ∘ₗ Algebra.linearMap K K' = LinearMap.id := by
  apply LinearMap.exists_leftInverse_of_injective
  exact LinearMap.ker_eq_bot_of_injective (algebraMap K K').injective

variable {X Y : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/--
@isnad1 id=eq.0h7v.s11.db33e7175a26 from=translated src=- shape=87d8d557 vocab=6a7845f1
-/
theorem baseChange_j (φ : X →ₗ[R] Y) (z : K ⊗[R] X) :
    φ.baseChange K' ((incl K K').rTensor X z) = (incl K K').rTensor Y (φ.baseChange K z) := by
  show (φ.lTensor K') ((incl K K').rTensor X z) = (incl K K').rTensor Y ((φ.lTensor K) z)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

/--
@isnad1 id=eq.0h8v.s11.8bf45a8ee581 from=translated src=- shape=cb965e9f vocab=7f576c1f
-/
theorem baseChange_ρ (r : K' →ₗ[K] K) (φ : X →ₗ[R] Y) (z : K' ⊗[R] X) :
    φ.baseChange K ((r.restrictScalars R).rTensor X z) = (r.restrictScalars R).rTensor Y (φ.baseChange K' z) := by
  show (φ.lTensor K) ((r.restrictScalars R).rTensor X z) = (r.restrictScalars R).rTensor Y ((φ.lTensor K') z)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

/--
@isnad1 id=eq.1h6v.s10.9a2afc0f4561 from=translated src=- shape=ae161c0a vocab=5071f4ed
-/
theorem ρ_j (r : K' →ₗ[K] K) (hr : r ∘ₗ Algebra.linearMap K K' = LinearMap.id) (z : K ⊗[R] X) :
    (r.restrictScalars R).rTensor X ((incl K K').rTensor X z) = z := by
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have : r.restrictScalars R ∘ₗ incl K K' = LinearMap.id := by
    ext c
    exact congrArg (fun f : K →ₗ[K] K => f c) hr
  rw [this, LinearMap.rTensor_id, LinearMap.id_apply]

/--
@isnad1 id=le.1h8v.s11.461cef6b02ff from=translated src=- shape=80467b9c vocab=1a3e0b73
-/
theorem ker_le_range_descend {Z : Type u} [AddCommGroup Z] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : LinearMap.ker (g.baseChange K') ≤ LinearMap.range (f.baseChange K')) :
    LinearMap.ker (g.baseChange K) ≤ LinearMap.range (f.baseChange K) := by
  obtain ⟨r, hr⟩ := exists_retraction K K'
  intro u hu
  rw [LinearMap.mem_ker] at hu
  have hj : (incl K K').rTensor Y u ∈ LinearMap.ker (g.baseChange K') := by
    rw [LinearMap.mem_ker, baseChange_j, hu, map_zero]
  obtain ⟨v, hv⟩ := h hj
  refine ⟨(r.restrictScalars R).rTensor X v, ?_⟩
  rw [baseChange_ρ, hv, ρ_j K K' r hr]

/--
@isnad1 id=eq.0h7v.s13.4d37f27a9417 from=translated src=- shape=fa90508a vocab=27575eda
-/
theorem cancelBaseChange_baseChange_baseChange (φ : X →ₗ[R] Y) (z : K' ⊗[K] (K ⊗[R] X)) :
    AlgebraTensorModule.cancelBaseChange R K K' K' Y (((φ.baseChange K).baseChange K') z) =
      (φ.baseChange K') (AlgebraTensorModule.cancelBaseChange R K K' K' X z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]
    | add y₁ y₂ h₁ h₂ => simp only [tmul_add, map_add, h₁, h₂]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

omit [Algebra R K] [Algebra R K'] [IsScalarTower R K K'] in
/--
@isnad1 id=eq.0h3v.s7.4104078aa180 from=translated src=- shape=510a70f4 vocab=7827525a
-/
theorem finrank_baseChange_field (V : Type u) [AddCommGroup V] [Module K V] :
    Module.finrank K' (K' ⊗[K] V) = Module.finrank K V :=
  Module.finrank_baseChange

/--
@isnad1 id=eq.0h6v.s11.e4c70054e153 from=translated src=- shape=0848776b vocab=77fc797c
-/
theorem finrank_ker_descend (φ : X →ₗ[R] Y) :
    Module.finrank K' (LinearMap.ker (φ.baseChange K')) = Module.finrank K (LinearMap.ker (φ.baseChange K)) := by
  set eX := AlgebraTensorModule.cancelBaseChange R K K' K' X
  set eY := AlgebraTensorModule.cancelBaseChange R K K' K' Y
  set A := (φ.baseChange K).baseChange K'
  set B := φ.baseChange K'
  have key : B ∘ₗ eX.toLinearMap = eY.toLinearMap ∘ₗ A := by
    apply LinearMap.ext; intro z
    exact (cancelBaseChange_baseChange_baseChange K K' φ z).symm
  have hmap : (LinearMap.ker A).map eX.toLinearMap = LinearMap.ker B := by
    have h1 : LinearMap.ker A = (LinearMap.ker B).comap eX.toLinearMap := by
      rw [← LinearMap.ker_comp, key, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
    rw [h1, Submodule.map_comap_eq_of_surjective eX.surjective]
  have e1 : LinearMap.ker A ≃ₗ[K'] LinearMap.ker B := LinearEquiv.ofSubmodules eX _ _ hmap
  have e2 : K' ⊗[K] LinearMap.ker (φ.baseChange K) ≃ₗ[K'] LinearMap.ker A :=
    LinearMap.tensorKerEquiv K' K' (φ.baseChange K)
  rw [← e1.finrank_eq, ← e2.finrank_eq]
  exact finrank_baseChange_field K K' (LinearMap.ker (φ.baseChange K))

end K4EDescendGood

open K4EDescendGood in
/--
@isnad1 id=and.3h8v.s13.35b6d9278935 from=translated src=- shape=df93058d vocab=47c9cc59
-/
theorem solution
    {R : Type u} [CommRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1))
    {F : Type u} [AddCommGroup F] [Module R F] (Θ : F →ₗ[R] C 0)
    (K : Type u) [Field K] [Algebra R K] (K' : Type u) [Field K'] [Algebra R K'] [Algebra K K']
    [IsScalarTower R K K'] (r : ℕ)
    (h1 : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K') ≤ LinearMap.range ((d i).baseChange K'))
    (h2 : LinearMap.ker ((d 0).baseChange K') ≤ LinearMap.range (Θ.baseChange K'))
    (h3 : Module.finrank K' (LinearMap.ker ((d 0).baseChange K')) = r) :
    (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) ∧
    LinearMap.ker ((d 0).baseChange K) ≤ LinearMap.range (Θ.baseChange K) ∧
    Module.finrank K (LinearMap.ker ((d 0).baseChange K)) = r := by
  refine ⟨fun i => ker_le_range_descend K K' (d i) (d (i + 1)) (h1 i),
    ker_le_range_descend K K' Θ (d 0) h2, ?_⟩
  rw [← finrank_ker_descend K K' (d 0), h3]
