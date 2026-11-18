import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField open _root_.NumberField.AdelicFourier open _root_.IsDedekindDomain
open scoped Classical SchwartzMap

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (pureTensorSet schwartzBruhat mem_schwartzBruhat_of_mem_pureTensorSet zero_mem_schwartzBruhat schwartzBruhat_induction)
namespace D2cPrime
open _root_.NumberField.AdelicFourier open _root_.NumberField

def mulLeftCLE {A : Type*} [CommRing A] [Algebra ℝ A] [TopologicalSpace A] [ContinuousMul A]
    (c c' : A) (h : c' * c = 1) : A ≃L[ℝ] A where
  toFun x := c * x
  invFun x := c' * x
  map_add' x y := mul_add c x y
  map_smul' r x := by simp only [RingHom.id_apply, mul_smul_comm]
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def mulLeftHomeomorph {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousMul A]
    (c c' : A) (h : c' * c = 1) : A ≃ₜ A where
  toFun x := c * x
  invFun x := c' * x
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

variable (F : Type) [Field F] [NumberField F]

theorem comp_mul_mem_pureTensorSet_impl (y : (AdeleRing (𝓞 F) F)ˣ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (↑y * x)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  have hyinv : (↑y⁻¹ : AdeleRing (𝓞 F) F) * ↑y = 1 := y.inv_mul

  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F (↑y : AdeleRing (𝓞 F) F).1 with hc
  set c' := InfiniteAdeleRing.ringEquiv_mixedSpace F (↑y⁻¹ : AdeleRing (𝓞 F) F).1 with hc'
  have hcc : c' * c = 1 := by
    rw [hc, hc', ← map_mul]
    have h1 : (↑y⁻¹ : AdeleRing (𝓞 F) F).1 * (↑y : AdeleRing (𝓞 F) F).1
        = (1 : AdeleRing (𝓞 F) F).1 := congrArg Prod.fst hyinv
    rw [h1]; exact map_one _
  let M := mulLeftCLE c c' hcc
  let g' : 𝓢(mixedEmbedding.mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g
  have hg' : ∀ v, g' v = g (c * v) := fun v => by
    show (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g) v = _
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]; rfl

  set d := (↑y : AdeleRing (𝓞 F) F).2 with hd
  set d' := (↑y⁻¹ : AdeleRing (𝓞 F) F).2 with hd'
  have hdd : d' * d = 1 := congrArg Prod.snd hyinv
  let Φ := mulLeftHomeomorph d d' hdd
  have hΦ : (fun z => h (d * z)) = h ∘ Φ := rfl
  refine ⟨g', fun z => h (d * z), hlc.comp_continuous (continuous_const.mul continuous_id),
    by rw [hΦ]; exact hcs.comp_homeomorph Φ, ?_⟩
  funext x
  have h1 : (↑y * x : AdeleRing (𝓞 F) F).1 = (↑y : AdeleRing (𝓞 F) F).1 * x.1 := rfl
  have h2 : (↑y * x : AdeleRing (𝓞 F) F).2 = d * x.2 := rfl
  show g (InfiniteAdeleRing.ringEquiv_mixedSpace F (↑y * x : AdeleRing (𝓞 F) F).1)
      * h (↑y * x : AdeleRing (𝓞 F) F).2
    = g' (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h (d * x.2)
  rw [h1, h2, map_mul, hg']

theorem comp_mul_mem_schwartzBruhat_impl (y : (AdeleRing (𝓞 F) F)ˣ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x ↦ f (↑y * x)) ∈ schwartzBruhat F := by
  refine schwartzBruhat_induction (F := F)
    (p := fun f _ => (fun x ↦ f (↑y * x)) ∈ schwartzBruhat F) ?_ ?_ ?_ ?_ hf
  · intro f hf
    exact mem_schwartzBruhat_of_mem_pureTensorSet (comp_mul_mem_pureTensorSet_impl F y hf)
  · exact zero_mem_schwartzBruhat
  · intro f g _ _ hf hg
    exact Submodule.add_mem _ hf hg
  · intro c f _ hf
    exact Submodule.smul_mem _ c hf

end NumberField.AdelicFourier.D2cPrime

end

open _root_.NumberField open _root_.P2MW.S_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat.NumberField open _root_.NumberField.AdelicFourier open _root_.P2MW.S_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat.NumberField.AdelicFourier

theorem solution
    (F : Type) [Field F] [NumberField F] (y : (AdeleRing (𝓞 F) F)ˣ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x ↦ f (↑y * x)) ∈ schwartzBruhat F :=
  NumberField.AdelicFourier.D2cPrime.comp_mul_mem_schwartzBruhat_impl F y hf

