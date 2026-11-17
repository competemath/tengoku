import Tengoku.Seed.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Tengoku.Seed.NumberTheory.ModularForms.Discriminant
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups
import Tengoku.Seed.Analysis.Meromorphic.NormalForm
import Tengoku.Seed.Geometry.Manifold.Notation
import Tengoku.FltAnthropic.Theorems.Thm_WLight_exists_analyticOnNhd_div_of_monicRel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WLight_exists_mdifferentiable_div_of_monicRel.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WLight_exists_mdifferentiable_div_of_monicRel

set_option autoImplicit false

noncomputable section

open _root_.Complex open _root_.Real open _root_.UpperHalfPlane open _root_.ModularForm open _root_.Polynomial open _root_.Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace WLight
export _root_.WLight (exists_analyticOnNhd_div_of_monicRel)
open _root_.WLight

section ValuationEngine

end ValuationEngine

section HBridge

lemma analyticOnNhd_comp_ofComplex {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet

lemma mdifferentiable_of_analyticOnNhd {f : ℍ → ℂ}
    (hf : AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  UpperHalfPlane.mdifferentiable_iff.mpr hf.differentiableOn

end HBridge

end WLight

open _root_.WLight _root_.P2MW.S_WLight_exists_mdifferentiable_div_of_monicRel.WLight in

theorem solution {a b : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hahol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a) (hbhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b)
    (hb0 : b ≠ 0) (hc : ∀ k < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c k))
    (hrel : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) :
    ∃ F : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ F * b = a := by
  obtain ⟨τ₀, hτ₀⟩ := Function.ne_iff.mp hb0
  have hrelH : ∀ τ : ℍ, a τ ^ d
      + ∑ k ∈ Finset.range d, c k τ * b τ ^ (d - k) * a τ ^ k = 0 := by
    intro τ
    simpa only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply,
      Pi.zero_apply] using congrFun hrel τ
  let a' := a ∘ ofComplex
  let b' := b ∘ ofComplex
  let c' := fun k ↦ (c k) ∘ ofComplex
  have hrel' : Set.EqOn (a' ^ d + ∑ k ∈ Finset.range d, c' k * b' ^ (d - k) * a' ^ k) 0
      upperHalfPlaneSet := by
    intro z hz
    simp only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply,
      a', b', c', comp_ofComplex_of_im_pos _ z hz]
    exact hrelH ⟨z, hz⟩
  obtain ⟨H', hH'an, hH'eq⟩ := exists_analyticOnNhd_div_of_monicRel isOpen_upperHalfPlaneSet
    (convex_halfSpace_im_gt 0).isPreconnected (analyticOnNhd_comp_ofComplex hahol)
    (analyticOnNhd_comp_ofComplex hbhol)
    ⟨(τ₀ : ℂ), τ₀.im_pos, by
      simpa [b', comp_ofComplex_of_im_pos b _ τ₀.im_pos] using hτ₀⟩
    (fun k hk ↦ analyticOnNhd_comp_ofComplex (hc k hk)) hrel'
  have hHmem : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ H' ↑τ) := by
    apply mdifferentiable_of_analyticOnNhd
    refine AnalyticOnNhd.congr isOpen_upperHalfPlaneSet hH'an (fun z hz ↦ ?_)
    exact (comp_ofComplex_of_im_pos (fun τ : ℍ ↦ H' ↑τ) z hz).symm
  refine ⟨fun τ ↦ H' ↑τ, hHmem, ?_⟩
  funext τ
  have heq := hH'eq τ.im_pos
  simp only [Pi.mul_apply, Function.comp_apply, ofComplex_apply] at heq
  show H' ↑τ * b τ = a τ
  rw [mul_comm]
  exact heq.symm
