/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.LanaOka.Oka.Uniformization.HalfPlaneAut
import Tengoku.LanaOka.Oka.Uniformization.LatticeComplement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The deck group of `ℍ → ℂ ∖ Λ → (ℂ ∖ Λ) / Λ`

Let `ψ : ℍ → ℂ ∖ Λ` be the holomorphic universal covering of `PeriodPair.exists_uniformization`
(packaged as `Uniformization.Unif`). Every translation by a period lifts through `ψ` to a
holomorphic bijection of `ℍ`, which is a Möbius map (`exists_SL2R_eq_of_holomorphic`). So

`Γ = {g ∈ SL(2, ℝ) | ∃ l ∈ Λ, ∀ τ, ψ (g • τ) = ψ τ + l}`

is a subgroup of `SL(2, ℝ)` whose orbits are exactly the fibres of `ψ` modulo `Λ`
(`Unif.exists_mem_deckGroup`), and `Γ` acts freely modulo `±1` (`Unif.eq_one_or_neg_one`).
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

/-- A holomorphic universal covering `ℍ → ℂ ∖ Λ` (as a function on `ℂ`, restricted to `ℍ`). -/
structure Unif (L : PeriodPair) where
  /-- The covering map, as a function on `ℂ`. -/
  Ψ : ℂ → ℂ
  covering : IsCoveringMapOn (fun τ : ℍ ↦ Ψ τ) (L.lattice : Set ℂ)ᶜ
  notMem : ∀ z : ℂ, 0 < z.im → Ψ z ∉ L.lattice
  differentiableOn : DifferentiableOn ℂ Ψ {z | 0 < z.im}
  deriv_ne_zero : ∀ z : ℂ, 0 < z.im → deriv Ψ z ≠ 0
  surj : ∀ w ∉ L.lattice, ∃ τ : ℍ, Ψ τ = w

namespace Unif

variable {L : PeriodPair} (U : Unif L)

/-- The covering `ψ : ℍ → ℂ ∖ Λ`. -/
def ψ (τ : ℍ) : ℂ := U.Ψ τ

theorem ψ_notMem (τ : ℍ) : U.ψ τ ∉ L.lattice := U.notMem τ τ.im_pos

theorem continuous_ψ : Continuous U.ψ :=
  U.differentiableOn.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos

theorem add_notMem {z l : ℂ} (hz : z ∉ L.lattice) (hl : l ∈ L.lattice) : z + l ∉ L.lattice :=
  fun h ↦ hz (by simpa using sub_mem h hl)

/-- Uniqueness of lifts through `ψ` of maps out of `ℍ`. -/
theorem eq_of_comp_eq {A B : ℍ → ℍ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ τ, U.ψ (A τ) = U.ψ (B τ)) {τ₀ : ℍ} (h₀ : A τ₀ = B τ₀) : A = B := by
  obtain ⟨F, -, hF⟩ := U.covering.existsUnique_continuousMap_lifts ⟨fun τ ↦ U.ψ (A τ),
    U.continuous_ψ.comp hA⟩ (a₀ := τ₀) (e₀ := A τ₀) rfl fun τ ↦ U.ψ_notMem (A τ)
  have h1 := hF ⟨A, hA⟩ ⟨rfl, rfl⟩
  have h2 := hF ⟨B, hB⟩ ⟨h₀.symm, by funext τ; exact (h τ).symm⟩
  have := h2.trans h1.symm
  funext τ
  exact (congrArg (fun F : C(ℍ, ℍ) ↦ F τ) this).symm

/-- Translations by periods lift through `ψ`. -/
theorem exists_lift {l : ℂ} (hl : l ∈ L.lattice) (τ τ' : ℍ) (h : U.ψ τ' = U.ψ τ + l) :
    ∃ T : ℍ → ℍ, Continuous T ∧ T τ = τ' ∧ ∀ σ, U.ψ (T σ) = U.ψ σ + l := by
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := U.covering.existsUnique_continuousMap_lifts ⟨fun σ ↦ U.ψ σ + l,
    U.continuous_ψ.add continuous_const⟩ (a₀ := τ) (e₀ := τ') h
    fun σ ↦ add_notMem (U.ψ_notMem σ) hl
  exact ⟨F, F.continuous, hF0, fun σ ↦ congrFun hF σ⟩

theorem hasStrictDerivAt_Ψ {z : ℂ} (hz : 0 < z.im) : HasStrictDerivAt U.Ψ (deriv U.Ψ z) z :=
  (U.differentiableOn.analyticAt (isOpen_upper.mem_nhds hz)).hasStrictDerivAt

/-- A continuous lift of a translation is holomorphic. -/
theorem holomorphicH_of_lift {T : ℍ → ℍ} (hT : Continuous T) {l : ℂ}
    (h : ∀ σ, U.ψ (T σ) = U.ψ σ + l) : HolomorphicH T := by
  intro z hz
  have hz' : ofComplex z = ⟨z, hz⟩ := ofComplex_apply_of_im_pos hz
  refine (differentiableAt_of_comp_eq (f := U.Ψ) (g := fun w ↦ U.Ψ w + l)
    (U.hasStrictDerivAt_Ψ (T (ofComplex z)).im_pos) (U.deriv_ne_zero _ (T _).im_pos) ?_ ?_
    ?_).differentiableWithinAt
  · exact (continuous_coe.comp hT).continuousAt.comp
      (ofComplex.continuousOn.continuousAt (ofComplex.open_source.mem_nhds (by
        change z ∈ (isOpenEmbedding_coe.toOpenPartialHomeomorph _).target
        simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact ⟨⟨z, hz⟩, rfl⟩)))
  · filter_upwards [isOpen_upper.mem_nhds hz] with w hw
    have := h (ofComplex w)
    simp only [ψ] at this
    rw [this, ofComplex_of_im_pos hw]
  · exact ((U.differentiableOn.differentiableAt (isOpen_upper.mem_nhds hz)).add_const l)

/-- The deck group `Γ ⊆ SL(2, ℝ)` of `ℍ → ℂ ∖ Λ → (ℂ ∖ Λ)/Λ`. -/
def deckGroup : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ l ∈ L.lattice, ∀ τ, U.ψ (g • τ) = U.ψ τ + l}
  one_mem' := ⟨0, zero_mem _, fun τ ↦ by simp⟩
  mul_mem' := by
    rintro g h ⟨l, hl, hg⟩ ⟨m, hm, hh⟩
    exact ⟨m + l, add_mem hm hl, fun τ ↦ by rw [mul_smul, hg, hh, add_assoc]⟩
  inv_mem' := by
    rintro g ⟨l, hl, hg⟩
    exact ⟨-l, neg_mem hl, fun τ ↦ by
      have := hg (g⁻¹ • τ)
      rw [smul_inv_smul] at this
      rw [this]; ring⟩

end Unif

end Uniformization
