/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Complex.Schwarz
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Topology
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.LanaOka.Oka.Uniformization.Cayley

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic automorphisms of the upper half-plane

A bijection `T : ℍ → ℍ` which is holomorphic together with its inverse is a Möbius transformation
`τ ↦ g • τ` with `g ∈ SL(2, ℝ)` (`Uniformization.exists_SL2R_eq_of_holomorphic`).

Proof: move `T i` back to `i` by an element of `SL(2, ℝ)`; conjugated by the Cayley map the result
is a holomorphic bijection of the unit disc fixing `0`, so by the Schwarz lemma applied to it and
to its inverse it preserves `|w|`, and by the equality case of the Schwarz lemma it is a rotation
`w ↦ u w`. The rotation is the Cayley conjugate of `[[c, s], [-s, c]]` with `(c + i s)² = u`.

Holomorphy of a map `F : ℍ → ℍ` is expressed as holomorphy of `z ↦ F (ofComplex z)` on
`{z | 0 < z.im}`.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

/-- A map `ℍ → ℍ` is holomorphic if it is holomorphic as a map on `{z | 0 < z.im}`. -/
def HolomorphicH (F : ℍ → ℍ) : Prop :=
  DifferentiableOn ℂ (fun z ↦ (F (ofComplex z) : ℂ)) {z | 0 < z.im}

theorem coe_SL2R_smul (g : SL(2, ℝ)) (τ : ℍ) :
    ((g • τ : ℍ) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / ((g 1 0 : ℂ) * τ + g 1 1) := by
  rw [coe_specialLinearGroup_apply]; rfl

theorem denom_SL2R_ne_zero (g : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    (g 1 0 : ℂ) * z + g 1 1 ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) ⟨z, hz⟩
  simpa [UpperHalfPlane.denom] using this

theorem ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

theorem HolomorphicH.smul {F : ℍ → ℍ} (hF : HolomorphicH F) (g : SL(2, ℝ)) :
    HolomorphicH fun τ ↦ g • F τ := by
  unfold HolomorphicH at *
  have : DifferentiableOn ℂ (fun z ↦ ((g 0 0 : ℂ) * (F (ofComplex z) : ℂ) + g 0 1) /
      ((g 1 0 : ℂ) * (F (ofComplex z) : ℂ) + g 1 1)) {z | 0 < z.im} :=
    (((differentiableOn_const _).mul hF).add_const _).div
      (((differentiableOn_const _).mul hF).add_const _)
      fun z _ ↦ denom_SL2R_ne_zero g (F (ofComplex z)).im_pos
  exact this.congr fun z _ ↦ coe_SL2R_smul g _

theorem HolomorphicH.comp_smul {F : ℍ → ℍ} (hF : HolomorphicH F) (g : SL(2, ℝ)) :
    HolomorphicH fun τ ↦ F (g • τ) := by
  unfold HolomorphicH at *
  have hg : DifferentiableOn ℂ (fun z ↦ ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1))
      {z | 0 < z.im} :=
    (((differentiableOn_const _).mul differentiableOn_id).add_const _).div
      (((differentiableOn_const _).mul differentiableOn_id).add_const _)
      fun z hz ↦ denom_SL2R_ne_zero g hz
  have hmaps : MapsTo (fun z ↦ ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1))
      {z | 0 < z.im} {z | 0 < z.im} := fun z hz ↦ by
    have := (g • (⟨z, hz⟩ : ℍ)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_SL2R_smul] at this
  refine (hF.comp hg hmaps).congr fun z hz ↦ ?_
  simp only [Function.comp_apply]
  congr 2
  apply UpperHalfPlane.ext
  rw [ofComplex_of_im_pos (hmaps hz), ofComplex_apply_of_im_pos hz, coe_SL2R_smul]

/-- The Cayley conjugate `w ↦ cayley (F (cayleyInv w))` of a map `F : ℍ → ℍ`. -/
noncomputable def discConj (F : ℍ → ℍ) (w : ℂ) : ℂ := cayley (F (ofComplex (cayleyInv w)))

theorem discConj_mem_ball (F : ℍ → ℍ) (w : ℂ) : discConj F w ∈ ball (0 : ℂ) 1 :=
  cayley_mem_ball (F _).im_pos

theorem differentiableOn_discConj {F : ℍ → ℍ} (hF : HolomorphicH F) :
    DifferentiableOn ℂ (discConj F) (ball 0 1) :=
  (differentiableOn_cayley.comp (hF.comp differentiableOn_cayleyInv fun _ hw ↦ im_cayleyInv_pos hw)
    fun z _ ↦ (F (ofComplex (cayleyInv z))).im_pos : _)

theorem cayleyInv_zero : cayleyInv 0 = I := by simp [cayleyInv]

theorem cayley_I : cayley I = 0 := by simp [cayley]

theorem discConj_comp {F G : ℍ → ℍ} (w : ℂ) :
    discConj F (discConj G w) = discConj (F ∘ G) w := by
  unfold discConj
  rw [cayleyInv_cayley (G _).im_pos]
  simp only [Function.comp_apply]
  congr 3
  exact ofComplex_apply _

theorem discConj_id {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : discConj id w = w := by
  unfold discConj
  simp only [id]
  rw [ofComplex_of_im_pos (im_cayleyInv_pos hw), cayley_cayleyInv hw]

/-- The rotation matrix with first row `(c, s)` where `c + i s = e`, `|e| = 1`. -/
noncomputable def rot (e : ℂ) (he : ‖e‖ = 1) : SL(2, ℝ) :=
  ⟨!![e.re, e.im; -e.im, e.re], by
    rw [Matrix.det_fin_two_of]
    have := Complex.sq_norm e
    rw [he, normSq_apply] at this
    nlinarith⟩

theorem cayley_rot_smul (e : ℂ) (he : ‖e‖ = 1) (τ : ℍ) :
    cayley ((rot e he • τ : ℍ) : ℂ) = e ^ 2 * cayley τ := by
  have hsq : e.re ^ 2 + e.im ^ 2 = 1 := by
    have := Complex.sq_norm e; rw [he, normSq_apply] at this; nlinarith
  have hcoe : ((rot e he • τ : ℍ) : ℂ) =
      ((e.re : ℂ) * τ + e.im) / (-(e.im : ℂ) * τ + e.re) := by
    rw [coe_SL2R_smul]; simp [rot]
  have hden : -(e.im : ℂ) * τ + e.re ≠ 0 := by
    have := denom_SL2R_ne_zero (rot e he) τ.im_pos
    simpa [rot] using this
  have hτI := add_I_ne_zero τ.im_pos
  have hconj : ((e.re : ℂ) - e.im * I) * e = 1 := by
    apply Complex.ext <;> simp [mul_re, mul_im] <;> nlinarith [hsq]
  have hnum : (e.re : ℂ) * τ + e.im - (-(e.im : ℂ) * τ + e.re) * I = e * (τ - I) := by
    apply Complex.ext <;> simp [mul_re, mul_im] <;> ring
  have hden2 : (e.re : ℂ) * τ + e.im + I * (-(e.im : ℂ) * τ + e.re) =
      ((e.re : ℂ) - e.im * I) * (τ + I) := by
    apply Complex.ext <;> simp [mul_re, mul_im] <;> ring
  have hc : ((e.re : ℂ) - e.im * I) = e⁻¹ := eq_inv_of_mul_eq_one_left hconj
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  rw [hcoe, cayley, cayley, div_sub' hden, div_add' _ _ _ hden, div_div_div_cancel_right₀ hden,
    hnum, hden2, hc]
  field_simp

/-- **Holomorphic automorphisms of `ℍ` are Möbius maps.** A bijection `T` of `ℍ`, holomorphic with
holomorphic inverse `S`, is `τ ↦ g • τ` for some `g ∈ SL(2, ℝ)`. -/
theorem exists_SL2R_eq_of_holomorphic {T S : ℍ → ℍ} (hT : HolomorphicH T) (hS : HolomorphicH S)
    (hTS : ∀ τ, T (S τ) = τ) (hST : ∀ τ, S (T τ) = τ) : ∃ g : SL(2, ℝ), ∀ τ, T τ = g • τ := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq SL(2, ℝ) (T UpperHalfPlane.I) UpperHalfPlane.I
  set F : ℍ → ℍ := fun τ ↦ g₀ • T τ
  set Fi : ℍ → ℍ := fun τ ↦ S (g₀⁻¹ • τ)
  have hFFi : F ∘ Fi = id := by funext τ; simp [F, Fi, hTS]
  have hFiF : Fi ∘ F = id := by funext τ; simp [F, Fi, hST]
  have hF : HolomorphicH F := hT.smul g₀
  have hFi : HolomorphicH Fi := hS.comp_smul g₀⁻¹
  set G := discConj F
  set H := discConj Fi
  have hofI : (ofComplex (cayleyInv 0) : ℍ) = UpperHalfPlane.I := by
    rw [cayleyInv_zero]; exact ofComplex_apply UpperHalfPlane.I
  have hG0 : G 0 = 0 := by
    change cayley (F (ofComplex (cayleyInv 0))) = 0
    rw [hofI]; simp only [F, hg₀]; exact cayley_I
  have hH0 : H 0 = 0 := by
    change cayley (Fi (ofComplex (cayleyInv 0))) = 0
    rw [hofI]
    have : g₀⁻¹ • UpperHalfPlane.I = T UpperHalfPlane.I := by rw [inv_smul_eq_iff, hg₀]
    simp only [Fi, this, hST]; exact cayley_I
  have hHG : ∀ w ∈ ball (0 : ℂ) 1, H (G w) = w := fun w hw ↦ by
    change discConj Fi (discConj F w) = w
    rw [discConj_comp, hFiF, discConj_id hw]
  have hmaps : ∀ K : ℍ → ℍ, MapsTo (discConj K) (ball 0 1) (closedBall 0 1) :=
    fun K w _ ↦ ball_subset_closedBall (discConj_mem_ball K w)
  have hGle : ∀ w ∈ ball (0 : ℂ) 1, ‖G w‖ ≤ ‖w‖ := fun w hw ↦
    Complex.norm_le_norm_of_mapsTo_ball (differentiableOn_discConj hF) (hmaps F) hG0
      (mem_ball_zero_iff.mp hw)
  have hHle : ∀ w ∈ ball (0 : ℂ) 1, ‖H w‖ ≤ ‖w‖ := fun w hw ↦
    Complex.norm_le_norm_of_mapsTo_ball (differentiableOn_discConj hFi) (hmaps Fi) hH0
      (mem_ball_zero_iff.mp hw)
  have hGnorm : ∀ w ∈ ball (0 : ℂ) 1, ‖G w‖ = ‖w‖ := fun w hw ↦ le_antisymm (hGle w hw) (by
    have := hHle (G w) (discConj_mem_ball F w)
    rwa [hHG w hw] at this)
  -- `G` is a rotation
  have hhalf : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; norm_num
  set u := dslope G 0 (1 / 2)
  have hu : ‖u‖ = 1 := by
    simp only [u]
    rw [dslope_of_ne _ (by norm_num), slope_def_field, hG0, sub_zero, sub_zero, norm_div,
      hGnorm _ hhalf]
    norm_num
  have hGu : ∀ w ∈ ball (0 : ℂ) 1, G w = w * u := by
    intro w hw
    have := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div (R₁ := 1) (R₂ := 1)
      (differentiableOn_discConj hF)
      (by change MapsTo G _ (closedBall (G 0) 1); rw [hG0]; exact hmaps F) hhalf
      (by change ‖u‖ = 1 / 1; rw [hu]; norm_num) hw
    change G w = _ at this
    rw [this]
    change G 0 + (w - 0) • u = w * u
    rw [hG0]; simp [smul_eq_mul]
  -- the rotation matrix
  set e : ℂ := u ^ ((2 : ℕ) : ℂ)⁻¹
  have he2 : e ^ 2 = u := cpow_nat_inv_pow u two_ne_zero
  have he : ‖e‖ = 1 := by
    have h1 : ‖e‖ ^ 2 = 1 := by rw [← norm_pow, he2, hu]
    nlinarith [norm_nonneg e]
  refine ⟨g₀⁻¹ * rot e he, fun τ ↦ ?_⟩
  have hFτ : F τ = rot e he • τ := by
    apply UpperHalfPlane.ext
    have h1 : cayley (F τ) = cayley ((rot e he • τ : ℍ) : ℂ) := by
      rw [cayley_rot_smul, he2]
      have : G (cayley τ) = cayley (F τ) := by
        change cayley (F (ofComplex (cayleyInv (cayley τ)))) = _
        rw [cayleyInv_cayley τ.im_pos, ofComplex_apply]
      rw [← this, hGu _ (cayley_mem_ball τ.im_pos), mul_comm]
    have := congrArg cayleyInv h1
    rwa [cayleyInv_cayley (F τ).im_pos, cayleyInv_cayley (rot e he • τ).im_pos] at this
  rw [mul_smul, ← hFτ]
  simp [F]

end Uniformization
