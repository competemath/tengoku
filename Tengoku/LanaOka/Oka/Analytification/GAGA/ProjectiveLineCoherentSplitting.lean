/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytification.GAGA.ProjectiveLineBundle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The splitting `h = s₀ - zᵏ g t(z⁻¹)` for the cover of `ℙ¹` by two discs of arbitrary radii

`Complex.ProjectiveLineBundle.exists_vanishing` solves `h = s₀ - wᵏ g t(w⁻¹)` for the cover of
`ℙ¹` by the discs `{‖w‖ < ρ}` and `{‖w⁻¹‖ < ρ}`, `ρ > 1`. Rescaling the coordinate by `l > 0`,
we obtain the same statement for the cover by `{‖z‖ < l ρ}` and `{‖z⁻¹‖ < ρ / l}`, whose
intersection is the annulus `{l / ρ < ‖z‖ < l ρ}`
(`Complex.ProjectiveLineBundle.exists_vanishing_scaled`), for transition functions given by
invertible matrices indexed by a finite type.
-/

open Set Filter Metric
open scoped Matrix

namespace Complex.ProjectiveLineBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The monoid homomorphism sending a matrix to the continuous linear endomorphism `v ↦ A *ᵥ v`
of `ι → ℂ`. -/
noncomputable def matCLM : Matrix ι ι ℂ →* (ι → ℂ) →L[ℂ] (ι → ℂ) where
  toFun A := LinearMap.toContinuousLinearMap (Matrix.toLin' A)
  map_one' := by ext1 v; simp
  map_mul' A B := by ext1 v; simp [Matrix.mulVec_mulVec]

@[simp]
lemma matCLM_apply (A : Matrix ι ι ℂ) (v : ι → ℂ) : matCLM A v = A *ᵥ v := by
  simp [matCLM]

lemma differentiableOn_matCLM {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {g : X → Matrix ι ι ℂ} {s : Set X} (hg : DifferentiableOn ℂ g s) :
    DifferentiableOn ℂ (fun p ↦ matCLM (g p)) s := by
  open scoped Matrix.Norms.Operator in
  let L : Matrix ι ι ℂ →ₗ[ℂ] (ι → ℂ) →L[ℂ] (ι → ℂ) :=
    { toFun := fun A ↦ matCLM A
      map_add' := fun A B ↦ by ext1 v; simp [Matrix.add_mulVec]
      map_smul' := fun c A ↦ by ext1 v; simp [Matrix.smul_mulVec] }
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap L).differentiable.comp_differentiableOn hg

/-- The annulus `{r₁⁻¹ < ‖z‖ < r₀}`, the intersection of `{‖z‖ < r₀}` and `{‖z⁻¹‖ < r₁}`. -/
def annulusSet (r₀ r₁ : ℝ) : Set ℂ := {z | r₁⁻¹ < ‖z‖ ∧ ‖z‖ < r₀}

lemma isOpen_annulusSet (r₀ r₁ : ℝ) : IsOpen (annulusSet r₀ r₁) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma mem_annulusSet_iff {l ρ : ℝ} (hl : 0 < l) {w : ℂ} :
    w ∈ annulusSet (l * ρ) (ρ / l) ↔ w / (l : ℂ) ∈ overlap ρ := by
  have hl' : ‖(l : ℂ)‖ = l := by rw [Complex.norm_real, Real.norm_of_nonneg hl.le]
  simp only [annulusSet, overlap, mem_ofPred_eq, norm_div, hl']
  rw [inv_div, lt_div_iff₀ hl, inv_mul_eq_div, div_lt_iff₀ hl, mul_comm ρ l]

variable [FiniteDimensional ℂ E]

/-- **The splitting `h = s₀ - zᵏ g t(z⁻¹)` for the cover by `{‖z‖ < l ρ}` and
`{‖z⁻¹‖ < ρ / l}`**, `l > 0`, `ρ > 1`, whose intersection is the annulus
`{l / ρ < ‖z‖ < l ρ}`. Let `g` be holomorphic with invertible matrix values on `U` times the
annulus and `K ⊆ U` compact. Then there are an open `U' ⊇ K` and `k₀` such that for all `k ≥ k₀`
and all open `W ⊆ U'`, every holomorphic `h` on `W` times the annulus is `h = s₀ - zᵏ g t(z⁻¹)`
with `s₀` holomorphic on `W × {‖z‖ < l ρ}` and `t` holomorphic on `W × {‖w‖ < ρ / l}`. -/
theorem exists_vanishing_scaled {l ρ : ℝ} (hl : 0 < l) (hρ : 1 < ρ) {U : Set E} (hU : IsOpen U)
    {g : E × ℂ → Matrix ι ι ℂ} (hg : DifferentiableOn ℂ g (U ×ˢ annulusSet (l * ρ) (ρ / l)))
    (hgu : ∀ p ∈ U ×ˢ annulusSet (l * ρ) (ρ / l), IsUnit (g p)) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ U' : Set E, IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ W ⊆ U', IsOpen W →
      ∀ h : E × ℂ → ι → ℂ, DifferentiableOn ℂ h (W ×ˢ annulusSet (l * ρ) (ρ / l)) →
      ∃ s₀ t : E × ℂ → ι → ℂ, DifferentiableOn ℂ s₀ (W ×ˢ ball 0 (l * ρ)) ∧
        DifferentiableOn ℂ t (W ×ˢ ball 0 (ρ / l)) ∧
        ∀ z ∈ W, ∀ w ∈ annulusSet (l * ρ) (ρ / l),
          h (z, w) = s₀ (z, w) - w ^ k • g (z, w) *ᵥ t (z, w⁻¹) := by
  have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
  have hscale : ∀ w : ℂ, w ∈ overlap ρ → (l : ℂ) * w ∈ annulusSet (l * ρ) (ρ / l) := by
    intro w hw
    rw [mem_annulusSet_iff hl, mul_div_cancel_left₀ _ hl0]
    exact hw
  have hmaps : MapsTo (fun p : E × ℂ ↦ (p.1, (l : ℂ) * p.2)) (U ×ˢ overlap ρ)
      (U ×ˢ annulusSet (l * ρ) (ρ / l)) := fun p hp ↦ ⟨hp.1, hscale _ hp.2⟩
  have hdiff : Differentiable ℂ (fun p : E × ℂ ↦ (p.1, (l : ℂ) * p.2)) :=
    differentiable_fst.prodMk (differentiable_snd.const_mul _)
  obtain ⟨U', hU'o, hKU', hU'U, k₀, hk₀⟩ := exists_vanishing (V := ι → ℂ) hρ hU
    (g := fun p ↦ matCLM (g (p.1, (l : ℂ) * p.2)))
    ((differentiableOn_matCLM hg).comp hdiff.differentiableOn hmaps)
    (fun p hp ↦ (hgu _ (hmaps hp)).map matCLM) hK hKU
  refine ⟨U', hU'o, hKU', hU'U, k₀, fun k hk W hWU hW h hh ↦ ?_⟩
  have hmapsW : MapsTo (fun p : E × ℂ ↦ (p.1, (l : ℂ) * p.2)) (W ×ˢ overlap ρ)
      (W ×ˢ annulusSet (l * ρ) (ρ / l)) := fun p hp ↦ ⟨hp.1, hscale _ hp.2⟩
  obtain ⟨s₀, t, hs₀, ht, hrel⟩ := hk₀ k hk W hWU hW (fun p ↦ h (p.1, (l : ℂ) * p.2))
    (hh.comp hdiff.differentiableOn hmapsW)
  refine ⟨fun p ↦ s₀ (p.1, (l : ℂ)⁻¹ * p.2), fun p ↦ ((l : ℂ) ^ k)⁻¹ • t (p.1, (l : ℂ) * p.2),
    ?_, ?_, fun z hz w hw ↦ ?_⟩
  · have hmaps₀ : MapsTo (fun p : E × ℂ ↦ (p.1, (l : ℂ)⁻¹ * p.2)) (W ×ˢ ball 0 (l * ρ))
        (W ×ˢ ball 0 ρ) := by
      intro p hp
      refine ⟨hp.1, ?_⟩
      have := hp.2
      rw [mem_ball_zero_iff] at this ⊢
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hl.le, inv_mul_eq_div,
        div_lt_iff₀ hl, mul_comm]
      exact this
    exact hs₀.comp (differentiable_fst.prodMk (differentiable_snd.const_mul _)).differentiableOn
      hmaps₀
  · have hmaps₁ : MapsTo (fun p : E × ℂ ↦ (p.1, (l : ℂ) * p.2)) (W ×ˢ ball 0 (ρ / l))
        (W ×ˢ ball 0 ρ) := by
      intro p hp
      refine ⟨hp.1, ?_⟩
      have := hp.2
      rw [mem_ball_zero_iff] at this ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl.le, ← lt_div_iff₀' hl]
      exact this
    have := (ht.comp hdiff.differentiableOn hmaps₁).const_smul ((l : ℂ) ^ k)⁻¹
    exact this
  · have hw' : w / l ∈ overlap ρ := (mem_annulusSet_iff hl).1 hw
    have := hrel z hz (w / l) hw'
    simp only [matCLM_apply] at this
    have e1 : (l : ℂ) * (w / l) = w := mul_div_cancel₀ w hl0
    have e2 : (w / l)⁻¹ = (l : ℂ) * w⁻¹ := by rw [inv_div, div_eq_mul_inv]
    rw [e1, e2] at this
    rw [this]
    change _ = s₀ (z, (l : ℂ)⁻¹ * w) - w ^ k • g (z, w) *ᵥ (((l : ℂ) ^ k)⁻¹ • t (z, (l : ℂ) * w⁻¹))
    rw [inv_mul_eq_div, Matrix.mulVec_smul, smul_smul, div_pow, div_eq_mul_inv,
      div_eq_mul_inv]

end Complex.ProjectiveLineBundle
