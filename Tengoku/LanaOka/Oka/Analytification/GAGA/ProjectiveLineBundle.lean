/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Matrix.Normed
import Tengoku.Seed.Analysis.Normed.Group.Tannery
import Tengoku.LanaOka.Oka.Analytic.Laurent.L1Holomorphic
import Tengoku.LanaOka.Oka.Analytic.Laurent.Toeplitz

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Direct images of vector bundles under `G × ℙ¹ → G`

Let `G ⊆ E` be open (e.g. a box in `ℂⁿ`) and cover `G × ℙ¹` by the charts `G × {‖w‖ < ρ}` and
`G × {‖w‖ > ρ⁻¹}` (with coordinate `w⁻¹` at infinity), `ρ > 1`, which overlap in
`G × {ρ⁻¹ < ‖w‖ < ρ}`. A holomorphic vector bundle trivialised on both charts is given by a
holomorphic transition function `g` with invertible values in `V →L[ℂ] V` on the overlap, and
`E(k)` has transition function `wᵏ g`. A section of `E(k)` over `W × ℙ¹` is a pair `(s₀, t)` of
holomorphic functions on `W × {‖w‖ < ρ}` with `s₀ (z, w) = wᵏ g (z, w) (t (z, w⁻¹))` on the
overlap (`Complex.ProjectiveLineBundle.IsSection`), and `H¹(W × ℙ¹, E(k))` is the cokernel of
`(s₀, t) ↦ s₀ - wᵏ g t(w⁻¹)`.

We prove the two finiteness statements of Grauert–Remmert for the projection `G × ℙ¹ → G`, after
shrinking `G` to a neighbourhood `G'` of a given compact set:

* **Vanishing** (`Complex.ProjectiveLineBundle.exists_vanishing`): there is `k₀` such that for
  `k ≥ k₀` and every open `W ⊆ G'`, `H¹(W × ℙ¹, E(k)) = 0`: every holomorphic `h` on the overlap
  over `W` splits as `h = s₀ - wᵏ g t(w⁻¹)`.
* **Local freeness of the direct image** (`Complex.ProjectiveLineBundle.exists_jet_equiv`): for
  `k ≥ k₀` there are `D` and a holomorphic family of idempotents `e z` of `V^D`, `z ∈ G'`, such
  that for every open `W ⊆ G'` the map sending a section `(s₀, t)` to the first `D` Taylor
  coefficients of `s₀` in `w` is a bijection from `H⁰(W × ℙ¹, E(k))` onto the holomorphic
  `c : W → V^D` with `e c = c`. This map is `𝒪(W)`-linear and compatible with restriction, so
  `π_* E(k)` is a direct summand of `𝒪^{D · dim V}` over `G'`; in particular it is locally free
  of finite rank, hence coherent.

The proof expands everything in Laurent series in `w` with coefficients in weighted `ℓ¹` spaces
(`Laurent.L1`), where the Čech differential becomes a Toeplitz-type operator. For `k ≫ 0` it has
an explicit right inverse and for `m ≪ 0` the differential of `E(m)` has an explicit left inverse
(`Oka/Analytic/Laurent/Toeplitz.lean`); both are given by Neumann series and depend
holomorphically on the base point (`Laurent.L1.differentiableOn_toL1`).

## Main definitions

- `Complex.ProjectiveLineBundle.overlap ρ`: the annulus `{ρ⁻¹ < ‖w‖ < ρ}`.
- `Complex.ProjectiveLineBundle.IsSection`: sections of `E(k)` over `W × ℙ¹`.
- `Complex.ProjectiveLineBundle.jet`: the first `D` Taylor coefficients in `w`.

## Main results

- `Complex.ProjectiveLineBundle.exists_extend`: a solution of `h = s₀ - wᵏ g t(w⁻¹)` on a smaller
  cover extends to the given one.
- `Complex.ProjectiveLineBundle.exists_vanishing`: `R¹π_* E(k) = 0` for `k ≫ 0`.
- `Complex.ProjectiveLineBundle.exists_jet_equiv`: `π_* E(k)` is a direct summand of a free
  module of finite rank, for `k ≫ 0`.
- `Complex.ProjectiveLineBundle.exists_vanishing_matrix`,
  `Complex.ProjectiveLineBundle.exists_jet_equiv_matrix`: the versions for transition functions
  given by invertible matrices.
-/

open Set Filter Metric
open scoped Topology

namespace Complex.ProjectiveLineBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The annulus `{ρ⁻¹ < ‖w‖ < ρ}`, the overlap of the charts `{‖w‖ < ρ}` and `{‖w‖ > ρ⁻¹}` of
`ℙ¹`. -/
def overlap (ρ : ℝ) : Set ℂ := {w | ρ⁻¹ < ‖w‖ ∧ ‖w‖ < ρ}

lemma isOpen_overlap (ρ : ℝ) : IsOpen (overlap ρ) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma overlap_eq_annulus {ρ : ℝ} (hρ : 0 < ρ) :
    overlap ρ = Laurent.annulus ρ⁻¹ (ENNReal.ofReal ρ) := by
  ext w
  rw [Laurent.mem_annulus, Laurent.enorm_lt_iff_ofReal_lt, ENNReal.ofReal_lt_ofReal_iff hρ]
  rfl

lemma ne_zero_of_mem_overlap {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : w ∈ overlap ρ) : w ≠ 0 :=
  norm_pos_iff.1 ((inv_pos.2 hρ).trans hw.1)

lemma inv_mem_overlap {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : w ∈ overlap ρ) : w⁻¹ ∈ overlap ρ := by
  have hw0 : 0 < ‖w‖ := (inv_pos.2 hρ).trans hw.1
  refine ⟨?_, ?_⟩
  · rw [norm_inv]
    exact inv_strictAnti₀ hw0 hw.2
  · rw [norm_inv]
    exact (inv_lt_comm₀ hρ hw0).1 hw.1

variable (ρ : ℝ) (g : E × ℂ → V →L[ℂ] V) (k : ℕ) (W : Set E)

/-- `(s₀, t)` is a section of `E(k)` over `W × ℙ¹`, where `E` is the bundle with transition
function `g` from the chart at infinity (coordinate `w⁻¹`, component `t`) to the chart at `0`
(coordinate `w`, component `s₀`): `s₀` and `t` are holomorphic on `W × {‖w‖ < ρ}` and
`s₀ (z, w) = wᵏ • g (z, w) (t (z, w⁻¹))` on the overlap. -/
def IsSection (s₀ t : E × ℂ → V) : Prop :=
  DifferentiableOn ℂ s₀ (W ×ˢ ball 0 ρ) ∧ DifferentiableOn ℂ t (W ×ˢ ball 0 ρ) ∧
    ∀ z ∈ W, ∀ w ∈ overlap ρ, s₀ (z, w) = w ^ k • g (z, w) (t (z, w⁻¹))

variable {ρ g k W}

lemma inverse_apply_apply {A : V →L[ℂ] V} (hA : IsUnit A) (v : V) : Ring.inverse A (A v) = v := by
  change (Ring.inverse A * A) v = v
  rw [Ring.inverse_mul_cancel _ hA]
  rfl

lemma apply_inverse_apply {A : V →L[ℂ] V} (hA : IsUnit A) (v : V) : A (Ring.inverse A v) = v := by
  change (A * Ring.inverse A) v = v
  rw [Ring.mul_inverse_cancel _ hA]
  rfl

/-! ### Extension from a smaller cover -/

section Extend

variable [CompleteSpace V]

/-- A solution of `h = s₀ - wᵏ g t(w⁻¹)` for the cover of `ℙ¹` by `{‖w‖ < σ}` and `{‖w‖ > σ⁻¹}`
extends to a solution for the cover by `{‖w‖ < ρ}` and `{‖w‖ > ρ⁻¹}`, `1 < σ < ρ`. -/
theorem exists_extend {σ : ℝ} (hσ : 1 < σ) (hσρ : σ < ρ) (hW : IsOpen W)
    (hg : DifferentiableOn ℂ g (W ×ˢ overlap ρ)) (hgu : ∀ p ∈ W ×ˢ overlap ρ, IsUnit (g p))
    {h s₀ t : E × ℂ → V} (hh : DifferentiableOn ℂ h (W ×ˢ overlap ρ))
    (hs : DifferentiableOn ℂ s₀ (W ×ˢ ball 0 σ)) (ht : DifferentiableOn ℂ t (W ×ˢ ball 0 σ))
    (hrel : ∀ z ∈ W, ∀ w ∈ overlap σ, h (z, w) = s₀ (z, w) - w ^ k • g (z, w) (t (z, w⁻¹))) :
    ∃ s₀' t' : E × ℂ → V, DifferentiableOn ℂ s₀' (W ×ˢ ball 0 ρ) ∧
      DifferentiableOn ℂ t' (W ×ˢ ball 0 ρ) ∧
      (∀ z ∈ W, ∀ w ∈ overlap ρ, h (z, w) = s₀' (z, w) - w ^ k • g (z, w) (t' (z, w⁻¹))) ∧
      ∀ z ∈ W, ∀ w ∈ ball (0 : ℂ) σ, s₀' (z, w) = s₀ (z, w) ∧ t' (z, w) = t (z, w) := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hρ0 : 0 < ρ := hσ0.trans hσρ
  have hσi : σ⁻¹ < σ := (inv_lt_one_of_one_lt₀ hσ).trans hσ
  have hρσ : ρ⁻¹ < σ⁻¹ := inv_strictAnti₀ hσ0 hσρ
  set O₂ : Set ℂ := {w | σ⁻¹ < ‖w‖ ∧ ‖w‖ < ρ}
  have hO₂ : IsOpen O₂ := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hO₂ρ : O₂ ⊆ overlap ρ := fun w hw ↦ ⟨hρσ.trans hw.1, hw.2⟩
  have hO₂0 : ∀ w ∈ O₂, w ≠ 0 := fun w hw ↦ norm_pos_iff.1 ((inv_pos.2 hσ0).trans hw.1)
  -- the inversion `(z, w) ↦ (z, w⁻¹)`
  set ι : E × ℂ → E × ℂ := fun p ↦ (p.1, p.2⁻¹)
  have hι : ∀ p ∈ W ×ˢ O₂, DifferentiableAt ℂ ι p := fun p hp ↦
    differentiableAt_fst.prodMk (differentiableAt_snd.inv (hO₂0 p.2 hp.2))
  have hιO₂ : MapsTo ι (W ×ˢ O₂) (W ×ˢ ball 0 σ) := fun p hp ↦ ⟨hp.1, by
    rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_comm₀ hσ0 ((inv_pos.2 hσ0).trans hp.2.1)).1 hp.2.1⟩
  have hιO₂' : MapsTo ι (W ×ˢ O₂) (W ×ˢ (overlap ρ ∩ ball 0 ρ)) := fun p hp ↦ by
    have hp0 : 0 < ‖p.2‖ := (inv_pos.2 hσ0).trans hp.2.1
    refine ⟨hp.1, ⟨?_, ?_⟩, ?_⟩
    · rw [norm_inv]
      exact inv_strictAnti₀ hp0 hp.2.2
    · rw [norm_inv]
      exact ((inv_lt_comm₀ hσ0 hp0).1 hp.2.1).trans hσρ
    · rw [mem_ball_zero_iff, norm_inv]
      exact ((inv_lt_comm₀ hσ0 hp0).1 hp.2.1).trans hσρ
  -- the extension of `s₀`
  set F : E × ℂ → V := fun p ↦ h p + p.2 ^ k • g p (t (ι p))
  have hF : DifferentiableOn ℂ F (W ×ˢ O₂) := by
    refine (hh.mono (prod_mono subset_rfl hO₂ρ)).add (DifferentiableOn.smul ?_ ?_)
    · exact (differentiable_snd.pow k).differentiableOn
    · refine (hg.mono (prod_mono subset_rfl hO₂ρ)).clm_apply ?_
      exact fun p hp ↦ ((ht.differentiableAt ((hW.prod isOpen_ball).mem_nhds (hιO₂ hp))).comp p
        (hι p hp)).differentiableWithinAt
  set s₀' : E × ℂ → V := fun p ↦ if ‖p.2‖ < σ then s₀ p else F p
  have hs₀'F : ∀ p ∈ W ×ˢ O₂, s₀' p = F p := by
    intro p hp
    simp only [s₀']
    split_ifs with hp'
    · have := hrel p.1 hp.1 p.2 ⟨hp.2.1, hp'⟩
      simp only [F, ι, this, sub_add_cancel]
    · rfl
  have hs₀' : DifferentiableOn ℂ s₀' (W ×ˢ ball 0 ρ) := by
    intro p hp
    by_cases hp' : ‖p.2‖ < σ
    · have hmem : W ×ˢ ball (0 : ℂ) σ ∈ 𝓝 p :=
        (hW.prod isOpen_ball).mem_nhds ⟨hp.1, mem_ball_zero_iff.2 hp'⟩
      refine ((hs.differentiableAt hmem).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hmem] with q hq
      exact ite_eq_left (mem_ball_zero_iff.1 hq.2)
    · have hpO : p ∈ W ×ˢ O₂ :=
        ⟨hp.1, hσi.trans_le (not_lt.1 hp'), mem_ball_zero_iff.1 hp.2⟩
      have hmem : W ×ˢ O₂ ∈ 𝓝 p := (hW.prod hO₂).mem_nhds hpO
      refine ((hF.differentiableAt hmem).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hmem] with q hq
      exact hs₀'F q hq
  -- the extension of `t`
  set T : E × ℂ → V := fun p ↦
    Ring.inverse (g (ι p)) ((((ι p).2) ^ k)⁻¹ • (s₀' (ι p) - h (ι p)))
  have hT : DifferentiableOn ℂ T (W ×ˢ O₂) := by
    have hginv : DifferentiableOn ℂ (fun p ↦ Ring.inverse (g p)) (W ×ˢ overlap ρ) :=
      hg.inverse hgu
    intro p hp
    have hιp := hιO₂' hp
    have hn1 : W ×ˢ overlap ρ ∈ 𝓝 (ι p) :=
      (hW.prod (isOpen_overlap ρ)).mem_nhds ⟨hιp.1, hιp.2.1⟩
    have hn2 : W ×ˢ ball (0 : ℂ) ρ ∈ 𝓝 (ι p) := (hW.prod isOpen_ball).mem_nhds ⟨hιp.1, hιp.2.2⟩
    refine DifferentiableAt.differentiableWithinAt ?_
    refine ((hginv.differentiableAt hn1).comp p (hι p hp)).clm_apply ?_
    refine DifferentiableAt.smul ?_ ?_
    · have hpw : DifferentiableAt ℂ ((fun q : E × ℂ ↦ q.2 ^ k) ∘ ι) p :=
        (differentiable_snd.pow k).differentiableAt.comp p (hι p hp)
      exact hpw.inv (pow_ne_zero _ (inv_ne_zero (hO₂0 p.2 hp.2)))
    · exact ((hs₀'.differentiableAt hn2).comp p (hι p hp)).sub
        ((hh.differentiableAt hn1).comp p (hι p hp))
  set t' : E × ℂ → V := fun p ↦ if ‖p.2‖ < σ then t p else T p
  have ht'T : ∀ p ∈ W ×ˢ O₂, t' p = T p := by
    intro p hp
    simp only [t']
    split_ifs with hp'
    · have hw : (ι p).2 ∈ overlap σ := inv_mem_overlap hσ0 ⟨hp.2.1, hp'⟩
      have hs := hrel p.1 hp.1 _ hw
      have hw0 : (ι p).2 ≠ 0 := ne_zero_of_mem_overlap hσ0 hw
      have hs₀ι : s₀' (ι p) = s₀ (ι p) := ite_eq_left hw.2
      have hu : IsUnit (g (ι p)) := hgu _ ⟨(hιO₂' hp).1, (hιO₂' hp).2.1⟩
      have e1 : s₀ (ι p) - h (ι p) = (ι p).2 ^ k • g (ι p) (t p) := by
        simp only [ι, inv_inv, Prod.mk.eta] at hs ⊢
        rw [hs, sub_sub_cancel]
      simp only [T, hs₀ι]
      rw [e1, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hw0), one_smul, inverse_apply_apply hu]
    · rfl
  have ht' : DifferentiableOn ℂ t' (W ×ˢ ball 0 ρ) := by
    intro p hp
    by_cases hp' : ‖p.2‖ < σ
    · have hmem : W ×ˢ ball (0 : ℂ) σ ∈ 𝓝 p :=
        (hW.prod isOpen_ball).mem_nhds ⟨hp.1, mem_ball_zero_iff.2 hp'⟩
      refine ((ht.differentiableAt hmem).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hmem] with q hq
      exact ite_eq_left (mem_ball_zero_iff.1 hq.2)
    · have hpO : p ∈ W ×ˢ O₂ :=
        ⟨hp.1, hσi.trans_le (not_lt.1 hp'), mem_ball_zero_iff.1 hp.2⟩
      have hmem : W ×ˢ O₂ ∈ 𝓝 p := (hW.prod hO₂).mem_nhds hpO
      refine ((hT.differentiableAt hmem).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hmem] with q hq
      exact ht'T q hq
  refine ⟨s₀', t', hs₀', ht', fun z hz w hw ↦ ?_, fun z hz w hw ↦
    ⟨ite_eq_left (mem_ball_zero_iff.1 hw), ite_eq_left (mem_ball_zero_iff.1 hw)⟩⟩
  have hw0 : w ≠ 0 := ne_zero_of_mem_overlap hρ0 hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  by_cases hw' : σ⁻¹ < ‖w‖
  · have ht'w : t' (z, w⁻¹) = t (z, w⁻¹) := ite_eq_left (by
      rw [norm_inv]
      exact (inv_lt_comm₀ hσ0 hwn).1 hw')
    rw [ht'w]
    by_cases hw'' : ‖w‖ < σ
    · rw [show s₀' (z, w) = s₀ (z, w) from ite_eq_left hw'']
      exact hrel z hz w ⟨hw', hw''⟩
    · rw [show s₀' (z, w) = F (z, w) from ite_eq_right hw'']
      simp [F, ι]
  · replace hw' := not_lt.1 hw'
    have ht'w : t' (z, w⁻¹) = T (z, w⁻¹) := ite_eq_right (by
      rw [norm_inv, not_lt]
      exact (le_inv_comm₀ hσ0 hwn).2 hw')
    have hu : IsUnit (g (z, w)) := hgu _ ⟨hz, hw⟩
    rw [ht'w]
    simp only [T, ι, inv_inv]
    rw [apply_inverse_apply hu, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hw0), one_smul,
      sub_sub_cancel]

end Extend
/-! ### Laurent series of the transition function -/

section Family

open Laurent L1

variable [FiniteDimensional ℂ V] {U : Set E}

lemma differentiableOn_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E × ℂ → F} {O : Set ℂ} (hf : DifferentiableOn ℂ f (U ×ˢ O)) {z : E} (hz : z ∈ U) :
    DifferentiableOn ℂ (fun w ↦ f (z, w)) O :=
  hf.comp ((differentiable_const z).prodMk differentiable_id).differentiableOn
    fun _ hw ↦ ⟨hz, hw⟩

lemma isRadius_overlap {ρ τ : ℝ} (hρ : 1 < ρ) (hτ : 1 < τ) (hτρ : τ < ρ) :
    IsRadius ρ⁻¹ (ENNReal.ofReal ρ) τ ∧ IsRadius ρ⁻¹ (ENNReal.ofReal ρ) τ⁻¹ := by
  have hτ0 : 0 < τ := zero_lt_one.trans hτ
  have hρ0 : 0 < ρ := hτ0.trans hτρ
  refine ⟨⟨hτ0, (inv_lt_one_of_one_lt₀ hρ).trans hτ, (ENNReal.ofReal_lt_ofReal_iff hρ0).2 hτρ⟩,
    ⟨inv_pos.2 hτ0, inv_strictAnti₀ hτ0 hτρ, (ENNReal.ofReal_lt_ofReal_iff hρ0).2
      ((inv_lt_one_of_one_lt₀ hτ).trans hρ)⟩⟩

lemma sphere_union_subset_overlap {ρ τ : ℝ} (hρ : 1 < ρ) (hτ : 1 < τ) (hτρ : τ < ρ) :
    sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹ ⊆ overlap ρ := by
  have h := isRadius_overlap hρ hτ hτρ
  rw [overlap_eq_annulus (zero_lt_one.trans hρ)]
  exact union_subset (sphere_subset_annulus h.1) (sphere_subset_annulus h.2)

variable (σ τ : ℝ) [hσ : Fact (1 ≤ σ)] (g)

/-- The Laurent series in `w` of the transition function `g (z, ·)`. -/
noncomputable def ghat (z : E) : L1 (V →L[ℂ] V) :=
  toL1 σ τ fun w ↦ g (z, w)

/-- The Laurent series in `w` of the inverse `g (z, ·)⁻¹` of the transition function. -/
noncomputable def uhat (z : E) : L1 (V →L[ℂ] V) :=
  toL1 σ τ fun w ↦ Ring.inverse (g (z, w))

variable {σ τ g}

lemma eval_ghat (hρ : 1 < ρ) (hστ : σ < τ) (hτρ : τ < ρ)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) {z : E} (hz : z ∈ U) {w : ℂ} (h₁ : σ⁻¹ ≤ ‖w‖)
    (h₂ : ‖w‖ ≤ σ) : eval σ w (ghat g σ τ z) = g (z, w) := by
  have hτ : 1 < τ := hσ.out.trans_lt hστ
  have h := isRadius_overlap hρ hτ hτρ
  refine eval_toL1 hστ ?_ h.1 h.2 h₁ h₂
  rw [← overlap_eq_annulus (zero_lt_one.trans hρ)]
  exact differentiableOn_slice hg hz

lemma eval_uhat (hρ : 1 < ρ) (hστ : σ < τ) (hτρ : τ < ρ)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p))
    {z : E} (hz : z ∈ U) {w : ℂ} (h₁ : σ⁻¹ ≤ ‖w‖) (h₂ : ‖w‖ ≤ σ) :
    eval σ w (uhat g σ τ z) = Ring.inverse (g (z, w)) := by
  have hτ : 1 < τ := hσ.out.trans_lt hστ
  have h := isRadius_overlap hρ hτ hτρ
  refine eval_toL1 hστ ?_ h.1 h.2 h₁ h₂
  rw [← overlap_eq_annulus (zero_lt_one.trans hρ)]
  exact differentiableOn_slice (hg.inverse hgu) hz

lemma mem_overlap_of_norm_eq_one (hρ : 1 < ρ) {w : ℂ} (hw : ‖w‖ = 1) : w ∈ overlap ρ :=
  ⟨hw ▸ inv_lt_one_of_one_lt₀ hρ, hw ▸ hρ⟩

lemma mulL_ghat_uhat (hρ : 1 < ρ) (hστ : σ < τ) (hτρ : τ < ρ)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p))
    {z : E} (hz : z ∈ U) (x : L1 V) :
    mulL V σ (ghat g σ τ z) (mulL V σ (uhat g σ τ z) x) = x := by
  refine eq_of_eval_eq (σ := σ) fun w hw ↦ ?_
  have h₁ : σ⁻¹ ≤ ‖w‖ := hw ▸ inv_le_one_of_one_le₀ hσ.out
  have h₂ : ‖w‖ ≤ σ := hw ▸ hσ.out
  rw [mulL, eval_conv _ h₁ h₂, eval_conv _ h₁ h₂, eval_ghat hρ hστ hτρ hg hz h₁ h₂,
    eval_uhat hρ hστ hτρ hg hgu hz h₁ h₂]
  exact apply_inverse_apply (hgu _ ⟨hz, mem_overlap_of_norm_eq_one hρ hw⟩) _

lemma mulL_uhat_ghat (hρ : 1 < ρ) (hστ : σ < τ) (hτρ : τ < ρ)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p))
    {z : E} (hz : z ∈ U) (x : L1 V) :
    mulL V σ (uhat g σ τ z) (mulL V σ (ghat g σ τ z) x) = x := by
  refine eq_of_eval_eq (σ := σ) fun w hw ↦ ?_
  have h₁ : σ⁻¹ ≤ ‖w‖ := hw ▸ inv_le_one_of_one_le₀ hσ.out
  have h₂ : ‖w‖ ≤ σ := hw ▸ hσ.out
  rw [mulL, eval_conv _ h₁ h₂, eval_conv _ h₁ h₂, eval_ghat hρ hστ hτρ hg hz h₁ h₂,
    eval_uhat hρ hστ hτρ hg hgu hz h₁ h₂]
  exact inverse_apply_apply (hgu _ ⟨hz, mem_overlap_of_norm_eq_one hρ hw⟩) _

variable [FiniteDimensional ℂ E]

lemma differentiableOn_ghat (hρ : 1 < ρ) (hστ : σ < τ) (hτρ : τ < ρ) (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) : DifferentiableOn ℂ (ghat g σ τ) U :=
  differentiableOn_toL1 (h := g) hστ hU (sphere_union_subset_overlap hρ (hσ.out.trans_lt hστ) hτρ)
    hg

lemma differentiableOn_uhat (hρ : 1 < ρ) (hστ : σ < τ) (hτρ : τ < ρ) (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p)) :
    DifferentiableOn ℂ (uhat g σ τ) U :=
  differentiableOn_toL1 (h := fun p ↦ Ring.inverse (g p)) hστ hU
    (sphere_union_subset_overlap hρ (hσ.out.trans_lt hστ) hτρ) (hg.inverse hgu)

end Family
/-! ### Uniform bounds -/

section Bounds

open Laurent L1

lemma norm_proj_toL1_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {σ τ : ℝ}
    [hσ : Fact (1 ≤ σ)] (hστ : σ < τ) {f : ℂ → F} {M : ℝ}
    (hM : ∀ ζ ∈ sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹, ‖f ζ‖ ≤ M) (S : Set ℤ) :
    ‖proj F S (toL1 σ τ f)‖ ≤ ∑' j, S.indicator (fun j ↦ M * (σ / τ) ^ j.natAbs) j := by
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hτ : 0 < τ := h0.trans hστ
  have hs : Summable fun j : ℤ ↦ M * (σ / τ) ^ j.natAbs :=
    (summable_pow_natAbs (div_nonneg h0.le hτ.le) ((div_lt_one hτ).2 hστ)).mul_left M
  rw [norm_eq_tsum]
  refine Summable.tsum_le_tsum (fun j ↦ ?_) (summable_norm _) (hs.indicator S)
  rw [proj_apply]
  by_cases hj : j ∈ S
  · rw [indicator_of_mem hj, indicator_of_mem hj]
    exact norm_toL1_apply_le hστ hM j
  · simp [hj]

lemma tendsto_tsum_indicator_Ioi {c : ℤ → ℝ} (hc : Summable c) (hc0 : ∀ j, 0 ≤ c j) :
    Tendsto (fun k : ℤ ↦ ∑' j, (Ioi k).indicator c j) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℤ))
    (f := fun k j ↦ (Ioi k).indicator c j) (g := fun _ ↦ (0 : ℝ)) hc (fun j ↦ ?_)
    (Eventually.of_forall fun k j ↦ ?_)
  · simpa using h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop j] with k hk
    rw [indicator_of_notMem (by simpa using hk)]
  · by_cases h : j ∈ Ioi k
    · rw [indicator_of_mem h, Real.norm_of_nonneg (hc0 j)]
    · rw [indicator_of_notMem h, norm_zero]
      exact hc0 j

lemma tendsto_tsum_indicator_Iic {c : ℤ → ℝ} (hc : Summable c) (hc0 : ∀ j, 0 ≤ c j) :
    Tendsto (fun m : ℤ ↦ ∑' j, (Iic m).indicator c j) atBot (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atBot : Filter ℤ))
    (f := fun m j ↦ (Iic m).indicator c j) (g := fun _ ↦ (0 : ℝ)) hc (fun j ↦ ?_)
    (Eventually.of_forall fun m j ↦ ?_)
  · simpa using h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot j] with m hm
    rw [indicator_of_notMem (by simpa using hm)]
  · by_cases h : j ∈ Iic m
    · rw [indicator_of_mem h, Real.norm_of_nonneg (hc0 j)]
    · rw [indicator_of_notMem h, norm_zero]
      exact hc0 j

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ V]

/-- After shrinking the base to a neighbourhood `U'` of a compact set, the Laurent series of the
transition function are uniformly bounded, and those of its inverse have uniformly small tails. -/
lemma exists_uniform_bounds (hρ : 1 < ρ) {U : Set E} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {σ τ : ℝ} [hσ : Fact (1 ≤ σ)] (hστ : σ < τ)
    (hτρ : τ < ρ) :
    ∃ U' : Set E, IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      (∀ z ∈ U', ‖ghat g σ τ z‖ ≤ C) ∧
      (∀ ε > 0, ∀ᶠ k : ℤ in atTop, ∀ z ∈ U', ‖proj _ (Ioi k) (uhat g σ τ z)‖ ≤ ε) ∧
      (∀ ε > 0, ∀ᶠ m : ℤ in atBot, ∀ z ∈ U', ‖proj _ (Iic m) (uhat g σ τ z)‖ ≤ ε) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have h0 : 0 < σ := zero_lt_one.trans_le hσ.out
  have hτ0 : 0 < τ := h0.trans hστ
  have hτ : 1 < τ := hσ.out.trans_lt hστ
  set S := sphere (0 : ℂ) τ ∪ sphere 0 τ⁻¹
  have hL : IsCompact (cthickening δ K ×ˢ S) :=
    hK.cthickening.prod ((isCompact_sphere _ _).union (isCompact_sphere _ _))
  have hLU : cthickening δ K ×ˢ S ⊆ U ×ˢ overlap ρ :=
    prod_mono hδU (sphere_union_subset_overlap hρ hτ hτρ)
  obtain ⟨Mg, hMg⟩ := hL.exists_bound_of_continuousOn (hg.continuousOn.mono hLU)
  obtain ⟨Mu, hMu⟩ := hL.exists_bound_of_continuousOn ((hg.inverse hgu).continuousOn.mono hLU)
  have hsub : thickening δ K ⊆ cthickening δ K := thickening_subset_cthickening δ K
  set q := σ / τ
  have hq : Summable fun j : ℤ ↦ q ^ j.natAbs :=
    summable_pow_natAbs (div_nonneg h0.le hτ0.le) ((div_lt_one hτ0).2 hστ)
  have hq0 : ∀ j : ℤ, 0 ≤ max Mu 0 * q ^ j.natAbs := fun j ↦
    mul_nonneg (le_max_right _ _) (pow_nonneg (div_nonneg h0.le hτ0.le) _)
  refine ⟨thickening δ K, isOpen_thickening, self_subset_thickening hδ K, hsub.trans hδU,
    ∑' j, (univ : Set ℤ).indicator (fun j ↦ max Mg 0 * q ^ j.natAbs) j,
    tsum_nonneg fun j ↦ indicator_nonneg (fun j _ ↦ mul_nonneg (le_max_right _ _)
      (pow_nonneg (div_nonneg h0.le hτ0.le) _)) j, fun z hz ↦ ?_, fun ε hε ↦ ?_,
    fun ε hε ↦ ?_⟩
  · have := norm_proj_toL1_le hστ (M := max Mg 0)
      (fun ζ hζ ↦ (hMg (z, ζ) ⟨hsub hz, hζ⟩).trans (le_max_left _ _)) univ
    rwa [proj_univ] at this
  · have ht := tendsto_tsum_indicator_Ioi (hq.mul_left (max Mu 0)) hq0
    filter_upwards [ht.eventually (ge_mem_nhds hε)] with k hk z hz
    exact (norm_proj_toL1_le hστ (M := max Mu 0)
      (fun ζ hζ ↦ (hMu (z, ζ) ⟨hsub hz, hζ⟩).trans (le_max_left _ _)) _).trans hk
  · have ht := tendsto_tsum_indicator_Iic (hq.mul_left (max Mu 0)) hq0
    filter_upwards [ht.eventually (ge_mem_nhds hε)] with m hm z hz
    exact (norm_proj_toL1_le hστ (M := max Mu 0)
      (fun ζ hζ ↦ (hMu (z, ζ) ⟨hsub hz, hζ⟩).trans (le_max_left _ _)) _).trans hm

omit [FiniteDimensional ℂ E] in
/-- The value of the Čech differential at `w` on a pair `(a, b)` of Laurent series without terms
of negative, resp. positive, degree. -/
lemma eval_phi (hρ : 1 < ρ) {U : Set E} (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ))
    {σ τ : ℝ} [hσ : Fact (1 ≤ σ)] (hστ : σ < τ) (hτρ : τ < ρ) {z : E} (hz : z ∈ U)
    {x : L1 V × L1 V} (h₁ : proj V (Ici 0) x.1 = x.1) (h₂ : proj V (Iic 0) x.2 = x.2)
    {w : ℂ} (hw : w ∈ overlap σ) :
    eval σ w (phi σ (ghat g σ τ z) k x) =
      evalNat V σ w x.1 - w ^ k • g (z, w) (evalNeg V σ w⁻¹ x.2) := by
  have hw₁ : σ⁻¹ ≤ ‖w‖ := hw.1.le
  have hw₂ : ‖w‖ ≤ σ := hw.2.le
  rw [phi_apply, eval_sub hw₁ hw₂, eval_shift hw₁ hw₂, mulL, eval_conv _ hw₁ hw₂,
    eval_ghat hρ hστ hτρ hg hz hw₁ hw₂,
    eval_eq_evalNat hw₁ hw.2 fun j hj ↦ coeff_eq_zero_of_proj_eq_self h₁ (by simpa using hj),
    eval_eq_evalNeg hw.1 hw₂ fun j hj ↦ coeff_eq_zero_of_proj_eq_self h₂ (by simpa using hj),
    zpow_natCast]
  rfl

end Bounds
/-! ### Holomorphic functions from holomorphic families of Laurent series -/

section EvalComp

open Laurent L1

variable [CompleteSpace V] {σ : ℝ} [Fact (1 ≤ σ)] {W : Set E} {y : E → L1 V}

lemma differentiableOn_evalNat_comp (hy : DifferentiableOn ℂ y W) :
    DifferentiableOn ℂ (fun p : E × ℂ ↦ evalNat V σ p.2 (y p.1)) (W ×ˢ ball 0 σ) := by
  have h1 : DifferentiableOn ℂ (fun p : E × ℂ ↦ evalNat V σ p.2) (W ×ˢ ball 0 σ) :=
    (differentiableOn_evalNat (V := V) (σ := σ)).comp differentiableOn_snd
      fun _ hp ↦ (mem_prod.1 hp).2
  have h2 : DifferentiableOn ℂ (fun p : E × ℂ ↦ y p.1) (W ×ˢ ball 0 σ) :=
    hy.comp differentiableOn_fst fun _ hp ↦ (mem_prod.1 hp).1
  exact h1.clm_apply h2

lemma differentiableOn_evalNeg_comp (hy : DifferentiableOn ℂ y W) :
    DifferentiableOn ℂ (fun p : E × ℂ ↦ evalNeg V σ p.2 (y p.1)) (W ×ˢ ball 0 σ) := by
  have h1 : DifferentiableOn ℂ (fun p : E × ℂ ↦ evalNeg V σ p.2) (W ×ˢ ball 0 σ) :=
    (differentiableOn_evalNeg (V := V) (σ := σ)).comp differentiableOn_snd
      fun _ hp ↦ (mem_prod.1 hp).2
  have h2 : DifferentiableOn ℂ (fun p : E × ℂ ↦ y p.1) (W ×ˢ ball 0 σ) :=
    hy.comp differentiableOn_fst fun _ hp ↦ (mem_prod.1 hp).1
  exact h1.clm_apply h2

end EvalComp

/-! ### Vanishing of `R¹π_* E(k)` -/

section Vanishing

open Laurent L1

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ V]

/-- **Vanishing of `H¹(W × ℙ¹, E(k))` for `k ≫ 0`.** Let `g` be the transition function of a
holomorphic vector bundle `E` on `U × ℙ¹`, with respect to the charts `U × {‖w‖ < ρ}` and
`U × {‖w‖ > ρ⁻¹}`, and let `K ⊆ U` be compact. Then there are an open `U' ⊇ K` and `k₀` such that
for all `k ≥ k₀` and all open `W ⊆ U'` every holomorphic `h` on `W × {ρ⁻¹ < ‖w‖ < ρ}` splits as
`h = s₀ - wᵏ g t(w⁻¹)` with `s₀`, `t` holomorphic on `W × {‖w‖ < ρ}`. -/
theorem exists_vanishing (hρ : 1 < ρ) {U : Set E} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ U' : Set E, IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ W ⊆ U', IsOpen W →
      ∀ h : E × ℂ → V, DifferentiableOn ℂ h (W ×ˢ overlap ρ) →
      ∃ s₀ t : E × ℂ → V, DifferentiableOn ℂ s₀ (W ×ˢ ball 0 ρ) ∧
        DifferentiableOn ℂ t (W ×ˢ ball 0 ρ) ∧
        ∀ z ∈ W, ∀ w ∈ overlap ρ, h (z, w) = s₀ (z, w) - w ^ k • g (z, w) (t (z, w⁻¹)) := by
  set τ := (1 + ρ) / 2
  set σ := (1 + τ) / 2
  have hτρ : τ < ρ := by simp only [τ]; linarith
  have hστ : σ < τ := by simp only [σ, τ]; linarith
  have hσ1 : 1 < σ := by simp only [σ, τ]; linarith
  haveI : Fact (1 ≤ σ) := ⟨hσ1.le⟩
  obtain ⟨U', hU'o, hKU', hU'U, C, hC0, hC, hR, -⟩ :=
    exists_uniform_bounds hρ hU hg hgu hK hKU hστ hτρ
  have hε : (0 : ℝ) < 1 / (2 * (C + 1)) := by positivity
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 (hR _ hε)
  refine ⟨U', hU'o, hKU', hU'U, k₁.toNat, fun k hk W hWU hW h hh ↦ ?_⟩
  have hkk : k₁ ≤ (k : ℤ) := (Int.self_le_toNat k₁).trans (by exact_mod_cast hk)
  have hunit : ∀ z ∈ U', IsUnit (1 - errR σ (ghat g σ τ z) (uhat g σ τ z) k) := by
    intro z hz
    refine isUnit_one_sub_of_norm_lt_one ((norm_errR_le _).trans_lt ?_)
    calc ‖ghat g σ τ z‖ * ‖proj _ (Ioi (k : ℤ)) (uhat g σ τ z)‖ ≤ C * (1 / (2 * (C + 1))) :=
          mul_le_mul (hC z hz) (hk₁ k hkk z hz) (norm_nonneg _) hC0
      _ < 1 := by
          rw [mul_one_div, div_lt_one (by positivity)]
          linarith
  have hWU' : W ⊆ U := hWU.trans hU'U
  have hgW := (differentiableOn_ghat hρ hστ hτρ hU hg).mono hWU'
  have huW := (differentiableOn_uhat hρ hστ hτρ hU hg hgu).mono hWU'
  have hhat : DifferentiableOn ℂ (fun z ↦ toL1 σ τ fun w ↦ h (z, w)) W :=
    differentiableOn_toL1 (h := h) hστ hW
      (sphere_union_subset_overlap hρ (hσ1.trans hστ) hτρ) hh
  set x : E → L1 V × L1 V := fun z ↦
    rinv σ (ghat g σ τ z) (uhat g σ τ z) k (toL1 σ τ fun w ↦ h (z, w))
  have hx : DifferentiableOn ℂ x W :=
    (differentiableOn_rinv hgW huW fun z hz ↦ hunit z (hWU hz)).clm_apply hhat
  set s₀ : E × ℂ → V := fun p ↦ evalNat V σ p.2 (x p.1).1
  set t : E × ℂ → V := fun p ↦ evalNeg V σ p.2 (x p.1).2
  have hs₀ : DifferentiableOn ℂ s₀ (W ×ˢ ball 0 σ) := differentiableOn_evalNat_comp hx.fst
  have ht : DifferentiableOn ℂ t (W ×ˢ ball 0 σ) := differentiableOn_evalNeg_comp hx.snd
  have hrel : ∀ z ∈ W, ∀ w ∈ overlap σ,
      h (z, w) = s₀ (z, w) - w ^ k • g (z, w) (t (z, w⁻¹)) := by
    intro z hz w hw
    have hzU : z ∈ U := hWU' hz
    have hphi : phi σ (ghat g σ τ z) k (x z) = toL1 σ τ fun w ↦ h (z, w) :=
      phi_rinv (fun y ↦ mulL_ghat_uhat hρ hστ hτρ hg hgu hzU y) (hunit z (hWU hz)) _
    have := congrArg (eval σ w) hphi
    have hr := isRadius_overlap hρ (hσ1.trans hστ) hτρ
    have hhz : DifferentiableOn ℂ (fun w ↦ h (z, w)) (annulus ρ⁻¹ (ENNReal.ofReal ρ)) := by
      rw [← overlap_eq_annulus (zero_lt_one.trans hρ)]
      exact differentiableOn_slice hh hz
    rw [eval_phi hρ hg hστ hτρ hzU (rinv_fst_mem _ _) (rinv_snd_mem _ _) hw,
      eval_toL1 hστ hhz hr.1 hr.2 hw.1.le hw.2.le] at this
    exact this.symm
  obtain ⟨s₀', t', hs₀', ht', hrel', -⟩ := exists_extend hσ1 (hστ.trans hτρ) hW
    (hg.mono (prod_mono hWU' subset_rfl)) (fun p hp ↦ hgu p ⟨hWU' hp.1, hp.2⟩) hh hs₀ ht hrel
  exact ⟨s₀', t', hs₀', ht', hrel'⟩

end Vanishing
/-! ### The direct image `π_* E(k)` -/

section DirectImage

open Laurent L1

/-- The first `D` Taylor coefficients `(2πi)⁻¹ ∮_{‖w‖ = 1} w^{-i-1} s₀ (z, w) dw`, `i < D`, of
`w ↦ s₀ (z, w)`. -/
noncomputable def jet (D : ℕ) (s₀ : E × ℂ → V) (z : E) : Fin D → V :=
  fun i ↦ circleCoeff (fun w ↦ s₀ (z, w)) 1 i

lemma isRadius_disc {ρ τ : ℝ} (hτ : 1 < τ) (hτρ : τ < ρ) :
    IsRadius (-1) (ENNReal.ofReal ρ) τ ∧ IsRadius (-1) (ENNReal.ofReal ρ) τ⁻¹ := by
  have hτ0 : 0 < τ := zero_lt_one.trans hτ
  have hρ0 : 0 < ρ := hτ0.trans hτρ
  exact ⟨⟨hτ0, by linarith, (ENNReal.ofReal_lt_ofReal_iff hρ0).2 hτρ⟩,
    ⟨inv_pos.2 hτ0, by linarith [inv_pos.2 hτ0], (ENNReal.ofReal_lt_ofReal_iff hρ0).2
      ((inv_lt_one_of_one_lt₀ hτ).trans (hτ.trans hτρ))⟩⟩

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ V]

/-- **The direct image of `E(k)` is a direct summand of a free module of finite rank, `k ≫ 0`.**
Let `g` be the transition function of a holomorphic vector bundle `E` on `U × ℙ¹`, with respect
to the charts `U × {‖w‖ < ρ}` and `U × {‖w‖ > ρ⁻¹}`, and let `K ⊆ U` be compact. Then there are
an open `U' ⊇ K` and `k₀` such that for all `k ≥ k₀` there are `D` and a holomorphic family `e` of
idempotent endomorphisms of `V^D` on `U'` with the following property: for every open `W ⊆ U'`,
taking the first `D` Taylor coefficients `jet D s₀` in `w` is a bijection from the sections of
`E(k)` over `W × ℙ¹` onto the holomorphic maps `c : W → V^D` with `e c = c`. -/
theorem exists_jet_equiv (hρ : 1 < ρ) {U : Set E} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ)) (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p))
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ U' : Set E, IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (D : ℕ)
      (e : E → (Fin D → V) →L[ℂ] (Fin D → V)), DifferentiableOn ℂ e U' ∧
      (∀ z ∈ U', e z ∘L e z = e z) ∧ ∀ W ⊆ U', IsOpen W →
        (∀ s₀ t, IsSection ρ g k W s₀ t →
          DifferentiableOn ℂ (jet D s₀) W ∧ ∀ z ∈ W, e z (jet D s₀ z) = jet D s₀ z) ∧
        (∀ s₀ t, IsSection ρ g k W s₀ t → (∀ z ∈ W, jet D s₀ z = 0) →
          ∀ z ∈ W, ∀ w ∈ ball (0 : ℂ) ρ, s₀ (z, w) = 0 ∧ t (z, w) = 0) ∧
        (∀ c : E → Fin D → V, DifferentiableOn ℂ c W → (∀ z ∈ W, e z (c z) = c z) →
          ∃ s₀ t, IsSection ρ g k W s₀ t ∧ ∀ z ∈ W, jet D s₀ z = c z) := by
  set τ := (1 + ρ) / 2
  set σ := (1 + τ) / 2
  have hτρ : τ < ρ := by simp only [τ]; linarith
  have hστ : σ < τ := by simp only [σ, τ]; linarith
  have hσ1 : 1 < σ := by simp only [σ, τ]; linarith
  have hτ1 : 1 < τ := hσ1.trans hστ
  have hσ0 : 0 < σ := zero_lt_one.trans hσ1
  haveI : Fact (1 ≤ σ) := ⟨hσ1.le⟩
  obtain ⟨U', hU'o, hKU', hU'U, C, hC0, hC, hR, hL⟩ :=
    exists_uniform_bounds hρ hU hg hgu hK hKU hστ hτρ
  have hε : (0 : ℝ) < 1 / (2 * (C + 1)) := by positivity
  have hsmall : C * (1 / (2 * (C + 1))) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 (hR _ hε)
  obtain ⟨m₁, hm₁⟩ := eventually_atBot.1 (hL _ hε)
  set N : ℕ := (-m₁).toNat
  refine ⟨U', hU'o, hKU', hU'U, k₁.toNat, fun k hk ↦ ?_⟩
  set D : ℕ := k + N
  have hkD : (k : ℤ) - (D : ℕ) = -(N : ℤ) := by simp only [D]; push_cast; ring
  have hNm : -(N : ℤ) ≤ m₁ := by simp only [N]; omega
  have hkk : k₁ ≤ (k : ℤ) := (Int.self_le_toNat k₁).trans (by exact_mod_cast hk)
  have hunitR : ∀ z ∈ U', IsUnit (1 - errR σ (ghat g σ τ z) (uhat g σ τ z) k) := fun z hz ↦
    isUnit_one_sub_of_norm_lt_one ((norm_errR_le _).trans_lt
      ((mul_le_mul (hC z hz) (hk₁ k hkk z hz) (norm_nonneg _) hC0).trans_lt hsmall))
  have hunitL : ∀ z ∈ U', IsUnit (1 - errL σ (ghat g σ τ z) (uhat g σ τ z) ((k : ℤ) - D)) :=
    fun z hz ↦ by
      rw [hkD]
      exact isUnit_one_sub_of_norm_lt_one ((norm_errL_le _).trans_lt
        ((mul_le_mul (hC z hz) (hm₁ _ hNm z hz) (norm_nonneg _) hC0).trans_lt hsmall))
  have hgU' := (differentiableOn_ghat hρ hστ hτρ hU hg).mono hU'U
  have huU' := (differentiableOn_uhat hρ hστ hτρ hU hg hgu).mono hU'U
  have hgu' : ∀ z ∈ U', ∀ y, mulL V σ (ghat g σ τ z) (mulL V σ (uhat g σ τ z) y) = y :=
    fun z hz y ↦ mulL_ghat_uhat hρ hστ hτρ hg hgu (hU'U hz) y
  have hug' : ∀ z ∈ U', ∀ y, mulL V σ (uhat g σ τ z) (mulL V σ (ghat g σ τ z) y) = y :=
    fun z hz y ↦ mulL_uhat_ghat hρ hστ hτρ hg hgu (hU'U hz) y
  refine ⟨D, fun z ↦ jetIdem σ (ghat g σ τ z) (uhat g σ τ z) k D,
    differentiableOn_jetIdem hgU' huU' hunitR hunitL,
    fun z hz ↦ jetIdem_comp_self (hgu' z hz) (hug' z hz) (hunitR z hz) (hunitL z hz),
    fun W hWU hW ↦ ?_⟩
  have hr := isRadius_disc hτ1 hτρ
  -- the Laurent series of a section
  have hsec : ∀ s₀ t, IsSection ρ g k W s₀ t → ∀ z ∈ W,
      proj V (Ici 0) (toL1 σ τ fun w ↦ s₀ (z, w)) = (toL1 σ τ fun w ↦ s₀ (z, w)) ∧
      proj V (Iic 0) (refl V (toL1 σ τ fun w ↦ t (z, w))) =
        refl V (toL1 σ τ fun w ↦ t (z, w)) ∧
      phi σ (ghat g σ τ z) k
        ((toL1 σ τ fun w ↦ s₀ (z, w)), refl V (toL1 σ τ fun w ↦ t (z, w))) = 0 ∧
      toJet V σ D (toL1 σ τ fun w ↦ s₀ (z, w)) = jet D s₀ z := by
    intro s₀ t hst z hz
    have hs : DifferentiableOn ℂ (fun w ↦ s₀ (z, w)) (ball 0 ρ) := differentiableOn_slice hst.1 hz
    have ht : DifferentiableOn ℂ (fun w ↦ t (z, w)) (ball 0 ρ) := differentiableOn_slice hst.2.1 hz
    have hs' : DifferentiableOn ℂ (fun w ↦ s₀ (z, w)) (annulus (-1) (ENNReal.ofReal ρ)) := by
      rwa [annulus_neg_one_ofReal]
    have ht' : DifferentiableOn ℂ (fun w ↦ t (z, w)) (annulus (-1) (ENNReal.ofReal ρ)) := by
      rwa [annulus_neg_one_ofReal]
    refine ⟨proj_eq_self_iff.2 fun j hj ↦ ?_, proj_eq_self_iff.2 fun j hj ↦ ?_, ?_, ?_⟩
    · rw [apply_eq_wt_smul_coeff hσ0, coeff_toL1_eq_zero_of_neg hστ hτρ hs (by simpa using hj),
        smul_zero]
    · rw [refl_apply, apply_eq_wt_smul_coeff hσ0,
        coeff_toL1_eq_zero_of_neg hστ hτρ ht (by simp only [mem_Iic, not_le] at hj; omega),
        smul_zero]
    · refine eq_of_eval_eq (σ := σ) fun w hw ↦ ?_
      have hw₁ : σ⁻¹ ≤ ‖w‖ := hw ▸ inv_le_one_of_one_le₀ hσ1.le
      have hw₂ : ‖w‖ ≤ σ := hw ▸ hσ1.le
      have hwi : ‖w⁻¹‖ = 1 := by rw [norm_inv, hw, inv_one]
      have hwi₁ : σ⁻¹ ≤ ‖w⁻¹‖ := hwi ▸ inv_le_one_of_one_le₀ hσ1.le
      have hwi₂ : ‖w⁻¹‖ ≤ σ := hwi ▸ hσ1.le
      rw [eval_zero, phi_apply, eval_sub hw₁ hw₂, eval_shift hw₁ hw₂, mulL,
        eval_conv _ hw₁ hw₂, eval_ghat hρ hστ hτρ hg (hU'U (hWU hz)) hw₁ hw₂,
        eval_refl hw₁ hw₂, eval_toL1 hστ hs' hr.1 hr.2 hw₁ hw₂,
        eval_toL1 hστ ht' hr.1 hr.2 hwi₁ hwi₂, zpow_natCast,
        hst.2.2 z hz w (mem_overlap_of_norm_eq_one hρ hw)]
      exact sub_self _
    · funext i
      rw [toJet_apply, coeff_toL1_eq_circleCoeff hστ hτρ hs one_pos hρ (by positivity)]
      rfl
  refine ⟨fun s₀ t hst ↦ ⟨?_, fun z hz ↦ ?_⟩, fun s₀ t hst h0 z hz w hw ↦ ?_,
    fun c hc hce ↦ ?_⟩
  · refine differentiableOn_pi.2 fun i ↦ ?_
    exact differentiableOn_circleCoeff hW one_pos
      (fun w hw ↦ by rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hw]; exact hρ) hst.1 i
  · obtain ⟨ha, hb, hab, hjet⟩ := hsec s₀ t hst z hz
    rw [← hjet]
    exact jetIdem_toJet (hug' z (hWU hz)) (hunitL z (hWU hz)) ha hb hab
  · obtain ⟨ha, hb, hab, hjet⟩ := hsec s₀ t hst z hz
    have hrec := recon_ofJet_toJet (hug' z (hWU hz)) (hunitL z (hWU hz)) ha hb hab
    rw [hjet, h0 z hz, map_zero, map_zero] at hrec
    have ha0 : (toL1 σ τ fun w ↦ s₀ (z, w)) = 0 := (congrArg Prod.fst hrec).symm
    have hb0 : (toL1 σ τ fun w ↦ t (z, w)) = 0 := by
      have := (congrArg Prod.snd hrec).symm
      refine lp.ext (funext fun j ↦ ?_)
      have hj := congrArg (fun y : L1 V ↦ y (-j)) this
      simpa [refl_apply] using hj
    exact ⟨eq_zero_of_toL1_eq_zero hστ hτρ (differentiableOn_slice hst.1 hz) ha0 hw,
      eq_zero_of_toL1_eq_zero hστ hτρ (differentiableOn_slice hst.2.1 hz) hb0 hw⟩
  · set x : E → L1 V × L1 V := fun z ↦
      recon σ (ghat g σ τ z) (uhat g σ τ z) k ((k : ℤ) - D) (ofJet V σ D (c z))
    have hx : DifferentiableOn ℂ x W :=
      ((differentiableOn_recon hgU' huU' hunitR hunitL).mono hWU).clm_apply
        ((ofJet V σ D).differentiable.comp_differentiableOn hc)
    set s₀ : E × ℂ → V := fun p ↦ evalNat V σ p.2 (x p.1).1
    set t : E × ℂ → V := fun p ↦ evalNeg V σ p.2 (x p.1).2
    have hs₀ : DifferentiableOn ℂ s₀ (W ×ˢ ball 0 σ) := differentiableOn_evalNat_comp hx.fst
    have ht : DifferentiableOn ℂ t (W ×ˢ ball 0 σ) := differentiableOn_evalNeg_comp hx.snd
    have hrel : ∀ z ∈ W, ∀ w ∈ overlap σ,
        (0 : E × ℂ → V) (z, w) = s₀ (z, w) - w ^ k • g (z, w) (t (z, w⁻¹)) := by
      intro z hz w hw
      have hphi : phi σ (ghat g σ τ z) k (x z) = 0 :=
        phi_recon_ofJet (hgu' z (hWU hz)) (hunitR z (hWU hz)) D (c z)
      have := congrArg (eval σ w) hphi
      rw [eval_phi hρ hg hστ hτρ (hU'U (hWU hz))
        (recon_fst_mem (hunitL z (hWU hz)) (by omega) (proj_ofJet D (c z)))
        (recon_snd_mem _) hw, eval_zero] at this
      exact this.symm
    have hWU' : W ⊆ U := hWU.trans hU'U
    obtain ⟨s₀', t', hs₀', ht', hrel', hagree⟩ := exists_extend hσ1 (hστ.trans hτρ) hW
      (hg.mono (prod_mono hWU' subset_rfl)) (fun p hp ↦ hgu p ⟨hWU' hp.1, hp.2⟩)
      (differentiableOn_const 0) hs₀ ht hrel
    refine ⟨s₀', t', ⟨hs₀', ht', fun z hz w hw ↦ ?_⟩, fun z hz ↦ ?_⟩
    · exact (sub_eq_zero.1 (hrel' z hz w hw).symm)
    · funext i
      have hcongr : circleCoeff (fun w ↦ s₀' (z, w)) 1 i = circleCoeff (fun w ↦ s₀ (z, w)) 1 i :=
        circleCoeff_congr zero_le_one (fun w hw ↦ (hagree z hz w (by
          rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hw]; exact hσ1)).1) i
      change circleCoeff (fun w ↦ s₀' (z, w)) 1 i = c z i
      rw [hcongr]
      change circleCoeff (fun w ↦ evalNat V σ w (x z).1) 1 (i : ℤ) = c z i
      rw [circleCoeff_evalNat one_pos hσ1 _ (by positivity)]
      exact congrFun (hce z hz) i

end DirectImage
/-! ### Transition functions given by matrices -/

section Matrix

open scoped Matrix

variable {r : ℕ}

/-- The monoid homomorphism sending a matrix to the continuous linear endomorphism
`v ↦ A *ᵥ v` of `Fin r → ℂ`. -/
noncomputable def matrixCLM : Matrix (Fin r) (Fin r) ℂ →* (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) where
  toFun A := LinearMap.toContinuousLinearMap (Matrix.toLin' A)
  map_one' := by ext1 v; simp
  map_mul' A B := by ext1 v; simp [Matrix.mulVec_mulVec]

@[simp]
lemma matrixCLM_apply (A : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    matrixCLM A v = A *ᵥ v := by
  simp [matrixCLM]

lemma differentiableOn_matrixCLM {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {g : X → Matrix (Fin r) (Fin r) ℂ} {s : Set X} (hg : DifferentiableOn ℂ g s) :
    DifferentiableOn ℂ (fun p ↦ matrixCLM (g p)) s := by
  open scoped Matrix.Norms.Operator in
  let L : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
    { toFun := fun A ↦ matrixCLM A
      map_add' := fun A B ↦ by ext1 v; simp [Matrix.add_mulVec]
      map_smul' := fun c A ↦ by ext1 v; simp [Matrix.smul_mulVec] }
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap L).differentiable.comp_differentiableOn hg
lemma isSection_matrixCLM_iff {g : E × ℂ → Matrix (Fin r) (Fin r) ℂ} {s₀ t : E × ℂ → Fin r → ℂ} :
    IsSection ρ (fun p ↦ matrixCLM (g p)) k W s₀ t ↔
      DifferentiableOn ℂ s₀ (W ×ˢ ball 0 ρ) ∧ DifferentiableOn ℂ t (W ×ˢ ball 0 ρ) ∧
        ∀ z ∈ W, ∀ w ∈ overlap ρ, s₀ (z, w) = w ^ k • g (z, w) *ᵥ t (z, w⁻¹) := by
  simp [IsSection]

variable [FiniteDimensional ℂ E]

/-- `Complex.ProjectiveLineBundle.exists_vanishing` for a transition function given by invertible
matrices. -/
theorem exists_vanishing_matrix (hρ : 1 < ρ) {U : Set E} (hU : IsOpen U)
    {g : E × ℂ → Matrix (Fin r) (Fin r) ℂ} (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ))
    (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p)) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ U' : Set E, IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ W ⊆ U', IsOpen W →
      ∀ h : E × ℂ → Fin r → ℂ, DifferentiableOn ℂ h (W ×ˢ overlap ρ) →
      ∃ s₀ t : E × ℂ → Fin r → ℂ, DifferentiableOn ℂ s₀ (W ×ˢ ball 0 ρ) ∧
        DifferentiableOn ℂ t (W ×ˢ ball 0 ρ) ∧
        ∀ z ∈ W, ∀ w ∈ overlap ρ, h (z, w) = s₀ (z, w) - w ^ k • g (z, w) *ᵥ t (z, w⁻¹) := by
  obtain ⟨U', h1, h2, h3, k₀, hk₀⟩ := exists_vanishing (g := fun p ↦ matrixCLM (g p)) hρ hU
    (differentiableOn_matrixCLM hg) (fun p hp ↦ (hgu p hp).map matrixCLM) hK hKU
  refine ⟨U', h1, h2, h3, k₀, fun k hk W hWU hW h hh ↦ ?_⟩
  obtain ⟨s₀, t, hs, ht, hrel⟩ := hk₀ k hk W hWU hW h hh
  exact ⟨s₀, t, hs, ht, fun z hz w hw ↦ by simpa using hrel z hz w hw⟩

/-- `Complex.ProjectiveLineBundle.exists_jet_equiv` for a transition function given by invertible
matrices; see `Complex.ProjectiveLineBundle.isSection_matrixCLM_iff` for the sections. -/
theorem exists_jet_equiv_matrix (hρ : 1 < ρ) {U : Set E} (hU : IsOpen U)
    {g : E × ℂ → Matrix (Fin r) (Fin r) ℂ} (hg : DifferentiableOn ℂ g (U ×ˢ overlap ρ))
    (hgu : ∀ p ∈ U ×ˢ overlap ρ, IsUnit (g p)) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ U' : Set E, IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (D : ℕ)
      (e : E → (Fin D → Fin r → ℂ) →L[ℂ] (Fin D → Fin r → ℂ)), DifferentiableOn ℂ e U' ∧
      (∀ z ∈ U', e z ∘L e z = e z) ∧ ∀ W ⊆ U', IsOpen W →
        (∀ s₀ t, IsSection ρ (fun p ↦ matrixCLM (g p)) k W s₀ t →
          DifferentiableOn ℂ (jet D s₀) W ∧ ∀ z ∈ W, e z (jet D s₀ z) = jet D s₀ z) ∧
        (∀ s₀ t, IsSection ρ (fun p ↦ matrixCLM (g p)) k W s₀ t → (∀ z ∈ W, jet D s₀ z = 0) →
          ∀ z ∈ W, ∀ w ∈ ball (0 : ℂ) ρ, s₀ (z, w) = 0 ∧ t (z, w) = 0) ∧
        (∀ c : E → Fin D → Fin r → ℂ, DifferentiableOn ℂ c W → (∀ z ∈ W, e z (c z) = c z) →
          ∃ s₀ t, IsSection ρ (fun p ↦ matrixCLM (g p)) k W s₀ t ∧
            ∀ z ∈ W, jet D s₀ z = c z) :=
  exists_jet_equiv hρ hU (differentiableOn_matrixCLM hg) (fun p hp ↦ (hgu p hp).map matrixCLM) hK
    hKU

end Matrix

end Complex.ProjectiveLineBundle
