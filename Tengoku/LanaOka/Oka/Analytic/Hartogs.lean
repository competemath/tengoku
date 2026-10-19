/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytic.RiemannExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hartogs extension across sets sliced by discs

Let `E` be a finite-dimensional complex normed space, `U ⊆ E` open and `S ⊆ E` with `U \ S` open.
Suppose that near every point `a ∈ U ∩ S` there are a direction `v` and a radius `r > 0` such
that for all `z` near `a` the closed disc `{z + t • v | ‖t‖ ≤ r}` lies in `U`, its boundary circle
misses `S`, and the points `z` whose disc meets `S` form a set with empty interior
(`HasHartogsSlicesAt`). Then every holomorphic function on `U \ S` extends to a holomorphic
function on `U`.

This is the form in which Hartogs' extension theorem across sets of codimension at least two is
proved: for the common zero set of a regular sequence `(g, h)`, the discs are the fibres of a
projection which is finite on the zero set of `g`, and the discs meeting `S` lie over the zero
set of a nonzero function of the remaining coordinates.

## Main definitions

- `HasHartogsSlicesAt U S a`: the slicing condition at `a` described above.

## Main results

- `HasHartogsSlicesAt.of_continuousLinearEquiv`: invariance under linear changes of coordinates.
- `HasHartogsSlicesAt.exists_local`: near `a`, a holomorphic function on `U \ S` extends, via the
  Cauchy integral over the boundary circles of the discs.
- `interior_inter_eq_empty_of_hasHartogsSlicesAt`: `U ∩ S` has empty interior.
- `exists_differentiableOn_eqOn_of_hasHartogsSlicesAt`: **Hartogs extension.**
-/

open Set Filter Metric Complex Real
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U S : Set E} {a : E}

/-- `S` is sliced by discs near `a` inside `U`: there are a neighbourhood `W` of `a`, a direction
`v` and a radius `r > 0` such that for `z ∈ W` the closed disc `{z + t • v | ‖t‖ ≤ r}` lies in
`U`, its boundary circle does not meet `S`, and the set of `z ∈ W` whose disc meets `S` has empty
interior. -/
def HasHartogsSlicesAt (U S : Set E) (a : E) : Prop :=
  ∃ W ∈ 𝓝 a, ∃ (v : E) (r : ℝ), 0 < r ∧
    (∀ z ∈ W, ∀ t : ℂ, ‖t‖ ≤ r → z + t • v ∈ U) ∧
    (∀ z ∈ W, ∀ t : ℂ, ‖t‖ = r → z + t • v ∉ S) ∧
    interior {z ∈ W | ∃ t : ℂ, ‖t‖ ≤ r ∧ z + t • v ∈ S} = ∅

/-- Slicing by discs is invariant under linear changes of coordinates. -/
theorem HasHartogsSlicesAt.of_continuousLinearEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) (h : HasHartogsSlicesAt (e.symm ⁻¹' U) (e.symm ⁻¹' S) (e a)) :
    HasHartogsSlicesAt U S a := by
  obtain ⟨W, hW, v, r, hr, hdisc, hcirc, hbad⟩ := h
  have hmap : ∀ z (t : ℂ), e.symm (e z + t • v) = z + t • e.symm v := fun z t ↦ by
    rw [map_add, map_smul, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨e ⁻¹' W, e.continuous.continuousAt.preimage_mem_nhds hW, e.symm v, r, hr,
    fun z hz t ht ↦ ?_, fun z hz t ht ↦ ?_, ?_⟩
  · simpa [hmap] using hdisc (e z) hz t ht
  · simpa [hmap] using hcirc (e z) hz t ht
  · have : {z ∈ e ⁻¹' W | ∃ t : ℂ, ‖t‖ ≤ r ∧ z + t • e.symm v ∈ S} =
        e ⁻¹' {z ∈ W | ∃ t : ℂ, ‖t‖ ≤ r ∧ z + t • v ∈ e.symm ⁻¹' S} := by
      ext z
      simp
    rw [this]
    exact (e.toHomeomorph.preimage_interior _).symm.trans (by rw [hbad, preimage_empty])

/-- Two functions continuous on an open set `O` which agree on `O \ B` agree on `O`, if `B` has
empty interior. -/
lemma Set.EqOn.of_eqOn_diff_of_interior_eq_empty {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {O B : Set X} {F G : X → Y} (hO : IsOpen O)
    (hB : interior B = ∅) (hF : ContinuousOn F O) (hG : ContinuousOn G O) (h : EqOn F G (O \ B)) :
    EqOn F G O :=
  h.of_subset_closure hF hG sdiff_subset
    ((interior_eq_empty_iff_dense_compl.mp hB).open_subset_closure_inter hO)

namespace HasHartogsSlicesAt

variable [FiniteDimensional ℂ E]

/-- **Local Hartogs extension.** Near a point at which `S` is sliced by discs, a holomorphic
function on `U \ S` extends holomorphically. The extension is the Cauchy integral over the
boundary circles of the discs. -/
theorem exists_local (h : HasHartogsSlicesAt U S a) (hUS : IsOpen (U \ S)) {f : E → ℂ}
    (hf : DifferentiableOn ℂ f (U \ S)) :
    ∃ W : Set E, IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧ interior (W ∩ S) = ∅ ∧
      ∃ F : E → ℂ, DifferentiableOn ℂ F W ∧ EqOn F f (W \ S) := by
  obtain ⟨W₀, hW₀, v, r, hr, hdisc, hcirc, hbad⟩ := h
  set W := interior W₀
  have hWW₀ : W ⊆ W₀ := interior_subset
  have hWo : IsOpen W := isOpen_interior
  set B := {z ∈ W₀ | ∃ t : ℂ, ‖t‖ ≤ r ∧ z + t • v ∈ S}
  have hWU : W ⊆ U := fun z hz ↦ by simpa using hdisc z (hWW₀ hz) 0 (by simp [hr.le])
  have hWSB : W ∩ S ⊆ B := fun z hz ↦ ⟨hWW₀ hz.1, 0, by simp [hr.le], by simpa using hz.2⟩
  have hWS : interior (W ∩ S) = ∅ := subset_empty_iff.mp (hbad ▸ interior_mono hWSB)
  have hsph : ∀ z ∈ W, ∀ ζ ∈ sphere (0 : ℂ) r, z + ζ • v ∈ U \ S := fun z hz ζ hζ ↦ by
    rw [mem_sphere_zero_iff_norm] at hζ
    exact ⟨hdisc z (hWW₀ hz) ζ hζ.le, hcirc z (hWW₀ hz) ζ hζ⟩
  set G : E → ℂ → ℂ := fun z ζ ↦ ζ⁻¹ • f (z + ζ • v)
  have hGd : DifferentiableOn ℂ (fun z ↦ ∮ ζ in C(0, r), G z ζ) W := by
    refine differentiableOn_circleIntegral hWo hr (fun ζ hζ ↦ ?_) ?_
    · exact ((hf.comp (by fun_prop : Differentiable ℂ fun z : E ↦ z + ζ • v).differentiableOn
        fun z hz ↦ hsph z hz ζ hζ)).const_smul ζ⁻¹
    · refine ContinuousOn.smul (continuousOn_snd.inv₀ fun p hp ↦ ?_) ?_
      · have := (mem_prod.mp hp).2
        rw [mem_sphere_zero_iff_norm] at this
        exact norm_ne_zero_iff.mp (this ▸ hr.ne')
      · exact hf.continuousOn.comp (by fun_prop) fun p hp ↦ hsph p.1 (mem_prod.mp hp).1 p.2
          (mem_prod.mp hp).2
  refine ⟨W, hWo, mem_interior_iff_mem_nhds.mpr hW₀, hWU, hWS,
    fun z ↦ (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, r), G z ζ, hGd.fun_const_smul _, ?_⟩
  -- The Cauchy integral agrees with `f` wherever the disc misses `S`.
  have hgood : EqOn (fun z ↦ (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, r), G z ζ) f (W \ B) := by
    rintro z ⟨hzW, hzB⟩
    have hmem : ∀ t ∈ closedBall (0 : ℂ) r, z + t • v ∈ U \ S := fun t ht ↦ by
      rw [mem_closedBall_zero_iff] at ht
      exact ⟨hdisc z (hWW₀ hzW) t ht, fun hS ↦ hzB ⟨hWW₀ hzW, t, ht, hS⟩⟩
    have hd : DifferentiableOn ℂ (fun t : ℂ ↦ f (z + t • v)) (closedBall 0 r) :=
      hf.comp (by fun_prop : Differentiable ℂ fun t : ℂ ↦ z + t • v).differentiableOn hmem
    have := hd.circleIntegral_sub_inv_smul (w := 0) (mem_ball_self hr)
    simp only [sub_zero, zero_smul, add_zero] at this
    simp only [G, this, smul_smul]
    rw [inv_mul_cancel₀ (by simp [pi_ne_zero, I_ne_zero]), one_smul]
  have hWSo : IsOpen (W \ S) := by
    rw [show W \ S = W ∩ (U \ S) by ext z; exact ⟨fun h ↦ ⟨h.1, hWU h.1, h.2⟩,
      fun h ↦ ⟨h.1, h.2.2⟩⟩]
    exact hWo.inter hUS
  refine EqOn.of_eqOn_diff_of_interior_eq_empty hWSo hbad
    ((hGd.fun_const_smul _).continuousOn.mono sdiff_subset) (hf.continuousOn.mono
      (sdiff_subset_sdiff_left hWU)) fun z hz ↦ hgood ⟨hz.1.1, hz.2⟩

end HasHartogsSlicesAt

/-- If `S` is sliced by discs near every point of `U ∩ S`, then `U ∩ S` has empty interior. -/
theorem interior_inter_eq_empty_of_hasHartogsSlicesAt [FiniteDimensional ℂ E]
    (hUS : IsOpen (U \ S)) (h : ∀ a ∈ U ∩ S, HasHartogsSlicesAt U S a) :
    interior (U ∩ S) = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun a ha ↦ ?_
  obtain ⟨W, hWo, haW, -, hWS, -⟩ := (h a (interior_subset ha)).exists_local hUS
    (f := 0) (differentiableOn_const 0)
  have hsub : W ∩ interior (U ∩ S) ⊆ W ∩ S := fun z hz ↦
    ⟨hz.1, (interior_subset hz.2 : z ∈ U ∩ S).2⟩
  have : a ∈ interior (W ∩ S) :=
    interior_maximal hsub (hWo.inter isOpen_interior) ⟨haW, ha⟩
  simp [hWS] at this

/-- **Hartogs extension.** If `S` is sliced by discs near every point of `U ∩ S`, then every
holomorphic function on `U \ S` extends to a holomorphic function on `U`. -/
theorem exists_differentiableOn_eqOn_of_hasHartogsSlicesAt [FiniteDimensional ℂ E]
    (hUS : IsOpen (U \ S)) (h : ∀ a ∈ U ∩ S, HasHartogsSlicesAt U S a)
    {f : E → ℂ} (hf : DifferentiableOn ℂ f (U \ S)) :
    ∃ F : E → ℂ, DifferentiableOn ℂ F U ∧ EqOn F f (U \ S) := by
  classical
  choose W hWo haW hWU hWS F hFd hFf using fun (a : E) (ha : a ∈ U ∩ S) ↦
    (h a ha).exists_local hUS hf
  -- Two local extensions agree where both are defined.
  have hagree : ∀ a ha b hb, EqOn (F a ha) (F b hb) (W a ha ∩ W b hb) := by
    intro a ha b hb
    refine EqOn.of_eqOn_diff_of_interior_eq_empty ((hWo a ha).inter (hWo b hb))
      (B := W a ha ∩ S) (hWS a ha) ((hFd a ha).continuousOn.mono inter_subset_left)
      ((hFd b hb).continuousOn.mono inter_subset_right) fun z hz ↦ ?_
    have hzS : z ∉ S := fun hS ↦ hz.2 ⟨hz.1.1, hS⟩
    rw [hFf a ha ⟨hz.1.1, hzS⟩, hFf b hb ⟨hz.1.2, hzS⟩]
  set G : E → ℂ := fun z ↦ if hz : z ∈ U ∩ S then F z hz z else f z
  refine ⟨G, fun b hb ↦ ?_, fun z hz ↦ by simp [G, hz.2]⟩
  by_cases hbS : b ∈ S
  · have hbUS : b ∈ U ∩ S := ⟨hb, hbS⟩
    have hGF : G =ᶠ[𝓝 b] F b hbUS := by
      filter_upwards [(hWo b hbUS).mem_nhds (haW b hbUS)] with z hz
      by_cases hzS : z ∈ S
      · have hzUS : z ∈ U ∩ S := ⟨hWU b hbUS hz, hzS⟩
        simp only [G, dite_eq_left hzUS]
        exact hagree z hzUS b hbUS ⟨haW z hzUS, hz⟩
      · simp only [G, show z ∉ U ∩ S from fun h ↦ hzS h.2, dite_false]
        exact (hFf b hbUS ⟨hz, hzS⟩).symm
    exact (((hFd b hbUS).differentiableAt
      ((hWo b hbUS).mem_nhds (haW b hbUS))).congr_of_eventuallyEq hGF).differentiableWithinAt
  · have hGf : G =ᶠ[𝓝 b] f := by
      filter_upwards [hUS.mem_nhds ⟨hb, hbS⟩] with z hz
      simp [G, hz.2]
    exact ((hf.differentiableAt (hUS.mem_nhds ⟨hb, hbS⟩)).congr_of_eventuallyEq
      hGf).differentiableWithinAt
