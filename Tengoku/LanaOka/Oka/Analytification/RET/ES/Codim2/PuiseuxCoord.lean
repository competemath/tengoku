/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.Polynomial.Cyclotomic.Basic
import Tengoku.LanaOka.Oka.Analysis.Complex.KummerExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Puiseux map `t ↦ tˢ` in one coordinate

Let `ι` be a finite type, `i₀ : ι` a distinguished coordinate and `s > 0`. The Puiseux map
`α = Kummer.coordPow i₀ s : ℂ^ι → ℂ^ι` replaces the coordinate `t = x i₀` by `tˢ`. The group of
`s`-th roots of unity acts on `ℂ^ι` by `Kummer.coordRot i₀ ζ : t ↦ ζ t`, and the fibres of `α` are
the orbits (`Kummer.exists_coordRot_eq`).

For an open `G ⊆ ℂ^ι`, every holomorphic function on `α⁻¹(G)` is `∑_{j < s} tʲ gⱼ ∘ α` with `gⱼ`
holomorphic on `G` (`Kummer.exists_eqOn_sum_pow_mul_comp_coordPow`); this is
`Kummer.exists_eqOn_sum_pow_mul_comp_powMap` in the splitting `ℂ^ι ≅ ℂ^{ι ∖ i₀} × ℂ`. Averaging
over the roots of unity shows that a function `h` on `G` with `h ∘ α` holomorphic is holomorphic
(`Kummer.differentiableOn_of_comp_coordPow`).

Near a point `y'` with `y' i₀ ≠ 0`, the preimage under `α` of a small neighbourhood of `α(y')` is
the disjoint union of `s` small balls around the points `ζᵏ y'` of the fibre
(`Kummer.exists_pieces_coordPow`); in particular it is the union of the rotations of a piece
(`Kummer.IsPiece`, `Kummer.exists_isPiece`). The roots of `tˢ` depend continuously on `t`
(`Kummer.exists_coordRot_norm_sub_lt`).

## Main definitions

- `Kummer.coordPow i₀ s`: the Puiseux map `t ↦ tˢ` in the coordinate `i₀`.
- `Kummer.coordRot i₀ ζ`: the rotation `t ↦ ζ t` in the coordinate `i₀`.
- `Kummer.IsPiece i₀ s V₀ P₀`: every point of `α⁻¹(V₀)` has exactly one rotation in `P₀`, and
  membership in `P₀` is locally constant on `α⁻¹(V₀)`.

## Main results

- `Kummer.exists_eqOn_sum_pow_mul_comp_coordPow`: the decomposition `∑_{j < s} tʲ gⱼ ∘ α`.
- `Kummer.differentiableOn_of_comp_coordPow`: descent of holomorphy along `α`.
- `Kummer.exists_pieces_coordPow`, `Kummer.exists_isPiece`: the preimage of a small neighbourhood
  off `t = 0` splits into `s` disjoint pieces.
-/

open Set Filter Topology Metric

namespace Kummer

noncomputable section

variable {ι : Type*} [DecidableEq ι] (i₀ : ι)

/-- The Puiseux map: the coordinate `x i₀` is replaced by `x i₀ ^ s`. -/
def coordPow (s : ℕ) (x : ι → ℂ) : ι → ℂ :=
  Function.update x i₀ (x i₀ ^ s)

/-- The rotation of the coordinate `x i₀` by `ζ`. -/
def coordRot (ζ : ℂ) (x : ι → ℂ) : ι → ℂ :=
  Function.update x i₀ (ζ * x i₀)

/-- A point of the fibre of `Kummer.coordPow i₀ s` over `x`. -/
def coordRoot (s : ℕ) (x : ι → ℂ) : ι → ℂ :=
  Function.update x i₀ (x i₀ ^ ((s : ℂ)⁻¹))

variable {i₀}

@[simp]
lemma coordPow_self (s : ℕ) (x : ι → ℂ) : coordPow i₀ s x i₀ = x i₀ ^ s := by
  simp [coordPow]

lemma coordPow_of_ne (s : ℕ) (x : ι → ℂ) {j : ι} (hj : j ≠ i₀) : coordPow i₀ s x j = x j := by
  simp [coordPow, hj]

@[simp]
lemma coordRot_self (ζ : ℂ) (x : ι → ℂ) : coordRot i₀ ζ x i₀ = ζ * x i₀ := by
  simp [coordRot]

lemma coordRot_of_ne (ζ : ℂ) (x : ι → ℂ) {j : ι} (hj : j ≠ i₀) : coordRot i₀ ζ x j = x j := by
  simp [coordRot, hj]

lemma coordPow_coordRot {s : ℕ} {ζ : ℂ} (hζ : ζ ^ s = 1) (x : ι → ℂ) :
    coordPow i₀ s (coordRot i₀ ζ x) = coordPow i₀ s x := by
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [mul_pow, hζ]
  · simp [coordPow_of_ne _ _ hj, coordRot_of_ne _ _ hj]

lemma coordRot_coordRot (ζ ξ : ℂ) (x : ι → ℂ) :
    coordRot i₀ ζ (coordRot i₀ ξ x) = coordRot i₀ (ζ * ξ) x := by
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [mul_assoc]
  · simp [coordRot_of_ne _ _ hj]

@[simp]
lemma coordRot_one (x : ι → ℂ) : coordRot i₀ 1 x = x := by
  simp [coordRot]

lemma coordRoot_of_eq_zero {s : ℕ} (hs : s ≠ 0) {x : ι → ℂ} (hx : x i₀ = 0) :
    coordRoot i₀ s x = x := by
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [coordRoot, hx, Complex.zero_cpow (inv_ne_zero (Nat.cast_ne_zero.2 hs))]
  · simp [coordRoot, hj]

lemma coordPow_coordRoot {s : ℕ} (hs : s ≠ 0) (x : ι → ℂ) :
    coordPow i₀ s (coordRoot i₀ s x) = x := by
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [coordRoot, Complex.cpow_nat_inv_pow _ hs]
  · simp [coordPow_of_ne _ _ hj, coordRoot, hj]

@[fun_prop]
lemma differentiable_coordPow [Finite ι] (s : ℕ) :
    Differentiable ℂ (coordPow (ι := ι) i₀ s) := by
  have := Fintype.ofFinite ι
  refine differentiable_pi'' fun j ↦ ?_
  by_cases hj : j = i₀
  · subst hj
    simp only [coordPow_self]
    fun_prop
  · simp only [coordPow_of_ne _ _ hj]
    fun_prop

@[fun_prop]
lemma continuous_coordPow (s : ℕ) : Continuous (coordPow (ι := ι) i₀ s) :=
  continuous_id.update i₀ ((continuous_apply i₀).pow s)

@[fun_prop]
lemma differentiable_coordRot [Finite ι] (ζ : ℂ) :
    Differentiable ℂ (coordRot (ι := ι) i₀ ζ) := by
  have := Fintype.ofFinite ι
  refine differentiable_pi'' fun j ↦ ?_
  by_cases hj : j = i₀
  · subst hj
    simp only [coordRot_self]
    fun_prop
  · simp only [coordRot_of_ne _ _ hj]
    fun_prop

@[fun_prop]
lemma continuous_coordRot (ζ : ℂ) : Continuous (coordRot (ι := ι) i₀ ζ) :=
  continuous_id.update i₀ (continuous_const.mul (continuous_apply i₀))

/-- `zetaᵏ` only depends on `k` modulo `s`. -/
lemma zeta_pow_mod {s : ℕ} (hs : 0 < s) (a : ℕ) : zeta s ^ (a % s) = zeta s ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a s, pow_add, pow_mul, (isPrimitiveRoot_zeta hs).pow_eq_one,
    one_pow, mul_one]

lemma zeta_pow_add {s : ℕ} (hs : 0 < s) (k l : Fin s) :
    zeta s ^ ((k + l : Fin s) : ℕ) = zeta s ^ (k : ℕ) * zeta s ^ (l : ℕ) := by
  rw [Fin.val_add, zeta_pow_mod hs, pow_add]

lemma zeta_pow_pow {s : ℕ} (hs : 0 < s) (k : ℕ) : (zeta s ^ k) ^ s = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, (isPrimitiveRoot_zeta hs).pow_eq_one, one_pow]

lemma norm_zeta_pow {s : ℕ} (hs : 0 < s) (k : ℕ) : ‖zeta s ^ k‖ = 1 := by
  have h : ‖zeta s ^ k‖ ^ s = 1 := by rw [← norm_pow, zeta_pow_pow hs k, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hs.ne').1 h

/-- **The fibres of the Puiseux map are the orbits of the rotations.** -/
lemma exists_coordRot_eq {s : ℕ} (hs : 0 < s) {x y : ι → ℂ}
    (h : coordPow i₀ s x = coordPow i₀ s y) :
    ∃ k : Fin s, y = coordRot i₀ (zeta s ^ (k : ℕ)) x := by
  have hζ := isPrimitiveRoot_zeta hs
  have hi : y i₀ ^ s = x i₀ ^ s := by
    simpa using (congrFun h i₀).symm
  have hne : ∀ j, j ≠ i₀ → y j = x j := fun j hj ↦ by
    simpa [coordPow_of_ne _ _ hj] using (congrFun h j).symm
  suffices ∃ k : Fin s, y i₀ = zeta s ^ (k : ℕ) * x i₀ by
    obtain ⟨k, hk⟩ := this
    refine ⟨k, funext fun j ↦ ?_⟩
    by_cases hj : j = i₀
    · subst hj
      simpa using hk
    · rw [coordRot_of_ne _ _ hj, hne j hj]
  by_cases hx : x i₀ = 0
  · refine ⟨⟨0, hs⟩, ?_⟩
    rw [hx, zero_pow hs.ne'] at hi
    simp [hx, pow_eq_zero_iff hs.ne' |>.1 hi]
  · haveI : NeZero s := ⟨hs.ne'⟩
    obtain ⟨i, hi', hζi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := y i₀ / x i₀)
      (by rw [div_pow, hi, div_self (pow_ne_zero _ hx)])
    exact ⟨⟨i, hi'⟩, by rw [hζi, div_mul_cancel₀ _ hx]⟩

/-! ### The splitting `ℂ^ι ≅ ℂ^{ι ∖ i₀} × ℂ` -/

variable (i₀)

/-- The splitting `x ↦ ((x j)_{j ≠ i₀}, x i₀)`. -/
def splitAt (x : ι → ℂ) : ({j // j ≠ i₀} → ℂ) × ℂ :=
  (fun j ↦ x j, x i₀)

/-- The inverse of `Kummer.splitAt`. -/
def unsplitAt (p : ({j // j ≠ i₀} → ℂ) × ℂ) : ι → ℂ :=
  fun j ↦ if h : j = i₀ then p.2 else p.1 ⟨j, h⟩

variable {i₀}

@[simp]
lemma unsplitAt_splitAt (x : ι → ℂ) : unsplitAt i₀ (splitAt i₀ x) = x := by
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [unsplitAt, splitAt]
  · simp [unsplitAt, splitAt, hj]

omit [DecidableEq ι] in
lemma differentiable_splitAt [Finite ι] : Differentiable ℂ (splitAt (ι := ι) i₀) := by
  have := Fintype.ofFinite {j // j ≠ i₀}
  have := Fintype.ofFinite ι
  unfold splitAt
  fun_prop

lemma differentiable_unsplitAt [Finite ι] : Differentiable ℂ (unsplitAt (ι := ι) i₀) := by
  have := Fintype.ofFinite {j // j ≠ i₀}
  have := Fintype.ofFinite ι
  refine differentiable_pi'' fun j ↦ ?_
  by_cases hj : j = i₀
  · simp only [unsplitAt, dite_eq_left hj]
    fun_prop
  · simp only [unsplitAt, dite_eq_right hj]
    fun_prop

lemma coordPow_unsplitAt (s : ℕ) (p : ({j // j ≠ i₀} → ℂ) × ℂ) :
    coordPow i₀ s (unsplitAt i₀ p) = unsplitAt i₀ (powMap s p) := by
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [unsplitAt]
  · simp [coordPow_of_ne _ _ hj, unsplitAt, hj]

lemma splitAt_coordPow (s : ℕ) (x : ι → ℂ) :
    splitAt i₀ (coordPow i₀ s x) = powMap s (splitAt i₀ x) := by
  refine Prod.ext (funext fun j ↦ ?_) ?_
  · exact coordPow_of_ne _ _ j.2
  · simp [splitAt]

/-! ### Holomorphic functions on `α⁻¹(G)` -/

variable [Finite ι]

omit [DecidableEq ι] in
/-- The zero set of the coordinate `i₀` has empty interior. -/
lemma interior_inter_preimage_apply_eq_empty (U : Set (ι → ℂ)) :
    interior (U ∩ (fun x : ι → ℂ ↦ x i₀) ⁻¹' {0}) = ∅ := by
  have := Fintype.ofFinite ι
  have h : interior (univ ∩ (fun x : ι → ℂ ↦ x i₀) ⁻¹' {0}) = ∅ :=
    AnalyticOnNhd.interior_inter_preimage_zero_eq_empty (g := fun x : ι → ℂ ↦ x i₀)
      (fun x _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i₀).analyticAt x)
      isPreconnected_univ (z := fun _ ↦ (1 : ℂ)) trivial one_ne_zero
  exact subset_empty_iff.1 (h ▸ interior_mono (inter_subset_inter_left _ (subset_univ U)))

/-- **Holomorphic functions on the preimage under the Puiseux map**: a holomorphic function on
`α⁻¹(G)` is `∑_{j < s} tʲ gⱼ ∘ α` with `gⱼ` holomorphic on `G`, where `t = x i₀`. -/
theorem exists_eqOn_sum_pow_mul_comp_coordPow {s : ℕ} (hs : 0 < s) {G : Set (ι → ℂ)}
    (hG : IsOpen G) {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (coordPow i₀ s ⁻¹' G)) :
    ∃ g : Fin s → (ι → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (g j) G) ∧
      EqOn f (fun x ↦ ∑ j : Fin s, x i₀ ^ (j : ℕ) * g j (coordPow i₀ s x))
        (coordPow i₀ s ⁻¹' G) := by
  have := Fintype.ofFinite ι
  set V : Set (({j // j ≠ i₀} → ℂ) × ℂ) := unsplitAt i₀ ⁻¹' G
  have hV : IsOpen V := hG.preimage differentiable_unsplitAt.continuous
  have hpre : powMap s ⁻¹' V = unsplitAt i₀ ⁻¹' (coordPow i₀ s ⁻¹' G) := by
    ext p
    simp only [V, mem_preimage, coordPow_unsplitAt]
  have hf' : DifferentiableOn ℂ (f ∘ unsplitAt i₀) (powMap s ⁻¹' V) := by
    rw [hpre]
    exact hf.comp differentiable_unsplitAt.differentiableOn fun _ hp ↦ hp
  have hVo : IsOpen (powMap s ⁻¹' V) := hV.preimage (continuous_powMap s)
  obtain ⟨g, hgd, hgeq⟩ := exists_eqOn_sum_pow_mul_comp_powMap hs hV
    (hf'.mono sdiff_subset) fun x hx hx0 ↦ by
      have hxm : x ∈ powMap s ⁻¹' V := by
        change (x.1, x.2 ^ s) ∈ V
        rw [hx0, zero_pow hs.ne']
        rw [← hx0]
        exact hx
      exact ((hf'.continuousOn.continuousAt (hVo.mem_nhds hxm)).norm.tendsto.isBoundedUnder_le).mono
        nhdsWithin_le_nhds
  refine ⟨fun j ↦ g j ∘ splitAt i₀, fun j ↦ (hgd j).comp differentiable_splitAt.differentiableOn
    fun x hx ↦ show unsplitAt i₀ (splitAt i₀ x) ∈ G by rw [unsplitAt_splitAt]; exact hx, ?_⟩
  have hGo : IsOpen (coordPow i₀ s ⁻¹' G) := hG.preimage (continuous_coordPow s)
  refine EqOn.of_eqOn_diff_zero (g := fun x : ι → ℂ ↦ x i₀) hGo
    (interior_inter_preimage_apply_eq_empty _) hf.continuousOn
    ?_ fun x hx ↦ ?_
  · refine continuousOn_finsetSum _ fun j _ ↦ ((continuous_apply i₀).pow _).continuousOn.mul ?_
    refine ((hgd j).continuousOn.comp differentiable_splitAt.continuous.continuousOn ?_).comp
      (continuous_coordPow s).continuousOn fun x hx ↦ hx
    intro x hx
    exact show unsplitAt i₀ (splitAt i₀ x) ∈ G by rw [unsplitAt_splitAt]; exact hx
  · have hp : splitAt i₀ x ∈ powMap s ⁻¹' V \ Prod.snd ⁻¹' {0} := by
      refine ⟨?_, hx.2⟩
      rw [hpre]
      simpa using hx.1
    have := hgeq hp
    simp only [Function.comp_apply, unsplitAt_splitAt] at this
    rw [this]
    simp only [Function.comp_apply, splitAt_coordPow]
    rfl

/-- `∑_{k < s} (ζʲ)ᵏ` is `s` for `j = 0` and `0` for `0 < j < s`. -/
lemma sum_zeta_pow_pow {s : ℕ} (hs : 0 < s) (j : Fin s) :
    ∑ k : Fin s, (zeta s ^ (j : ℕ)) ^ (k : ℕ) = if (j : ℕ) = 0 then (s : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (zeta s ^ (j : ℕ)) ^ k)]
  split_ifs with hj
  · simp [hj]
  · have hne : zeta s ^ (j : ℕ) ≠ 1 :=
      (isPrimitiveRoot_zeta hs).pow_ne_one_of_pos_of_lt hj j.2
    rw [geom_sum_eq hne, zeta_pow_pow hs, sub_self, zero_div]

/-- **Descent of holomorphy along the Puiseux map**: if `h ∘ α` is holomorphic on `α⁻¹(G)`, then
`h` is holomorphic on `G`. -/
theorem differentiableOn_of_comp_coordPow {s : ℕ} (hs : 0 < s) {G : Set (ι → ℂ)}
    (hG : IsOpen G) {h : (ι → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ (h ∘ coordPow i₀ s) (coordPow i₀ s ⁻¹' G)) :
    DifferentiableOn ℂ h G := by
  obtain ⟨g, hgd, hgeq⟩ := exists_eqOn_sum_pow_mul_comp_coordPow hs hG hh
  refine (hgd ⟨0, hs⟩).congr fun y hy ↦ ?_
  set x := coordRoot i₀ s y
  have hxy : coordPow i₀ s x = y := coordPow_coordRoot hs.ne' y
  have hk (k : Fin s) : h y = ∑ j : Fin s, (x i₀ ^ (j : ℕ) * g j y) *
      (zeta s ^ (j : ℕ)) ^ (k : ℕ) := by
    have hmem : coordRot i₀ (zeta s ^ (k : ℕ)) x ∈ coordPow i₀ s ⁻¹' G := by
      rw [mem_preimage, coordPow_coordRot (zeta_pow_pow hs k), hxy]
      exact hy
    have := hgeq hmem
    simp only [Function.comp_apply, coordPow_coordRot (zeta_pow_pow hs k), hxy,
      coordRot_self] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k : ℕ) (j : ℕ)]
    ring
  have hsum : (s : ℂ) * h y = s * g ⟨0, hs⟩ y := by
    calc (s : ℂ) * h y = ∑ k : Fin s, h y := by simp
      _ = ∑ k : Fin s, ∑ j : Fin s, (x i₀ ^ (j : ℕ) * g j y) * (zeta s ^ (j : ℕ)) ^ (k : ℕ) :=
          Finset.sum_congr rfl fun k _ ↦ hk k
      _ = ∑ j : Fin s, (x i₀ ^ (j : ℕ) * g j y) * ∑ k : Fin s, (zeta s ^ (j : ℕ)) ^ (k : ℕ) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ ↦ (Finset.mul_sum _ _ _).symm
      _ = s * g ⟨0, hs⟩ y := by
          simp_rw [sum_zeta_pow_pow hs]
          rw [Finset.sum_eq_single ⟨0, hs⟩ (fun j _ hj ↦ by
            rw [ite_eq_right fun h ↦ hj (Fin.ext h), mul_zero]) (fun h ↦ absurd (Finset.mem_univ _) h)]
          simp [mul_comm]
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hs.ne') hsum

/-! ### Pieces of the preimage off `t = 0` -/

/-- The powers of `zeta s` below `s` are at pairwise distance at least some `d > 0`. -/
lemma exists_le_norm_zeta_pow_sub {s : ℕ} (hs : 0 < s) :
    ∃ d > 0, ∀ k l : Fin s, k ≠ l → d ≤ ‖zeta s ^ (k : ℕ) - zeta s ^ (l : ℕ)‖ := by
  classical
  set S := (Finset.univ : Finset (Fin s × Fin s)).filter fun p ↦ p.1 ≠ p.2
  have hpos : ∀ p ∈ S, 0 < ‖zeta s ^ (p.1 : ℕ) - zeta s ^ (p.2 : ℕ)‖ := fun p hp ↦ by
    refine norm_pos_iff.2 (sub_ne_zero.2 fun h ↦ (Finset.mem_filter.1 hp).2 (Fin.ext ?_))
    exact (isPrimitiveRoot_zeta hs).pow_inj p.1.2 p.2.2 h
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := S.exists_min_image (fun p ↦ ‖zeta s ^ (p.1 : ℕ) -
      zeta s ^ (p.2 : ℕ)‖) hS
    exact ⟨_, hpos p hp, fun k l hkl ↦ hmin (k, l) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hkl⟩)⟩
  · refine ⟨1, one_pos, fun k l hkl ↦ absurd ⟨(k, l), ?_⟩ hS⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hkl⟩

/-- If `aˢ` is close to `bˢ`, then `a` is close to `ζᵏ b` for some `k`. -/
lemma exists_norm_sub_zeta_pow_mul_lt {s : ℕ} (hs : 0 < s) {a b : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ‖a ^ s - b ^ s‖ < r ^ s) : ∃ k : Fin s, ‖a - zeta s ^ (k : ℕ) * b‖ < r := by
  by_contra hcon
  push Not at hcon
  have hζ := isPrimitiveRoot_zeta hs
  have hle : ∀ μ ∈ Polynomial.nthRootsFinset s (1 : ℂ), r ≤ ‖a - μ * b‖ := fun μ hμ ↦ by
    haveI : NeZero s := ⟨hs.ne'⟩
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hs _).1 hμ)
    exact hcon ⟨i, hi⟩
  have : r ^ s ≤ ‖a ^ s - b ^ s‖ := by
    rw [hζ.pow_sub_pow_eq_prod_sub_mul a b hs, norm_prod]
    calc r ^ s = ∏ _μ ∈ Polynomial.nthRootsFinset s (1 : ℂ), r := by
          rw [Finset.prod_const, hζ.card_nthRootsFinset]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ hr.le) hle
  exact absurd h (not_lt.2 this)

/-- **The preimage of a small neighbourhood off `t = 0` splits into `s` pieces.** Let `y'` be a
point with `t = y' i₀ ≠ 0` and `O k` a neighbourhood of `ζᵏ y'` for every `k < s`. There are a
neighbourhood `V` of `α(y')` and open pieces `P k ⊆ O k` such that every point of `α⁻¹(V)` lies
in exactly one piece, and exactly one rotation `ζᵏ` takes it into the piece `P 0`. -/
theorem exists_pieces_coordPow {s : ℕ} (hs : 0 < s) {y' : ι → ℂ} (hy' : y' i₀ ≠ 0)
    {O : Fin s → Set (ι → ℂ)} (hO : ∀ k : Fin s, O k ∈ 𝓝 (coordRot i₀ (zeta s ^ (k : ℕ)) y')) :
    ∃ V ∈ 𝓝 (coordPow i₀ s y'), ∃ P : Fin s → Set (ι → ℂ), (∀ k, IsOpen (P k)) ∧
      (∀ k, P k ⊆ O k) ∧ (∀ k, P k ⊆ coordPow i₀ s ⁻¹' V) ∧
      (∀ x ∈ coordPow i₀ s ⁻¹' V, ∃! k, x ∈ P k) ∧
      (∀ x ∈ coordPow i₀ s ⁻¹' V, ∃! k : Fin s, coordRot i₀ (zeta s ^ (k : ℕ)) x ∈ P ⟨0, hs⟩) := by
  have := Fintype.ofFinite ι
  set u : Fin s → ℂ := fun k ↦ zeta s ^ (k : ℕ)
  have hu : ∀ k, ‖u k‖ = 1 := fun k ↦ norm_zeta_pow hs k
  obtain ⟨d, hd, hdist⟩ := exists_le_norm_zeta_pow_sub hs
  choose ε hε hεO using fun k ↦ Metric.mem_nhds_iff.1 (hO k)
  set t := y' i₀
  have ht : 0 < ‖t‖ := norm_pos_iff.2 hy'
  -- the radius of the pieces
  obtain ⟨r, hr, hrd, hrε⟩ : ∃ r > 0, 2 * r ≤ d * ‖t‖ ∧ ∀ k, r ≤ ε k := by
    refine ⟨min (d * ‖t‖ / 2) (Finset.univ.inf' ⟨⟨0, hs⟩, Finset.mem_univ _⟩ ε),
      lt_min (by positivity) ((Finset.lt_inf'_iff _).2 fun k _ ↦ hε k), ?_, fun k ↦
        (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ k))⟩
    linarith [min_le_left (d * ‖t‖ / 2) (Finset.univ.inf' ⟨⟨0, hs⟩, Finset.mem_univ _⟩ ε)]
  set y := coordPow i₀ s y'
  set V := ball y (min r (r ^ s))
  have hρ : 0 < min r (r ^ s) := lt_min hr (pow_pos hr s)
  set P : Fin s → Set (ι → ℂ) := fun k ↦
    coordPow i₀ s ⁻¹' V ∩ ball (coordRot i₀ (u k) y') r
  -- the points of the fibre are far apart
  have hsep : ∀ k l : Fin s, ∀ z : ℂ, ‖z - u k * t‖ < r → ‖z - u l * t‖ < r → k = l := by
    intro k l z hk hl
    by_contra hkl
    have h1 : d * ‖t‖ ≤ ‖u k * t - u l * t‖ := by
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hdist k l hkl) (norm_nonneg _)
    have h2 : ‖u k * t - u l * t‖ < 2 * r := by
      calc ‖u k * t - u l * t‖ = ‖(z - u l * t) - (z - u k * t)‖ := by ring_nf
        _ ≤ ‖z - u l * t‖ + ‖z - u k * t‖ := norm_sub_le _ _
        _ < 2 * r := by linarith
    linarith
  have hmemP : ∀ k x, x ∈ coordPow i₀ s ⁻¹' V → (x ∈ P k ↔ ‖x i₀ - u k * t‖ < r) := by
    intro k x hx
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨hx, ?_⟩⟩
    · have := (mem_ball_iff_norm.1 h.2)
      have h' := (norm_le_pi_norm (x - coordRot i₀ (u k) y') i₀).trans_lt this
      simpa [t] using h'
    · rw [mem_ball_iff_norm, pi_norm_lt_iff hr]
      intro j
      by_cases hj : j = i₀
      · subst hj
        simpa using h
      · have hxV := mem_ball_iff_norm.1 hx
        have := (norm_le_pi_norm (coordPow i₀ s x - y) j).trans_lt hxV
        simp only [Pi.sub_apply, y, coordPow_of_ne _ _ hj] at this
        simp only [Pi.sub_apply, coordRot_of_ne _ _ hj]
        exact this.trans_le (min_le_left _ _)
  have hex : ∀ x ∈ coordPow i₀ s ⁻¹' V, ∃ k, ‖x i₀ - u k * t‖ < r := by
    intro x hx
    have hxV := mem_ball_iff_norm.1 hx
    have := (norm_le_pi_norm (coordPow i₀ s x - y) i₀).trans_lt hxV
    simp only [Pi.sub_apply, y, coordPow_self] at this
    exact exists_norm_sub_zeta_pow_mul_lt hs hr (this.trans_le (min_le_right _ _))
  refine ⟨V, ball_mem_nhds _ hρ, P, fun k ↦ ((isOpen_ball.preimage (continuous_coordPow s)).inter
    isOpen_ball), fun k x hx ↦ hεO k (ball_subset_ball (hrε k) hx.2), fun k x hx ↦ hx.1,
    fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨k, hk⟩ := hex x hx
    exact ⟨k, (hmemP k x hx).2 hk, fun l hl ↦ hsep l k _ ((hmemP l x hx).1 hl) hk⟩
  · have hrot : ∀ k, coordRot i₀ (u k) x ∈ coordPow i₀ s ⁻¹' V := fun k ↦ by
      rw [mem_preimage, coordPow_coordRot (zeta_pow_pow hs k)]
      exact hx
    have hiff : ∀ k l : Fin s, u k * u l = 1 →
        (coordRot i₀ (u k) x ∈ P ⟨0, hs⟩ ↔ ‖x i₀ - u l * t‖ < r) := by
      intro k l hkl
      rw [hmemP _ _ (hrot k), coordRot_self]
      have : u k * x i₀ - u ⟨0, hs⟩ * t = u k * (x i₀ - u l * t) := by
        have h0 : u ⟨0, hs⟩ = 1 := by simp [u]
        rw [h0]
        linear_combination t * hkl
      rw [this, norm_mul, hu, one_mul]
    have hinv : ∀ k : Fin s, ∃ l : Fin s, u k * u l = 1 := fun k ↦
      ⟨⟨(s - k) % s, Nat.mod_lt _ hs⟩, by
        simp only [u]
        rw [zeta_pow_mod hs, ← pow_add, Nat.add_sub_cancel' k.2.le,
          (isPrimitiveRoot_zeta hs).pow_eq_one]⟩
    obtain ⟨l, hl⟩ := hex x hx
    obtain ⟨k, hk⟩ : ∃ k : Fin s, u k * u l = 1 := by
      obtain ⟨k, hk⟩ := hinv l
      exact ⟨k, by rw [mul_comm]; exact hk⟩
    refine ⟨k, (hiff k l hk).2 hl, fun k' hk' ↦ ?_⟩
    obtain ⟨l', hl'⟩ := hinv k'
    have := hsep l' l _ ((hiff k' l' hl').1 hk') hl
    subst this
    have h1 : u k' = u k := by
      calc u k' = u k' * (u l' * u k) := by rw [mul_comm (u l') (u k), hk, mul_one]
        _ = u k := by rw [← mul_assoc, hl', one_mul]
    exact Fin.ext ((isPrimitiveRoot_zeta hs).pow_inj k'.2 k.2 h1)

omit [Finite ι] in
/-- **The roots of `tˢ` depend continuously on `t`**: if `α(y)` is close to `α(x)`, then `y` is
close to `ζᵏ x` for some `k`. -/
lemma exists_coordRot_norm_sub_lt [Fintype ι] {s : ℕ} (hs : 0 < s) {x y : ι → ℂ} {r : ℝ}
    (hr : 0 < r) (h : ‖coordPow i₀ s y - coordPow i₀ s x‖ < min r (r ^ s)) :
    ∃ k : Fin s, ‖y - coordRot i₀ (zeta s ^ (k : ℕ)) x‖ < r := by
  have hi : ‖y i₀ ^ s - x i₀ ^ s‖ < r ^ s := by
    have := (norm_le_pi_norm (coordPow i₀ s y - coordPow i₀ s x) i₀).trans_lt h
    simp only [Pi.sub_apply, coordPow_self] at this
    exact this.trans_le (min_le_right _ _)
  obtain ⟨k, hk⟩ := exists_norm_sub_zeta_pow_mul_lt hs hr hi
  refine ⟨k, (pi_norm_lt_iff hr).2 fun j ↦ ?_⟩
  by_cases hj : j = i₀
  · subst hj
    simpa using hk
  · have := (norm_le_pi_norm (coordPow i₀ s y - coordPow i₀ s x) j).trans_lt h
    simp only [Pi.sub_apply, coordPow_of_ne _ _ hj] at this
    simp only [Pi.sub_apply, coordRot_of_ne _ _ hj]
    exact this.trans_le (min_le_left _ _)

omit [Finite ι] in
/-- A sum over all rotations is invariant under rotations. -/
lemma sum_comp_coordRot_coordRot {s : ℕ} (hs : 0 < s) {M : Type*} [AddCommMonoid M]
    (G : (ι → ℂ) → M) (j : Fin s) (x : ι → ℂ) :
    ∑ l : Fin s, G (coordRot i₀ (zeta s ^ (l : ℕ)) (coordRot i₀ (zeta s ^ (j : ℕ)) x)) =
      ∑ l : Fin s, G (coordRot i₀ (zeta s ^ (l : ℕ)) x) := by
  haveI : NeZero s := ⟨hs.ne'⟩
  simp_rw [coordRot_coordRot, ← zeta_pow_add hs]
  exact Fintype.sum_equiv (Equiv.addRight j) _ _ fun _ ↦ rfl

omit [Finite ι] in
/-- A sum over all rotations only depends on the image under the Puiseux map. -/
lemma sum_comp_coordRot_coordRoot {s : ℕ} (hs : 0 < s) {M : Type*} [AddCommMonoid M]
    (G : (ι → ℂ) → M) (x : ι → ℂ) :
    ∑ l : Fin s, G (coordRot i₀ (zeta s ^ (l : ℕ)) (coordRoot i₀ s (coordPow i₀ s x))) =
      ∑ l : Fin s, G (coordRot i₀ (zeta s ^ (l : ℕ)) x) := by
  obtain ⟨j, hj⟩ := exists_coordRot_eq hs
    (coordPow_coordRoot (i₀ := i₀) hs.ne' (coordPow i₀ s x)).symm
  rw [hj, sum_comp_coordRot_coordRot hs]

/-! ### Pieces -/

variable (i₀) in
/-- **`P₀` is a piece of `α⁻¹(V₀)`**: `V₀` is open, `P₀ ⊆ α⁻¹(V₀)`, membership in `P₀` is locally
constant on `α⁻¹(V₀)`, and every point of `α⁻¹(V₀)` has exactly one rotation `ζᵏ x` in `P₀`. -/
structure IsPiece (s : ℕ) (V₀ P₀ : Set (ι → ℂ)) : Prop where
  isOpen : IsOpen V₀
  subset : P₀ ⊆ coordPow i₀ s ⁻¹' V₀
  eventually_mem_iff : ∀ x ∈ coordPow i₀ s ⁻¹' V₀, ∀ᶠ z in 𝓝 x, (z ∈ P₀ ↔ x ∈ P₀)
  existsUnique : ∀ x ∈ coordPow i₀ s ⁻¹' V₀,
    ∃! k : Fin s, coordRot i₀ (zeta s ^ (k : ℕ)) x ∈ P₀

namespace IsPiece

variable {s : ℕ} {V₀ P₀ : Set (ι → ℂ)} (hP : IsPiece i₀ s V₀ P₀)
include hP

omit [Finite ι] in
lemma isOpen_piece : IsOpen P₀ :=
  isOpen_iff_mem_nhds.2 fun x hx ↦ Filter.mem_of_superset
    (hP.eventually_mem_iff x (hP.subset hx)) fun _ hz ↦ hz.2 hx

omit [Finite ι] in
open Classical in
/-- Over a point of `P₀`, only the trivial rotation lands in `P₀`. -/
lemma sum_ite {M : Type*} [AddCommMonoid M] (hs : 0 < s) {x : ι → ℂ} (hx : x ∈ P₀)
    (G : Fin s → M) :
    ∑ k : Fin s, (if coordRot i₀ (zeta s ^ (k : ℕ)) x ∈ P₀ then G k else 0) = G ⟨0, hs⟩ := by
  obtain ⟨k₀, -, huniq⟩ := hP.existsUnique x (hP.subset hx)
  have h0 : coordRot i₀ (zeta s ^ ((⟨0, hs⟩ : Fin s) : ℕ)) x ∈ P₀ := by simpa using hx
  rw [Finset.sum_eq_single ⟨0, hs⟩ (fun k _ hk ↦ ite_eq_right fun h ↦ hk ((huniq k h).trans
    (huniq _ h0).symm)) (fun h ↦ absurd (Finset.mem_univ _) h), ite_eq_left h0]

omit [Finite ι] in
/-- Every point of `α⁻¹(V₀)` has a rotation in `P₀`. -/
lemma exists_coordRot_mem {x : ι → ℂ} (hx : x ∈ coordPow i₀ s ⁻¹' V₀) :
    ∃ k : Fin s, coordRot i₀ (zeta s ^ (k : ℕ)) x ∈ P₀ :=
  (hP.existsUnique x hx).exists

omit [Finite ι] in
open Classical in
/-- A function holomorphic on `P₀ ∩ Z`, extended by zero, is holomorphic on `Z ⊆ α⁻¹(V₀)`. -/
lemma differentiableOn_ite {Z : Set (ι → ℂ)} (hZ : IsOpen Z) (hZV : Z ⊆ coordPow i₀ s ⁻¹' V₀)
    {G : (ι → ℂ) → ℂ} (hG : DifferentiableOn ℂ G (P₀ ∩ Z)) :
    DifferentiableOn ℂ (fun x ↦ if x ∈ P₀ then G x else 0) Z := by
  classical
  intro x hx
  have hev := hP.eventually_mem_iff x (hZV hx)
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases hxP : x ∈ P₀
  · have hGx : DifferentiableAt ℂ G x :=
      hG.differentiableAt ((hP.isOpen_piece.inter hZ).mem_nhds ⟨hxP, hx⟩)
    refine hGx.congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    rw [ite_eq_left (hz.2 hxP)]
  · refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    rw [ite_eq_right fun h ↦ hxP (hz.1 h)]

end IsPiece

/-- **Pieces off `t = 0`**: near a point `y'` with `y' i₀ ≠ 0`, there is a piece `P₀ ⊆ O` of
`α⁻¹(V₀)` for an open `V₀ ∋ α(y')`, for any neighbourhood `O` of `y'`. -/
theorem exists_isPiece {s : ℕ} (hs : 0 < s) {y' : ι → ℂ} (hy' : y' i₀ ≠ 0) {O : Set (ι → ℂ)}
    (hO : O ∈ 𝓝 y') : ∃ V₀ P₀ : Set (ι → ℂ), coordPow i₀ s y' ∈ V₀ ∧ P₀ ⊆ O ∧
      IsPiece i₀ s V₀ P₀ := by
  classical
  set O' : Fin s → Set (ι → ℂ) := fun k ↦ if (k : ℕ) = 0 then O else Set.univ
  have hO' : ∀ k : Fin s, O' k ∈ 𝓝 (coordRot i₀ (zeta s ^ (k : ℕ)) y') := fun k ↦ by
    by_cases hk : (k : ℕ) = 0
    · simpa [O', hk] using hO
    · simp [O', hk]
  obtain ⟨V, hV, Pc, hPco, hPcO, hPcV, huniqP, huniqR⟩ := exists_pieces_coordPow hs hy' hO'
  set k₀ : Fin s := ⟨0, hs⟩
  have hsub : interior V ⊆ V := interior_subset
  refine ⟨interior V, Pc k₀ ∩ coordPow i₀ s ⁻¹' interior V, mem_interior_iff_mem_nhds.2 hV,
    fun x hx ↦ by simpa [O', k₀] using hPcO k₀ hx.1, ⟨isOpen_interior, fun x hx ↦ hx.2,
    fun x hx ↦ ?_, fun x hx ↦ ?_⟩⟩
  · obtain ⟨k, hk, huk⟩ := huniqP x (hsub hx)
    have hopen : IsOpen (Pc k ∩ coordPow i₀ s ⁻¹' interior V) :=
      (hPco k).inter (isOpen_interior.preimage (continuous_coordPow s))
    filter_upwards [hopen.mem_nhds ⟨hk, hx⟩] with z hz
    have hzk : ∀ l, z ∈ Pc l → l = k := fun l hl ↦
      ((huniqP z (hsub hz.2)).unique hl hz.1)
    constructor
    · rintro ⟨hz0, -⟩
      have := hzk k₀ hz0
      exact ⟨this ▸ hk, hx⟩
    · rintro ⟨hx0, -⟩
      have := huk k₀ hx0
      exact ⟨this ▸ hz.1, hz.2⟩
  · have hrot : ∀ k : Fin s, coordRot i₀ (zeta s ^ (k : ℕ)) x ∈ coordPow i₀ s ⁻¹' interior V :=
      fun k ↦ by rw [Set.mem_preimage, coordPow_coordRot (zeta_pow_pow hs k)]; exact hx
    obtain ⟨k, hk, huk⟩ := huniqR x (hsub hx)
    exact ⟨k, ⟨hk, hrot k⟩, fun l hl ↦ huk l hl.1⟩

end

end Kummer
