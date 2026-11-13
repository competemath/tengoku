import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sphere-target homotopy glue

For maps into the unit sphere of a real inner product space `E`, pointwise
non-antipodality lets one build straight-line ("chord") homotopies after
renormalization.  Main results:

* `Submission.dist_lt_two_of_ne_neg`: two non-antipodal points of the unit sphere are
  at distance `< 2`;
* `Submission.chordHomotopyRel` / `Submission.homotopicRel_of_dist_lt_two`: two
  sphere-valued maps that are pointwise at distance `< 2` are homotopic rel any set on
  which they agree, by normalizing the chord between them;
* `Submission.genLoop_homotopic_of_dist_lt_two`: generalized loops in the sphere that
  are pointwise at distance `< 2` are homotopic rel the cube boundary;
* `Submission.normalizeMap`: the pointwise normalization of a nonvanishing map into
  `E`, as a map to the unit sphere;
* `Submission.normalizedRawHomotopyRel`: a sphere-valued map `f` is homotopic rel `S`
  to the normalization of any map `g` into `E` with `dist (f a) (g a) < 1` pointwise
  and `g = f` on `S`.
-/

noncomputable section

open scoped Topology unitInterval RealInnerProductSpace
open Topology.Homotopy Metric

namespace Submission

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit sphere in a real inner product space.-/
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Type _ :=
  Metric.sphere (0 : E) 1

theorem UnitSphere.norm_coe (v : UnitSphere E) : ‖(v : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp v.2

theorem UnitSphere.coe_ne_neg_coe {u v : UnitSphere E} (h : u ≠ -v) :
    (u : E) ≠ -(v : E) := fun hc =>
  h (Subtype.ext (hc.trans (coe_neg_sphere v).symm))

/-- Two non-antipodal points of the unit sphere are at distance less than `2`.-/
theorem dist_lt_two_of_ne_neg (u v : UnitSphere E) (h : u ≠ -v) : dist u v < 2 := by
  have hu : ‖(u : E)‖ = 1 := UnitSphere.norm_coe u
  have hv : ‖(v : E)‖ = 1 := UnitSphere.norm_coe v
  have hne : ⟪(u : E), (v : E)⟫ ≠ -1 := fun hc =>
    UnitSphere.coe_ne_neg_coe h ((inner_eq_neg_one_iff_of_norm_eq_one hu hv).mp hc)
  have hge : -1 ≤ ⟪(u : E), (v : E)⟫ := neg_one_le_real_inner_of_norm_eq_one hu hv
  have hlt : -1 < ⟪(u : E), (v : E)⟫ := lt_of_le_of_ne hge (Ne.symm hne)
  rw [Subtype.dist_eq, dist_eq_norm]
  refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
  rw [norm_sub_sq_real, hu, hv]
  nlinarith

/-- A point of the unit sphere is not antipodal to any point at distance less
than `2` from it.-/
theorem ne_neg_of_dist_lt_two (u v : UnitSphere E) (h : dist u v < 2) : u ≠ -v := by
  rintro rfl
  have hv : ‖(v : E)‖ = 1 := UnitSphere.norm_coe v
  rw [Subtype.dist_eq, coe_neg_sphere, dist_eq_norm] at h
  have : -(v : E) - v = (-2 : ℝ) • (v : E) := by module
  rw [this, norm_smul, Real.norm_eq_abs, hv] at h
  norm_num at h

/-- Normalizing a nonzero vector produces a unit vector.-/
theorem norm_normalize {v : E} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- The chord between two non-antipodal unit vectors does not vanish.-/
theorem chord_ne_zero {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : u ≠ -w) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (1 - s) • u + s • w ≠ 0 := by
  intro hc
  have hkey : (1 - s) • u = s • (-w) := by
    rw [smul_neg]
    exact add_eq_zero_iff_eq_neg.mp hc
  have hnorm : 1 - s = s := by
    have h1 : ‖(1 - s) • u‖ = ‖s • (-w)‖ := by rw [hkey]
    rw [norm_smul, norm_smul, hu, norm_neg, hw, mul_one, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg hs0] at h1
    exact h1
  have hsne : s ≠ 0 := by intro h0; rw [h0, sub_zero] at hnorm; norm_num at hnorm
  rw [hnorm] at hkey
  exact h (smul_right_injective E hsne hkey)

section Chord

variable {A : Type*} [TopologicalSpace A]

/-- The chord between two sphere-valued maps, as a continuous map `I × A → E`.-/
def chordMap (f g : C(A, UnitSphere E)) : C(I × A, E) where
  toFun sa := (1 - (sa.1 : ℝ)) • ((f sa.2 : E)) + (sa.1 : ℝ) • ((g sa.2 : E))
  continuous_toFun := by
    have hf : Continuous fun sa : I × A => (f sa.2 : E) :=
      continuous_subtype_val.comp ((map_continuous f).comp continuous_snd)
    have hg : Continuous fun sa : I × A => (g sa.2 : E) :=
      continuous_subtype_val.comp ((map_continuous g).comp continuous_snd)
    have hs : Continuous fun sa : I × A => (sa.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub hs).smul hf).add (hs.smul hg)

theorem chordMap_ne_zero (f g : C(A, UnitSphere E)) (h : ∀ a, dist (f a) (g a) < 2)
    (sa : I × A) : chordMap f g sa ≠ 0 :=
  chord_ne_zero (UnitSphere.norm_coe (f sa.2)) (UnitSphere.norm_coe (g sa.2))
    (UnitSphere.coe_ne_neg_coe (ne_neg_of_dist_lt_two _ _ (h sa.2)))
    (sa.1.2.1) (sa.1.2.2)

/-- The normalized-chord homotopy between two sphere-valued maps that are pointwise
at distance `< 2`, rel any set on which they agree.-/
def chordHomotopyRel (f g : C(A, UnitSphere E)) (h : ∀ a, dist (f a) (g a) < 2)
    (S : Set A) (hS : ∀ a ∈ S, f a = g a) : ContinuousMap.HomotopyRel f g S where
  toFun sa :=
    ⟨‖chordMap f g sa‖⁻¹ • chordMap f g sa,
      mem_sphere_zero_iff_norm.mpr
        (norm_normalize (chordMap_ne_zero f g h sa))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (((map_continuous (chordMap f g)).norm).inv₀ fun sa =>
      norm_ne_zero_iff.mpr (chordMap_ne_zero f g h sa)).smul
        (map_continuous (chordMap f g))
  map_zero_left a := by
    apply Subtype.ext
    show ‖chordMap f g (0, a)‖⁻¹ • chordMap f g (0, a) = ((f a : E))
    have hc : chordMap f g (0, a) = (f a : E) := by
      show (1 - ((0 : I) : ℝ)) • ((f a : E)) + ((0 : I) : ℝ) • ((g a : E)) = (f a : E)
      rw [Set.Icc.coe_zero]
      simp
    rw [hc, UnitSphere.norm_coe (f a)]
    simp
  map_one_left a := by
    apply Subtype.ext
    show ‖chordMap f g (1, a)‖⁻¹ • chordMap f g (1, a) = ((g a : E))
    have hc : chordMap f g (1, a) = (g a : E) := by
      show (1 - ((1 : I) : ℝ)) • ((f a : E)) + ((1 : I) : ℝ) • ((g a : E)) = (g a : E)
      rw [Set.Icc.coe_one]
      simp
    rw [hc, UnitSphere.norm_coe (g a)]
    simp
  prop' s a ha := by
    apply Subtype.ext
    show ‖chordMap f g (s, a)‖⁻¹ • chordMap f g (s, a) = ((f a : E))
    have hc : chordMap f g (s, a) = (f a : E) := by
      show (1 - (s : ℝ)) • ((f a : E)) + (s : ℝ) • ((g a : E)) = (f a : E)
      rw [← hS a ha]
      rw [← add_smul]
      simp
    rw [hc, UnitSphere.norm_coe (f a)]
    simp

/-- Two sphere-valued maps that are pointwise at distance `< 2` are homotopic rel any
set on which they agree.-/
theorem homotopicRel_of_dist_lt_two (f g : C(A, UnitSphere E))
    (h : ∀ a, dist (f a) (g a) < 2) (S : Set A) (hS : ∀ a ∈ S, f a = g a) :
    f.HomotopicRel g S :=
  ⟨chordHomotopyRel f g h S hS⟩

end Chord

/-- Generalized loops in the unit sphere that are pointwise at distance `< 2` are
homotopic rel the cube boundary.-/
theorem genLoop_homotopic_of_dist_lt_two {N : Type*} {x : UnitSphere E}
    (p q : Ω^ N (UnitSphere E) x) (h : ∀ t, dist (p t) (q t) < 2) :
    GenLoop.Homotopic p q :=
  homotopicRel_of_dist_lt_two p.1 q.1 h (Cube.boundary N) fun t ht =>
    (p.2 t ht).trans (q.2 t ht).symm

section Normalize

variable {A : Type*} [TopologicalSpace A]

/-- Pointwise normalization of a nonvanishing map into `E`, as a map into the unit
sphere.-/
def normalizeMap (g : C(A, E)) (hg : ∀ a, g a ≠ 0) : C(A, UnitSphere E) where
  toFun a := ⟨‖g a‖⁻¹ • g a, mem_sphere_zero_iff_norm.mpr (norm_normalize (hg a))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (((map_continuous g).norm).inv₀ fun a =>
      norm_ne_zero_iff.mpr (hg a)).smul (map_continuous g)

@[simp]
theorem normalizeMap_coe (g : C(A, E)) (hg : ∀ a, g a ≠ 0) (a : A) :
    (normalizeMap g hg a : E) = ‖g a‖⁻¹ • g a :=
  rfl

/-- If a map into `E` is pointwise within distance `1` of a sphere-valued map, it does
not vanish.-/
theorem ne_zero_of_dist_lt_one {f : C(A, UnitSphere E)} {g : C(A, E)}
    (h : ∀ a, dist ((f a : E)) (g a) < 1) (a : A) : g a ≠ 0 := by
  intro hc
  have := h a
  rw [hc, dist_zero_right, UnitSphere.norm_coe (f a)] at this
  exact lt_irrefl 1 this

/-- If `g` is pointwise within distance `1` of the sphere-valued `f`, then `f` pairs
positively with `g`.-/
theorem inner_pos_of_dist_lt_one {f : C(A, UnitSphere E)} {g : C(A, E)}
    (h : ∀ a, dist ((f a : E)) (g a) < 1) (a : A) : 0 < ⟪(f a : E), g a⟫ := by
  have hf : ‖(f a : E)‖ = 1 := UnitSphere.norm_coe (f a)
  have h1 : ⟪(f a : E), (f a : E) - g a⟫ ≤ ‖(f a : E)‖ * ‖(f a : E) - g a‖ :=
    real_inner_le_norm _ _
  have h2 : ‖(f a : E) - g a‖ < 1 := by
    rw [← dist_eq_norm]; exact h a
  have h3 : ⟪(f a : E), (f a : E) - g a⟫
      = ⟪(f a : E), (f a : E)⟫ - ⟪(f a : E), g a⟫ := inner_sub_right _ _ _
  have h4 : ⟪(f a : E), (f a : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hf]; norm_num
  rw [hf, one_mul] at h1
  linarith

/-- A sphere-valued map `f` is homotopic, rel a set `S` on which `g` agrees with `f`,
to the normalization of any map `g` into `E` that stays pointwise within distance `1`
of `f`.-/
theorem normalizedRawHomotopyRel (f : C(A, UnitSphere E)) (g : C(A, E))
    (h : ∀ a, dist ((f a : E)) (g a) < 1) (S : Set A)
    (hS : ∀ a ∈ S, g a = (f a : E)) :
    f.HomotopicRel (normalizeMap g (ne_zero_of_dist_lt_one h)) S := by
  refine homotopicRel_of_dist_lt_two f _ (fun a => ?_) S (fun a ha => ?_)
  · refine dist_lt_two_of_ne_neg _ _ fun hc => ?_
    have hpos : 0 < ⟪(f a : E), g a⟫ := inner_pos_of_dist_lt_one h a
    have hcoe : (f a : E) = -(‖g a‖⁻¹ • g a) := by
      rw [hc, coe_neg_sphere]; rfl
    have hneg : ⟪(f a : E), g a⟫ = -(‖g a‖⁻¹ * ⟪g a, g a⟫) := by
      rw [hcoe, inner_neg_left, real_inner_smul_left]
    have hg0 : (0 : ℝ) < ‖g a‖ :=
      norm_pos_iff.mpr (ne_zero_of_dist_lt_one h a)
    have hgg : ⟪g a, g a⟫ = ‖g a‖ ^ 2 := real_inner_self_eq_norm_sq _
    rw [hneg, hgg] at hpos
    have hmul : 0 < ‖g a‖⁻¹ * ‖g a‖ ^ 2 := mul_pos (inv_pos.mpr hg0) (pow_pos hg0 2)
    linarith
  · apply Subtype.ext
    rw [normalizeMap_coe, hS a ha, UnitSphere.norm_coe (f a)]
    simp

end Normalize

end Submission
