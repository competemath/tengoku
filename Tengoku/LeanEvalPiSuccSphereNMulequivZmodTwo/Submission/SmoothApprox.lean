import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.Collar
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth approximation of generalized loops in the unit sphere

Every generalized loop `p : Ω^ N (UnitSphere E) x` is homotopic rel boundary to the
pointwise normalization of a `C^∞` map `raw : (N → ℝ) → E` which is exactly the
basepoint near the (clamped) boundary.

The construction: extend the collared loop `Submission.collared p` to all of `ℝ^N`
by clamping coordinates to the cube (`cubeClamp`); the extension `extended p` is
constant (equal to the basepoint) on the open set `ambientCollar N`, hence `C^∞`
there; Mathlib's `Continuous.exists_contDiff_approx_and_eqOn` produces a globally
`C^∞` map `raw` that is `1/8`-close to `extended p` and agrees with it on the closed
set `closedAmbientCollar N`.  Since `extended p` takes values in the unit sphere,
`raw` never vanishes, and its normalization is a generalized loop homotopic to `p`
via `Submission.normalizedRawHomotopyRel`.

Main declarations:

* `Submission.cubeClamp`, `Submission.extended`;
* `Submission.ambientCollar`, `Submission.closedAmbientCollar`;
* `Submission.Approximation`: the bundled data of a smooth approximation;
* `Submission.exists_approximation`;
* `Submission.exists_approximation_of_homotopy_class`.
-/

noncomputable section

open scoped Topology unitInterval ContDiff
open Topology.Homotopy Set Function Metric

namespace Submission

variable {N : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {x : UnitSphere E}

/-! ### Clamping `ℝ^N` onto the cube -/

/-- Coordinatewise clamp of `ℝ^N` onto the unit cube.-/
def cubeClamp (v : N → ℝ) : I^N := fun i => Set.projIcc (0 : ℝ) 1 zero_le_one (v i)

theorem continuous_cubeClamp : Continuous (cubeClamp (N := N)) :=
  continuous_pi fun i => continuous_projIcc.comp (continuous_apply i)

@[simp]
theorem cubeClamp_coords (t : I^N) : cubeClamp (fun i => (t i : ℝ)) = t :=
  funext fun i => Set.projIcc_val zero_le_one (t i)

theorem cubeClamp_coe_le {v : N → ℝ} {i : N} (h : v i ≤ 1 / 4) :
    ((cubeClamp v i : ℝ)) ≤ 1 / 4 := by
  rw [cubeClamp, Set.coe_projIcc]
  exact max_le (by norm_num) ((min_le_right _ _).trans h)

theorem le_cubeClamp_coe {v : N → ℝ} {i : N} (h : 3 / 4 ≤ v i) :
    (3 / 4 : ℝ) ≤ (cubeClamp v i : ℝ) := by
  rw [cubeClamp, Set.coe_projIcc]
  exact le_trans (le_min (by norm_num) h) (le_max_right _ _)

/-! ### The ambient collar sets -/

/-- The open collar of the boundary of the cube inside `ℝ^N`: some coordinate is
strictly below `1/4` or strictly above `3/4`.-/
def ambientCollar (N : Type*) : Set (N → ℝ) :=
  {v | ∃ i, v i < 1 / 4 ∨ 3 / 4 < v i}

/-- A closed set contained in `ambientCollar` and still containing (the coordinates
of) the boundary of the cube: some coordinate is at most `1/5` or at least `4/5`.-/
def closedAmbientCollar (N : Type*) : Set (N → ℝ) :=
  {v | ∃ i, v i ≤ 1 / 5 ∨ 4 / 5 ≤ v i}

theorem isOpen_ambientCollar : IsOpen (ambientCollar N) := by
  have h : ambientCollar N
      = ⋃ i, ({v : N → ℝ | v i < 1 / 4} ∪ {v : N → ℝ | 3 / 4 < v i}) := by
    ext v
    simp only [ambientCollar, mem_ofPred_eq, mem_iUnion, mem_union]
  rw [h]
  exact isOpen_iUnion fun i =>
    (isOpen_lt (continuous_apply i) continuous_const).union
      (isOpen_lt continuous_const (continuous_apply i))

theorem isClosed_closedAmbientCollar [Finite N] : IsClosed (closedAmbientCollar N) := by
  have h : closedAmbientCollar N
      = ⋃ i, ({v : N → ℝ | v i ≤ 1 / 5} ∪ {v : N → ℝ | 4 / 5 ≤ v i}) := by
    ext v
    simp only [closedAmbientCollar, mem_ofPred_eq, mem_iUnion, mem_union]
  rw [h]
  exact isClosed_iUnion_of_finite fun i =>
    (isClosed_le (continuous_apply i) continuous_const).union
      (isClosed_le continuous_const (continuous_apply i))

theorem closedAmbientCollar_subset : closedAmbientCollar N ⊆ ambientCollar N := by
  rintro v ⟨i, hi | hi⟩
  · exact ⟨i, Or.inl (by linarith)⟩
  · exact ⟨i, Or.inr (by linarith)⟩

theorem coords_mem_closedAmbientCollar {t : I^N} (ht : t ∈ Cube.boundary N) :
    (fun i => (t i : ℝ)) ∈ closedAmbientCollar N := by
  obtain ⟨i, hi | hi⟩ := ht
  · refine ⟨i, Or.inl ?_⟩
    show (t i : ℝ) ≤ 1 / 5
    rw [hi, Set.Icc.coe_zero]
    norm_num
  · refine ⟨i, Or.inr ?_⟩
    show (4 / 5 : ℝ) ≤ (t i : ℝ)
    rw [hi, Set.Icc.coe_one]
    norm_num

/-! ### The clamped extension of a collared loop -/

/-- The extension of the collared loop `collared p` to all of `ℝ^N`, by clamping the
coordinates onto the cube and passing to the ambient space `E`.-/
def extended (p : Ω^ N (UnitSphere E) x) : (N → ℝ) → E := fun v =>
  ((collared p).1 (cubeClamp v) : E)

theorem continuous_extended (p : Ω^ N (UnitSphere E) x) : Continuous (extended p) :=
  continuous_subtype_val.comp ((map_continuous (collared p).1).comp continuous_cubeClamp)

theorem norm_extended (p : Ω^ N (UnitSphere E) x) (v : N → ℝ) :
    ‖extended p v‖ = 1 :=
  UnitSphere.norm_coe _

theorem extended_coords (p : Ω^ N (UnitSphere E) x) (t : I^N) :
    extended p (fun i => (t i : ℝ)) = ((collared p).1 t : E) := by
  show ((collared p).1 (cubeClamp fun i => (t i : ℝ)) : E) = _
  rw [cubeClamp_coords]

/-- On the ambient collar, the clamped extension is constantly the basepoint.-/
theorem extended_eq_basepoint (p : Ω^ N (UnitSphere E) x) {v : N → ℝ}
    (hv : v ∈ ambientCollar N) : extended p v = (x : E) := by
  obtain ⟨i, hi | hi⟩ := hv
  · exact congrArg Subtype.val (collared_eq_basepoint p ⟨i, Or.inl (cubeClamp_coe_le hi.le)⟩)
  · exact congrArg Subtype.val (collared_eq_basepoint p ⟨i, Or.inr (le_cubeClamp_coe hi.le)⟩)

/-- The clamped extension is `C^∞` (being locally constant) on the open ambient
collar.-/
theorem contDiffOn_extended [Fintype N] (p : Ω^ N (UnitSphere E) x) :
    ContDiffOn ℝ ∞ (extended p) (ambientCollar N) :=
  contDiffOn_const.congr fun _ hv => extended_eq_basepoint p hv

/-! ### The approximation structure -/

/-- A smooth approximation of a generalized loop `p` in the unit sphere: a `C^∞` map
`raw : ℝ^N → E`, `1/8`-close to the clamped extension of the collared loop, exactly
equal to the basepoint on the closed ambient collar, together with the induced
representative (its pointwise normalization) and the homotopy `p ≃ representative`
rel the cube boundary.-/
structure Approximation [Fintype N] (p : Ω^ N (UnitSphere E) x) where
  /-- The smooth raw map `ℝ^N → E`.-/
  raw : (N → ℝ) → E
  contDiff_raw : ContDiff ℝ ∞ raw
  raw_close : ∀ v, dist (raw v) (extended p v) < 1 / 8
  raw_eq_basepoint_on_collar : ∀ v ∈ closedAmbientCollar N, raw v = (x : E)
  /-- The normalized representative, a generalized loop homotopic to `p`.-/
  representative : Ω^ N (UnitSphere E) x
  representative_coe : ∀ t : I^N,
    (representative t : E) = ‖raw (fun i => (t i : ℝ))‖⁻¹ • raw (fun i => (t i : ℝ))
  homotopic : GenLoop.Homotopic p representative

/-- The raw map of an approximation never vanishes: it is `1/8`-close to a
sphere-valued map.-/
theorem Approximation.raw_ne_zero [Fintype N] {p : Ω^ N (UnitSphere E) x} (a : Approximation p)
    (v : N → ℝ) : a.raw v ≠ 0 := by
  intro h0
  have h := a.raw_close v
  rw [h0, dist_zero_left, norm_extended] at h
  norm_num at h

/-- Existence of smooth approximations, via Mathlib's smooth approximation theorem
`Continuous.exists_contDiff_approx_and_eqOn`.-/
theorem exists_approximation [Fintype N] (p : Ω^ N (UnitSphere E) x) :
    Nonempty (Approximation p) := by
  obtain ⟨g, g_smooth, g_close, g_eq, -⟩ :=
    (continuous_extended p).exists_contDiff_approx_and_eqOn (ε := fun _ => 1 / 8) ⊤
      continuous_const (fun _ => by norm_num)
      isClosed_closedAmbientCollar
      (isOpen_ambientCollar.mem_nhdsSet.mpr closedAmbientCollar_subset)
      (contDiffOn_extended p)
  -- restriction of `g` to the cube
  let gI : C(I^N, E) :=
    ⟨fun t => g (fun i => (t i : ℝ)),
      g_smooth.continuous.comp
        (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))⟩
  have hclose1 : ∀ t : I^N, dist (((collared p).1 t : E)) (gI t) < 1 := by
    intro t
    have h8 := g_close (fun i => (t i : ℝ))
    rw [extended_coords] at h8
    have hsymm : dist (((collared p).1 t : E)) (gI t)
        = dist (gI t) (((collared p).1 t : E)) := dist_comm _ _
    rw [hsymm]
    calc dist (gI t) (((collared p).1 t : E)) < 1 / 8 := h8
    _ < 1 := by norm_num
  have hbnd : ∀ t ∈ Cube.boundary N, gI t = (x : E) := by
    intro t ht
    have h1 : gI t = extended p (fun i => (t i : ℝ)) :=
      g_eq (coords_mem_closedAmbientCollar ht)
    rw [h1, extended_coords]
    exact congrArg Subtype.val ((collared p).2 t ht)
  -- the normalized representative
  refine ⟨⟨g, g_smooth, fun v => by simpa using g_close v,
    fun v hv => (g_eq hv).trans
      (extended_eq_basepoint p (closedAmbientCollar_subset hv)),
    ⟨normalizeMap gI (ne_zero_of_dist_lt_one hclose1), fun t ht => ?_⟩,
    fun t => rfl, ?_⟩⟩
  · apply Subtype.ext
    rw [normalizeMap_coe, hbnd t ht, UnitSphere.norm_coe x, inv_one, one_smul]
  · refine (homotopic_collared p).trans ?_
    exact normalizedRawHomotopyRel (collared p).1 gI hclose1 (Cube.boundary N)
      fun t ht => by
        rw [hbnd t ht]
        exact (congrArg Subtype.val ((collared p).2 t ht)).symm

/-- Every homotopy class in the sphere is represented by the normalization of a
smooth raw map.-/
theorem exists_approximation_of_homotopy_class [Fintype N]
    (z : HomotopyGroup N (UnitSphere E) x) :
    ∃ (p : Ω^ N (UnitSphere E) x) (a : Approximation p), z = ⟦a.representative⟧ := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep z
  obtain ⟨a⟩ := exists_approximation p
  exact ⟨p, a, Quotient.sound a.homotopic⟩

end Submission
