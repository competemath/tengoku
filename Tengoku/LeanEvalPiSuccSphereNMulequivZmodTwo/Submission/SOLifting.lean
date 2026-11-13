import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SORotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parametrized path lifting for the projection `SO(n+1) → Sⁿ`

The projection `Submission.proj : SO(n+1) → Sⁿ` sends a special orthogonal matrix to its
last column.  This file proves the parametrized (compact-family) path-lifting property of
`proj`, by the "short-distance transport" method: subdivide time using uniform continuity
so that consecutive sphere points are at distance `< 1`, and compose the canonical
rotations `rotTo` of `Submission.SORotation` along the subdivision.  Because
`proj (R * A) = R •ᵥ proj A` and `rotTo x y` maps `x` exactly to `y`, the transport
lift is an exact lift (no correction terms needed).

Main declarations:

* `Submission.projVec`, `Submission.proj`, `Submission.continuous_proj`,
  `Submission.projVec_mul`, `Submission.proj_rotTo_mul`;
* `Submission.basePoint : Sⁿ` (the last basis vector, `proj 1`);
* `Submission.exists_pathFamilyLift`: for compact pseudometric `P`, a continuous
  `f : P × I → Sⁿ` and a continuous initial lift `A₀ : P → SO(n+1)` of `f (·, 0)`,
  there is a continuous `L : P × I → SO(n+1)` lifting `f`, restricting to `A₀` at
  time `0`, and constant on every slice on which `f` is constant (the degenerate
  uniqueness surrogate used for boundary preservation downstream).
-/

noncomputable section

open Matrix
open scoped unitInterval

namespace Submission

variable {n : ℕ}

/-! ## The projection to the sphere -/

/-- The last column of a special orthogonal matrix.-/
def projVec (A : SOGroup (n + 1)) : Fin (n + 1) → ℝ :=
  fun i => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i (Fin.last n)

/--
@isnad1 id=eq.0h2v.s9.9c33a55099bf from=translated src=- shape=a6d53bfd vocab=a3f03b22
-/
theorem projVec_dotProduct_self (A : SOGroup (n + 1)) : projVec A ⬝ᵥ projVec A = 1 := by
  have hO : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      * (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin (n + 1)) ℝ).mp
      ((Matrix.mem_specialOrthogonalGroup_iff.mp A.2).1)
  have hOT : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ
      * (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = 1 := mul_eq_one_comm.mp hO
  have h := congr_fun (congr_fun hOT (Fin.last n)) (Fin.last n)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  simpa [projVec, dotProduct] using h

/-- The projection `SO(n+1) → Sⁿ`, sending `A` to its last column.-/
def proj (A : SOGroup (n + 1)) : UnitSphere (EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨WithLp.toLp 2 (projVec A), by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    have h : ∀ i : Fin (n + 1),
        ‖(WithLp.toLp 2 (projVec A)).ofLp i‖ ^ 2 = projVec A i * projVec A i := by
      intro i
      rw [Real.norm_eq_abs, sq_abs, sq]
    rw [Finset.sum_congr rfl fun i _ => h i]
    have hd : ∑ i, projVec A i * projVec A i = 1 := projVec_dotProduct_self A
    rw [hd, Real.sqrt_one]⟩

/--
@isnad1 id=eq.0h2v.s9.ee9977c06d3a from=translated src=- shape=da56a644 vocab=8e85cd5b
-/
@[simp]
theorem coords_proj (A : SOGroup (n + 1)) : coords (proj A) = projVec A := rfl

/--
@isnad1 id=continuo.0h1v.s10.9cde97574d30 from=translated src=- shape=04636c9d vocab=837a493d
-/
theorem continuous_projVec : Continuous (projVec (n := n)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (Fin.last n)).comp
    ((continuous_apply i).comp continuous_subtype_val)

/--
@isnad1 id=continuo.0h1v.s10.db988cea54fd from=translated src=- shape=101c05c7 vocab=013096f8
-/
theorem continuous_proj : Continuous (proj (n := n)) := by
  apply Continuous.subtype_mk
  exact (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp continuous_projVec

/-- Left multiplication acts on the projection by matrix-vector multiplication.
@isnad1 id=eq.0h3v.s12.ddd103b06eff from=translated src=- shape=2bdfc1dd vocab=c01486c2
-/
theorem projVec_mul (R A : SOGroup (n + 1)) :
    projVec (R * A) = (R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ projVec A := by
  ext i
  exact Matrix.mul_apply

/-- The workhorse: if `proj A = x` and `x, y` are non-antipodal then
`proj (rotTo x y * A) = y`.
@isnad1 id=eq.2h4v.s11.8f0389f280a0 from=translated src=- shape=4f4f1b43 vocab=a5e04577
-/
theorem proj_rotTo_mul {x y : UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))}
    (h : -1 < coords x ⬝ᵥ coords y) {A : SOGroup (n + 1)} (hA : proj A = x) :
    proj (rotTo x y * A) = y := by
  have hv : projVec A = coords x := by rw [← hA]; rfl
  apply Subtype.ext
  show WithLp.toLp 2 (projVec (rotTo x y * A)) = (y : EuclideanSpace ℝ (Fin (n + 1)))
  rw [projVec_mul, hv, rotTo_mulVec h]
  rfl

/-- The basepoint of the sphere: the last standard basis vector, i.e. `proj 1`.-/
def basePoint : UnitSphere (EuclideanSpace ℝ (Fin (n + 1))) := proj 1

/--
@isnad1 id=eq.0h1v.s10.2a02097f0552 from=translated src=- shape=dbc2999e vocab=2e383b2a
-/
@[simp]
theorem proj_one : proj (1 : SOGroup (n + 1)) = basePoint := rfl

/-! ## Time subdivision -/

/-- `clampT N i t = min t (i / N)`: time clamped to the `i`-th subdivision point.-/
def clampT (N i : ℕ) (t : I) : I :=
  ⟨min t.1 ((i : ℝ) / N), by
    constructor
    · exact le_min t.2.1 (by positivity)
    · exact le_trans (min_le_left _ _) t.2.2⟩

/--
@isnad1 id=eq.0h2v.s5.632a94771105 from=translated src=- shape=46cfbf85 vocab=25be5baf
-/
theorem clampT_zero_idx (N : ℕ) (t : I) : clampT N 0 t = 0 := by
  apply Subtype.ext
  show min t.1 (((0 : ℕ) : ℝ) / N) = 0
  rw [Nat.cast_zero, zero_div]
  exact min_eq_right t.2.1

/--
@isnad1 id=eq.1h2v.s4.ce5b55928fa7 from=translated src=- shape=6ab8c9d0 vocab=25be5baf
-/
theorem clampT_last (N : ℕ) (hN : N ≠ 0) (t : I) : clampT N N t = t := by
  apply Subtype.ext
  show min t.1 ((N : ℝ) / N) = t.1
  rw [div_self (Nat.cast_ne_zero.mpr hN)]
  exact min_eq_left t.2.2

/--
@isnad1 id=eq.0h2v.s5.d0f4a3eaafc6 from=translated src=- shape=a9ec5fd3 vocab=25be5baf
-/
theorem clampT_of_zero (N i : ℕ) : clampT N i 0 = 0 := by
  apply Subtype.ext
  show min ((0 : I) : ℝ) ((i : ℝ) / N) = 0
  exact min_eq_left (by positivity)

/--
@isnad1 id=continuo.0h2v.s5.e8443a3e70fa from=translated src=- shape=3e3b6106 vocab=7334b027
-/
theorem continuous_clampT (N i : ℕ) : Continuous (clampT N i) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.min continuous_const

/--
@isnad1 id=le.0h3v.s6.9709de72ee1f from=translated src=- shape=fb3462c7 vocab=a1559dcc
-/
theorem dist_clampT_succ (N i : ℕ) (t : I) :
    dist (clampT N i t) (clampT N (i + 1) t) ≤ 1 / N := by
  rw [Subtype.dist_eq]
  show |min t.1 ((i : ℝ) / N) - min t.1 (((i + 1 : ℕ) : ℝ) / N)| ≤ 1 / N
  have hcast : (((i + 1 : ℕ)) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hbc : (i : ℝ) / N ≤ ((i : ℝ) + 1) / N := by gcongr; linarith
  have h1 : min t.1 ((i : ℝ) / N) ≤ min t.1 (((i : ℝ) + 1) / N) := min_le_min le_rfl hbc
  have h2 : min t.1 (((i : ℝ) + 1) / N) ≤ min t.1 ((i : ℝ) / N) + 1 / N := by
    rcases le_total t.1 ((i : ℝ) / N) with h | h
    · rw [min_eq_left h]
      calc min t.1 (((i : ℝ) + 1) / N) ≤ t.1 := min_le_left _ _
        _ ≤ t.1 + 1 / N := le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right h]
      calc min t.1 (((i : ℝ) + 1) / N) ≤ ((i : ℝ) + 1) / N := min_le_right _ _
        _ = (i : ℝ) / N + 1 / N := by ring
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith

/-! ## The transport lift -/

section Lift

variable {P : Type*} [PseudoMetricSpace P] [CompactSpace P]

/-- Composition of one-step canonical transports along the time subdivision.-/
def liftSeq (f : P × I → UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (A₀ : P → SOGroup (n + 1)) (N : ℕ) : ℕ → P × I → SOGroup (n + 1)
  | 0 => fun q => A₀ q.1
  | (i + 1) => fun q =>
      rotTo (f (q.1, clampT N i q.2)) (f (q.1, clampT N (i + 1) q.2)) * liftSeq f A₀ N i q

variable {f : P × I → UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))}
  {A₀ : P → SOGroup (n + 1)} {N : ℕ}

/-- The fineness hypothesis: on time steps of length `≤ 1/N`, `f` moves by less
than `1` on the sphere.-/
def Fine (f : P × I → UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (N : ℕ) : Prop :=
  ∀ (p : P) (s t : I), dist s t ≤ 1 / N → dist (f (p, s)) (f (p, t)) < 1

omit [PseudoMetricSpace P] [CompactSpace P] in
/--
@isnad1 id=lt.1h6v.s8.4a86b1c4476e from=translated src=- shape=339d8c1e vocab=4d9a58ae
-/
theorem Fine.dom (hfine : Fine f N) (i : ℕ) (q : P × I) :
    -1 < coords (f (q.1, clampT N i q.2)) ⬝ᵥ coords (f (q.1, clampT N (i + 1) q.2)) :=
  neg_one_lt_coords_dot_of_dist_lt_two
    (lt_trans (hfine q.1 _ _ (dist_clampT_succ N i q.2)) one_lt_two)

omit [CompactSpace P] in
/--
@isnad1 id=continuo.3h6v.s11.b5d010f9f3c6 from=translated src=- shape=d5777a27 vocab=bb52bb83
-/
theorem continuous_liftSeq (hf : Continuous f) (hA₀ : Continuous A₀)
    (hfine : Fine f N) : ∀ i, Continuous (liftSeq f A₀ N i) := by
  intro i
  induction i with
  | zero => exact hA₀.comp continuous_fst
  | succ i ih =>
    exact Continuous.mul
      (continuous_rotTo
        (hf.comp (continuous_fst.prodMk ((continuous_clampT N i).comp continuous_snd)))
        (hf.comp (continuous_fst.prodMk ((continuous_clampT N (i + 1)).comp continuous_snd)))
        (hfine.dom i))
      ih

omit [PseudoMetricSpace P] [CompactSpace P] in
/--
@isnad1 id=eq.2h7v.s10.60044414f472 from=translated src=- shape=0de4437c vocab=fccebd40
-/
theorem liftSeq_proj (h₀ : ∀ p, proj (A₀ p) = f (p, 0))
    (hfine : Fine f N) : ∀ i (q : P × I),
      proj (liftSeq f A₀ N i q) = f (q.1, clampT N i q.2) := by
  intro i
  induction i with
  | zero =>
    intro q
    show proj (A₀ q.1) = _
    rw [clampT_zero_idx, h₀]
  | succ i ih =>
    intro q
    exact proj_rotTo_mul (hfine.dom i q) (ih q)

omit [PseudoMetricSpace P] [CompactSpace P] in
/--
@isnad1 id=eq.0h7v.s10.5700954c64ca from=translated src=- shape=9700e1ad vocab=04bf18e6
-/
theorem liftSeq_apply_zero : ∀ i (p : P), liftSeq f A₀ N i (p, 0) = A₀ p := by
  intro i
  induction i with
  | zero => intro p; rfl
  | succ i ih =>
    intro p
    show rotTo (f (p, clampT N i 0)) (f (p, clampT N (i + 1) 0)) * liftSeq f A₀ N i (p, 0)
      = A₀ p
    rw [clampT_of_zero, clampT_of_zero, rotTo_self, one_mul, ih]

omit [PseudoMetricSpace P] [CompactSpace P] in
/--
@isnad1 id=eq.1h8v.s10.95caf46a5060 from=translated src=- shape=d2837ed5 vocab=04bf18e6
-/
theorem liftSeq_apply_const {p : P} (hp : ∀ t, f (p, t) = f (p, 0)) :
    ∀ i t, liftSeq f A₀ N i (p, t) = A₀ p := by
  intro i
  induction i with
  | zero => intro t; rfl
  | succ i ih =>
    intro t
    show rotTo (f (p, clampT N i t)) (f (p, clampT N (i + 1) t)) * liftSeq f A₀ N i (p, t)
      = A₀ p
    rw [hp (clampT N i t), hp (clampT N (i + 1) t), rotTo_self, one_mul, ih]

/-- **Parametrized path lifting** for `proj : SO(n+1) → Sⁿ`.  Given a compact family of
paths `f : P × I → Sⁿ` and a continuous lift `A₀` of the initial slice, there is a
continuous lift `L` of `f` extending `A₀`, which is constant on slices where `f` is.
@isnad1 id=ex.3h4v.s12.f4da96cf58c5 from=translated src=- shape=84e61855 vocab=19ce498c
-/
theorem exists_pathFamilyLift
    {f : P × I → UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))} (hf : Continuous f)
    {A₀ : P → SOGroup (n + 1)} (hA₀ : Continuous A₀)
    (h₀ : ∀ p, proj (A₀ p) = f (p, 0)) :
    ∃ L : P × I → SOGroup (n + 1),
      Continuous L ∧ (∀ q, proj (L q) = f q) ∧ (∀ p, L (p, 0) = A₀ p) ∧
        ∀ p, (∀ t, f (p, t) = f (p, 0)) → ∀ t, L (p, t) = A₀ p := by
  have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hH⟩ := Metric.uniformContinuous_iff.mp huc 1 one_pos
  obtain ⟨N, hNgt⟩ := exists_nat_gt (1 / δ)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hNgt
  have hNpos : 0 < N := by exact_mod_cast hN0
  have hN : N ≠ 0 := hNpos.ne'
  have hstep : (1 : ℝ) / N < δ := by
    rw [div_lt_iff₀ hN0]
    have h1 : 1 < N * δ := by
      have := (div_lt_iff₀ hδ).mp hNgt
      linarith
    linarith [h1]
  have hfine : Fine f N := by
    intro p s t hst
    apply hH
    rw [Prod.dist_eq]
    have hps : dist p p = 0 := dist_self p
    rw [hps, max_eq_right dist_nonneg]
    exact lt_of_le_of_lt hst hstep
  refine ⟨liftSeq f A₀ N N, continuous_liftSeq hf hA₀ hfine N, ?_, liftSeq_apply_zero N,
    fun p hp t => liftSeq_apply_const hp N t⟩
  intro q
  rw [liftSeq_proj h₀ hfine N q, clampT_last N hN]

end Lift

end Submission
