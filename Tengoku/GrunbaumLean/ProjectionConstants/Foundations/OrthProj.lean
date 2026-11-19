/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Authors: Giuliano Basso, Claude
-/
import Tengoku.GrunbaumLean.ProjectionConstants.Foundations.Linfty
import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.Topology.Instances.Matrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Orthogonal projection matrices

An **orthogonal projection matrix** is a matrix `P ∈ 𝕜^{ι×ι}` with `Pᴴ = P` and `P² = P`.
We write `orthProjs 𝕜 ι m` for the set of those of rank (equivalently, trace) `m`.

Main results:

* `IsOrthProj.diag_eq`, `IsOrthProj.norm_apply_le_one`, ... : elementary entry bounds;
* `finrank_range_eq_trace` : for an idempotent matrix the rank is the trace;
* `exists_parseval_range` : every `m`-dimensional `Y ⊆ 𝕜^ι` is the range of `Uᴴ` for some
  `U ∈ 𝕜^{m×ι}` with `U Uᴴ = 1` (an orthonormal basis of `Y`);
* `exists_parseval_of_mem_orthProjs` : every `P ∈ orthProjs 𝕜 ι m` is `Uᴴ U` with `U Uᴴ = 1`, so
  the columns of `U` form a Parseval frame whose Gram matrix is `P`;
* `exists_mem_orthProjs_range` : the orthogonal projection onto a subspace;
* `isCompact_orthProjs`, `orthProjs_nonempty`.
-/

open Matrix

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- An **orthogonal projection matrix**: Hermitian and idempotent.-/
structure IsOrthProj (P : Matrix ι ι 𝕜) : Prop where
  herm : Pᴴ = P
  idem : P * P = P

variable (𝕜 ι) in
/-- The orthogonal projection matrices of rank `m` (equivalently, of trace `m`).-/
def orthProjs (m : ℕ) : Set (Matrix ι ι 𝕜) := {P | IsOrthProj P ∧ P.trace = m}

namespace IsOrthProj

variable {P : Matrix ι ι 𝕜} (hP : IsOrthProj P)
include hP

/--
@isnad1 id=eq.1h5v.s6.3826f486b956 from=translated src=- shape=c50ac618 vocab=78e5274f
-/
lemma apply_symm (i j : ι) : P j i = star (P i j) := by
  conv_lhs => rw [← hP.herm]
  rfl

/--
@isnad1 id=eq.1h5v.s5.7b4b4761ba5b from=translated src=- shape=fceaac39 vocab=3ead13a0
-/
lemma norm_apply_symm (i j : ι) : ‖P j i‖ = ‖P i j‖ := by
  rw [hP.apply_symm, norm_star]

/--
@isnad1 id=eq.1h3v.s7.d1995f00edb2 from=translated src=- shape=273f4e9d vocab=639efd77
-/
lemma conjTranspose_mul_self : Pᴴ * P = P := by rw [hP.herm, hP.idem]

/-- The diagonal entries: `Pᵢᵢ = ∑ₖ |Pₖᵢ|²`.
@isnad1 id=eq.1h4v.s6.a9d10db82a27 from=translated src=- shape=ef9101c7 vocab=7366dbf1
-/
lemma diag_eq (i : ι) : P i i = ((∑ k, ‖P k i‖ ^ 2 : ℝ) : 𝕜) := by
  conv_lhs => rw [← hP.conjTranspose_mul_self]
  simp only [mul_apply, conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  push_cast
  rfl

/--
@isnad1 id=eq.1h4v.s7.5890c05f7c64 from=translated src=- shape=adefee92 vocab=32cac033
-/
lemma re_diag (i : ι) : RCLike.re (P i i) = ∑ k, ‖P k i‖ ^ 2 := by
  rw [hP.diag_eq i, RCLike.ofReal_re]

/--
@isnad1 id=eq.1h4v.s7.b67d95d87220 from=translated src=- shape=f8af42ff vocab=0e4bb925
-/
lemma diag_eq_re (i : ι) : P i i = (RCLike.re (P i i) : 𝕜) := by
  rw [hP.re_diag, hP.diag_eq]

/--
@isnad1 id=eq.1h4v.s7.df500c23de30 from=translated src=- shape=60779deb vocab=32cac033
-/
lemma re_diag_eq_sum_row (i : ι) : RCLike.re (P i i) = ∑ k, ‖P i k‖ ^ 2 := by
  rw [hP.re_diag]
  exact Finset.sum_congr rfl fun k _ => by rw [hP.norm_apply_symm]

/--
@isnad1 id=le.1h4v.s7.25b5ef3f7732 from=translated src=- shape=3cee3fd3 vocab=d41f7da4
-/
lemma re_diag_nonneg (i : ι) : 0 ≤ RCLike.re (P i i) := by
  rw [hP.re_diag]
  exact Finset.sum_nonneg fun k _ => by positivity

/--
@isnad1 id=le.1h5v.s7.2e64fb2b3146 from=translated src=- shape=adcc47e8 vocab=739a147d
-/
lemma norm_apply_sq_le (i j : ι) : ‖P i j‖ ^ 2 ≤ RCLike.re (P j j) := by
  rw [hP.re_diag]
  exact Finset.single_le_sum (f := fun k => ‖P k j‖ ^ 2) (fun k _ => by positivity)
    (Finset.mem_univ i)

/--
@isnad1 id=eq.1h4v.s7.73bbceee4312 from=translated src=- shape=4af59dbe vocab=fe6ae430
-/
lemma norm_diag_eq (i : ι) : ‖P i i‖ = RCLike.re (P i i) := by
  rw [hP.diag_eq_re i, RCLike.norm_ofReal, abs_of_nonneg (by simpa using hP.re_diag_nonneg i)]
  simp

/--
@isnad1 id=le.1h4v.s7.c68844aaa105 from=translated src=- shape=a4ec6df7 vocab=d41f7da4
-/
lemma re_diag_le_one (i : ι) : RCLike.re (P i i) ≤ 1 := by
  have h := hP.norm_apply_sq_le i i
  rw [hP.norm_diag_eq] at h
  nlinarith [hP.re_diag_nonneg i]

/--
@isnad1 id=le.1h5v.s5.7d5d8c9304a7 from=translated src=- shape=02f7f861 vocab=f3ff20d5
-/
lemma norm_apply_le_one (i j : ι) : ‖P i j‖ ≤ 1 := by
  have h := (hP.norm_apply_sq_le i j).trans (hP.re_diag_le_one j)
  nlinarith [norm_nonneg (P i j)]

end IsOrthProj

/-! ### Rank and trace -/

section DecEq

variable [DecidableEq ι]

/-- For an idempotent matrix the rank is the trace.
@isnad1 id=eq.1h3v.s13.6200ac2fe449 from=translated src=- shape=d4055696 vocab=2539381e
-/
theorem finrank_range_eq_trace {P : Matrix ι ι 𝕜} (hP : P * P = P) :
    (Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' P)) : 𝕜) = P.trace := by
  have hid : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  rw [← Matrix.trace_toLin'_eq P,
    ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hid).trace]

/--
@isnad1 id=eq.1h4v.s13.4d61e324eee1 from=translated src=- shape=c5d9ce8d vocab=899b74d6
-/
lemma finrank_range_of_mem_orthProjs {m : ℕ} {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' P)) = m := by
  have h := finrank_range_eq_trace hP.1.idem
  rw [hP.2] at h
  exact_mod_cast h

/-- An idempotent matrix is a projection onto its range.
@isnad1 id=ismatrix.1h3v.s11.257a28cf4e6b from=translated src=- shape=3ca27990 vocab=1f9efc1f
-/
lemma isMatrixProjOnto_range {P : Matrix ι ι 𝕜} (hP : P * P = P) :
    IsMatrixProjOnto (LinearMap.range (Matrix.toLin' P)) P := by
  refine ⟨fun x => ⟨x, by simp⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  simp [Matrix.mulVec_mulVec, hP]

end DecEq

/--
@isnad1 id=eq.0h3v.s8.47d50bfeb689 from=translated src=- shape=2587f60c vocab=7be79acf
-/
lemma re_trace_eq_sum {P : Matrix ι ι 𝕜} : RCLike.re P.trace = ∑ i, RCLike.re (P i i) := by
  simp [Matrix.trace]

/--
@isnad1 id=eq.1h4v.s7.f0d3f2ce34c2 from=translated src=- shape=af97ebd2 vocab=a7fd8636
-/
lemma sum_re_diag {m : ℕ} {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    ∑ i, RCLike.re (P i i) = m := by
  rw [← re_trace_eq_sum, hP.2]
  simp

/--
@isnad1 id=le.1h4v.s5.6d476ac7030e from=translated src=- shape=725e7d40 vocab=e5c1c83c
-/
lemma le_card_of_mem_orthProjs [DecidableEq ι] {m : ℕ} {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    m ≤ Fintype.card ι := by
  rw [← finrank_range_of_mem_orthProjs hP]
  exact (Submodule.finrank_le _).trans (by simp)

/-! ### Parseval frames and orthonormal bases -/

/-- If `U Uᴴ = 1`, then `Uᴴ U` is an orthogonal projection of rank `m`.
@isnad1 id=mem.1h4v.s8.d374353e013c from=translated src=- shape=66d19832 vocab=db49322f
-/
lemma conjTranspose_mul_self_mem_orthProjs {m : ℕ} {U : Matrix (Fin m) ι 𝕜}
    (hU : U * Uᴴ = 1) : Uᴴ * U ∈ orthProjs 𝕜 ι m := by
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hU, Matrix.one_mul]
  · rw [Matrix.trace_mul_comm, hU, Matrix.trace_one]
    simp

section DecEq

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- If `U Uᴴ = 1` then `Uᴴ` is injective.
@isnad1 id=injectiv.1h4v.s11.fcecca969551 from=translated src=- shape=8808627b vocab=36b3d0ed
-/
lemma injective_toLin'_conjTranspose {m : ℕ} {U : Matrix (Fin m) ι 𝕜} (hU : U * Uᴴ = 1) :
    Function.Injective (Matrix.toLin' Uᴴ) := by
  intro x y hxy
  have := congrArg (fun z => U *ᵥ z) hxy
  simpa [Matrix.mulVec_mulVec, hU] using this

omit [DecidableEq ι] in
/--
@isnad1 id=eq.1h4v.s13.f1a71bc6fb40 from=translated src=- shape=35adc3c8 vocab=e5aa7740
-/
lemma finrank_range_toLin'_conjTranspose {m : ℕ} {U : Matrix (Fin m) ι 𝕜} (hU : U * Uᴴ = 1) :
    Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' Uᴴ)) = m := by
  rw [LinearMap.finrank_range_of_inj (injective_toLin'_conjTranspose hU)]
  simp

omit [DecidableEq ι] in
/-- Every `r`-dimensional subspace `Y ⊆ 𝕜^ι` is the range of `Uᴴ` for some `U ∈ 𝕜^{r×ι}`
with `U Uᴴ = 1`: the rows of `U` are the conjugates of an orthonormal basis of `Y`.
@isnad1 id=ex.1h4v.s11.ac8e65bc4b3e from=translated src=- shape=3e3f1349 vocab=e5aa7740
-/
theorem exists_parseval_range (Y : Submodule 𝕜 (ι → 𝕜)) {r : ℕ}
    (hr : Module.finrank 𝕜 Y = r) :
    ∃ U : Matrix (Fin r) ι 𝕜, U * Uᴴ = 1 ∧ LinearMap.range (Matrix.toLin' Uᴴ) = Y := by
  let e : EuclideanSpace 𝕜 ι ≃ₗ[𝕜] (ι → 𝕜) := WithLp.linearEquiv 2 𝕜 (ι → 𝕜)
  let Y' : Submodule 𝕜 (EuclideanSpace 𝕜 ι) := Y.map e.symm.toLinearMap
  have hr' : Module.finrank 𝕜 Y' = r := by
    rw [← hr]
    exact LinearEquiv.finrank_map_eq e.symm Y
  let b : OrthonormalBasis (Fin r) 𝕜 Y' := (stdOrthonormalBasis 𝕜 Y').reindex (finCongr hr')
  let v : Fin r → (ι → 𝕜) := fun k => e (b k : EuclideanSpace 𝕜 ι)
  have hvY : ∀ k, v k ∈ Y := by
    intro k
    have hk : (b k : EuclideanSpace 𝕜 ι) ∈ Y' := (b k).2
    rw [Submodule.mem_map_equiv] at hk
    simpa [v] using hk
  let U : Matrix (Fin r) ι 𝕜 := Matrix.of fun k i => star (v k i)
  have hU : U * Uᴴ = 1 := by
    ext k l
    have hon := orthonormal_iff_ite.1 b.orthonormal k l
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at hon
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.of_apply, star_star,
      Matrix.one_apply]
    rw [← hon]
    simp only [dotProduct, Pi.star_apply, v]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, mul_comm]
  refine ⟨U, hU, ?_⟩
  have hle : LinearMap.range (Matrix.toLin' Uᴴ) ≤ Y := by
    rintro _ ⟨z, rfl⟩
    have hz : Matrix.toLin' Uᴴ z = ∑ k, z k • v k := by
      ext i
      simp [Matrix.mulVec, dotProduct, U, Finset.sum_apply, mul_comm]
    rw [hz]
    exact Y.sum_mem fun k _ => Y.smul_mem _ (hvY k)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_range_toLin'_conjTranspose hU, hr]

/-- `Uᴴ U` and `Uᴴ` have the same range when `U Uᴴ = 1`.
@isnad1 id=eq.1h4v.s12.1991233c80e6 from=translated src=- shape=6acbbe5d vocab=37da08ec
-/
lemma range_toLin'_conjTranspose_mul_self {m : ℕ} {U : Matrix (Fin m) ι 𝕜} (hU : U * Uᴴ = 1) :
    LinearMap.range (Matrix.toLin' (Uᴴ * U)) = LinearMap.range (Matrix.toLin' Uᴴ) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨U *ᵥ z, by simp [Matrix.mulVec_mulVec]⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨Uᴴ *ᵥ z, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]

/-- The orthogonal projection onto an `m`-dimensional subspace `Y ⊆ 𝕜^ι`.
@isnad1 id=ex.1h4v.s11.94a86582ea6e from=translated src=- shape=a75eddb1 vocab=899b74d6
-/
theorem exists_mem_orthProjs_range (Y : Submodule 𝕜 (ι → 𝕜)) {m : ℕ}
    (hm : Module.finrank 𝕜 Y = m) :
    ∃ P ∈ orthProjs 𝕜 ι m, LinearMap.range (Matrix.toLin' P) = Y := by
  obtain ⟨U, hU, hrange⟩ := exists_parseval_range Y hm
  exact ⟨Uᴴ * U, conjTranspose_mul_self_mem_orthProjs hU,
    (range_toLin'_conjTranspose_mul_self hU).trans hrange⟩

/-- Every orthogonal projection of rank `m` is the Gram matrix `Uᴴ U` of a Parseval frame
`U U ᴴ = 1` in `𝕜^m`.
@isnad1 id=ex.1h4v.s8.01e6083161b3 from=translated src=- shape=a868ae6e vocab=2f108f17
-/
theorem exists_parseval_of_mem_orthProjs {m : ℕ} {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) : ∃ U : Matrix (Fin m) ι 𝕜, U * Uᴴ = 1 ∧ Uᴴ * U = P := by
  obtain ⟨U, hU, hrange⟩ := exists_parseval_range (LinearMap.range (Matrix.toLin' P))
    (finrank_range_of_mem_orthProjs hP)
  refine ⟨U, hU, ?_⟩
  -- `Uᴴ U` fixes the range of `P`, and `P` fixes the range of `Uᴴ U`.
  have h1 : Uᴴ * U * P = P := by
    refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
    have hz : P *ᵥ z ∈ LinearMap.range (Matrix.toLin' Uᴴ) := by
      rw [hrange]; exact ⟨z, by simp⟩
    obtain ⟨w, hw⟩ := hz
    simp only [Matrix.toLin'_apply] at hw ⊢
    rw [← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec, Matrix.mul_assoc, hU,
      Matrix.mul_one]
  have h2 : P * (Uᴴ * U) = Uᴴ * U := by
    refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
    have hz : (Uᴴ * U) *ᵥ z ∈ LinearMap.range (Matrix.toLin' P) := by
      rw [← hrange]; exact ⟨U *ᵥ z, by simp [Matrix.mulVec_mulVec]⟩
    obtain ⟨w, hw⟩ := hz
    simp only [Matrix.toLin'_apply] at hw ⊢
    rw [← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec, hP.1.idem]
  have h3 : P * (Uᴴ * U) = P := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hP.1.herm, Matrix.mul_assoc] using this
  rw [← h2, h3]

end DecEq

/-! ### Nonemptiness and compactness -/

/--
@isnad1 id=nonempty.1h3v.s5.5ef7df3aed2b from=translated src=- shape=64f01a2c vocab=0e036456
-/
theorem orthProjs_nonempty [DecidableEq ι] {m : ℕ} (hm : m ≤ Fintype.card ι) :
    (orthProjs 𝕜 ι m).Nonempty := by
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (by simpa)
  refine ⟨Matrix.diagonal fun i => if i ∈ s then 1 else 0, ⟨?_, ?_⟩, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all [eq_comm]
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  · simp [Matrix.trace_diagonal, Finset.sum_ite_mem, hs]

/--
@isnad1 id=iscompac.0h3v.s5.f9eae6804282 from=translated src=- shape=00e0938a vocab=f6559f06
-/
theorem isCompact_orthProjs (m : ℕ) : IsCompact (orthProjs 𝕜 ι m) := by
  let K : Set (Matrix ι ι 𝕜) :=
    Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Metric.closedBall (0 : 𝕜) 1
  have hK : IsCompact K :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {P : Matrix ι ι 𝕜 | Pᴴ = P} :=
      isClosed_eq continuous_id.matrix_conjTranspose continuous_id
    have h2 : IsClosed {P : Matrix ι ι 𝕜 | P * P = P} :=
      isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id
    have h3 : IsClosed {P : Matrix ι ι 𝕜 | P.trace = m} :=
      isClosed_eq continuous_id.matrix_trace continuous_const
    have : orthProjs 𝕜 ι m =
        ({P : Matrix ι ι 𝕜 | Pᴴ = P} ∩ {P | P * P = P}) ∩ {P | P.trace = m} := by
      ext P
      exact ⟨fun h => ⟨⟨h.1.herm, h.1.idem⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩⟩
    rw [this]
    exact (h1.inter h2).inter h3
  · intro P hP i _ j _
    exact Metric.mem_closedBall.2 (by simpa using hP.1.norm_apply_le_one i j)

/-! ### The maximal relative projection constant is finite -/

section MaxRel

/-- `λ(Y, ℓ∞^N) ≤ N`: the crude bound given by the orthogonal projection.
@isnad1 id=le.0h3v.s7.96fd557afee3 from=translated src=- shape=b83f82ff vocab=c3038bbe
-/
lemma relProjConst_le_card [DecidableEq ι] (Y : Submodule 𝕜 (ι → 𝕜)) :
    relProjConst Y ≤ Fintype.card ι := by
  obtain ⟨P, hP, hPY⟩ := exists_mem_orthProjs_range Y rfl
  have h := relProjConst_le_rowSumNorm Y (hPY ▸ isMatrixProjOnto_range hP.1.idem)
  refine h.trans (rowSumNorm_le (Nat.cast_nonneg _) fun i => ?_)
  calc ∑ j, ‖P i j‖ ≤ ∑ _j : ι, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => hP.1.norm_apply_le_one i j
    _ = Fintype.card ι := by simp

/--
@isnad1 id=bddabove.0h3v.s11.31e401f94935 from=translated src=- shape=b0e0d151 vocab=2ea20dfe
-/
lemma bddAbove_maxRelProjConst (m N : ℕ) :
    BddAbove (Set.range fun Y : {Y : Submodule 𝕜 (Fin N → 𝕜) // Module.finrank 𝕜 Y = m} =>
      relProjConst Y.1) :=
  ⟨N, by rintro _ ⟨Y, rfl⟩; simpa using relProjConst_le_card Y.1⟩

/--
@isnad1 id=le.1h4v.s9.923c7914bac4 from=translated src=- shape=434f26ef vocab=4564dec1
-/
lemma relProjConst_le_maxRelProjConst {m N : ℕ} (Y : Submodule 𝕜 (Fin N → 𝕜))
    (hY : Module.finrank 𝕜 Y = m) : relProjConst Y ≤ maxRelProjConst 𝕜 m N :=
  le_ciSup (bddAbove_maxRelProjConst m N) ⟨Y, hY⟩

/--
@isnad1 id=le.0h3v.s4.682a52b66bb0 from=translated src=- shape=bea2bd96 vocab=f4287d62
-/
lemma maxRelProjConst_nonneg (m N : ℕ) : 0 ≤ maxRelProjConst 𝕜 m N :=
  Real.iSup_nonneg fun Y => relProjConst_nonneg Y.1

end MaxRel

end ProjectionConstants
