import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.LevelSet
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.LevelOrbit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Framed level sets: the frame loop

Along a periodic flow line `γ` of a framed level set `X`, the family
`(τ(γ t), ∇g₁(γ t), …, ∇gₙ(γ t))` is a continuously varying basis of `ℝ^{n+1}`.
Applying (normalized) Gram–Schmidt row-wise produces a continuous, `T`-periodic loop

  `frameLoop X γ : ℝ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ`

with values in the special orthogonal group.

Main statements:

* `Submission.linearIndependent_frameAt` : the frame is a basis at regular points;
* `Submission.det_rowsMatrix_gramSchmidt` : Gram–Schmidt preserves the determinant
  of the row matrix (proved by row operations);
* `Submission.frameLoop_mem_specialOrthogonalGroup`;
* `Submission.continuous_frameLoop`;
* `Submission.frameLoop_periodic`;
* `Submission.TamedField.exists_frameLoop` : packaged form along the periodic flow
  through any fiber point.
-/

noncomputable section

namespace Submission

open Set Function Metric Module Submodule Finset InnerProductSpace
open scoped RealInnerProductSpace ContDiff Topology Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "F" => EuclideanSpace ℝ (Fin n)

/-! ## The frame family -/

/-- The frame at a point: the unit kernel vector followed by the component
gradients.-/
def frameAt (X : FramedLevelSet n) (x : E) : Fin (n + 1) → E :=
  Fin.cons (tauField X.g x) fun i => gradVec X.g i x

lemma tauField_inner_gradVec (g : E → F) (x : E) (i : Fin n) :
    ⟪tauField g x, gradVec g i x⟫ = 0 := by
  rw [tauField, real_inner_smul_left]
  have h : ⟪kerCross g x, gradVec g i x⟫ = 0 :=
    inner_crossVec_self (fun j => gradVec g j x) i
  rw [h, mul_zero]

/-- At a regular point the frame is linearly independent (hence a basis).-/
lemma linearIndependent_frameAt (X : FramedLevelSet n) {x : E}
    (hx : x ∈ regularSet X.g) :
    LinearIndependent ℝ (frameAt X x) := by
  rw [frameAt]
  apply linearIndependent_finCons.mpr
  refine ⟨(surjective_fderiv_iff_linearIndependent X.g x).mp hx, ?_⟩
  intro hmem
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun _).mp hmem
  have hzero : ⟪tauField X.g x, tauField X.g x⟫ = 0 := by
    nth_rewrite 2 [← hc]
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [real_inner_smul_right, tauField_inner_gradVec, mul_zero]
  have : tauField X.g x = 0 := inner_self_eq_zero.mp hzero
  have h1 : ‖tauField X.g x‖ = 1 := norm_tauField hx
  rw [this, norm_zero] at h1
  norm_num at h1

/-! ## Determinant of the row matrix under Gram–Schmidt -/

variable {m : ℕ}

/-- The matrix whose rows are the coordinates of the given family.-/
def rowsMatrix (v : Fin m → EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i => WithLp.ofLp (v i)

/-- Adding a linear combination of the other rows to a row does not change the
determinant.-/
lemma det_updateRow_add_of_mem_span (A : Matrix (Fin m) (Fin m) ℝ) (j : Fin m)
    {w : Fin m → ℝ} (hw : w ∈ Submodule.span ℝ (A '' {i | i ≠ j})) :
    (A.updateRow j (A j + w)).det = A.det := by
  classical
  set L : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => (A.updateRow j x).det
      map_add' := fun x y => Matrix.det_updateRow_add A j x y
      map_smul' := fun c x => Matrix.det_updateRow_smul A j c x } with hL
  have hL0 : ∀ u ∈ Submodule.span ℝ (A '' {i | i ≠ j}), L u = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hij, rfl⟩ := hx
      show (A.updateRow j (A i)).det = 0
      apply Matrix.det_zero_of_row_eq (i := i) (j := j) hij
      rw [Matrix.updateRow_ne hij, Matrix.updateRow_self]
    | zero => exact map_zero L
    | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul c x hx ih => rw [map_smul, ih, smul_zero]
  have hadd : L (A j + w) = L (A j) + L w := map_add L _ _
  have hself : L (A j) = A.det := by
    show (A.updateRow j (A j)).det = A.det
    rw [Matrix.updateRow_eq_self]
  calc (A.updateRow j (A j + w)).det = L (A j + w) := rfl
    _ = L (A j) + L w := hadd
    _ = A.det + 0 := by rw [hself, hL0 w hw]
    _ = A.det := add_zero _

/-- The Gram–Schmidt correction of the `i`-th vector lies in the span of the previous
Gram–Schmidt vectors.-/
lemma gramSchmidt_sub_mem_span (v : Fin m → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    gramSchmidt ℝ v i - v i ∈ Submodule.span ℝ (gramSchmidt ℝ v '' Set.Iio i) := by
  have h := gramSchmidt_def ℝ v i
  have : gramSchmidt ℝ v i - v i
      = -∑ j ∈ Finset.Iio i, (ℝ ∙ gramSchmidt ℝ v j).starProjection (v i) := by
    rw [h]
    abel
  rw [this]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro j hj
  have hjlt : j < i := Finset.mem_Iio.mp hj
  have hmem : (ℝ ∙ gramSchmidt ℝ v j).starProjection (v i) ∈ ℝ ∙ gramSchmidt ℝ v j :=
    (ℝ ∙ gramSchmidt ℝ v j).starProjection_apply_mem (v i)
  have himg : gramSchmidt ℝ v j ∈ gramSchmidt ℝ v '' Set.Iio i := ⟨j, hjlt, rfl⟩
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr himg) hmem

/-- **Gram–Schmidt preserves the determinant** of the matrix of rows.-/
lemma det_rowsMatrix_gramSchmidt (v : Fin m → EuclideanSpace ℝ (Fin m)) :
    (rowsMatrix (gramSchmidt ℝ v)).det = (rowsMatrix v).det := by
  classical
  -- interpolating matrices: first `k` rows original, remaining rows Gram–Schmidt
  set Mix : ℕ → Matrix (Fin m) (Fin m) ℝ := fun k =>
    Matrix.of fun i => if (i : ℕ) < k then WithLp.ofLp (v i)
      else WithLp.ofLp (gramSchmidt ℝ v i) with hMix
  have hstep : ∀ k, (Mix (k + 1)).det = (Mix k).det := by
    intro k
    by_cases hk : k < m
    · set i₀ : Fin m := ⟨k, hk⟩ with hi₀
      -- `Mix k` is `Mix (k+1)` with row `i₀` replaced by the Gram–Schmidt vector
      have hupdate : Mix k = (Mix (k + 1)).updateRow i₀
          (WithLp.ofLp (gramSchmidt ℝ v i₀)) := by
        ext i j
        by_cases hii : i = i₀
        · subst hii
          rw [Matrix.updateRow_self]
          simp [hMix, hi₀]
        · rw [Matrix.updateRow_ne hii]
          have hiff : (i : ℕ) < k ↔ (i : ℕ) < k + 1 := by
            constructor
            · omega
            · intro h
              rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
              · exact h'
              · exact absurd (Fin.ext h' : i = i₀) hii
          simp only [hMix, Matrix.of_apply]
          by_cases hlt : (i : ℕ) < k
          · rw [ite_eq_left hlt, ite_eq_left (hiff.mp hlt)]
          · rw [ite_eq_right hlt, ite_eq_right (fun h => hlt (hiff.mpr h))]
      have hrow : (Mix (k + 1)) i₀ = WithLp.ofLp (v i₀) := by
        have hlt : (i₀ : ℕ) < k + 1 := by rw [hi₀]; exact Nat.lt_succ_self k
        show (if (i₀ : ℕ) < k + 1 then WithLp.ofLp (v i₀)
          else WithLp.ofLp (gramSchmidt ℝ v i₀)) = WithLp.ofLp (v i₀)
        rw [ite_eq_left hlt]
      -- the correction lies in the span of the other rows of `Mix (k+1)`
      have hw : WithLp.ofLp (gramSchmidt ℝ v i₀) - WithLp.ofLp (v i₀)
          ∈ Submodule.span ℝ ((Mix (k + 1)) '' {i | i ≠ i₀}) := by
        have h1 : gramSchmidt ℝ v i₀ - v i₀
            ∈ Submodule.span ℝ (v '' Set.Iio i₀) := by
          rw [← span_gramSchmidt_Iio ℝ v i₀]
          exact gramSchmidt_sub_mem_span v i₀
        have h2 : (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap
              (gramSchmidt ℝ v i₀ - v i₀)
            ∈ Submodule.map (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap
              (Submodule.span ℝ (v '' Set.Iio i₀)) :=
          Submodule.mem_map_of_mem h1
        rw [Submodule.map_span] at h2
        have h3 : (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap '' (v '' Set.Iio i₀)
            ⊆ (Mix (k + 1)) '' {i | i ≠ i₀} := by
          rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
          have hjlt : j < i₀ := hj
          have hjk : (j : ℕ) < k := hjlt
          refine ⟨j, fun h => absurd (h ▸ hjlt) (lt_irrefl i₀), ?_⟩
          have hlt : (j : ℕ) < k + 1 := by omega
          show (if (j : ℕ) < k + 1 then WithLp.ofLp (v j)
            else WithLp.ofLp (gramSchmidt ℝ v j)) = _
          rw [ite_eq_left hlt]
          rfl
        exact Submodule.span_mono h3 h2
      have hw' : WithLp.ofLp (gramSchmidt ℝ v i₀)
          = (Mix (k + 1)) i₀
            + (WithLp.ofLp (gramSchmidt ℝ v i₀) - WithLp.ofLp (v i₀)) := by
        rw [hrow]
        abel
      rw [hupdate, hw']
      exact (det_updateRow_add_of_mem_span (Mix (k + 1)) i₀ hw).symm
    · -- for `k ≥ m` the two matrices coincide
      have : Mix (k + 1) = Mix k := by
        ext i j
        have h1 : (i : ℕ) < k + 1 := by omega
        have h2 : (i : ℕ) < k := by omega
        simp [hMix, h1, h2]
      rw [this]
  have hall : ∀ k, (Mix k).det = (Mix 0).det := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [hstep k, ih]
  have hm : Mix m = rowsMatrix v := by
    ext i j
    simp [hMix, rowsMatrix, i.isLt]
  have h0 : Mix 0 = rowsMatrix (gramSchmidt ℝ v) := by
    ext i j
    simp [hMix, rowsMatrix]
  rw [← hm, hall m, h0]

/-- Determinant of the normalized Gram–Schmidt row matrix.-/
lemma det_rowsMatrix_gramSchmidtNormed (v : Fin m → EuclideanSpace ℝ (Fin m)) :
    (rowsMatrix (gramSchmidtNormed ℝ v)).det
      = (∏ i, ‖gramSchmidt ℝ v i‖⁻¹) * (rowsMatrix v).det := by
  have h : rowsMatrix (gramSchmidtNormed ℝ v)
      = Matrix.of fun i j => ‖gramSchmidt ℝ v i‖⁻¹ * rowsMatrix (gramSchmidt ℝ v) i j := by
    ext i j
    show WithLp.ofLp (gramSchmidtNormed ℝ v i) j
      = ‖gramSchmidt ℝ v i‖⁻¹ * WithLp.ofLp (gramSchmidt ℝ v i) j
    rw [gramSchmidtNormed]
    rfl
  calc (rowsMatrix (gramSchmidtNormed ℝ v)).det
      = (Matrix.of fun i j =>
          ‖gramSchmidt ℝ v i‖⁻¹ * rowsMatrix (gramSchmidt ℝ v) i j).det := by rw [h]
    _ = (∏ i, ‖gramSchmidt ℝ v i‖⁻¹) * (rowsMatrix (gramSchmidt ℝ v)).det :=
        Matrix.det_mul_column _ _
    _ = (∏ i, ‖gramSchmidt ℝ v i‖⁻¹) * (rowsMatrix v).det := by
        rw [det_rowsMatrix_gramSchmidt]

/-- The row matrix of the frame is the `crossRows` matrix of the gradients and `τ`.-/
lemma rowsMatrix_frameAt (X : FramedLevelSet n) (x : E) :
    rowsMatrix (frameAt X x)
      = crossRows (fun i => gradVec X.g i x) (tauField X.g x) := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;>
    simp [rowsMatrix, frameAt, crossRows]

lemma det_rowsMatrix_frameAt_pos (X : FramedLevelSet n) {x : E}
    (hx : x ∈ regularSet X.g) :
    0 < (rowsMatrix (frameAt X x)).det := by
  rw [rowsMatrix_frameAt]
  exact crossDet_tauField_pos hx

/-! ## Continuity of Gram–Schmidt along a continuous family -/

/-- Gram–Schmidt is continuous along a pointwise linearly independent continuous
family of frames.-/
lemma continuous_gramSchmidt_family {T : Type*} [TopologicalSpace T]
    {A : T → Fin m → EuclideanSpace ℝ (Fin m)}
    (hA : ∀ i, Continuous fun t => A t i)
    (hInd : ∀ t, LinearIndependent ℝ (A t)) (i : Fin m) :
    Continuous fun t => gramSchmidt ℝ (A t) i := by
  have key : ∀ N : ℕ, ∀ i : Fin m, (i : ℕ) = N →
      Continuous fun t => gramSchmidt ℝ (A t) i := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro i hi
      have hrw : (fun t => gramSchmidt ℝ (A t) i) = fun t => A t i -
          ∑ j ∈ Finset.Iio i,
            (⟪gramSchmidt ℝ (A t) j, A t i⟫ / ((‖gramSchmidt ℝ (A t) j‖ : ℝ) ^ 2)) •
              gramSchmidt ℝ (A t) j := by
        funext t
        rw [gramSchmidt_def]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [starProjection_singleton]
        norm_num
      rw [hrw]
      apply (hA i).sub
      apply continuous_finsetSum
      intro j hj
      have hjN : (j : ℕ) < N := by
        have h1 : j < i := Finset.mem_Iio.mp hj
        have h2 : (j : ℕ) < (i : ℕ) := h1
        omega
      have hcj : Continuous fun t => gramSchmidt ℝ (A t) j := IH (j : ℕ) hjN j rfl
      have hdiv : Continuous fun t =>
          ⟪gramSchmidt ℝ (A t) j, A t i⟫ / ‖gramSchmidt ℝ (A t) j‖ ^ 2 := by
        apply Continuous.div
        · exact hcj.inner (hA i)
        · exact (hcj.norm).pow 2
        · intro t
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j (hInd t)))
      exact hdiv.smul hcj
  exact key (i : ℕ) i rfl

/-- Normalized Gram–Schmidt is continuous along a pointwise independent continuous
family of frames.-/
lemma continuous_gramSchmidtNormed_family {T : Type*} [TopologicalSpace T]
    {A : T → Fin m → EuclideanSpace ℝ (Fin m)}
    (hA : ∀ i, Continuous fun t => A t i)
    (hInd : ∀ t, LinearIndependent ℝ (A t)) (i : Fin m) :
    Continuous fun t => gramSchmidtNormed ℝ (A t) i := by
  have hgs := continuous_gramSchmidt_family hA hInd i
  have hnorm : Continuous fun t => ‖gramSchmidt ℝ (A t) i‖⁻¹ :=
    (hgs.norm).inv₀ fun t =>
      norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i (hInd t))
  have heq : (fun t => gramSchmidtNormed ℝ (A t) i)
      = fun t => ‖gramSchmidt ℝ (A t) i‖⁻¹ • gramSchmidt ℝ (A t) i := by
    funext t
    rw [gramSchmidtNormed]
    norm_num
  rw [heq]
  exact hnorm.smul hgs

/-! ## The frame loop -/

/-- The frame loop along a curve: the row matrix of the orthonormalized frame.-/
def frameLoop (X : FramedLevelSet n) (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) :
    ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun t => rowsMatrix (gramSchmidtNormed ℝ (frameAt X (γ t)))

/-- Continuity of the frame family along a continuous curve in the regular set.-/
lemma continuous_frameAt_comp (X : FramedLevelSet n)
    {T : Type*} [TopologicalSpace T]
    {γ : T → EuclideanSpace ℝ (Fin (n + 1))} (hγc : Continuous γ)
    (hγ : ∀ t, γ t ∈ regularSet X.g) (i : Fin (n + 1)) :
    Continuous fun t => frameAt X (γ t) i := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
  · have heq : (fun t => frameAt X (γ t) 0) = fun t => tauField X.g (γ t) := by
      funext t; simp [frameAt]
    rw [heq]
    exact (contDiffOn_tauField X.smooth).continuousOn.comp_continuous hγc hγ
  · have heq : (fun t => frameAt X (γ t) k.succ) = fun t => gradVec X.g k (γ t) := by
      funext t; simp [frameAt]
    rw [heq]
    exact (contDiff_gradVec X.g X.smooth k).continuous.comp hγc

theorem continuous_frameLoop (X : FramedLevelSet n)
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} (hγc : Continuous γ)
    (hγ : ∀ t, γ t ∈ X.fiber) :
    Continuous (frameLoop X γ) := by
  have hreg : ∀ t, γ t ∈ regularSet X.g := fun t => X.fiber_subset_regularSet (hγ t)
  have hInd : ∀ t, LinearIndependent ℝ (frameAt X (γ t)) := fun t =>
    linearIndependent_frameAt X (hreg t)
  apply continuous_matrix
  intro i j
  have h := continuous_gramSchmidtNormed_family
    (A := fun t => frameAt X (γ t)) (continuous_frameAt_comp X hγc hreg) hInd i
  exact (EuclideanSpace.proj j).continuous.comp h

/-- The orthonormalized frame matrix varies continuously along a continuous
family of regular points, with an arbitrary topological parameter space.-/
theorem continuous_frameMatrix_comp (X : FramedLevelSet n)
    {T : Type*} [TopologicalSpace T]
    {γ : T → EuclideanSpace ℝ (Fin (n + 1))} (hγc : Continuous γ)
    (hγ : ∀ t, γ t ∈ regularSet X.g) :
    Continuous fun t =>
      rowsMatrix (gramSchmidtNormed ℝ (frameAt X (γ t))) := by
  have hInd : ∀ t, LinearIndependent ℝ (frameAt X (γ t)) := fun t =>
    linearIndependent_frameAt X (hγ t)
  apply continuous_matrix
  intro i j
  have h := continuous_gramSchmidtNormed_family
    (A := fun t => frameAt X (γ t)) (continuous_frameAt_comp X hγc hγ) hInd i
  exact (EuclideanSpace.proj j).continuous.comp h

theorem frameLoop_periodic (X : FramedLevelSet n)
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {T : ℝ}
    (h : Function.Periodic γ T) :
    Function.Periodic (frameLoop X γ) T := by
  intro t
  unfold frameLoop
  rw [h t]

/-- The frame loop takes values in the special orthogonal group.-/
theorem frameLoop_mem_specialOrthogonalGroup (X : FramedLevelSet n)
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} (hγ : ∀ t, γ t ∈ X.fiber) (t : ℝ) :
    frameLoop X γ t ∈ Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ := by
  have hreg : γ t ∈ regularSet X.g := X.fiber_subset_regularSet (hγ t)
  have hInd : LinearIndependent ℝ (frameAt X (γ t)) :=
    linearIndependent_frameAt X hreg
  have horthonormal : Orthonormal ℝ (gramSchmidtNormed ℝ (frameAt X (γ t))) :=
    gramSchmidtNormed_orthonormal hInd
  set A := frameLoop X γ t with hA
  -- orthogonality: the rows are orthonormal
  have hmul : A * Aᵀ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hentries : ∀ k, A i k * Aᵀ k j
        = (gramSchmidtNormed ℝ (frameAt X (γ t)) i) k
          * (gramSchmidtNormed ℝ (frameAt X (γ t)) j) k := by
      intro k
      rw [Matrix.transpose_apply]
      rfl
    rw [Finset.sum_congr rfl fun k _ => hentries k]
    have hinner := orthonormal_iff_ite.mp horthonormal i j
    rw [PiLp.inner_apply] at hinner
    simp only [RCLike.inner_apply, conj_trivial] at hinner
    rw [← hinner]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have horth : A ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
    (Matrix.mem_orthogonalGroup_iff (Fin (n + 1)) ℝ).mpr hmul
  -- positive determinant via the orientation of `τ`
  have hdetpos : 0 < A.det := by
    rw [hA, frameLoop, det_rowsMatrix_gramSchmidtNormed]
    apply mul_pos
    · apply Finset.prod_pos
      intro i _
      have hne : gramSchmidt ℝ (frameAt X (γ t)) i ≠ 0 := gramSchmidt_ne_zero i hInd
      have : 0 < ‖gramSchmidt ℝ (frameAt X (γ t)) i‖ := norm_pos_iff.mpr hne
      positivity
    · exact det_rowsMatrix_frameAt_pos X hreg
  have hdetsq : A.det * A.det = 1 := by
    have h1 := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    exact h1
  have hdet1 : A.det = 1 := by
    rcases mul_self_eq_one_iff.mp hdetsq with h | h
    · exact h
    · rw [h] at hdetpos; linarith
  exact Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨horth, hdet1⟩

/-- The orthonormalized frame at any regular point lies in the special
orthogonal group.  Fiber membership is not needed for this pointwise form.-/
theorem frameMatrix_mem_specialOrthogonalGroup_of_regular (X : FramedLevelSet n)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hreg : x ∈ regularSet X.g) :
    rowsMatrix (gramSchmidtNormed ℝ (frameAt X x)) ∈
      Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ := by
  have hInd : LinearIndependent ℝ (frameAt X x) :=
    linearIndependent_frameAt X hreg
  have horthonormal : Orthonormal ℝ (gramSchmidtNormed ℝ (frameAt X x)) :=
    gramSchmidtNormed_orthonormal hInd
  set A := rowsMatrix (gramSchmidtNormed ℝ (frameAt X x)) with hA
  have hmul : A * Aᵀ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hentries : ∀ k, A i k * Aᵀ k j
        = (gramSchmidtNormed ℝ (frameAt X x) i) k
          * (gramSchmidtNormed ℝ (frameAt X x) j) k := by
      intro k
      rw [Matrix.transpose_apply]
      rfl
    rw [Finset.sum_congr rfl fun k _ => hentries k]
    have hinner := orthonormal_iff_ite.mp horthonormal i j
    rw [PiLp.inner_apply] at hinner
    simp only [RCLike.inner_apply, conj_trivial] at hinner
    rw [← hinner]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have horth : A ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
    (Matrix.mem_orthogonalGroup_iff (Fin (n + 1)) ℝ).mpr hmul
  have hdetpos : 0 < A.det := by
    rw [hA, det_rowsMatrix_gramSchmidtNormed]
    apply mul_pos
    · apply Finset.prod_pos
      intro i _
      have hne : gramSchmidt ℝ (frameAt X x) i ≠ 0 := gramSchmidt_ne_zero i hInd
      have : 0 < ‖gramSchmidt ℝ (frameAt X x) i‖ := norm_pos_iff.mpr hne
      positivity
    · exact det_rowsMatrix_frameAt_pos X hreg
  have hdetsq : A.det * A.det = 1 := by
    have h1 := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    exact h1
  have hdet1 : A.det = 1 := by
    rcases mul_self_eq_one_iff.mp hdetsq with h | h
    · exact h
    · rw [h] at hdetpos
      linarith
  exact Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨horth, hdet1⟩

/-! ## Packaged form: the frame loop along a periodic flow line -/

end Submission
