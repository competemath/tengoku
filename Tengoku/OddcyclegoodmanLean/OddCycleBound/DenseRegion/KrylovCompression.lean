import Tengoku.Seed.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.AtomicMomentRepresentation
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.AtomicSpectral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped InnerProductSpace

namespace OddCycleBound.DenseRegion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def krylovSubspace (T : E →L[ℝ] E) (g : E) (d : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun j : Fin (d + 1) => linearIter T.toLinearMap j g)

/--
@isnad1 id=finitedi.0h4v.s7.eb30d64124ab from=translated src=- shape=583cc49d vocab=330d5c4b
-/
noncomputable instance krylovSubspace_finiteDimensional (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    FiniteDimensional ℝ (krylovSubspace T g d) := by
  unfold krylovSubspace
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

noncomputable def krylovVector (T : E →L[ℝ] E) (g : E) (d : ℕ) : krylovSubspace T g d :=
  ⟨g, Submodule.subset_span ⟨⟨0, Nat.succ_pos d⟩, by simp⟩⟩

noncomputable def krylovCompression (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    krylovSubspace T g d →L[ℝ] krylovSubspace T g d :=
  (krylovSubspace T g d).orthogonalProjectionOnto.comp
    (T.comp (krylovSubspace T g d).subtypeL)

/--
@isnad1 id=issymmet.1h4v.s9.b79529d1e200 from=translated src=- shape=e3d87fac vocab=a82e6d21
-/
theorem krylovCompression_isSymmetric (T : E →L[ℝ] E) (g : E) (d : ℕ)
    (hT : T.toLinearMap.IsSymmetric) :
    (krylovCompression T g d).toLinearMap.IsSymmetric := by
  intro x y
  unfold krylovCompression
  change inner ℝ ((krylovSubspace T g d).orthogonalProjectionOnto (T (x : E))) y =
    inner ℝ x ((krylovSubspace T g d).orthogonalProjectionOnto (T (y : E)))
  rw [(krylovSubspace T g d).inner_orthogonalProjectionOnto_eq_of_mem_right,
    (krylovSubspace T g d).inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hT x y

/--
@isnad1 id=le.0h4v.s10.f5a1cfaacd52 from=translated src=- shape=85ff43c3 vocab=ed0b2a7e
-/
theorem norm_krylovCompression_le (T : E →L[ℝ] E) (g : E) (d : ℕ) :
    ‖krylovCompression T g d‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
  unfold krylovCompression
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact ((krylovSubspace T g d).norm_orthogonalProjectionOnto_apply_le (T (x : E))).trans
    (T.le_opNorm (x : E))

/--
@isnad1 id=mem.1h5v.s8.5dd6db2a2edf from=translated src=- shape=a2fde060 vocab=74a27b90
-/
lemma linearIter_mem_krylovSubspace (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    linearIter T.toLinearMap j g ∈ krylovSubspace T g d := by
  apply Submodule.subset_span
  exact ⟨⟨j, by omega⟩, rfl⟩

noncomputable def krylovIterVector (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    krylovSubspace T g d :=
  ⟨linearIter T.toLinearMap j g, linearIter_mem_krylovSubspace T g hj⟩

/--
@isnad1 id=eq.1h5v.s9.04366d6a02e9 from=translated src=- shape=7ae53074 vocab=ba82bc6f
-/
theorem linearIter_krylovCompression (T : E →L[ℝ] E) (g : E) {d j : ℕ} (hj : j ≤ d) :
    linearIter (krylovCompression T g d).toLinearMap j (krylovVector T g d) =
      krylovIterVector T g hj := by
  induction j with
  | zero =>
      apply Subtype.ext
      rfl
  | succ j ih =>
      have hjd : j ≤ d := by omega
      rw [linearIter_succ, ih hjd]
      unfold krylovCompression
      change (krylovSubspace T g d).orthogonalProjectionOnto
          (T (linearIter T.toLinearMap j g)) = krylovIterVector T g hj
      change (krylovSubspace T g d).orthogonalProjectionOnto
          (krylovIterVector T g hj : E) = krylovIterVector T g hj
      exact (krylovSubspace T g d).orthogonalProjectionOnto_mem_subspace_eq_self
        (krylovIterVector T g hj)

/--
@isnad1 id=eq.1h5v.s10.dd14705936d3 from=translated src=- shape=e06ffeb1 vocab=8048a58e
-/
theorem inner_linearIter_krylovCompression_eq (T : E →L[ℝ] E) (g : E)
    {d j : ℕ} (hj : j ≤ d) :
    inner ℝ (krylovVector T g d)
        (linearIter (krylovCompression T g d).toLinearMap j (krylovVector T g d)) =
      inner ℝ g (linearIter T.toLinearMap j g) := by
  rw [linearIter_krylovCompression T g hj]
  exact Submodule.coe_inner _ _ _

/--
@isnad1 id=eq.2h5v.s11.477befe27686 from=translated src=- shape=e76b8996 vocab=513eaf2b
-/
theorem inner_linearIter_eq_krylovAtomicMoment (T : E →L[ℝ] E) (g : E)
    (hT : T.toLinearMap.IsSymmetric) {d j : ℕ} (hj : j ≤ d) :
    inner ℝ g (linearIter T.toLinearMap j g) =
      atomicMoment
        (finiteAtomWeight (krylovCompression T g d).toLinearMap
          (krylovCompression_isSymmetric T g d hT) (krylovVector T g d))
        (finiteAtomEigenvalue (krylovCompression T g d).toLinearMap
          (krylovCompression_isSymmetric T g d hT)) j := by
  rw [← inner_linearIter_krylovCompression_eq T g hj]
  exact inner_linearIter_eq_atomicMoment _ (krylovCompression_isSymmetric T g d hT) _ j

/--
@isnad1 id=mem.2h5v.s10.503e32e382a8 from=translated src=- shape=f2303dce vocab=4a437962
-/
theorem krylovAtomEigenvalue_mem_halfInterval (T : E →L[ℝ] E) (g : E) (d : ℕ)
    (hT : T.toLinearMap.IsSymmetric) (hnorm : ‖T‖ ≤ (1 : ℝ) / 2) (i) :
    finiteAtomEigenvalue (krylovCompression T g d).toLinearMap
        (krylovCompression_isSymmetric T g d hT) i ∈
      Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  apply eigenvalue_mem_halfInterval (krylovCompression T g d)
    ((norm_krylovCompression_le T g d).trans hnorm)
  · exact ((krylovCompression_isSymmetric T g d hT).eigenvectorBasis rfl).orthonormal.ne_zero i
  · change (krylovCompression T g d).toLinearMap
        ((krylovCompression_isSymmetric T g d hT).eigenvectorBasis rfl i) =
      finiteAtomEigenvalue (krylovCompression T g d).toLinearMap
          (krylovCompression_isSymmetric T g d hT) i •
        (krylovCompression_isSymmetric T g d hT).eigenvectorBasis rfl i
    simp [finiteAtomEigenvalue]

end OddCycleBound.DenseRegion
