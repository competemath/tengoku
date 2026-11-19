/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Rotations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The orthogonal action on unit directions

The orthogonal group acts continuously and transitively on the unit
sphere. Transitivity follows by extending the isometry between the
one-dimensional spans of two unit vectors to the ambient space.
-/

@[expose] public section

open MeasureTheory Submodule Metric

namespace NKBesicovitch.Rotations

variable {n : ℕ}

/-- The action of an orthogonal operator on a unit direction.-/
noncomputable def rotateSphere (u : Rotations n)
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨Unitary.linearIsometryEquiv u v, by
    simpa only [mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using
      norm_eq_of_mem_sphere v⟩

/--
@isnad1 id=eq.0h2v.s13.09da0e14e1b9 from=translated src=- shape=0f4d42b5 vocab=43db5f8c
-/
theorem rotateSphere_one (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    rotateSphere 1 v = v := by
  apply Subtype.ext
  rfl

/--
@isnad1 id=eq.0h4v.s14.e9686d592344 from=translated src=- shape=84c0525e vocab=58b38cc2
-/
theorem rotateSphere_mul (u w : Rotations n)
    (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    rotateSphere (u * w) v = rotateSphere u (rotateSphere w v) := by
  apply Subtype.ext
  rfl

/--
@isnad1 id=continuo.0h1v.s14.072cf13da6f9 from=translated src=- shape=690cb77f vocab=ac09f69e
-/
theorem continuous_rotateSphere :
    Continuous (fun p : Rotations n × sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
      rotateSphere p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).clm_apply
    (continuous_subtype_val.comp continuous_snd)

noncomputable instance : MulAction (Rotations n) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) where
  smul := rotateSphere
  one_smul := rotateSphere_one
  mul_smul := rotateSphere_mul

/--
@isnad1 id=ex.0h3v.s12.8f1720a2dd74 from=translated src=- shape=a2240199 vocab=43db5f8c
-/
theorem exists_rotateSphere_eq (v w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ u : Rotations n, rotateSphere u v = w := by
  let ev : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n))) :=
    LinearIsometryEquiv.toSpanUnitSingleton (v : EuclideanSpace ℝ (Fin n))
    (norm_eq_of_mem_sphere v)
  let ew : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ (w : EuclideanSpace ℝ (Fin n))) :=
    LinearIsometryEquiv.toSpanUnitSingleton (w : EuclideanSpace ℝ (Fin n))
    (norm_eq_of_mem_sphere w)
  let L := (ℝ ∙ (w : EuclideanSpace ℝ (Fin n))).subtypeₗᵢ.comp
    (ev.symm.trans ew).toLinearIsometry
  let e := L.extend.toLinearIsometryEquiv rfl
  refine ⟨Unitary.linearIsometryEquiv.symm e, ?_⟩
  apply Subtype.ext
  change L.extend (v : EuclideanSpace ℝ (Fin n)) = (w : EuclideanSpace ℝ (Fin n))
  rw [L.extend_apply ⟨v, mem_span_singleton_self _⟩]
  have hv : ev 1 = ⟨v, mem_span_singleton_self _⟩ := by
    apply Subtype.ext
    simp [ev]
  rw [← hv]
  change (ew (ev.symm (ev 1)) : EuclideanSpace ℝ (Fin n)) = w
  simp [ew]

end NKBesicovitch.Rotations
