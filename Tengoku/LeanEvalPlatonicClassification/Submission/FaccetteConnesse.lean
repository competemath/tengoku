import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.ConnessioneVentaglio
import Tengoku.LeanEvalPlatonicClassification.Submission.DiamanteRelativo
import Tengoku.LeanEvalPlatonicClassification.Submission.FacciaIntermedia
import Tengoku.LeanEvalPlatonicClassification.Submission.PerturbazioneFinita
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.PoligonoConnesso

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ}

/-! The convex hull of the image of a finite polytope, with the redundant
image points removed.  This is deliberately stated for a continuous linear
map: the quotient used below is not injective. -/
noncomputable def linearImagePolytope (P : ConvexPolytope n)
    (f : E n →L[ℝ] E m) : ConvexPolytope m := by
  classical
  let S : Finset (E m) := P.vertices.image f
  let K : Set (E m) := convexHull ℝ (S : Set (E m))
  let V : Finset (E m) := S.filter (fun x => x ∈ K.extremePoints ℝ)
  have hSne : S.Nonempty := P.vertices_nonempty.image f
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨x, subset_convexHull ℝ _ (by exact_mod_cast hx)⟩
  have hKcompact : IsCompact K := S.finite_toSet.isCompact_convexHull ℝ
  have hVne : V.Nonempty := by
    obtain ⟨x, hx⟩ := hKcompact.extremePoints_nonempty hKne
    have hxS : x ∈ (S : Set (E m)) := extremePoints_convexHull_subset hx
    exact ⟨x, Finset.mem_filter.mpr ⟨by exact_mod_cast hxS, hx⟩⟩
  have hVset : (V : Set (E m)) = K.extremePoints ℝ := by
    ext x
    simp only [V, Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by exact_mod_cast (extremePoints_convexHull_subset hx), hx⟩
  have hKV : convexHull ℝ (V : Set (E m)) = K := by
    have hKM := closure_convexHull_extremePoints hKcompact (convex_convexHull ℝ _)
    rw [← hVset] at hKM
    rw [← hKM]
    exact (V.finite_toSet.isClosed_convexHull ℝ).closure_eq.symm
  exact
    { vertices := V
      vertices_nonempty := hVne
      vertices_eq_extremePoints := by
        rw [hKV, hVset] }

/--
@isnad1 id=eq.0h4v.s9.94a41750f633 from=translated src=- shape=4f18fabc vocab=a148d9bb
-/
theorem linearImagePolytope_toSet (P : ConvexPolytope n)
    (f : E n →L[ℝ] E m) :
    (linearImagePolytope P f).toSet = f '' P.toSet := by
  classical
  let S : Finset (E m) := P.vertices.image f
  let K : Set (E m) := convexHull ℝ (S : Set (E m))
  let V : Finset (E m) := S.filter (fun x => x ∈ K.extremePoints ℝ)
  have hKcompact : IsCompact K := S.finite_toSet.isCompact_convexHull ℝ
  have hVset : (V : Set (E m)) = K.extremePoints ℝ := by
    ext x
    simp only [V, Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by exact_mod_cast (extremePoints_convexHull_subset hx), hx⟩
  have hKV : convexHull ℝ (V : Set (E m)) = K := by
    have hKM := closure_convexHull_extremePoints hKcompact (convex_convexHull ℝ _)
    rw [← hVset] at hKM
    rw [← hKM]
    exact (V.finite_toSet.isClosed_convexHull ℝ).closure_eq.symm
  change convexHull ℝ
      (((linearImagePolytope P f).vertices : Finset (E m)) : Set (E m)) = _
  change convexHull ℝ (V : Set (E m)) = _
  rw [hKV]
  have hS : (S : Set (E m)) = f '' (P.vertices : Set (E n)) := by
    ext x
    simp [S]
  rw [show K = convexHull ℝ (S : Set (E m)) from rfl, hS]
  exact (f.toLinearMap.toAffineMap.image_convexHull
    (P.vertices : Set (E n))).symm

/-! Orthogonal projection to `Uᵌ ∩ W` is the concrete quotient of `W`
by `U`.  The point of the next lemma is the exact fibre statement; no
ambient full-dimensionality is used. -/
/--
@isnad1 id=iff.2h5v.s11.08ceac7cf329 from=translated src=- shape=b63f69db vocab=8d8d9683
-/
theorem relative_starProjection_fiber
    {U W : Submodule ℝ (E n)} (hUW : U ≤ W) {x y : E n}
    (hxyW : x - y ∈ W) :
    (U.orthogonal ⊓ W).starProjection x =
        (U.orthogonal ⊓ W).starProjection y ↔
      x - y ∈ U := by
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  constructor
  · intro hproj
    have hzero : V.starProjection (x - y) = 0 := by
      rw [map_sub, hproj, sub_self]
    have hperp : x - y ∈ V.orthogonal := by
      rw [← V.ker_starProjection]
      exact hzero
    let p : E n := U.orthogonal.starProjection (x - y)
    have hpUperp : p ∈ U.orthogonal :=
      U.orthogonal.starProjection_apply_mem (x - y)
    have hdiffU : x - y - p ∈ U := by
      dsimp [p]
      rw [Submodule.starProjection_orthogonal_val]
      simpa only [sub_sub_cancel] using U.starProjection_apply_mem (x - y)
    have hpW : p ∈ W := by
      have hpform : p = (x - y) - (x - y - p) := by abel
      rw [hpform]
      exact W.sub_mem hxyW (hUW hdiffU)
    have hpV : p ∈ V := ⟨hpUperp, hpW⟩
    have hdp : inner ℝ (x - y) p = 0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal V (x - y)).mp hperp p hpV
    have hdiffp : inner ℝ (x - y - p) p = 0 := by
      exact (Submodule.mem_orthogonal U p).mp hpUperp (x - y - p) hdiffU
    have hpp : inner ℝ p p = 0 := by
      rw [inner_sub_left] at hdiffp
      linarith
    have hpzero : p = 0 := inner_self_eq_zero.mp hpp
    simpa [hpzero] using hdiffU
  · intro hxyU
    have hxyVperp : x - y ∈ V.orthogonal := by
      intro z hz
      rw [real_inner_comm]
      exact hz.1 (x - y) hxyU
    have hzero : V.starProjection (x - y) = 0 := by
      exact V.starProjection_apply_eq_zero_iff.mpr hxyVperp
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero

/--
@isnad1 id=mem.2h4v.s11.f71af998cb03 from=translated src=- shape=0d0094c4 vocab=8d8d9683
-/
theorem relative_sub_starProjection_mem
    {U W : Submodule ℝ (E n)} (hUW : U ≤ W) {z : E n} (hzW : z ∈ W) :
    z - (U.orthogonal ⊓ W).starProjection z ∈ U := by
  let V : Submodule ℝ (E n) := U.orthogonal ⊓ W
  have hpV : V.starProjection z ∈ V := V.starProjection_apply_mem z
  have hdiffW : z - V.starProjection z ∈ W :=
    W.sub_mem hzW hpV.2
  apply (relative_starProjection_fiber hUW hdiffW).mp
  exact (V.starProjection_eq_self_iff.mpr hpV).symm

/--
@isnad1 id=other.2h6v.s13.fb2e752d3720 from=translated src=- shape=03e275f5 vocab=9d41909a
-/
theorem relative_lift_isFace (P : ConvexPolytope n)
    {A B : Set (E n)} (_hA : P.IsFace A) (hB : P.IsFace B)
    (e : ↥((vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B) ≃L[ℝ] E 3)
    {Y : Set (E 3)} :
    let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
    let q : E n →L[ℝ] E 3 :=
      e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
    let Q := linearImagePolytope (facePolytope P hB) q
    Q.IsFace Y → P.IsFace (B ∩ q ⁻¹' Y) := by
  classical
  dsimp only
  let V := (vectorSpan ℝ A).orthogonal ⊓ vectorSpan ℝ B
  let q : E n →L[ℝ] E 3 :=
    e.toContinuousLinearMap.comp V.orthogonalProjectionOnto
  let QB := facePolytope P hB
  let Q := linearImagePolytope QB q
  intro hY
  obtain ⟨l3, hmem, hchar⟩ := espositore_di_faccia Q hY
  let l : E n →L[ℝ] ℝ := l3.comp q
  have hQT : Q.toSet = q '' B := by
    rw [linearImagePolytope_toSet, facePolytope_toSet P hB]
  have hLiftNe : (B ∩ q ⁻¹' Y).Nonempty := by
    obtain ⟨y, hyY⟩ := hY.2
    have hyQ : y ∈ Q.toSet := face_subset_toSet Q hY hyY
    rw [hQT] at hyQ
    obtain ⟨x, hxB, rfl⟩ := hyQ
    exact ⟨x, hxB, hyY⟩
  have hLiftQB : QB.IsFace (B ∩ q ⁻¹' Y) := by
    refine ⟨?_, hLiftNe⟩
    intro _hne
    refine ⟨l, Set.ext ?_⟩
    intro x
    constructor
    · rintro ⟨hxB, hqxY⟩
      have hqxQ : q x ∈ Q.toSet := by
        rw [hQT]
        exact ⟨x, hxB, rfl⟩
      refine ⟨?_, ?_⟩
      · change x ∈ (facePolytope P hB).toSet
        rwa [facePolytope_toSet P hB]
      · intro z hzQB
        have hzB : z ∈ B := by
          change z ∈ (facePolytope P hB).toSet at hzQB
          rwa [facePolytope_toSet P hB] at hzQB
        change l3 (q z) ≤ l3 (q x)
        exact (hmem (q x) hqxY).2 (q z) (by
          rw [hQT]
          exact ⟨z, hzB, rfl⟩)
    · rintro ⟨hxQB, hxmax⟩
      have hxB : x ∈ B := by
        change x ∈ (facePolytope P hB).toSet at hxQB
        rwa [facePolytope_toSet P hB] at hxQB
      refine ⟨hxB, ?_⟩
      apply hchar (q x) (by rw [hQT]; exact ⟨x, hxB, rfl⟩)
      intro y hyQ
      rw [hQT] at hyQ
      obtain ⟨z, hzB, rfl⟩ := hyQ
      apply hxmax z
      change z ∈ (facePolytope P hB).toSet
      rwa [facePolytope_toSet P hB]
  exact isFace_of_facePolytope P hB hLiftQB

end LeanEval.Geometry.PlatonicClassification
