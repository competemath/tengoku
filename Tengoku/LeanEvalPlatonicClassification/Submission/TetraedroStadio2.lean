import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Fondamenta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set Metric
open scoped RealInnerProductSpace

noncomputable section

/-! ## Copia di `Platonici_Tetraedro.lean` -/

abbrev _root_.Tengoku.LeanEvalPlatonicClassification.E3 := EuclideanSpace ℝ (Fin 3)

/--
@isnad1 id=eq.1h4v.s7.8ba8e447e686 from=translated src=- shape=3c79d8e4 vocab=bd3cbdd4
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.cosferico_extremePoints {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] [Nontrivial A]
    (x : A) (r : ℝ) (V : Set A) (hV : V ⊆ sphere x r) :
    (convexHull ℝ V).extremePoints ℝ = V := by
  refine le_antisymm extremePoints_convexHull_subset ?_
  have hball : convexHull ℝ V ⊆ closedBall x r :=
    convexHull_min (hV.trans sphere_subset_closedBall) (convex_closedBall x r)
  intro v hv
  have hsfera : v ∈ (closedBall x r).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    exact hV hv
  exact inter_extremePoints_subset_extremePoints_of_subset hball
    ⟨subset_convexHull ℝ V hv, hsfera⟩

def _root_.Tengoku.LeanEvalPlatonicClassification.w0 : E3 := WithLp.toLp 2 ![1, 1, 1]
def _root_.Tengoku.LeanEvalPlatonicClassification.w1 : E3 := WithLp.toLp 2 ![1, -1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.w2 : E3 := WithLp.toLp 2 ![-1, 1, -1]
def _root_.Tengoku.LeanEvalPlatonicClassification.w3 : E3 := WithLp.toLp 2 ![-1, -1, 1]

open Classical in
def _root_.Tengoku.LeanEvalPlatonicClassification.verticiTetra : Finset E3 := {w0, w1, w2, w3}

/--
@isnad1 id=eq.0h3v.s7.5fdaa67f4b62 from=translated src=- shape=bc44a84a vocab=494e4ac0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.norma_toLp (a b c : ℝ) :
    ‖(WithLp.toLp 2 ![a, b, c] : E3)‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  norm_num [show (![a, b, c] : Fin 3 → ℝ) 0 = a from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 1 = b from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 2 = c from rfl]

/--
@isnad1 id=eq.1h1v.s6.9c5f5f989976 from=translated src=- shape=3bc45c0e vocab=285fb170
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.norm_vertici : ∀ v ∈ verticiTetra, ‖v‖ = Real.sqrt 3 := by
  intro v hv
  have hcasi : v = w0 ∨ v = w1 ∨ v = w2 ∨ v = w3 := by
    simpa [verticiTetra] using hv
  rcases hcasi with h | h | h | h
  · subst h
    show ‖(WithLp.toLp 2 ![(1:ℝ), 1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(1:ℝ), -1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(-1:ℝ), 1, -1] : E3)‖ = _
    rw [norma_toLp]; norm_num
  · subst h
    show ‖(WithLp.toLp 2 ![(-1:ℝ), -1, 1] : E3)‖ = _
    rw [norma_toLp]; norm_num

def _root_.Tengoku.LeanEvalPlatonicClassification.tetraedro : FiniteConvexPolytope E3 where
  vertices := verticiTetra
  nonempty := ⟨w0, by simp [verticiTetra]⟩
  vertices_eq_extremePoints := by
    have hV : (verticiTetra : Set E3) ⊆ sphere 0 (Real.sqrt 3) := by
      intro v hv
      rw [mem_sphere_zero_iff_norm]
      exact norm_vertici v (by exact_mod_cast hv)
    exact (cosferico_extremePoints 0 (Real.sqrt 3) _ hV).symm

/-! ## Coordinate finite e indipendenza affine -/

def _root_.Tengoku.LeanEvalPlatonicClassification.w : Fin 4 → E3 := ![w0, w1, w2, w3]

/--
@isnad1 id=eq.0h0v.s4.d59fd54e6a86 from=translated src=- shape=fdee698a vocab=18c11e4b
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.w_apply_zero : w 0 = w0 := rfl
/--
@isnad1 id=eq.0h0v.s4.95c50156144f from=translated src=- shape=fdee698a vocab=e5541724
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.w_apply_one : w 1 = w1 := rfl
/--
@isnad1 id=eq.0h0v.s4.df5b122795d6 from=translated src=- shape=fdee698a vocab=b1ca6fb3
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.w_apply_two : w 2 = w2 := rfl
/--
@isnad1 id=eq.0h0v.s4.76a3afb8bb52 from=translated src=- shape=fdee698a vocab=aa2364f0
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.w_apply_three : w 3 = w3 := rfl

/--
@isnad1 id=affinein.0h0v.s8.c11bf0b496a6 from=translated src=- shape=7e71be5a vocab=bbeb1ec4
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.w_affineIndependent : AffineIndependent ℝ w := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro a b ha hb hab
  funext i
  have hcoord (j : Fin 3) := congrArg (fun x : E3 => x j) hab
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using ha),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hb)] at hcoord
  simp [w, w0, w1, w2, w3, Fin.sum_univ_four] at hcoord
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  change a 0 * 1 + a 1 * 1 + a 2 * (-1) + a 3 * (-1) =
    b 0 * 1 + b 1 * 1 + b 2 * (-1) + b 3 * (-1) at h0
  change a 0 * 1 + a 1 * (-1) + a 2 * 1 + a 3 * (-1) =
    b 0 * 1 + b 1 * (-1) + b 2 * 1 + b 3 * (-1) at h1
  change a 0 * 1 + a 1 * (-1) + a 2 * (-1) + a 3 * 1 =
    b 0 * 1 + b 1 * (-1) + b 2 * (-1) + b 3 * 1 at h2
  rw [Fin.sum_univ_four] at ha hb
  have e0 : a 0 = b 0 := by linarith
  have e1 : a 1 = b 1 := by linarith
  have e2 : a 2 = b 2 := by linarith
  have e3 : a 3 = b 3 := by linarith
  fin_cases i
  · exact e0
  · exact e1
  · simpa using e2
  · simpa using e3

/--
@isnad1 id=injectiv.0h0v.s3.321fba3143f8 from=translated src=- shape=bfe16b09 vocab=65261403
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.w_injective : Function.Injective w := w_affineIndependent.injective

def _root_.Tengoku.LeanEvalPlatonicClassification.wEmb : Fin 4 ↪ E3 := ⟨w, w_injective⟩

/--
@isnad1 id=eq.0h0v.s4.712696c0e6c6 from=translated src=- shape=005f93a2 vocab=3f3b2505
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.verticiTetra_eq_map : verticiTetra = Finset.univ.map wEmb := by
  ext x
  simp only [verticiTetra, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [wEmb, w]

/--
@isnad1 id=eq.0h0v.s4.64f60a91cb49 from=translated src=- shape=75b2c703 vocab=09cae4e0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.range_w_eq_vertices : Set.range w = (verticiTetra : Set E3) := by
  rw [verticiTetra_eq_map]
  ext x
  simp [wEmb]

def _root_.Tengoku.LeanEvalPlatonicClassification.tetraBasis : AffineBasis (Fin 4) ℝ E3 where
  toFun := w
  ind' := w_affineIndependent
  tot' := by
    apply (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E3 E3
      ⟨w 0, Set.mem_range_self 0⟩).2
    exact w_affineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one (by simp)

/--
@isnad1 id=eq.0h1v.s9.41c6cb38d5ea from=translated src=- shape=d38ba8b0 vocab=e0a691d5
-/
@[simp] theorem _root_.Tengoku.LeanEvalPlatonicClassification.tetraBasis_apply (i : Fin 4) : tetraBasis i = w i := rfl

/--
@isnad1 id=eq.0h0v.s9.1fdc3a0fc3ab from=translated src=- shape=dc71d321 vocab=505b1fea
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.range_tetraBasis_eq_vertices :
    Set.range tetraBasis = (tetraedro.vertices : Set E3) := by
  change Set.range w = (verticiTetra : Set E3)
  exact range_w_eq_vertices

def _root_.Tengoku.LeanEvalPlatonicClassification.faceVertices (k : Fin 4) : Finset E3 :=
  (Finset.univ.erase k).map wEmb

def _root_.Tengoku.LeanEvalPlatonicClassification.tetraFace (k : Fin 4) : Set E3 :=
  convexHull ℝ (faceVertices k : Set E3)

/--
@isnad1 id=le.0h1v.s4.79cca2b10f0a from=translated src=- shape=a2f0bcd3 vocab=f04aaede
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceVertices_subset (k : Fin 4) : faceVertices k ⊆ verticiTetra := by
  rw [verticiTetra_eq_map]
  exact Finset.map_subset_map.mpr (Finset.erase_subset _ _)

/--
@isnad1 id=eq.0h1v.s4.840eebda9ed2 from=translated src=- shape=ae9651fe vocab=c00b9219
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceVertices_card (k : Fin 4) : (faceVertices k).card = 3 := by
  simp [faceVertices]

/--
@isnad1 id=nonempty.0h1v.s3.5f7bf0b33f4e from=translated src=- shape=f3e6f14a vocab=38c38f8d
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tetraFace_nonempty (k : Fin 4) : (tetraFace k).Nonempty := by
  apply Set.Nonempty.mono (subset_convexHull ℝ (faceVertices k : Set E3))
  simpa only [Finset.coe_nonempty] using (Finset.card_pos.mp (by simp [faceVertices_card k]))

/--
@isnad1 id=eq.0h1v.s10.f20ff0f36547 from=translated src=- shape=d7f8c8d5 vocab=d14fb3ae
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tetraFace_finrank (k : Fin 4) :
    Module.finrank ℝ (vectorSpan ℝ (tetraFace k)) = 2 := by
  rw [tetraFace, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  unfold faceVertices
  rw [Finset.map_eq_image]
  change Module.finrank ℝ
    (vectorSpan ℝ ((Finset.univ.erase k).image w : Set E3)) = 2
  exact w_affineIndependent.finrank_vectorSpan_image_finset
    (s := Finset.univ.erase k) (n := 2) (by simp)

/--
@isnad1 id=iff.0h2v.s10.10aed50a3ab4 from=translated src=- shape=abd98b50 vocab=d7d21d09
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.mem_tetraFace_iff (k : Fin 4) (x : E3) :
    x ∈ tetraFace k ↔
      x ∈ tetraedro.toSet ∧ tetraBasis.coord k x = 0 := by
  have hfull : tetraFace k ⊆ tetraedro.toSet := by
    apply convexHull_mono
    change (faceVertices k : Set E3) ⊆ (verticiTetra : Set E3)
    exact_mod_cast faceVertices_subset k
  have hzero : tetraFace k ⊆ (tetraBasis.coord k) ⁻¹' ({0} : Set ℝ) := by
    apply convexHull_min
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      change tetraBasis.coord k (w i) = 0
      rw [← tetraBasis_apply i, tetraBasis.coord_apply]
      simp [hik.symm]
    · exact convex_singleton 0 |>.affine_preimage (tetraBasis.coord k)
  constructor
  · intro hx
    exact ⟨hfull hx, by simpa using hzero hx⟩
  · rintro ⟨hx, hxk⟩
    have hn : ∀ i : Fin 4, 0 ≤ tetraBasis.coord i x := by
      have hm : x ∈ convexHull ℝ (Set.range tetraBasis) := by
        simpa [FiniteConvexPolytope.toSet, range_tetraBasis_eq_vertices] using hx
      rw [tetraBasis.convexHull_eq_nonneg_coord] at hm
      exact hm
    let I := {i : Fin 4 // i ≠ k}
    refine mem_convexHull_of_exists_fintype
      (ι := I) (fun i => tetraBasis.coord i x) (fun i => w i) ?_ ?_ ?_ ?_
    · intro i
      exact hn i
    · rw [← Finset.sum_subtype (p := fun i : Fin 4 => i ≠ k)
        (Finset.univ.erase k) (by simp) (fun i => tetraBasis.coord i x)]
      calc
        ∑ i ∈ (Finset.univ.erase k), tetraBasis.coord i x =
            ∑ i ∈ (Finset.univ : Finset (Fin 4)), tetraBasis.coord i x :=
          Finset.sum_erase (s := (Finset.univ : Finset (Fin 4)))
            (f := fun i => tetraBasis.coord i x) hxk
        _ = 1 := tetraBasis.sum_coord_apply_eq_one x
    · intro i
      exact Finset.mem_map.mpr ⟨i.val, Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩, rfl⟩
    · calc
        ∑ i : I, tetraBasis.coord i x • w i =
            ∑ i ∈ Finset.univ.erase k, tetraBasis.coord i x • tetraBasis i := by
              rw [Finset.sum_subtype (p := fun i : Fin 4 => i ≠ k)
                (Finset.univ.erase k) (by simp)]
              rfl
        _ = ∑ i : Fin 4, tetraBasis.coord i x • tetraBasis i := by
              exact Finset.sum_erase (s := (Finset.univ : Finset (Fin 4)))
                (f := fun i => tetraBasis.coord i x • tetraBasis i) (by simp [hxk])
        _ = x := tetraBasis.linear_combination_coord_eq_self x

/--
@isnad1 id=isexpose.0h1v.s8.e2c791cfb374 from=translated src=- shape=2934168a vocab=f2d1334c
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tetraFace_isExposed (k : Fin 4) :
    IsExposed ℝ tetraedro.toSet (tetraFace k) := by
  intro _hne
  let L : E3 →L[ℝ] ℝ := -(tetraBasis.coord k).linear.toContinuousLinearMap
  refine ⟨L, ?_⟩
  ext x
  rw [mem_tetraFace_iff]
  constructor
  · rintro ⟨hxP, hx0⟩
    refine ⟨hxP, ?_⟩
    intro y hyP
    have hny : 0 ≤ tetraBasis.coord k y := by
      have hm : y ∈ convexHull ℝ (Set.range tetraBasis) := by
        simpa [FiniteConvexPolytope.toSet, range_tetraBasis_eq_vertices] using hyP
      have : ∀ i : Fin 4, 0 ≤ tetraBasis.coord i y := by
        rw [tetraBasis.convexHull_eq_nonneg_coord] at hm
        exact hm
      exact this k
    change -(tetraBasis.coord k).linear y ≤ -(tetraBasis.coord k).linear x
    have haff (z : E3) :
        (tetraBasis.coord k).linear z = tetraBasis.coord k z - tetraBasis.coord k 0 := by
      simpa using congrFun (tetraBasis.coord k).decomp' z
    rw [haff, haff, hx0]
    linarith
  · rintro ⟨hxP, hxmax⟩
    refine ⟨hxP, ?_⟩
    let j : Fin 4 := finRotate 4 k
    have hjk : j ≠ k := by
      dsimp [j]
      fin_cases k <;> decide
    have hwjP : w j ∈ tetraedro.toSet := by
      apply subset_convexHull ℝ
      change w j ∈ (verticiTetra : Set E3)
      rw [← range_w_eq_vertices]
      exact Set.mem_range_self j
    have hle := hxmax (w j) hwjP
    have hxnonneg : 0 ≤ tetraBasis.coord k x := by
      have hm : x ∈ convexHull ℝ (Set.range tetraBasis) := by
        simpa [FiniteConvexPolytope.toSet, range_tetraBasis_eq_vertices] using hxP
      have : ∀ i : Fin 4, 0 ≤ tetraBasis.coord i x := by
        rw [tetraBasis.convexHull_eq_nonneg_coord] at hm
        exact hm
      exact this k
    change -(tetraBasis.coord k).linear (w j) ≤
      -(tetraBasis.coord k).linear x at hle
    have haff (z : E3) :
        (tetraBasis.coord k).linear z = tetraBasis.coord k z - tetraBasis.coord k 0 := by
      simpa using congrFun (tetraBasis.coord k).decomp' z
    rw [haff, haff] at hle
    rw [← tetraBasis_apply j, tetraBasis.coord_apply] at hle
    simp [hjk.symm] at hle
    linarith

/--
@isnad1 id=isfacet.0h1v.s6.d454c86e60d7 from=translated src=- shape=58d06a47 vocab=63b5c089
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tetraFace_isFacet (k : Fin 4) : tetraedro.IsFacet (tetraFace k) := by
  exact ⟨⟨tetraFace_isExposed k, tetraFace_nonempty k⟩, tetraFace_finrank k⟩

/--
@isnad1 id=eq.0h1v.s6.86f73c1282de from=translated src=- shape=93df2467 vocab=ed0d61da
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.faceVertices_eq_erase (k : Fin 4) :
    faceVertices k = verticiTetra.erase (w k) := by
  rw [faceVertices, Finset.map_erase, ← verticiTetra_eq_map]
  rfl

open Classical in
/--
@isnad1 id=eq.1h1v.s8.8f11db88c9e5 from=translated src=- shape=d419a73e vocab=2bb56da6
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.exposedFace_eq_convexHull_vertices {F : Set E3}
    (hF : tetraedro.IsFace F) :
    F = convexHull ℝ ((tetraedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := by
  classical
  let S : Finset E3 := tetraedro.vertices.filter (· ∈ F)
  have hPcompact : IsCompact tetraedro.toSet := by
    exact (tetraedro.vertices.finite_toSet.isCompact_convexHull ℝ)
  have hFcompact : IsCompact F := hF.1.isCompact hPcompact
  have hFconvex : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : F.extremePoints ℝ = (S : Set E3) := by
    rw [hF.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    change (x ∈ F ∧ x ∈ tetraedro.toSet.extremePoints ℝ) ↔
      x ∈ tetraedro.vertices ∧ x ∈ F
    rw [FiniteConvexPolytope.toSet, ← tetraedro.vertices_eq_extremePoints]
    tauto
  calc
    F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set E3)) := by rw [hext]
    _ = convexHull ℝ (S : Set E3) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((tetraedro.vertices.filter (· ∈ F) : Finset E3) : Set E3) := rfl

/--
@isnad1 id=affinein.0h0v.s8.bd4d755dbed5 from=translated src=- shape=0d5c9307 vocab=d8098ae3
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.affineIndependent_vertices :
    AffineIndependent ℝ
      ((↑) : {x // x ∈ (tetraedro.vertices : Set E3)} → E3) := by
  rw [← range_tetraBasis_eq_vertices]
  exact tetraBasis.ind.range

/--
@isnad1 id=ex.1h1v.s6.a6f53a49fe1b from=translated src=- shape=fbbec5b8 vocab=67eb4c9e
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.facet_classification {F : Set E3} (hF : tetraedro.IsFacet F) :
    ∃ k : Fin 4, F = tetraFace k := by
  classical
  let S : Finset E3 := tetraedro.vertices.filter (· ∈ F)
  have hFS : F = convexHull ℝ (S : Set E3) := exposedFace_eq_convexHull_vertices hF.1
  have hSsub : S ⊆ tetraedro.vertices := by
    change tetraedro.vertices.filter (· ∈ F) ⊆ tetraedro.vertices
    exact Finset.filter_subset _ _
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hne := hF.1.2
    rw [hFS, h] at hne
    simp at hne
  have hSind : AffineIndependent ℝ
      ((↑) : {x // x ∈ (S : Set E3)} → E3) :=
    affineIndependent_vertices.mono (by
      intro x hx
      exact_mod_cast hSsub hx)
  have hd : Module.finrank ℝ (vectorSpan ℝ (S : Set E3)) = 2 := by
    have hdF := hF.2
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan] at hdF
    exact hdF
  letI : Nonempty {x // x ∈ (S : Set E3)} :=
    ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  have hcard : S.card = 3 := by
    have hdim := hSind.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ (S : Set E3)} → E3) = (S : Set E3) :=
      Subtype.range_coe_subtype
    rw [hrange, hd] at hdim
    simpa using hdim.symm
  have hVcard : tetraedro.vertices.card = 4 := by
    change verticiTetra.card = 4
    rw [verticiTetra_eq_map, Finset.card_map]
    simp
  have hSneV : S ≠ tetraedro.vertices := by
    intro heq
    rw [heq, hVcard] at hcard
    omega
  obtain ⟨a, haV, haS⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨hSsub, hSneV⟩)
  have hSerase : S = tetraedro.vertices.erase a := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact Finset.mem_erase.mpr ⟨fun hxa => haS (hxa ▸ hx), hSsub hx⟩
    · rw [Finset.card_erase_of_mem haV, hVcard, hcard]
  have haRange : a ∈ Set.range w := by
    rw [range_w_eq_vertices]
    exact haV
  obtain ⟨k, rfl⟩ := haRange
  refine ⟨k, ?_⟩
  rw [hFS, hSerase]
  congr 1
  exact_mod_cast (faceVertices_eq_erase k).symm

/-! ## Le quattro rotazioni di ordine tre -/

def _root_.Tengoku.LeanEvalPlatonicClassification.flip1 : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.refl ℝ ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.neg ℝ]

def _root_.Tengoku.LeanEvalPlatonicClassification.flip2 : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.refl ℝ ℝ,
      LinearIsometryEquiv.neg ℝ]

def _root_.Tengoku.LeanEvalPlatonicClassification.flip3 : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![LinearIsometryEquiv.neg ℝ, LinearIsometryEquiv.neg ℝ,
      LinearIsometryEquiv.refl ℝ ℝ]

def _root_.Tengoku.LeanEvalPlatonicClassification.rot0Linear : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate 3)

def _root_.Tengoku.LeanEvalPlatonicClassification.rotLinear : Fin 4 → E3 ≃ₗᵢ[ℝ] E3 :=
  ![rot0Linear,
    flip1.trans (rot0Linear.trans flip1),
    flip2.trans (rot0Linear.trans flip2),
    flip3.trans (rot0Linear.trans flip3)]

def _root_.Tengoku.LeanEvalPlatonicClassification.rot (k : Fin 4) : E3 ≃ᵃⁱ[ℝ] E3 :=
  (rotLinear k).toAffineIsometryEquiv

def _root_.Tengoku.LeanEvalPlatonicClassification.τ0 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.τ1 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.τ2 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.τ3 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def _root_.Tengoku.LeanEvalPlatonicClassification.τ : Fin 4 → Equiv.Perm (Fin 4) := ![τ0, τ1, τ2, τ3]

def _root_.Tengoku.LeanEvalPlatonicClassification.opp : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 3, 2], ![0, 1, 3], ![0, 2, 1]]

/--
@isnad1 id=eq.0h1v.s6.acf9bf5be7f5 from=translated src=- shape=b7c5c06e vocab=edcec7af
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.τ_fixed (k : Fin 4) : τ k k = k := by
  fin_cases k <;> rfl

/--
@isnad1 id=ne.0h2v.s4.c30ff2eeb888 from=translated src=- shape=863660e4 vocab=01153f17
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.opp_ne (k : Fin 4) (i : Fin 3) : opp k i ≠ k := by
  fin_cases k <;> fin_cases i <;> decide

/--
@isnad1 id=injectiv.0h1v.s4.9e950ec9de6d from=translated src=- shape=bac0a165 vocab=aa7a6910
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.opp_injective (k : Fin 4) : Function.Injective (opp k) := by
  intro i j hij
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp_all [opp]

/--
@isnad1 id=ex.1h2v.s5.8778161ef29d from=translated src=- shape=19bf2012 vocab=01153f17
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.opp_complete (k j : Fin 4) (hjk : j ≠ k) : ∃ i : Fin 3, opp k i = j := by
  fin_cases k <;> fin_cases j <;> simp_all [opp]
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

/--
@isnad1 id=eq.0h2v.s7.11555db1b369 from=translated src=- shape=7ed4e130 vocab=ba8d35a0
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.τ_opp (k : Fin 4) (i : Fin 3) :
    τ k (opp k i) = opp k (finRotate 3 i) := by
  fin_cases k <;> fin_cases i <;> rfl

/--
@isnad1 id=eq.0h2v.s10.b20b5d88bacb from=translated src=- shape=f706fb6b vocab=25e3af39
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rot_vertex (k i : Fin 4) : rot k (w i) = w (τ k i) := by
  have hm1 : (-1 : Fin 3) = 2 := by decide
  have h21 : (2 - 1 : Fin 3) = 1 := by decide
  fin_cases k <;> fin_cases i <;> ext j <;> fin_cases j <;>
    simp [rot, rotLinear, rot0Linear, flip1, flip2, flip3,
      w, w0, w1, w2, w3, τ, τ0, τ1, τ2, τ3, hm1, h21]

/--
@isnad1 id=eq.0h1v.s10.7e6965619f1d from=translated src=- shape=7d6fee41 vocab=e811a4e3
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rot_fixed (k : Fin 4) : rot k (w k) = w k := by
  rw [rot_vertex, τ_fixed]

/--
@isnad1 id=eq.0h1v.s10.bfabdffd0cdb from=translated src=- shape=7ac53442 vocab=904ac59d
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rot_image_vertices (k : Fin 4) :
    (⇑(rot k)) '' (tetraedro.vertices : Set E3) =
      (tetraedro.vertices : Set E3) := by
  rw [← range_tetraBasis_eq_vertices, show Set.range tetraBasis = Set.range w by rfl]
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [rot_vertex]
    exact Set.mem_range_self (τ k i)
  · rintro ⟨i, rfl⟩
    refine ⟨w ((τ k).symm i), Set.mem_range_self _, ?_⟩
    rw [rot_vertex, (τ k).apply_symm_apply]

/--
@isnad1 id=eq.0h1v.s10.9b4bfc6dfbc2 from=translated src=- shape=c08ff654 vocab=68f8496e
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rot_preserves_polytope (k : Fin 4) :
    (⇑(rot k)) '' tetraedro.toSet = tetraedro.toSet := by
  change (⇑(rot k)) '' convexHull ℝ (tetraedro.vertices : Set E3) =
    convexHull ℝ (tetraedro.vertices : Set E3)
  calc
    (⇑(rot k)) '' convexHull ℝ (tetraedro.vertices : Set E3) =
        convexHull ℝ ((⇑(rot k)) '' (tetraedro.vertices : Set E3)) := by
      simpa only [AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.coe_toAffineEquiv] using
        ((rot k).toAffineEquiv.toAffineMap.image_convexHull
          (tetraedro.vertices : Set E3))
    _ = convexHull ℝ (tetraedro.vertices : Set E3) := by
      rw [rot_image_vertices]

/--
@isnad1 id=eq.0h2v.s10.89735caf125e from=translated src=- shape=4ec52a3a vocab=b6d2bd62
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rot_image_faceVertices (k a : Fin 4) :
    (⇑(rot k)) '' (faceVertices a : Set E3) =
      (faceVertices (τ k a) : Set E3) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
    change rot k (w i) ∈ (faceVertices (τ k a) : Set E3)
    rw [rot_vertex]
    apply Finset.mem_map.mpr
    refine ⟨τ k i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    exact (τ k).injective.ne (Finset.ne_of_mem_erase hi)
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Finset.mem_map.mp hx
    subst x
    let i := (τ k).symm j
    have hia : i ≠ a := by
      intro h
      apply Finset.ne_of_mem_erase hj
      rw [← h, (τ k).apply_symm_apply]
    refine ⟨w i, ?_, ?_⟩
    · exact Finset.mem_map.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hia, Finset.mem_univ _⟩, rfl⟩
    · rw [rot_vertex, (τ k).apply_symm_apply]
      rfl

/--
@isnad1 id=eq.0h2v.s10.fa52478201c2 from=translated src=- shape=2d51fa4e vocab=d1db3b79
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.rot_image_tetraFace (k a : Fin 4) :
    (⇑(rot k)) '' tetraFace a = tetraFace (τ k a) := by
  change (⇑(rot k)) '' convexHull ℝ (faceVertices a : Set E3) =
    convexHull ℝ (faceVertices (τ k a) : Set E3)
  calc
    (⇑(rot k)) '' convexHull ℝ (faceVertices a : Set E3) =
        convexHull ℝ ((⇑(rot k)) '' (faceVertices a : Set E3)) := by
      simpa only [AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.coe_toAffineEquiv] using
        ((rot k).toAffineEquiv.toAffineMap.image_convexHull
          (faceVertices a : Set E3))
    _ = convexHull ℝ (faceVertices (τ k a) : Set E3) := by
      rw [rot_image_faceVertices]

/-! ## Regolarità uniforme delle quattro faccette -/

def _root_.Tengoku.LeanEvalPlatonicClassification.edgeLength : ℝ := Real.sqrt 8

/--
@isnad1 id=lt.0h0v.s3.a43d7fcfb706 from=translated src=- shape=ff3a10fc vocab=a7d79b97
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.edgeLength_pos : 0 < edgeLength := by
  dsimp [edgeLength]
  positivity

/-! ## I fan ciclici ai quattro vertici -/

/--
@isnad1 id=iff.0h2v.s5.af305035bd13 from=translated src=- shape=0b1bf834 vocab=6f9a5d6f
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.vertex_mem_tetraFace_iff (i a : Fin 4) :
    w i ∈ tetraFace a ↔ i ≠ a := by
  constructor
  · intro hi hia
    subst a
    have hz := (mem_tetraFace_iff i (w i)).mp hi |>.2
    rw [← tetraBasis_apply i, tetraBasis.coord_apply] at hz
    norm_num at hz
  · intro hia
    apply subset_convexHull ℝ
    exact Finset.mem_map.mpr
      ⟨i, Finset.mem_erase.mpr ⟨hia, Finset.mem_univ _⟩, rfl⟩

/--
@isnad1 id=injectiv.0h0v.s3.5db10d8887e3 from=translated src=- shape=b032868b vocab=ce2100b4
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.tetraFace_injective : Function.Injective tetraFace := by
  intro a b hab
  by_contra habne
  have hmem : w a ∈ tetraFace b := (vertex_mem_tetraFace_iff a b).2 habne
  rw [← hab] at hmem
  exact (vertex_mem_tetraFace_iff a a).1 hmem rfl

/--
@isnad1 id=mem.0h2v.s4.4972405b9bd8 from=translated src=- shape=7aa90588 vocab=1754a368
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.vertex_mem_incident_face (k : Fin 4) (i : Fin 3) :
    w k ∈ tetraFace (opp k i) :=
  (vertex_mem_tetraFace_iff k (opp k i)).2 (opp_ne k i).symm

def _root_.Tengoku.LeanEvalPlatonicClassification.thirdOpp (k : Fin 4) (i : Fin 3) : Fin 4 :=
  opp k (finRotate 3 (finRotate 3 i))

/--
@isnad1 id=ne.0h2v.s4.f307e620d0fd from=translated src=- shape=863660e4 vocab=d75891b9
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.thirdOpp_ne_vertex (k : Fin 4) (i : Fin 3) : thirdOpp k i ≠ k :=
  opp_ne k _

/--
@isnad1 id=ne.0h2v.s4.7a1f35d6ffd0 from=translated src=- shape=ba312d2c vocab=11c7ce14
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.thirdOpp_ne_current (k : Fin 4) (i : Fin 3) :
    thirdOpp k i ≠ opp k i := by
  intro h
  have := opp_injective k h
  fin_cases i <;> contradiction

/--
@isnad1 id=ne.0h2v.s6.39ba89be036d from=translated src=- shape=566721f7 vocab=22cc3147
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.thirdOpp_ne_next (k : Fin 4) (i : Fin 3) :
    thirdOpp k i ≠ opp k (finRotate 3 i) := by
  intro h
  have := opp_injective k h
  fin_cases i <;> contradiction

/--
@isnad1 id=or.2h3v.s7.421eacecfe93 from=translated src=- shape=1024fa8f vocab=bbe8dd6b
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.fin3_cycle_exhausts (i j : Fin 3) (hji : j ≠ i)
    (hjr : j ≠ finRotate 3 i) (t : Fin 3) :
    t = i ∨ t = finRotate 3 i ∨ t = j := by
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals fin_cases t <;> simp

/--
@isnad1 id=eq.1h2v.s5.fdcb9223945a from=translated src=- shape=0530115c vocab=1754a368
-/
theorem _root_.Tengoku.LeanEvalPlatonicClassification.three_incident_faces_meet_at_vertex (k : Fin 4) (x : E3)
    (hx : ∀ i : Fin 3, x ∈ tetraFace (opp k i)) : x = w k := by
  have hzero (a : Fin 4) (hak : a ≠ k) : tetraBasis.coord a x = 0 := by
    obtain ⟨i, hi⟩ := opp_complete k a hak
    rw [← hi]
    exact (mem_tetraFace_iff (opp k i) x).mp (hx i) |>.2
  have hk : tetraBasis.coord k x = 1 := by
    have hs := tetraBasis.sum_coord_apply_eq_one x
    rw [Fin.sum_univ_four] at hs
    fin_cases k
    · have h1 := hzero 1 (by decide)
      have h2 := hzero 2 (by decide)
      have h3 := hzero 3 (by decide)
      change tetraBasis.coord 0 x = 1
      linarith
    · have h0 := hzero 0 (by decide)
      have h2 := hzero 2 (by decide)
      have h3 := hzero 3 (by decide)
      change tetraBasis.coord 1 x = 1
      linarith
    · have h0 := hzero 0 (by decide)
      have h1 := hzero 1 (by decide)
      have h3 := hzero 3 (by decide)
      change tetraBasis.coord 2 x = 1
      linarith
    · have h0 := hzero 0 (by decide)
      have h1 := hzero 1 (by decide)
      have h2 := hzero 2 (by decide)
      change tetraBasis.coord 3 x = 1
      linarith
  apply tetraBasis.ext_elem
  intro a
  by_cases hak : a = k
  · subst a
    rw [hk, ← tetraBasis_apply k, tetraBasis.coord_apply]
    simp
  · rw [hzero a hak, ← tetraBasis_apply k, tetraBasis.coord_apply]
    simp [hak]

def _root_.Tengoku.LeanEvalPlatonicClassification.tetraCyclicData (k : Fin 4) :
    tetraedro.CyclicVertexData (w k) 3 where
  faccetta i := tetraFace (opp k i)
  isFacet i := tetraFace_isFacet (opp k i)
  mem_v i := vertex_mem_incident_face k i
  distinte := by
    intro i j hij
    exact opp_injective k (tetraFace_injective hij)
  complete := by
    intro F hF hwk
    obtain ⟨a, rfl⟩ := facet_classification hF
    have hak : a ≠ k := by
      exact ((vertex_mem_tetraFace_iff k a).1 hwk).symm
    obtain ⟨i, hi⟩ := opp_complete k a hak
    exact ⟨i, by rw [hi]⟩
  σ := rot k
  fissa_v := rot_fixed k
  preserva := rot_preserves_polytope k
  ruota i := by
    rw [rot_image_tetraFace, τ_opp]
  spigolo i := by
    refine ⟨w (thirdOpp k i), w_injective.ne (thirdOpp_ne_vertex k i), ?_, ?_⟩
    · exact (vertex_mem_tetraFace_iff _ _).2 (thirdOpp_ne_current k i)
    · exact (vertex_mem_tetraFace_iff _ _).2 (thirdOpp_ne_next k i)
  spigolo_due i j x hx hxne hxj := by
    by_cases hji : j = i
    · exact Or.inl hji
    by_cases hjr : j = finRotate 3 i
    · exact Or.inr hjr
    exfalso
    apply hxne
    apply three_incident_faces_meet_at_vertex k x
    intro t
    rcases fin3_cycle_exhausts i j hji hjr t with rfl | ht | ht
    · exact hx.1
    · rw [ht]
      exact hx.2
    · rw [ht]
      exact hxj

/-! ## Assemblaggio finale -/
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
