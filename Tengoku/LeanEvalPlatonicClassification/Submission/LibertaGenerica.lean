import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.SottoPolitopo
import Tengoku.LeanEvalPlatonicClassification.Submission.Diamante
import Tengoku.LeanEvalPlatonicClassification.Submission.ScalaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.DimStretta
import Tengoku.LeanEvalPlatonicClassification.Submission.Equivarianza
import Tengoku.LeanEvalPlatonicClassification.Submission.DiamanteRelativo
import Tengoku.LeanEvalPlatonicClassification.Submission.Muovi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una simmetria del politopo ne permuta l'insieme dei vertici.
@isnad1 id=eq.1h3v.s8.36e8d9a73b71 from=translated src=- shape=cc0bd38b vocab=90aecbb8
-/
theorem simmetria_permuta_vertici (P : ConvexPolytope n) {φ : Isom n}
    (hφ : P.isSymmetry φ) :
    (⇑φ) '' (P.vertices : Set (E n)) = (P.vertices : Set (E n)) := by
  rw [P.vertices_eq_extremePoints]
  change (⇑φ.toAffineEquiv) '' Set.extremePoints ℝ P.toSet =
    Set.extremePoints ℝ P.toSet
  rw [← extremePoints_image_affineEquiv φ.toAffineEquiv P.toSet]
  change Set.extremePoints ℝ ((⇑φ) '' P.toSet) =
    Set.extremePoints ℝ P.toSet
  rw [hφ]

open Classical in
/-- Su una faccia fissata, una simmetria permuta i vertici della faccia.
@isnad1 id=eq.2h4v.s9.1a47b17edba9 from=translated src=- shape=b282db75 vocab=7293bca5
-/
theorem simmetria_permuta_vertici_faccia (P : ConvexPolytope n)
    {φ : Isom n} (hφ : P.isSymmetry φ) {f : Set (E n)}
    (hfix : (⇑φ) '' f = f) :
    (⇑φ) '' ((P.vertices.filter (fun x => x ∈ f) : Finset (E n)) : Set (E n)) =
      ((P.vertices.filter (fun x => x ∈ f) : Finset (E n)) : Set (E n)) := by
  classical
  have hV := simmetria_permuta_vertici P hφ
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
    refine ⟨?_, ?_⟩
    · have : φ x ∈ (P.vertices : Set (E n)) := by
        rw [← hV]
        exact ⟨x, by exact_mod_cast hx.1, rfl⟩
      exact_mod_cast this
    · rw [← hfix]
      exact ⟨x, hx.2, rfl⟩
  · intro hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hy
    have hyV : y ∈ (⇑φ) '' (P.vertices : Set (E n)) := hV.symm ▸ hy.1
    obtain ⟨x, hxV, hxy⟩ := hyV
    have hyf : y ∈ (⇑φ) '' f := hfix.symm ▸ hy.2
    obtain ⟨x', hx'f, hx'y⟩ := hyf
    have hxx' : x = x' := φ.injective (hxy.trans hx'y.symm)
    subst x'
    refine ⟨x, ?_, hxy⟩
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨hxV, hx'f⟩

open Classical in
/-- Il centroide dei vertici di una faccia fissata è un punto fisso.
@isnad1 id=eq.3h4v.s10.26c7300f2789 from=translated src=- shape=387d21cc vocab=1420e856
-/
theorem centroide_di_faccia_fissato (P : ConvexPolytope n)
    {φ : Isom n} (hφ : P.isSymmetry φ) {f : Set (E n)}
    (hf : P.IsFace f) (hfix : (⇑φ) '' f = f) :
    φ (Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id) =
      Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id := by
  classical
  let s : Finset (E n) := P.vertices.filter (fun x => x ∈ f)
  have hs : s.Nonempty := (facePolytope P hf).vertices_nonempty
  have hw : ∑ i ∈ s, s.centroidWeights ℝ i = 1 :=
    s.sum_centroidWeights_eq_one_of_nonempty ℝ hs
  have hmap :
      φ (s.centroid ℝ id) = s.centroid ℝ (fun x => φ x) := by
    rw [Finset.centroid_def, Finset.centroid_def]
    exact s.map_affineCombination id (s.centroidWeights ℝ) hw
      φ.toAffineEquiv.toAffineMap
  rw [show P.vertices.filter (fun x => x ∈ f) = s from rfl]
  rw [hmap]
  apply Finset.centroid_eq_of_inj_on_of_image_eq ℝ s s
  · intro i _ j _ hij
    exact φ.injective hij
  · intro i _ j _ hij
    exact hij
  · simpa [s] using simmetria_permuta_vertici_faccia P hφ hfix

open Classical in
/-- Il centroide dei vertici di una faccia appartiene alla faccia.
@isnad1 id=mem.1h3v.s8.08647c8ca37c from=translated src=- shape=a9fc88e9 vocab=f10e2b7b
-/
theorem centroide_mem_faccia (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) :
    Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id ∈ f := by
  let s : Finset (E n) := P.vertices.filter (fun x => x ∈ f)
  have hs : s.Nonempty := (facePolytope P hf).vertices_nonempty
  change s.centroid ℝ id ∈ f
  rw [face_eq_hull_vertices P hf]
  exact Finset.centroid_mem_convexHull (R := ℝ) s hs

open Classical in
/-- Il centroide di una faccia non appartiene allo span affine di una
sottofaccia propria.
@isnad1 id=not.3h4v.s10.196605eb4388 from=translated src=- shape=82eeed2c vocab=7c76d025
-/
theorem centroide_fuori_da_span_sottofaccia (P : ConvexPolytope n)
    {g f : Set (E n)} (hg : P.IsFace g) (hf : P.IsFace f)
    (hgf : g ⊂ f) :
    Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id ∉
      affineSpan ℝ g := by
  let s : Finset (E n) := P.vertices.filter (fun x => x ∈ f)
  have hs : s.Nonempty := (facePolytope P hf).vertices_nonempty
  have hgconv : Convex ℝ g := hg.1.convex (convex_convexHull ℝ _)
  have hout : ∃ v ∈ s, v ∉ g := by
    by_contra hall
    push Not at hall
    have hfg : f ⊆ g := by
      rw [face_eq_hull_vertices P hf]
      apply convexHull_min
      · intro v hv
        exact hall v hv
      · exact hgconv
    exact hgf.2 hfg
  obtain ⟨v₀, hv₀s, hv₀g⟩ := hout
  obtain ⟨l, hlg, hchar⟩ := espositore_di_faccia P hg
  obtain ⟨p₀, hp₀g⟩ := hg.2
  let M : ℝ := l p₀
  have hp₀max : ∀ z ∈ P.toSet, l z ≤ M := by
    simpa [M] using (hlg p₀ hp₀g).2
  have hlgval : ∀ z ∈ g, l z = M := by
    intro z hz
    apply le_antisymm
    · exact hp₀max z (hlg z hz).1
    · exact (hlg z hz).2 p₀ (hlg p₀ hp₀g).1
  have hsP : ∀ v ∈ s, v ∈ P.toSet := by
    intro v hv
    have hvV : v ∈ P.vertices := (Finset.mem_filter.mp hv).1
    exact subset_convexHull ℝ _ (by exact_mod_cast hvV)
  have hlstrict : ∀ v ∈ s, v ∉ g → l v < M := by
    intro v hv hvnot
    have hvle := hp₀max v (hsP v hv)
    rcases lt_or_eq_of_le hvle with hlt | heq
    · exact hlt
    · exfalso
      apply hvnot
      apply hchar v (hsP v hv)
      intro z hz
      simpa [heq] using hp₀max z hz
  let c : E n := s.centroid ℝ id
  have hw : ∑ v ∈ s, s.centroidWeights ℝ v = 1 :=
    s.sum_centroidWeights_eq_one_of_nonempty ℝ hs
  have hlc : l c = ∑ v ∈ s, s.centroidWeights ℝ v * l v := by
    change l.toLinearMap.toAffineMap c = _
    rw [show c = s.centroid ℝ id from rfl, Finset.centroid_def]
    rw [s.map_affineCombination id (s.centroidWeights ℝ) hw
      l.toLinearMap.toAffineMap]
    rw [← Finset.centroid_def]
    rw [Finset.centroid_eq_centerMass s hs]
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw]
    simp
  have hwpos : ∀ v, 0 < s.centroidWeights ℝ v := by
    intro v
    simp only [Finset.centroidWeights_apply]
    positivity
  have hsumlt :
      (∑ v ∈ s, s.centroidWeights ℝ v * l v) <
        ∑ v ∈ s, s.centroidWeights ℝ v * M := by
    apply Finset.sum_lt_sum
    · intro v hv
      exact mul_le_mul_of_nonneg_left (hp₀max v (hsP v hv))
        (le_of_lt (hwpos v))
    · exact ⟨v₀, hv₀s, mul_lt_mul_of_pos_left (hlstrict v₀ hv₀s hv₀g)
        (hwpos v₀)⟩
  have hlc_lt : l c < M := by
    calc
      l c = ∑ v ∈ s, s.centroidWeights ℝ v * l v := hlc
      _ < ∑ v ∈ s, s.centroidWeights ℝ v * M := hsumlt
      _ = M := by rw [← Finset.sum_mul, hw, one_mul]
  intro hc
  let A : AffineSubspace ℝ (E n) :=
    AffineSubspace.mk' p₀ (LinearMap.ker l.toLinearMap)
  have hgA : g ⊆ (A : Set (E n)) := by
    intro z hz
    change z - p₀ ∈ LinearMap.ker l.toLinearMap
    rw [LinearMap.mem_ker]
    simp [hlgval z hz, M]
  have hcA : c ∈ A := (affineSpan_le.mpr hgA) hc
  rw [AffineSubspace.mem_mk', LinearMap.mem_ker] at hcA
  have hzero : l c - l p₀ = 0 := by simpa using hcA
  change l c < l p₀ at hlc_lt
  linarith

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
