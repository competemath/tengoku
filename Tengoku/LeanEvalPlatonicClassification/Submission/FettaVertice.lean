import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.FacciaArgmax
import Tengoku.LeanEvalPlatonicClassification.Submission.PerturbazioneFinita
import Tengoku.LeanEvalPlatonicClassification.Submission.BandieraCompagna

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
LA FETTA AL VERTICE — IL CORPO (21 lug 2026).

Primo modulo della figura al vertice: dato un politopo `Q`, un vertice `v`
e un funzionale `l` che separa strettamente `v` da tutti gli altri vertici
(`l w < c < l v`), la fetta `Q.toSet ∩ {l = c}` è l'hull convesso dei punti
`attra w` in cui i segmenti `[v, w]` attraversano il livello.

Il calcolo chiave (`fetta_eq_hull`) è puramente baricentrico: da
`x = a_v • v + ∑ a_w • w` al livello `c` si ricavano pesi
`μ_w = a_w (l v − l w)/(l v − c)` non negativi di somma uno con
`x = ∑ μ_w • attra w`.  Nessun interno relativo, nessun cono tangente.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- I dati di una fetta al vertice: il funzionale separatore `l`, il livello
`c` strettamente fra gli altri vertici e `v`, e almeno un altro vertice.-/
structure DatiFetta (Q : ConvexPolytope n) (v : E n) where
  l : E n →L[ℝ] ℝ
  c : ℝ
  hv : v ∈ Q.vertices
  hvc : c < l v
  hsep : ∀ w ∈ Q.vertices, w ≠ v → l w < c
  hW : (Q.vertices.erase v).Nonempty

namespace DatiFetta

variable {Q : ConvexPolytope n} {v : E n} (D : DatiFetta Q v)

/-- Il punto in cui il segmento `[v, w]` attraversa il livello `l = c`.-/
def attra (w : E n) : E n :=
  v + ((D.l v - D.c) / (D.l v - D.l w)) • (w - v)

/--
@isnad1 id=lt.1h5v.s8.6f64b39e8061 from=translated src=- shape=2b295d24 vocab=337a028b
-/
theorem sep_of_mem_erase {w : E n} (hw : w ∈ Q.vertices.erase v) :
    D.l w < D.c :=
  D.hsep w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)

/--
@isnad1 id=lt.0h4v.s8.9d15e67d13c5 from=translated src=- shape=63f59460 vocab=d7056e34
-/
theorem numpos : 0 < D.l v - D.c := by linarith [D.hvc]

/--
@isnad1 id=lt.1h5v.s9.e29f04679101 from=translated src=- shape=4c6b0b0c vocab=d7056e34
-/
theorem denpos {w : E n} (hwc : D.l w < D.c) : 0 < D.l v - D.l w := by
  linarith [D.hvc]

/--
@isnad1 id=lt.1h5v.s10.8c9e6eb1498f from=translated src=- shape=978c50f2 vocab=3be871da
-/
theorem tau_pos {w : E n} (hwc : D.l w < D.c) :
    0 < (D.l v - D.c) / (D.l v - D.l w) :=
  div_pos D.numpos (D.denpos hwc)

/--
@isnad1 id=lt.1h5v.s10.7cfcf978fe25 from=translated src=- shape=81f905e2 vocab=3be871da
-/
theorem tau_lt_one {w : E n} (hwc : D.l w < D.c) :
    (D.l v - D.c) / (D.l v - D.l w) < 1 := by
  rw [div_lt_one (D.denpos hwc)]
  linarith

/-- La differenza radiale dell'attraversamento.
@isnad1 id=eq.0h5v.s10.2f2bb442250d from=translated src=- shape=a3a9630f vocab=ab274d00
-/
theorem attra_sub (w : E n) :
    D.attra w - v = ((D.l v - D.c) / (D.l v - D.l w)) • (w - v) := by
  rw [attra, add_sub_cancel_left]

/-- L'attraversamento sta al livello `c`.
@isnad1 id=eq.1h5v.s9.3dab35e05c83 from=translated src=- shape=d0c45375 vocab=6f65e341
-/
theorem attra_level {w : E n} (hwc : D.l w < D.c) :
    D.l (D.attra w) = D.c := by
  have hden : D.l v - D.l w ≠ 0 := ne_of_gt (D.denpos hwc)
  rw [attra]
  simp only [map_add, map_smul, map_sub, smul_eq_mul]
  have hcancel : (D.l v - D.c) / (D.l v - D.l w) * (D.l v - D.l w)
      = D.l v - D.c := div_mul_cancel₀ _ hden
  nlinarith [hcancel]

/-- L'attraversamento sta sul segmento `[v, w]`.
@isnad1 id=mem.1h5v.s8.b6d261492793 from=translated src=- shape=1345c327 vocab=e81ec307
-/
theorem attra_mem_segment {w : E n} (hwc : D.l w < D.c) :
    D.attra w ∈ segment ℝ v w := by
  refine ⟨1 - (D.l v - D.c) / (D.l v - D.l w),
    (D.l v - D.c) / (D.l v - D.l w),
    by linarith [D.tau_lt_one hwc], le_of_lt (D.tau_pos hwc), by ring, ?_⟩
  rw [attra]
  match_scalars <;> ring

/-- L'attraversamento è distinto dal vertice.
@isnad1 id=ne.1h5v.s8.0c7e68304de6 from=translated src=- shape=c1b342d8 vocab=6f65e341
-/
theorem attra_ne {w : E n} (hwc : D.l w < D.c) : D.attra w ≠ v := by
  intro h
  have := D.attra_level hwc
  rw [h] at this
  linarith [D.hvc]

/-- L'attraversamento appartiene al corpo del politopo.
@isnad1 id=mem.2h5v.s8.1dc8eabb3eff from=translated src=- shape=8db0164f vocab=5d8a6183
-/
theorem attra_mem_toSet {w : E n} (hwV : w ∈ Q.vertices)
    (hwc : D.l w < D.c) : D.attra w ∈ Q.toSet := by
  have hvT : v ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast D.hv)
  have hwT : w ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast hwV)
  exact (convex_convexHull ℝ _).segment_subset hvT hwT
    (D.attra_mem_segment hwc)

/-- I generatori finiti della fetta: gli attraversamenti degli altri vertici.-/
def gen : Finset (E n) := (Q.vertices.erase v).image D.attra

/--
@isnad1 id=nonempty.0h4v.s4.b45a3173a00f from=translated src=- shape=46b66405 vocab=4ed8d4d5
-/
theorem gen_nonempty : D.gen.Nonempty := D.hW.image D.attra

/--
@isnad1 id=mem.1h5v.s7.4b464cc22ceb from=translated src=- shape=a87faa80 vocab=8e4a1618
-/
theorem mem_gen_of_mem_erase {w : E n} (hw : w ∈ Q.vertices.erase v) :
    D.attra w ∈ D.gen := Finset.mem_image_of_mem D.attra hw

/-- **LA FETTA È L'HULL DEGLI ATTRAVERSAMENTI.**
@isnad1 id=eq.0h4v.s8.26114ae330c9 from=translated src=- shape=3b5ab6b0 vocab=9cf7a70a
-/
theorem fetta_eq_hull :
    Q.toSet ∩ {x | D.l x = D.c} = convexHull ℝ (D.gen : Set (E n)) := by
  classical
  set W : Finset (E n) := Q.vertices.erase v with hWdef
  have hvins : Q.vertices = insert v W := (Finset.insert_erase D.hv).symm
  have hvnotW : v ∉ W := Finset.notMem_erase v Q.vertices
  apply Set.Subset.antisymm
  · rintro x ⟨hxT, hxc⟩
    have hxc' : D.l x = D.c := hxc
    have hxT' : x ∈ convexHull ℝ ((Q.vertices : Finset (E n)) : Set (E n)) :=
      hxT
    rw [Finset.convexHull_eq] at hxT'
    obtain ⟨a, ha0, ha1, hax⟩ := hxT'
    have hxrep : x = ∑ u ∈ Q.vertices, a u • u := by
      rw [← hax, Finset.centerMass_eq_of_sum_1 _ _ ha1]
      rfl
    -- livello: ∑ a u * l u = c
    have hlev : ∑ u ∈ Q.vertices, a u * D.l u = D.c := by
      have hmap := congrArg D.l hxrep
      rw [map_sum] at hmap
      simp only [map_smul, smul_eq_mul] at hmap
      exact hmap.symm.trans hxc'
    -- separazione della somma
    have ha1' : a v + ∑ w ∈ W, a w = 1 := by
      rw [hvins, Finset.sum_insert hvnotW] at ha1
      exact ha1
    have hlev' : a v * D.l v + ∑ w ∈ W, a w * D.l w = D.c := by
      rw [hvins, Finset.sum_insert hvnotW] at hlev
      exact hlev
    have hxrep' : x = a v • v + ∑ w ∈ W, a w • w := by
      rw [hvins, Finset.sum_insert hvnotW] at hxrep
      exact hxrep
    -- i pesi della fetta
    set μ : E n → ℝ := fun w => a w * (D.l v - D.l w) / (D.l v - D.c)
      with hμdef
    have hμ0 : ∀ w ∈ W, 0 ≤ μ w := by
      intro w hw
      exact div_nonneg
        (mul_nonneg (ha0 w (Finset.mem_of_mem_erase hw))
          (le_of_lt (D.denpos (D.sep_of_mem_erase hw))))
        (le_of_lt D.numpos)
    have hnum : ∑ w ∈ W, a w * (D.l v - D.l w) = D.l v - D.c := by
      have hexp : ∀ w ∈ W, a w * (D.l v - D.l w)
          = a w * D.l v - a w * D.l w := fun w _ => mul_sub _ _ _
      rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib,
        ← Finset.sum_mul]
      have h1 : ∑ w ∈ W, a w = 1 - a v := by linarith
      have h2 : ∑ w ∈ W, a w * D.l w = D.c - a v * D.l v := by linarith
      rw [h1, h2]
      ring
    have hμ1 : ∑ w ∈ W, μ w = 1 := by
      have hstep : ∑ w ∈ W, μ w
          = (∑ w ∈ W, a w * (D.l v - D.l w)) / (D.l v - D.c) := by
        rw [Finset.sum_div]
      rw [hstep, hnum, div_self (ne_of_gt D.numpos)]
    -- x è combinazione dei tagli
    have hterm : ∀ w ∈ W, μ w • D.attra w = μ w • v + a w • (w - v) := by
      intro w hw
      have hden : D.l v - D.l w ≠ 0 :=
        ne_of_gt (D.denpos (D.sep_of_mem_erase hw))
      have hd : D.l v - D.c ≠ 0 := ne_of_gt D.numpos
      have hcoef : μ w * ((D.l v - D.c) / (D.l v - D.l w)) = a w := by
        rw [hμdef]
        field_simp
      rw [attra, smul_add, smul_smul, hcoef]
    have hx2 : x = ∑ w ∈ W, μ w • D.attra w := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        ← Finset.sum_smul, hμ1, one_smul]
      have hsub : ∀ w ∈ W, a w • (w - v) = a w • w - a w • v :=
        fun w _ => smul_sub _ _ _
      rw [Finset.sum_congr rfl hsub, Finset.sum_sub_distrib,
        ← Finset.sum_smul]
      have h1 : ∑ w ∈ W, a w = 1 - a v := by linarith
      rw [h1, hxrep']
      rw [sub_smul, one_smul]
      abel
    have hmem := Finset.centerMass_mem_convexHull W (w := μ) hμ0
      (by rw [hμ1]; norm_num)
      (z := D.attra)
      (fun w hw => Finset.mem_coe.mpr (D.mem_gen_of_mem_erase hw))
    rw [Finset.centerMass_eq_of_sum_1 _ _ hμ1] at hmem
    rw [hx2]
    exact hmem
  · apply convexHull_min
    · intro y hy
      have hy' : y ∈ D.gen := hy
      simp only [gen, Finset.mem_image] at hy'
      obtain ⟨w, hw', rfl⟩ := hy'
      refine ⟨D.attra_mem_toSet (Finset.mem_of_mem_erase hw')
        (D.sep_of_mem_erase hw'), ?_⟩
      exact D.attra_level (D.sep_of_mem_erase hw')
    · exact (convex_convexHull ℝ _).inter
        (convex_hyperplane (LinearMap.isLinear D.l.toLinearMap) D.c)

/-! ## La fetta come politopo -/

/-- Krein–Milman finito: l'hull dei punti estremi dell'hull dei generatori
è l'hull dei generatori.  (L'hull finito è compatto e chiuso.)
@isnad1 id=eq.0h4v.s9.5e8400312cf0 from=translated src=- shape=40a1495e vocab=35cf7943
-/
theorem hull_ext :
    convexHull ℝ ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ)
      = convexHull ℝ (D.gen : Set (E n)) := by
  have hcomp : IsCompact (convexHull ℝ (D.gen : Set (E n))) :=
    D.gen.finite_toSet.isCompact_convexHull ℝ
  have hconv : Convex ℝ (convexHull ℝ (D.gen : Set (E n))) :=
    convex_convexHull ℝ _
  have hKM := closure_convexHull_extremePoints hcomp hconv
  have hfin : ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ).Finite :=
    D.gen.finite_toSet.subset extremePoints_convexHull_subset
  calc convexHull ℝ ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ)
      = closure (convexHull ℝ
          ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ)) :=
        (hfin.isClosed_convexHull ℝ).closure_eq.symm
    _ = convexHull ℝ (D.gen : Set (E n)) := hKM

/-- I punti estremi della fetta formano un insieme finito.
@isnad1 id=finite.0h4v.s8.abd0f1632b43 from=translated src=- shape=28042972 vocab=80b281dc
-/
theorem ext_finite :
    ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ).Finite :=
  D.gen.finite_toSet.subset extremePoints_convexHull_subset

/-- I punti estremi della fetta sono non vuoti.
@isnad1 id=nonempty.0h4v.s8.a55309e4bd2b from=translated src=- shape=28042972 vocab=d94166c5
-/
theorem ext_nonempty :
    ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have h0 := D.hull_ext
  rw [hempty, convexHull_empty] at h0
  obtain ⟨y, hy⟩ := D.gen_nonempty
  have hymem : y ∈ convexHull ℝ (D.gen : Set (E n)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr hy)
  rw [← h0] at hymem
  exact hymem

/-- **LA FETTA COME POLITOPO**: i vertici sono i punti estremi dell'hull
degli attraversamenti.-/
def politopo : ConvexPolytope n where
  vertices := D.ext_finite.toFinset
  vertices_nonempty := by
    obtain ⟨x, hx⟩ := D.ext_nonempty
    exact ⟨x, (Set.Finite.mem_toFinset _).mpr hx⟩
  vertices_eq_extremePoints := by
    rw [Set.Finite.coe_toFinset, D.hull_ext]

/-- Il corpo del politopo-fetta è esattamente la fetta.
@isnad1 id=eq.0h4v.s8.0c376f7fc1f7 from=translated src=- shape=0af0de4b vocab=73a888b8
-/
theorem politopo_toSet :
    D.politopo.toSet = Q.toSet ∩ {x | D.l x = D.c} := by
  have h1 : D.politopo.toSet = convexHull ℝ
      ((convexHull ℝ (D.gen : Set (E n))).extremePoints ℝ) := by
    show convexHull ℝ ((D.ext_finite.toFinset : Finset (E n)) : Set (E n)) = _
    rw [Set.Finite.coe_toFinset]
  rw [h1, D.hull_ext, ← D.fetta_eq_hull]

/-! ## Il trasferimento delle facce -/

/-- Una faccia di dimensione positiva che contiene `v` contiene un altro
vertice.
@isnad1 id=ex.3h4v.s7.f65f1dc3e729 from=translated src=- shape=7c4f5b37 vocab=dd00a384
-/
theorem esiste_vertice_altro {F : Set (E n)} (hF : Q.IsFace F) (hvF : v ∈ F)
    (hdF : 1 ≤ faceDim F) : ∃ w ∈ Q.vertices.erase v, w ∈ F := by
  classical
  by_contra hcon
  push Not at hcon
  have hfe := face_eq_hull_vertices Q hF
  have hsub : ((Q.vertices.filter (· ∈ F) : Finset (E n)) : Set (E n))
      ⊆ ({v} : Set (E n)) := by
    intro u hu
    have hu' : u ∈ Q.vertices.filter (· ∈ F) := by exact_mod_cast hu
    have huV : u ∈ Q.vertices := (Finset.mem_filter.mp hu').1
    have huF : u ∈ F := (Finset.mem_filter.mp hu').2
    by_contra huv
    have huv' : u ≠ v := by simpa using huv
    exact hcon u (Finset.mem_erase.mpr ⟨huv', huV⟩) huF
  have hFsub : F ⊆ ({v} : Set (E n)) := by
    rw [hfe]
    exact convexHull_min hsub (convex_singleton v)
  have hFeq : F = ({v} : Set (E n)) :=
    Set.Subset.antisymm hFsub (Set.singleton_subset_iff.mpr hvF)
  rw [hFeq, faceDim_singleton] at hdF
  omega

/-- **AVANTI**: la fetta di una faccia dello star è una faccia del
politopo-fetta, esposta dallo stesso funzionale.
@isnad1 id=isface.3h5v.s8.c30888c00a49 from=translated src=- shape=9df1b7d0 vocab=ee0acd59
-/
theorem faccia_fetta {F : Set (E n)} (hF : Q.IsFace F) (hvF : v ∈ F)
    (hdF : 1 ≤ faceDim F) :
    D.politopo.IsFace (F ∩ {x | D.l x = D.c}) := by
  obtain ⟨w₀, hw₀W, hw₀F⟩ := esiste_vertice_altro hF hvF hdF
  have hw₀c := D.sep_of_mem_erase hw₀W
  have hattra₀F : D.attra w₀ ∈ F :=
    (hF.1.convex (convex_convexHull ℝ _)).segment_subset hvF hw₀F
      (D.attra_mem_segment hw₀c)
  have hne : (F ∩ {x | D.l x = D.c}).Nonempty :=
    ⟨D.attra w₀, hattra₀F, D.attra_level hw₀c⟩
  refine ⟨?_, hne⟩
  intro _
  obtain ⟨f, hf⟩ := hF.1 hF.2
  refine ⟨f, ?_⟩
  rw [D.politopo_toSet]
  ext x
  constructor
  · rintro ⟨hxF, hxc⟩
    have hx' := hxF
    rw [hf] at hx'
    exact ⟨⟨hx'.1, hxc⟩, fun y hy => hx'.2 y hy.1⟩
  · rintro ⟨⟨hxT, hxc⟩, hxmax⟩
    have hatt' := hattra₀F
    rw [hf] at hatt'
    have h1 : f (D.attra w₀) ≤ f x :=
      hxmax _ ⟨hatt'.1, D.attra_level hw₀c⟩
    refine ⟨?_, hxc⟩
    rw [hf]
    exact ⟨hxT, fun y hy => le_trans (hatt'.2 y hy) h1⟩

/-- **MONOTONIA**: se la fetta di `F₁` sta nella fetta di `F₂`, allora
`F₁ ⊆ F₂`.  Il punto di attraversamento è interno al segmento `[v, w]`, e
un funzionale massimo lì è massimo anche in `w`.
@isnad1 id=le.5h6v.s9.f26ff326a9e5 from=translated src=- shape=f4587c8f vocab=62fa00dc
-/
theorem fetta_mono {F₁ F₂ : Set (E n)} (hF₁ : Q.IsFace F₁) (hvF₁ : v ∈ F₁)
    (hF₂ : Q.IsFace F₂) (hvF₂ : v ∈ F₂)
    (hsub : F₁ ∩ {x | D.l x = D.c} ⊆ F₂ ∩ {x | D.l x = D.c}) :
    F₁ ⊆ F₂ := by
  classical
  obtain ⟨f₂, hf₂⟩ := hF₂.1 hF₂.2
  have hv₂ := hvF₂
  rw [hf₂] at hv₂
  have hfe := face_eq_hull_vertices Q hF₁
  rw [hfe]
  apply convexHull_min ?_ (hF₂.1.convex (convex_convexHull ℝ _))
  intro u hu
  have hu' : u ∈ Q.vertices.filter (· ∈ F₁) := by exact_mod_cast hu
  have huV : u ∈ Q.vertices := (Finset.mem_filter.mp hu').1
  have huF₁ : u ∈ F₁ := (Finset.mem_filter.mp hu').2
  by_cases huv : u = v
  · subst huv
    exact hvF₂
  · have huW : u ∈ Q.vertices.erase v := Finset.mem_erase.mpr ⟨huv, huV⟩
    have huc : D.l u < D.c := D.sep_of_mem_erase huW
    have hattra₁ : D.attra u ∈ F₁ :=
      (hF₁.1.convex (convex_convexHull ℝ _)).segment_subset hvF₁ huF₁
        (D.attra_mem_segment huc)
    have hattra₂ : D.attra u ∈ F₂ :=
      (hsub ⟨hattra₁, D.attra_level huc⟩).1
    have hatt := hattra₂
    rw [hf₂] at hatt
    have heq : f₂ (D.attra u) = f₂ v :=
      le_antisymm (hv₂.2 _ hatt.1) (hatt.2 v hv₂.1)
    have hexp : f₂ (D.attra u)
        = f₂ v + ((D.l v - D.c) / (D.l v - D.l u)) * (f₂ u - f₂ v) := by
      rw [attra]
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    have hzero : ((D.l v - D.c) / (D.l v - D.l u)) * (f₂ u - f₂ v) = 0 := by
      linarith [hexp, heq]
    have hf₂u : f₂ u = f₂ v := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (ne_of_gt (D.tau_pos huc))
      · linarith
    rw [hf₂]
    have huT : u ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast huV)
    exact ⟨huT, fun y hy => (hv₂.2 y hy).trans_eq hf₂u.symm⟩

/-- **INDIETRO**: ogni faccia del politopo-fetta è la fetta di una faccia
dello star.  Il funzionale è `g + t⋆ · l` con `t⋆ = (M − g v)/(l v − c)`:
sui vertici `w` con `p(w)` argmax il rapporto incrementale vale
esattamente `t⋆`, sugli altri è strettamente minore.
@isnad1 id=ex.1h5v.s8.de0db37a0969 from=translated src=- shape=78e4dd5a vocab=ee0acd59
-/
theorem faccia_dalla_fetta {G : Set (E n)} (hG : D.politopo.IsFace G) :
    ∃ F : Set (E n), Q.IsFace F ∧ v ∈ F ∧ 1 ≤ faceDim F ∧
      F ∩ {x | D.l x = D.c} = G := by
  obtain ⟨g, hg⟩ := hG.1 hG.2
  rw [D.politopo_toSet] at hg
  obtain ⟨x₀, hx₀⟩ := hG.2
  have hx₀' := hx₀
  rw [hg] at hx₀'
  set M : ℝ := g x₀ with hM
  set t : ℝ := (M - g v) / (D.l v - D.c) with ht
  set f : E n →L[ℝ] ℝ := g + t • D.l with hfdef
  have hfapp : ∀ x, f x = g x + t * D.l x := by
    intro x
    simp [hfdef]
  have hvT : v ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast D.hv)
  -- il fatto chiave sui vertici
  have hkey : ∀ w ∈ Q.vertices.erase v,
      f v - f w = ((D.l v - D.l w) / (D.l v - D.c)) * (M - g (D.attra w)) := by
    intro w hw
    have hwc := D.sep_of_mem_erase hw
    have hden : D.l v - D.l w ≠ 0 := ne_of_gt (D.denpos hwc)
    have hd : D.l v - D.c ≠ 0 := ne_of_gt D.numpos
    have hgatt : g (D.attra w)
        = g v + ((D.l v - D.c) / (D.l v - D.l w)) * (g w - g v) := by
      rw [attra]
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    rw [hfapp, hfapp, hgatt, ht]
    field_simp
    ring
  -- massimo in v sui vertici
  have hfvert : ∀ u ∈ (Q.vertices : Set (E n)), f u ≤ f v := by
    intro u huS
    have huV : u ∈ Q.vertices := by exact_mod_cast huS
    by_cases huv : u = v
    · subst huv
      exact le_refl _
    · have huW : u ∈ Q.vertices.erase v := Finset.mem_erase.mpr ⟨huv, huV⟩
      have hwc := D.sep_of_mem_erase huW
      have hattmem : D.attra u ∈ Q.toSet ∩ {x | D.l x = D.c} :=
        ⟨D.attra_mem_toSet (Finset.mem_of_mem_erase huW) hwc,
          D.attra_level hwc⟩
      have hle : g (D.attra u) ≤ M := hx₀'.2 _ hattmem
      have hfrac : 0 ≤ (D.l v - D.l u) / (D.l v - D.c) :=
        le_of_lt (div_pos (D.denpos hwc) D.numpos)
      have hk := hkey u huW
      nlinarith [mul_nonneg hfrac (by linarith : (0:ℝ) ≤ M - g (D.attra u))]
  have hfmax : ∀ y ∈ Q.toSet, f y ≤ f v := le_su_toSet Q f hfvert
  set Fs : Set (E n) := {x ∈ Q.toSet | ∀ y ∈ Q.toSet, f y ≤ f x} with hFs
  have hvF : v ∈ Fs := ⟨hvT, hfmax⟩
  have hFface : Q.IsFace Fs := ⟨fun _ => ⟨f, rfl⟩, ⟨v, hvF⟩⟩
  -- t·(l v − c) = M − g v
  have ht' : t * D.l v - t * D.c = M - g v := by
    rw [← mul_sub]
    exact div_mul_cancel₀ _ (ne_of_gt D.numpos)
  have hfv : f v = M + t * D.c := by
    have := hfapp v
    linarith
  -- la fetta di Fs è G
  have hslice : Fs ∩ {x | D.l x = D.c} = G := by
    ext x
    constructor
    · rintro ⟨⟨hxT, hxmax⟩, hxc⟩
      rw [hg]
      refine ⟨⟨hxT, hxc⟩, ?_⟩
      intro y hy
      have h1 := hxmax y hy.1
      rw [hfapp, hfapp] at h1
      have hyc : D.l y = D.c := hy.2
      have hxc' : D.l x = D.c := hxc
      rw [hyc, hxc'] at h1
      linarith
    · intro hxG
      have hx' := hxG
      rw [hg] at hx'
      have hgx : g x = M :=
        le_antisymm (hx₀'.2 x hx'.1) (hx'.2 x₀ hx₀'.1)
      have hxc : D.l x = D.c := hx'.1.2
      have hfx : f x = M + t * D.c := by
        rw [hfapp, hgx, hxc]
      refine ⟨⟨hx'.1.1, ?_⟩, hxc⟩
      intro y hy
      calc f y ≤ f v := hfmax y hy
        _ = f x := by rw [hfv, hfx]
    -- fine hslice
  have hx₀F : x₀ ∈ Fs := by
    have hx₀G : x₀ ∈ G := hx₀
    rw [← hslice] at hx₀G
    exact hx₀G.1
  have hx₀v : x₀ ≠ v := by
    intro h
    have hc := hx₀'.1.2
    rw [h] at hc
    have : D.l v = D.c := hc
    linarith [D.hvc]
  have hdim : 1 ≤ faceDim Fs := by
    have hmem : x₀ - v ∈ vectorSpan ℝ Fs := vsub_mem_vectorSpan ℝ hx₀F hvF
    have hne0 : x₀ - v ≠ 0 := sub_ne_zero.mpr hx₀v
    have hle : Submodule.span ℝ {x₀ - v} ≤ vectorSpan ℝ Fs := by
      rw [Submodule.span_le]
      exact Set.singleton_subset_iff.mpr hmem
    have h2 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hne0] at h2
    exact h2
  exact ⟨Fs, hFface, hvF, hdim, hslice⟩

/-- **LO SHIFT DIMENSIONALE**: la fetta di una faccia dello star ha
dimensione esattamente una in meno.  `vectorSpan F` si spezza come
`vectorSpan (F ∩ H) ⊔ ℝ·(p(w₀) − v)`: i due addendi si intersecano solo
nell'origine perché il primo sta nel nucleo di `l` e il secondo no.
@isnad1 id=eq.3h5v.s8.5505eb43530a from=translated src=- shape=3045664f vocab=4534d8ee
-/
theorem fetta_faceDim {F : Set (E n)} (hF : Q.IsFace F) (hvF : v ∈ F)
    (hdF : 1 ≤ faceDim F) :
    faceDim (F ∩ {x | D.l x = D.c}) + 1 = faceDim F := by
  classical
  obtain ⟨w₀, hw₀W, hw₀F⟩ := esiste_vertice_altro hF hvF hdF
  have hw₀c := D.sep_of_mem_erase hw₀W
  have hFconv : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
  have hatt₀F : D.attra w₀ ∈ F :=
    hFconv.segment_subset hvF hw₀F (D.attra_mem_segment hw₀c)
  have hatt₀H : D.l (D.attra w₀) = D.c := D.attra_level hw₀c
  set U : Submodule ℝ (E n) := vectorSpan ℝ F with hU
  set U' : Submodule ℝ (E n) :=
    vectorSpan ℝ (F ∩ {x | D.l x = D.c}) with hU'
  set L : Submodule ℝ (E n) := Submodule.span ℝ {D.attra w₀ - v} with hL
  set K : Submodule ℝ (E n) := LinearMap.ker D.l.toLinearMap with hK
  -- inclusioni elementari
  have h1 : U' ≤ U := vectorSpan_mono ℝ Set.inter_subset_left
  have h2 : L ≤ U := by
    rw [hL, Submodule.span_le, Set.singleton_subset_iff]
    exact vsub_mem_vectorSpan ℝ hatt₀F hvF
  -- la fetta vive nel nucleo di l
  have h4 : U' ≤ K := by
    rw [hU']
    have hbase : D.attra w₀ ∈ F ∩ {x | D.l x = D.c} := ⟨hatt₀F, hatt₀H⟩
    rw [vectorSpan_eq_span_vsub_set_right ℝ hbase, Submodule.span_le]
    rintro z ⟨x, hx, rfl⟩
    have hxc : D.l x = D.c := hx.2
    rw [hK, SetLike.mem_coe, LinearMap.mem_ker]
    show D.l (x - D.attra w₀) = 0
    rw [map_sub, hxc, hatt₀H, sub_self]
  -- la retta trasversale incontra il nucleo solo nell'origine
  have h5 : L ⊓ K = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxL, hxK⟩
    rw [hL] at hxL
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxL
    have hxK' : D.l.toLinearMap (a • (D.attra w₀ - v)) = 0 := hxK
    have hval : D.l.toLinearMap (a • (D.attra w₀ - v))
        = a * (D.c - D.l v) := by
      rw [map_smul, smul_eq_mul]
      show a * D.l (D.attra w₀ - v) = _
      rw [map_sub, hatt₀H]
    rw [hval] at hxK'
    have hane : D.c - D.l v ≠ 0 := by linarith [D.hvc]
    have ha : a = 0 := by
      rcases mul_eq_zero.mp hxK' with h | h
      · exact h
      · exact absurd h hane
    rw [ha, zero_smul]
  -- lo span della faccia è generato dalla fetta più la trasversale
  have h3 : U ≤ U' ⊔ L := by
    have hfe := face_eq_hull_vertices Q hF
    have hUv : U = vectorSpan ℝ
        ((Q.vertices.filter (· ∈ F) : Finset (E n)) : Set (E n)) := by
      rw [hU]
      conv_lhs => rw [hfe]
      rw [← direction_affineSpan, affineSpan_convexHull,
        direction_affineSpan]
    have hvmem : v ∈
        ((Q.vertices.filter (· ∈ F) : Finset (E n)) : Set (E n)) := by
      exact_mod_cast Finset.mem_filter.mpr ⟨D.hv, hvF⟩
    rw [hUv, vectorSpan_eq_span_vsub_set_right ℝ hvmem, Submodule.span_le]
    rintro z ⟨u, hu, rfl⟩
    have hu' : u ∈ Q.vertices.filter (· ∈ F) := by exact_mod_cast hu
    have huV : u ∈ Q.vertices := (Finset.mem_filter.mp hu').1
    have huF : u ∈ F := (Finset.mem_filter.mp hu').2
    show u - v ∈ (U' ⊔ L : Submodule ℝ (E n))
    by_cases huv : u = v
    · subst huv
      simp
    · have huW : u ∈ Q.vertices.erase v := Finset.mem_erase.mpr ⟨huv, huV⟩
      have huc := D.sep_of_mem_erase huW
      have hattuF : D.attra u ∈ F :=
        hFconv.segment_subset hvF huF (D.attra_mem_segment huc)
      have hd1 : D.attra u - D.attra w₀ ∈ U' := by
        rw [hU']
        exact vsub_mem_vectorSpan ℝ ⟨hattuF, D.attra_level huc⟩
          ⟨hatt₀F, hatt₀H⟩
      have hd2 : D.attra w₀ - v ∈ L := by
        rw [hL]
        exact Submodule.mem_span_singleton_self _
      have hsum : D.attra u - v ∈ (U' ⊔ L : Submodule ℝ (E n)) := by
        have hsplit : D.attra u - v
            = (D.attra u - D.attra w₀) + (D.attra w₀ - v) := by abel
        rw [hsplit]
        exact Submodule.add_mem _ (Submodule.mem_sup_left hd1)
          (Submodule.mem_sup_right hd2)
      have hscal : u - v
          = ((D.l v - D.l u) / (D.l v - D.c)) • (D.attra u - v) := by
        rw [D.attra_sub u, smul_smul]
        have hden : D.l v - D.l u ≠ 0 := ne_of_gt (D.denpos huc)
        have hd : D.l v - D.c ≠ 0 := ne_of_gt D.numpos
        rw [show (D.l v - D.l u) / (D.l v - D.c)
            * ((D.l v - D.c) / (D.l v - D.l u)) = 1 by field_simp, one_smul]
      rw [hscal]
      exact Submodule.smul_mem _ _ hsum
  -- l'assemblaggio dei ranghi
  have hsup : U' ⊔ L = U := le_antisymm (sup_le h1 h2) h3
  have hinf : U' ⊓ L = ⊥ := by
    rw [← le_bot_iff, ← h5]
    exact le_inf inf_le_right (inf_le_left.trans h4)
  have hrk := Submodule.finrank_sup_add_finrank_inf_eq U' L
  rw [hsup, hinf] at hrk
  have hL1 : Module.finrank ℝ L = 1 := by
    rw [hL]
    apply finrank_span_singleton
    intro h0
    have hattv : D.attra w₀ = v := by
      have := sub_eq_zero.mp h0
      exact this
    rw [hattv] at hatt₀H
    linarith [D.hvc]
  have hbot : Module.finrank ℝ (⊥ : Submodule ℝ (E n)) = 0 := finrank_bot ℝ _
  show Module.finrank ℝ U' + 1 = Module.finrank ℝ U
  omega

end DatiFetta

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
