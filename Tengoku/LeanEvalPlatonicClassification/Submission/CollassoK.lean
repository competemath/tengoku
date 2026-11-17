import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.MassimoConsecutivo
import Tengoku.LeanEvalPlatonicClassification.Submission.ResiduoGeometrico
import Tengoku.LeanEvalPlatonicClassification.Submission.RotazioneElementareDue
import Tengoku.LeanEvalPlatonicClassification.Submission.OrdineTreBordi
import Tengoku.LeanEvalPlatonicClassification.Submission.FormulaRiflessione
import Tengoku.LeanEvalPlatonicClassification.Submission.Iperpiano

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-! ## Centroidi e passo combinatorio -/

/-- Centroide dei vertici del politopo appartenenti a una faccia.-/
noncomputable def centroideFaccia (P : ConvexPolytope n) (f : Set (E n)) : E n := by
  classical
  exact Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ f)) id

/-- Una simmetria manda il centroide di una faccia nel centroide della
faccia immagine.  È la versione non stazionaria di
`centroide_di_faccia_fissato`.
@isnad1 id=eq.4h5v.s9.e49a516857f5 from=translated src=- shape=1d053215 vocab=4d8b38ee
-/
theorem centroide_di_faccia_mandato (P : ConvexPolytope n)
    {φ : Isom n} (hφ : P.isSymmetry φ) {f g : Set (E n)}
    (hf : P.IsFace f) (hg : P.IsFace g) (hfg : (⇑φ) '' f = g) :
    φ (centroideFaccia P f) = centroideFaccia P g := by
  classical
  let s : Finset (E n) := P.vertices.filter (fun x => x ∈ f)
  let t : Finset (E n) := P.vertices.filter (fun x => x ∈ g)
  have hs : s.Nonempty := (facePolytope P hf).vertices_nonempty
  have hw : ∑ x ∈ s, s.centroidWeights ℝ x = 1 :=
    s.sum_centroidWeights_eq_one_of_nonempty ℝ hs
  have hmap : φ (s.centroid ℝ id) = s.centroid ℝ (fun x => φ x) := by
    rw [Finset.centroid_def, Finset.centroid_def]
    exact s.map_affineCombination id (s.centroidWeights ℝ) hw
      φ.toAffineEquiv.toAffineMap
  have himage : (⇑φ) '' (s : Set (E n)) = (t : Set (E n)) := by
    have hvertices := simmetria_permuta_vertici P hφ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [s, t, Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
      constructor
      · have : φ x ∈ (P.vertices : Set (E n)) := by
          rw [← hvertices]
          exact ⟨x, by exact_mod_cast hx.1, rfl⟩
        exact_mod_cast this
      · rw [← hfg]
        exact ⟨x, hx.2, rfl⟩
    · intro hy
      simp only [s, t, Finset.coe_filter, Set.mem_ofPred_eq] at hy
      have hyv : y ∈ (⇑φ) '' (P.vertices : Set (E n)) := by
        rw [hvertices]
        exact_mod_cast hy.1
      obtain ⟨x, hxv, hxy⟩ := hyv
      have hyf : y ∈ (⇑φ) '' f := by
        rw [hfg]
        exact hy.2
      obtain ⟨x', hx'f, hx'y⟩ := hyf
      have hxx' : x = x' := φ.injective (hxy.trans hx'y.symm)
      subst x'
      refine ⟨x, ?_, hxy⟩
      simp only [s, Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨hxv, hx'f⟩
  have hcentroid : s.centroid ℝ (fun x => φ x) = t.centroid ℝ id := by
    apply Finset.centroid_eq_of_inj_on_of_image_eq ℝ s t
    · intro x _ y _ hxy
      exact φ.injective hxy
    · intro x _ y _ hxy
      exact hxy
    · simpa using himage
  simpa only [centroideFaccia, s, t] using hmap.trans hcentroid

/-- Il prodotto `rᵢ rᵢ₊₁` manda il centroide della faccia di rango `i`
nel centroide dell'altra faccia di rango `i` della bandiera adiacente.
@isnad1 id=eq.2h4v.s9.5a6731bcbc40 from=translated src=- shape=e3278b4a vocab=9a7dd7cf
-/
theorem orbita_passo_combinatorio (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    simpleReflection P hreg F i
        (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩
          (centroideFaccia P (F.face i))) =
      centroideFaccia P ((adjacentFlag P hreg.1 F i).face i) := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [j] at this
    omega
  have hjfix : (⇑(simpleReflection P hreg F j)) '' F.face i = F.face i :=
    simpleReflection_fissa_facce P hreg F j hij
  have hcfix : simpleReflection P hreg F j (centroideFaccia P (F.face i)) =
      centroideFaccia P (F.face i) := by
    exact centroide_di_faccia_fissato P
      (simpleReflection_isSymmetry P hreg F j) (F.isFace i) hjfix
  have himage : (⇑(simpleReflection P hreg F i)) '' F.face i =
      (adjacentFlag P hreg.1 F i).face i := by
    have h := congrArg (fun G : P.Flag => G.face i)
      (simpleReflection_mapFlag P hreg F i)
    simpa only [mapFlag_face] using h
  rw [show (⟨(i : ℕ) + 1, hi⟩ : Fin n) = j from rfl, hcfix]
  exact centroide_di_faccia_mandato P
    (simpleReflection_isSymmetry P hreg F i) (F.isFace i)
    ((adjacentFlag P hreg.1 F i).isFace i) himage

/-- Il prodotto delle due riflessioni adiacenti, come elemento del gruppo.-/
noncomputable def rhoSimple (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) : symGroup P :=
  simpleGen P hreg F i * simpleGen P hreg F ⟨(i : ℕ) + 1, hi⟩

/-! ## Il mezzo passo astratto sul piano del residuo -/

/-- Il centro globale usato come origine affine del residuo.-/
noncomputable def centroGlobale (P : ConvexPolytope n) : E n :=
  Finset.centroid ℝ P.vertices id

/-- Vettore ottenuto proiettando sul piano del residuo.-/
noncomputable def vettoreProiettato (V : Submodule ℝ (E n)) (O c : E n) : V :=
  V.orthogonalProjectionOnto (c - O)

/-- Punto affine corrispondente al vettore proiettato.-/
noncomputable def puntoProiettato (V : Submodule ℝ (E n)) (O c : E n) : E n :=
  O + (vettoreProiettato V O c : E n)

/-! ## Pacchetto esplicito del solo innesto ancora mancante -/

/-- Dati geometrici che trasferiscono la separazione dell'orbita alla
restrizione lineare sul piano `V`.  Nessuna condizione è nascosta: in
particolare compaiono sia `orderOf R = m` sia tutte le disuguaglianze
strette richieste da `massimo_consecutivo`.-/
structure DatiMezzoPasso (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (αi αj : E n) where
  c₁ : E n
  cnext : E n
  V : Submodule ℝ (E n)
  hVspan : V = Submodule.span ℝ ({αi, αj} : Set (E n))
  hc₁_fisso_j : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ c₁ = c₁
  hc₁_mosso_i : simpleReflection P hreg F i c₁ ≠ c₁
  hcnext_fisso_i : simpleReflection P hreg F i cnext = cnext
  hcnext_mosso_j : simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ cnext ≠ cnext
  R : V ≃ₗᵢ[ℝ] V
  hord : orderOf R = coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩
  heq : ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      ((R (vettoreProiettato V (centroGlobale P) c₁) : V) : E n)⟫ =
    ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      (vettoreProiettato V (centroGlobale P) c₁ : E n)⟫
  hlt : ∀ t : ℕ, 2 ≤ t →
    t ≤ coxeterMatrix P hreg F i ⟨(i : ℕ) + 1, hi⟩ - 1 →
    ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      (((R ^ t) (vettoreProiettato V (centroGlobale P) c₁) : V) : E n)⟫ <
    ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      (vettoreProiettato V (centroGlobale P) c₁ : E n)⟫
  hperp : ⟪(vettoreProiettato V (centroGlobale P) cnext : E n),
      (vettoreProiettato V (centroGlobale P) c₁ : E n) -
        ((R (vettoreProiettato V (centroGlobale P) c₁) : V) : E n)⟫ = 0

/-! ## Riparazione simmetrica dell'interfaccia di proiezione -/

/-- Versione generica di `proiettato_fissato`, utilizzabile anche per
la seconda riflessione.
@isnad1 id=eq.5h7v.s9.591a90930aa2 from=translated src=- shape=7ffded55 vocab=2ac5f26c
-/
theorem proiettato_fissato_da_formula
    {α p O c : E n} {r : E n → E n} (hα : ‖α‖ = 1)
    (hr : ∀ x, r x = x - (2 * ⟪α, x - p⟫ : ℝ) • α)
    {V : Submodule ℝ (E n)} (hαV : α ∈ V)
    (hOfix : r O = O) (hcfix : r c = c) :
    r (puntoProiettato V O c) = puntoProiettato V O c := by
  have hαne : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα
    norm_num at hα
  have hfixed : ∀ {x : E n}, r x = x → ⟪α, x - p⟫ = 0 := by
    intro x hx
    rw [hr x] at hx
    have hs : (2 * ⟪α, x - p⟫ : ℝ) • α = 0 := sub_eq_self.mp hx
    have : (2 * ⟪α, x - p⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαne
    linarith
  have hproj :
      ⟪α, (vettoreProiettato V O c : E n)⟫ = ⟪α, c - O⟫ := by
    have ho := Submodule.inner_right_of_mem_orthogonal hαV
      (V.sub_starProjection_mem_orthogonal (c - O))
    rw [inner_sub_right, sub_eq_zero] at ho
    exact ho.symm
  have hOinner := hfixed hOfix
  have hcinner := hfixed hcfix
  have hcOinner : ⟪α, c - O⟫ = 0 := by
    rw [show c - p = (O - p) + (c - O) by abel, inner_add_right,
      hOinner, zero_add] at hcinner
    exact hcinner
  rw [hr, puntoProiettato]
  rw [show O + (vettoreProiettato V O c : E n) - p =
      (O - p) + (vettoreProiettato V O c : E n) by abel,
    inner_add_right, hOinner, zero_add, hproj, hcOinner, mul_zero,
    zero_smul, sub_zero]

/-- Versione generica di `proiettato_non_fissato`, utilizzabile anche
per la seconda riflessione.
@isnad1 id=ne.5h7v.s9.51252f84a832 from=translated src=- shape=79e1a11b vocab=2ac5f26c
-/
theorem proiettato_non_fissato_da_formula
    {α p O c : E n} {r : E n → E n} (hα : ‖α‖ = 1)
    (hr : ∀ x, r x = x - (2 * ⟪α, x - p⟫ : ℝ) • α)
    {V : Submodule ℝ (E n)} (hαV : α ∈ V)
    (hOfix : r O = O) (hcne : r c ≠ c) :
    r (puntoProiettato V O c) ≠ puntoProiettato V O c := by
  have hαne : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα
    norm_num at hα
  have hOinner : ⟪α, O - p⟫ = 0 := by
    have h := hOfix
    rw [hr O] at h
    have hs : (2 * ⟪α, O - p⟫ : ℝ) • α = 0 := sub_eq_self.mp h
    have : (2 * ⟪α, O - p⟫ : ℝ) = 0 :=
      (smul_eq_zero.mp hs).resolve_right hαne
    linarith
  have hcinner_ne : ⟪α, c - p⟫ ≠ 0 := by
    intro hc
    apply hcne
    rw [hr c, hc, mul_zero, zero_smul, sub_zero]
  have hproj :
      ⟪α, (vettoreProiettato V O c : E n)⟫ = ⟪α, c - O⟫ := by
    have ho := Submodule.inner_right_of_mem_orthogonal hαV
      (V.sub_starProjection_mem_orthogonal (c - O))
    rw [inner_sub_right, sub_eq_zero] at ho
    exact ho.symm
  intro hfix
  rw [hr] at hfix
  have hs :
      (2 * ⟪α, puntoProiettato V O c - p⟫ : ℝ) • α = 0 :=
    sub_eq_self.mp hfix
  have hscalar : (2 * ⟪α, puntoProiettato V O c - p⟫ : ℝ) = 0 :=
    (smul_eq_zero.mp hs).resolve_right hαne
  apply hcinner_ne
  have hinner : ⟪α, puntoProiettato V O c - p⟫ = ⟪α, c - p⟫ := by
    rw [puntoProiettato]
    rw [show O + (vettoreProiettato V O c : E n) - p =
        (O - p) + (vettoreProiettato V O c : E n) by abel,
      inner_add_right, hOinner, zero_add, hproj]
    rw [show c - p = (O - p) + (c - O) by abel, inner_add_right,
      hOinner, zero_add]
  rw [← hinner]
  linarith

/-! ## Collasso `k = 1` -/

end LeanEval.Geometry.PlatonicClassification
