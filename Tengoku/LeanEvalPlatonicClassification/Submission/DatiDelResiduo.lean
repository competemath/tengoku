import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.CollassoK

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Parte lineare del prodotto delle due riflessioni semplici adiacenti.-/
noncomputable def rhoLineare (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n) : E n ≃ₗᵢ[ℝ] E n :=
  ((((rhoSimple P hreg F i hi : symGroup P) : Isom n)).linearIsometryEquiv)

/-- Formula esplicita della parte lineare di `rhoSimple`.
@isnad1 id=eq.4h9v.s11.684e2a8787c4 from=translated src=- shape=43a5aa39 vocab=248a03bb
-/
theorem rhoLineare_formula (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n}
    (hri : ∀ x, simpleReflection P hreg F i x =
      x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) (x : E n) :
    rhoLineare P hreg F i hi x =
      (x - (2 * ⟪αj, x⟫ : ℝ) • αj) -
        (2 * ⟪αi, x - (2 * ⟪αj, x⟫ : ℝ) • αj⟫ : ℝ) • αi := by
  have hmap := ((((rhoSimple P hreg F i hi : symGroup P) : Isom n)).map_vsub x 0)
  have heval : ∀ z : E n,
      (((rhoSimple P hreg F i hi : symGroup P) : Isom n) z) =
        simpleReflection P hreg F i
          (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ z) := by
    intro z
    rfl
  have hmap' : rhoLineare P hreg F i hi x =
      simpleReflection P hreg F i
          (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x) -
        simpleReflection P hreg F i
          (simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ 0) := by
    rw [heval x, heval 0] at hmap
    simpa only [rhoLineare, vsub_eq_sub, sub_zero] using hmap
  rw [hrj x, hri, hrj 0, hri] at hmap'
  rw [hmap']
  simp only [zero_sub, inner_sub_right, inner_neg_right,
    real_inner_smul_right]
  match_scalars <;> ring

/-! ## Libertà dell'orbita ciclica sulla faccia di rango `i` -/

/-- Ogni potenza di `rhoSimple` fissa le facce della bandiera base di
rango diverso dai due ranghi adiacenti coinvolti.
@isnad1 id=eq.4h6v.s11.a04c9b59ae76 from=translated src=- shape=d1207248 vocab=7a9e95f0
-/
theorem rhoSimple_pow_fissa_faccia (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ ⟨(i : ℕ) + 1, hi⟩) (t : ℕ) :
    (⇑((((rhoSimple P hreg F i hi) ^ t : symGroup P) : Isom n))) ''
        F.face k = F.face k := by
  let g : symGroup P := rhoSimple P hreg F i hi
  have hg : (⇑((g : symGroup P) : Isom n)) '' F.face k = F.face k := by
    calc
      (⇑((g : symGroup P) : Isom n)) '' F.face k =
          (⇑(simpleReflection P hreg F i)) ''
            ((⇑(simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩)) ''
              F.face k) := by
                rw [Set.image_image]
                rfl
      _ = F.face k := by
        rw [simpleReflection_fissa_facce P hreg F
          ⟨(i : ℕ) + 1, hi⟩ hkj,
          simpleReflection_fissa_facce P hreg F i hki]
  change (⇑((((g : symGroup P) ^ t : symGroup P) : Isom n))) ''
      F.face k = F.face k
  induction t with
  | zero => simp
  | succ t iht =>
      rw [pow_succ]
      calc
        (⇑((((g ^ t) * g : symGroup P) : Isom n))) '' F.face k =
            (⇑(((g ^ t : symGroup P) : Isom n))) ''
              ((⇑((g : symGroup P) : Isom n)) '' F.face k) := by
                rw [Set.image_image]
                rfl
        _ = F.face k := by rw [hg, iht]

/-- Un passo di `rhoSimple` manda la faccia di rango `i` nell'altra
faccia di rango `i` contenuta nello stesso lato di rango `i+1`.
@isnad1 id=eq.2h4v.s9.fc88f1e93dde from=translated src=- shape=d0742905 vocab=727abff7
-/
theorem rhoSimple_manda_faccia (P : ConvexPolytope n)
    (hreg : P.IsRegular) (F : P.Flag) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    (⇑(((rhoSimple P hreg F i hi : symGroup P) : Isom n))) '' F.face i =
      (adjacentFlag P hreg.1 F i).face i := by
  let j : Fin n := ⟨(i : ℕ) + 1, hi⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [j] at this
    omega
  calc
    (⇑(((rhoSimple P hreg F i hi : symGroup P) : Isom n))) '' F.face i =
        (⇑(simpleReflection P hreg F i)) ''
          ((⇑(simpleReflection P hreg F j)) '' F.face i) := by
            rw [Set.image_image]
            rfl
    _ = (⇑(simpleReflection P hreg F i)) '' F.face i := by
      rw [simpleReflection_fissa_facce P hreg F j hij]
    _ = (adjacentFlag P hreg.1 F i).face i := by
      have h := congrArg (fun G : P.Flag => G.face i)
        (simpleReflection_mapFlag P hreg F i)
      simpa only [mapFlag_face] using h

/-! ## Espositore separante dell'orbita -/

/-! ## Dal funzionale al vettore del residuo -/

/-- Vettore di Riesz della restrizione di un funzionale al sottospazio `V`.-/
noncomputable def rieszResiduo (V : Submodule ℝ (E n))
    (l : E n →L[ℝ] ℝ) : V :=
  (InnerProductSpace.toDual ℝ V).symm (l.comp V.subtypeL)

/--
@isnad1 id=eq.0h4v.s10.8c0357c92d50 from=translated src=- shape=a6d7ab0d vocab=2ad2dd05
-/
theorem rieszResiduo_spec (V : Submodule ℝ (E n))
    (l : E n →L[ℝ] ℝ) (z : V) :
    ⟪(rieszResiduo V l : E n), (z : E n)⟫ = l (z : E n) := by
  change ⟪rieszResiduo V l, z⟫ = l (z : E n)
  rw [rieszResiduo, InnerProductSpace.toDual_symm_apply]
  rfl

/-- Facce distinte della stessa dimensione hanno centroidi distinti.
@isnad1 id=ne.4h4v.s5.e984af74244a from=translated src=- shape=b6ac9eea vocab=cade1f0e
-/
theorem centroidi_facce_distinte (P : ConvexPolytope n)
    {f g : Set (E n)} (hf : P.IsFace f) (hg : P.IsFace g)
    (hdim : faceDim f = faceDim g) (hne : f ≠ g) :
    centroideFaccia P f ≠ centroideFaccia P g := by
  intro hc
  have hcf : centroideFaccia P f ∈ f := centroide_mem_faccia P hf
  have hcg : centroideFaccia P g ∈ g := centroide_mem_faccia P hg
  have hcfg : centroideFaccia P f ∈ f ∩ g := ⟨hcf, by simpa [hc] using hcg⟩
  have hDface : P.IsFace (f ∩ g) := ⟨hf.1.inter hg.1, ⟨_, hcfg⟩⟩
  have hDproper : f ∩ g < f := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro hback
    have hfg : f ⊆ g := fun x hx => (hback hx).2
    have hstrict : f < g :=
      ⟨hfg, fun hgf => hne (Set.Subset.antisymm hfg hgf)⟩
    have hlt := faceDim_lt_of_ssubset P hf hg hstrict
    omega
  have hout := centroide_fuori_da_span_sottofaccia P hDface hf hDproper
  exact hout (subset_affineSpan ℝ (f ∩ g) hcfg)

/-- L'ortogonalità richiesta dal mezzo passo è la forma bilineare
dell'uguaglianza dei primi due valori.
@isnad1 id=eq.1h6v.s13.087ac5cf646e from=translated src=- shape=23e99a1e vocab=d8916c7d
-/
theorem perp_del_lato (V : Submodule ℝ (E n)) (O c₁ cnext : E n)
    (R : V ≃ₗᵢ[ℝ] V)
    (heq : ⟪(vettoreProiettato V O cnext : E n),
        ((R (vettoreProiettato V O c₁) : V) : E n)⟫ =
      ⟪(vettoreProiettato V O cnext : E n),
        (vettoreProiettato V O c₁ : E n)⟫) :
    ⟪(vettoreProiettato V O cnext : E n),
      (vettoreProiettato V O c₁ : E n) -
        ((R (vettoreProiettato V O c₁) : V) : E n)⟫ = 0 := by
  rw [inner_sub_right, heq]
  ring

/-! ## Assemblaggio -/

end LeanEval.Geometry.PlatonicClassification
