import Tengoku.LeanEvalPlatonicClassification.Submission.OrtoplesseFacce

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Il simplesso regolare in dimensione arbitraria.

La realizzazione parte dai `d + 1` vettori razionali
`e_k - (1 / (d + 1)) * 1` nell'iperpiano di `E (d + 1)` ortogonale
al vettore costante.  Un'equivalenza isometrica, scelta tramite una base
ortonormale dell'iperpiano, li trasporta in `E d`.  In questo modo i calcoli
e l'azione delle permutazioni restano quelli trasparenti di `E (d + 1)`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Il vettore costante uno in `E (d + 1)`.-/
def simplexOne (d : ℕ) : E (d + 1) :=
  ∑ i : Fin (d + 1), EuclideanSpace.single i (1 : ℝ)

/--
@isnad1 id=eq.0h2v.s6.09919446cb92 from=translated src=- shape=891eeed3 vocab=1883af8a
-/
@[simp] theorem simplexOne_apply (d : ℕ) (i : Fin (d + 1)) :
    simplexOne d i = 1 := by
  simp [simplexOne]

/--
@isnad1 id=ne.0h1v.s7.21c24c5b1748 from=translated src=- shape=99adc771 vocab=4d50c6ab
-/
theorem simplexOne_ne_zero (d : ℕ) : simplexOne d ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : E (d + 1) => x 0) h
  norm_num at h0

/-- Permutazione delle `d + 1` coordinate ambienti.-/
noncomputable def simplexCoordPerm (d : ℕ) (σ : Equiv.Perm (Fin (d + 1))) :
    E (d + 1) ≃ₗᵢ[ℝ] E (d + 1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

/--
@isnad1 id=eq.0h4v.s10.66d8f034d7a2 from=translated src=- shape=84c21747 vocab=447d9175
-/
@[simp] theorem simplexCoordPerm_single (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) (i : Fin (d + 1)) (a : ℝ) :
    simplexCoordPerm d σ (EuclideanSpace.single i a) =
      EuclideanSpace.single (σ i) a := by
  simp [simplexCoordPerm]

/--
@isnad1 id=eq.0h2v.s10.194ba5460085 from=translated src=- shape=ef36af3b vocab=b54d43e4
-/
@[simp] theorem simplexCoordPerm_one (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) :
    simplexCoordPerm d σ (simplexOne d) = simplexOne d := by
  ext i
  change simplexOne d (σ.symm i) = simplexOne d i
  simp

/-- L'iperpiano delle coordinate a somma zero.-/
abbrev simplexHyperplane (d : ℕ) : Submodule ℝ (E (d + 1)) :=
  (ℝ ∙ simplexOne d)ᗮ

/-- Una base ortonormale non canonica dell'iperpiano delle coordinate a somma zero.-/
noncomputable def simplexHyperplaneBasis (d : ℕ) :
    OrthonormalBasis (Fin d) ℝ (simplexHyperplane d) := by
  letI : Fact (Module.finrank ℝ (E (d + 1)) = d + 1) :=
    ⟨by simp [finrank_euclideanSpace]⟩
  exact OrthonormalBasis.fromOrthogonalSpanSingleton d (simplexOne_ne_zero d)

/-- Identificazione isometrica dell'iperpiano somma-zero con `E d`.-/
noncomputable def simplexHyperplaneEquiv (d : ℕ) :
    simplexHyperplane d ≃ₗᵢ[ℝ] E d :=
  (simplexHyperplaneBasis d).repr

/-- Il vertice centrato razionale nell'iperpiano somma-zero.-/
noncomputable def simplexRawVert (d : ℕ) (k : Fin (d + 1)) :
    simplexHyperplane d := by
  refine ⟨EuclideanSpace.single k 1 -
      ((d + 1 : ℕ) : ℝ)⁻¹ • simplexOne d, ?_⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [inner_sub_left, PiLp.inner_apply]
  rw [mul_inv_cancel₀]
  · ring
  · positivity

/-- Il vertice del simplesso in `E d`.-/
noncomputable def vertSimplesso (d : ℕ) (k : Fin (d + 1)) : E d :=
  simplexHyperplaneEquiv d (simplexRawVert d k)

/--
@isnad1 id=injectiv.0h1v.s9.50dd9775b631 from=translated src=- shape=6a21da69 vocab=091e8bb5
-/
theorem simplexRawVert_injective (d : ℕ) :
    Function.Injective (simplexRawVert d) := by
  intro i j hij
  have hij' := congrArg Subtype.val hij
  change EuclideanSpace.single i (1 : ℝ) -
      ((d + 1 : ℕ) : ℝ)⁻¹ • simplexOne d =
    EuclideanSpace.single j (1 : ℝ) -
      ((d + 1 : ℕ) : ℝ)⁻¹ • simplexOne d at hij'
  have hs : EuclideanSpace.single i (1 : ℝ) =
      EuclideanSpace.single j (1 : ℝ) := sub_left_inj.mp hij'
  have hi := congrArg (fun x : E (d + 1) => x i) hs
  by_contra hne
  simp [hne] at hi

/--
@isnad1 id=injectiv.0h1v.s4.c54c8b07fa97 from=translated src=- shape=704cff23 vocab=badc15a0
-/
theorem vertSimplesso_injective (d : ℕ) :
    Function.Injective (vertSimplesso d) :=
  (simplexHyperplaneEquiv d).injective.comp (simplexRawVert_injective d)

/-- I `d + 1` vertici del simplesso regolare.-/
noncomputable def verticiSimplesso (d : ℕ) : Finset (E d) :=
  (Finset.univ : Finset (Fin (d + 1))).image (vertSimplesso d)

/--
@isnad1 id=iff.0h2v.s5.3b45dff49878 from=translated src=- shape=e114a40d vocab=ae5e9e78
-/
theorem mem_verticiSimplesso {d : ℕ} {x : E d} :
    x ∈ verticiSimplesso d ↔ ∃ k : Fin (d + 1), vertSimplesso d k = x := by
  simp [verticiSimplesso]

/--
@isnad1 id=eq.0h1v.s4.b11f80815acc from=translated src=- shape=70c10c0d vocab=d2097fc5
-/
theorem card_verticiSimplesso (d : ℕ) : (verticiSimplesso d).card = d + 1 := by
  rw [verticiSimplesso,
    Finset.card_image_of_injective _ (vertSimplesso_injective d)]
  simp

/--
@isnad1 id=affinein.0h1v.s12.dbee7fb074ba from=translated src=- shape=40243d88 vocab=e69ab226
-/
theorem simplexRawVert_affineIndependent (d : ℕ) :
    AffineIndependent ℝ (simplexRawVert d) := by
  have hb : LinearIndependent ℝ
      (fun k : Fin (d + 1) => EuclideanSpace.single k (1 : ℝ)) := by
    have heq : (fun k : Fin (d + 1) => EuclideanSpace.single k (1 : ℝ)) =
        (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis := by
      funext k
      exact (EuclideanSpace.basisFun_apply (Fin (d + 1)) ℝ k).symm
    rw [heq]
    exact (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis.linearIndependent
  have ha : AffineIndependent ℝ
      (fun k : Fin (d + 1) => EuclideanSpace.single k (1 : ℝ)) :=
    hb.affineIndependent
  have hat : AffineIndependent ℝ (fun k : Fin (d + 1) =>
      EuclideanSpace.single k (1 : ℝ) -
        ((d + 1 : ℕ) : ℝ)⁻¹ • simplexOne d) := by
    have hv := (affineIndependent_vadd (k := ℝ)
      (p := fun k : Fin (d + 1) => EuclideanSpace.single k (1 : ℝ))
      (v := -(((d + 1 : ℕ) : ℝ)⁻¹ • simplexOne d))).2 ha
    have heq : (fun k : Fin (d + 1) =>
        EuclideanSpace.single k (1 : ℝ) -
          ((d + 1 : ℕ) : ℝ)⁻¹ • simplexOne d) =
        (-(((d + 1 : ℕ) : ℝ)⁻¹ • simplexOne d) +ᵥ
          fun k : Fin (d + 1) => EuclideanSpace.single k (1 : ℝ)) := by
      funext k
      simp [sub_eq_add_neg, add_comm]
    rw [heq]
    exact hv
  apply AffineIndependent.of_comp (simplexHyperplane d).subtype.toAffineMap
  simpa [Function.comp_def, simplexRawVert] using hat

/--
@isnad1 id=affinein.0h1v.s7.fee0ae273a0f from=translated src=- shape=e8ff49b8 vocab=69bacc00
-/
theorem vertSimplesso_affineIndependent (d : ℕ) :
    AffineIndependent ℝ (vertSimplesso d) := by
  exact (simplexHyperplaneEquiv d).toLinearEquiv.toAffineEquiv.affineIndependent_iff.mpr
    (simplexRawVert_affineIndependent d)

/--
@isnad1 id=eq.0h1v.s5.5704299c43f0 from=translated src=- shape=cac76bd9 vocab=8c8e36f6
-/
theorem verticiSimplesso_coe_eq_range (d : ℕ) :
    ((verticiSimplesso d : Finset (E d)) : Set (E d)) =
      Set.range (vertSimplesso d) := by
  ext x
  simp [verticiSimplesso]

/--
@isnad1 id=eq.0h3v.s11.bf167299ecf6 from=translated src=- shape=453e1f89 vocab=596b026e
-/
theorem norm_simplexRawVert_eq (d : ℕ) (i j : Fin (d + 1)) :
    ‖simplexRawVert d i‖ = ‖simplexRawVert d j‖ := by
  let σ : Equiv.Perm (Fin (d + 1)) := Equiv.swap i j
  let L := simplexCoordPerm d σ
  change ‖(simplexRawVert d i : E (d + 1))‖ =
    ‖(simplexRawVert d j : E (d + 1))‖
  calc
    ‖(simplexRawVert d i : E (d + 1))‖ =
        ‖L (simplexRawVert d i : E (d + 1))‖ := (L.norm_map _).symm
    _ = ‖(simplexRawVert d j : E (d + 1))‖ := by
      congr 1
      simp [L, σ, simplexRawVert]

/--
@isnad1 id=le.0h1v.s7.3f666b8fd531 from=translated src=- shape=205e2901 vocab=4fc055d5
-/
theorem vertSimplesso_cospherical (d : ℕ) :
    (Set.range (vertSimplesso d)) ⊆ sphere 0 ‖vertSimplesso d 0‖ := by
  rintro _ ⟨k, rfl⟩
  rw [mem_sphere_zero_iff_norm]
  simp only [vertSimplesso, LinearIsometryEquiv.norm_map]
  exact norm_simplexRawVert_eq d k 0

/--
@isnad1 id=eq.0h1v.s8.06d910757071 from=translated src=- shape=4133bf23 vocab=f2b656b8
-/
theorem verticiSimplesso_eq_extremePoints (d : ℕ) :
    ((verticiSimplesso d : Finset (E d)) : Set (E d)) =
      Set.extremePoints ℝ
        (convexHull ℝ ((verticiSimplesso d : Finset (E d)) : Set (E d))) := by
  by_cases hd : d = 0
  · subst d
    have hsingle : ((verticiSimplesso 0 : Finset (E 0)) : Set (E 0)) = {0} := by
      ext x
      simp only [Set.mem_singleton_iff]
      constructor
      · intro _
        exact Subsingleton.elim x 0
      · rintro rfl
        rw [verticiSimplesso_coe_eq_range]
        exact ⟨0, Subsingleton.elim _ _⟩
    rw [hsingle]
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    haveI : Nontrivial (E d) := by
      refine ⟨⟨0, EuclideanSpace.single ⟨0, hdpos⟩ 1, ?_⟩⟩
      intro h
      have h0 := congrArg (fun x : E d => x ⟨0, hdpos⟩) h
      norm_num [PiLp.single_apply] at h0
    rw [verticiSimplesso_coe_eq_range]
    symm
    exact cosferico_extremePoints 0 ‖vertSimplesso d 0‖ _
      (vertSimplesso_cospherical d)

/-- Il simplesso regolare, sul dominio `d ≥ 1`.-/
noncomputable def simplesso (d : ℕ) (hd : 1 ≤ d) : ConvexPolytope d := by
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  let k : Fin (d + 1) := ⟨0, hdpos.trans (Nat.lt_succ_self d)⟩
  exact ⟨verticiSimplesso d,
    ⟨vertSimplesso d k, mem_verticiSimplesso.mpr ⟨k, rfl⟩⟩,
    verticiSimplesso_eq_extremePoints d⟩

/--
@isnad1 id=eq.1h1v.s5.5422c53ebb99 from=translated src=- shape=6ed9e32b vocab=9aa840a1
-/
theorem card_simplesso (d : ℕ) (hd : 1 ≤ d) :
    (simplesso d hd).vertices.card = d + 1 :=
  card_verticiSimplesso d

/-- Il simplesso genera affineamente tutto `E d`.
@isnad1 id=isfulldi.1h1v.s4.75308f318f1a from=translated src=- shape=dd19ab6e vocab=cae15218
-/
theorem simplesso_isFullDim (d : ℕ) (hd : 1 ≤ d) :
    (simplesso d hd).IsFullDim := by
  have hspan : vectorSpan ℝ (Set.range (vertSimplesso d)) = ⊤ :=
    (vertSimplesso_affineIndependent d).vectorSpan_eq_top_of_card_eq_finrank_add_one
      (by simp [finrank_euclideanSpace])
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim]
  change Module.finrank ℝ
    (vectorSpan ℝ (convexHull ℝ
      ((verticiSimplesso d : Finset (E d)) : Set (E d)))) = d
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan,
    verticiSimplesso_coe_eq_range, hspan, finrank_top, finrank_euclideanSpace]
  simp

/--
@isnad1 id=affinein.0h1v.s8.75528fbd4df8 from=translated src=- shape=e86ec20e vocab=f14b1a8e
-/
theorem verticiSimplesso_affineIndependent_set (d : ℕ) :
    AffineIndependent ℝ
      ((↑) : {x // x ∈
        (((verticiSimplesso d : Finset (E d)) : Set (E d)))} → E d) := by
  rw [verticiSimplesso_coe_eq_range]
  exact (vertSimplesso_affineIndependent d).range

open Classical in
/-- Ogni sottoinsieme dei vertici del simplesso è affinemente indipendente.
@isnad1 id=affinein.1h2v.s8.106662785221 from=translated src=- shape=85469edc vocab=7b68ac7a
-/
theorem simplesso_face_affineIndependent (d : ℕ) (hd : 1 ≤ d)
    {f : Set (E d)} :
    AffineIndependent ℝ
      ((↑) : {x // x ∈
        ((((simplesso d hd).vertices.filter (· ∈ f) : Finset (E d)) : Set (E d)))} →
        E d) := by
  apply (verticiSimplesso_affineIndependent_set d).mono
  intro x hx
  exact (Finset.mem_filter.mp (by exact_mod_cast hx)).1

open Classical in
/-- Una faccia del simplesso ha esattamente `faceDim + 1` vertici.
@isnad1 id=eq.2h2v.s6.0d6bf5f693a4 from=translated src=- shape=85c171fc vocab=1cba6b33
-/
theorem simplesso_face_card (d : ℕ) (hd : 1 ≤ d)
    {f : Set (E d)} (hf : (simplesso d hd).IsFace f) :
    ((simplesso d hd).vertices.filter (· ∈ f)).card = faceDim f + 1 := by
  let S : Finset (E d) := (simplesso d hd).vertices.filter (· ∈ f)
  have hFS : f = convexHull ℝ (S : Set (E d)) := face_eq_hull_vertices _ hf
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hne := hf.2
    rw [hFS, h] at hne
    simp at hne
  have hSind : AffineIndependent ℝ
      ((↑) : {x // x ∈ (S : Set (E d))} → E d) := by
    simpa only [S] using simplesso_face_affineIndependent d hd (f := f)
  letI : Nonempty {x // x ∈ (S : Set (E d))} :=
    ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  have hdim := hSind.finrank_vectorSpan_add_one
  have hrange : Set.range ((↑) : {x // x ∈ (S : Set (E d))} → E d) =
      (S : Set (E d)) := Subtype.range_coe_subtype
  rw [hrange] at hdim
  have hdim' : Module.finrank ℝ (vectorSpan ℝ (S : Set (E d))) = faceDim f := by
    symm
    unfold faceDim
    rw [hFS, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  rw [hdim'] at hdim
  change S.card = faceDim f + 1
  simpa using hdim.symm

/--
@isnad1 id=mem.1h3v.s11.9a473aeb52ab from=translated src=- shape=c0dafedd vocab=a70fbffc
-/
theorem simplexCoordPerm_mem_hyperplane (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) {x : E (d + 1)}
    (hx : x ∈ simplexHyperplane d) :
    simplexCoordPerm d σ x ∈ simplexHyperplane d := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hx ⊢
  rw [← simplexCoordPerm_one d σ,
    LinearIsometryEquiv.inner_map_map]
  exact hx

/-- La permutazione delle coordinate ristretta all'iperpiano somma-zero.-/
noncomputable def simplexHyperplanePerm (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) :
    simplexHyperplane d ≃ₗᵢ[ℝ] simplexHyperplane d where
  toFun x := ⟨simplexCoordPerm d σ x,
    simplexCoordPerm_mem_hyperplane d σ x.property⟩
  invFun x := ⟨simplexCoordPerm d σ.symm x,
    simplexCoordPerm_mem_hyperplane d σ.symm x.property⟩
  left_inv x := by
    apply Subtype.ext
    change simplexCoordPerm d σ.symm (simplexCoordPerm d σ x) = x
    rw [show simplexCoordPerm d σ.symm = (simplexCoordPerm d σ).symm by
      simp [simplexCoordPerm]]
    exact (simplexCoordPerm d σ).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    change simplexCoordPerm d σ (simplexCoordPerm d σ.symm x) = x
    rw [show simplexCoordPerm d σ.symm = (simplexCoordPerm d σ).symm by
      simp [simplexCoordPerm]]
    exact (simplexCoordPerm d σ).apply_symm_apply x
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp
  norm_map' x := by
    change ‖simplexCoordPerm d σ (x : E (d + 1))‖ = ‖(x : E (d + 1))‖
    exact (simplexCoordPerm d σ).norm_map x

/--
@isnad1 id=eq.0h3v.s13.1304644bbbf6 from=translated src=- shape=7bf026ef vocab=593bc1c5
-/
@[simp] theorem simplexHyperplanePerm_raw (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) (k : Fin (d + 1)) :
    simplexHyperplanePerm d σ (simplexRawVert d k) =
      simplexRawVert d (σ k) := by
  apply Subtype.ext
  simp [simplexHyperplanePerm, simplexRawVert]

/-- La permutazione dei vertici, trasportata come isometria lineare di `E d`.-/
noncomputable def simplexLinearPerm (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) : E d ≃ₗᵢ[ℝ] E d :=
  (simplexHyperplaneEquiv d).symm.trans
    ((simplexHyperplanePerm d σ).trans (simplexHyperplaneEquiv d))

/-- La permutazione dei vertici come isometria affine di `E d`.-/
noncomputable def simplexPerm (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) : Isom d :=
  (simplexLinearPerm d σ).toAffineIsometryEquiv

/--
@isnad1 id=eq.0h3v.s9.6f645009c4a6 from=translated src=- shape=7b16ea61 vocab=1527cc13
-/
@[simp] theorem simplexLinearPerm_vert (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) (k : Fin (d + 1)) :
    simplexLinearPerm d σ (vertSimplesso d k) = vertSimplesso d (σ k) := by
  simp [simplexLinearPerm, vertSimplesso]

/--
@isnad1 id=eq.0h3v.s8.a47abb210a72 from=translated src=- shape=fffba23e vocab=1aea660d
-/
@[simp] theorem simplexPerm_vert (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) (k : Fin (d + 1)) :
    simplexPerm d σ (vertSimplesso d k) = vertSimplesso d (σ k) := by
  exact simplexLinearPerm_vert d σ k

/--
@isnad1 id=eq.0h2v.s8.fdfd238bf43f from=translated src=- shape=ef89ed2a vocab=1bda366e
-/
theorem simplexPerm_image_vertici (d : ℕ)
    (σ : Equiv.Perm (Fin (d + 1))) :
    (simplexPerm d σ : E d → E d) '' (verticiSimplesso d : Set (E d)) =
      (verticiSimplesso d : Set (E d)) := by
  rw [verticiSimplesso_coe_eq_range]
  ext x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨σ k, (simplexPerm_vert d σ k).symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨vertSimplesso d (σ.symm k), ⟨σ.symm k, rfl⟩, ?_⟩
    simp

/--
@isnad1 id=issymmet.1h2v.s5.7b3b504da2ff from=translated src=- shape=8033e828 vocab=7e6e9523
-/
theorem simplexPerm_isSymmetry (d : ℕ) (hd : 1 ≤ d)
    (σ : Equiv.Perm (Fin (d + 1))) :
    (simplesso d hd).isSymmetry (simplexPerm d σ) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (simplexPerm d σ : E d → E d) ''
        convexHull ℝ ((simplesso d hd).vertices : Set (E d)) =
      convexHull ℝ ((simplexPerm d σ : E d → E d) ''
        ((simplesso d hd).vertices : Set (E d))) := by
          exact (simplexPerm d σ).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((simplesso d hd).vertices : Set (E d)) := by
      rw [show ((simplesso d hd).vertices : Set (E d)) =
          (verticiSimplesso d : Set (E d)) by rfl,
        simplexPerm_image_vertici]

open Classical in
noncomputable def simplessoFlagVertices (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) : Finset (E d) :=
  (simplesso d hd).vertices.filter (· ∈ F.face k)

open Classical in
noncomputable def simplessoFlagPrev (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) : Finset (E d) :=
  if hk : k.val = 0 then ∅ else
    simplessoFlagVertices d hd F (finPredSame k hk)

open Classical in
/--
@isnad1 id=eq.1h3v.s5.43c761ac80b3 from=translated src=- shape=97810871 vocab=439a62b6
-/
theorem simplessoFlagVertices_card (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) :
    (simplessoFlagVertices d hd F k).card = k.val + 1 := by
  simpa [simplessoFlagVertices, F.dim_eq] using
    simplesso_face_card d hd (F.isFace k)

open Classical in
/--
@isnad1 id=le.2h4v.s5.dde5ab83af42 from=translated src=- shape=b1fc39e9 vocab=13d6da9d
-/
theorem simplessoFlagVertices_mono (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) {i j : Fin d} (hij : i ≤ j) :
    simplessoFlagVertices d hd F i ⊆ simplessoFlagVertices d hd F j := by
  intro v hv
  rw [simplessoFlagVertices, Finset.mem_filter] at hv ⊢
  refine ⟨hv.1, ?_⟩
  rcases hij.eq_or_lt with rfl | hij
  · exact hv.2
  · exact (F.strict_mono i j hij).1 hv.2

open Classical in
/--
@isnad1 id=nonempty.1h3v.s6.cb71c4295e0b from=translated src=- shape=68e0eda3 vocab=04ea2b1c
-/
theorem simplessoFlagStep_nonempty (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) :
    (simplessoFlagVertices d hd F k \ simplessoFlagPrev d hd F k).Nonempty := by
  by_cases hk : k.val = 0
  · have hc := simplessoFlagVertices_card d hd F k
    simpa [simplessoFlagPrev, hk] using
      (Finset.card_pos.mp
        (by omega : 0 < (simplessoFlagVertices d hd F k).card))
  · let p : Fin d := finPredSame k hk
    have hpk : p < k := by
      apply Fin.mk_lt_mk.mpr
      simp
      omega
    have hsub : simplessoFlagVertices d hd F p ⊆
        simplessoFlagVertices d hd F k :=
      simplessoFlagVertices_mono d hd F hpk.le
    have hcp := simplessoFlagVertices_card d hd F p
    have hck := simplessoFlagVertices_card d hd F k
    have hcdiff :
        (simplessoFlagVertices d hd F k \
          simplessoFlagVertices d hd F p).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hcp, hck]
      simp [p]
      omega
    have hne : (simplessoFlagVertices d hd F k \
        simplessoFlagVertices d hd F p).Nonempty :=
      Finset.card_pos.mp (by omega)
    simpa [simplessoFlagPrev, hk, p] using hne

open Classical in
noncomputable def simplessoFlagNew (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) : E d :=
  (simplessoFlagStep_nonempty d hd F k).choose

open Classical in
/--
@isnad1 id=mem.1h3v.s5.7754298a9677 from=translated src=- shape=9979f4fa vocab=5374aabc
-/
theorem simplessoFlagNew_mem (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) :
    simplessoFlagNew d hd F k ∈ simplessoFlagVertices d hd F k :=
  (Finset.mem_sdiff.mp
    (simplessoFlagStep_nonempty d hd F k).choose_spec).1

open Classical in
/--
@isnad1 id=not.1h3v.s5.25db8fafa161 from=translated src=- shape=4d048094 vocab=fff53ee2
-/
theorem simplessoFlagNew_not_prev (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) :
    simplessoFlagNew d hd F k ∉ simplessoFlagPrev d hd F k :=
  (Finset.mem_sdiff.mp
    (simplessoFlagStep_nonempty d hd F k).choose_spec).2

open Classical in
/--
@isnad1 id=injectiv.1h2v.s4.915444fde042 from=translated src=- shape=e63742cb vocab=079a7eb9
-/
theorem simplessoFlagNew_injective (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) :
    Function.Injective (simplessoFlagNew d hd F) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hj0 : j.val ≠ 0 := by omega
    let p : Fin d := finPredSame j hj0
    have hip : i ≤ p := by
      apply Fin.mk_le_mk.mpr
      omega
    have himem : simplessoFlagNew d hd F i ∈
        simplessoFlagVertices d hd F p :=
      simplessoFlagVertices_mono d hd F hip
        (simplessoFlagNew_mem d hd F i)
    have hjnot : simplessoFlagNew d hd F j ∉
        simplessoFlagVertices d hd F p := by
      simpa [simplessoFlagPrev, hj0, p] using
        simplessoFlagNew_not_prev d hd F j
    exact hjnot (hij ▸ himem)
  · have hi0 : i.val ≠ 0 := by omega
    let p : Fin d := finPredSame i hi0
    have hjp : j ≤ p := by
      apply Fin.mk_le_mk.mpr
      omega
    have hjmem : simplessoFlagNew d hd F j ∈
        simplessoFlagVertices d hd F p :=
      simplessoFlagVertices_mono d hd F hjp
        (simplessoFlagNew_mem d hd F j)
    have hinot : simplessoFlagNew d hd F i ∉
        simplessoFlagVertices d hd F p := by
      simpa [simplessoFlagPrev, hi0, p] using
        simplessoFlagNew_not_prev d hd F i
    exact hinot (hij.symm ▸ hjmem)

open Classical in
/--
@isnad1 id=eq.1h3v.s6.00e05c846e94 from=translated src=- shape=95a6b99b vocab=6226895e
-/
theorem simplessoFlagVertices_eq_image_Iic (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) :
    simplessoFlagVertices d hd F k =
      (Finset.Iic k).image (simplessoFlagNew d hd F) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact simplessoFlagVertices_mono d hd F (Finset.mem_Iic.mp hj)
      (simplessoFlagNew_mem d hd F j)
  · rw [Finset.card_image_of_injective _ (simplessoFlagNew_injective d hd F),
      simplessoFlagVertices_card d hd F k]
    simp

open Classical in
noncomputable def simplessoFlagCode (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) : Fin (d + 1) :=
  (mem_verticiSimplesso.mp
    (show simplessoFlagNew d hd F k ∈ verticiSimplesso d from
      (Finset.mem_filter.mp (simplessoFlagNew_mem d hd F k)).1)).choose

open Classical in
/--
@isnad1 id=eq.1h3v.s5.2d14270ec196 from=translated src=- shape=caeac899 vocab=cf6851a4
-/
theorem simplessoFlagCode_spec (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) (k : Fin d) :
    vertSimplesso d (simplessoFlagCode d hd F k) =
      simplessoFlagNew d hd F k :=
  (mem_verticiSimplesso.mp
    (show simplessoFlagNew d hd F k ∈ verticiSimplesso d from
      (Finset.mem_filter.mp (simplessoFlagNew_mem d hd F k)).1)).choose_spec

open Classical in
/--
@isnad1 id=injectiv.1h2v.s5.e975fbf55beb from=translated src=- shape=b2fa1a8a vocab=5dbaa714
-/
theorem simplessoFlagCode_injective (d : ℕ) (hd : 1 ≤ d)
    (F : (simplesso d hd).Flag) :
    Function.Injective (simplessoFlagCode d hd F) := by
  intro i j hij
  apply simplessoFlagNew_injective d hd F
  rw [← simplessoFlagCode_spec d hd F i,
    ← simplessoFlagCode_spec d hd F j, hij]

open Classical in
noncomputable def simplessoFlagPerm (d : ℕ) (hd : 1 ≤ d)
    (F G : (simplesso d hd).Flag) : Equiv.Perm (Fin (d + 1)) :=
  (Equiv.Perm.exists_extending_pair
    (simplessoFlagCode d hd F) (simplessoFlagCode d hd G)
    (simplessoFlagCode_injective d hd F)
    (simplessoFlagCode_injective d hd G)).choose

open Classical in
/--
@isnad1 id=eq.1h4v.s7.ffd2ab7eed91 from=translated src=- shape=8a7b2c5e vocab=88c5ed1b
-/
theorem simplessoFlagPerm_spec (d : ℕ) (hd : 1 ≤ d)
    (F G : (simplesso d hd).Flag) (k : Fin d) :
    simplessoFlagPerm d hd F G (simplessoFlagCode d hd F k) =
      simplessoFlagCode d hd G k :=
  (Equiv.Perm.exists_extending_pair
    (simplessoFlagCode d hd F) (simplessoFlagCode d hd G)
    (simplessoFlagCode_injective d hd F)
    (simplessoFlagCode_injective d hd G)).choose_spec k

open Classical in
/--
@isnad1 id=eq.1h4v.s8.5cec665e60e4 from=translated src=- shape=bb619ad7 vocab=2c51e741
-/
theorem simplessoFlagIsom_new (d : ℕ) (hd : 1 ≤ d)
    (F G : (simplesso d hd).Flag) (k : Fin d) :
    simplexPerm d (simplessoFlagPerm d hd F G)
        (simplessoFlagNew d hd F k) =
      simplessoFlagNew d hd G k := by
  rw [← simplessoFlagCode_spec d hd F k,
    ← simplessoFlagCode_spec d hd G k,
    simplexPerm_vert, simplessoFlagPerm_spec]

open Classical in
/--
@isnad1 id=eq.1h4v.s8.30b51a50cdc0 from=translated src=- shape=a4c32065 vocab=d95259e1
-/
theorem simplessoFlagIsom_image_vertices (d : ℕ) (hd : 1 ≤ d)
    (F G : (simplesso d hd).Flag) (k : Fin d) :
    Finset.image (simplexPerm d (simplessoFlagPerm d hd F G))
        (simplessoFlagVertices d hd F k) =
      simplessoFlagVertices d hd G k := by
  rw [simplessoFlagVertices_eq_image_Iic d hd F k,
    simplessoFlagVertices_eq_image_Iic d hd G k]
  ext x
  simp only [Finset.mem_image, Finset.mem_Iic]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, (simplessoFlagIsom_new d hd F G j).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨simplessoFlagNew d hd F j, ⟨j, hj, rfl⟩,
      simplessoFlagIsom_new d hd F G j⟩

open Classical in
/--
@isnad1 id=eq.1h4v.s8.e160a9fcbbf6 from=translated src=- shape=a8413261 vocab=3ced4531
-/
theorem simplessoFlagIsom_image_face (d : ℕ) (hd : 1 ≤ d)
    (F G : (simplesso d hd).Flag) (k : Fin d) :
    (simplexPerm d (simplessoFlagPerm d hd F G) : E d → E d) '' F.face k =
      G.face k := by
  let φ := simplexPerm d (simplessoFlagPerm d hd F G)
  calc
    (φ : E d → E d) '' F.face k =
        (φ : E d → E d) '' convexHull ℝ
          ((simplessoFlagVertices d hd F k : Finset (E d)) : Set (E d)) := by
      rw [face_eq_hull_vertices (simplesso d hd) (F.isFace k)]
      rfl
    _ = convexHull ℝ ((φ : E d → E d) ''
          ((simplessoFlagVertices d hd F k : Finset (E d)) : Set (E d))) := by
      exact φ.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ
          ((simplessoFlagVertices d hd G k : Finset (E d)) : Set (E d)) := by
      rw [← Finset.coe_image, simplessoFlagIsom_image_vertices d hd F G k]
    _ = G.face k := by
      rw [face_eq_hull_vertices (simplesso d hd) (G.isFace k)]
      rfl

open Classical in
/--
@isnad1 id=isregula.1h1v.s4.2fb6e7dfab25 from=translated src=- shape=dd19ab6e vocab=85d28c61
-/
theorem simplesso_isRegular (d : ℕ) (hd : 1 ≤ d) :
    (simplesso d hd).IsRegular := by
  refine ⟨simplesso_isFullDim d hd, ?_⟩
  intro F G
  refine ⟨simplexPerm d (simplessoFlagPerm d hd F G),
    simplexPerm_isSymmetry d hd _, ?_⟩
  exact simplessoFlagIsom_image_face d hd F G

/--
@isnad1 id=mem.1h1v.s4.621d7620ed7b from=translated src=- shape=3ed95865 vocab=f1e3d880
-/
theorem simplesso_mem_regularPolytopes (d : ℕ) (hd : 1 ≤ d) :
    simplesso d hd ∈ regularPolytopes d :=
  simplesso_isRegular d hd

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
