import Tengoku.Seed.Algebra.Category.ModuleCat.Abelian
import Tengoku.Seed.RepresentationTheory.Basic
import Tengoku.Seed.Algebra.Category.ModuleCat.Colimits
import Tengoku.Seed.CategoryTheory.Preadditive.Schur
import Tengoku.Seed.CategoryTheory.Limits.Shapes.ZeroObjects
import Tengoku.Seed.RepresentationTheory.FDRep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-dimensional representations

Main contents:

* lifting representations
* duals and internal Homs;
* zero objects and zero-dimensionality lemmas;
* stable subrepresentations and the mono/injective criterion;
* the finite-dimensional left regular and trivial representations.
-/

universe u v w w'
open CategoryTheory
open CategoryTheory.Limits

namespace FDRep

section HomExt

variable {k : Type u} [CommRing k]
variable {G : Type v} [Monoid G]

/--
Extensionality for morphisms of Mathlib `FDRep`s, by checking the underlying
morphism of `Rep`s pointwise.
@isnad1 id=eq.1h6v.s17.d8e48388c50b from=translated src=- shape=2706913d vocab=f9a00337
-/
lemma hom_ext {V W : FDRep k G} {f g : V ⟶ W}
    (h : ∀ x : V,
      (((forget₂ (FDRep k G) (Rep k G)).map f).hom x)
        =
      (((forget₂ (FDRep k G) (Rep k G)).map g).hom x)) :
    f = g := by
  apply (forget₂ (FDRep k G) (Rep k G)).map_injective
  apply Rep.hom_ext
  ext x
  exact h x

/-- A morphism of `FDRep`s intertwines the actions, as an equality of linear maps.
@isnad1 id=eq.0h6v.s13.902bff95aab9 from=translated src=- shape=243c4138 vocab=f5ba5d67
-/
lemma hom_comp_ρ {X Y : FDRep k G} (f : X ⟶ Y) (g : G) :
    f.hom.hom.hom ∘ₗ X.ρ g = Y.ρ g ∘ₗ f.hom.hom.hom := by
  ext v
  simp only [LinearMap.comp_apply]
  have h_cat := Action.Hom.comm f g
  let h := congr_arg (fun φ => φ.hom.hom) h_cat
  change f.hom.hom.hom ∘ₗ X.ρ g = Y.ρ g ∘ₗ f.hom.hom.hom at h
  exact LinearMap.congr_fun h v

/-- The underlying linear map of an `FDRep` morphism.-/
noncomputable abbrev homToLinearMap
    {H : Type w} [Monoid H]
    {V W : FDRep k H} (f : V ⟶ W) :
    V →ₗ[k] W :=
  ((forget₂ (FGModuleCat k) (ModuleCat k)).map f.hom).hom

/--
@isnad1 id=eq.0h4v.s10.52b2a3ae5f8e from=translated src=- shape=0300d595 vocab=377cb00b
-/
@[simp]
lemma homToLinearMap_zero {V W : FDRep k G} :
    homToLinearMap (0 : V ⟶ W) = 0 := by
  rfl

/--
@isnad1 id=eq.0h3v.s9.c1f8116ecc13 from=translated src=- shape=43e96e6a vocab=39be667d
-/
@[simp]
lemma homToLinearMap_id {X : FDRep k G} :
    homToLinearMap (𝟙 X) = LinearMap.id := by
  ext x
  rfl

/--
@isnad1 id=eq.0h7v.s10.a25d30818844 from=translated src=- shape=b5bb91ad vocab=a0df1937
-/
@[simp]
lemma homToLinearMap_comp {U V W : FDRep k G} (f : U ⟶ V) (g : V ⟶ W) :
    homToLinearMap (f ≫ g) =
      (homToLinearMap g).comp (homToLinearMap f) := by
  rfl

/--
@isnad1 id=eq.0h7v.s13.41908668df69 from=translated src=- shape=beed10e3 vocab=8b4aff1d
-/
lemma homToLinearMap_comm
    {V W : FDRep k G} (f : V ⟶ W) (g : G) (x : V) :
    homToLinearMap f (V.ρ g x) =
      W.ρ g (homToLinearMap f x) := by
  let F := (forget₂ (FDRep k G) (Rep k G)).map f
  change F.hom (V.ρ g x) = W.ρ g (F.hom x)
  exact
    Representation.IntertwiningMap.isIntertwining ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ
      ((forget₂ (FDRep k G) (Rep k G)).obj W).ρ (Rep.Hom.hom F) g x

/--
@isnad1 id=eq.0h6v.s11.4a7d727893de from=translated src=- shape=b932bca4 vocab=c1e19a36
-/
@[simp]
lemma homToLinearMap_add {X Y : FDRep k G} (f g : X ⟶ Y) :
    homToLinearMap (f + g) = homToLinearMap f + homToLinearMap g := by
  rfl

/--
@isnad1 id=eq.0h4v.s9.71eeb62364a6 from=translated src=- shape=4f87013a vocab=ac613fe3
-/
@[simp]
lemma homToLinearMap_id_apply {X : FDRep k G} (x : X) :
    homToLinearMap (𝟙 X) x = x := by
  rfl

/--
@isnad1 id=eq.0h5v.s10.3327cbddab44 from=translated src=- shape=b7e302ea vocab=b9280667
-/
@[simp]
lemma homToLinearMap_zero_apply {X Y : FDRep k G} (x : X) :
    homToLinearMap (0 : X ⟶ Y) x = 0 := by
  rfl

/--
@isnad1 id=eq.0h7v.s11.d5a40ba9cff6 from=translated src=- shape=0c286910 vocab=f76f395e
-/
@[simp]
lemma homToLinearMap_add_apply {X Y : FDRep k G}
    (f g : X ⟶ Y) (x : X) :
    homToLinearMap (f + g) x = homToLinearMap f x + homToLinearMap g x := by
  rfl

/--
@isnad1 id=eq.0h8v.s11.f6b4c3ca819d from=translated src=- shape=469eacc1 vocab=613ddc3b
-/
@[simp]
lemma homToLinearMap_comp_apply {X Y Z : FDRep k G}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    homToLinearMap (f ≫ g) x = homToLinearMap g (homToLinearMap f x) := by
  rfl

/--
@isnad1 id=eq.0h6v.s11.754c2a047fa0 from=translated src=- shape=8ddbe811 vocab=8325747e
-/
@[simp]
lemma homToLinearMap_smul
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    {X Y : FDRep k G} (c : k) (f : X ⟶ Y) :
    FDRep.homToLinearMap (c • f) = c • FDRep.homToLinearMap f := by
  rfl

/--
@isnad1 id=eq.0h7v.s12.d6ea45dfa534 from=translated src=- shape=4462865e vocab=63beb248
-/
@[simp]
lemma homToLinearMap_smul_apply
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    {X Y : FDRep k G} (c : k) (f : X ⟶ Y) (x : X) :
    FDRep.homToLinearMap (c • f) x = c • FDRep.homToLinearMap f x := by
  rfl

/-- A morphism of `FDRep`s intertwines the actions, pointwise.
@isnad1 id=eq.0h7v.s13.8bce1546d7f6 from=translated src=- shape=8422f904 vocab=69a1fc27
-/
lemma homToLinearMap_rho_apply {H : Type v} [Group H]
    {X Y : FDRep k H} (f : X ⟶ Y) (h : H) (x : X.V.obj) :
    homToLinearMap f (X.ρ h x) = Y.ρ h (homToLinearMap f x) := by
  have hcat := Action.Hom.comm f h
  let hlin := congrArg (fun φ => φ.hom.hom) hcat
  exact LinearMap.congr_fun hlin x

/--
@isnad1 id=eq.0h5v.s16.33f0bd6f3700 from=translated src=- shape=86d4e853 vocab=674e2816
-/
@[simp]
lemma forget₂_map_forget₂HomLinearEquiv
    {k : Type u} [CommRing k]
    {G : Type u} [Group G]
    {X Y : FDRep k G}
    (f :
      (forget₂ (FDRep k G) (Rep k G)).obj X ⟶
        (forget₂ (FDRep k G) (Rep k G)).obj Y) :
    (forget₂ (FDRep k G) (Rep k G)).map
        (FDRep.forget₂HomLinearEquiv X Y f) = f := by
  change
    (FDRep.forget₂HomLinearEquiv X Y).symm
      ((FDRep.forget₂HomLinearEquiv X Y) f) = f
  simp

/--
@isnad1 id=eq.0h5v.s16.1bf5c73d6021 from=translated src=- shape=23761c4b vocab=adf3c006
-/
@[simp]
lemma forget₂HomLinearEquiv_symm_apply
    {k : Type u} [CommRing k]
    {G : Type u} [Group G]
    {X Y : FDRep k G}
    (f : X ⟶ Y) :
    (FDRep.forget₂HomLinearEquiv X Y).symm f =
      (forget₂ (FDRep k G) (Rep k G)).map f := by
  apply (FDRep.forget₂HomLinearEquiv X Y).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (forget₂ (FDRep k G) (Rep k G)).map_injective
  simp only [FGModuleCat.obj_carrier,
    forget₂_map_forget₂HomLinearEquiv
        ((forget₂ (FDRep k G) (Rep k G)).map f)]

/--
Build an `FDRep` morphism from an equivariant linear map.

The equivariance condition is stated pointwise in the usual direction.-/
noncomputable def homOfLinearMap {H : Type v} [Group H]
    {X Y : FDRep k H}
    (f : X.V.obj →ₗ[k] Y.V.obj)
    (hf : ∀ h : H, f ∘ₗ X.ρ h = Y.ρ h ∘ₗ f) :
    X ⟶ Y := by
  refine ⟨?_, ?_⟩
  · exact FGModuleCat.ofHom f
  · intro h
    ext x
    exact LinearMap.congr_fun (hf h) x

/-- The action of a group element as a linear equivalence.-/
noncomputable def rhoLinearEquiv {H : Type v} [Group H]
    (σ : FDRep k H) (h : H) :
    σ.V.obj ≃ₗ[k] σ.V.obj :=
  { toLinearMap := σ.ρ h
    invFun := fun v => σ.ρ h⁻¹ v
    left_inv := by
      intro v
      calc
        σ.ρ h⁻¹ (σ.ρ h v)
            = σ.ρ (h⁻¹ * h) v := by
                rw [map_mul]
                rfl
        _ = v := by simp
    right_inv := by
      intro v
      calc
        σ.ρ h (σ.ρ h⁻¹ v)
            = σ.ρ (h * h⁻¹) v := by
                rw [map_mul]
                rfl
        _ = v := by simp }

end HomExt

section quotient

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
/--
Descend a representation of `G` to the quotient `G ⧸ K` when the normal
subgroup `K` acts trivially.-/
noncomputable def lift
    (V : FDRep k G)
    (K : Subgroup G) [K.Normal]
    (h_triv : ∀ x ∈ K, V.ρ x = 1) :
    FDRep k (G ⧸ K) := by
  let ρq : Representation k (G ⧸ K) V :=
    QuotientGroup.lift K V.ρ (by
      intro x hx
      exact h_triv x hx)
  exact FDRep.of ρq

end quotient

/-- Tensor product of finite-dimensional representations.-/
abbrev tensor
    {k : Type u} [Field k]
    {G : Type v} [Monoid G]
    (V W : FDRep k G) : FDRep k G :=
  CategoryTheory.MonoidalCategoryStruct.tensorObj V W

section dual_and_hom

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
The dual finite-dimensional representation.-/
noncomputable def dual (V : FDRep k G) : FDRep k G :=
  FDRep.of (Representation.dual V.ρ)

/--
@isnad1 id=eq.0h3v.s11.37e812974b00 from=translated src=- shape=3ce8177c vocab=f3496bd5
-/
@[simp]
lemma dual_ρ (V : FDRep k G) :
    (V.dual).ρ = Representation.dual V.ρ := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/--
@isnad1 id=eq.0h4v.s14.46f53adbc850 from=translated src=- shape=b4344cf4 vocab=bca65a4b
-/
@[simp]
lemma dual_ρ_apply (V : FDRep k G) (g : G) :
    (V.dual).ρ g = Module.Dual.transpose (V.ρ g⁻¹) := by
  rw [dual_ρ]
  exact Representation.dual_apply V.ρ g

/--
The internal Hom representation `Hom_k(V,W)` bundled as an `FDRep`.

The group acts by conjugation: `g` sends a linear map `f` to
`ρ_W(g) ∘ f ∘ ρ_V(g⁻¹)`.-/
noncomputable def linHom (V W : FDRep k G) : FDRep k G :=
  FDRep.of (Representation.linHom V.ρ W.ρ)

/--
@isnad1 id=eq.0h4v.s11.53187c9d6ee5 from=translated src=- shape=f7012638 vocab=c089a633
-/
@[simp]
lemma linHom_rho (V W : FDRep k G) [Module.Free k V] :
    (V.linHom W).ρ = Representation.linHom V.ρ W.ρ := by dsimp[FDRep.linHom]

end dual_and_hom

section zero

variable {k : Type u} [CommRing k]
variable {G : Type v} [Monoid G]

/--
A finite-dimensional representation is a zero object iff its underlying vector
space is subsingleton.
@isnad1 id=iff.0h3v.s6.86357a21acf9 from=translated src=- shape=f5ccf11b vocab=e2a9ae8d
-/
theorem isZero_iff_subsingleton (V : FDRep k G) :
    IsZero V ↔ Subsingleton V := by
  constructor
  · intro hV
    refine ⟨fun x y => ?_⟩
    have hid : (𝟙 V : V ⟶ V) = 0 :=
      (IsZero.iff_id_eq_zero V).mp hV
    have hx :=
      congrArg
        (fun f : V ⟶ V =>
          (((forget₂ (FDRep k G) (Rep k G)).map f).hom x))
        hid
    have hy :=
      congrArg
        (fun f : V ⟶ V =>
          (((forget₂ (FDRep k G) (Rep k G)).map f).hom y))
        hid
    simp at hx hy
    exact hx.trans hy.symm
  · intro hsub
    haveI : Subsingleton V := hsub
    refine IsZero.mk ?_ ?_
    · intro Y
      refine ⟨{ default := (0 : V ⟶ Y), uniq := fun f => ?_ }⟩
      apply hom_ext
      intro x
      have hx : x = 0 := Subsingleton.elim x 0
      subst hx
      exact (map_zero _).trans (map_zero _).symm
    · intro Y
      refine ⟨{ default := (0 : Y ⟶ V), uniq := fun f => ?_ }⟩
      apply hom_ext
      intro x
      exact @Subsingleton.elim V hsub _ _

/-- A zero object has subsingleton underlying vector space.
@isnad1 id=subsingl.1h3v.s6.0650b2670475 from=translated src=- shape=83e1d4de vocab=e2a9ae8d
-/
theorem subsingleton_of_IsZero {V : FDRep k G} (hV : IsZero V) :
    Subsingleton V :=
  (isZero_iff_subsingleton V).mp hV

/-- A representation with subsingleton underlying vector space is a zero object.
@isnad1 id=iszero.0h3v.s6.74517e3e7b17 from=translated src=- shape=397c2742 vocab=e2a9ae8d
-/
theorem isZero_of_subsingleton (V : FDRep k G) [Subsingleton V] :
    IsZero V :=
  (isZero_iff_subsingleton V).mpr inferInstance

end zero

section Finrank

variable {k : Type u} {G : Type v} [Monoid G]

/-- The dimension of a finite-dimensional representation.-/
noncomputable abbrev finrank [CommRing k] (V : FDRep k G) : ℕ :=
  Module.finrank k V

/--
@isnad1 id=eq.0h5v.s6.a4ea67a521d3 from=translated src=- shape=4f8c2c9f vocab=c093e8d0
-/
lemma finrank_congr [CommRing k] {V W : FDRep k G} (e : V ≅ W) :
    V.finrank = W.finrank := by
  simpa [finrank] using LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv e)

/-- A `FDRep` is zero-dimensional iff it is a zero object.
@isnad1 id=iff.0h3v.s6.0c3cc712d989 from=translated src=- shape=861d367d vocab=d261ee6c
-/
theorem finrank_eq_zero_iff_IsZero [Field k] (V : FDRep k G) :
    V.finrank = 0 ↔ IsZero V := by
  simp only [isZero_iff_subsingleton]
  exact Module.finrank_eq_zero_iff_of_free k ↑V.V

end Finrank

section zero_object

variable {k : Type u} [CommRing k]
variable {G : Type v} [Monoid G]

/--
The zero object of `FDRep k G`: the trivial representation on the zero module
`PUnit`.-/
noncomputable abbrev zeroObj : FDRep k G :=
  FDRep.of ((Rep.trivial k G PUnit).ρ)

/--
`FDRep` has a zero object, represented by the zero module `PUnit` with the
trivial action.
@isnad1 id=haszeroo.0h2v.s5.da94bbfc8292 from=translated src=- shape=003c111b vocab=7cd64428
-/

noncomputable instance instHasZeroObject :
    HasZeroObject (FDRep k G) where
  zero :=
    ⟨zeroObj (k := k) (G := G),
      { unique_to := fun X =>
          ⟨{
            default := (0 : zeroObj (k := k) (G := G) ⟶ X)
            uniq := fun f => by
              apply hom_ext
              intro x
              have hx : x = 0 := Subsingleton.elim x 0
              subst hx
              exact (map_zero _).trans (map_zero _).symm

          }⟩
        unique_from := fun X =>
          ⟨{
            default := (0 : X ⟶ zeroObj (k := k) (G := G))
            uniq := fun f => by
              apply hom_ext
              intro x
              exact ConcreteCategory.congr_hom rfl x
          }⟩ }⟩

/-- A `FDRep` is nontrivial iff it is not a zero object.
@isnad1 id=iff.0h3v.s6.db254103d616 from=translated src=- shape=96c599bb vocab=8a6441bd
-/
theorem nontrivial_iff_not_IsZero (V : FDRep k G) :
    Nontrivial V ↔ ¬ IsZero V := by
  constructor
  · intro hnt hzero
    have hsub : Subsingleton V :=
      subsingleton_of_IsZero hzero
    exact not_subsingleton V hsub
  · intro h
    by_contra hnt
    have hsub : Subsingleton V :=
      not_nontrivial_iff_subsingleton.mp hnt
    exact h ((isZero_iff_subsingleton V).mpr hsub)

end zero_object

section Submodule

variable {k : Type u} [CommRing k] [IsNoetherianRing k]
variable {G : Type v} [Monoid G]

/--
Construct the subrepresentation associated to a stable submodule.

The assumption `hK` says that `K` is stable under the action of every group
element. The Noetherian hypothesis ensures that the submodule is finite as a
`k`-module, hence defines an object of `FDRep`.-/
noncomputable def ofSubmodule
    (X : FDRep k G)
    (K : Submodule k X)
    (hK : ∀ g : G, K ≤ K.comap (X.ρ g)) :
    FDRep k G := by
  let ρK : Representation k G K :=
  { toFun := fun g =>
      { toFun := fun x =>
          ⟨X.ρ g x.1, hK g x.2⟩
        map_add' := by
          intro x y
          ext
          simp
        map_smul' := by
          intro c x
          ext
          simp }
    map_one' := by
      ext x
      simp
    map_mul' := by
      intro g h
      ext x
      simp [map_mul] }
  haveI : Module.Finite k K :=
    Module.Finite.of_injective K.subtype Subtype.val_injective
  exact FDRep.of ρK

/--
The canonical inclusion of a stable submodule representation.-/
noncomputable def ofSubmoduleIncl
    (X : FDRep k G)
    (K : Submodule k X)
    (hK : ∀ g : G, K ≤ K.comap (X.ρ g)) :
    ofSubmodule X K hK ⟶ X :=
  FDRep.forget₂HomLinearEquiv (ofSubmodule X K hK) X
    (Rep.ofHom
      { toLinearMap := K.subtype
        isIntertwining' := by
          intro g
          ext x
          rfl })

/--
@isnad1 id=eq.1h5v.s12.6e75e7e16051 from=translated src=- shape=d6e8efc7 vocab=12acc7bc
-/
@[simp] lemma ofSubmoduleIncl_apply
    (X : FDRep k G)
    (K : Submodule k X)
    (hK : ∀ g : G, K ≤ K.comap (X.ρ g))
    (x : K) :
    (ofSubmoduleIncl X K hK).hom x = (x : X) := by
  rfl

end Submodule

section misc

/--
Postcomposition with an isomorphism gives a linear equivalence on morphism
spaces.-/
noncomputable def postcompIsoLinearEquiv
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    {X Y Z : FDRep k G}
    (e : Y ≅ Z) :
    (X ⟶ Y) ≃ₗ[k] (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by
    simp [Category.assoc]
  right_inv f := by
    simp [Category.assoc]
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp

/-- The finite-dimensional left regular representation as a Mathlib `FDRep`.-/
noncomputable def leftRegular
    (k : Type u) [CommRing k]
    (G : Type u) [Monoid G] [Fintype G] :
    FDRep k G :=
  FDRep.of ((Rep.leftRegular k G).ρ)

/--
The left regular representation sends the basis vector at `b` to the basis
vector at `a * b`.
@isnad1 id=eq.0h5v.s12.f0786f9993be from=translated src=- shape=87f6700a vocab=3bfba0d4
-/
@[simp]
lemma leftRegular_rho_single
    {k : Type u} [CommRing k]
    {G : Type u} [Monoid G] [Fintype G]
    (a b : G) (r : k) :
    ((FDRep.leftRegular k G).ρ a)
        (MonoidAlgebra.single b r)
      =
    MonoidAlgebra.single (a * b) r := by
  change
    ((Rep.leftRegular k G).ρ a)
        (MonoidAlgebra.single b r)
      =
    MonoidAlgebra.single (a * b) r
  simp only [Rep.leftRegular, Rep.ofMulAction,
    Representation.ofMulAction_single, smul_eq_mul]

/--
The trivial one-dimensional representation on the coefficient module `k`.-/
noncomputable def trivial
    (k : Type u) (G : Type v)
    [CommRing k] [Monoid G] :
    FDRep k G :=
  FDRep.of ((Rep.trivial k G k).ρ)

/--
@isnad1 id=eq.0h4v.s12.48b185a24ece from=translated src=- shape=4a192659 vocab=d5d258b3
-/
@[simp]
lemma trivial_ρ_apply
    (k : Type u) (G : Type v)
    [CommRing k] [Monoid G]
    (g : G) (x : k) :
    ((FDRep.trivial k G).ρ g) x = x := by
  change ((Rep.trivial k G k).ρ g) x = x
  simp only [Rep.trivial, Representation.isTrivial_def, LinearMap.id_coe, id_eq]

/--
@isnad1 id=ne.0h3v.s8.e99c67ffb51f from=translated src=- shape=33713c9c vocab=4a572097
-/
lemma id_ne_zero_of_nontrivial
    {k : Type u} [Field k]
    {G : Type u} [Group G]
    (V : FDRep k G) [Nontrivial V] :
    (𝟙 V : V ⟶ V) ≠ 0 := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne V
  have hlin :=
    congrArg (fun f : V ⟶ V => FDRep.homToLinearMap f) h
  have hx : x = 0 := by
    have hx' := congrArg (fun L : V →ₗ[k] V => L x) hlin
    exact (AddOpposite.op_eq_zero_iff x).mp (congrArg AddOpposite.op hx')
  have hy : y = 0 := by
    have hy' := congrArg (fun L : V →ₗ[k] V => L y) hlin
    exact (AddOpposite.op_eq_zero_iff y).mp (congrArg AddOpposite.op hy')
  exact hxy (hx.trans hy.symm)

/--
@isnad1 id=ne.0h5v.s9.a85c64a8a353 from=translated src=- shape=674781d1 vocab=a81acb84
-/
lemma isIso_hom_ne_zero_of_nontrivial
    {k : Type u} [Field k]
    {G : Type u} [Group G]
    {W V : FDRep k G} (f : W ⟶ V)
    [IsIso f] [Nontrivial V] :
    f ≠ 0 := by
  intro hf
  exact id_ne_zero_of_nontrivial V
    (by
      calc
        (𝟙 V : V ⟶ V) = inv f ≫ f := by simp
        _ = inv f ≫ 0 := by exact (IsIso.inv_comp_eq f).mpr hf
        _ = 0 := by simp)

/--
Lift an isomorphism of the underlying `Rep`s to an isomorphism of `FDRep`s.-/
noncomputable def isoOfAsRepIso
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    {V W : FDRep k G}
    (e :
      (forget₂ (FDRep k G) (Rep k G)).obj V ≅
        (forget₂ (FDRep k G) (Rep k G)).obj W) :
    V ≅ W := by
  let U : FDRep k G ⥤ Rep k G :=
    forget₂ (FDRep k G) (Rep k G)

  refine
    { hom := FDRep.forget₂HomLinearEquiv V W e.hom
      inv := FDRep.forget₂HomLinearEquiv W V e.inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }

  · apply U.map_injective
    change e.hom ≫ e.inv = 𝟙 (U.obj V)
    exact e.hom_inv_id

  · apply U.map_injective
    change e.inv ≫ e.hom = 𝟙 (U.obj W)
    exact e.inv_hom_id

noncomputable def _root_.Rep.isoOfLinearEquiv
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    {X Y : Rep k G} (e : X.V ≃ₗ[k] Y.V)
    (h : ∀ g : G, Y.ρ g ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ X.ρ g) : X ≅ Y :=
  Rep.mkIso (Representation.Equiv.mk e fun g => (h g).symm)

noncomputable abbrev asRep
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    (V : FDRep k G) : Rep k G :=
  (forget₂ (FDRep k G) (Rep k G)).obj V

/--
@isnad1 id=eq.0h3v.s6.17be8b6de0b6 from=translated src=- shape=5f9a59b5 vocab=c86fcbbc
-/
@[simp]
lemma asRep_ρ
    {k : Type u} [CommRing k]
    {G : Type u} [Monoid G]
    (V : FDRep k G) :
    (asRep V).ρ = V.ρ :=
  FDRep.forget₂_ρ V

/-- Build an isomorphism in `FDRep` from an equivariant linear equivalence.-/
noncomputable def isoOfLinearEquiv
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    {X Y : FDRep k G}
    (e : X.V ≃ₗ[k] Y.V)
    (h : ∀ g : G, Y.ρ g ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ X.ρ g) :
    X ≅ Y :=
  FDRep.isoOfAsRepIso (Rep.isoOfLinearEquiv e h)

end misc

end FDRep
