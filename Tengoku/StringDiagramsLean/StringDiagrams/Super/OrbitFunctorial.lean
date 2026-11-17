import Tengoku.StringDiagramsLean.StringDiagrams.Super.Orbit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Functoriality of the orbit construction

Further properties of the orbit supercategory `Orbit d` of a shift datum
(`StringDiagrams.Super.Orbit`), used for the 2-categorical orbit construction (the associated
graded `(Q, Π)`-2-supercategory of a `(Q, Π)`-2-category, J. Brundan, A. P. Ellis, *Monoidal
supercategories*, arXiv:1603.05928v3, §6, after Definition 6.14).

* Morphisms of shift data compose (`ShiftFunctor.id`, `ShiftFunctor.comp`), and
  `Orbit.map` is functorial (`Orbit.map_id`, `Orbit.map_comp`); the isomorphisms `Γⁱ` of a
  composite are the composites of the `Γⁱ` (`ShiftFunctor.Γ_comp_hom_app`).
* `Orbit.map` depends only on the underlying functor and `γ` (`Orbit.map_congr`).
* `Orbit.map Φ` carries the isomorphisms `σ_X : Q X ≅ X` to `σ_{F X}` up to `γ`
  (`Orbit.map_σIso_hom`).
* The shift functor `(Q, 1) : d → d` (`ShiftFunctor.self`) induces the functor `Q` of the
  orbit supercategory: `σ` is natural with respect to it (`Orbit.map_self_comp_σIso_hom`).
* A homogeneous supernatural transformation compatible with `γ` induces a homogeneous
  supernatural transformation of the induced functors (`Orbit.map_map_comp_ι`), extending
  `Orbit.mapNat` from natural to supernatural transformations.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u v₁ u₁ v₂ u₂

/-- Induction on `ℤ` from `0` by a two-sided step.
@isnad1 id=var.1h3v.s5.37b042183fa1 from=translated src=- shape=f9bec466 vocab=92f6bef1
-/
theorem Int.forall_of_step {P : ℤ → Prop} (h0 : P 0) (step : ∀ i, P (i + 1) ↔ P i) (i : ℤ) :
    P i := by
  induction i using Int.induction_on with
  | zero => exact h0
  | succ k ih => exact (step k).2 ih
  | pred k ih =>
    exact (step (-(k : ℤ) - 1)).1 (by rw [show -(k : ℤ) - 1 + 1 = -k by ring]; exact ih)

namespace ShiftFunctor

variable {R : Type w} [CommRing R]
  {S : Type u} [Category.{v} S] [Preadditive S] [Linear R S] [Supercategory R S]
  {S' : Type u₁} [Category.{v₁} S'] [Preadditive S'] [Linear R S'] [Supercategory R S']
  {S'' : Type u₂} [Category.{v₂} S''] [Preadditive S''] [Linear R S''] [Supercategory R S'']
  {d : ShiftData R S} {d' : ShiftData R S'} {d'' : ShiftData R S''}

open ShiftData

/-! ## Identity and composition -/

variable (d) in
/-- The identity morphism of shift data.-/
def id : ShiftFunctor R d d where
  F := 𝟭 S
  γ := Iso.refl _
  γ_mem _ := id_mem _

/--
@isnad1 id=eq.0h3v.s6.09d11a2e629f from=translated src=- shape=459acc1a vocab=3be57001
-/
@[simp] theorem id_F : (id d).F = 𝟭 S := rfl

/--
@isnad1 id=eq.0h4v.s8.bfe93906c790 from=translated src=- shape=7ec28bdf vocab=9d95fa26
-/
@[simp] theorem id_γ_hom_app (X : S) : (id d).γ.hom.app X = 𝟙 (d.Q.obj X) := by
  simp [id]

/-- The composite of morphisms of shift data, with `γ_{ΨΦ} = Ψ(γ_Φ) ∘ γ_Ψ Φ`.-/
def comp (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') : ShiftFunctor R d d'' where
  F := Φ.F ⋙ Ψ.F
  γ := (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft Φ.F Ψ.γ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerRight Φ.γ Ψ.F ≪≫ Functor.associator _ _ _
  γ_mem X := by
    have := comp_mem (Ψ.γ_mem (Φ.F.obj X)) (map_mem Ψ.F (Φ.γ_mem X))
    simpa using this

/--
@isnad1 id=eq.0h9v.s7.d7bbd2faf22d from=translated src=- shape=9c989366 vocab=a6132f1c
-/
@[simp] theorem comp_F (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') :
    (Φ.comp Ψ).F = Φ.F ⋙ Ψ.F := rfl

/--
@isnad1 id=eq.0h10v.s10.8f0667afa23a from=translated src=- shape=5d02e14e vocab=56c57678
-/
theorem comp_γ_hom_app (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') (X : S) :
    (Φ.comp Ψ).γ.hom.app X = Ψ.γ.hom.app (Φ.F.obj X) ≫ Ψ.F.map (Φ.γ.hom.app X) := by
  simp [comp]

/--
@isnad1 id=eq.0h10v.s10.d130bccc88ff from=translated src=- shape=0abb5870 vocab=ff969c4b
-/
theorem comp_γ_inv_app (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') (X : S) :
    (Φ.comp Ψ).γ.inv.app X = Ψ.F.map (Φ.γ.inv.app X) ≫ Ψ.γ.inv.app (Φ.F.obj X) := by
  simp [comp]

/-! ## The isomorphisms `Γⁱ` of identities and composites -/

/--
@isnad1 id=eq.0h7v.s8.9a6062ec3579 from=translated src=- shape=9298a302 vocab=12243de7
-/
theorem Γ_zero_hom_app (Φ : ShiftFunctor R d d') (X : S) : (Φ.Γ 0).hom.app X = 𝟙 _ := by
  show 𝟙 _ ≫ 𝟙 _ = _
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h7v.s8.2b043d832ae8 from=translated src=- shape=8e688e59 vocab=bcb7a54b
-/
theorem Γ_zero_inv_app (Φ : ShiftFunctor R d d') (X : S) : (Φ.Γ 0).inv.app X = 𝟙 _ := by
  rw [← cancel_epi ((Φ.Γ 0).hom.app X), Iso.hom_inv_id_app, Γ_zero_hom_app, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s8.748bc1a722c2 from=translated src=- shape=e9ddfa1a vocab=571df354
-/
theorem Γ_id_hom_app (i : ℤ) (X : S) : ((id d).Γ i).hom.app X = 𝟙 ((d.pow i).obj X) := by
  refine Int.forall_of_step (P := fun i => ((id d).Γ i).hom.app X = 𝟙 ((d.pow i).obj X))
    (Γ_zero_hom_app _ X) (fun i => ?_) i
  rw [Γ_succ_hom_app]
  constructor
  · intro h
    apply d.Q.map_injective
    rw [← cancel_epi ((d.succ i).inv.app X), ← cancel_mono ((d.succ i).hom.app X)]
    simpa using h
  · intro h
    rw [h]
    simp

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s8.f5ac7ed7ff4a from=translated src=- shape=f7272704 vocab=8765d8c4
-/
theorem Γ_id_inv_app (i : ℤ) (X : S) : ((id d).Γ i).inv.app X = 𝟙 ((d.pow i).obj X) := by
  rw [← cancel_epi (((id d).Γ i).hom.app X), Iso.hom_inv_id_app, Γ_id_hom_app]
  exact (Category.id_comp _).symm

/--
@isnad1 id=eq.0h11v.s10.1ad2c7ec9e12 from=translated src=- shape=c931c3ca vocab=723d7609
-/
theorem Γ_comp_hom_app (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') (i : ℤ) (X : S) :
    ((Φ.comp Ψ).Γ i).hom.app X = (Ψ.Γ i).hom.app (Φ.F.obj X) ≫ Ψ.F.map ((Φ.Γ i).hom.app X) := by
  refine Int.forall_of_step (P := fun i => ((Φ.comp Ψ).Γ i).hom.app X =
    (Ψ.Γ i).hom.app (Φ.F.obj X) ≫ Ψ.F.map ((Φ.Γ i).hom.app X)) ?_ (fun i => ?_) i
  · rw [Γ_zero_hom_app, Γ_zero_hom_app, Γ_zero_hom_app]; simp
  · have key : (Ψ.Γ (i + 1)).hom.app (Φ.F.obj X) ≫ Ψ.F.map ((Φ.Γ (i + 1)).hom.app X) =
        (d''.succ i).inv.app (Ψ.F.obj (Φ.F.obj X)) ≫
          d''.Q.map ((Ψ.Γ i).hom.app (Φ.F.obj X) ≫ Ψ.F.map ((Φ.Γ i).hom.app X)) ≫
            (Φ.comp Ψ).γ.hom.app ((d.pow i).obj X) ≫ (Φ.comp Ψ).F.map ((d.succ i).hom.app X) := by
      rw [Γ_succ_hom_app, Γ_succ_hom_app, comp_γ_hom_app]
      simp only [Functor.map_comp, Category.assoc, comp_F, Functor.comp_map]
      rw [← Ψ.F.map_comp_assoc ((d'.succ i).hom.app _), Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
      have n := Ψ.γ.hom.naturality ((Φ.Γ i).hom.app X)
      simp only [Functor.comp_obj, Functor.comp_map] at n
      rw [reassoc_of% n]
    rw [Γ_succ_hom_app (Φ.comp Ψ), key]
    constructor
    · intro h
      exact d''.Q.map_injective ((cancel_mono _).1 ((cancel_epi _).1 h))
    · intro h; rw [h]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h11v.s10.d852870f31bd from=translated src=- shape=168f7658 vocab=37865b84
-/
theorem Γ_comp_inv_app (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') (i : ℤ) (X : S) :
    ((Φ.comp Ψ).Γ i).inv.app X = Ψ.F.map ((Φ.Γ i).inv.app X) ≫ (Ψ.Γ i).inv.app (Φ.F.obj X) := by
  rw [← cancel_epi (((Φ.comp Ψ).Γ i).hom.app X), Iso.hom_inv_id_app, Γ_comp_hom_app]
  simp only [Category.assoc]
  rw [← Ψ.F.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

/--
@isnad1 id=eq.0h10v.s12.72e4b1b578b5 from=translated src=- shape=7454a83c vocab=88185ea4
-/
@[simp] theorem famMapₗ_apply (Φ : ShiftFunctor R d d') {m : ℤ} {X Y : S} (f : d.Fam R m X Y) :
    ((Φ.famMapₗ m X Y f : d'.Fam R m (Φ.F.obj X) (Φ.F.obj Y)) : d'.FamAll _ _) =
      Φ.famMap f.1 := rfl

/--
@isnad1 id=eq.0h6v.s7.7bc5eed7db73 from=translated src=- shape=d6551fd2 vocab=b19abec9
-/
theorem famMap_id {X Y : S} (f : d.FamAll X Y) : (id d).famMap f = f := by
  ext i j
  simp [famMap, Γ_id_hom_app, Γ_id_inv_app]

/--
@isnad1 id=eq.0h12v.s8.9fe79197a6f4 from=translated src=- shape=4e768a26 vocab=0e9ebe50
-/
theorem famMap_comp (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') {X Y : S}
    (f : d.FamAll X Y) : (Φ.comp Ψ).famMap f = Ψ.famMap (Φ.famMap f) := by
  ext i j
  simp [famMap, Γ_comp_hom_app, Γ_comp_inv_app]

/-! ## The shift functor `(Q, 1)` -/

variable (d) in
/-- The functor `Q` itself, as a morphism of shift data `d → d` with `γ = 1`.-/
def self : ShiftFunctor R d d where
  F := d.Q
  γ := Iso.refl _
  γ_mem _ := id_mem _

/--
@isnad1 id=eq.0h3v.s6.341f95801b07 from=translated src=- shape=e68a4923 vocab=a0766315
-/
@[simp] theorem self_F : (self d).F = d.Q := rfl

/--
@isnad1 id=eq.0h4v.s8.3fe324c4e69e from=translated src=- shape=329fb568 vocab=9aa848df
-/
@[simp] theorem self_γ_hom_app (X : S) : (self d).γ.hom.app X = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `Γⁱ` of `(Q, 1)` is the comparison `Qⁱ Q ≅ Qⁱ⁺¹ ≅ Q Qⁱ`.
@isnad1 id=eq.0h5v.s9.449c4a896788 from=translated src=- shape=6ed29dc8 vocab=da3c8b0a
-/
theorem Γ_self_hom_app (i : ℤ) (X : S) :
    ((self d).Γ i).hom.app X ≫ (d.succ i).hom.app X = (d.comm i).hom.app X := by
  refine Int.forall_of_step (P := fun i => ((self d).Γ i).hom.app X ≫ (d.succ i).hom.app X =
    (d.comm i).hom.app X) ?_ (fun i => ?_) i
  · rw [Γ_zero_hom_app, comm_zero_hom_app, Category.id_comp]; rfl
  · rw [Γ_succ_hom_app, comm_succ]
    simp only [self_F, self_γ_hom_app, Functor.comp_obj, Category.id_comp, Category.assoc,
      cancel_epi]
    constructor
    · intro h
      apply d.Q.map_injective
      rw [← cancel_mono ((d.succ (i + 1)).hom.app X), ← h, d.Q.map_comp, Category.assoc]
    · intro h
      rw [← h, d.Q.map_comp, Category.assoc]

/-! ## Supernatural transformations compatible with `γ` -/

/-- A family of morphisms natural with respect to even morphisms and compatible with `γ` is
compatible with all the `Γⁱ` (the version of `ShiftFunctor.Γ_hom_app_comp_app` for
supernatural transformations).
@isnad1 id=eq.2h10v.s11.4cd0b1e162e1 from=translated src=- shape=34b09259 vocab=3f5a52c5
-/
theorem Γ_hom_app_comp_of_even {Φ Ψ : ShiftFunctor R d d'} (x : ∀ X, Φ.F.obj X ⟶ Ψ.F.obj X)
    (hnat : ∀ {X Y : S} (g : X ⟶ Y), g ∈ parity (R := R) X Y 0 →
      Φ.F.map g ≫ x Y = x X ≫ Ψ.F.map g)
    (hx : ∀ X, Φ.γ.hom.app X ≫ x (d.Q.obj X) = d'.Q.map (x X) ≫ Ψ.γ.hom.app X)
    (i : ℤ) (X : S) :
    (Φ.Γ i).hom.app X ≫ x ((d.pow i).obj X) = (d'.pow i).map (x X) ≫ (Ψ.Γ i).hom.app X := by
  refine Int.forall_of_step (P := fun i => (Φ.Γ i).hom.app X ≫ x ((d.pow i).obj X) =
    (d'.pow i).map (x X) ≫ (Ψ.Γ i).hom.app X) ?_ (fun i => ?_) i
  · rw [Γ_zero_hom_app, Γ_zero_hom_app]; simp
  · have e1 : (Φ.Γ (i + 1)).hom.app X ≫ x ((d.pow (i + 1)).obj X) =
        (d'.succ i).inv.app (Φ.F.obj X) ≫
          d'.Q.map ((Φ.Γ i).hom.app X ≫ x ((d.pow i).obj X)) ≫
            Ψ.γ.hom.app ((d.pow i).obj X) ≫ Ψ.F.map ((d.succ i).hom.app X) := by
      rw [Γ_succ_hom_app]
      simp only [Category.assoc, CategoryTheory.Functor.map_comp]
      rw [hnat _ (d.succ_hom_mem i X)]
      erw [reassoc_of% (hx ((d.pow i).obj X))]
    have e2 : (d'.pow (i + 1)).map (x X) ≫ (Ψ.Γ (i + 1)).hom.app X =
        (d'.succ i).inv.app (Φ.F.obj X) ≫
          d'.Q.map ((d'.pow i).map (x X) ≫ (Ψ.Γ i).hom.app X) ≫
            Ψ.γ.hom.app ((d.pow i).obj X) ≫ Ψ.F.map ((d.succ i).hom.app X) := by
      rw [Γ_succ_hom_app, CategoryTheory.Functor.map_comp, Category.assoc]
      have n := (d'.succ i).inv.naturality (x X)
      simp only [Functor.comp_obj, Functor.comp_map] at n
      rw [reassoc_of% n]
    show _ = _ ↔ _ = _
    rw [e1, e2, cancel_epi, cancel_mono]
    exact ⟨fun h => d'.Q.map_injective h, fun h => by rw [h]⟩

/--
@isnad1 id=eq.2h10v.s11.8452f097726b from=translated src=- shape=f3ac22d8 vocab=73bbb0a5
-/
theorem Γ_inv_app_comp_of_even {Φ Ψ : ShiftFunctor R d d'} (x : ∀ X, Φ.F.obj X ⟶ Ψ.F.obj X)
    (hnat : ∀ {X Y : S} (g : X ⟶ Y), g ∈ parity (R := R) X Y 0 →
      Φ.F.map g ≫ x Y = x X ≫ Ψ.F.map g)
    (hx : ∀ X, Φ.γ.hom.app X ≫ x (d.Q.obj X) = d'.Q.map (x X) ≫ Ψ.γ.hom.app X)
    (i : ℤ) (X : S) :
    (Φ.Γ i).inv.app X ≫ (d'.pow i).map (x X) = x ((d.pow i).obj X) ≫ (Ψ.Γ i).inv.app X := by
  rw [← cancel_mono ((Ψ.Γ i).hom.app X), Category.assoc, ← Γ_hom_app_comp_of_even x hnat hx,
    Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

end ShiftFunctor

namespace Orbit

open ShiftData ShiftFunctor GradedSupercategory

variable {R : Type w} [CommRing R]
  {S : Type u} [Category.{v} S] [Preadditive S] [Linear R S] [Supercategory R S]
  {S' : Type u₁} [Category.{v₁} S'] [Preadditive S'] [Linear R S'] [Supercategory R S']
  {S'' : Type u₂} [Category.{v₂} S''] [Preadditive S''] [Linear R S''] [Supercategory R S'']
  {d : ShiftData R S} {d' : ShiftData R S'} {d'' : ShiftData R S''}

/-! ## Functoriality of `Orbit.map` -/

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h12v.s9.cd3f55469430 from=translated src=- shape=0460c079 vocab=09ec3165
-/
theorem map_map_comp (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') {X Y : Orbit d}
    (x : X ⟶ Y) : (map Ψ).map ((map Φ).map x) = (map (Φ.comp Ψ)).map x := by
  induction x using Hom.induction_on with
  | zero => simp
  | add x y hx hy => rw [(map _).map_add, (map _).map_add, (map _).map_add, hx, hy]
  | lof m f =>
    rw [map_map_lof]
    erw [map_map_lof, map_map_lof]
    congr 1
    exact Subtype.ext (famMap_comp Φ Ψ f.1).symm

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h9v.s8.765977952187 from=translated src=- shape=1d03fb7f vocab=ea1d2fea
-/
theorem map_comp (Φ : ShiftFunctor R d d') (Ψ : ShiftFunctor R d' d'') :
    map (Φ.comp Ψ) = map Φ ⋙ map Ψ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y x => by
    simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    exact (map_map_comp Φ Ψ x).symm

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h6v.s8.40ef5ef0ff7b from=translated src=- shape=903389c0 vocab=420d37f1
-/
theorem map_map_id {X Y : Orbit d} (x : X ⟶ Y) : (map (ShiftFunctor.id d)).map x = x := by
  induction x using Hom.induction_on with
  | zero => simp
  | add x y hx hy => rw [(map _).map_add, hx, hy]
  | lof m f =>
    rw [map_map_lof]
    congr 1
    exact Subtype.ext (famMap_id f.1)

/-- `Orbit.map` depends only on the functor and on `γ`.
@isnad1 id=eq.2h7v.s9.1bacaf47ab14 from=translated src=- shape=466f4f31 vocab=0ccea87a
-/
theorem map_congr {Φ Ψ : ShiftFunctor R d d'} (hF : Φ.F = Ψ.F)
    (hγ : ∀ X, Φ.γ.hom.app X ≫ eqToHom (congrArg (fun F : S ⥤ S' => F.obj (d.Q.obj X)) hF) =
      eqToHom (congrArg (fun F : S ⥤ S' => d'.Q.obj (F.obj X)) hF) ≫ Ψ.γ.hom.app X) :
    map Φ = map Ψ := by
  cases Φ with
  | mk F γ hγm =>
    cases Ψ with
    | mk G γ' hγm' =>
      dsimp only at hF hγ
      subst hF
      obtain rfl : γ = γ' := by
        ext X
        simpa using hγ X
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- `Orbit.map Φ` on the morphisms of degree zero coming from `S` (`Orbit.ι_comp_map`,
componentwise).
@isnad1 id=eq.0h9v.s9.8840c3b08cdc from=translated src=- shape=15a6d627 vocab=a08cbe55
-/
theorem map_ι_map (Φ : ShiftFunctor R d d') {X Y : S} (g : X ⟶ Y) :
    (map Φ).map ((ι d).map g) = (ι d').map (Φ.F.map g) := by
  have := CategoryTheory.Functor.congr_hom (ι_comp_map Φ) g
  simpa only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp] using this

/-- The naturality of `Orbit.mapNat`, componentwise.
@isnad1 id=eq.1h11v.s10.366dcf91fd14 from=translated src=- shape=64720ecd vocab=2105cfc2
-/
theorem map_map_comp_ι_map {Φ Ψ : ShiftFunctor R d d'} (x : Φ.F ⟶ Ψ.F)
    (hx : ∀ X, Φ.γ.hom.app X ≫ x.app (d.Q.obj X) = d'.Q.map (x.app X) ≫ Ψ.γ.hom.app X)
    {X Y : Orbit d} (z : X ⟶ Y) :
    (map Φ).map z ≫ (ι d').map (x.app Y.obj) = (ι d').map (x.app X.obj) ≫ (map Ψ).map z :=
  (mapNat x hx).naturality z

/-- `Orbit.map` depends only on the functor and on `γ`, with the functor equality given
objectwise.
@isnad1 id=eq.3h7v.s10.e1cddf0e4a0a from=translated src=- shape=f813b23d vocab=cbd77ad6
-/
theorem map_congr' {Φ Ψ : ShiftFunctor R d d'} (hobj : ∀ X, Φ.F.obj X = Ψ.F.obj X)
    (hmap : ∀ {X Y : S} (g : X ⟶ Y),
      Φ.F.map g = eqToHom (hobj X) ≫ Ψ.F.map g ≫ eqToHom (hobj Y).symm)
    (hγ : ∀ X, Φ.γ.hom.app X ≫ eqToHom (hobj (d.Q.obj X)) =
      eqToHom (congrArg d'.Q.obj (hobj X)) ≫ Ψ.γ.hom.app X) :
    map Φ = map Ψ :=
  map_congr (CategoryTheory.Functor.ext hobj fun _ _ g => hmap g) fun X => hγ X

/-! ## The isomorphisms `σ` -/

/-- `Orbit.map Φ` carries `σ_X` to `σ_{F X}`, up to `γ`.
@isnad1 id=eq.0h4v.s8.b4df9223fcec from=translated src=- shape=72dbb45e vocab=54b6574a
-/
theorem _root_.StringDiagrams.ShiftData.succ_zero_hom_app (X : S) :
    (d.succ 0).hom.app X = 𝟙 (d.Q.obj X) := rfl

/--
@isnad1 id=eq.0h4v.s8.d36aafeb196c from=translated src=- shape=b358724c vocab=e2002354
-/
theorem _root_.StringDiagrams.ShiftData.succ_zero_inv_app (X : S) :
    (d.succ 0).inv.app X = 𝟙 (d.Q.obj X) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h7v.s10.f0fdb2282494 from=translated src=- shape=411aca24 vocab=48d773d1
-/
theorem map_σIso_hom (Φ : ShiftFunctor R d d') (X : Orbit d) :
    (map Φ).map (σIso X).hom =
      (ι d').map (Φ.γ.inv.app X.obj) ≫ (σIso (⟨Φ.F.obj X.obj⟩ : Orbit d')).hom := by
  show (map Φ).map (d.lof (-1) _ _ _) = d'.compL _ _ _ (d'.lof 0 _ _ _) (d'.lof (-1) _ _ _)
  rw [map_map_lof, compL_lof_lof]
  refine d'.lof_congr (by norm_num) ?_
  rw [famCompₗ_apply]
  refine Fam.eq_of_entry (Φ.famMap_mem (d.famσ_mem X.obj))
    (by simpa using famComp_mem (d'.mapFam _).2 (d'.famσ_mem _)) (i₀ := 0) (j₀ := 0 + 1)
    (by norm_num) ?_
  simp only [famMapₗ_apply, famMap, famComp, mapFam]
  rw [show (0 : ℤ) - 0 = 0 by ring, diagFam_self, famσ_succ, famσ_succ, comm_zero_hom_app,
    comm_zero_hom_app, Γ_zero_hom_app, Γ_succ_inv_app, Γ_zero_inv_app, succ_zero_hom_app,
    succ_zero_inv_app]
  simp
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h7v.s10.42917e0343a9 from=translated src=- shape=66c9b5b7 vocab=48d773d1
-/
theorem map_σIso_inv (Φ : ShiftFunctor R d d') (X : Orbit d) :
    (map Φ).map (σIso X).inv =
      (σIso (⟨Φ.F.obj X.obj⟩ : Orbit d')).inv ≫ (ι d').map (Φ.γ.hom.app X.obj) := by
  rw [← cancel_epi ((map Φ).map (σIso X).hom), ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, map_σIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `σ` is natural with respect to the functor `Orbit.map (ShiftFunctor.self d)` induced by
`(Q, 1)`; equivalently, this functor is the functor `Q` of the orbit supercategory.
@isnad1 id=eq.0h6v.s9.d98d8391b32f from=translated src=- shape=dd915aa4 vocab=49354a0c
-/
theorem map_self_comp_σIso_hom {X Y : Orbit d} (z : X ⟶ Y) :
    (map (ShiftFunctor.self d)).map z ≫ (σIso Y).hom = (σIso X).hom ≫ z := by
  induction z using Hom.induction_on with
  | zero => simp
  | add x y hx hy => rw [(map _).map_add, Preadditive.add_comp, Preadditive.comp_add, hx, hy]
  | lof m f =>
    show d.compL _ _ _ ((map (ShiftFunctor.self d)).map (d.lof m _ _ f)) (d.lof (-1) _ _ _) =
      d.compL _ _ _ (d.lof (-1) _ _ _) (d.lof m _ _ f)
    rw [map_map_lof]
    erw [compL_lof_lof, compL_lof_lof]
    refine d.lof_congr (by ring) ?_
    rw [famCompₗ_apply, famCompₗ_apply]
    ext i k
    simp only [famComp, famMapₗ_apply]
    by_cases h : i - m + 1 = k
    · subst h
      rw [famσ_succ, show i - -1 = i + 1 by ring, famσ_succ]
      show (((ShiftFunctor.self d).Γ i).hom.app X.obj ≫ d.Q.map (f.1 i (i - m)) ≫
        ((ShiftFunctor.self d).Γ (i - m)).inv.app Y.obj) ≫ (d.comm (i - m)).hom.app Y.obj =
          (d.comm i).hom.app X.obj ≫ f.1 (i + 1) (i - m + 1)
      rw [Fam.compat f.2, ← Γ_self_hom_app, ← Γ_self_hom_app]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
    · have h1 : d.famσ Y.obj (i - m) k = 0 := by rw [famσ, dite_eq_right (by omega)]
      have h2 : f.1 (i - -1) k = 0 := Fam.eq_zero f.2 (by omega)
      rw [h1, h2, Limits.comp_zero, Limits.comp_zero]

/-! ## Supernatural transformations -/

set_option backward.isDefEq.respectTransparency false in
/-- **Supernatural transformations of orbit functors.** A homogeneous supernatural
transformation `x : F ⇒ G` of parity `p` compatible with `γ` induces a supernatural
transformation `ι x : F̃ ⇒ G̃` of parity `p`: for a morphism `z` of parity `q` of the orbit
supercategory, `F̃ z ∘ ι x = (-1)^{pq} ι x ∘ G̃ z`.
@isnad1 id=eq.3h13v.s12.404dc6e96ed1 from=translated src=- shape=97828174 vocab=0befe401
-/
theorem map_map_comp_ι {Φ Ψ : ShiftFunctor R d d'} {p : ZMod 2} {x : ∀ X, Φ.F.obj X ⟶ Ψ.F.obj X}
    (hx : IsSupernatural R p x)
    (hγ : ∀ X, Φ.γ.hom.app X ≫ x (d.Q.obj X) = d'.Q.map (x X) ≫ Ψ.γ.hom.app X)
    {X Y : Orbit d} {q : ZMod 2} {z : X ⟶ Y} (hz : z ∈ parity (R := R) X Y q) :
    (map Φ).map z ≫ (ι d').map (x Y.obj) =
      sign R (p * q) • ((ι d').map (x X.obj) ≫ (map Ψ).map z) := by
  have hnat : ∀ {X Y : S} (g : X ⟶ Y), g ∈ parity (R := R) X Y 0 →
      Φ.F.map g ≫ x Y = x X ≫ Ψ.F.map g := fun g hg => by
    rw [hx.naturality hg, mul_zero, sign_zero, one_smul]
  rw [← d.projHom_of_mem hz]
  clear hz
  induction z using Hom.induction_on with
  | zero => simp
  | add z z' hz hz' =>
    rw [map_add, (map _).map_add, (map _).map_add, Preadditive.add_comp, Preadditive.comp_add,
      smul_add, hz, hz']
  | lof m f =>
    rw [projHom_lof]
    show d'.compL _ _ _ ((map Φ).map (d.lof m _ _ _)) (d'.lof 0 _ _ _) =
      sign R (p * q) • d'.compL _ _ _ (d'.lof 0 _ _ _) ((map Ψ).map (d.lof m _ _ _))
    rw [map_map_lof, map_map_lof]
    erw [compL_lof_lof, compL_lof_lof]
    rw [← map_smul]
    refine d'.lof_congr (by ring) ?_
    rw [Submodule.coe_smul, famCompₗ_apply, famCompₗ_apply]
    ext i k
    simp only [famComp, mapFam, FamAll.smul_apply, famMapₗ_apply]
    rw [show i - 0 = i by ring, diagFam_self]
    by_cases h : i - m = k
    · subst h
      rw [diagFam_self]
      simp only [famMap, famProj_apply, Category.assoc]
      rw [Γ_inv_app_comp_of_even x hnat hγ,
        reassoc_of% (hx.naturality (proj_mem q (f.1 i (i - m))))]
      simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
      rw [← Category.assoc ((Φ.Γ i).hom.app _), Γ_hom_app_comp_of_even x hnat hγ, Category.assoc]
    · have h1 : Ψ.famMap (d.famProj R q m X.obj Y.obj f).1 i k = 0 := by
        rw [famMap, Fam.eq_zero (d.famProj R q m X.obj Y.obj f).2 (by omega)]; simp
      rw [h1, Limits.comp_zero, smul_zero]
      simp [diagFam, h]

end Orbit

end StringDiagrams

end
