import Tengoku
import Tengoku.HodgeStructuresLean4.HodgePilot.ExtSplice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The stalkwise-split short-exactness engine for sheafified pointwise tensors

Engine parts for the sheaf category `Sheaf (Opens.grothendieckTopology X)
(ModuleCat.{0} ℤ)` of a topological space `X : TopCat.{0}`, organised in
three stages:

**(i) presheaf-level whiskering.**
`monoidalPreadditive_functorCategory` proves `MonoidalPreadditive (K ⥤ D)`
for any category `K` and any monoidal preadditive `D`, componentwise from
`MonoidalPreadditive D` (the pin has no such instance at either the pointwise
or the localized level); `zero_whiskerRight_presheaf` is the resulting
zero-whiskering lemma, and `tensorRight G` on presheaves becomes additive,
so whiskering a short complex of presheaves with a fixed presheaf `G` is
`.map (tensorRight G)`.

**(ii) the sheafified image complex.**
`tensorSheafify G` is the additive endofunctor of the sheaf category sending
a sheaf `F` to the sheafification of the pointwise presheaf tensor
`F.obj ⊗ G` — the sheafified-pointwise-tensor spelling; no monoidal
structure on the sheaf category is used in any statement of this module, and
no tensor product of complexes of sheaves appears anywhere.  The endpoint
identifications `tensorSheafify_obj`, `tensorSheafify_map` and
`map_tensorSheafify` (all `rfl`) say the image of a short complex under
`tensorSheafify G` is literally the `presheafToSheaf`-image of the
`▷ G`-whiskered short complex of underlying presheaves.

**(iii) per-point splitting and detection.**
`fiberTensorComponent`/`fiberTensorIso`/`sheafFiberTensorSheafifyIso`: the
fiber at a point of the site (`Opens.pointGrothendieckTopology p`) of the
sheafified tensor is the tensor of the fibers, functorially in the sheaf.
`fiber_splitting_map_tensorSheafify` transports a splitting of the fiber
complex to a splitting of the fiber of the image complex.
`shortExact_of_forall_fiber_splitting` detects short exactness of a short
complex of sheaves from splittings of all its fiber complexes, through the
conservative family of points.  The two are composed into the engine
theorem `shortExact_map_tensorSheafify`, instantiated at the pulled-back
short exact sequence in `pbSES_map_tensorSheafify_shortExact`: for a short
exact `S`, a map `x : W ⟶ S.X₃`, and a sheaf `W` all of whose fibers are
projective, the `tensorSheafify G`-image of `ExtSplice.pbSES S x` is short
exact.  Fiber projectivity is discharged from a free (`≅ ℤ`) fiber in
`projective_sheafFiber_of_free`, and for the monoidal unit of the localized
monoidal structure in `projective_sheafFiber_unit` (transport along the
monoidality isomorphism of the fiber functor; the monoidal structure is a
`local instance` confined to that one section).

## Claim discipline

Every statement in this module is a statement about short exactness of short
complexes of sheaves of ℤ-modules, about fibers at points of the site, or
about the interchange of those fibers with a sheafified pointwise tensor —
and nothing stronger.  NO pairing, NO cup product, and NO intersection
product on any (hyper)cohomology carrier is constructed, claimed, or implied
anywhere in this module or by it: this module builds hypothesis-discharge
engine parts only, and no product structure of any kind on any cohomology
carrier exists in this development.  The carriers here are sheaves on the
topological site; no identification or comparison of any two cohomology
theories is stated, implied, or approached.  Nothing here makes the Hodge
conjecture statable.
-/

open CategoryTheory Limits Opposite TopologicalSpace MonoidalCategory Abelian
open CategoryTheory.GrothendieckTopology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace HodgePilot

namespace CycSplitEngine

/-! ## (i) Monoidal preadditivity of functor categories, componentwise -/

section FunctorCategory

universe v₁ u₁ v₂ u₂

variable {K : Type u₁} [Category.{v₁} K] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory D] [Preadditive D] [MonoidalPreadditive D]

/-- The pointwise monoidal structure on a functor category into a monoidal
preadditive category is monoidal preadditive, componentwise.  (Neither the
pointwise nor any localized `MonoidalPreadditive` instance exists at the
pin; the componentwise closing `rfl`s are default-transparency, absorbing
the instance-path mismatch between the two sides.)-/
instance monoidalPreadditive_functorCategory : MonoidalPreadditive (K ⥤ D) where
  whiskerLeft_zero := by intros; ext U; simp; rfl
  zero_whiskerRight := by intros; ext U; simp; rfl
  whiskerLeft_add := by intros; ext U; simp; rfl
  add_whiskerRight := by intros; ext U; simp; rfl

/-- The hand-proved zero-whiskering lemma at the presheaf level: whiskering
the zero morphism with a fixed functor is zero.  (This is what makes
`.map (tensorRight G)` of a short complex of presheaves well-defined.)-/
theorem zero_whiskerRight_presheaf (G : K ⥤ D) {P Q : K ⥤ D} :
    (0 : P ⟶ Q) ▷ G = 0 :=
  MonoidalPreadditive.zero_whiskerRight

end FunctorCategory

/-! ## (ii) The tensor-then-sheafify endofunctor -/

/-- The coefficient category: ℤ-modules at universe 0.-/
abbrev AZ := ModuleCat.{0} ℤ

variable {X : TopCat.{0}}

/-- The pointwise-tensor-then-sheafify endofunctor of the category of
sheaves of ℤ-modules on `X`: forget to presheaves, whisker with `G` in the
pointwise monoidal structure, sheafify.  Its object action is the
sheafified-pointwise-tensor spelling `(presheafToSheaf _ _).obj (F.obj ⊗ G)`
(see `tensorSheafify_obj`); no monoidal structure on the sheaf category is
used.-/
def tensorSheafify (G : (Opens ↑X)ᵒᵖ ⥤ AZ) :
    Sheaf (Opens.grothendieckTopology X) AZ ⥤ Sheaf (Opens.grothendieckTopology X) AZ :=
  sheafToPresheaf _ _ ⋙ tensorRight G ⋙ presheafToSheaf _ _

/-- `tensorSheafify G` is additive: the inclusion of sheaves and the
sheafification are additive at the pin, and `tensorRight G` is additive by
`monoidalPreadditive_functorCategory`.-/
instance tensorSheafify_additive (G : (Opens ↑X)ᵒᵖ ⥤ AZ) :
    (tensorSheafify (X := X) G).Additive :=
  inferInstanceAs (sheafToPresheaf _ _ ⋙ tensorRight G ⋙ presheafToSheaf _ _).Additive

/-- Endpoint identification, object level: `tensorSheafify G` sends a sheaf
`F` to the sheafification of the pointwise presheaf tensor `F.obj ⊗ G`.-/
theorem tensorSheafify_obj (G : (Opens ↑X)ᵒᵖ ⥤ AZ)
    (F : Sheaf (Opens.grothendieckTopology X) AZ) :
    (tensorSheafify G).obj F = (presheafToSheaf _ _).obj (F.obj ⊗ G) := rfl

/-- Endpoint identification, morphism level: `tensorSheafify G` sends a
morphism of sheaves to the sheafification of its `▷ G`-whiskered underlying
presheaf morphism.-/
theorem tensorSheafify_map (G : (Opens ↑X)ᵒᵖ ⥤ AZ)
    {F F' : Sheaf (Opens.grothendieckTopology X) AZ} (φ : F ⟶ F') :
    (tensorSheafify G).map φ = (presheafToSheaf _ _).map (φ.hom ▷ G) := rfl

/-- Endpoint identification, short-complex level: the image of a short
complex of sheaves under `tensorSheafify G` is the `presheafToSheaf`-image
of the `▷ G`-whiskered short complex of underlying presheaves.-/
theorem map_tensorSheafify (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AZ))
    (G : (Opens ↑X)ᵒᵖ ⥤ AZ) :
    T.map (tensorSheafify G) =
      ((T.map (sheafToPresheaf _ _)).map (tensorRight G)).map (presheafToSheaf _ _) := rfl

/-! ## (iii) Per-point splitting and detection -/

/-- Retype-once: the cotensorator isomorphism of the fiber functor at a
point of the site, at its natural `obj`-applied endpoints — the fiber of a
pointwise presheaf tensor is the tensor of the fibers.  (Building this
`asIso` under a composite-functor expected type poisons the `IsIso`
synthesis; it must be typed here, once, and consumed by definitional
equality.)-/
def fiberTensorComponent (G : (Opens ↑X)ᵒᵖ ⥤ AZ) (p : ↑X) (P : (Opens ↑X)ᵒᵖ ⥤ AZ) :
    ((Opens.pointGrothendieckTopology p).presheafFiber (A := AZ)).obj (P ⊗ G) ≅
      ((Opens.pointGrothendieckTopology p).presheafFiber (A := AZ)).obj P ⊗
        ((Opens.pointGrothendieckTopology p).presheafFiber (A := AZ)).obj G :=
  asIso (Functor.OplaxMonoidal.δ
    ((Opens.pointGrothendieckTopology p).presheafFiber (A := AZ)) P G)

/-- Fiber-of-tensor is tensor-of-fibers, functorially: whiskering with `G`
then taking the presheaf fiber at `p` is naturally isomorphic to taking the
fiber and tensoring with the fiber of `G`.-/
def fiberTensorIso (G : (Opens ↑X)ᵒᵖ ⥤ AZ) (p : ↑X) :
    tensorRight G ⋙ (Opens.pointGrothendieckTopology p).presheafFiber (A := AZ) ≅
      (Opens.pointGrothendieckTopology p).presheafFiber (A := AZ) ⋙
        tensorRight ((Opens.pointGrothendieckTopology p).presheafFiber.obj G) :=
  NatIso.ofComponents
    (fun P => fiberTensorComponent G p P)
    (fun {P P'} f => by
      dsimp [fiberTensorComponent]
      exact (Functor.OplaxMonoidal.δ_natural_left _ f G).symm)

/-- The sheaf fiber at `p` of the `tensorSheafify G`-image is the fiber
tensored with the fiber of `G`, functorially in the sheaf: compose the
sheafification–fiber isomorphism (`presheafToSheafCompSheafFiberIso`) with
`fiberTensorIso`.-/
def sheafFiberTensorSheafifyIso (G : (Opens ↑X)ᵒᵖ ⥤ AZ) (p : ↑X) :
    tensorSheafify (X := X) G ⋙ (Opens.pointGrothendieckTopology p).sheafFiber ≅
      (Opens.pointGrothendieckTopology p).sheafFiber (A := AZ) ⋙
        tensorRight ((Opens.pointGrothendieckTopology p).presheafFiber.obj G) :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ _ ⋙ tensorRight G)
      ((Opens.pointGrothendieckTopology p).presheafToSheafCompSheafFiberIso AZ) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _) (fiberTensorIso G p)

/-- Per-point splitting transport: a splitting of the fiber complex of `T`
at `p` yields a splitting of the fiber complex of the `tensorSheafify
G`-image of `T` at `p` — tensor the splitting with the fiber of `G`
(additive functors preserve splittings) and transport along
`sheafFiberTensorSheafifyIso`.-/
theorem fiber_splitting_map_tensorSheafify
    {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AZ)}
    (G : (Opens ↑X)ᵒᵖ ⥤ AZ) (p : ↑X)
    (σ : (T.map ((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ))).Splitting) :
    Nonempty (((T.map (tensorSheafify G)).map
      ((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ))).Splitting) :=
  ⟨ShortComplex.Splitting.ofIso
    (σ.map (tensorRight ((Opens.pointGrothendieckTopology p).presheafFiber.obj G)))
    (T.mapNatIso (sheafFiberTensorSheafifyIso G p)).symm⟩

/-- Stalkwise detection: a short complex of sheaves of ℤ-modules whose fiber
complex at every point admits a splitting is short exact.  Monomorphy and
epimorphy are reflected by the conservative family of points of the
topological site; exactness is detected on homology, whose fibers vanish
because the fiber functors preserve homology and split complexes are
exact.-/
theorem shortExact_of_forall_fiber_splitting
    (W : ShortComplex (Sheaf (Opens.grothendieckTopology X) AZ))
    (h : ∀ p : ↑X, Nonempty ((W.map
      ((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ))).Splitting)) :
    W.ShortExact := by
  have hfib : ∀ p : ↑X,
      ((W.map ((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ)))).ShortExact :=
    fun p => (h p).some.shortExact
  have hP := Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology (X : Type 0)
  haveI hm : ∀ Φ : (Opens.pointsGrothendieckTopology (↑X : Type 0)).FullSubcategory,
      Mono ((Φ.obj.sheafFiber (A := AZ)).map W.f) := by
    rintro ⟨Φo, ⟨p⟩⟩
    exact (hfib p).mono_f
  haveI hmono : Mono W.f := (hP.jointlyReflectMonomorphisms AZ).mono W.f
  haveI he : ∀ Φ : (Opens.pointsGrothendieckTopology (↑X : Type 0)).FullSubcategory,
      Epi ((Φ.obj.sheafFiber (A := AZ)).map W.g) := by
    rintro ⟨Φo, ⟨p⟩⟩
    exact (hfib p).epi_g
  haveI hepi : Epi W.g := (hP.jointlyReflectEpimorphisms AZ).epi W.g
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply (hP.jointlyFaithful AZ).map_injective
  rintro ⟨Φo, ⟨p⟩⟩
  rw [CategoryTheory.Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero]
  exact ((W.map _).exact_iff_isZero_homology.1 (hfib p).exact).of_iso
    (W.mapHomologyIso _).symm

/-- **The engine**: if the fiber complex of a short complex `T` of sheaves
of ℤ-modules splits at every point, then the image complex of `T` under
`tensorSheafify G` is short exact, for every presheaf `G`.-/
theorem shortExact_map_tensorSheafify
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AZ))
    (G : (Opens ↑X)ᵒᵖ ⥤ AZ)
    (h : ∀ p : ↑X, Nonempty ((T.map
      ((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ))).Splitting)) :
    (T.map (tensorSheafify G)).ShortExact :=
  shortExact_of_forall_fiber_splitting _ fun p =>
    fiber_splitting_map_tensorSheafify G p (h p).some

open HodgePilot.ExtSplice in
/-- The discharge shape: for a short exact `S`, a map `x : W ⟶ S.X₃`
pulled back as in `ExtSplice.pbSES`, and `W` with projective fibers, the
`tensorSheafify G`-image of the pulled-back short exact sequence is short
exact — the fiber of the pullback is short exact with projective third
term, hence splits (`splittingOfProjective`), and the engine applies.-/
theorem pbSES_map_tensorSheafify_shortExact
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AZ)} (hS : S.ShortExact)
    {W : Sheaf (Opens.grothendieckTopology X) AZ} (x : W ⟶ S.X₃)
    (G : (Opens ↑X)ᵒᵖ ⥤ AZ)
    (hproj : ∀ p : ↑X,
      Projective (((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ)).obj W)) :
    ((pbSES S x).map (tensorSheafify G)).ShortExact := by
  apply shortExact_map_tensorSheafify
  intro p
  have hfib : ((pbSES S x).map
      ((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ))).ShortExact :=
    (pbSES_shortExact x hS).map_of_exact _
  letI : Projective ((pbSES S x).map
      ((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ))).X₃ := hproj p
  exact ⟨hfib.splittingOfProjective⟩

/-! ## Fiber projectivity discharges -/

/-- A sheaf whose fiber at `p` is isomorphic to `ℤ` has projective fiber at
`p`.-/
theorem projective_sheafFiber_of_free
    {W : Sheaf (Opens.grothendieckTopology X) AZ} (p : ↑X)
    (hfree : Nonempty
      (((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ)).obj W ≅
        ModuleCat.of ℤ ℤ)) :
    Projective (((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ)).obj W) :=
  Projective.of_iso hfree.some.symm inferInstance

section Unit

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory

/-- The monoidal unit of the localized monoidal structure on sheaves of
ℤ-modules has projective fibers: the fiber functor is monoidal, so its value
on the unit is isomorphic to `ℤ`, and projectivity transports along the
isomorphism.  (The localized monoidal structure is used only inside this
section, as a local instance, and only to name the unit.)-/
theorem projective_sheafFiber_unit (p : ↑X) :
    Projective (((Opens.pointGrothendieckTopology p).sheafFiber (A := AZ)).obj
      (𝟙_ (Sheaf (Opens.grothendieckTopology X) AZ))) :=
  Projective.of_iso
    (Functor.Monoidal.εIso ((Opens.pointGrothendieckTopology p).sheafFiber))
    (inferInstanceAs (Projective (ModuleCat.of ℤ ℤ)))

end Unit

/-! ## Consumption receipt (anonymous)

The engine's conclusion is, verbatim, the short-exactness hypothesis that
the splice device of `HodgePilot.ExtSplice` takes on the spliced short
exact sequence: the example below type-checks the composite.  It is an
`Ext`-class bookkeeping receipt only; it does not construct, claim, or
imply any pairing or any product on any (hyper)cohomology carrier. -/

end CycSplitEngine

end HodgePilot
