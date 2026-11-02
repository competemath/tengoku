import Tengoku.HodgeStructuresLean4.HodgePilot.ContractibleSingular
import Tengoku.Seed.Topology.Homotopy.LocallyContractible
import Tengoku.Seed.Topology.Sheaves.Abelian
import Tengoku.Seed.Topology.Sheaves.Sheafify
import Tengoku.Seed.Topology.Sheaves.Stalks
import Tengoku.Seed.CategoryTheory.Sites.ConstantSheaf
import Tengoku.Seed.CategoryTheory.Sites.Abelian
import Tengoku.Seed.Algebra.Homology.ShortComplex.Ab
import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sheafified singular cochains against the constant `ℚ`-sheaf: stalkwise exactness in positive degrees, stalkwise-injective augmentation

For a topological space `X` this file constructs, on the site `Opens X`:

1. the **singular cochain presheaf complex** `singularPresheafComplex X` — the
   restriction of the house singular cochain functor
   (`HodgePilot.SingularCohomology.singularCochainFunctor`, with abelian-group
   carrier via `forget₂ (ModuleCat ℚ) AddCommGrpCat`) along the subspace
   inclusions of opens; the degreewise presheaves are genuine singular cochain
   presheaves;
2. its termwise sheafification `sheafifiedCochainComplex X`, a cochain complex
   of abelian sheaves obtained by applying `presheafToSheaf`; these objects are
   called **sheafified cochain sheaves** — they are *not* singular cochain
   objects, and no property of singular cochains is attributed to them;
3. the **augmentation** `augmentationSheaf X : constQSheaf X ⟶ 𝒮⁰` from the
   constant abelian sheaf with values `ULift ℚ` (the house coefficient
   spelling on the site `Opens X`), induced by the presheaf-level augmentation
   sending `q` to `q` times the unit cochain (the pullback of a chosen
   0-cochain on the one-point space);
4. **the theorem** (`exactAt_sheafifiedCochainComplex`): on a strongly locally
   contractible space, the sheafified cochain complex is exact in every degree
   `n ≠ 0` — stalkwise, a cocycle germ is represented over some open, shrunk
   into a contractible basis neighbourhood, and killed there by the
   contractible-space vanishing of `HodgePilot.ContractibleSingular`; together
   with `stalk_augmentationSheaf_injective` (the stalks of the augmentation
   are injective, on any space), this is the stalkwise-exactness part of the
   resolution statement at degree `≥ 1` and at the injectivity spot.

The entitled claim of this file, in full: *the constant `ℚ`-sheaf on a
strongly locally contractible space is resolved by the termwise-sheafified
singular cochain complex, in the sense of stalkwise exactness of the augmented
complex, at exactly the scope proven here* — namely exactness of the
sheafified complex in every positive degree and injectivity of the
augmentation on stalks.  **What remains open here**: exactness of the
augmented complex at the `𝒮⁰` spot (that a degree-0 cocycle germ is locally a
constant cochain) is *not* proven in this file; `Γ`-acyclicity of the
sheafified cochain sheaves, the presheaf-versus-sheaf global-sections step,
and the comparison itself are not approached.  **Nothing here identifies
sheaf cohomology with singular cohomology in any degree**; no sheaf
cohomology group of any kind is mentioned, computed, or related to another,
and no statement about the cohomology of the sheafified complex is made.  The
word "singular" below refers exclusively to the genuine singular-cochain
objects (the presheaf level and the auxiliary complexes on subspaces); the
sheafified objects are never called singular.  Everything is at universe `0`,
forced by the `ModuleCat.{0} ℚ` coefficients of the house carrier.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology
  HodgePilot.SingularCohomology HodgePilot.ContractibleSingular

noncomputable section

namespace HodgePilot.SingularResolution

/-! ## The unit cochain

A canonical 0-cochain on each space, pulled back from a chosen 0-cochain on
the one-point space along the unique map.  Because the degree-`(0,1)`
differential of the one-point cochain complex vanishes, the unit cochain is a
cocycle on every space, functorially — this is the presheaf-level augmentation
datum. -/

/-- The house singular chain functor at `ℚ`-coefficients (the complex the
house cochain functor dualizes).-/
abbrev chainsFunctor : TopCat.{0} ⥤ ChainComplex QMod ℕ :=
  (singularChainComplexFunctor QMod).obj Qcoef

/-- The unique map to the one-point space.-/
def terminalMap (U : TopCat.{0}) : U ⟶ pointSpace :=
  TopCat.ofHom ⟨fun _ => (), continuous_const⟩

lemma comp_terminalMap {V U : TopCat.{0}} (f : V ⟶ U) :
    f ≫ terminalMap U = terminalMap V :=
  TopCat.hom_ext (ContinuousMap.ext fun _ => rfl)

lemma terminalMap_pointSpace : terminalMap pointSpace = 𝟙 pointSpace :=
  TopCat.hom_ext (ContinuousMap.ext fun _ => rfl)

/-- A nonzero functional on the point module: the preimage of `1 : ℚ` under
the house evaluation equivalence of `HodgePilot.ContractibleSingular`.-/
def pointModuleSum : pointModule ⟶ Qcoef :=
  dualPointModuleEquiv.symm 1

set_option backward.isDefEq.respectTransparency false in
lemma pointModuleSum_ne_zero : pointModuleSum ≠ 0 := by
  intro h
  have h1 := congrArg dualPointModuleEquiv h
  rw [show dualPointModuleEquiv pointModuleSum = 1 from
    dualPointModuleEquiv.apply_symm_apply 1, map_zero] at h1
  exact one_ne_zero h1

/-- The singular chain complex of the one-point space is isomorphic to the
alternating-constant complex on the point module (Mathlib's
totally-disconnected isomorphism, exactly as consumed in
`HodgePilot.ContractibleSingular`).-/
abbrev pointChainsIso :
    chainsFunctor.obj pointSpace ≅ ChainComplex.alternatingConst.obj pointModule :=
  singularChainComplexFunctorIsoOfTotallyDisconnectedSpace QMod Qcoef pointSpace

/-- The degree-`(1,0)` differential of the singular chain complex of the
one-point space vanishes (transported from the alternating-constant complex,
whose odd-to-even differentials are zero).-/
lemma d_one_zero_pointChains : (chainsFunctor.obj pointSpace).d 1 0 = 0 := by
  have halt : (ChainComplex.alternatingConst.obj pointModule).d 1 0 = 0 := by
    simp [ChainComplex.alternatingConst, HomologicalComplex.alternatingConst]
    rfl
  have h := pointChainsIso.hom.comm 1 0
  rw [halt, comp_zero] at h
  haveI : IsIso (pointChainsIso.hom.f 0) :=
    inferInstanceAs
      (IsIso ((HomologicalComplex.eval QMod (ComplexShape.down ℕ) 0).mapIso pointChainsIso).hom)
  rw [← cancel_mono (pointChainsIso.hom.f 0), zero_comp]
  exact h.symm

/-- The chosen 0-cochain on the one-point space, as a morphism: the
sum-of-coefficients functional transported along the totally-disconnected
isomorphism.-/
def pointUnitCochainHom : (chainsFunctor.obj pointSpace).X 0 ⟶ Qcoef :=
  pointChainsIso.hom.f 0 ≫ pointModuleSum

/-- The unit 0-cochain on a space `U`, as a morphism: the pullback of the
point cochain along the unique map to the point.-/
def unitCochainHom (U : TopCat.{0}) : (chainsFunctor.obj U).X 0 ⟶ Qcoef :=
  (chainsFunctor.map (terminalMap U)).f 0 ≫ pointUnitCochainHom

lemma unitCochainHom_comp {V U : TopCat.{0}} (f : V ⟶ U) :
    (chainsFunctor.map f).f 0 ≫ unitCochainHom U = unitCochainHom V := by
  show (chainsFunctor.map f).f 0 ≫ (chainsFunctor.map (terminalMap U)).f 0 ≫ pointUnitCochainHom
      = (chainsFunctor.map (terminalMap V)).f 0 ≫ pointUnitCochainHom
  rw [← Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp, comp_terminalMap]

lemma d_comp_unitCochainHom (U : TopCat.{0}) :
    (chainsFunctor.obj U).d 1 0 ≫ unitCochainHom U = 0 := by
  show (chainsFunctor.obj U).d 1 0 ≫ (chainsFunctor.map (terminalMap U)).f 0 ≫ pointUnitCochainHom = 0
  rw [← Category.assoc, ← (chainsFunctor.map (terminalMap U)).comm 1 0, Category.assoc,
    show (chainsFunctor.obj pointSpace).d 1 0 ≫ pointUnitCochainHom
      = (0 : _ ⟶ _) ≫ pointUnitCochainHom from by rw [d_one_zero_pointChains],
    zero_comp, comp_zero]

/-! ## The singular cochain presheaf complex and its termwise sheafification -/

/-- The house singular cochain functor with abelian-group carrier: the
`ℚ`-linear singular cochain complex followed by
`forget₂ (ModuleCat ℚ) AddCommGrpCat` (the carrier the sheaf theory on
`Opens X` consumes).-/
def singularCochainAbFunctor : TopCat.{0}ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  singularCochainFunctor ⋙
    (forget₂ QMod AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The restriction of the singular cochain functor along the subspace
inclusions of opens: a presheaf of cochain complexes on `Opens X`
(contravariance is inherited from `singularCochainFunctor`).-/
def singularCochainOpensFunctor (X : TopCat.{0}) :
    (Opens X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  (Opens.toTopCat X).op ⋙ singularCochainAbFunctor

/-- The **singular cochain presheaf complex** on `Opens X`: the presheaf of
cochain complexes `singularCochainOpensFunctor`, reorganized as a cochain
complex of abelian presheaves.  Each degree is a genuine singular cochain
presheaf; no sheaf condition holds or is claimed at this level.-/
def singularPresheafComplex (X : TopCat.{0}) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{0} X) ℕ where
  X n := singularCochainOpensFunctor X ⋙
    HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.up ℕ) n
  d i j :=
    { app := fun U => ((singularCochainOpensFunctor X).obj U).d i j
      naturality := fun _ _ f => ((singularCochainOpensFunctor X).map f).comm i j }
  shape i j hij := by
    refine NatTrans.ext (funext fun U => ?_)
    exact ((singularCochainOpensFunctor X).obj U).shape i j hij
  d_comp_d' i j k _ _ := by
    refine NatTrans.ext (funext fun U => ?_)
    exact ((singularCochainOpensFunctor X).obj U).d_comp_d i j k

/-- The termwise sheafification of the singular cochain presheaf complex: a
cochain complex of abelian **sheafified cochain sheaves** on `X`.  These
objects are sheafifications; they are not singular cochain objects, and
nothing about their cohomology is stated anywhere in this file.-/
def sheafifiedCochainComplex (X : TopCat.{0}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj (singularPresheafComplex X)

instance instPresheafToSheafAdditive (X : TopCat.{0}) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).Additive :=
  presheafToSheaf_additive

instance instPresheafToSheafPreservesZeroMorphisms (X : TopCat.{0}) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-! ## The augmentation -/

/-- The constant abelian presheaf with values `ULift ℚ` on `Opens X` (the
house coefficient spelling: `ULift` keeps the coefficients in the universe of
the site).-/
def constQPresheaf (X : TopCat.{0}) : TopCat.Presheaf AddCommGrpCat.{0} X :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{0} ℚ))

/-- The constant abelian **sheaf** with values `ULift ℚ` on `X`, in exactly
the house constant-sheaf coefficient spelling (`constantSheaf` on the site
`Opens X` at `AddCommGrpCat.of (ULift ℚ)`).-/
def constQSheaf (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift.{0} ℚ))

/-- The unit cochain over an open, as an element of the degree-0 singular
cochain presheaf (the carrier of the `ℚ`-dual is the hom-module, so the
morphism *is* the element).-/
def unitCochainSection (X : TopCat.{0}) (U : Opens X) :
    ((singularPresheafComplex X).X 0).obj (op U) :=
  unitCochainHom ((Opens.toTopCat X).obj U)

/-- A rational multiple of the unit cochain, as an element of the degree-0
singular cochain presheaf (the scalar action is taken on the hom-module
carrier).-/
def smulUnitSection (X : TopCat.{0}) (U : Opens X) (q : ℚ) :
    ((singularPresheafComplex X).X 0).obj (op U) :=
  (q • unitCochainHom ((Opens.toTopCat X).obj U) :
    (chainsFunctor.obj ((Opens.toTopCat X).obj U)).X 0 ⟶ Qcoef)

set_option backward.isDefEq.respectTransparency false in
lemma smulUnitSection_zero (X : TopCat.{0}) (U : Opens X) : smulUnitSection X U 0 = 0 :=
  zero_smul ℚ (unitCochainHom ((Opens.toTopCat X).obj U))

set_option backward.isDefEq.respectTransparency false in
lemma smulUnitSection_add (X : TopCat.{0}) (U : Opens X) (a b : ℚ) :
    smulUnitSection X U (a + b) = smulUnitSection X U a + smulUnitSection X U b :=
  add_smul a b (unitCochainHom ((Opens.toTopCat X).obj U))

set_option backward.isDefEq.respectTransparency false in
/-- The element-level form of `unitCochainHom_comp`: pulling the unit cochain
back along a continuous map yields the unit cochain (the `ℚ`-dual acts by
precomposition, definitionally).-/
lemma unitCochain_map {V U : TopCat.{0}} (f : V ⟶ U) :
    (singularCochainFunctor.map f.op).f 0 (unitCochainHom U) = unitCochainHom V :=
  unitCochainHom_comp f

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of unit-cochain multiples along an inclusion of opens is
again the corresponding unit-cochain multiple.-/
lemma presheafRes_smulUnitSection (X : TopCat.{0}) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (q : ℚ) :
    ((singularPresheafComplex X).X 0).map i (smulUnitSection X (unop U) q)
      = smulUnitSection X (unop V) q := by
  show (singularCochainFunctor.map ((Opens.toTopCat X).map i.unop).op).f 0
      (q • unitCochainHom ((Opens.toTopCat X).obj (unop U)))
      = q • unitCochainHom ((Opens.toTopCat X).obj (unop V))
  rw [map_smul]
  congr 1
  exact unitCochain_map ((Opens.toTopCat X).map i.unop)

/-- The presheaf-level augmentation component at an open `U`: rational
multiples of the unit cochain.-/
def augApp (X : TopCat.{0}) (U : Opens X) :
    AddCommGrpCat.of (ULift.{0} ℚ) ⟶ ((singularPresheafComplex X).X 0).obj (op U) :=
  AddCommGrpCat.ofHom
    { toFun := fun q => smulUnitSection X U q.down
      map_zero' := smulUnitSection_zero X U
      map_add' := fun a b => smulUnitSection_add X U a.down b.down }

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf-level augmentation: the constant `ULift ℚ`-presheaf maps to
the degree-0 singular cochain presheaf by constant cochains.-/
def augmentationPresheaf (X : TopCat.{0}) :
    constQPresheaf X ⟶ (singularPresheafComplex X).X 0 where
  app U := augApp X U.unop
  naturality {U V} i := by
    ext q
    show smulUnitSection X (unop V) q.down
        = ((singularPresheafComplex X).X 0).map i (smulUnitSection X (unop U) q.down)
    rw [presheafRes_smulUnitSection]

/-- The **augmentation**: the constant `ULift ℚ`-sheaf maps to the degree-0
sheafified cochain sheaf, by sheafifying the presheaf-level augmentation.
This is a constructed morphism of abelian sheaves; no property beyond the
composite-with-`d` vanishing and the stalkwise statements below is claimed.-/
def augmentationSheaf (X : TopCat.{0}) :
    constQSheaf X ⟶ (sheafifiedCochainComplex X).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map (augmentationPresheaf X)

set_option backward.isDefEq.respectTransparency false in
lemma augmentationPresheaf_comp_d (X : TopCat.{0}) :
    augmentationPresheaf X ≫ (singularPresheafComplex X).d 0 1 = 0 := by
  ext U q
  show ((singularPresheafComplex X).d 0 1).app (op U) ((augmentationPresheaf X).app (op U) q) = 0
  show (singularCochainFunctor.obj (op ((Opens.toTopCat X).obj U))).d 0 1
      (q.down • unitCochainHom ((Opens.toTopCat X).obj U)) = 0
  rw [map_smul]
  have hd : (singularCochainFunctor.obj (op ((Opens.toTopCat X).obj U))).d 0 1
      (unitCochainHom ((Opens.toTopCat X).obj U))
      = ((chainsFunctor.obj ((Opens.toTopCat X).obj U)).d 1 0
        ≫ unitCochainHom ((Opens.toTopCat X).obj U)) := rfl
  rw [hd, d_comp_unitCochainHom, smul_zero]

set_option backward.isDefEq.respectTransparency false in
lemma augmentationSheaf_comp_d (X : TopCat.{0}) :
    augmentationSheaf X ≫ (sheafifiedCochainComplex X).d 0 1 = 0 := by
  have h : augmentationSheaf X ≫ (sheafifiedCochainComplex X).d 0 1
      = (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
        (augmentationPresheaf X ≫ (singularPresheafComplex X).d 0 1) := by
    rw [Functor.map_comp]
    rfl
  rw [h, augmentationPresheaf_comp_d X, Functor.map_zero]

/-- The augmented complex at its lowest spots, packaged as a short complex of
abelian sheaves: `constQSheaf X ⟶ 𝒮⁰ ⟶ 𝒮¹`.  Its exactness at the middle
spot is **not** proven in this file (see the module docstring); only the
data and the composite-vanishing are provided here.-/
def augmentedShortComplex (X : TopCat.{0}) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (augmentationSheaf X) ((sheafifiedCochainComplex X).d 0 1)
    (augmentationSheaf_comp_d X)

/-! ## Stalkwise exactness in positive degrees -/

/-- Coboundary extraction on a contractible space, in the abelian-group
carrier: in positive degree, a singular cocycle on a contractible space is a
coboundary (the elementwise form of the vanishing from
`HodgePilot.ContractibleSingular`).-/
lemma exists_coboundary (B : TopCat.{0}) [ContractibleSpace ↑B] (m : ℕ)
    (s : (singularCochainAbFunctor.obj (op B)).X (m + 1))
    (hs : (singularCochainAbFunctor.obj (op B)).d (m + 1) (m + 2) s = 0) :
    ∃ t : (singularCochainAbFunctor.obj (op B)).X m,
      (singularCochainAbFunctor.obj (op B)).d m (m + 1) t = s := by
  have hex : ((singularCochainFunctor.obj (op B)).sc' m (m + 1) (m + 2)).Exact := by
    rw [← (singularCochainFunctor.obj (op B)).exactAt_iff' m (m + 1) (m + 2)
      (by simp) (by simp)]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact isZero_singularCohomology_of_contractible B (m + 1) (Nat.succ_ne_zero m)
  rw [ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨t, ht⟩ := hex s hs
  exact ⟨t, ht⟩

set_option backward.isDefEq.respectTransparency false in
/-- The `toSheafify` units are isomorphisms on stalks, so exactness of a
stalk short complex transfers from the singular cochain presheaf complex to
the sheafified complex.-/
lemma exact_map_stalk_of_exact (X : TopCat.{0}) (i j k : ℕ) (x : ↑X)
    (h : (((singularPresheafComplex X).sc' i j k).map
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)).Exact) :
    (((sheafifiedCochainComplex X).sc' i j k).map
      (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)).Exact := by
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
    ((singularPresheafComplex X).X i)
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
    ((singularPresheafComplex X).X j)
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
    ((singularPresheafComplex X).X k)
  refine (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X i))))
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X j))))
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X k))))
    ?_ ?_)).mp h
  · show (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X i))
        ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (sheafifyMap (Opens.grothendieckTopology X) ((singularPresheafComplex X).d i j))
        = (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ((singularPresheafComplex X).d i j)
        ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X j))
    rw [← Functor.map_comp, ← Functor.map_comp, ← toSheafify_naturality]
  · show (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X j))
        ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (sheafifyMap (Opens.grothendieckTopology X) ((singularPresheafComplex X).d j k))
        = (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ((singularPresheafComplex X).d j k)
        ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X k))
    rw [← Functor.map_comp, ← Functor.map_comp, ← toSheafify_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- **Stalkwise exactness in positive degrees** (see the module docstring for
scope and for what this does *not* say): on a strongly locally contractible
space, the termwise-sheafified singular cochain complex is exact in every
degree `n ≠ 0`, as a complex of sheafified cochain sheaves.  Nothing about
any cohomology of this complex — sheaf, singular, or otherwise — is stated or
implied.-/
theorem exactAt_sheafifiedCochainComplex (X : TopCat.{0})
    [StronglyLocallyContractibleSpace ↑X] (n : ℕ) (hn : n ≠ 0) :
    (sheafifiedCochainComplex X).ExactAt n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [(sheafifiedCochainComplex X).exactAt_iff' m (m + 1) (m + 2) (by simp) (by simp)]
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  refine exact_map_stalk_of_exact X m (m + 1) (m + 2) x ?_
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((singularPresheafComplex X).X (m + 1)) z
  have hz' : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((singularPresheafComplex X).d (m + 1) (m + 2)))
      (((singularPresheafComplex X).X (m + 1)).germ U x hxU s) = 0 := hz
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz'
  -- restrict to an open W where the coboundary of s vanishes on the nose
  have h0 : ((singularPresheafComplex X).X (m + 2)).germ U x hxU
      (((singularPresheafComplex X).d (m + 1) (m + 2)).app (op U) s) =
      ((singularPresheafComplex X).X (m + 2)).germ U x hxU 0 := by
    rw [hz']; simp
  obtain ⟨W, hxW, iWU, iWU', hres⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ h0
  set sW := ((singularPresheafComplex X).X (m + 1)).map iWU.op s with hsW
  have hdW : ((singularPresheafComplex X).d (m + 1) (m + 2)).app (op W) sW = 0 := by
    rw [hsW, ← ConcreteCategory.comp_apply,
      ((singularPresheafComplex X).d (m + 1) (m + 2)).naturality iWU.op,
      ConcreteCategory.comp_apply, hres]
    simp
  -- shrink into a contractible basis neighbourhood B, then into an open O
  obtain ⟨B, ⟨hBmem, hBcontr⟩, hBW⟩ :=
    (contractible_basis (x : ↑X)).mem_iff.mp (W.isOpen.mem_nhds hxW)
  obtain ⟨O, hOB, hOopen, hxO⟩ := mem_nhds_iff.mp hBmem
  haveI := hBcontr
  let Wsp := (Opens.toTopCat X).obj W
  let bT : TopCat.{0} := TopCat.of ↥B
  let OW : Opens X := ⟨O, hOopen⟩
  have hOle : OW ⟶ W := homOfLE fun a ha => hBW (hOB ha)
  let ιBW : bT ⟶ Wsp := TopCat.ofHom ⟨Set.inclusion hBW, continuous_inclusion hBW⟩
  let ιOB : (Opens.toTopCat X).obj OW ⟶ bT :=
    TopCat.ofHom ⟨Set.inclusion hOB, continuous_inclusion hOB⟩
  have hglue : (Opens.toTopCat X).map hOle = ιOB ≫ ιBW :=
    TopCat.hom_ext (ContinuousMap.ext fun a => Subtype.ext rfl)
  -- transport the cocycle to B and kill it there
  set sB := (singularCochainAbFunctor.map ιBW.op).f (m + 1) sW with hsB
  have hsBzero : (singularCochainAbFunctor.obj (op bT)).d (m + 1) (m + 2) sB = 0 := by
    rw [hsB, ← ConcreteCategory.comp_apply,
      (singularCochainAbFunctor.map ιBW.op).comm (m + 1) (m + 2),
      ConcreteCategory.comp_apply]
    have hbridge : (singularCochainAbFunctor.obj (op Wsp)).d (m + 1) (m + 2) sW = 0 := hdW
    rw [hbridge]
    simp
  obtain ⟨t, ht⟩ := exists_coboundary bT m sB hsBzero
  -- the germ of the transported coboundary witness maps to the original germ
  refine ⟨((singularPresheafComplex X).X m).germ OW x hxO
    ((singularCochainAbFunctor.map ιOB.op).f m t), ?_⟩
  show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((singularPresheafComplex X).d m (m + 1)))
      (((singularPresheafComplex X).X m).germ OW x hxO
        ((singularCochainAbFunctor.map ιOB.op).f m t))
      = ((singularPresheafComplex X).X (m + 1)).germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hcompute : ((singularPresheafComplex X).d m (m + 1)).app (op OW)
      ((singularCochainAbFunctor.map ιOB.op).f m t)
      = ((singularPresheafComplex X).X (m + 1)).map hOle.op sW := by
    show (singularCochainAbFunctor.obj (op ((Opens.toTopCat X).obj OW))).d m (m + 1)
        ((singularCochainAbFunctor.map ιOB.op).f m t)
        = (singularCochainAbFunctor.map ((Opens.toTopCat X).map hOle).op).f (m + 1) sW
    rw [← ConcreteCategory.comp_apply, (singularCochainAbFunctor.map ιOB.op).comm m (m + 1),
      ConcreteCategory.comp_apply, ht, hsB, hglue,
      ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, ← op_comp]
  rw [hcompute, TopCat.Presheaf.germ_res_apply, hsW, TopCat.Presheaf.germ_res_apply]

/-! ## Stalkwise injectivity of the augmentation -/

end HodgePilot.SingularResolution
