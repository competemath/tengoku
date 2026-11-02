import Tengoku.HodgeStructuresLean4.HodgePilot.SingularGamma
import Tengoku.HodgeStructuresLean4.HodgePilot.CPointsMetrizable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Global sections of the sheafified cochain complex against the singular cochains: the comparison map, its kernel, and degreewise `Γ`-surjectivity

For a topological space `X` this file builds, on the site `Opens X`, the
global-sections layer of the presheaf-versus-sheaf comparison for the singular
cochain presheaf complex of `HodgePilot.SingularResolution`:

1. **the two global-sections complexes**: `gammaSingularComplex X`, the value
   of the singular cochain presheaf complex at the top open (its terms are
   genuine singular cochain groups of the subspace `⊤ ⊆ X`), and
   `gammaSheafifiedComplex X`, the global sections of the sheafified cochain
   complex — both as cochain complexes of abelian groups;
2. **the comparison chain map** (`gammaComparison`): degreewise the
   `toSheafify` unit at the top open, with the chain-map receipt carried by
   the construction itself (the commutation squares are `toSheafify`
   naturality);
3. **the kernel characterization** (`gammaComparison_eq_zero_iff`,
   `ker_gammaComparison`): on any space, a global singular cochain maps to
   zero exactly when it is **locally zero** (it restricts to zero on a
   neighbourhood of every point) — through the stalk bridges of
   `HodgePilot.SingularGamma`; the locally-zero cochains form the subgroup
   `locallyZeroSubgroup`;
4. **degreewise `Γ`-surjectivity** (`gammaComparison_surjective`): on a
   paracompact Hausdorff space the comparison map is surjective in every
   degree.  A global section of the sheafified cochain sheaf is locally
   represented by genuine singular cochains; a partition of the space
   subordinate to the representing cover
   (`HodgePilot.SingularGamma.exists_subordinate_partition`) selects, per
   singular simplex, the representative indexed by the ambient first vertex
   of the simplex (`selectCochain` — the classical Warner gluing, built on
   the summand cofan of the singular chain complex), and the partition-sum
   identity of `HodgePilot.SingularFineness`/`SingularGamma` shows the
   selection maps onto the given section;
5. **the degreewise identification** (`gammaQuotientEquiv`): consequently, on
   a paracompact Hausdorff space and for each degree `n` separately, the
   group of global sections of the `n`-th sheafified cochain sheaf is
   identified with the quotient of the group of global singular `n`-cochains
   by the locally-zero ones — a statement about one degree at a time, with no
   chain-level or cohomology-level consequence drawn anywhere;
6. **the degree-0 seed** (`eq_zero_of_locallyZero_degreeZero`,
   `gammaComparison_injective_degreeZero`): a locally-zero `0`-cochain is
   zero (a `0`-simplex is a point, contained in every neighbourhood of
   itself), so in degree `0` the comparison map is injective on any space;
7. metrizable-scope and analytic point-space corollaries of 4 and 5
   (`gammaComparison_surjective_of_metrizable`, `_cpoints`, `_spoints`,
   `gammaQuotientEquiv_of_metrizable`), mirroring the corollary pattern of
   `HodgePilot.CochainAcyclic`.

The entitled claim of this file, in full: *for every topological space the
comparison chain map from the global singular cochains to the global sections
of the sheafified cochain complex is constructed, its kernel is exactly the
locally-zero cochains in every degree, and in degree `0` it is injective; on
every paracompact Hausdorff space it is surjective in every degree, so that,
degree by degree, the global sections of the sheafified cochain sheaves are
identified as groups with the global singular cochains modulo the locally-zero
ones — at exactly that scope, and degreewise only.*

**What remains open here — deliberately and permanently at this Mathlib pin**:
no statement about the cohomology of either complex is made anywhere in this
file.  The comparison map is *not* claimed to be a quasi-isomorphism; the
locally-zero subcomplex is *not* claimed to be cohomologically trivial; no
map, iso, or identification between cohomology groups of any kind appears
here.  (The cohomological triviality of the locally-zero subcomplex is
classically equivalent to small-simplices/barycentric-subdivision content
which this Mathlib pin does not contain; it is out of reach of the partition
toolkit by design, not by accident — see the campaign notes.)  In particular
nothing here identifies sheaf cohomology with singular cohomology in any
degree: that identification remains the named, future, unproven and
undeclared Prop (`SingularSheafComparison`, the P4-Prop of the commentary in
`HodgePilot.HodgePredicate`), which in addition needs the descent assembly —
it is untouched by this module.  The word "singular" below refers exclusively
to the genuine presheaf-level singular-cochain objects
(`singularPresheafComplex` and its sections); the sheaf-level carriers are
sheafified cochain sheaves and are never called singular.  **Nothing here
makes the Hodge conjecture statable.**  Everything is at universe `0`, forced
by the `ModuleCat.{0} ℚ` coefficients of the house carrier.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology
  HodgePilot.SingularCohomology HodgePilot.ContractibleSingular HodgePilot.SingularResolution
  HodgePilot.SingularFineness HodgePilot.SingularGamma
open scoped Simplicial

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace HodgePilot.CochainGlobal

/-! ## The two global-sections complexes and the comparison chain map -/

set_option backward.isDefEq.respectTransparency false in
/-- Global sections (the value at the top open) of the singular cochain
presheaf complex: a cochain complex of abelian groups whose terms are genuine
singular cochain groups of the subspace `⊤ ⊆ X`.-/
def gammaSingularComplex (X : TopCat.{0}) : CochainComplex AddCommGrpCat.{0} ℕ where
  X n := ((singularPresheafComplex X).X n).obj (op ⊤)
  d i j := ((singularPresheafComplex X).d i j).app (op ⊤)
  shape i j hij := by
    rw [(singularPresheafComplex X).shape i j hij]
    rfl
  d_comp_d' i j k _ _ := by
    rw [← NatTrans.comp_app, (singularPresheafComplex X).d_comp_d i j k]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Global sections of the sheafified cochain complex, as a cochain complex of
abelian groups.  The terms are sections of sheafified cochain sheaves; they
are not singular cochain objects and are never called singular.-/
def gammaSheafifiedComplex (X : TopCat.{0}) : CochainComplex AddCommGrpCat.{0} ℕ where
  X n := ((sheafifiedCochainComplex X).X n).1.obj (op ⊤)
  d i j := ((sheafifiedCochainComplex X).d i j).hom.app (op ⊤)
  shape i j hij := by
    rw [(sheafifiedCochainComplex X).shape i j hij]
    rfl
  d_comp_d' i j k _ _ := by
    rw [show ((sheafifiedCochainComplex X).d i j).hom.app (op ⊤)
          ≫ ((sheafifiedCochainComplex X).d j k).hom.app (op ⊤)
        = ((sheafifiedCochainComplex X).d i j ≫ (sheafifiedCochainComplex X).d j k).hom.app (op ⊤)
        from rfl,
      (sheafifiedCochainComplex X).d_comp_d i j k]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison chain map**: degreewise the `toSheafify` unit at the top
open.  The chain-map receipt is the construction itself: the commutation
squares are the naturality of `toSheafify`.  No property of this map beyond
what is proven below (kernel characterization on any space, surjectivity on
paracompact Hausdorff spaces, injectivity in degree `0`) is claimed; in
particular it is nowhere claimed to be a quasi-isomorphism.-/
def gammaComparison (X : TopCat.{0}) : gammaSingularComplex X ⟶ gammaSheafifiedComplex X where
  f n := (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)).app (op ⊤)
  comm' i j _ := by
    show (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X i)).app (op ⊤)
        ≫ (sheafifyMap (Opens.grothendieckTopology X)
            ((singularPresheafComplex X).d i j)).app (op ⊤)
      = ((singularPresheafComplex X).d i j).app (op ⊤)
        ≫ (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X j)).app (op ⊤)
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← toSheafify_naturality]

/-- The components of the comparison map are the `toSheafify` components
(definitional receipt).-/
lemma gammaComparison_f_apply (X : TopCat.{0}) (n : ℕ)
    (s : ((singularPresheafComplex X).X n).obj (op (⊤ : Opens X))) :
    (gammaComparison X).f n s
      = (toSheafify (Opens.grothendieckTopology X)
          ((singularPresheafComplex X).X n)).app (op ⊤) s := rfl

/-! ## Restriction and naturality helpers -/

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along a composite of inclusions of opens collapses, for any
abelian presheaf (presheaf-level form of `HodgePilot.SingularGamma.res_res'`).-/
lemma pres_res_res {X : TopCat.{0}} (F : TopCat.Presheaf AddCommGrpCat.{0} X)
    {O P' Q : Opens X} (i : O ⟶ P') (j : P' ⟶ Q) (k : O ⟶ Q) (s : F.obj (op Q)) :
    F.map i.op (F.map j.op s) = F.map k.op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `toSheafify` unit commutes with restriction, elementwise.-/
lemma unit_res {X : TopCat.{0}} (F : TopCat.Presheaf AddCommGrpCat.{0} X)
    {O P' : Opens X} (i : O ⟶ P') (s : F.obj (op P')) :
    (toSheafify (Opens.grothendieckTopology X) F).app (op O) (F.map i.op s)
      = ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj F).1.map i.op
          ((toSheafify (Opens.grothendieckTopology X) F).app (op P') s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    (toSheafify (Opens.grothendieckTopology X) F).naturality]

set_option backward.isDefEq.respectTransparency false in
/-- The `toSheafify` unit intertwines the presheaf-level and sheafified
partition endomorphisms, elementwise.-/
lemma unit_partitionEndo_app (X : TopCat.{0}) (A : Set ↑X) (n : ℕ) (O : Opens X)
    (c : ((singularPresheafComplex X).X n).obj (op O)) :
    (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)).app (op O)
        ((partitionEndo X A n).app (op O) c)
      = (partitionEndoSheaf X A n).hom.app (op O)
          ((toSheafify (Opens.grothendieckTopology X)
            ((singularPresheafComplex X).X n)).app (op O) c) := by
  have hsq : (partitionEndo X A n).app (op O)
        ≫ (toSheafify (Opens.grothendieckTopology X)
            ((singularPresheafComplex X).X n)).app (op O)
      = (toSheafify (Opens.grothendieckTopology X)
            ((singularPresheafComplex X).X n)).app (op O)
        ≫ (sheafifyMap (Opens.grothendieckTopology X) (partitionEndo X A n)).app (op O) := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← toSheafify_naturality]
  exact (ConcreteCategory.comp_apply _ _ c).symm.trans
    ((congrArg (fun (f : _ ⟶ _) => (ConcreteCategory.hom f) c) hsq).trans
      (ConcreteCategory.comp_apply _ _ c))

/-! ## Locally-zero cochains and the kernel characterization -/

/-- A section of an abelian presheaf over the top open is **locally zero** if
it restricts to zero on a neighbourhood of every point.-/
def LocallyZero (X : TopCat.{0}) (F : TopCat.Presheaf AddCommGrpCat.{0} X)
    (s : F.obj (op (⊤ : Opens X))) : Prop :=
  ∀ x : ↑X, ∃ (U : Opens X) (_ : x ∈ U), F.map (homOfLE (le_top : U ≤ ⊤)).op s = 0

set_option backward.isDefEq.respectTransparency false in
/-- **The kernel characterization** (deliverable 2): on any space, a global
singular cochain maps to zero under the comparison map exactly when it is
locally zero.  Forward: the `toSheafify` unit is a stalk isomorphism, so a
section with zero image has zero germs, and germ equality descends to honest
restriction over some neighbourhood.  Backward: a locally-zero cochain has
zero germs after sheafification, and sections of a sheaf are determined by
their germs.-/
theorem gammaComparison_eq_zero_iff (X : TopCat.{0}) (n : ℕ)
    (s : ((singularPresheafComplex X).X n).obj (op (⊤ : Opens X))) :
    (gammaComparison X).f n s = 0
      ↔ LocallyZero X ((singularPresheafComplex X).X n) s := by
  constructor
  · intro hs x
    haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      ((singularPresheafComplex X).X n)
    have hg : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n))
        (((singularPresheafComplex X).X n).germ ⊤ x trivial s) = 0 := by
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      have hz : (toSheafify (Opens.grothendieckTopology X)
          ((singularPresheafComplex X).X n)).app (op ⊤) s = 0 := hs
      rw [hz, map_zero]
    have hstalk : ((singularPresheafComplex X).X n).germ ⊤ x trivial s
        = ((singularPresheafComplex X).X n).germ ⊤ x trivial 0 := by
      have hinj := (ConcreteCategory.bijective_of_isIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
          (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)))).1
      refine hinj ?_
      rw [hg, map_zero, map_zero]
    obtain ⟨W, hxW, iWT, iWT', hres⟩ := TopCat.Presheaf.germ_eq
      ((singularPresheafComplex X).X n) x (show x ∈ (⊤ : Opens X) from trivial)
      (show x ∈ (⊤ : Opens X) from trivial) _ _ hstalk
    refine ⟨W, hxW, ?_⟩
    have hbridge : ((singularPresheafComplex X).X n).map (homOfLE (le_top : W ≤ ⊤)).op s
        = ((singularPresheafComplex X).X n).map iWT.op s := rfl
    rw [hbridge, hres, map_zero]
  · intro hs
    have hz : (toSheafify (Opens.grothendieckTopology X)
        ((singularPresheafComplex X).X n)).app (op ⊤) s = 0 := by
      refine TopCat.Presheaf.section_ext ((sheafifiedCochainComplex X).X n) ⊤ _ _
        (fun x hx => ?_)
      obtain ⟨U, hxU, hU⟩ := hs x
      have h1 : ((sheafifiedCochainComplex X).X n).presheaf.germ ⊤ x hx
          ((toSheafify (Opens.grothendieckTopology X)
            ((singularPresheafComplex X).X n)).app (op ⊤) s)
          = ((sheafifiedCochainComplex X).X n).presheaf.germ U x hxU
            (((sheafifiedCochainComplex X).X n).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
              ((toSheafify (Opens.grothendieckTopology X)
                ((singularPresheafComplex X).X n)).app (op ⊤) s)) :=
        (TopCat.Presheaf.germ_res_apply ((sheafifiedCochainComplex X).X n).presheaf
          (homOfLE (le_top : U ≤ ⊤)) x hxU _).symm
    -- rewrite the restricted unit through naturality and kill it with `hU`
      have h2 : ((sheafifiedCochainComplex X).X n).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((toSheafify (Opens.grothendieckTopology X)
            ((singularPresheafComplex X).X n)).app (op ⊤) s)
          = (toSheafify (Opens.grothendieckTopology X)
              ((singularPresheafComplex X).X n)).app (op U)
            (((singularPresheafComplex X).X n).map (homOfLE (le_top : U ≤ ⊤)).op s) :=
        (unit_res ((singularPresheafComplex X).X n) (homOfLE (le_top : U ≤ ⊤)) s).symm
      rw [h1, h2, hU, map_zero, map_zero, map_zero]
    exact hz
  -- (the `exact hz` closes the definitional bridge to `(gammaComparison X).f n s = 0`)

/-- **The locally-zero subgroup**: locally-zero global cochains form an
additive subgroup of the global singular cochains.-/
def locallyZeroSubgroup (X : TopCat.{0}) (n : ℕ) :
    AddSubgroup ↑(((singularPresheafComplex X).X n).obj (op (⊤ : Opens X))) where
  carrier := {s | LocallyZero X ((singularPresheafComplex X).X n) s}
  zero_mem' := fun x => ⟨⊤, trivial, map_zero _⟩
  add_mem' := by
    intro a b ha hb x
    obtain ⟨U, hxU, hU⟩ := ha x
    obtain ⟨W, hxW, hW⟩ := hb x
    refine ⟨U ⊓ W, ⟨hxU, hxW⟩, ?_⟩
    rw [map_add,
      ← pres_res_res ((singularPresheafComplex X).X n)
        (homOfLE (inf_le_left : U ⊓ W ≤ U)) (homOfLE (le_top : U ≤ ⊤))
        (homOfLE (le_top : U ⊓ W ≤ ⊤)) a,
      ← pres_res_res ((singularPresheafComplex X).X n)
        (homOfLE (inf_le_right : U ⊓ W ≤ W)) (homOfLE (le_top : W ≤ ⊤))
        (homOfLE (le_top : U ⊓ W ≤ ⊤)) b,
      hU, hW, map_zero, map_zero, add_zero]
  neg_mem' := by
    intro a ha x
    obtain ⟨U, hxU, hU⟩ := ha x
    exact ⟨U, hxU, by rw [map_neg, hU, neg_zero]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the comparison map, as a subgroup, is exactly the
locally-zero subgroup.-/
theorem ker_gammaComparison (X : TopCat.{0}) (n : ℕ) :
    (((gammaComparison X).f n).hom).ker = locallyZeroSubgroup X n := by
  refine AddSubgroup.ext fun s => ?_
  rw [AddMonoidHom.mem_ker]
  exact gammaComparison_eq_zero_iff X n s

/-! ## The simplex-selection layer

The Warner gluing needs one genuinely simplex-level construction: from a
family of local cochains indexed by a partition of the space, the global
cochain valuing each singular simplex by the representative selected by the
ambient first vertex of the simplex.  It is built on the summand cofan of the
singular chain complex, exactly as the weighting endomorphisms of
`HodgePilot.SingularFineness`. -/

section Selection

variable {X : TopCat.{0}}

/-- A subspace simplex lies (pointwise, ambiently) in an open `V`.-/
def SimplexIn {U : Opens X} {n : ℕ}
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) _⦋n⦌) (V : Opens X) : Prop :=
  ∀ p, ambient (σ.down.hom p) ∈ V

set_option backward.isDefEq.respectTransparency false in
/-- Corestriction of a subspace simplex through an open it lies in.-/
def corestrict {U : Opens X} {n : ℕ}
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) _⦋n⦌) {V : Opens X}
    (h : SimplexIn σ V) : (TopCat.toSSet.obj ((Opens.toTopCat X).obj V)) _⦋n⦌ :=
  ULift.up (TopCat.ofHom ⟨fun p => ⟨ambient (σ.down.hom p), h p⟩,
    (continuous_subtype_val.comp σ.down.hom.continuous).subtype_mk _⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Pushing a subspace simplex forward along an inclusion of opens.-/
def pushSimplex {U W : Opens X} (i : U ⟶ W) {n : ℕ}
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) _⦋n⦌) :
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj W)) _⦋n⦌ :=
  (TopCat.toSSet.map ((Opens.toTopCat X).map i)).app (op ⦋n⦌) σ

set_option backward.isDefEq.respectTransparency false in
/-- Points of a pushed simplex have the same ambient values.-/
lemma ambient_pushSimplex {U W : Opens X} (i : U ⟶ W) {n : ℕ}
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) _⦋n⦌) (p) :
    ambient ((pushSimplex i σ).down.hom p) = ambient (σ.down.hom p) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pushing a corestriction forward returns the original simplex.-/
lemma pushSimplex_corestrict {W : Opens X} {n : ℕ}
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj W)) _⦋n⦌) {U : Opens X}
    (h : SimplexIn σ U) (hUW : U ≤ W) :
    pushSimplex (homOfLE hUW) (corestrict σ h) = σ :=
  ULift.down_injective (TopCat.hom_ext (ContinuousMap.ext fun _ => Subtype.ext rfl))

set_option backward.isDefEq.respectTransparency false in
/-- Corestricting a pushed simplex agrees with pushing into the target open
directly.-/
lemma corestrict_pushSimplex {O W : Opens X} {n : ℕ}
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj O)) _⦋n⦌) (j : O ⟶ W)
    {V : Opens X} (h : SimplexIn (pushSimplex j σ) V) (hOV : O ≤ V) :
    corestrict (pushSimplex j σ) h = pushSimplex (homOfLE hOV) σ :=
  ULift.down_injective (TopCat.hom_ext (ContinuousMap.ext fun _ => Subtype.ext rfl))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a singular cochain, evaluated on a simplex summand, is
evaluation of the cochain on the pushed simplex.-/
lemma ι_res_cochain {U W : Opens X} (i : U ⟶ W) (n : ℕ)
    (φ : ((singularPresheafComplex X).X n).obj (op W))
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) _⦋n⦌) :
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).ιChainComplex σ
        ≫ (((singularPresheafComplex X).X n).map i.op φ :
          (chainsFunctor.obj ((Opens.toTopCat X).obj U)).X n ⟶ Qcoef)
      = (TopCat.toSSet.obj ((Opens.toTopCat X).obj W)).ιChainComplex (pushSimplex i σ)
        ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj W)).X n ⟶ Qcoef) := by
  show (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).ιChainComplex σ
      ≫ ((SSet.chainComplexMap (TopCat.toSSet.map ((Opens.toTopCat X).map i)) Qcoef).f n
        ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj W)).X n ⟶ Qcoef))
    = (TopCat.toSSet.obj ((Opens.toTopCat X).obj W)).ιChainComplex (pushSimplex i σ)
      ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj W)).X n ⟶ Qcoef)
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  rfl

variable {ι : Type}

set_option backward.isDefEq.respectTransparency false in
/-- **The selection cochain**: given a partition `A` of the base and local
cochains `b i` over opens `V i`, the global cochain valuing a simplex `σ` by
`b i(σ)` when `σ` lies in `V i(σ)` — where `i(σ)` is the partition index of
the ambient first vertex of `σ` — and by `0` otherwise (the classical Warner
gluing datum).-/
def selectCochain (X : TopCat.{0}) (n : ℕ) (A : ι → Set ↑X) (V : ι → Opens X)
    (hA : ∀ y : ↑X, ∃! i, y ∈ A i)
    (b : ∀ i, ((singularPresheafComplex X).X n).obj (op (V i))) :
    ((singularPresheafComplex X).X n).obj (op (⊤ : Opens X)) :=
  (((TopCat.toSSet.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).isColimitChainComplexXCofan
      Qcoef n).desc
    (Cofan.mk Qcoef (fun σ =>
      if h : SimplexIn σ (V (hA (ambient (firstVertex σ))).choose)
      then ((TopCat.toSSet.obj ((Opens.toTopCat X).obj
          (V (hA (ambient (firstVertex σ))).choose))).ιChainComplex (corestrict σ h)
        ≫ (b (hA (ambient (firstVertex σ))).choose :
            (chainsFunctor.obj ((Opens.toTopCat X).obj
              (V (hA (ambient (firstVertex σ))).choose))).X n ⟶ Qcoef))
      else 0)) :
    (chainsFunctor.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).X n ⟶ Qcoef)

set_option backward.isDefEq.respectTransparency false in
/-- The summand description of the selection cochain.-/
lemma ι_selectCochain (X : TopCat.{0}) (n : ℕ) (A : ι → Set ↑X) (V : ι → Opens X)
    (hA : ∀ y : ↑X, ∃! i, y ∈ A i)
    (b : ∀ i, ((singularPresheafComplex X).X n).obj (op (V i)))
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (⊤ : Opens X))) _⦋n⦌) :
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).ιChainComplex σ
        ≫ (selectCochain X n A V hA b :
          (chainsFunctor.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).X n ⟶ Qcoef)
      = if h : SimplexIn σ (V (hA (ambient (firstVertex σ))).choose)
        then ((TopCat.toSSet.obj ((Opens.toTopCat X).obj
            (V (hA (ambient (firstVertex σ))).choose))).ιChainComplex (corestrict σ h)
          ≫ (b (hA (ambient (firstVertex σ))).choose :
              (chainsFunctor.obj ((Opens.toTopCat X).obj
                (V (hA (ambient (firstVertex σ))).choose))).X n ⟶ Qcoef))
        else 0 :=
  (((TopCat.toSSet.obj ((Opens.toTopCat X).obj ⊤)).isColimitChainComplexXCofan
    Qcoef n).fac _ ⟨σ⟩)

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction of the selection cochain**: on any open meeting only
partition sets whose indices lie in a finite set `T`, and contained in every
`V i` with `i ∈ T`, the restricted selection cochain is the finite sum of the
partition-endomorphism images of the restricted local representatives.-/
lemma res_selectCochain (X : TopCat.{0}) (n : ℕ) (A : ι → Set ↑X) (V : ι → Opens X)
    (hA : ∀ y : ↑X, ∃! i, y ∈ A i)
    (b : ∀ i, ((singularPresheafComplex X).X n).obj (op (V i)))
    {O : Opens X} (T : Finset ι) (hOV : ∀ i ∈ T, O ≤ V i)
    (hT : ∀ i ∉ T, Disjoint (O : Set ↑X) (A i)) :
    ((singularPresheafComplex X).X n).map (homOfLE (le_top : O ≤ ⊤)).op
        (selectCochain X n A V hA b)
      = ∑ i ∈ T.attach, (partitionEndo X (A i.1) n).app (op O)
          (((singularPresheafComplex X).X n).map (homOfLE (hOV i.1 i.2)).op (b i.1)) := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  -- the ambient first vertex of `σ` and its partition data
  have hyO : ambient (firstVertex σ) ∈ O := (σ.down.hom (vertexPt n)).2
  have hiA : ambient (firstVertex σ) ∈ A ((hA (ambient (firstVertex σ))).choose) :=
    (hA (ambient (firstVertex σ))).choose_spec.1
  have hiT : (hA (ambient (firstVertex σ))).choose ∈ T := by
    by_contra hns
    exact Set.disjoint_left.mp (hT _ hns) hyO hiA
  have hcond : SimplexIn (pushSimplex (homOfLE (le_top : O ≤ ⊤)) σ)
      (V (hA (ambient (firstVertex (pushSimplex (homOfLE (le_top : O ≤ ⊤)) σ)))).choose) :=
    fun p => hOV _ hiT (σ.down.hom p).2
  -- the left-hand side evaluates by first-vertex selection
  have hL : (TopCat.toSSet.obj ((Opens.toTopCat X).obj O)).ιChainComplex σ
      ≫ (((singularPresheafComplex X).X n).map (homOfLE (le_top : O ≤ ⊤)).op
          (selectCochain X n A V hA b) :
        (chainsFunctor.obj ((Opens.toTopCat X).obj O)).X n ⟶ Qcoef)
      = (TopCat.toSSet.obj ((Opens.toTopCat X).obj
            (V ((hA (ambient (firstVertex σ))).choose)))).ιChainComplex
          (pushSimplex (homOfLE (hOV ((hA (ambient (firstVertex σ))).choose) hiT)) σ)
        ≫ (b ((hA (ambient (firstVertex σ))).choose) :
            (chainsFunctor.obj ((Opens.toTopCat X).obj
              (V ((hA (ambient (firstVertex σ))).choose)))).X n ⟶ Qcoef) := by
    rw [ι_res_cochain (homOfLE (le_top : O ≤ ⊤)) n (selectCochain X n A V hA b) σ,
      ι_selectCochain X n A V hA b (pushSimplex (homOfLE (le_top : O ≤ ⊤)) σ),
      dite_eq_left hcond,
      corestrict_pushSimplex σ (homOfLE (le_top : O ≤ ⊤)) hcond
        (hOV ((hA (ambient (firstVertex σ))).choose) hiT)]
  -- each summand of the right-hand side is a first-vertex weighting
  have hterm : ∀ i : {x // x ∈ T},
      (TopCat.toSSet.obj ((Opens.toTopCat X).obj O)).ιChainComplex σ
        ≫ ((partitionEndo X (A i.1) n).app (op O)
            (((singularPresheafComplex X).X n).map (homOfLE (hOV i.1 i.2)).op (b i.1)) :
          (chainsFunctor.obj ((Opens.toTopCat X).obj O)).X n ⟶ Qcoef)
      = if ambient (firstVertex σ) ∈ A i.1
        then (TopCat.toSSet.obj ((Opens.toTopCat X).obj O)).ιChainComplex σ
          ≫ (((singularPresheafComplex X).X n).map (homOfLE (hOV i.1 i.2)).op (b i.1) :
            (chainsFunctor.obj ((Opens.toTopCat X).obj O)).X n ⟶ Qcoef)
        else 0 := by
    intro i
    show (TopCat.toSSet.obj ((Opens.toTopCat X).obj O)).ιChainComplex σ
        ≫ (keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj O)) n (vertexPred X (A i.1) O n)
          ≫ (((singularPresheafComplex X).X n).map (homOfLE (hOV i.1 i.2)).op (b i.1) :
            (chainsFunctor.obj ((Opens.toTopCat X).obj O)).X n ⟶ Qcoef))
      = _
    rw [← Category.assoc, ι_keep]
    by_cases hmem : ambient (firstVertex σ) ∈ A i.1
    · rw [ite_eq_left (show vertexPred X (A i.1) O n σ from hmem), ite_eq_left hmem]
    · rw [ite_eq_right (show ¬ vertexPred X (A i.1) O n σ from hmem), ite_eq_right hmem,
        Limits.zero_comp]
  -- the right-hand side collapses to the selected index
  have hR : (TopCat.toSSet.obj ((Opens.toTopCat X).obj O)).ιChainComplex σ
      ≫ (∑ i ∈ T.attach, ((partitionEndo X (A i.1) n).app (op O)
          (((singularPresheafComplex X).X n).map (homOfLE (hOV i.1 i.2)).op (b i.1)) :
        (chainsFunctor.obj ((Opens.toTopCat X).obj O)).X n ⟶ Qcoef))
      = (TopCat.toSSet.obj ((Opens.toTopCat X).obj
            (V ((hA (ambient (firstVertex σ))).choose)))).ιChainComplex
          (pushSimplex (homOfLE (hOV ((hA (ambient (firstVertex σ))).choose) hiT)) σ)
        ≫ (b ((hA (ambient (firstVertex σ))).choose) :
            (chainsFunctor.obj ((Opens.toTopCat X).obj
              (V ((hA (ambient (firstVertex σ))).choose)))).X n ⟶ Qcoef) := by
    rw [Preadditive.comp_sum, Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_eq_single (⟨(hA (ambient (firstVertex σ))).choose, hiT⟩ : {x // x ∈ T})
        (fun j _ hne => ite_eq_right (fun hmem =>
          hne (Subtype.ext ((hA (ambient (firstVertex σ))).choose_spec.2 j.1 hmem))))
        (fun habs => absurd (Finset.mem_attach T _) habs),
      ite_eq_left hiA,
      ι_res_cochain (homOfLE (hOV ((hA (ambient (firstVertex σ))).choose) hiT)) n
        (b ((hA (ambient (firstVertex σ))).choose)) σ]
  exact hL.trans hR.symm

end Selection

/-! ## Local representatives and adequate opens -/

set_option backward.isDefEq.respectTransparency false in
/-- **Local representatives**: near every point, a global section of a
sheafified cochain sheaf is the image under the `toSheafify` unit of a genuine
singular cochain.-/
lemma exists_localRep (X : TopCat.{0}) (n : ℕ)
    (s : ((sheafifiedCochainComplex X).X n).1.obj (op (⊤ : Opens X))) (x : ↑X) :
    ∃ (V : Opens X) (_ : x ∈ V) (b : ((singularPresheafComplex X).X n).obj (op V)),
      (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)).app
          (op V) b
        = ((sheafifiedCochainComplex X).X n).1.map (homOfLE (le_top : V ≤ ⊤)).op s := by
  obtain ⟨w, hw⟩ := exists_stalk_toSheafify_preimage ((singularPresheafComplex X).X n) x
    (((sheafifiedCochainComplex X).X n).presheaf.germ ⊤ x trivial s)
  obtain ⟨U, hxU, b₀, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq ((singularPresheafComplex X).X n) w
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hw
  obtain ⟨W, hxW, iWU, iWT, hres⟩ := TopCat.Presheaf.germ_eq
    ((sheafifiedCochainComplex X).X n).presheaf x hxU
    (show x ∈ (⊤ : Opens X) from trivial) _ _ hw
  refine ⟨W, hxW, ((singularPresheafComplex X).X n).map iWU.op b₀, ?_⟩
  rw [unit_res ((singularPresheafComplex X).X n) iWU b₀]
  have hbridge : ((sheafifiedCochainComplex X).X n).1.map (homOfLE (le_top : W ≤ ⊤)).op s
      = ((sheafifiedCochainComplex X).X n).presheaf.map iWT.op s := rfl
  rw [hbridge]
  exact hres

set_option backward.isDefEq.respectTransparency false in
/-- **Adequate opens**: around every point of a space carrying a locally
finite family of closed supports subordinate to opens `V i`, there is an open
neighbourhood meeting only supports indexed by a finite set `T` and contained
in every `V i` with `i ∈ T`.-/
lemma exists_adequate_open (X : TopCat.{0}) {ι : Type} (A : ι → Set ↑X) (V : ι → Opens X)
    (hclA : ∀ i, closure (A i) ⊆ ((V i : Opens X) : Set ↑X))
    (hlf : LocallyFinite fun i => closure (A i)) (x : ↑X) :
    ∃ (O : Opens X) (_ : x ∈ O) (T : Finset ι),
      (∀ i ∈ T, O ≤ V i) ∧ ∀ i ∉ T, Disjoint (O : Set ↑X) (closure (A i)) := by
  obtain ⟨N, hN, hfin⟩ := hlf x
  classical
  set F : Finset ι := hfin.toFinset with hF
  set T : Finset ι := F.filter (fun i => x ∈ closure (A i)) with hTdef
  set G : Finset ι := F.filter (fun i => x ∉ closure (A i)) with hGdef
  refine ⟨⟨interior N ∩ ((⋂ i ∈ T, ((V i : Opens X) : Set ↑X))
      ∩ ⋂ i ∈ G, (closure (A i))ᶜ), ?_⟩, ?_, T, ?_, ?_⟩
  · exact isOpen_interior.inter ((isOpen_biInter_finset
      (fun i _ => (V i).isOpen)).inter
      (isOpen_biInter_finset (fun i _ => isClosed_closure.isOpen_compl)))
  · refine ⟨mem_interior_iff_mem_nhds.mpr hN, ?_, ?_⟩
    · exact Set.mem_iInter₂.mpr fun i hi => hclA i (Finset.mem_filter.mp hi).2
    · exact Set.mem_iInter₂.mpr fun i hi => (Finset.mem_filter.mp hi).2
  · intro i hi y hy
    exact Set.mem_iInter₂.mp hy.2.1 i hi
  · intro i hi
    by_cases hiF : i ∈ F
    · have hix : x ∉ closure (A i) := fun hmem => hi (Finset.mem_filter.mpr ⟨hiF, hmem⟩)
      exact Set.disjoint_left.mpr fun y hy hyA =>
        (Set.mem_iInter₂.mp hy.2.2 i (Finset.mem_filter.mpr ⟨hiF, hix⟩)) hyA
    · refine Set.disjoint_left.mpr fun y hy hyA => hiF ?_
      rw [hF, Set.Finite.mem_toFinset]
      exact ⟨y, hyA, interior_subset hy.1⟩

/-! ## Degreewise `Γ`-surjectivity and the quotient identification -/

set_option backward.isDefEq.respectTransparency false in
/-- **Degreewise `Γ`-surjectivity of the comparison map** (the Warner
gluing): on a paracompact Hausdorff space, every global section of a
sheafified cochain sheaf is the image of a genuine global singular cochain
under the comparison map.  Local representatives exist by the stalk bridges;
a subordinate partition selects a representative per simplex
(`selectCochain`); the partition-sum identity shows the selection maps onto
the given section.  This is a statement about sections in one degree at a
time; nothing about cohomology is stated or implied.-/
theorem gammaComparison_surjective (X : TopCat.{0})
    [ParacompactSpace ↑X] [T2Space ↑X] (n : ℕ) :
    Function.Surjective ((gammaComparison X).f n) := by
  intro s
  choose V hxV b hb using fun x : ↑X => exists_localRep X n s x
  obtain ⟨A, hA, hclA, hlf⟩ := exists_subordinate_partition V
    (fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩)
  refine ⟨selectCochain X n A V hA b, ?_⟩
  show (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)).app
      (op ⊤) (selectCochain X n A V hA b) = s
  choose O hxO T hOV hOT using fun x : ↑X => exists_adequate_open X A V hclA hlf x
  refine ((sheafifiedCochainComplex X).X n).eq_of_locally_eq' O ⊤
    (fun x => homOfLE le_top) (fun y _ => Opens.mem_iSup.mpr ⟨y, hxO y⟩) _ _ (fun x => ?_)
  have hstep1 : ((sheafifiedCochainComplex X).X n).1.map (homOfLE (le_top : O x ≤ ⊤)).op
      ((toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)).app
        (op ⊤) (selectCochain X n A V hA b))
      = (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)).app
        (op (O x)) (((singularPresheafComplex X).X n).map (homOfLE (le_top : O x ≤ ⊤)).op
          (selectCochain X n A V hA b)) :=
    (unit_res ((singularPresheafComplex X).X n) (homOfLE (le_top : O x ≤ ⊤))
      (selectCochain X n A V hA b)).symm
  rw [hstep1,
    res_selectCochain X n A V hA b (T x) (hOV x)
      (fun i hi => ((hOT x) i hi).mono_right subset_closure),
    map_sum]
  have hterm : ∀ i : {j // j ∈ T x},
      (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)).app
          (op (O x)) ((partitionEndo X (A i.1) n).app (op (O x))
            (((singularPresheafComplex X).X n).map (homOfLE (hOV x i.1 i.2)).op (b i.1)))
        = (partitionEndoSheaf X (A i.1) n).hom.app (op (O x))
          (((sheafifiedCochainComplex X).X n).1.map (homOfLE (le_top : O x ≤ ⊤)).op s) := by
    intro i
    rw [unit_partitionEndo_app X (A i.1) n (O x),
      unit_res ((singularPresheafComplex X).X n) (homOfLE (hOV x i.1 i.2)) (b i.1),
      hb i.1]
    congr 1
    exact res_res' ((sheafifiedCochainComplex X).X n) (homOfLE (hOV x i.1 i.2))
      (homOfLE (le_top : V i.1 ≤ ⊤)) (homOfLE (le_top : O x ≤ ⊤)) s
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_attach (T x) (fun i => (partitionEndoSheaf X (A i) n).hom.app (op (O x))
      (((sheafifiedCochainComplex X).X n).1.map (homOfLE (le_top : O x ≤ ⊤)).op s))]
  have hone : ∀ y ∈ ((O x : Opens X) : Set ↑X), ∃! i, i ∈ T x ∧ y ∈ A i := by
    intro y hy
    obtain ⟨i₀, hi₀, huniq⟩ := hA y
    have hiT : i₀ ∈ T x := by
      by_contra hns
      exact Set.disjoint_left.mp ((hOT x) i₀ hns) hy (subset_closure hi₀)
    exact ⟨i₀, ⟨hiT, hi₀⟩, fun k hk => huniq k hk.2⟩
  exact sum_partitionEndoSheaf_app_apply X A (T x) n hone
    (((sheafifiedCochainComplex X).X n).1.map (homOfLE (le_top : O x ≤ ⊤)).op s)

set_option backward.isDefEq.respectTransparency false in
/-- **The degreewise identification** (group-level, one degree at a time):
on a paracompact Hausdorff space, the global sections of the `n`-th
sheafified cochain sheaf are identified, as an abelian group, with the global
singular `n`-cochains modulo the locally-zero ones.  Exactly this scope and
exactly degreewise; no chain-level or cohomology-level statement is made.-/
def gammaQuotientEquiv (X : TopCat.{0}) [ParacompactSpace ↑X] [T2Space ↑X] (n : ℕ) :
    (↑(((singularPresheafComplex X).X n).obj (op (⊤ : Opens X)))
        ⧸ locallyZeroSubgroup X n)
      ≃+ ↑(((sheafifiedCochainComplex X).X n).1.obj (op (⊤ : Opens X))) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_gammaComparison X n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (((gammaComparison X).f n).hom)
      (gammaComparison_surjective X n))

/-! ## The degree-0 seed -/

set_option backward.isDefEq.respectTransparency false in
/-- The topological `0`-simplex has a unique point.-/
lemma point_eq_vertexPt (p : ↑(SimplexCategory.toTop.{0}.obj ⦋0⦌)) : p = vertexPt 0 := by
  have hsum : ∑ i, p.down.1 i = 1 := p.down.2.2
  rw [Fin.sum_univ_one] at hsum
  refine ULift.down_injective (Subtype.ext (funext fun i => ?_))
  have hi : i = (0 : Fin (SimplexCategory.len ⦋0⦌ + 1)) :=
    Fin.ext (Nat.lt_one_iff.mp i.isLt)
  rw [hi]
  show p.down.1 0 = (Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) 0
  rw [Pi.single_eq_same]
  exact hsum

set_option backward.isDefEq.respectTransparency false in
/-- A locally-zero `0`-cochain is zero: a `0`-simplex is a point, contained in
every neighbourhood of itself.-/
theorem eq_zero_of_locallyZero_degreeZero (X : TopCat.{0})
    (s : ((singularPresheafComplex X).X 0).obj (op (⊤ : Opens X)))
    (hs : LocallyZero X ((singularPresheafComplex X).X 0) s) : s = 0 := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  obtain ⟨U, hxU, hU⟩ := hs (ambient (firstVertex σ))
  have h : SimplexIn σ U := by
    intro p
    rw [point_eq_vertexPt p]
    exact hxU
  calc (TopCat.toSSet.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).ιChainComplex σ
        ≫ (s : (chainsFunctor.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).X 0 ⟶ Qcoef)
      = (TopCat.toSSet.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).ιChainComplex
          (pushSimplex (homOfLE (le_top : U ≤ ⊤)) (corestrict σ h))
        ≫ (s : (chainsFunctor.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).X 0 ⟶ Qcoef) := by
        rw [pushSimplex_corestrict σ h (le_top : U ≤ ⊤)]
    _ = (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)).ιChainComplex (corestrict σ h)
        ≫ (((singularPresheafComplex X).X 0).map (homOfLE (le_top : U ≤ ⊤)).op s :
          (chainsFunctor.obj ((Opens.toTopCat X).obj U)).X 0 ⟶ Qcoef) :=
      (ι_res_cochain (homOfLE (le_top : U ≤ ⊤)) 0 s (corestrict σ h)).symm
    _ = (TopCat.toSSet.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).ιChainComplex σ
        ≫ (0 : (chainsFunctor.obj ((Opens.toTopCat X).obj (⊤ : Opens X))).X 0 ⟶ Qcoef) := by
        rw [hU]
        rw [Limits.comp_zero, Limits.comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- In degree `0` the comparison map is injective, on any space (the
locally-zero subgroup is trivial there).-/
theorem gammaComparison_injective_degreeZero (X : TopCat.{0}) :
    Function.Injective ((gammaComparison X).f 0) := by
  intro a b hab
  have hz : (gammaComparison X).f 0 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hlz := (gammaComparison_eq_zero_iff X 0 (a - b)).mp hz
  have h0 := eq_zero_of_locallyZero_degreeZero X (a - b) hlz
  exact sub_eq_zero.mp h0

/-! ## Metrizable-scope and analytic point-space corollaries -/

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise `Γ`-surjectivity at metrizable scope: metrizability supplies
Hausdorffness and paracompactness.-/
theorem gammaComparison_surjective_of_metrizable (X : TopCat.{0})
    [MetrizableSpace ↑X] (n : ℕ) :
    Function.Surjective ((gammaComparison X).f n) := by
  letI : MetricSpace ↑X := TopologicalSpace.metrizableSpaceMetric ↑X
  haveI : ParacompactSpace ↑X := inferInstance
  haveI : T2Space ↑X := inferInstance
  exact gammaComparison_surjective X n

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise identification at metrizable scope.-/
def gammaQuotientEquiv_of_metrizable (X : TopCat.{0}) [MetrizableSpace ↑X] (n : ℕ) :
    (↑(((singularPresheafComplex X).X n).obj (op (⊤ : Opens X)))
        ⧸ locallyZeroSubgroup X n)
      ≃+ ↑(((sheafifiedCochainComplex X).X n).1.obj (op (⊤ : Opens X))) := by
  letI : MetricSpace ↑X := TopologicalSpace.metrizableSpaceMetric ↑X
  haveI : ParacompactSpace ↑X := inferInstance
  haveI : T2Space ↑X := inferInstance
  exact gammaQuotientEquiv X n

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise `Γ`-surjectivity at the affine analytic point-space `CPoints A`
of a finite-type ℂ-algebra.-/
theorem gammaComparison_surjective_cpoints (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (n : ℕ) :
    Function.Surjective
      ((gammaComparison (TopCat.of (HodgePilot.Analytic.CPoints A))).f n) := by
  haveI : MetrizableSpace ↑(TopCat.of (HodgePilot.Analytic.CPoints A)) :=
    inferInstanceAs (MetrizableSpace (HodgePilot.Analytic.CPoints A))
  exact gammaComparison_surjective_of_metrizable
    (TopCat.of (HodgePilot.Analytic.CPoints A)) n

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise `Γ`-surjectivity at the scheme-level analytic point-space of an
affine ℂ-scheme.-/
theorem gammaComparison_surjective_spoints (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (n : ℕ) :
    Function.Surjective
      ((gammaComparison (TopCat.of (HodgePilot.Analytic.SPoints
        (HodgePilot.Analytic.structMor A)))).f n) := by
  haveI : MetrizableSpace ↑(TopCat.of (HodgePilot.Analytic.SPoints
      (HodgePilot.Analytic.structMor A))) :=
    inferInstanceAs (MetrizableSpace (HodgePilot.Analytic.SPoints
      (HodgePilot.Analytic.structMor A)))
  exact gammaComparison_surjective_of_metrizable
    (TopCat.of (HodgePilot.Analytic.SPoints (HodgePilot.Analytic.structMor A))) n

end HodgePilot.CochainGlobal
