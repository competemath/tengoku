import Tengoku.HodgeStructuresLean4.HodgePilot.SingularCohomology
import Tengoku.Seed.Topology.Homotopy.Contractible
import Tengoku.Seed.Analysis.Convex.Contractible
import Tengoku.Seed.Analysis.Normed.Module.Connected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular cohomology of a contractible space: `ℚ` in degree 0, zero above

For a contractible space `U`, this file computes the singular cohomology of
`U` with rational coefficients — the cohomology of the house singular cochain
complex `HodgePilot.SingularCohomology.singularCochainFunctor`, the `ℚ`-linear
dual of Mathlib's singular chain complex — and nothing else:

* `isZero_singularCohomology_of_contractible` — for a contractible space `U`,
  the singular cohomology `Hⁿ(U, ℚ)` of the house singular-cochain carrier is
  zero in every degree `n ≠ 0`;
* `contractibleCohomologyZeroEquiv` — for a contractible space `U`, the
  degree-0 singular cohomology `H⁰(U, ℚ)` of the house singular-cochain
  carrier is `ℚ`, by a constructed additive equivalence;
* `isZero_singularCohomology_convex` / `convexCohomologyZeroEquiv` and
  `isZero_singularCohomology_ball` / `ballCohomologyZeroEquiv` — the same two
  statements instantiated on nonempty convex subsets of real topological
  vector spaces and on open balls in real normed spaces (which are
  contractible by `Convex.contractibleSpace` / `Metric.contractibleSpace_ball`).

Route: a contraction (a homotopy equivalence `U ≃ₕ Unit`, from
`ContractibleSpace.hequiv_unit`) induces, by the homotopy invariance of the
house carrier (`cohomology_congr_of_homotopy`), an isomorphism between the
singular cohomology of `U` and that of the one-point space
(`cohomologyIsoPoint`).  The singular chain complex of the one-point space is
homotopy equivalent to the single complex `pointModule[0]`
(`singularChainComplexFunctorIsoOfTotallyDisconnectedSpace` composed with
`ChainComplex.alternatingConstHomotopyEquiv`); `ℚ`-dualizing that homotopy
equivalence (`dualHomotopyEquiv`, via the house idiom
`dualFunctor.mapHomotopy` + `Homotopy.op`) and passing to cohomology
(`HomotopyEquiv.toHomologyIso`) reduces everything to the dual of a complex
concentrated in degree 0, whose cohomology is computed directly.

Everything in this file is a statement about the genuine singular-cochain
objects of `HodgePilot.SingularCohomology`, at the stated contractible /
convex / ball scopes only.  No ring structure, no naturality of the degree-0
equivalence, and nothing beyond those scopes is claimed.  Everything is at
universe `0`, forced by the `ModuleCat.{0} ℚ` coefficients of the house
carrier.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
  HodgePilot.SingularCohomology

noncomputable section

namespace HodgePilot.ContractibleSingular

/-- The `ℚ`-coefficient object.-/
abbrev Qcoef : QMod := ModuleCat.of ℚ ℚ

/-- The singular chain complex of a space with `ℚ`-coefficients (the complex
the house cochain functor dualizes).-/
abbrev singularChains (X : TopCat.{0}) : ChainComplex QMod ℕ :=
  ((singularChainComplexFunctor QMod).obj Qcoef).obj X

/-- The dual cochain complex of a chain complex of `ℚ`-modules, in exactly the
house spelling of `HodgePilot.SingularCohomology.singularCochainFunctor`.-/
abbrev dualComplex (K : ChainComplex QMod ℕ) : CochainComplex QMod ℕ :=
  (dualFunctor.mapHomologicalComplex ((ComplexShape.down ℕ).symm)).obj
    ((HomologicalComplex.opFunctor _ _).obj (op K))

/-- The `ℚ`-dual of a homotopy equivalence of chain complexes of `ℚ`-modules
is a homotopy equivalence of the dual cochain complexes (contravariantly).
This is pure homological bookkeeping: `Homotopy.op` followed by
`dualFunctor.mapHomotopy`, the house homotopy-transport idiom.-/
def dualHomotopyEquiv {K L : ChainComplex QMod ℕ} (E : HomotopyEquiv K L) :
    HomotopyEquiv (dualComplex L) (dualComplex K) where
  hom := (dualFunctor.mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor _ _).map E.hom.op)
  inv := (dualFunctor.mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor _ _).map E.inv.op)
  homotopyHomInvId := by
    refine (Homotopy.ofEq ?_).trans
      ((dualFunctor.mapHomotopy E.homotopyInvHomId.op).trans (Homotopy.ofEq (by simp; rfl)))
    rw [op_comp, Functor.map_comp, Functor.map_comp]; rfl
  homotopyInvHomId := by
    refine (Homotopy.ofEq ?_).trans
      ((dualFunctor.mapHomotopy E.homotopyHomInvId.op).trans (Homotopy.ofEq (by simp; rfl)))
    rw [op_comp, Functor.map_comp, Functor.map_comp]; rfl

/-! ## The one-point space and its dual singular complex -/

instance instTotallyDisconnectedSpaceUnit : TotallyDisconnectedSpace Unit :=
  ⟨fun _ _ _ => Set.subsingleton_of_subsingleton⟩

/-- The one-point space, the codomain of every contraction below.-/
abbrev pointSpace : TopCat.{0} := TopCat.of Unit

/-- The coefficient object of the one-point space's chain complex: the
coproduct of copies of `ℚ` indexed by the one point.-/
abbrev pointModule : QMod := ∐ fun _ : pointSpace => Qcoef

/-- The singular chain complex of the one-point space is homotopy equivalent
to the single complex with `pointModule` in degree 0: Mathlib's
totally-disconnected computation composed with
`ChainComplex.alternatingConstHomotopyEquiv`.-/
def pointChainsHomotopyEquiv :
    HomotopyEquiv (singularChains pointSpace)
      ((ChainComplex.single₀ QMod).obj pointModule) :=
  (HomotopyEquiv.ofIso
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace QMod Qcoef pointSpace)).trans
    (ChainComplex.alternatingConstHomotopyEquiv pointModule)

/-- The dual cochain complex of the one-point single complex has a zero object
in every degree `n ≠ 0` (the dual of a zero object is a zero object).-/
lemma isZero_dualSingle_X (n : ℕ) (hn : n ≠ 0) :
    IsZero ((dualComplex ((ChainComplex.single₀ QMod).obj pointModule)).X n) :=
  dualFunctor.map_isZero
    ((HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 pointModule n hn).op)

/-- The dual cochain complex of the one-point single complex is exact in every
degree `n ≠ 0` (its component there is a zero object).-/
lemma exactAt_dualSingle (n : ℕ) (hn : n ≠ 0) :
    (dualComplex ((ChainComplex.single₀ QMod).obj pointModule)).ExactAt n :=
  HomologicalComplex.ExactAt.of_isZero (isZero_dualSingle_X n hn)

/-- Homology data in degree 0 for the dual cochain complex of the one-point
single complex: both differentials at 0 vanish, so the degree-0 cohomology is
the degree-0 component.-/
def dualSingleHomologyDataZero :
    ((dualComplex ((ChainComplex.single₀ QMod).obj pointModule)).sc 0).HomologyData :=
  ShortComplex.HomologyData.ofZeros _
    ((dualComplex ((ChainComplex.single₀ QMod).obj pointModule)).shape _ 0 (by simp))
    (IsZero.eq_of_tgt
      (by simpa [CochainComplex.next] using isZero_dualSingle_X 1 one_ne_zero) _ _)

/-- The degree-0 cohomology of the dual cochain complex of the one-point
single complex is the `ℚ`-dual of `pointModule`.-/
def dualSingleHomologyZeroIso :
    (dualComplex ((ChainComplex.single₀ QMod).obj pointModule)).homology 0 ≅
      dualFunctor.obj (op pointModule) :=
  dualSingleHomologyDataZero.left.homologyIso ≪≫
    (dualFunctor.mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 pointModule).op).symm

/-! ## Hom-group equivalences (the house degree-0 idioms) -/

/-- Maps out of a coproduct are families of maps, additively.-/
def coproductHomAddEquiv {ι : Type} (f : ι → QMod) :
    ((∐ f) ⟶ Qcoef) ≃+ ∀ i, (f i ⟶ Qcoef) where
  toFun φ i := Sigma.ι f i ≫ φ
  invFun v := Sigma.desc v
  left_inv φ := Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_desc]
  right_inv v := funext fun i => Sigma.ι_desc v i
  map_add' φ ψ := funext fun i => Preadditive.comp_add _ _ _ _ _ _

/-- Endomorphisms of the coefficient module are scalars: `(ℚ ⟶ ℚ) ≃+ ℚ`.-/
def endQcoefEquiv : (Qcoef ⟶ Qcoef) ≃+ ℚ :=
  ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf ℚ ℚ ℚ).toAddEquiv

/-- The `ℚ`-dual of `pointModule` is `ℚ`: maps out of a one-point coproduct of
copies of `ℚ` into `ℚ` are scalars.-/
def dualPointModuleEquiv : (dualFunctor.obj (op pointModule) : QMod) ≃+ ℚ :=
  (coproductHomAddEquiv fun _ : pointSpace => Qcoef).trans
    ((AddEquiv.piUnique fun _ : pointSpace => (Qcoef ⟶ Qcoef)).trans endQcoefEquiv)

/-! ## Transport along a contraction -/

/-- A choice of contraction of a contractible space: a homotopy equivalence
with the one-point type.-/
def contraction (U : TopCat.{0}) [ContractibleSpace U] :
    ContinuousMap.HomotopyEquiv ↑U Unit :=
  (ContractibleSpace.hequiv_unit ↑U).some

/-- The forward map of the chosen contraction, as a morphism in `TopCat`.-/
def toPoint (U : TopCat.{0}) [ContractibleSpace U] : U ⟶ pointSpace :=
  TopCat.ofHom (contraction U).toFun

/-- The backward map of the chosen contraction, as a morphism in `TopCat`.-/
def fromPoint (U : TopCat.{0}) [ContractibleSpace U] : pointSpace ⟶ U :=
  TopCat.ofHom (contraction U).invFun

/-- The round trip through the point is homotopic to the identity of `U`.-/
def homotopyToFromId (U : TopCat.{0}) [ContractibleSpace U] :
    TopCat.Homotopy (toPoint U ≫ fromPoint U) (𝟙 U) :=
  (contraction U).left_inv.some

/-- The round trip through `U` is homotopic to the identity of the point.-/
def homotopyFromToId (U : TopCat.{0}) [ContractibleSpace U] :
    TopCat.Homotopy (fromPoint U ≫ toPoint U) (𝟙 pointSpace) :=
  (contraction U).right_inv.some

/-- **Transport along the contraction**: for a contractible space `U`, the
singular cohomology `Hⁿ(U, ℚ)` of the house singular-cochain carrier is
isomorphic to that of the one-point space, by the homotopy invariance of the
house carrier (`cohomology_congr_of_homotopy`).-/
def cohomologyIsoPoint (U : TopCat.{0}) [ContractibleSpace U] (n : ℕ) :
    (singularCohomologyFunctor n).obj (op U) ≅
      (singularCohomologyFunctor n).obj (op pointSpace) where
  hom := (singularCohomologyFunctor n).map (fromPoint U).op
  inv := (singularCohomologyFunctor n).map (toPoint U).op
  hom_inv_id := by
    rw [← Functor.map_comp, ← op_comp,
      cohomology_congr_of_homotopy (homotopyToFromId U) n, op_id,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp, ← op_comp,
      cohomology_congr_of_homotopy (homotopyFromToId U) n, op_id,
      CategoryTheory.Functor.map_id]

/-- The singular cohomology of the one-point space, computed by the dual of
the one-point single complex: the `ℚ`-dual of `pointChainsHomotopyEquiv`
passed to cohomology.-/
def pointCohomologyIso (n : ℕ) :
    (singularCohomologyFunctor n).obj (op pointSpace) ≅
      (dualComplex ((ChainComplex.single₀ QMod).obj pointModule)).homology n :=
  ((dualHomotopyEquiv pointChainsHomotopyEquiv).toHomologyIso n).symm

/-! ## The contractible-space computation -/

/-- **Vanishing above degree 0**: for a contractible space `U`, the singular
cohomology `Hⁿ(U, ℚ)` of the house singular-cochain carrier is zero in every
degree `n ≠ 0`.-/
theorem isZero_singularCohomology_of_contractible (U : TopCat.{0}) [ContractibleSpace U]
    (n : ℕ) (hn : n ≠ 0) :
    IsZero ((singularCohomologyFunctor n).obj (op U)) :=
  (((exactAt_dualSingle n hn).isZero_homology).of_iso (pointCohomologyIso n)).of_iso
    (cohomologyIsoPoint U n)

/-- **Degree 0 is `ℚ`**: for a contractible space `U`, the degree-0 singular
cohomology `H⁰(U, ℚ)` of the house singular-cochain carrier is `ℚ`, by a
constructed additive equivalence.-/
def contractibleCohomologyZeroEquiv (U : TopCat.{0}) [ContractibleSpace U] :
    (singularCohomologyFunctor 0).obj (op U) ≃+ ℚ :=
  ((cohomologyIsoPoint U 0 ≪≫ pointCohomologyIso 0 ≪≫
    dualSingleHomologyZeroIso).toLinearEquiv.toAddEquiv).trans dualPointModuleEquiv

/-! ## Instantiations: convex sets and balls

Nonempty convex subsets of real topological vector spaces and open balls in
real normed spaces are contractible (`Convex.contractibleSpace`,
`Metric.contractibleSpace_ball`), so the two computations above instantiate.
All statements remain statements about the genuine singular-cochain carrier
on those subspaces, and about nothing else. -/

section Convex

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- For a nonempty convex subset `s` of a real topological vector space, the
singular cohomology `Hⁿ(s, ℚ)` of the house singular-cochain carrier is zero
in every degree `n ≠ 0`.-/
theorem isZero_singularCohomology_convex {s : Set E} (hs : Convex ℝ s)
    (hne : s.Nonempty) (n : ℕ) (hn : n ≠ 0) :
    IsZero ((singularCohomologyFunctor n).obj (op (TopCat.of s))) :=
  haveI := hs.contractibleSpace hne
  isZero_singularCohomology_of_contractible (TopCat.of s) n hn

/-- For a nonempty convex subset `s` of a real topological vector space, the
degree-0 singular cohomology `H⁰(s, ℚ)` of the house singular-cochain carrier
is `ℚ`, by a constructed additive equivalence.-/
def convexCohomologyZeroEquiv {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty) :
    (singularCohomologyFunctor 0).obj (op (TopCat.of s)) ≃+ ℚ :=
  haveI := hs.contractibleSpace hne
  contractibleCohomologyZeroEquiv (TopCat.of s)

end Convex

section Ball

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For an open ball of positive radius in a real normed space, the singular
cohomology `Hⁿ(ball x r, ℚ)` of the house singular-cochain carrier is zero in
every degree `n ≠ 0`.-/
theorem isZero_singularCohomology_ball (x : E) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero ((singularCohomologyFunctor n).obj (op (TopCat.of (Metric.ball x r)))) :=
  haveI := Metric.contractibleSpace_ball (x := x) hr
  isZero_singularCohomology_of_contractible (TopCat.of (Metric.ball x r)) n hn

/-- For an open ball of positive radius in a real normed space, the degree-0
singular cohomology `H⁰(ball x r, ℚ)` of the house singular-cochain carrier is
`ℚ`, by a constructed additive equivalence.-/
def ballCohomologyZeroEquiv (x : E) {r : ℝ} (hr : 0 < r) :
    (singularCohomologyFunctor 0).obj (op (TopCat.of (Metric.ball x r))) ≃+ ℚ :=
  haveI := Metric.contractibleSpace_ball (x := x) hr
  contractibleCohomologyZeroEquiv (TopCat.of (Metric.ball x r))

end Ball

end HodgePilot.ContractibleSingular
