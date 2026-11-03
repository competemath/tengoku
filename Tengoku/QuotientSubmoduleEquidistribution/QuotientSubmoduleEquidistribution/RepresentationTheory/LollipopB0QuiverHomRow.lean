import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.Representation.Simple
import Tengoku.Seed.Algebra.Category.ModuleCat.EpiMono
import Tengoku.Seed.LinearAlgebra.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A free-quiver Hom row for the dead-path lollipop

The project foundation does not yet identify bound-quiver representations with modules over
the corresponding quotient path algebra.  It can nevertheless express the
five named representations and their morphisms: the relation equations are
extra predicates on free-quiver representations, while natural transformations
already impose exactly the usual commuting-square equations.

This file proves the easiest free-quiver row associated to `B₀`.  Every morphism from
`S₁`, `X`, `A`, or `P` to `S₂` is zero.  Equivalently, the quotient-side row
`{X,A,S₁,P}` omits `S₂`; after a module-category bridge this supplies the trace
bound `trace ≤ 0` required by `DeadPathCertificates.quotient_p_omissions`.
No module-category equivalence, indecomposable classification, or faithful-core
identification is asserted here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.QuiverLayer

universe u

inductive Vertex where
  | one
  | two
  deriving DecidableEq

inductive Arrow : Vertex → Vertex → Type
  | loop : Arrow .one .one
  | stem : Arrow .one .two

instance : Quiver Vertex where
  Hom := Arrow

abbrev loopPath : Quiver.Path Vertex.one Vertex.one :=
  Quiver.Hom.toPath (Arrow.loop : Vertex.one ⟶ Vertex.one)

abbrev stemPath : Quiver.Path Vertex.one Vertex.two :=
  Quiver.Hom.toPath (Arrow.stem : Vertex.one ⟶ Vertex.two)

variable (K : Type u) [Field K]

/-- A lollipop representation specified by its two spaces and two arrow maps.-/
def rep (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex :=
  Paths.lift
    { obj := fun v => match v with
        | .one => V1
        | .two => V2
      map := fun f => match f with
        | .loop => loop
        | .stem => stem }

/--
@isnad1 id=eq.0h5v.s6.0563cd8ecee4 from=translated src=- shape=9eb14033 vocab=f202ebbc
-/
@[simp]
theorem rep_obj_one (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    (rep K V1 V2 loop stem).obj .one = V1 := rfl

/--
@isnad1 id=eq.0h5v.s6.b095f14eac5a from=translated src=- shape=50845bf0 vocab=2d3edf28
-/
@[simp]
theorem rep_obj_two (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    (rep K V1 V2 loop stem).obj .two = V2 := rfl

/--
@isnad1 id=eq.0h5v.s7.0f7485d32505 from=translated src=- shape=38a11950 vocab=145679bc
-/
@[simp]
theorem rep_map_loop (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    (rep K V1 V2 loop stem).map loopPath = loop := by
  exact Paths.lift_toPath _ _

/--
@isnad1 id=eq.0h5v.s7.7721280506e1 from=translated src=- shape=e4891c31 vocab=67de24cb
-/
@[simp]
theorem rep_map_stem (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    (rep K V1 V2 loop stem).map stemPath = stem := by
  exact Paths.lift_toPath _ _

/-- The two relations defining a `B₀` representation.-/
structure IsB0Representation (M : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex) : Prop where
  loop_sq : M.map loopPath ≫ M.map loopPath = 0
  loop_stem : M.map loopPath ≫ M.map stemPath = 0

abbrev K1 : ModuleCat K := ModuleCat.of K K
abbrev K2 : ModuleCat K := ModuleCat.of K (K × K)

/-- The nilpotent Jordan arrow `(u,v) ↦ (0,u)`.-/
def jordan : K2 K ⟶ K2 K :=
  ModuleCat.ofHom
    { toFun := fun p => (0, p.1)
      map_add' := by simp
      map_smul' := by simp }

/-- The arrow map of the projective fork, `(u,v) ↦ u`.-/
def forkStem : K2 K ⟶ K1 K :=
  ModuleCat.ofHom (LinearMap.fst K K K)

abbrev S1 : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex := QuotientSubmoduleEquidistribution.Foundation.simpleRep K Vertex .one
abbrev S2 : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex := QuotientSubmoduleEquidistribution.Foundation.simpleRep K Vertex .two

/-- The two-dimensional nilpotent-loop representation.-/
def X : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex :=
  rep K (K2 K) (0 : ModuleCat K) (jordan K) 0

/-- The one-dimensional arrow representation.-/
def A : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex :=
  rep K (K1 K) (K1 K) 0 (𝟙 _)

/-- The fork-shaped representation at vertex `1`.-/
def P : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex :=
  rep K (K2 K) (K1 K) (jordan K) (forkStem K)

/--
@isnad1 id=isb0repr.0h1v.s3.cf0ff182a296 from=translated src=- shape=84bfdc15 vocab=cca7e487
-/
theorem isB0_S1 : IsB0Representation K (S1 K) := by
  constructor <;> rfl

/--
@isnad1 id=isb0repr.0h1v.s3.04b1266e982f from=translated src=- shape=84bfdc15 vocab=0c8516a0
-/
theorem isB0_S2 : IsB0Representation K (S2 K) := by
  constructor <;> rfl

/--
@isnad1 id=isb0repr.0h1v.s3.e7fe268aef1c from=translated src=- shape=84bfdc15 vocab=e490da22
-/
theorem isB0_X : IsB0Representation K (X K) := by
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    rfl
  · rfl

/--
@isnad1 id=isb0repr.0h1v.s3.aa09bf1a538a from=translated src=- shape=84bfdc15 vocab=e39628a1
-/
theorem isB0_A : IsB0Representation K (A K) := by
  constructor <;> rfl

/--
@isnad1 id=isb0repr.0h1v.s3.294746a63ee7 from=translated src=- shape=84bfdc15 vocab=63dc8c65
-/
theorem isB0_P : IsB0Representation K (P K) := by
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    rfl
  · apply ModuleCat.hom_ext
    ext p
    rfl

/-- Labels in the selected support of the quotient row obtained by adding `P` to the core.-/
inductive QuotientPRowLabel where
  | s1
  | x
  | a
  | p

def quotientPRowRep : QuotientPRowLabel → QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex
  | .s1 => S1 K
  | .x => X K
  | .a => A K
  | .p => P K

end QuotientSubmoduleEquidistribution.LollipopConcrete.QuiverLayer
