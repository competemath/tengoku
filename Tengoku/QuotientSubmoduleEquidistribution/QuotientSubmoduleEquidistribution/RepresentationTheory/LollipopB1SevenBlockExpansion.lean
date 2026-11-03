import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1Modules
import Tengoku.Seed.Algebra.Category.FGModuleCat.Abelian
import Tengoku.Seed.Algebra.Category.ModuleCat.Biproducts
import Tengoku.Seed.LinearAlgebra.Dimension.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Expansion of the canonical seven-block live-path representation

This file isolates the basis-expansion half of the live-path
classification.  It starts with seven arbitrary finite-dimensional
multiplicity spaces, forms the canonical block representation, and identifies
its genuine module with a finite biproduct of the seven named modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SevenBlockExpansion

universe u

variable (K : Type u) [Field K]

/-- The seven multiplicity spaces, without any chosen bases.-/
structure MultiplicitySpaces where
  x : FGModuleCat.{u} K
  u : FGModuleCat.{u} K
  w : FGModuleCat.{u} K
  p : FGModuleCat.{u} K
  s1 : FGModuleCat.{u} K
  a : FGModuleCat.{u} K
  s2 : FGModuleCat.{u} K

variable (S : MultiplicitySpaces K)

/-- The common coordinate space for the tops or lowers of the four
length-two blocks.-/
abbrev FourSpace := (((S.x × S.u) × S.w) × S.p)

/-- Source vertex of the canonical seven-block representation.  The first
`FourSpace` contains the loop tops; the second contains their lowers.-/
abbrev NormalVertexOne :=
  FourSpace K S × ((FourSpace K S × S.s1) × S.a)

/-- Target vertex of the canonical seven-block representation.-/
abbrev NormalVertexTwo :=
  (((S.u × S.w) × (S.p × S.p)) × S.a) × S.s2

abbrev normalV1 : FGModuleCat.{u} K :=
  FGModuleCat.of K (NormalVertexOne K S)

abbrev normalV2 : FGModuleCat.{u} K :=
  FGModuleCat.of K (NormalVertexTwo K S)

/-- The loop sends every `X/U/W/P` top coordinate to its lower coordinate
and kills every other coordinate.-/
def normalLoop : normalV1 K S ⟶ normalV1 K S :=
  FGModuleCat.ofHom
    { toFun := fun z => (0, ((z.1, 0), 0))
      map_add' := by intro z w; ext <;> simp
      map_smul' := by intro c z; ext <;> simp }

/-- The stem is live on the `U` lower, `W` top, both `P` coordinates, and
the loop-zero `A` coordinate.-/
def normalStem : normalV1 K S ⟶ normalV2 K S :=
  FGModuleCat.ofHom
    { toFun := fun z =>
        ((((z.2.1.1.1.1.2, z.1.1.2),
            (z.2.1.1.2, z.1.2)),
          z.2.2), 0)
      map_add' := by intro z w; ext <;> simp
      map_smul' := by intro c z; ext <;> simp }

/-- The canonical seven-block live-path representation attached to the
multiplicity spaces.-/
def normalRep : FiniteB1Rep K where
  V₁ := normalV1 K S
  V₂ := normalV2 K S
  loop := normalLoop K S
  stem := normalStem K S
  loop_sq := by intro z; rfl

/--
@isnad1 id=eq.0h3v.s10.75a6279505ca from=translated src=- shape=b5d63d35 vocab=5bbb88e6
-/
@[simp] theorem normalLoop_apply (z : NormalVertexOne K S) :
    (normalRep K S).loop.hom.hom z = (0, ((z.1, 0), 0)) := rfl

/--
@isnad1 id=eq.0h3v.s10.7c6474bba927 from=translated src=- shape=07ecc80f vocab=a8571851
-/
@[simp] theorem normalStem_apply (z : NormalVertexOne K S) :
    (normalRep K S).stem.hom.hom z =
      ((((z.2.1.1.1.1.2, z.1.1.2),
          (z.2.1.1.2, z.1.2)),
        z.2.2), 0) := rfl

/-! ## Expansion into basis-indexed named blocks -/

inductive BlockTag where
  | s1
  | s2
  | x
  | a
  | u
  | w
  | p
  deriving DecidableEq

instance : Fintype BlockTag where
  elems := {.s1, .s2, .x, .a, .u, .w, .p}
  complete t := by cases t <;> simp

def multiplicitySpace : BlockTag → FGModuleCat.{u} K
  | .s1 => S.s1
  | .s2 => S.s2
  | .x => S.x
  | .a => S.a
  | .u => S.u
  | .w => S.w
  | .p => S.p

def blockMultiplicity (t : BlockTag) : ℕ :=
  Module.finrank K (multiplicitySpace K S t)

abbrev BlockIndex := Σ t : BlockTag, Fin (blockMultiplicity K S t)

def namedBlockData : BlockTag → FiniteB1Rep K
  | .s1 => S1Data K
  | .s2 => S2Data K
  | .x => XData K
  | .a => AData K
  | .u => UData K
  | .w => WData K
  | .p => PData K

abbrev namedBlockCarrier (i : BlockIndex K S) :=
  FiniteB1Rep.Carrier K (namedBlockData (K := K) i.1)

def namedBlockModule (i : BlockIndex K S) : FGModuleCat (B1Model K) :=
  FiniteB1Rep.asFGModule K (namedBlockData (K := K) i.1)

def blockBasisEquiv (t : BlockTag) :
    multiplicitySpace K S t ≃ₗ[K]
      (Fin (blockMultiplicity K S t) → K) :=
  (Module.finBasis K (multiplicitySpace K S t)).equivFun

/--
@isnad1 id=eq.0h4v.s9.6e98d682f489 from=translated src=- shape=f9d7c6c2 vocab=d5eb8ef8
-/
@[simp] theorem blockBasisEquiv_zero_apply (t : BlockTag)
    (j : Fin (blockMultiplicity K S t)) :
    blockBasisEquiv K S t (0 : multiplicitySpace K S t) j = 0 := by
  rw [map_zero]
  rfl

/--
@isnad1 id=eq.0h3v.s9.1d90ca84d3b4 from=translated src=- shape=ca8c745d vocab=3c25f117
-/
@[simp] theorem s1BasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .s1)) :
    blockBasisEquiv K S .s1 (0 : S.s1) j = 0 := by
  change blockBasisEquiv K S .s1
    (0 : multiplicitySpace K S .s1) j = 0
  rw [map_zero]
  rfl

/--
@isnad1 id=eq.0h3v.s9.986897f9b9b6 from=translated src=- shape=ca8c745d vocab=3da2bbf4
-/
@[simp] theorem s2BasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .s2)) :
    blockBasisEquiv K S .s2 (0 : S.s2) j = 0 := by
  change blockBasisEquiv K S .s2
    (0 : multiplicitySpace K S .s2) j = 0
  rw [map_zero]
  rfl

/--
@isnad1 id=eq.0h3v.s9.0884bfde9fc8 from=translated src=- shape=ca8c745d vocab=3ede5cba
-/
@[simp] theorem xBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .x)) :
    blockBasisEquiv K S .x (0 : S.x) j = 0 := by
  change blockBasisEquiv K S .x
    (0 : multiplicitySpace K S .x) j = 0
  rw [map_zero]
  rfl

/--
@isnad1 id=eq.0h3v.s9.9a16c2e805b1 from=translated src=- shape=ca8c745d vocab=961603e4
-/
@[simp] theorem aBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .a)) :
    blockBasisEquiv K S .a (0 : S.a) j = 0 := by
  change blockBasisEquiv K S .a
    (0 : multiplicitySpace K S .a) j = 0
  rw [map_zero]
  rfl

/--
@isnad1 id=eq.0h3v.s9.ef20b403096e from=translated src=- shape=ca8c745d vocab=a7f02a6c
-/
@[simp] theorem uBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .u)) :
    blockBasisEquiv K S .u (0 : S.u) j = 0 := by
  change blockBasisEquiv K S .u
    (0 : multiplicitySpace K S .u) j = 0
  rw [map_zero]
  rfl

/--
@isnad1 id=eq.0h3v.s9.f8b9db7aae2b from=translated src=- shape=ca8c745d vocab=135c2b4a
-/
@[simp] theorem wBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .w)) :
    blockBasisEquiv K S .w (0 : S.w) j = 0 := by
  change blockBasisEquiv K S .w
    (0 : multiplicitySpace K S .w) j = 0
  rw [map_zero]
  rfl

/--
@isnad1 id=eq.0h3v.s9.446f45cee1d3 from=translated src=- shape=ca8c745d vocab=7bb8d748
-/
@[simp] theorem pBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .p)) :
    blockBasisEquiv K S .p (0 : S.p) j = 0 := by
  change blockBasisEquiv K S .p
    (0 : multiplicitySpace K S .p) j = 0
  rw [map_zero]
  rfl

/-- Concrete finite-product model of a finite biproduct in `FGModuleCat`.-/
def biproductIsoPiFG
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {J : Type} [Finite J] (f : J → FGModuleCat.{u} R) :
    biproduct f ≅ FGModuleCat.of R (∀ j, f j) := by
  let G := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  letI : PreservesBiproduct f G :=
    preservesBiproduct_of_preservesProduct G
  exact G.preimageIso
    (G.mapBiproduct f ≪≫
      ModuleCat.biproductIsoPi (fun j ↦ G.obj (f j)))

/--
@isnad1 id=eq.0h4v.s7.1d7e58544400 from=translated src=- shape=8eb7fec3 vocab=a5eec134
-/
@[simp] theorem carrier_fst_add (E : FiniteB1Rep K)
    (v w : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.fst K E (v + w) =
      FiniteB1Rep.fst K E v + FiniteB1Rep.fst K E w := rfl

/--
@isnad1 id=eq.0h4v.s7.4b893bb15d95 from=translated src=- shape=8eb7fec3 vocab=45150a44
-/
@[simp] theorem carrier_snd_add (E : FiniteB1Rep K)
    (v w : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.snd K E (v + w) =
      FiniteB1Rep.snd K E v + FiniteB1Rep.snd K E w := rfl

/--
@isnad1 id=eq.0h4v.s9.5ee73486731c from=translated src=- shape=2ab070c8 vocab=0100f6b4
-/
@[simp] theorem carrier_fst_smul (E : FiniteB1Rep K)
    (c : K) (v : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.fst K E (c • v) =
      c • FiniteB1Rep.fst K E v := rfl

/--
@isnad1 id=eq.0h4v.s9.dd0abf73f366 from=translated src=- shape=2ab070c8 vocab=56bb0e3a
-/
@[simp] theorem carrier_snd_smul (E : FiniteB1Rep K)
    (c : K) (v : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.snd K E (c • v) =
      c • FiniteB1Rep.snd K E v := rfl

/--
@isnad1 id=eq.0h4v.s6.6de90b4312ee from=translated src=- shape=c32c605b vocab=f18107e5
-/
@[simp] theorem carrier_fst_mk (E : FiniteB1Rep K)
    (v₁ : E.V₁) (v₂ : E.V₂) :
    FiniteB1Rep.fst K E
      ((v₁, v₂) : FiniteB1Rep.Carrier K E) = v₁ := rfl

/--
@isnad1 id=eq.0h4v.s6.0d0ea891295d from=translated src=- shape=9dbec2f8 vocab=f597644a
-/
@[simp] theorem carrier_snd_mk (E : FiniteB1Rep K)
    (v₁ : E.V₁) (v₂ : E.V₂) :
    FiniteB1Rep.snd K E
      ((v₁, v₂) : FiniteB1Rep.Carrier K E) = v₂ := rfl

/--
@isnad1 id=eq.0h3v.s5.d82b75335ecd from=translated src=- shape=2b604107 vocab=6f23c604
-/
@[simp] theorem carrier_fst_apply (E : FiniteB1Rep K)
    (v : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.fst K E v = v.1 := rfl

/--
@isnad1 id=eq.0h3v.s5.ac8ab5e97e2c from=translated src=- shape=a72d6f40 vocab=20ad247e
-/
@[simp] theorem carrier_snd_apply (E : FiniteB1Rep K)
    (v : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.snd K E v = v.2 := rfl

/--
@isnad1 id=eq.0h4v.s10.04c8f2f76c62 from=translated src=- shape=20c9369a vocab=e6d3bf3a
-/
@[simp] theorem normal_v1_fst_add (v w : NormalVertexOne K S) :
    (v + w).1 = v.1 + w.1 := rfl

/--
@isnad1 id=eq.0h4v.s10.55fa553370e6 from=translated src=- shape=9600c0e0 vocab=1314d4e0
-/
@[simp] theorem normal_v1_snd_add (v w : NormalVertexOne K S) :
    (v + w).2 = v.2 + w.2 := rfl

/--
@isnad1 id=eq.0h4v.s10.de2950567a1b from=translated src=- shape=ef80e3d2 vocab=8ea4732b
-/
@[simp] theorem normal_v2_fst_add (v w : NormalVertexTwo K S) :
    (v + w).1 = v.1 + w.1 := rfl

/--
@isnad1 id=eq.0h4v.s10.baac68559aa3 from=translated src=- shape=1e922cae vocab=161a455d
-/
@[simp] theorem normal_v2_snd_add (v w : NormalVertexTwo K S) :
    (v + w).2 = v.2 + w.2 := rfl

/--
@isnad1 id=eq.0h4v.s12.e62468df4d32 from=translated src=- shape=8a0b67ed vocab=b13801ea
-/
@[simp] theorem normal_v1_fst_smul (c : K) (v : NormalVertexOne K S) :
    (c • v).1 = c • v.1 := rfl

/--
@isnad1 id=eq.0h4v.s12.855072571964 from=translated src=- shape=891170ad vocab=789d31b5
-/
@[simp] theorem normal_v1_snd_smul (c : K) (v : NormalVertexOne K S) :
    (c • v).2 = c • v.2 := rfl

/--
@isnad1 id=eq.0h4v.s12.e788596b8909 from=translated src=- shape=8d614e67 vocab=36f12cfa
-/
@[simp] theorem normal_v2_fst_smul (c : K) (v : NormalVertexTwo K S) :
    (c • v).1 = c • v.1 := rfl

/--
@isnad1 id=eq.0h4v.s11.2b068bbc347f from=translated src=- shape=1bdddf83 vocab=b5b3e880
-/
@[simp] theorem normal_v2_snd_smul (c : K) (v : NormalVertexTwo K S) :
    (c • v).2 = c • v.2 := rfl

/--
@isnad1 id=eq.0h2v.s10.71dd57f1fba7 from=translated src=- shape=302632ce vocab=a4cc5e98
-/
@[simp] theorem normal_v1_zero_eq :
    (0 : (normalRep K S).V₁) =
      ((0, 0) : NormalVertexOne K S) := rfl

/--
@isnad1 id=eq.0h2v.s10.6f0a917291f1 from=translated src=- shape=2968e325 vocab=ddb63912
-/
@[simp] theorem normal_v2_zero_eq :
    (0 : (normalRep K S).V₂) =
      ((0, 0) : NormalVertexTwo K S) := rfl

/--
@isnad1 id=eq.0h2v.s8.ca46d9de5d95 from=translated src=- shape=73f6f436 vocab=53bc6f38
-/
theorem rep_v1_zero_add (E : FiniteB1Rep K) :
    (0 : E.V₁) + 0 = 0 := zero_add 0

/--
@isnad1 id=eq.0h2v.s8.512806bca19c from=translated src=- shape=73f6f436 vocab=f7f8d16f
-/
theorem rep_v2_zero_add (E : FiniteB1Rep K) :
    (0 : E.V₂) + 0 = 0 := zero_add 0

/--
@isnad1 id=eq.0h3v.s9.bd75b8a69e8d from=translated src=- shape=44180987 vocab=b48a4d6d
-/
theorem rep_v1_smul_zero (E : FiniteB1Rep K) (c : K) :
    c • (0 : E.V₁) = 0 := smul_zero c

/--
@isnad1 id=eq.0h3v.s9.18bd336a8ffb from=translated src=- shape=44180987 vocab=d62b4569
-/
theorem rep_v2_smul_zero (E : FiniteB1Rep K) (c : K) :
    c • (0 : E.V₂) = 0 := smul_zero c

/--
@isnad1 id=eq.0h2v.s10.2d3dc9655a60 from=translated src=- shape=ce3ad5f6 vocab=fd0bbd68
-/
@[simp] theorem S1_loop_apply (z : (S1Data K).V₁) :
    (S1Data K).loop.hom.hom z = 0 := rfl

/--
@isnad1 id=eq.0h2v.s10.f3b6cb11852a from=translated src=- shape=ce3ad5f6 vocab=bde4cc24
-/
@[simp] theorem S2_loop_apply (z : (S2Data K).V₁) :
    (S2Data K).loop.hom.hom z = 0 := rfl

/--
@isnad1 id=eq.0h2v.s9.b7b872483dc7 from=translated src=- shape=346dbcc3 vocab=0b3bc9ed
-/
@[simp] theorem X_loop_apply (z : (XData K).V₁) :
    (XData K).loop.hom.hom z = (0, z.1) := rfl

/--
@isnad1 id=eq.0h2v.s10.797465be9c6d from=translated src=- shape=ce3ad5f6 vocab=a44eb465
-/
@[simp] theorem A_loop_apply (z : (AData K).V₁) :
    (AData K).loop.hom.hom z = 0 := rfl

/--
@isnad1 id=eq.0h2v.s9.87be5a247cc2 from=translated src=- shape=346dbcc3 vocab=bf14282a
-/
@[simp] theorem U_loop_apply (z : (UData K).V₁) :
    (UData K).loop.hom.hom z = (0, z.1) := rfl

/--
@isnad1 id=eq.0h2v.s9.17b9c579fde3 from=translated src=- shape=346dbcc3 vocab=e470a382
-/
@[simp] theorem W_loop_apply (z : (WData K).V₁) :
    (WData K).loop.hom.hom z = (0, z.1) := rfl

/--
@isnad1 id=eq.0h2v.s9.5f7878ddff20 from=translated src=- shape=346dbcc3 vocab=61902988
-/
@[simp] theorem P_loop_apply (z : (PData K).V₁) :
    (PData K).loop.hom.hom z = (0, z.1) := rfl

/--
@isnad1 id=eq.0h2v.s10.4a52bf7ebb67 from=translated src=- shape=c1beb73a vocab=f6e97b78
-/
@[simp] theorem S1_stem_apply (z : (S1Data K).V₁) :
    (S1Data K).stem.hom.hom z = 0 := rfl

/--
@isnad1 id=eq.0h2v.s10.cd19ea1e8d65 from=translated src=- shape=c1beb73a vocab=d9a12a96
-/
@[simp] theorem S2_stem_apply (z : (S2Data K).V₁) :
    (S2Data K).stem.hom.hom z = 0 := rfl

/--
@isnad1 id=eq.0h2v.s10.797104af65b9 from=translated src=- shape=c1beb73a vocab=f75de654
-/
@[simp] theorem X_stem_apply (z : (XData K).V₁) :
    (XData K).stem.hom.hom z = 0 := rfl

/--
@isnad1 id=eq.0h2v.s9.e07b1003e94d from=translated src=- shape=346577d5 vocab=3643f0e1
-/
@[simp] theorem A_stem_apply (z : (AData K).V₁) :
    (AData K).stem.hom.hom z = z := rfl

/--
@isnad1 id=eq.0h2v.s9.6cafc5451948 from=translated src=- shape=fb2e4d85 vocab=b203239e
-/
@[simp] theorem U_stem_apply (z : (UData K).V₁) :
    (UData K).stem.hom.hom z = z.2 := rfl

/--
@isnad1 id=eq.0h2v.s9.f29ff4f2ad64 from=translated src=- shape=fb2e4d85 vocab=940658d0
-/
@[simp] theorem W_stem_apply (z : (WData K).V₁) :
    (WData K).stem.hom.hom z = z.1 := rfl

/--
@isnad1 id=eq.0h2v.s9.62afd26e9bf3 from=translated src=- shape=346577d5 vocab=0af37ab8
-/
@[simp] theorem P_stem_apply (z : (PData K).V₁) :
    (PData K).stem.hom.hom z = z := rfl

/-! The following named linear projections avoid transparency problems caused
by the separately derived module structure on `FiniteB1Rep.Carrier`. -/

def carrierV1Linear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] NormalVertexOne K S where
  toFun := FiniteB1Rep.fst K (normalRep K S)
  map_add' := carrier_fst_add K (normalRep K S)
  map_smul' := carrier_fst_smul K (normalRep K S)

def carrierV2Linear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] NormalVertexTwo K S where
  toFun := FiniteB1Rep.snd K (normalRep K S)
  map_add' := carrier_snd_add K (normalRep K S)
  map_smul' := carrier_snd_smul K (normalRep K S)

def normalV1TopLinear : NormalVertexOne K S →ₗ[K] FourSpace K S where
  toFun := Prod.fst
  map_add' := normal_v1_fst_add K S
  map_smul' := normal_v1_fst_smul K S

def normalV1RestLinear :
    NormalVertexOne K S →ₗ[K] ((FourSpace K S × S.s1) × S.a) where
  toFun := Prod.snd
  map_add' := normal_v1_snd_add K S
  map_smul' := normal_v1_snd_smul K S

abbrev NormalStemCoords :=
  ((S.u × S.w) × (S.p × S.p)) × S.a

def normalV2StemLinear :
    NormalVertexTwo K S →ₗ[K] NormalStemCoords K S where
  toFun := Prod.fst
  map_add' := normal_v2_fst_add K S
  map_smul' := normal_v2_fst_smul K S

def normalV2TailLinear : NormalVertexTwo K S →ₗ[K] S.s2 where
  toFun := Prod.snd
  map_add' := normal_v2_snd_add K S
  map_smul' := normal_v2_snd_smul K S

def fourXLinear : FourSpace K S →ₗ[K] S.x :=
  (LinearMap.fst K S.x S.u).comp
    ((LinearMap.fst K (S.x × S.u) S.w).comp
      (LinearMap.fst K ((S.x × S.u) × S.w) S.p))

def fourULinear : FourSpace K S →ₗ[K] S.u :=
  (LinearMap.snd K S.x S.u).comp
    ((LinearMap.fst K (S.x × S.u) S.w).comp
      (LinearMap.fst K ((S.x × S.u) × S.w) S.p))

def fourWLinear : FourSpace K S →ₗ[K] S.w :=
  (LinearMap.snd K (S.x × S.u) S.w).comp
    (LinearMap.fst K ((S.x × S.u) × S.w) S.p)

def fourPLinear : FourSpace K S →ₗ[K] S.p :=
  LinearMap.snd K ((S.x × S.u) × S.w) S.p

def topFourLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] FourSpace K S :=
  (normalV1TopLinear K S).comp (carrierV1Linear K S)

def lowerFourLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] FourSpace K S :=
  (LinearMap.fst K (FourSpace K S) S.s1).comp
    ((LinearMap.fst K (FourSpace K S × S.s1) S.a).comp
      ((normalV1RestLinear K S).comp (carrierV1Linear K S)))

def s1Linear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.s1 :=
  (LinearMap.snd K (FourSpace K S) S.s1).comp
    ((LinearMap.fst K (FourSpace K S × S.s1) S.a).comp
      ((normalV1RestLinear K S).comp (carrierV1Linear K S)))

def aOneLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.a :=
  (LinearMap.snd K (FourSpace K S × S.s1) S.a).comp
    ((normalV1RestLinear K S).comp (carrierV1Linear K S))

def stemCoordsLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] NormalStemCoords K S :=
  (normalV2StemLinear K S).comp (carrierV2Linear K S)

def uTailLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.u :=
  (LinearMap.fst K S.u S.w).comp
    ((LinearMap.fst K (S.u × S.w) (S.p × S.p)).comp
      ((LinearMap.fst K ((S.u × S.w) × (S.p × S.p)) S.a).comp
        (stemCoordsLinear K S)))

def wTailLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.w :=
  (LinearMap.snd K S.u S.w).comp
    ((LinearMap.fst K (S.u × S.w) (S.p × S.p)).comp
      ((LinearMap.fst K ((S.u × S.w) × (S.p × S.p)) S.a).comp
        (stemCoordsLinear K S)))

def pTopTailLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.p :=
  (LinearMap.snd K S.p S.p).comp
    ((LinearMap.snd K (S.u × S.w) (S.p × S.p)).comp
      ((LinearMap.fst K ((S.u × S.w) × (S.p × S.p)) S.a).comp
        (stemCoordsLinear K S)))

def pLowerTailLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.p :=
  (LinearMap.fst K S.p S.p).comp
    ((LinearMap.snd K (S.u × S.w) (S.p × S.p)).comp
      ((LinearMap.fst K ((S.u × S.w) × (S.p × S.p)) S.a).comp
        (stemCoordsLinear K S)))

def aTwoLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.a :=
  (LinearMap.snd K ((S.u × S.w) × (S.p × S.p)) S.a).comp
    (stemCoordsLinear K S)

def s2Linear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.s2 :=
  (normalV2TailLinear K S).comp (carrierV2Linear K S)

def basisCoord (t : BlockTag) (j : Fin (blockMultiplicity K S t)) :
    multiplicitySpace K S t →ₗ[K] K :=
  (LinearMap.proj j).comp (blockBasisEquiv K S t).toLinearMap

def blockComponent (i : BlockIndex K S) :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K]
      namedBlockCarrier K S i := by
  rcases i with ⟨t, j⟩
  cases t with
  | s1 =>
      exact ((basisCoord K S .s1 j).comp (s1Linear K S)).prod 0
  | s2 =>
      exact (0 : FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K]
        (Fin 0 → K)).prod
          ((basisCoord K S .s2 j).comp (s2Linear K S))
  | x =>
      exact (((basisCoord K S .x j).comp
          ((fourXLinear K S).comp (topFourLinear K S))).prod
        ((basisCoord K S .x j).comp
          ((fourXLinear K S).comp (lowerFourLinear K S)))).prod 0
  | a =>
      exact ((basisCoord K S .a j).comp (aOneLinear K S)).prod
        ((basisCoord K S .a j).comp (aTwoLinear K S))
  | u =>
      exact (((basisCoord K S .u j).comp
          ((fourULinear K S).comp (topFourLinear K S))).prod
        ((basisCoord K S .u j).comp
          ((fourULinear K S).comp (lowerFourLinear K S)))).prod
        ((basisCoord K S .u j).comp (uTailLinear K S))
  | w =>
      exact (((basisCoord K S .w j).comp
          ((fourWLinear K S).comp (topFourLinear K S))).prod
        ((basisCoord K S .w j).comp
          ((fourWLinear K S).comp (lowerFourLinear K S)))).prod
        ((basisCoord K S .w j).comp (wTailLinear K S))
  | p =>
      exact (((basisCoord K S .p j).comp
          ((fourPLinear K S).comp (topFourLinear K S))).prod
        ((basisCoord K S .p j).comp
          ((fourPLinear K S).comp (lowerFourLinear K S)))).prod
        (((basisCoord K S .p j).comp (pTopTailLinear K S)).prod
          ((basisCoord K S .p j).comp (pLowerTailLinear K S)))

/-- Read the canonical normal-form coordinates one basis coefficient at a
time as a family of the seven named modules.-/
def normalToBlockPi :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K]
      (∀ i, namedBlockCarrier K S i) :=
  LinearMap.pi (blockComponent K S)

/--
@isnad1 id=eq.0h4v.s10.6ee6b4ef7ef4 from=translated src=- shape=a961e6cc vocab=ca1b4d03
-/
@[simp] theorem blockComponent_s1_apply
    (j : Fin (blockMultiplicity K S .s1))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.s1, j⟩ v =
      (blockBasisEquiv K S .s1
        (FiniteB1Rep.fst K (normalRep K S) v).2.1.2 j, 0) := rfl

/--
@isnad1 id=eq.0h4v.s10.b54ad4dfc5ed from=translated src=- shape=a8baa7e2 vocab=2b66fc06
-/
@[simp] theorem blockComponent_s2_apply
    (j : Fin (blockMultiplicity K S .s2))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.s2, j⟩ v =
      (0, blockBasisEquiv K S .s2
        (FiniteB1Rep.snd K (normalRep K S) v).2 j) := rfl

/--
@isnad1 id=eq.0h4v.s11.27ad51a3bb24 from=translated src=- shape=8879cf2b vocab=9140c66e
-/
@[simp] theorem blockComponent_x_apply
    (j : Fin (blockMultiplicity K S .x))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.x, j⟩ v =
      ((blockBasisEquiv K S .x
          (FiniteB1Rep.fst K (normalRep K S) v).1.1.1.1 j,
        blockBasisEquiv K S .x
          (FiniteB1Rep.fst K (normalRep K S) v).2.1.1.1.1.1 j), 0) := rfl

/--
@isnad1 id=eq.0h4v.s10.519881a4dd62 from=translated src=- shape=c40a7757 vocab=3b2e0281
-/
@[simp] theorem blockComponent_a_apply
    (j : Fin (blockMultiplicity K S .a))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.a, j⟩ v =
      (blockBasisEquiv K S .a
          (FiniteB1Rep.fst K (normalRep K S) v).2.2 j,
        blockBasisEquiv K S .a
          (FiniteB1Rep.snd K (normalRep K S) v).1.2 j) := rfl

/--
@isnad1 id=eq.0h4v.s11.b2e7e9356769 from=translated src=- shape=240d3dd3 vocab=e41937e2
-/
@[simp] theorem blockComponent_u_apply
    (j : Fin (blockMultiplicity K S .u))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.u, j⟩ v =
      ((blockBasisEquiv K S .u
          (FiniteB1Rep.fst K (normalRep K S) v).1.1.1.2 j,
        blockBasisEquiv K S .u
          (FiniteB1Rep.fst K (normalRep K S) v).2.1.1.1.1.2 j),
        blockBasisEquiv K S .u
          (FiniteB1Rep.snd K (normalRep K S) v).1.1.1.1 j) := rfl

/--
@isnad1 id=eq.0h4v.s11.f7ca61bcb19e from=translated src=- shape=528ea352 vocab=8b7f3993
-/
@[simp] theorem blockComponent_w_apply
    (j : Fin (blockMultiplicity K S .w))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.w, j⟩ v =
      ((blockBasisEquiv K S .w
          (FiniteB1Rep.fst K (normalRep K S) v).1.1.2 j,
        blockBasisEquiv K S .w
          (FiniteB1Rep.fst K (normalRep K S) v).2.1.1.1.2 j),
        blockBasisEquiv K S .w
          (FiniteB1Rep.snd K (normalRep K S) v).1.1.1.2 j) := rfl

/--
@isnad1 id=eq.0h4v.s11.0dd1978025be from=translated src=- shape=878d8080 vocab=c0f8f904
-/
@[simp] theorem blockComponent_p_apply
    (j : Fin (blockMultiplicity K S .p))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.p, j⟩ v =
      ((blockBasisEquiv K S .p
          (FiniteB1Rep.fst K (normalRep K S) v).1.2 j,
        blockBasisEquiv K S .p
          (FiniteB1Rep.fst K (normalRep K S) v).2.1.1.2 j),
        (blockBasisEquiv K S .p
            (FiniteB1Rep.snd K (normalRep K S) v).1.1.2.2 j,
          blockBasisEquiv K S .p
            (FiniteB1Rep.snd K (normalRep K S) v).1.1.2.1 j)) := rfl

/-- Reassemble the seven multiplicity-space coordinates from a family of
named block coordinates.-/
def blockPiToNormal (g : ∀ i, namedBlockCarrier K S i) :
    FiniteB1Rep.Carrier K (normalRep K S) := by
  let xTop := (blockBasisEquiv K S .x).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .x)
      (g ⟨.x, j⟩)).1)
  let uTop := (blockBasisEquiv K S .u).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .u)
      (g ⟨.u, j⟩)).1)
  let wTop := (blockBasisEquiv K S .w).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .w)
      (g ⟨.w, j⟩)).1)
  let pTop := (blockBasisEquiv K S .p).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).1)
  let xLower := (blockBasisEquiv K S .x).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .x)
      (g ⟨.x, j⟩)).2)
  let uLower := (blockBasisEquiv K S .u).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .u)
      (g ⟨.u, j⟩)).2)
  let wLower := (blockBasisEquiv K S .w).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .w)
      (g ⟨.w, j⟩)).2)
  let pLower := (blockBasisEquiv K S .p).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).2)
  let s1 := (blockBasisEquiv K S .s1).symm (fun j =>
    FiniteB1Rep.fst K (namedBlockData (K := K) .s1)
      (g ⟨.s1, j⟩))
  let aOne := (blockBasisEquiv K S .a).symm (fun j =>
    FiniteB1Rep.fst K (namedBlockData (K := K) .a)
      (g ⟨.a, j⟩))
  let uTail := (blockBasisEquiv K S .u).symm (fun j =>
    FiniteB1Rep.snd K (namedBlockData (K := K) .u)
      (g ⟨.u, j⟩))
  let wTail := (blockBasisEquiv K S .w).symm (fun j =>
    FiniteB1Rep.snd K (namedBlockData (K := K) .w)
      (g ⟨.w, j⟩))
  let pTopTail := (blockBasisEquiv K S .p).symm (fun j =>
    (FiniteB1Rep.snd K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).1)
  let pLowerTail := (blockBasisEquiv K S .p).symm (fun j =>
    (FiniteB1Rep.snd K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).2)
  let aTwo := (blockBasisEquiv K S .a).symm (fun j =>
    FiniteB1Rep.snd K (namedBlockData (K := K) .a)
      (g ⟨.a, j⟩))
  let s2 := (blockBasisEquiv K S .s2).symm (fun j =>
    FiniteB1Rep.snd K (namedBlockData (K := K) .s2)
      (g ⟨.s2, j⟩))
  exact
    (((((xTop, uTop), wTop), pTop),
      (((((xLower, uLower), wLower), pLower), s1), aOne)),
      ((((uTail, wTail), (pLowerTail, pTopTail)), aTwo), s2))

/-! ## Genuine-module linearity and the biproduct endpoint -/

/-- Coordinate expansion in the five distinguished algebra generators.
@isnad1 id=eq.0h2v.s9.0a10145bde6a from=translated src=- shape=5a71a4f0 vocab=5017c10a
-/
theorem algebra_coordinate_decomposition (r : B1Model K) :
    r = (TrivSqZeroExt.fst r).1.fst • e1 K +
      (TrivSqZeroExt.fst r).2 • e2 K +
      (TrivSqZeroExt.fst r).1.snd • x K +
      (TrivSqZeroExt.snd r).fst • a K +
      (TrivSqZeroExt.snd r).snd • u K := by
  ext <;> simp [e1, e2, x, a, u]

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SevenBlockExpansion
