import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1Modules

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extracting finite live-path lollipop data from an arbitrary genuine module

The algebra idempotents split every finitely generated `B1Model`-module into
its two vertex spaces.  This file constructs the corresponding
`FiniteB1Rep` and a vector-space equivalence from its carrier back to the
original module.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.ModuleExtraction

universe u

variable (K : Type u) [Field K]

/-- A named scalar-restriction wrapper.  The wrapper prevents the induced
`K`-module instance from competing with unrelated module structures on the
same underlying type.-/
def RestrictedCarrier (M : FGModuleCat.{u} (B1Model K)) := M

instance (M : FGModuleCat.{u} (B1Model K)) :
    AddCommGroup (RestrictedCarrier K M) :=
  inferInstanceAs (AddCommGroup M)

instance (M : FGModuleCat.{u} (B1Model K)) :
    Module (B1Model K) (RestrictedCarrier K M) :=
  inferInstanceAs (Module (B1Model K) M)

instance (M : FGModuleCat.{u} (B1Model K)) :
    Module K (RestrictedCarrier K M) :=
  Module.compHom (RestrictedCarrier K M) (algebraMap K (B1Model K))

instance (M : FGModuleCat.{u} (B1Model K)) :
    IsScalarTower K (B1Model K) (RestrictedCarrier K M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance (M : FGModuleCat.{u} (B1Model K)) :
    Module.Finite K (RestrictedCarrier K M) :=
  Module.Finite.trans (B1Model K) (RestrictedCarrier K M)

/-- Multiplication by an algebra element, viewed as a `K`-linear map.-/
def actionLinear (M : FGModuleCat.{u} (B1Model K)) (r : B1Model K) :
    RestrictedCarrier K M →ₗ[K] RestrictedCarrier K M :=
  (Algebra.lsmul K K (RestrictedCarrier K M)) r

/--
@isnad1 id=eq.0h4v.s11.9eef8809fd0b from=translated src=- shape=5fe658da vocab=e6b9c7a6
-/
@[simp] theorem actionLinear_apply
    (M : FGModuleCat.{u} (B1Model K)) (r : B1Model K)
    (m : RestrictedCarrier K M) :
    actionLinear K M r m = r • m := rfl

/-- The vertex-one image.-/
def vertexOne (M : FGModuleCat.{u} (B1Model K)) :
    Submodule K (RestrictedCarrier K M) :=
  LinearMap.range (actionLinear K M (e1 K))

/-- The vertex-two image.-/
def vertexTwo (M : FGModuleCat.{u} (B1Model K)) :
    Submodule K (RestrictedCarrier K M) :=
  LinearMap.range (actionLinear K M (e2 K))

/--
@isnad1 id=eq.0h3v.s12.edb58709ea7c from=translated src=- shape=23f97458 vocab=ed48cc85
-/
theorem e1_fixed
    (M : FGModuleCat.{u} (B1Model K)) (v : vertexOne K M) :
    e1 K • (v.1 : RestrictedCarrier K M) = v.1 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change e1 K • (e1 K • m) = e1 K • m
  rw [← mul_smul, e1_sq]

/--
@isnad1 id=eq.0h3v.s12.e60bce4132da from=translated src=- shape=83aa8d0f vocab=97bd7c73
-/
theorem e2_kills_vertexOne
    (M : FGModuleCat.{u} (B1Model K)) (v : vertexOne K M) :
    e2 K • (v.1 : RestrictedCarrier K M) = 0 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change e2 K • (e1 K • m) = 0
  rw [← mul_smul, e2_mul_e1, zero_smul]

/--
@isnad1 id=eq.0h3v.s12.1f957e9b7d24 from=translated src=- shape=23f97458 vocab=15e484a3
-/
theorem e2_fixed
    (M : FGModuleCat.{u} (B1Model K)) (v : vertexTwo K M) :
    e2 K • (v.1 : RestrictedCarrier K M) = v.1 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change e2 K • (e2 K • m) = e2 K • m
  rw [← mul_smul, e2_sq]

/--
@isnad1 id=eq.0h3v.s12.695974fb4361 from=translated src=- shape=83aa8d0f vocab=a96500ac
-/
theorem e1_kills_vertexTwo
    (M : FGModuleCat.{u} (B1Model K)) (v : vertexTwo K M) :
    e1 K • (v.1 : RestrictedCarrier K M) = 0 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change e1 K • (e2 K • m) = 0
  rw [← mul_smul, e1_mul_e2, zero_smul]

/--
@isnad1 id=eq.0h3v.s12.39557cd695d4 from=translated src=- shape=83aa8d0f vocab=ee715458
-/
theorem x_kills_vertexTwo
    (M : FGModuleCat.{u} (B1Model K)) (v : vertexTwo K M) :
    x K • (v.1 : RestrictedCarrier K M) = 0 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change x K • (e2 K • m) = 0
  rw [← mul_smul, x_mul_e2, zero_smul]

/--
@isnad1 id=eq.0h3v.s12.90999e1af086 from=translated src=- shape=83aa8d0f vocab=08793549
-/
theorem a_kills_vertexTwo
    (M : FGModuleCat.{u} (B1Model K)) (v : vertexTwo K M) :
    a K • (v.1 : RestrictedCarrier K M) = 0 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change a K • (e2 K • m) = 0
  rw [← mul_smul, a_mul_e2, zero_smul]

/-- The loop induced by multiplication by `x`.-/
def extractedLoopLinear (M : FGModuleCat.{u} (B1Model K)) :
    vertexOne K M →ₗ[K] vertexOne K M where
  toFun v := ⟨x K • (v.1 : RestrictedCarrier K M), by
    refine ⟨x K • (v.1 : RestrictedCarrier K M), ?_⟩
    change e1 K • (x K • (v.1 : RestrictedCarrier K M)) =
      x K • v.1
    rw [← mul_smul, e1_mul_x] ⟩
  map_add' v w := by
    apply Subtype.ext
    exact smul_add (x K) v.1 w.1
  map_smul' c v := by
    apply Subtype.ext
    exact (smul_comm c (x K) v.1).symm

/-- The stem induced by multiplication by `a`.-/
def extractedStemLinear (M : FGModuleCat.{u} (B1Model K)) :
    vertexOne K M →ₗ[K] vertexTwo K M where
  toFun v := ⟨a K • (v.1 : RestrictedCarrier K M), by
    refine ⟨a K • (v.1 : RestrictedCarrier K M), ?_⟩
    change e2 K • (a K • (v.1 : RestrictedCarrier K M)) =
      a K • v.1
    rw [← mul_smul, e2_mul_a] ⟩
  map_add' v w := by
    apply Subtype.ext
    exact smul_add (a K) v.1 w.1
  map_smul' c v := by
    apply Subtype.ext
    exact (smul_comm c (a K) v.1).symm

/--
@isnad1 id=eq.0h3v.s14.56b57c38fd01 from=translated src=- shape=dba07d49 vocab=89597dcd
-/
theorem extractedLoop_sq
    (M : FGModuleCat.{u} (B1Model K)) (v : vertexOne K M) :
    extractedLoopLinear K M (extractedLoopLinear K M v) = 0 := by
  apply Subtype.ext
  change x K • (x K • (v.1 : RestrictedCarrier K M)) = 0
  rw [← mul_smul, x_sq, zero_smul]

/-- The finite representation extracted from an arbitrary genuine finitely
generated module.-/
def extractedRep (M : FGModuleCat.{u} (B1Model K)) : FiniteB1Rep K where
  V₁ := FGModuleCat.of K (vertexOne K M)
  V₂ := FGModuleCat.of K (vertexTwo K M)
  loop := FGModuleCat.ofHom (extractedLoopLinear K M)
  stem := FGModuleCat.ofHom (extractedStemLinear K M)
  loop_sq := extractedLoop_sq K M

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

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.ModuleExtraction
