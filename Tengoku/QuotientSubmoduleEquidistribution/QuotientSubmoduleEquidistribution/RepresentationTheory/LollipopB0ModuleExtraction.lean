import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0Modules

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extracting finite lollipop data from an arbitrary genuine module

The algebra idempotents split every finitely generated `B0Model`-module into
its two vertex spaces.  This file constructs the corresponding
`FiniteB0Rep` and a vector-space equivalence from its carrier back to the
original module.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.ModuleExtraction

universe u

variable (K : Type u) [Field K]

/-- A named scalar-restriction wrapper.  The wrapper prevents the induced
`K`-module instance from competing with unrelated module structures on the
same underlying type.-/
def RestrictedCarrier (M : FGModuleCat.{u} (B0Model K)) := M

instance (M : FGModuleCat.{u} (B0Model K)) :
    AddCommGroup (RestrictedCarrier K M) :=
  inferInstanceAs (AddCommGroup M)

instance (M : FGModuleCat.{u} (B0Model K)) :
    Module (B0Model K) (RestrictedCarrier K M) :=
  inferInstanceAs (Module (B0Model K) M)

instance (M : FGModuleCat.{u} (B0Model K)) :
    Module K (RestrictedCarrier K M) :=
  Module.compHom (RestrictedCarrier K M) (algebraMap K (B0Model K))

instance (M : FGModuleCat.{u} (B0Model K)) :
    IsScalarTower K (B0Model K) (RestrictedCarrier K M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance (M : FGModuleCat.{u} (B0Model K)) :
    Module.Finite K (RestrictedCarrier K M) :=
  Module.Finite.trans (B0Model K) (RestrictedCarrier K M)

/-- Multiplication by an algebra element, viewed as a `K`-linear map.-/
def actionLinear (M : FGModuleCat.{u} (B0Model K)) (r : B0Model K) :
    RestrictedCarrier K M →ₗ[K] RestrictedCarrier K M :=
  (Algebra.lsmul K K (RestrictedCarrier K M)) r

@[simp] theorem actionLinear_apply
    (M : FGModuleCat.{u} (B0Model K)) (r : B0Model K)
    (m : RestrictedCarrier K M) :
    actionLinear K M r m = r • m := rfl

/-- The vertex-one image.-/
def vertexOne (M : FGModuleCat.{u} (B0Model K)) :
    Submodule K (RestrictedCarrier K M) :=
  LinearMap.range (actionLinear K M (e1 K))

/-- The vertex-two image.-/
def vertexTwo (M : FGModuleCat.{u} (B0Model K)) :
    Submodule K (RestrictedCarrier K M) :=
  LinearMap.range (actionLinear K M (e2 K))

/-- The loop induced by multiplication by `x`.-/
def extractedLoopLinear (M : FGModuleCat.{u} (B0Model K)) :
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
def extractedStemLinear (M : FGModuleCat.{u} (B0Model K)) :
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

theorem extractedLoop_sq
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexOne K M) :
    extractedLoopLinear K M (extractedLoopLinear K M v) = 0 := by
  apply Subtype.ext
  change x K • (x K • (v.1 : RestrictedCarrier K M)) = 0
  rw [← mul_smul, x_sq, zero_smul]

theorem extractedStem_loop
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexOne K M) :
    extractedStemLinear K M (extractedLoopLinear K M v) = 0 := by
  apply Subtype.ext
  change a K • (x K • (v.1 : RestrictedCarrier K M)) = 0
  rw [← mul_smul, a_mul_x, zero_smul]

/-- The finite representation extracted from an arbitrary genuine finitely
generated module.-/
def extractedRep (M : FGModuleCat.{u} (B0Model K)) : FiniteB0Rep K where
  V₁ := FGModuleCat.of K (vertexOne K M)
  V₂ := FGModuleCat.of K (vertexTwo K M)
  loop := FGModuleCat.ofHom (extractedLoopLinear K M)
  stem := FGModuleCat.ofHom (extractedStemLinear K M)
  loop_sq := extractedLoop_sq K M
  stem_loop := extractedStem_loop K M

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.ModuleExtraction
