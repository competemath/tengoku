import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1AlgebraModel
import Tengoku.Seed.Algebra.Category.FGModuleCat.Basic
import Tengoku.Seed.LinearAlgebra.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genuine modules over the live-path lollipop model

Finite-dimensional data `L : V₁ → V₁`, `T : V₁ → V₂` with `L² = 0`
define a genuine module over `B1Model`.  The generator actions are

* `x(v₁,v₂) = (L v₁,0)`,
* `a(v₁,v₂) = (0,T v₁)`,
* `(a*x)(v₁,v₂) = (0,T(L v₁))`.

The seven named coordinate modules from the live-path table are then
constructed explicitly.  No indecomposability, pairwise-nonisomorphism, or
exhaustiveness statement is made here.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer

universe u

variable (K : Type u) [Field K]

variable (V₁ V₂ : Type u)
variable [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V₂] [Module K V₂]

/-- A scalar multiple of the proposed loop endomorphism.-/
def loopLinear (loop : V₁ →ₗ[K] V₁) :
    K →ₗ[K] Module.End K V₁ where
  toFun c := c • loop
  map_add' c d := by ext z; simp [add_smul]
  map_smul' c d := by ext z; simp [smul_smul]

/--
@isnad1 id=eq.1h5v.s10.b3ff80ba9d46 from=translated src=- shape=ee078138 vocab=ec9e0fbd
-/
theorem loopLinear_mul_eq_zero
    (loop : V₁ →ₗ[K] V₁)
    (hloop : ∀ z, loop (loop z) = 0)
    (c d : K) :
    loopLinear K V₁ loop c * loopLinear K V₁ loop d = 0 := by
  apply LinearMap.ext
  intro z
  simp [loopLinear, Module.End.mul_eq_comp, hloop, smul_smul]

/--
@isnad1 id=eq.0h5v.s10.72b50e17effc from=translated src=- shape=fd8f79d2 vocab=debcd68b
-/
theorem loopLinear_left_compat
    (loop : V₁ →ₗ[K] V₁) (r m : K) :
    loopLinear K V₁ loop (r • m) =
      (Algebra.ofId K (Module.End K V₁)) r * loopLinear K V₁ loop m := by
  apply LinearMap.ext
  intro z
  simp [loopLinear, Module.End.mul_eq_comp, smul_smul, mul_comm]

/--
@isnad1 id=eq.0h5v.s10.3c317e46c6ff from=translated src=- shape=65a72922 vocab=2a8e9470
-/
theorem loopLinear_right_compat
    (loop : V₁ →ₗ[K] V₁) (r m : K) :
    loopLinear K V₁ loop (MulOpposite.op r • m) =
      loopLinear K V₁ loop m * (Algebra.ofId K (Module.End K V₁)) r := by
  apply LinearMap.ext
  intro z
  simp [loopLinear, Module.End.mul_eq_comp, smul_smul, mul_comm]

/-- The dual-number action `c + tε ↦ c·id + t·loop`.-/
def loopCornerAction
    (loop : V₁ →ₗ[K] V₁)
    (hloop : ∀ z, loop (loop z) = 0) :
    LoopAlgebra K →ₐ[K] Module.End K V₁ :=
  TrivSqZeroExt.lift
    (Algebra.ofId K (Module.End K V₁))
    (loopLinear K V₁ loop)
    (loopLinear_mul_eq_zero K V₁ loop hloop)
    (loopLinear_left_compat K V₁ loop)
    (loopLinear_right_compat K V₁ loop)

/--
@isnad1 id=eq.1h5v.s9.2b7ffde1f78b from=translated src=- shape=48bb795b vocab=a4b39caf
-/
theorem loopCornerAction_apply
    (loop : V₁ →ₗ[K] V₁)
    (hloop : ∀ z, loop (loop z) = 0)
    (d : LoopAlgebra K) (z : V₁) :
    loopCornerAction K V₁ loop hloop d z =
      d.fst • z + d.snd • loop z := by
  unfold loopCornerAction
  rw [TrivSqZeroExt.lift_def]
  rfl

/-- The diagonal corner acts on the two vertex spaces.-/
def baseAction
    (loop : V₁ →ₗ[K] V₁)
    (hloop : ∀ z, loop (loop z) = 0) :
    BaseAlgebra K →ₐ[K] Module.End K (V₁ × V₂) where
  toFun r :=
    { toFun := fun z =>
        (loopCornerAction K V₁ loop hloop r.1 z.1, r.2 • z.2)
      map_add' := by
        intro z w
        apply Prod.ext
        · simp
        · simp
      map_smul' := by intro c z; ext <;> simp [smul_smul, mul_comm] }
  map_one' := by
    apply LinearMap.ext
    intro z
    ext <;> simp
  map_mul' := by
    intro r s
    apply LinearMap.ext
    intro z
    ext <;> simp [Module.End.mul_eq_comp, smul_smul]
  map_zero' := by
    apply LinearMap.ext
    intro z
    ext <;> simp
  map_add' := by
    intro r s
    apply LinearMap.ext
    intro z
    ext <;> simp [add_smul]
  commutes' := by
    intro c
    apply LinearMap.ext
    intro z
    ext <;> simp

/-- The arrow corner acts by `a·stem + (a*x)·(stem ∘ loop)`.-/
def arrowAction
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂) :
    ArrowCorner K →ₗ[K] Module.End K (V₁ × V₂) where
  toFun m :=
    { toFun := fun z =>
        (0, m.fst • stem z.1 + m.snd • stem (loop z.1))
      map_add' := by
        intro z w
        apply Prod.ext
        · simp
        · simp
          module
      map_smul' := by intro c z; ext <;> simp [smul_smul, mul_comm] }
  map_add' := by
    intro m n
    apply LinearMap.ext
    intro z
    ext <;> simp [add_smul, add_add_add_comm]
  map_smul' := by
    intro c m
    apply LinearMap.ext
    intro z
    ext <;> simp [smul_add, smul_smul]

/--
@isnad1 id=eq.0h7v.s10.8de5c0a78ea8 from=translated src=- shape=08460602 vocab=42cf9e04
-/
theorem arrowAction_mul_eq_zero
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (m n : ArrowCorner K) :
    arrowAction K V₁ V₂ loop stem m *
      arrowAction K V₁ V₂ loop stem n = 0 := by
  apply LinearMap.ext
  intro z
  ext <;> simp [arrowAction, Module.End.mul_eq_comp]

/--
@isnad1 id=eq.1h7v.s11.64e94c43ae2b from=translated src=- shape=3f327b66 vocab=d9f82c91
-/
theorem arrowAction_left_compat
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (r : BaseAlgebra K) (m : ArrowCorner K) :
    arrowAction K V₁ V₂ loop stem (r • m) =
      baseAction K V₁ V₂ loop hloop r * arrowAction K V₁ V₂ loop stem m := by
  apply LinearMap.ext
  intro z
  ext <;> simp [arrowAction, baseAction, Module.End.mul_eq_comp,
    smul_add, smul_smul]

/--
@isnad1 id=eq.1h7v.s11.4506ceb41af5 from=translated src=- shape=555cf3b9 vocab=4f6fcf91
-/
theorem arrowAction_right_compat
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (r : BaseAlgebra K) (m : ArrowCorner K) :
    arrowAction K V₁ V₂ loop stem (MulOpposite.op r • m) =
      arrowAction K V₁ V₂ loop stem m * baseAction K V₁ V₂ loop hloop r := by
  apply LinearMap.ext
  intro z
  ext
  · simp [arrowAction, baseAction, Module.End.mul_eq_comp]
  · simp [arrowAction, baseAction, Module.End.mul_eq_comp,
      loopCornerAction_apply, hloop, smul_add, add_smul, smul_smul]
    module

/-- The live-path algebra action associated to a square-zero loop and an
arbitrary stem map.-/
def b1Action
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0) :
    B1Model K →ₐ[K] Module.End K (V₁ × V₂) :=
  TrivSqZeroExt.lift
    (baseAction K V₁ V₂ loop hloop)
    (arrowAction K V₁ V₂ loop stem)
    (arrowAction_mul_eq_zero K V₁ V₂ loop stem)
    (arrowAction_left_compat K V₁ V₂ loop stem hloop)
    (arrowAction_right_compat K V₁ V₂ loop stem hloop)

/--
@isnad1 id=eq.1h6v.s10.eb41b8bb19bb from=translated src=- shape=0da3df38 vocab=69b5ba46
-/
theorem b1Action_e1
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (z : V₁ × V₂) :
    b1Action K V₁ V₂ loop stem hloop (e1 K) z = (z.1, 0) := by
  unfold b1Action e1
  rw [TrivSqZeroExt.lift_apply_inl]
  simp [baseAction]

/--
@isnad1 id=eq.1h6v.s10.64a6d027915e from=translated src=- shape=8605d260 vocab=7e09e6fa
-/
theorem b1Action_e2
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (z : V₁ × V₂) :
    b1Action K V₁ V₂ loop stem hloop (e2 K) z = (0, z.2) := by
  unfold b1Action e2
  rw [TrivSqZeroExt.lift_apply_inl]
  simp [baseAction]

/--
@isnad1 id=eq.1h6v.s10.54646b8f1214 from=translated src=- shape=cee66448 vocab=18df43ed
-/
theorem b1Action_x
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (z : V₁ × V₂) :
    b1Action K V₁ V₂ loop stem hloop (x K) z = (loop z.1, 0) := by
  unfold b1Action x
  rw [TrivSqZeroExt.lift_apply_inl]
  simp [baseAction, loopCornerAction_apply]

/--
@isnad1 id=eq.1h6v.s10.e3da9d51a45e from=translated src=- shape=1efc32aa vocab=9e030fed
-/
theorem b1Action_a
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (z : V₁ × V₂) :
    b1Action K V₁ V₂ loop stem hloop (a K) z = (0, stem z.1) := by
  unfold b1Action a
  rw [TrivSqZeroExt.lift_apply_inr]
  simp [arrowAction]

/--
@isnad1 id=eq.1h6v.s10.0d88f8287d9f from=translated src=- shape=d0700fe0 vocab=28d86631
-/
theorem b1Action_u
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (z : V₁ × V₂) :
    b1Action K V₁ V₂ loop stem hloop (u K) z =
      (0, stem (loop z.1)) := by
  unfold b1Action u
  rw [TrivSqZeroExt.lift_apply_inr]
  simp [arrowAction]

/-- Finite-dimensional live-path representation data.  Unlike the dead-path
model, there is no relation imposed on `stem ∘ loop`.-/
structure FiniteB1Rep where
  V₁ : FGModuleCat.{u} K
  V₂ : FGModuleCat.{u} K
  loop : V₁ ⟶ V₁
  stem : V₁ ⟶ V₂
  loop_sq : ∀ z, loop.hom.hom (loop.hom.hom z) = 0

namespace FiniteB1Rep

/-- Underlying vector space of a finite live-path representation.-/
def Carrier (D : FiniteB1Rep K) := D.V₁ × D.V₂
  deriving AddCommGroup, Module K

def fst (D : FiniteB1Rep K) (z : D.Carrier) : D.V₁ := z.1

def snd (D : FiniteB1Rep K) (z : D.Carrier) : D.V₂ := z.2

def ofV₁ (D : FiniteB1Rep K) (z : D.V₁) : D.Carrier := (z, 0)

def ofV₂ (D : FiniteB1Rep K) (z : D.V₂) : D.Carrier := (0, z)

/--
@isnad1 id=eq.2h4v.s6.13ea1fc0bd6c from=translated src=- shape=7a64a134 vocab=787a4195
-/
@[ext] theorem carrier_ext (D : FiniteB1Rep K) {z w : D.Carrier}
    (h₁ : fst K D z = fst K D w) (h₂ : snd K D z = snd K D w) : z = w :=
  Prod.ext h₁ h₂

instance (D : FiniteB1Rep K) : Module.Finite K D.Carrier := by
  change Module.Finite K (D.V₁ × D.V₂)
  infer_instance

def actionHom (D : FiniteB1Rep K) :
    B1Model K →ₐ[K] Module.End K D.Carrier :=
  b1Action K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom D.loop_sq

instance (D : FiniteB1Rep K) : Module (B1Model K) D.Carrier :=
  Module.compHom D.Carrier (actionHom K D).toRingHom

instance (D : FiniteB1Rep K) : IsScalarTower K (B1Model K) D.Carrier :=
  IsScalarTower.of_algebraMap_smul fun c z => by
    change actionHom K D (algebraMap K (B1Model K) c) z = c • z
    rw [(actionHom K D).commutes]
    rfl

instance (D : FiniteB1Rep K) : Module.Finite (B1Model K) D.Carrier :=
  Module.Finite.of_restrictScalars_finite K (B1Model K) D.Carrier

/-- The genuine finitely generated left module associated to `D`.-/
abbrev asFGModule (D : FiniteB1Rep K) : FGModuleCat (B1Model K) :=
  FGModuleCat.of (B1Model K) D.Carrier

/--
@isnad1 id=eq.0h3v.s9.ec29d1691526 from=translated src=- shape=52e65dd4 vocab=44bc7c91
-/
@[simp] theorem e1_smul (D : FiniteB1Rep K) (z : D.Carrier) :
    e1 K • z = (z.1, 0) := by
  change actionHom K D (e1 K) z = (z.1, 0)
  exact b1Action_e1 K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom D.loop_sq z

/--
@isnad1 id=eq.0h3v.s9.867f93f734b0 from=translated src=- shape=52f6311a vocab=9443eb9c
-/
@[simp] theorem e2_smul (D : FiniteB1Rep K) (z : D.Carrier) :
    e2 K • z = (0, z.2) := by
  change actionHom K D (e2 K) z = (0, z.2)
  exact b1Action_e2 K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom D.loop_sq z

/--
@isnad1 id=eq.0h3v.s10.b832dc25cd2e from=translated src=- shape=c5255f7f vocab=29335d8c
-/
@[simp] theorem x_smul (D : FiniteB1Rep K) (z : D.Carrier) :
    x K • z = (D.loop.hom.hom z.1, 0) := by
  change actionHom K D (x K) z = (D.loop.hom.hom z.1, 0)
  exact b1Action_x K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom D.loop_sq z

/--
@isnad1 id=eq.0h3v.s10.cd22653d0280 from=translated src=- shape=3fe29ec3 vocab=e51a2024
-/
@[simp] theorem a_smul (D : FiniteB1Rep K) (z : D.Carrier) :
    a K • z = (0, D.stem.hom.hom z.1) := by
  change actionHom K D (a K) z = (0, D.stem.hom.hom z.1)
  exact b1Action_a K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom D.loop_sq z

/--
@isnad1 id=eq.0h3v.s11.98db8df36491 from=translated src=- shape=33457004 vocab=ae4c859e
-/
@[simp] theorem u_smul (D : FiniteB1Rep K) (z : D.Carrier) :
    u K • z = (0, D.stem.hom.hom (D.loop.hom.hom z.1)) := by
  change actionHom K D (u K) z =
    (0, D.stem.hom.hom (D.loop.hom.hom z.1))
  exact b1Action_u K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom D.loop_sq z

end FiniteB1Rep

abbrev K0 : FGModuleCat.{u} K := FGModuleCat.of K (Fin 0 → K)
abbrev K1 : FGModuleCat.{u} K := FGModuleCat.of K K
abbrev K2 : FGModuleCat.{u} K := FGModuleCat.of K (K × K)

/-- Standard nilpotent Jordan loop `(r,s) ↦ (0,r)`.-/
def jordan : K2 K ⟶ K2 K :=
  FGModuleCat.ofHom
    { toFun := fun z => (0, z.1)
      map_add' := by simp
      map_smul' := by simp }

def firstStem : K2 K ⟶ K1 K :=
  FGModuleCat.ofHom (LinearMap.fst K K K)

def secondStem : K2 K ⟶ K1 K :=
  FGModuleCat.ofHom (LinearMap.snd K K K)

abbrev S1Data : FiniteB1Rep K where
  V₁ := K1 K
  V₂ := K0 K
  loop := 0
  stem := 0
  loop_sq := by simp

abbrev S2Data : FiniteB1Rep K where
  V₁ := K0 K
  V₂ := K1 K
  loop := 0
  stem := 0
  loop_sq := by simp

abbrev XData : FiniteB1Rep K where
  V₁ := K2 K
  V₂ := K0 K
  loop := jordan K
  stem := 0
  loop_sq := by intro z; rfl

abbrev AData : FiniteB1Rep K where
  V₁ := K1 K
  V₂ := K1 K
  loop := 0
  stem := 𝟙 _
  loop_sq := by simp

/-- Coordinate model for the string `U = x a`: the stem is live on the
image of the loop.-/
abbrev UData : FiniteB1Rep K where
  V₁ := K2 K
  V₂ := K1 K
  loop := jordan K
  stem := secondStem K
  loop_sq := by intro z; rfl

/-- Coordinate model for the string `W = x⁻¹ a`: after orienting the Jordan
basis uniformly, the stem is the first-coordinate projection.-/
abbrev WData : FiniteB1Rep K where
  V₁ := K2 K
  V₂ := K1 K
  loop := jordan K
  stem := firstStem K
  loop_sq := by intro z; rfl

/-- Coordinate model for `P = a⁻¹ x a`; both occurrences of the arrow give
the identity map between two-dimensional vertex spaces.-/
abbrev PData : FiniteB1Rep K where
  V₁ := K2 K
  V₂ := K2 K
  loop := jordan K
  stem := 𝟙 _
  loop_sq := by intro z; rfl

/-- The seven named genuine finitely generated modules.-/
abbrev S1Module : FGModuleCat (B1Model K) := FiniteB1Rep.asFGModule K (S1Data K)
abbrev S2Module : FGModuleCat (B1Model K) := FiniteB1Rep.asFGModule K (S2Data K)
abbrev XModule : FGModuleCat (B1Model K) := FiniteB1Rep.asFGModule K (XData K)
abbrev AModule : FGModuleCat (B1Model K) := FiniteB1Rep.asFGModule K (AData K)
abbrev UModule : FGModuleCat (B1Model K) := FiniteB1Rep.asFGModule K (UData K)
abbrev WModule : FGModuleCat (B1Model K) := FiniteB1Rep.asFGModule K (WData K)
abbrev PModule : FGModuleCat (B1Model K) := FiniteB1Rep.asFGModule K (PData K)

inductive NamedLabel where
  | s1
  | s2
  | x
  | a
  | u
  | w
  | p
  deriving DecidableEq

def namedModule : NamedLabel → FGModuleCat (B1Model K)
  | .s1 => S1Module K
  | .s2 => S2Module K
  | .x => XModule K
  | .a => AModule K
  | .u => UModule K
  | .w => WModule K
  | .p => PModule K

/-- The live path coordinate acts nontrivially on `U`.
@isnad1 id=eq.0h1v.s9.eb549515c103 from=translated src=- shape=0a6d1a5a vocab=d8cc570c
-/
theorem U_u_smul_top :
    u K • FiniteB1Rep.ofV₁ K (UData K) (1, 0) =
      FiniteB1Rep.ofV₂ K (UData K) 1 := by
  rw [FiniteB1Rep.u_smul]
  rfl

/--
@isnad1 id=ne.0h1v.s9.cb3cc89cafa2 from=translated src=- shape=5413a100 vocab=a24d3700
-/
theorem U_u_smul_top_ne_zero :
    u K • FiniteB1Rep.ofV₁ K (UData K) (1, 0) ≠ 0 := by
  rw [U_u_smul_top]
  intro h
  have hcoord := congrArg (fun z : UModule K => z.2) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

/-- The same coordinate vanishes on `W`, distinguishing the two strings.
@isnad1 id=eq.0h2v.s11.74f97f079e83 from=translated src=- shape=89cd3760 vocab=f0bccce4
-/
theorem W_u_smul_eq_zero (z : WModule K) : u K • z = 0 := by
  rw [FiniteB1Rep.u_smul]
  rfl

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer
