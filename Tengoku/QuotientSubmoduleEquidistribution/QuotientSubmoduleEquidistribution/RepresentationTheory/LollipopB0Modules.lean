import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0AlgebraModel
import Tengoku.Seed.Algebra.Category.FGModuleCat.Basic
import Tengoku.Seed.LinearAlgebra.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genuine finitely generated modules for the dead-path lollipop

This file turns a finite pair of vector spaces with maps
`L : V₁ → V₁`, `T : V₁ → V₂` satisfying `L² = 0` and `T L = 0`
into a left module over the tracked square-zero algebra `B0Model K`.
-/

noncomputable section

open CategoryTheory
open scoped RightActions

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer

universe u

variable (K : Type u) [Field K]

variable (V₁ V₂ : Type u)
variable [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V₂] [Module K V₂]

/-- The two vertex coordinates act diagonally on `V₁ × V₂`.-/
def vertexAction : VertexAlgebra K →ₐ[K] Module.End K (V₁ × V₂) where
  toFun r :=
    { toFun := fun v => (r.1 • v.1, r.2 • v.2)
      map_add' := by
        intro v w
        ext <;> simp
      map_smul' := by
        intro c v
        ext <;> simp [smul_smul, mul_comm] }
  map_one' := by
    apply LinearMap.ext
    intro v
    ext <;> simp
  map_mul' := by
    intro r s
    apply LinearMap.ext
    intro v
    ext <;> simp [smul_smul]
  map_zero' := by
    apply LinearMap.ext
    intro v
    ext <;> simp
  map_add' := by
    intro r s
    apply LinearMap.ext
    intro v
    ext <;> simp [add_smul]
  commutes' := by
    intro c
    apply LinearMap.ext
    intro v
    ext <;> simp

/-- The radical coordinates act through the loop and stem maps.-/
def radicalAction (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂) :
    B0Radical K →ₗ[K] Module.End K (V₁ × V₂) where
  toFun m :=
    { toFun := fun v => (m.x • loop v.1, m.a • stem v.1)
      map_add' := by
        intro v w
        ext <;> simp
      map_smul' := by
        intro c v
        ext <;> simp [smul_smul, mul_comm] }
  map_add' := by
    intro m n
    apply LinearMap.ext
    intro v
    ext <;> simp [add_smul]
  map_smul' := by
    intro c m
    apply LinearMap.ext
    intro v
    ext <;> simp [smul_smul]

/--
@isnad1 id=eq.2h7v.s11.c453fc2d7f47 from=translated src=- shape=0a420310 vocab=97f011c5
-/
theorem radicalAction_mul_eq_zero
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (m n : B0Radical K) :
    radicalAction K V₁ V₂ loop stem m * radicalAction K V₁ V₂ loop stem n = 0 := by
  apply LinearMap.ext
  intro v
  ext
  · simp [radicalAction, hloop, smul_smul]
  · simp [radicalAction, hstem, smul_smul]

/--
@isnad1 id=eq.0h7v.s11.15a5dc3cdba8 from=translated src=- shape=cb4c8f0a vocab=551bee13
-/
theorem radicalAction_left_compat
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (r : VertexAlgebra K) (m : B0Radical K) :
    radicalAction K V₁ V₂ loop stem (r • m) =
      vertexAction K V₁ V₂ r * radicalAction K V₁ V₂ loop stem m := by
  apply LinearMap.ext
  intro v
  ext <;> simp [radicalAction, vertexAction, smul_smul]

/--
@isnad1 id=eq.0h7v.s11.34baab9f5c2f from=translated src=- shape=bf5b1d68 vocab=ce87f3e1
-/
theorem radicalAction_right_compat
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (r : VertexAlgebra K) (m : B0Radical K) :
    radicalAction K V₁ V₂ loop stem (MulOpposite.op r • m) =
      radicalAction K V₁ V₂ loop stem m * vertexAction K V₁ V₂ r := by
  apply LinearMap.ext
  intro v
  ext <;> simp [radicalAction, vertexAction, smul_smul, mul_comm]

/-- The algebra action attached to a pair `(loop, stem)` satisfying the dead-path relations.-/
def b0Action
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0) :
    B0Model K →ₐ[K] Module.End K (V₁ × V₂) :=
  TrivSqZeroExt.lift
    (vertexAction K V₁ V₂)
    (radicalAction K V₁ V₂ loop stem)
    (radicalAction_mul_eq_zero K V₁ V₂ loop stem hloop hstem)
    (radicalAction_left_compat K V₁ V₂ loop stem)
    (radicalAction_right_compat K V₁ V₂ loop stem)

/--
@isnad1 id=eq.2h6v.s10.a832372a5993 from=translated src=- shape=f76af618 vocab=2ee49321
-/
theorem b0Action_e1
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (v : V₁ × V₂) :
    b0Action K V₁ V₂ loop stem hloop hstem (e1 K) v = (v.1, 0) := by
  unfold b0Action e1
  rw [TrivSqZeroExt.lift_apply_inl]
  simp [vertexAction]

/--
@isnad1 id=eq.2h6v.s10.269db7b9cdf8 from=translated src=- shape=e7343217 vocab=89d8b94b
-/
theorem b0Action_e2
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (v : V₁ × V₂) :
    b0Action K V₁ V₂ loop stem hloop hstem (e2 K) v = (0, v.2) := by
  unfold b0Action e2
  rw [TrivSqZeroExt.lift_apply_inl]
  simp [vertexAction]

/--
@isnad1 id=eq.2h6v.s10.5bb6fad343a2 from=translated src=- shape=4972397a vocab=891272a2
-/
theorem b0Action_a
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (v : V₁ × V₂) :
    b0Action K V₁ V₂ loop stem hloop hstem (a K) v = (0, stem v.1) := by
  unfold b0Action a
  rw [TrivSqZeroExt.lift_apply_inr]
  simp [radicalAction]

/--
@isnad1 id=eq.2h6v.s10.0f3311002f12 from=translated src=- shape=67b11c9e vocab=652d58c2
-/
theorem b0Action_x
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (v : V₁ × V₂) :
    b0Action K V₁ V₂ loop stem hloop hstem (x K) v = (loop v.1, 0) := by
  unfold b0Action x
  rw [TrivSqZeroExt.lift_apply_inr]
  simp [radicalAction]

/-- Finite-dimensional linear data satisfying the two dead-path relations.-/
structure FiniteB0Rep where
  V₁ : FGModuleCat.{u} K
  V₂ : FGModuleCat.{u} K
  loop : V₁ ⟶ V₁
  stem : V₁ ⟶ V₂
  loop_sq : ∀ v, loop.hom.hom (loop.hom.hom v) = 0
  stem_loop : ∀ v, stem.hom.hom (loop.hom.hom v) = 0

namespace FiniteB0Rep

/-- The underlying vector space of a finite `B₀` representation.-/
def Carrier (D : FiniteB0Rep K) := D.V₁ × D.V₂
  deriving AddCommGroup, Module K

def fst (D : FiniteB0Rep K) (v : D.Carrier) : D.V₁ := v.1

def snd (D : FiniteB0Rep K) (v : D.Carrier) : D.V₂ := v.2

def ofV₁ (D : FiniteB0Rep K) (v : D.V₁) : D.Carrier := (v, 0)

def ofV₂ (D : FiniteB0Rep K) (v : D.V₂) : D.Carrier := (0, v)

/--
@isnad1 id=eq.0h3v.s5.66f99eef7954 from=translated src=- shape=1b4a2e8c vocab=2868d0c5
-/
@[simp] theorem fst_ofV₁ (D : FiniteB0Rep K) (v : D.V₁) :
    fst K D (ofV₁ K D v) = v := rfl

/--
@isnad1 id=eq.0h3v.s7.7156a5ae05fd from=translated src=- shape=63cca9f0 vocab=b5108257
-/
@[simp] theorem snd_ofV₁ (D : FiniteB0Rep K) (v : D.V₁) :
    snd K D (ofV₁ K D v) = 0 := rfl

/--
@isnad1 id=eq.0h3v.s7.92a092ae732f from=translated src=- shape=63cca9f0 vocab=0234272d
-/
@[simp] theorem fst_ofV₂ (D : FiniteB0Rep K) (v : D.V₂) :
    fst K D (ofV₂ K D v) = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.bb136bd865e6 from=translated src=- shape=1b4a2e8c vocab=aaac0361
-/
@[simp] theorem snd_ofV₂ (D : FiniteB0Rep K) (v : D.V₂) :
    snd K D (ofV₂ K D v) = v := rfl

/--
@isnad1 id=eq.2h4v.s6.5457081e3bce from=translated src=- shape=7a64a134 vocab=39e74586
-/
@[ext] theorem carrier_ext (D : FiniteB0Rep K) {v w : D.Carrier}
    (h₁ : fst K D v = fst K D w) (h₂ : snd K D v = snd K D w) : v = w := by
  exact Prod.ext h₁ h₂

/--
@isnad1 id=eq.0h3v.s6.1d96f9d60583 from=translated src=- shape=368fda91 vocab=f297c58d
-/
theorem decompose (D : FiniteB0Rep K) (v : D.Carrier) :
    v = ofV₁ K D (fst K D v) + ofV₂ K D (snd K D v) := by
  apply carrier_ext K D
  · change v.1 = v.1 + 0
    simp
  · change v.2 = 0 + v.2
    simp

instance (D : FiniteB0Rep K) : Module.Finite K D.Carrier := by
  change Module.Finite K (D.V₁ × D.V₂)
  infer_instance

/-- The algebra representation associated to finite lollipop data.-/
def actionHom (D : FiniteB0Rep K) : B0Model K →ₐ[K] Module.End K D.Carrier :=
  b0Action K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom D.loop_sq D.stem_loop

instance (D : FiniteB0Rep K) : Module (B0Model K) D.Carrier :=
  Module.compHom D.Carrier (actionHom K D).toRingHom

instance (D : FiniteB0Rep K) : IsScalarTower K (B0Model K) D.Carrier :=
  IsScalarTower.of_algebraMap_smul fun c v => by
    change actionHom K D (algebraMap K (B0Model K) c) v = c • v
    rw [(actionHom K D).commutes]
    rfl

instance (D : FiniteB0Rep K) : Module.Finite (B0Model K) D.Carrier :=
  Module.Finite.of_restrictScalars_finite K (B0Model K) D.Carrier

/-- The genuine finitely generated left module associated to `D`.-/
abbrev asFGModule (D : FiniteB0Rep K) : FGModuleCat (B0Model K) :=
  FGModuleCat.of (B0Model K) D.Carrier

/--
@isnad1 id=eq.0h3v.s8.958fbba04373 from=translated src=- shape=52e65dd4 vocab=f6ff888e
-/
@[simp] theorem e1_smul (D : FiniteB0Rep K) (v : D.Carrier) :
    e1 K • v = (v.1, 0) := by
  change actionHom K D (e1 K) v = (v.1, 0)
  exact b0Action_e1 K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq D.stem_loop v

/--
@isnad1 id=eq.0h3v.s8.88d427293f3a from=translated src=- shape=52f6311a vocab=e6af220b
-/
@[simp] theorem e2_smul (D : FiniteB0Rep K) (v : D.Carrier) :
    e2 K • v = (0, v.2) := by
  change actionHom K D (e2 K) v = (0, v.2)
  exact b0Action_e2 K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq D.stem_loop v

/--
@isnad1 id=eq.0h3v.s10.06c65261fcf6 from=translated src=- shape=3fe29ec3 vocab=c01a6ae1
-/
@[simp] theorem a_smul (D : FiniteB0Rep K) (v : D.Carrier) :
    a K • v = (0, D.stem.hom.hom v.1) := by
  change actionHom K D (a K) v = (0, D.stem.hom.hom v.1)
  exact b0Action_a K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq D.stem_loop v

/--
@isnad1 id=eq.0h3v.s10.b256d779b0a3 from=translated src=- shape=c5255f7f vocab=29856698
-/
@[simp] theorem x_smul (D : FiniteB0Rep K) (v : D.Carrier) :
    x K • v = (D.loop.hom.hom v.1, 0) := by
  change actionHom K D (x K) v = (D.loop.hom.hom v.1, 0)
  exact b0Action_x K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq D.stem_loop v

/--
@isnad1 id=eq.0h3v.s8.66b06a4df087 from=translated src=- shape=60a33b01 vocab=7b8c5ce7
-/
@[simp] theorem e1_smul_ofV₁ (D : FiniteB0Rep K) (v : D.V₁) :
    e1 K • ofV₁ K D v = ofV₁ K D v := by
  rw [e1_smul]
  apply carrier_ext K D <;> rfl

/--
@isnad1 id=eq.0h3v.s10.f3399e8e1a4c from=translated src=- shape=f6c91683 vocab=d704eb27
-/
@[simp] theorem a_smul_ofV₁ (D : FiniteB0Rep K) (v : D.V₁) :
    a K • ofV₁ K D v = ofV₂ K D (D.stem.hom.hom v) := by
  rw [a_smul]
  apply carrier_ext K D <;> rfl

end FiniteB0Rep

abbrev K0 : FGModuleCat.{u} K := FGModuleCat.of K (Fin 0 → K)
abbrev K1 : FGModuleCat.{u} K := FGModuleCat.of K K
abbrev K2 : FGModuleCat.{u} K := FGModuleCat.of K (K × K)

/-- The nilpotent Jordan map `(u,v) ↦ (0,u)`.-/
def jordan : K2 K ⟶ K2 K :=
  FGModuleCat.ofHom
    { toFun := fun p => (0, p.1)
      map_add' := by simp
      map_smul' := by simp }

/-- The projective stem map `(u,v) ↦ u`.-/
def forkStem : K2 K ⟶ K1 K :=
  FGModuleCat.ofHom (LinearMap.fst K K K)

abbrev S1Data : FiniteB0Rep K where
  V₁ := K1 K
  V₂ := K0 K
  loop := 0
  stem := 0
  loop_sq := by simp
  stem_loop := by simp

abbrev S2Data : FiniteB0Rep K where
  V₁ := K0 K
  V₂ := K1 K
  loop := 0
  stem := 0
  loop_sq := by simp
  stem_loop := by simp

abbrev XData : FiniteB0Rep K where
  V₁ := K2 K
  V₂ := K0 K
  loop := jordan K
  stem := 0
  loop_sq := by
    intro v
    rfl
  stem_loop := by simp

abbrev AData : FiniteB0Rep K where
  V₁ := K1 K
  V₂ := K1 K
  loop := 0
  stem := 𝟙 _
  loop_sq := by simp
  stem_loop := by simp

abbrev PData : FiniteB0Rep K where
  V₁ := K2 K
  V₂ := K1 K
  loop := jordan K
  stem := forkStem K
  loop_sq := by
    intro v
    rfl
  stem_loop := by
    intro v
    rfl

/-- The five named genuine finitely generated `B₀`-modules.-/
abbrev S1Module : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (S1Data K)
abbrev S2Module : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (S2Data K)
abbrev XModule : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (XData K)
abbrev AModule : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (AData K)
abbrev PModule : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (PData K)

/--
@isnad1 id=eq.0h2v.s8.b08b8ab05412 from=translated src=- shape=1a6655cd vocab=2797f6df
-/
@[simp] theorem S2Data_e1_smul
    (w : FiniteB0Rep.Carrier K (S2Data K)) : e1 K • w = 0 := by
  rw [FiniteB0Rep.e1_smul]
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

/--
@isnad1 id=eq.0h2v.s8.6a7c6dcbe141 from=translated src=- shape=1a6655cd vocab=b6fc8a27
-/
@[simp] theorem S2Data_a_smul
    (w : FiniteB0Rep.Carrier K (S2Data K)) : a K • w = 0 := by
  rw [FiniteB0Rep.a_smul]
  rfl

/-- If the stem map is surjective, every unbundled `B₀`-linear map to `S₂` vanishes.
@isnad1 id=eq.1h3v.s10.960fefad13a2 from=translated src=- shape=bb79de97 vocab=a5a5f496
-/
theorem linearMap_S2_eq_zero_of_surjective_stem
    (D : FiniteB0Rep K)
    (hstem : Function.Surjective D.stem.hom.hom)
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K (S2Data K)) : f = 0 := by
  apply LinearMap.ext
  intro v
  have hv₁ : f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) = 0 := by
    calc
      f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) =
          f (e1 K • FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) := by
        rw [FiniteB0Rep.e1_smul_ofV₁]
      _ = e1 K • f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) := by
        rw [f.map_smul]
      _ = 0 := S2Data_e1_smul K _
  obtain ⟨u, hu⟩ := hstem (FiniteB0Rep.snd K D v)
  have hv₂ : f (FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) = 0 := by
    calc
      f (FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) =
          f (a K • FiniteB0Rep.ofV₁ K D u) := by
        rw [FiniteB0Rep.a_smul_ofV₁, hu]
      _ = a K • f (FiniteB0Rep.ofV₁ K D u) := by rw [f.map_smul]
      _ = 0 := S2Data_a_smul K _
  calc
    f v = f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v) +
        FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) :=
      congrArg f (FiniteB0Rep.decompose K D v)
    _ = f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) +
        f (FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) := by rw [map_add]
    _ = 0 := by rw [hv₁, hv₂, add_zero]

/-- The bundled `FGModuleCat` version of the same zero-Hom criterion.
@isnad1 id=eq.1h3v.s10.406ba6b5aae8 from=translated src=- shape=1e099a88 vocab=05151f20
-/
theorem hom_S2_eq_zero_of_surjective_stem
    (D : FiniteB0Rep K)
    (hstem : Function.Surjective D.stem.hom.hom)
    (f : FiniteB0Rep.asFGModule K D ⟶ S2Module K) : f = 0 := by
  apply FGModuleCat.hom_ext
  exact linearMap_S2_eq_zero_of_surjective_stem K D hstem f.hom.hom

/--
@isnad1 id=surjecti.0h1v.s9.dc78d13ca8d4 from=translated src=- shape=e0fad07d vocab=00c6cede
-/
theorem S1_stem_surjective : Function.Surjective (S1Data K).stem.hom.hom := by
  intro y
  refine ⟨0, ?_⟩
  exact Subsingleton.elim _ _

/--
@isnad1 id=surjecti.0h1v.s9.7d889d09a88d from=translated src=- shape=e0fad07d vocab=ef1ef1d9
-/
theorem X_stem_surjective : Function.Surjective (XData K).stem.hom.hom := by
  intro y
  refine ⟨0, ?_⟩
  exact Subsingleton.elim _ _

/--
@isnad1 id=surjecti.0h1v.s9.3915a56cba9f from=translated src=- shape=e0fad07d vocab=22e8b476
-/
theorem A_stem_surjective : Function.Surjective (AData K).stem.hom.hom := by
  intro y
  exact ⟨y, rfl⟩

/--
@isnad1 id=surjecti.0h1v.s9.d8c65aca947f from=translated src=- shape=e0fad07d vocab=c8e300be
-/
theorem P_stem_surjective : Function.Surjective (PData K).stem.hom.hom := by
  intro y
  exact ⟨(y, 0), rfl⟩

/--
@isnad1 id=eq.0h2v.s10.2e370052fbff from=translated src=- shape=8a6e859d vocab=d5ccf841
-/
theorem hom_A_S2_eq_zero (f : AModule K ⟶ S2Module K) : f = 0 :=
  hom_S2_eq_zero_of_surjective_stem K (AData K) (A_stem_surjective K) f

inductive QuotientPRowLabel where
  | s1
  | x
  | a
  | p

def quotientPRowModule : QuotientPRowLabel → FGModuleCat (B0Model K)
  | .s1 => S1Module K
  | .x => XModule K
  | .a => AModule K
  | .p => PModule K

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer
