import Tengoku.TdaLib.TDA.Persistence.SupportInterval
import Tengoku.TdaLib.TDA.Persistence.RankExact
import Tengoku.Seed.LinearAlgebra.Span.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hook morphisms and lifting along rank exact sequences

For grades `i < j` in a partial order, the hook has support `{a | i ≤ a ∧ ¬ j ≤ a}`.
A morphism from this hook to a persistence module is determined by a vector at `i` killed
by the structure map to `j`. For pointwise finite-dimensional middle modules,
rank exactness permits lifting that vector while retaining its vanishing relation,
which constructs a lift of the entire hook morphism.

This proves the lifting property for hooks with a finite death grade, using the kernel
criterion in `RankExact`. Principal upsets are treated in `HookInfinity`; the finite-poset
classification for pointwise finite-dimensional modules is in
`FiniteRankProjectiveClassification`. Exact-category axioms and classification beyond
that finite setting remain separate. Hook supports here may be unbounded. See Botnan,
Oppermann, Oudot and Scoccola, arXiv:2208.00300v3, Section 2.14 and Theorem 2.7.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.Hook

open CategoryTheory

variable {k : Type u} [Field k] {P : Type v} [PartialOrder P]

/-- A hook contains the points above its birth and outside the upset of its death.-/
abbrev support (i j : P) : Set P := {a | i ≤ a ∧ ¬ j ≤ a}

/-- Hook supports are order convex.
@isnad1 id=ordconne.0h3v.s4.ab42bab84b4d from=translated src=- shape=ce8ffaa7 vocab=e65e50e5
-/
theorem support_ordConnected (i j : P) : (support i j).OrdConnected where
  out' := by
    intro a ha c hc b hb
    exact ⟨ha.1.trans hb.1, fun hj => hc.2 (hj.trans hb.2)⟩

/-- The interval module on a hook support.-/
@[reducible]
noncomputable def module (i j : P) : PModule.{u,v,u} k P :=
  SupportInterval.module (support i j) (support_ordConnected i j)

/-- The birth grade belongs to every nonzero hook.
@isnad1 id=mem.1h3v.s4.1b9256cc428c from=translated src=- shape=f6d68567 vocab=13f03f50
-/
theorem birth_mem {i j : P} (hij : i < j) : i ∈ support i j :=
  ⟨le_rfl, not_le_of_gt hij⟩

/-- A hook excludes its death grade.
@isnad1 id=not.0h3v.s4.09489e4a69ed from=translated src=- shape=1fcf41f8 vocab=44217c7e
-/
theorem death_not_mem (i j : P) : j ∉ support i j := fun h => h.2 le_rfl

/-- The value on the unit at birth determines a morphism from a nonzero hook.
@isnad1 id=eq.2h7v.s10.f32859afd32e from=translated src=- shape=0e546aa5 vocab=3c523cba
-/
theorem hom_ext {i j : P} (hij : i < j) {M : PModule.{u,v,u} k P}
    {α β : module (k := k) i j ⟶ M}
    (h : (α.app i).hom (SupportInterval.one (support i j) (birth_mem hij)) =
      (β.app i).hom (SupportInterval.one (support i j) (birth_mem hij))) : α = β := by
  classical
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_cases hp : p ∈ support i j
  · have hg : structureMapLinear (module (k := k) i j) hp.1
        (SupportInterval.one (support i j) (birth_mem hij)) =
          SupportInterval.one (support i j) hp := by
      apply Subtype.ext
      exact (SupportInterval.structureMap_val (support i j) (support_ordConnected i j)
        hp.1 (SupportInterval.one (support i j) (birth_mem hij))).trans (by
          simp [hp, SupportInterval.one])
    have hx : x = (x : k) • structureMapLinear (module i j) hp.1
        (SupportInterval.one (support i j) (birth_mem hij)) := by
      rw [hg]
      apply Subtype.ext
      simp [SupportInterval.one]
    have hα := congrArg (fun f => f.hom
      (SupportInterval.one (support i j) (birth_mem hij)))
        (α.naturality (homOfLE hp.1))
    have hβ := congrArg (fun f => f.hom
      (SupportInterval.one (support i j) (birth_mem hij)))
        (β.naturality (homOfLE hp.1))
    change (α.app p).hom (structureMapLinear (module i j) hp.1 _) =
      structureMapLinear M hp.1 ((α.app i).hom _) at hα
    change (β.app p).hom (structureMapLinear (module i j) hp.1 _) =
      structureMapLinear M hp.1 ((β.app i).hom _) at hβ
    rw [hx, map_smul, map_smul, hα, hβ, h]
  · have hx : x = 0 := Subtype.ext (SupportInterval.val_eq_zero (support i j) hp x)
    simp [hx]

/-- The generating element of a hook morphism dies at the hook's death grade.
@isnad1 id=eq.1h6v.s10.5b1e6f473703 from=translated src=- shape=6ff7cc5c vocab=2dad572d
-/
theorem generator_dies {i j : P} (hij : i < j) {M : PModule.{u,v,u} k P}
    (α : module (k := k) i j ⟶ M) :
    structureMapLinear M hij.le
      ((α.app i).hom (SupportInterval.one (support i j) (birth_mem hij))) = 0 := by
  have hn := congrArg (fun f => f.hom
    (SupportInterval.one (support i j) (birth_mem hij)))
      (α.naturality (homOfLE hij.le))
  have hz : structureMapLinear (module (k := k) i j) hij.le = 0 :=
    (SupportInterval.structureMap_eq_zero_iff (support i j)
      (support_ordConnected i j) hij.le).mpr
      (fun h => death_not_mem i j h.2)
  change (α.app j).hom (structureMapLinear (module i j) hij.le _) = _ at hn
  rw [hz, LinearMap.zero_apply, map_zero] at hn
  exact hn.symm

private noncomputable def generatorLinear {i j : P} (M : PModule.{u,v,u} k P)
    (m : M.obj i) (p : P) : SupportInterval.fiber (k := k) (support i j) p →ₗ[k] M.obj p := by
  classical
  exact if hp : i ≤ p then
    (LinearMap.toSpanSingleton k (M.obj p) (structureMapLinear M hp m)).comp
      (SupportInterval.fiber (k := k) (support i j) p).subtype else 0

/-- A vector killed at the death grade defines a morphism out of the hook.-/
noncomputable def fromGenerator {i j : P} (hij : i < j) (M : PModule.{u,v,u} k P)
    (m : M.obj i) (hm : structureMapLinear M hij.le m = 0) : module i j ⟶ M where
  app p := ModuleCat.ofHom (generatorLinear M m p)
  naturality {p q} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change generatorLinear M m q (structureMapLinear (module i j) (leOfHom f) x) =
      structureMapLinear M (leOfHom f) (generatorLinear M m p x)
    by_cases hp : i ≤ p
    · have hq := hp.trans (leOfHom f)
      simp only [generatorLinear, dite_eq_left hp, dite_eq_left hq, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, map_smul]
      have hcomp : structureMapLinear M (leOfHom f) (structureMapLinear M hp m) =
          structureMapLinear M hq m := by
        exact (congrArg (fun g => g m)
          (structureMapLinear_comp M hp (leOfHom f))).symm
      rw [hcomp]
      change ((structureMapLinear (SupportInterval.module (support i j)
        (support_ordConnected i j)) (leOfHom f) x) : k) • structureMapLinear M hq m =
          (x : k) • structureMapLinear M hq m
      rw [SupportInterval.structureMap_val]
      by_cases hqs : q ∈ support i j
      · simp [hqs]
      · have hjq : j ≤ q := by
          by_contra hjq
          exact hqs ⟨hq, hjq⟩
        have hz : structureMapLinear M hq m = 0 := by
          rw [structureMapLinear_comp M hij.le hjq]
          simp [hm]
        simp [hqs, hz]
    · have hps : p ∉ support i j := fun h => hp h.1
      have hx : x = 0 := Subtype.ext (SupportInterval.val_eq_zero (support i j) hps x)
      simp [hx]

/-- The component of a generated morphism transports and scales its birth vector.
@isnad1 id=eq.3h8v.s11.7ea023eec8e2 from=translated src=- shape=606e2bee vocab=a8c0fca3
-/
theorem fromGenerator_app {i j p : P} (hij : i < j) (M : PModule.{u,v,u} k P)
    (m : M.obj i) (hm : structureMapLinear M hij.le m = 0) (hip : i ≤ p)
    (x : SupportInterval.fiber (k := k) (support i j) p) :
    ((fromGenerator hij M m hm).app p).hom x = (x : k) • structureMapLinear M hip m := by
  classical
  change generatorLinear M m p x = _
  simp [generatorLinear, hip, LinearMap.toSpanSingleton_apply]

/-- The morphism built from a generator takes the unit at birth to that generator.
@isnad1 id=eq.2h6v.s10.78dd2eaab7c3 from=translated src=- shape=3ea5b707 vocab=c4869dff
-/
theorem fromGenerator_birth {i j : P} (hij : i < j) (M : PModule.{u,v,u} k P)
    (m : M.obj i) (hm : structureMapLinear M hij.le m = 0) :
    ((fromGenerator hij M m hm).app i).hom
      (SupportInterval.one (support i j) (birth_mem hij)) = m := by
  classical
  change generatorLinear M m i (SupportInterval.one (support i j) (birth_mem hij)) = m
  simp only [generatorLinear, dite_eq_left (le_refl i), LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]
  change (1 : k) • structureMapLinear M (le_refl i) m = m
  simp

/-- Morphisms from a nonzero hook correspond to vectors killed between its endpoints.-/
noncomputable def homEquivKernel {i j : P} (hij : i < j) (M : PModule.{u,v,u} k P) :
    (module (k := k) i j ⟶ M) ≃ LinearMap.ker (structureMapLinear M hij.le) where
  toFun α := ⟨(α.app i).hom (SupportInterval.one (support i j) (birth_mem hij)),
    generator_dies hij α⟩
  invFun x := fromGenerator hij M x.val x.property
  left_inv _α := hom_ext hij (fromGenerator_birth hij M _ _)
  right_inv _x := Subtype.ext (fromGenerator_birth hij M _ _)

/-- Hooks lift against rank exact quotient maps. The lift is obtained by lifting its
birth generator while preserving the death relation.
@isnad1 id=ex.2h10v.s9.ee2ea0dc8dfe from=translated src=- shape=4059ab0b vocab=8023a497
-/
theorem exists_lift {i j : P} (hij : i < j)
    {L M N : PModule.{u,v,u} k P} {ι : L ⟶ M} {π : M ⟶ N}
    (hs : IsRankExact ι π)
    (α : module (k := k) i j ⟶ N) :
    ∃ β : module (k := k) i j ⟶ M, β ≫ π = α := by
  obtain ⟨m, hm, hdie⟩ := hs.lift_kernel hij.le
    ((α.app i).hom (SupportInterval.one (support i j) (birth_mem hij)))
    (generator_dies hij α)
  refine ⟨fromGenerator hij M m hdie, ?_⟩
  apply hom_ext hij
  change (π.app i).hom (((fromGenerator hij M m hdie).app i).hom _) = _
  rw [fromGenerator_birth]
  exact hm

end TDA.Persistence.Hook
