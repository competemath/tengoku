/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.Lie.UniversalEnveloping.LeftRegular
import Tengoku.LieLean.LieLean.Algebra.Lie.Quotient
import Tengoku.Seed.Algebra.Lie.TensorProduct
import Tengoku.Seed.LinearAlgebra.TensorAlgebra.Basic
import Tengoku.Seed.RingTheory.TwoSidedIdeal.Operations
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Natural transformations between tensoring functors

Let `I` be a two-sided ideal of `U = U(L)` and `A = U / I`. On the modules killed by `I`
consider the functors `F_V : M ↦ M ⊗ V` and `F_W : M ↦ M ⊗ W` for `L`-modules `V`, `W`.
Natural transformations `F_V → F_W` correspond to morphisms of `L`-modules
`V → A^{ad} ⊗ W`, where `A^{ad}` is `A` with the adjoint action `x · a = x a - a x`:

* a morphism `g : V → A^{ad} ⊗ W` gives `φ_M (m ⊗ v) = Σ aᵢ m ⊗ wᵢ` for `g v = Σ aᵢ ⊗ wᵢ`
  (`tensorNatMap`), natural in `M` (`tensorNatMap_naturality`);
* conversely `φ` is recovered from `g v = φ_A (1 ⊗ v)` (`evalNat`), using naturality of `φ`
  along the maps `A → A`, `a ↦ a u` (`evalNat`, requires them) and `A → M`, `a ↦ a m`
  (`tensorNatMap_evalNat`); and `evalNat (tensorNatMap g) = g` (`evalNat_tensorNatMap`).

This is the bimodule description of natural transformations between projective functors used
by Bernstein–Gelfand, and in the proof of Theorem 10.7 in Humphreys, *Representations of
semisimple Lie algebras in the BGG category `𝒪`*, GSM 94.

## Main definitions

* `UniversalEnvelopingAlgebra.AdRegular`: `U(L)` with the adjoint action.
* `UniversalEnvelopingAlgebra.IsKilledBy`: `I` acts by zero on `M`.
* `UniversalEnvelopingAlgebra.LeftQuotient`, `UniversalEnvelopingAlgebra.AdQuotient`: `U / I`
  with the left-multiplication action, resp. the adjoint action.
* `UniversalEnvelopingAlgebra.tensorNatMap`: `φ_M : M ⊗ V → M ⊗ W` for `g : V → A^{ad} ⊗ W`.
* `UniversalEnvelopingAlgebra.evalNat`: `g v = φ_A (1 ⊗ v)`.
-/

noncomputable section

open TensorProduct LieModule

namespace UniversalEnvelopingAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "𝓤" => UniversalEnvelopingAlgebra R L

/-! ### The adjoint module -/

/-- The enveloping algebra regarded as a Lie module by the adjoint action
`x · u = ι(x) u - u ι(x)`.-/
def AdRegular := UniversalEnvelopingAlgebra R L

namespace AdRegular

attribute [local instance] LieRing.ofAssociativeRing

instance : AddCommGroup (AdRegular R L) := inferInstanceAs (AddCommGroup 𝓤)

instance : Module R (AdRegular R L) := inferInstanceAs (Module R 𝓤)

instance : LieRingModule 𝓤 (AdRegular R L) := inferInstanceAs (LieRingModule 𝓤 𝓤)

instance : LieModule R 𝓤 (AdRegular R L) := inferInstanceAs (LieModule R 𝓤 𝓤)

instance : LieRingModule L (AdRegular R L) := LieRingModule.compLieHom _ (ι R)

instance : LieModule R L (AdRegular R L) := LieModule.compLieHom _ (ι R)

/-- The underlying linear identification forgets only the type tag.-/
def equiv : AdRegular R L ≃ₗ[R] 𝓤 := LinearEquiv.refl R _

/--
@isnad1 id=eq.0h4v.s10.81dd16df7dea from=translated src=- shape=911f7262 vocab=e56a1325
-/
@[simp] theorem equiv_lie (x : L) (u : AdRegular R L) :
    equiv R L ⁅x, u⁆ = ι R x * equiv R L u - equiv R L u * ι R x := rfl

end AdRegular

/-! ### Modules killed by an ideal -/

variable {R L} (I : TwoSidedIdeal (UniversalEnvelopingAlgebra R L))

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The action of `U(L)` on an `L`-module.-/
abbrev actionHom : 𝓤 →ₐ[R] Module.End R M := lift R (toEnd R L M)

/--
@isnad1 id=eq.0h4v.s9.25ed7c4d1eb8 from=translated src=- shape=2b3311b6 vocab=a5e2d069
-/
theorem actionHom_ι (x : L) : actionHom (R := R) (L := L) M (ι R x) = toEnd R L M x :=
  lift_ι_apply R _ x

/-- `I` acts by zero on `M`.-/
def IsKilledBy : Prop := ∀ a ∈ I, actionHom (R := R) (L := L) M a = 0

variable {M} {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- Morphisms of `L`-modules commute with the action of `U(L)`.
@isnad1 id=eq.0h7v.s9.ef938c5c2fc8 from=translated src=- shape=d06792fb vocab=dd9bfd0e
-/
theorem _root_.LieModuleHom.map_actionHom (f : M →ₗ⁅R,L⁆ N) (u : 𝓤) (m : M) :
    f (actionHom M u m) = actionHom N u (f m) := by
  obtain ⟨t, rfl⟩ : ∃ t, mkAlgHom R L t = u := by
    induction u using Quotient.inductionOn' with
    | h a => exact ⟨a, rfl⟩
  induction t using TensorAlgebra.induction generalizing m with
  | algebraMap r => simp
  | ι x => simp
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      map_add, ha, hb]

variable (R L)

/-- `I` as a Lie submodule of the left-regular module.-/
def leftIdeal : LieSubmodule R L (LeftRegular R L) where
  carrier := {u | LeftRegular.equiv R L u ∈ I}
  add_mem' ha hb := I.add_mem ha hb
  zero_mem' := I.zero_mem
  smul_mem' c u hu := by
    change LeftRegular.equiv R L (c • u) ∈ I
    rw [map_smul, Algebra.smul_def]
    exact I.mul_mem_left _ _ hu
  lie_mem {x u} hu := I.mul_mem_left (ι R x) _ hu

/-- `I` as a Lie submodule of the adjoint module.-/
def adIdeal : LieSubmodule R L (AdRegular R L) where
  carrier := {u | AdRegular.equiv R L u ∈ I}
  add_mem' ha hb := I.add_mem ha hb
  zero_mem' := I.zero_mem
  smul_mem' c u hu := by
    change AdRegular.equiv R L (c • u) ∈ I
    rw [map_smul, Algebra.smul_def]
    exact I.mul_mem_left _ _ hu
  lie_mem {x u} hu := I.sub_mem (I.mul_mem_left (ι R x) _ hu) (I.mul_mem_right _ (ι R x) hu)

/-- `U / I` with the left-multiplication action.-/
abbrev LeftQuotient := LeftRegular R L ⧸ leftIdeal R L I

/-- `U / I` with the adjoint action.-/
abbrev AdQuotient := AdRegular R L ⧸ adIdeal R L I

/-- The two quotients have the same underlying module.-/
def quotientEquiv : AdQuotient R L I ≃ₗ[R] LeftQuotient R L I :=
  Submodule.Quotient.equiv _ _ ((AdRegular.equiv R L).trans (LeftRegular.equiv R L).symm)
    (Submodule.ext fun u ↦ by
      constructor
      · rintro ⟨v, hv, rfl⟩; exact hv
      · intro hu; exact ⟨u, hu, rfl⟩)

/--
@isnad1 id=eq.0h4v.s10.af805c4d33ac from=translated src=- shape=ca9e227f vocab=611fe9b2
-/
@[simp] theorem quotientEquiv_mk (u : AdRegular R L) :
    quotientEquiv R L I (LieSubmodule.Quotient.mk u) =
      LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm (AdRegular.equiv R L u)) := rfl

/-! ### The action of `U / I` -/

variable {R L I}

/-- On a module killed by `I`, the action of `U` factors through `U / I`.-/
def quotientAction (hM : IsKilledBy I M) : AdQuotient R L I →ₗ[R] Module.End R M :=
  (adIdeal R L I).toSubmodule.liftQ
    ((actionHom M).toLinearMap ∘ₗ (AdRegular.equiv R L).toLinearMap)
    fun _ hu ↦ LinearMap.mem_ker.mpr (hM _ hu)

/--
@isnad1 id=eq.1h5v.s10.48eba51a2468 from=translated src=- shape=24b2eaa1 vocab=6d4257b4
-/
@[simp] theorem quotientAction_mk (hM : IsKilledBy I M) (u : AdRegular R L) :
    quotientAction hM (LieSubmodule.Quotient.mk u) = actionHom M (AdRegular.equiv R L u) := rfl

/-- The `U(L)`-orbit map `a ↦ a m` of `m ∈ M`, a morphism `U / I → M` of `L`-modules.-/
def orbitMap (hM : IsKilledBy I M) (m : M) : LeftQuotient R L I →ₗ⁅R,L⁆ M :=
  LieSubmodule.Quotient.lift _
    { toFun u := actionHom M (LeftRegular.equiv R L u) m
      map_add' u v := by simp
      map_smul' c u := by simp
      map_lie' {x u} := by
        change actionHom M (ι R x * LeftRegular.equiv R L u) m = _
        rw [map_mul, actionHom_ι]
        rfl }
    fun u hu ↦ LieModuleHom.mem_ker.mpr (by
      change actionHom M (LeftRegular.equiv R L u) m = 0
      rw [show actionHom M (LeftRegular.equiv R L u) = 0 from hM _ hu, LinearMap.zero_apply])

/--
@isnad1 id=eq.1h6v.s10.83fcf0d9a3ec from=translated src=- shape=b6a97011 vocab=4f926292
-/
@[simp] theorem orbitMap_mk (hM : IsKilledBy I M) (m : M) (u : LeftRegular R L) :
    orbitMap hM m (LieSubmodule.Quotient.mk u) = actionHom M (LeftRegular.equiv R L u) m := rfl

variable (I) in
/-- Right multiplication `a ↦ a u` on `U / I`, a morphism of `L`-modules.-/
def quotientMulRight (u : 𝓤) : LeftQuotient R L I →ₗ⁅R,L⁆ LeftQuotient R L I :=
  LieSubmodule.Quotient.lift _ ((LieSubmodule.Quotient.mk' _).comp (LeftRegular.mulRight u))
    fun _ hv ↦ LieModuleHom.mem_ker.mpr
      ((LieSubmodule.Quotient.mk_eq_zero' (N := leftIdeal R L I)).mpr (I.mul_mem_right _ _ hv))

/--
@isnad1 id=eq.0h5v.s10.aaffef363ee4 from=translated src=- shape=cc811313 vocab=78210fac
-/
@[simp] theorem quotientMulRight_mk (u : 𝓤) (v : LeftRegular R L) :
    quotientMulRight I u (LieSubmodule.Quotient.mk v) =
      LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm (LeftRegular.equiv R L v * u)) :=
  rfl

/-! ### From `g : V → A^{ad} ⊗ W` to natural transformations -/

variable {V W : Type*} [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]

/-! ### From natural transformations to `g` -/

variable (I) in
/-- The class of `1` in `U / I`.-/
abbrev quotientOne : LeftQuotient R L I :=
  LieSubmodule.Quotient.mk ((LeftRegular.equiv R L).symm 1)

end UniversalEnvelopingAlgebra
