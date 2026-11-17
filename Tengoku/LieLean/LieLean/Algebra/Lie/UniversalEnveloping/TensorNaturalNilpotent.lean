/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.Lie.UniversalEnveloping.TensorNatural
import Tengoku.Seed.LinearAlgebra.TensorProduct.RightExactness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Changing the ideal, and natural endomorphisms vanishing on `U / I`-modules

For two-sided ideals `I ≤ J` of `U = U(L)`, the quotient map `U / I → U / J` is a morphism of
adjoint modules (`adQuotientMap`), and for a module killed by `J` the natural transformation
attached to `g : V → (U / I)^{ad} ⊗ W` only depends on the image of `g` in `(U / J)^{ad} ⊗ W`
(`tensorNatMap_adQuotientMap`). Taking `I = ⊥`, morphisms `V → U^{ad} ⊗ W` give natural
transformations `M ⊗ V → M ⊗ W` on all modules.

A natural endomorphism `θ` of `M ↦ M ⊗ V` which vanishes on every module killed by `I` is
nilpotent on every module with a filtration of length `n` whose subquotients are killed by `I`:
`θ_M ^ n = 0` (`pow_eq_zero_of_hasKilledFiltration`). This is the step of Humphreys' proof of
Theorem 10.7 (b) that passes from `U / U ker χ`-modules to the whole block of `χ`.

## Main definitions

* `UniversalEnvelopingAlgebra.adQuotientMap`: `(U / I)^{ad} → (U / J)^{ad}` for `I ≤ J`.
* `UniversalEnvelopingAlgebra.HasKilledFiltration I M n`: `M` has a chain of Lie submodules of
  length `n` with subquotients killed by `I`.

## Main results

* `UniversalEnvelopingAlgebra.tensorNatMap_adQuotientMap`.
* `UniversalEnvelopingAlgebra.pow_eq_zero_of_hasKilledFiltration`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open TensorProduct

namespace UniversalEnvelopingAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {I J : TwoSidedIdeal (UniversalEnvelopingAlgebra R L)}
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {V W : Type*} [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]

/--
@isnad1 id=iskilled.2h5v.s7.3e406186a5c5 from=translated src=- shape=1cf416e6 vocab=bd814795
-/
theorem IsKilledBy.mono (hIJ : I ≤ J) (hM : IsKilledBy J M) : IsKilledBy I M :=
  fun a ha ↦ hM a (hIJ ha)

/-- Every module is killed by the zero ideal.
@isnad1 id=iskilled.0h3v.s6.b4c723c5e155 from=translated src=- shape=14f0d548 vocab=60b87fb5
-/
theorem isKilledBy_bot : IsKilledBy (⊥ : TwoSidedIdeal (UniversalEnvelopingAlgebra R L)) M :=
  fun a ha ↦ by
    rw [TwoSidedIdeal.mem_bot] at ha
    rw [ha, map_zero]

variable (R L) in
/-- The quotient map `(U / I)^{ad} → (U / J)^{ad}` for `I ≤ J`.-/
def adQuotientMap (hIJ : I ≤ J) : AdQuotient R L I →ₗ⁅R,L⁆ AdQuotient R L J :=
  LieSubmodule.Quotient.lift _ (LieSubmodule.Quotient.mk' (adIdeal R L J))
    fun _ hu ↦ LieModuleHom.mem_ker.mpr ((LieSubmodule.Quotient.mk_eq_zero _).mpr (hIJ hu))

/--
@isnad1 id=eq.1h5v.s9.926fa257a6bf from=translated src=- shape=eb216273 vocab=426a6c49
-/
@[simp] theorem adQuotientMap_mk (hIJ : I ≤ J) (u : AdRegular R L) :
    adQuotientMap R L hIJ (LieSubmodule.Quotient.mk u) = LieSubmodule.Quotient.mk u := rfl

/-! ### Nilpotence -/

universe u

variable (I) in
/-- `M` has a chain `0 = M₀ ≤ M₁ ≤ ⋯ ≤ Mₙ = M` of Lie submodules whose subquotients are killed
by `I`.-/
inductive HasKilledFiltration : ∀ (M : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M], ℕ → Prop
  | zero (M : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
      [Subsingleton M] : HasKilledFiltration M 0
  | succ (M : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
      (N : LieSubmodule R L M) (n : ℕ) (hN : HasKilledFiltration N n)
      (hMN : IsKilledBy I (M ⧸ N)) : HasKilledFiltration M (n + 1)

end UniversalEnvelopingAlgebra
