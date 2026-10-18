/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.Converse.ConstantFamily
import Tengoku.LanaBelyi.Belyi.Converse.IsoDescent
import Tengoku.LanaBelyi.Belyi.Converse.Points
import Tengoku.LanaBelyi.Belyi.Converse.Spread

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent of finite étale covers along `k ⊆ K` (★)

The core theorem (★) of `references/converse-rie-design.md`: for `k` algebraically closed of
characteristic zero and algebraic over `ℚ`, `K ⊇ k` algebraically closed, `R` a finitely generated
`k`-algebra and `B` a finite étale `K ⊗[k] R`-algebra, there is a finite étale `R`-algebra `B₀`
with `K ⊗[k] B₀ ≅ B` as `K ⊗[k] R`-algebras.

The proof is assembled from the packages of the converse, assuming the rigidity statement over
`ℂ` (package S3c), which is recorded here as the proposition `Belyi.Converse.RigidityOverC`:

1. (S1, `exists_spread`) `B` is the base change of a finite étale `A ⊗[k] R`-algebra `B_A` along
   `A ⊆ K`, for a finitely generated smooth `k`-subalgebra `A ⊆ K`.
2. (S4) There is a `k`-point `s : A → k` and an injective `k`-algebra map `ι : A → Ω := ULift ℂ`.
3. Let `B₀ := R ⊗[A ⊗[k] R] B_A` be the fibre of `B_A` at `s`; it is finite étale over `R`.
   The base change of `B_A` along `A → k → Ω` is the constant family `Ω ⊗[k] B₀`
   (`isBaseChangeAlong_fibre`).
4. (S3) By rigidity, the base change of `B_A` along `ι` is isomorphic to `Ω ⊗[k] B₀`, which is
   also the base change of the constant family `A ⊗[k] B₀` along `ι` (`isBaseChangeAlong_map`).
5. (S2, `nonempty_algEquiv_of_isBaseChangeAlong`) Hence the base changes of `B_A` and of
   `A ⊗[k] B₀` along `A ⊆ K`, namely `B` and `K ⊗[k] B₀`, are isomorphic.

## Main definitions and results

* `Belyi.Converse.FEtDescent k K`: the statement (★), as used by
  `Belyi/Converse/DefinableOfBelyi.lean`.
* `Belyi.Converse.RigidityOverC`: the statement of package S3c.
* `Belyi.Converse.exists_finiteEtale_model_of_rigidity`, `Belyi.Converse.fEtDescent_of_rigidity`:
  (★), assuming `RigidityOverC`.
-/

universe u

open TensorProduct

namespace Belyi.Converse

/-- **Finite étale descent along `k ⊆ K`** (the core theorem (★) of
`references/converse-rie-design.md`): every finite étale `K ⊗[k] R`-algebra `B`, for `R` a
finitely generated `k`-algebra, is the base change `K ⊗[k] B₀` of a finite étale `R`-algebra
`B₀`, compatibly with the structure maps from `K` and from `R`. -/
def FEtDescent (k K : Type u) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (B : Type u) [CommRing B] [Algebra (K ⊗[k] R) B] [Algebra.Etale (K ⊗[k] R) B]
    [Module.Finite (K ⊗[k] R) B],
    ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra R B₀) (_ : Algebra k B₀)
      (_ : IsScalarTower k R B₀) (_ : Algebra.Etale R B₀) (_ : Module.Finite R B₀)
      (e : K ⊗[k] B₀ ≃+* B),
      (∀ x : K, e (x ⊗ₜ 1) = algebraMap (K ⊗[k] R) B (x ⊗ₜ 1)) ∧
      (∀ r : R, e (1 ⊗ₜ algebraMap R B₀ r) = algebraMap (K ⊗[k] R) B (1 ⊗ₜ r))

/-- Rigidity over `ℂ` (package S3c): base changes of a finite étale family over a smooth
connected `Spec A` along any two `ℂ`-points are isomorphic. Here `ℂ` is lifted to `Type u` as
`ULift ℂ`, with an arbitrary `k`-algebra structure. -/
def RigidityOverC (k : Type u) [Field k] [Algebra k (ULift.{u} ℂ)] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Algebra.Smooth k A]
    (B : Type u) [CommRing B] [Algebra (A ⊗[k] R) B] [Algebra.Etale (A ⊗[k] R) B]
    [Module.Finite (A ⊗[k] R) B]
    (ι s : A →ₐ[k] ULift.{u} ℂ)
    (Bι Bs : Type u) [CommRing Bι] [Algebra (ULift.{u} ℂ ⊗[k] R) Bι] [CommRing Bs]
    [Algebra (ULift.{u} ℂ ⊗[k] R) Bs]
    (gι : B →+* Bι) (_ : IsBaseChangeAlong (R := R) ι gι) (gs : B →+* Bs)
    (_ : IsBaseChangeAlong (R := R) s gs),
    Nonempty (Bι ≃ₐ[ULift.{u} ℂ ⊗[k] R] Bs)

end Belyi.Converse
