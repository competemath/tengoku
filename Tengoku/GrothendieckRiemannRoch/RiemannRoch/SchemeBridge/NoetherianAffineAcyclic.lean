/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.AlgebraicGeometry.Modules.Tilde
import Tengoku
import Tengoku.Seed.Algebra.Category.ModuleCat.EnoughInjectives
import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.Seed.LinearAlgebra.Isomorphisms
import Tengoku.Seed.RingTheory.Noetherian.Basic
import Tengoku.Seed.RingTheory.Spectrum.Prime.Noetherian
import Tengoku.Seed.Topology.Sheaves.Flasque

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Injective modules give flasque sheaves on Noetherian affine schemes

For a Noetherian ring `R` and an injective `R`-module `I`, this file proves that the associated
quasicoherent sheaf `Ĩ` on `Spec R` is flasque.  The main algebraic step solves a finite compatible
system of denominator equations in `I`.  Noetherianity makes the relevant annihilator chains
stabilize, and injectivity extends the resulting map from a finitely generated ideal.

Consequently, every section of `Ĩ` over an arbitrary open subset extends to `Spec R`, and the
underlying abelian sheaf has vanishing higher cohomology.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeBridge

variable {R : CommRingCat.{u}} [IsNoetherianRing R]
variable (I : ModuleCat.{u} R) [Injective I]

private def powerSystemSource {ι : Type u} (s : Finset ι) (b : ι → R) (N : ℕ) :
    (ι →₀ R) →ₗ[R] R where
  toFun c := ∑ i ∈ s, c i * b i ^ (N + 1)
  map_add' c d := by simp only [Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Finsupp.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum,
      RingHom.id_apply]

private def powerSystemTarget {ι : Type u} (s : Finset ι) (a : ι → I)
    (b : ι → R) (N : ℕ) : (ι →₀ R) →ₗ[R] I where
  toFun c := ∑ i ∈ s, c i • (b i ^ N • a i)
  map_add' c d := by
    simp only [Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Finsupp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

private def PowerSystemCompatible {ι : Type u} (s : Finset ι) (a : ι → I)
    (b : ι → R) (N : ℕ) : Prop :=
  LinearMap.ker (powerSystemSource s b N) ≤ LinearMap.ker (powerSystemTarget I s a b N)

private noncomputable def basicOpenLocalizedEquiv (f : R) :
    LocalizedModule.Away f I ≃ₗ[R]
      (structureSheafInType R I).presheaf.obj (.op (PrimeSpectrum.basicOpen f)) :=
  IsLocalizedModule.iso (.powers f) (StructureSheaf.toOpenₗ R I (PrimeSpectrum.basicOpen f))

end AlgebraicGeometry.SchemeBridge
