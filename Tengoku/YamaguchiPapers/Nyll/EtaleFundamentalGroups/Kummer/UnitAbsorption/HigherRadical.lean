/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.PureRadical
import Tengoku.Seed.RingTheory.TensorProduct.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-etale unit absorption after a higher radical base change

If `e ∣ N`, the pure `e`-th root cover of an element maps canonically to
the pure `N`-th root cover by sending the first root to the `(N / e)`-th
power of the second.  This is the integral map needed to base change the
finite-etale unit factor supplied by the DVR Abhyankar calculation from the
ramification-index root to a prescribed larger root cover.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped TensorProduct
open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

/-- The canonical map from an `e`-th pure root cover to an `N`-th pure root
cover when `e ∣ N`.-/
def adjoinRootPowerMapOfDvd
    {A : Type u} [CommRing A] {e N : ℕ} (hdiv : e ∣ N) (a : A) :
    AdjoinRoot (X ^ e - C a) →ₐ[A] AdjoinRoot (X ^ N - C a) := by
  apply AdjoinRoot.liftAlgHom (X ^ e - C a) (Algebra.ofId A _)
    (AdjoinRoot.root (X ^ N - C a) ^ (N / e))
  change aeval (AdjoinRoot.root (X ^ N - C a) ^ (N / e))
    (X ^ e - C a) = 0
  rw [map_sub, map_pow, aeval_X, aeval_C]
  rw [← pow_mul, Nat.div_mul_cancel hdiv]
  rw [adjoinRoot_root_pow, AdjoinRoot.algebraMap_eq, sub_self]

/--
@isnad1 id=eq.1h4v.s12.2d36403d1501 from=translated src=- shape=cfce1ba9 vocab=4c35872b
-/
@[simp]
theorem adjoinRootPowerMapOfDvd_root
    {A : Type u} [CommRing A] {e N : ℕ} (hdiv : e ∣ N) (a : A) :
    adjoinRootPowerMapOfDvd hdiv a
        (AdjoinRoot.root (X ^ e - C a)) =
      AdjoinRoot.root (X ^ N - C a) ^ (N / e) := by
  simp [adjoinRootPowerMapOfDvd]

/-- The pure positive root polynomial of a prime element over a DVR is
prime, hence its adjoin-root algebra is a domain.
@isnad1 id=isdomain.2h3v.s9.789f52d1dbeb from=translated src=- shape=5f2377db vocab=4b57bf04
-/
theorem isDomain_adjoinRoot_X_pow_sub_C_of_prime
    {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {N : ℕ} (hN : 0 < N) (varpi : V) (hvarpi : Prime varpi) :
    IsDomain (AdjoinRoot (X ^ N - C varpi)) := by
  let p : V[X] := X ^ N - C varpi
  let K := FractionRing V
  have hNne : N ≠ 0 := hN.ne'
  have hpMonic : p.Monic := monic_X_pow_sub_C varpi hNne
  have hpIrreducibleMap :
      Irreducible (p.map (algebraMap V K)) := by
    simpa [p] using
      irreducible_X_pow_sub_C_fractionRing_of_prime hvarpi hN
  have hpIrreducible : Irreducible p :=
    (hpMonic.irreducible_iff_irreducible_map_fraction_map).2
      hpIrreducibleMap
  exact AdjoinRoot.isDomain_of_prime hpIrreducible.prime

end EtaleFundamentalGroups.Kummer

end
