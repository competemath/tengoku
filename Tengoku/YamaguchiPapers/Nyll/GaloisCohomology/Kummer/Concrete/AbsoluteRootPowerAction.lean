/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.FiniteGeneration
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Power actions on roots in the algebraic closure

When a base automorphism acts by a specified power on the roots of unity,
its chosen lift acts by that power on the same roots in the algebraic closure.
The roots are descended using an actual primitive root in the base field.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K]

/-- The chosen lift of a base automorphism has the same power action on
the roots in the algebraic closure as on the roots in the base field.
@isnad1 id=eq.2h5v.s10.b9bdf46af4b4 from=translated src=- shape=7700a575 vocab=0ce1ec03
-/
theorem absoluteGaloisLift_nthRoot_eq_pow
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (a : ℕ)
    (hτ : ∀ ζ : K, ζ ^ (n : ℕ) = 1 → τ ζ = ζ ^ a)
    (z : nthRootsSubgroup (AlgebraicClosure K) (n : ℕ)) :
    Units.map (IsAlgClosure.equivOfEquiv (AlgebraicClosure K)
      (AlgebraicClosure K) τ).toMonoidHom (z : (AlgebraicClosure K)ˣ) =
        (z : (AlgebraicClosure K)ˣ) ^ a := by
  have hz : (z : (AlgebraicClosure K)ˣ) ^ (n : ℕ) = 1 := z.property
  obtain ⟨ζ, hζ⟩ := nthRootsOfUnityInBase_of_primitiveRoots
    (K := K) (L := AlgebraicClosure K) n hmu (z : (AlgebraicClosure K)ˣ) hz
  have hζpow : ζ ^ (n : ℕ) = 1 := by
    apply Units.map_injective (algebraMap K (AlgebraicClosure K)).injective
    rw [map_pow, map_one, hζ, hz]
  have hζfield : (ζ : K) ^ (n : ℕ) = 1 := congrArg Units.val hζpow
  rw [← hζ]
  apply Units.ext
  change IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) τ
      (algebraMap K (AlgebraicClosure K) (ζ : K)) =
    (algebraMap K (AlgebraicClosure K) (ζ : K)) ^ a
  rw [IsAlgClosure.equivOfEquiv_algebraMap, hτ (ζ : K) hζfield, map_pow]

end ClassFieldTower.Martinet.Shafarevich
