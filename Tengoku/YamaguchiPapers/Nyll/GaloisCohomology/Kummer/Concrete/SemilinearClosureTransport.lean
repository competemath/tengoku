/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Tengoku.Seed.Algebra.Algebra.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Semilinear conjugation under a change of extension field

An actual base-linear equivalence transports a semilinear automorphism and
intertwines its conjugation on the two relative Galois groups.
-/

namespace KummerTheory

variable {K Ω Ω' : Type*} [Field K] [Field Ω] [Field Ω']
  [Algebra K Ω] [Algebra K Ω']

/-- Transport a field automorphism along a base-linear field equivalence.-/
def transportSemilinearEquiv (e : Ω ≃ₐ[K] Ω') (a : Ω ≃+* Ω) : Ω' ≃+* Ω' :=
  (e.symm.toRingEquiv.trans a).trans e.toRingEquiv

/-- Evaluation of the transported field automorphism.
@isnad1 id=eq.0h6v.s9.1abd69cb6277 from=translated src=- shape=499cb192 vocab=0e86be80
-/
theorem transportSemilinearEquiv_apply (e : Ω ≃ₐ[K] Ω') (a : Ω ≃+* Ω) (x : Ω') :
    transportSemilinearEquiv e a x = e (a (e.symm x)) := by
  rfl

/-- Evaluation of its inverse.
@isnad1 id=eq.0h6v.s9.334cd6bd1e73 from=translated src=- shape=9d99da25 vocab=bc497051
-/
theorem transportSemilinearEquiv_symm_apply (e : Ω ≃ₐ[K] Ω') (a : Ω ≃+* Ω)
    (x : Ω') :
    (transportSemilinearEquiv e a).symm x = e (a.symm (e.symm x)) := by
  rfl

/-- Transport preserves the base automorphism of a semilinear map.
@isnad1 id=eq.1h7v.s10.ad5bd10252a6 from=translated src=- shape=2384bbaf vocab=db12cbea
-/
theorem transportSemilinearEquiv_algebraMap (τ : K ≃+* K)
    (e : Ω ≃ₐ[K] Ω') (a : Ω ≃+* Ω)
    (ha : ∀ k : K, a (algebraMap K Ω k) = algebraMap K Ω (τ k)) (k : K) :
    transportSemilinearEquiv e a (algebraMap K Ω' k) = algebraMap K Ω' (τ k) := by
  rw [transportSemilinearEquiv_apply, e.symm.commutes, ha, e.commutes]

/-- The Galois-group transport intertwines the two concrete semilinear
conjugations, before passing to any quotient or character.
@isnad1 id=eq.1h7v.s11.5826da02b957 from=translated src=- shape=9b4b0d0c vocab=c41917ed
-/
theorem autCongr_semilinearGaloisConjugate (τ : K ≃+* K)
    (e : Ω ≃ₐ[K] Ω') (a : Ω ≃+* Ω)
    (ha : ∀ k : K, a (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (σ : Gal(Ω/K)) :
    AlgEquiv.autCongr e (semilinearGaloisConjugate τ a ha σ) =
      semilinearGaloisConjugate τ (transportSemilinearEquiv e a)
        (transportSemilinearEquiv_algebraMap τ e a ha) (AlgEquiv.autCongr e σ) := by
  apply AlgEquiv.ext
  intro x
  change e (semilinearGaloisConjugate τ a ha σ (e.symm x)) =
    semilinearGaloisConjugate τ (transportSemilinearEquiv e a)
      (transportSemilinearEquiv_algebraMap τ e a ha) (AlgEquiv.autCongr e σ) x
  rw [semilinearGaloisConjugate_apply, semilinearGaloisConjugate_apply,
    transportSemilinearEquiv_apply, transportSemilinearEquiv_symm_apply]
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

end KummerTheory
