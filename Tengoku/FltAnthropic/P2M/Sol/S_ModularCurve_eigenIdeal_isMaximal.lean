import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_eigenIdeal_isMaximal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_eigenIdeal_isMaximal

open ModularCurve

/--
@isnad1 id=ismaxima.0h2v.s5.4c8ee8c36947 from=translated src=- shape=5c890f4a vocab=33738a7b
-/
theorem solution {k : Type*} [Field k] [Finite k] (a : Nat.Primes → k) :
    (ModularCurve.eigenIdeal a).IsMaximal := by
  haveI : (eigenIdeal a).IsPrime := RingHom.ker_isPrime _
  haveI : Finite (HeckeAlg ⧸ eigenIdeal a) := by
    have e := RingHom.quotientKerEquivRange (R := HeckeAlg)
      (MvPolynomial.aeval (R := ℤ) a : HeckeAlg →ₐ[ℤ] k).toRingHom
    exact Finite.of_equiv _ e.symm.toEquiv
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
