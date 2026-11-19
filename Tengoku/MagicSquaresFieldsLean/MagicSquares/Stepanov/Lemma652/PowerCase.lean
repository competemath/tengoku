import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.DerivativeDataConstruct
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.ConcreteAssembly
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Lemma 6.52 with the derivative-data assumption removed

This wrapper retains `QuotientPowerIndependent` as an explicit input.
`Complete` proves the full book statement from absolute irreducibility
and the numerical hypotheses, including the translated case.
-/

/-- Concrete Lemma-6.52 assembly when `g=f^s`.
@isnad1 id=ex.11h12v.s10.99bbf4f32161 from=translated src=- shape=e6efc362 vocab=6cf06a2c
-/
theorem ln97_6_52_of_power_and_quotientIndependence
    {m r u D M K N G : ℕ}
    {f B : Polynomial F}
    (s : ℕ)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (hfK : f.natDegree ≤ K)
    (hgG : (f ^ s).natDegree ≤ G)
    (hMcard : M ≤ Fintype.card F)
    (hB : B.Monic)
    (hr : 0 < r)
    (hBdeg : B.natDegree = r)
    (hNu :
      (D + (M - 1) * (K - 1)) + u ≤ N)
    (hind :
      QuotientPowerIndependent
        (F := F) m (Fintype.card F) D (f ^ s))
    (hcount :
      r * M * (N + 1) < m * (u + 1) * (D + 1)) :
    ∃ E : Fin m → Polynomial (Polynomial F),
      (∃ i, E i ≠ 0) ∧
      stepanovAuxiliary
        (Fintype.card F) M f (f ^ s) E ≠ 0 ∧
      (∀ c, B.IsRoot (eval c (f ^ s)) →
        M ≤ rootMultiplicity c
          (stepanovAuxiliary
            (Fintype.card F) M f (f ^ s) E)) ∧
      (stepanovAuxiliary
        (Fintype.card F) M f (f ^ s) E).natDegree
        ≤ M * K +
          (D + Fintype.card F * u + (m - 1) * G) := by
  let data :=
    stepanovDerivativeDataOfPower
      (F := F) (m := m) (u := u) (D := D)
      (M := M) (K := K)
      f s hf hfdeg hfK hMcard
  exact
    ln97_6_52_of_derivativeData_and_quotientIndependence
      (F := F)
      hf hfK hgG hB hr hBdeg
      data hNu hind hcount

end LN97
end MagicSquares
