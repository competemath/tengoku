/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# degree bounds for the division remainder

This file supplies the degree estimate for the remainder in the coefficientwise Hensel
correction step.  It removes the later need to assume separately that the
residue of the remainder has small degree.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the remainder estimate before reducing
coefficients.
@isnad1 id=le.2h4v.s6.d87a67edc771 from=translated src=- shape=c89d5551 vocab=390f0d35
-/
theorem henselFactorization_remainder_natDegree_le_of_degree_lt
    {R : Type*} [CommRing R] {g0 p : R[X]} {m : ℕ}
    (hg0nat : g0.natDegree = m) (hpdeg : p.degree < g0.degree) :
    p.natDegree ≤ m := by
  apply Polynomial.natDegree_le_of_degree_le
  have hlt : p.degree < (m : WithBot ℕ) := by
    calc
      p.degree < g0.degree := hpdeg
      _ ≤ (g0.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ = (m : WithBot ℕ) := by rw [hg0nat]
  exact hlt.le

end Valuations
end AlgebraicNumberTheory

end
