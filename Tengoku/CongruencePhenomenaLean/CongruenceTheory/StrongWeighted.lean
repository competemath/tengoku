import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.StrongTwoAdic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**Corollary `cor:weighted`** ("Weighted-permutation specialization"): specializing Theorem
`thm:strong` (`strong_two_adic`) via the evaluation ring homomorphism `X_j ↦ w_j`, for an
arbitrary integral weight sequence `w`, with no positivity assumption. This is the
permutation-native analogue of `cor:weighted`, matching the manuscript's `Cperm`/`CpermSum`
scoping already used for `thm:strong` itself (`CpermSum n` models `C_{2n}` on the domain
`Fin n ⊕ Fin n`, per `StrongTwoAdic.lean`).
-/

namespace CongruenceTheory

open MvPolynomial

/-- `A_w(n)`, the permutation-native weighted-permutation enumerator: `C_n(w_1,w_2,\dots)`
built from `Cperm` rather than the recurrence-native `C` (contrast `Aw` in
`WeightedSpecialization.lean`, which specializes `thm:universal` via `C`).-/
noncomputable def AwPerm (w : ℕ → ℤ) (n : ℕ) : ℤ := MvPolynomial.eval w (Cperm n)

/-- The `2n`-domain counterpart of `AwPerm`, matching `CpermSum`.-/
noncomputable def AwPermSum (w : ℕ → ℤ) (n : ℕ) : ℤ := MvPolynomial.eval w (CpermSum n)

end CongruenceTheory
