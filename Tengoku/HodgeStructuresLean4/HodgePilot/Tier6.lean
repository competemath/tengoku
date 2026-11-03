import Tengoku.HodgeStructuresLean4.HodgePilot.Tier5

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @QHodgeStructure` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tier 6: the corrected record — a pure RATIONAL Hodge structure of weight
`n` on a FINITE-dimensional ℚ-vector space (the audit's blocker fix), with
conjugation symmetry via the semilinear `σ` of Tier 5. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

/-- A pure rational Hodge structure of weight `n` on a finite-dimensional
ℚ-vector space `V`: a `(p,q)`-indexed internal direct-sum decomposition of the
complexification `ℂ ⊗[ℚ] V`, supported on `p + q = n`, with
`σ(H^{p,q}) = H^{q,p}`.-/
structure QHodgeStructure (n : ℤ) (V : Type*) [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] where
  H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  supported : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ≠ n → H pq = ⊥
  isInternal : DirectSum.IsInternal H
  conj_symm : ∀ p q : ℤ, (H (p, q)).map (sigmaQ V) = H (q, p)

end HodgePilot
