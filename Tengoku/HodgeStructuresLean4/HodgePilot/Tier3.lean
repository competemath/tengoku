import Tengoku.HodgeStructuresLean4.HodgePilot.Tier2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @HodgeStructure` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tier 3 (stretch): the `HodgeStructure` record typechecks — (p,q)-indexed
`ℂ`-submodules of the complexification, internal-direct-sum axiom, and
conjugation symmetry expressed via `Submodule.map` along the semilinear `σ`. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

/-- `starRingEnd ℂ` is surjective (it is an involution), so `ℂ`-submodules can
be pushed forward along `σ`-semilinear maps.-/
instance : RingHomSurjective (starRingEnd ℂ) :=
  ⟨fun c => ⟨(starRingEnd ℂ) c, Complex.conj_conj c⟩⟩

/-- A pure Hodge structure of weight `n` on a real vector space `V`
(decomposition presentation; pilot version).-/
structure HodgeStructure (n : ℤ) (V : Type*) [AddCommGroup V] [Module ℝ V] where
  H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℝ] V)
  supported : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ≠ n → H pq = ⊥
  isInternal : DirectSum.IsInternal H
  conj_symm : ∀ p q : ℤ, (H (p, q)).map (sigma V) = H (q, p)

end HodgePilot
