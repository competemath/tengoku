import Tengoku.Seed.Algebra.MvPolynomial.Funext

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms eq_zero_of_eval_algebraMap_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eq_zero_of_eval_algebraMap_eq_zero_of_denominator_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Polynomial identity from an infinite embedded base-field grid

This is an ordinary polynomial lemma.  It does not construct a rational action
or prove that any particular denominator-cleared invariant vanishes.
-/

noncomputable section

namespace AlbertLean.Generic.OpenGridIdentity

universe u v w

variable {k : Type u} {K : Type v} {σ : Type w}
variable [Field k] [Infinite k] [Field K] [Algebra k K]

/-- A polynomial over `K` which vanishes on the whole embedded `k`-grid is zero.
The variable type need not be finite.-/
theorem eq_zero_of_eval_algebraMap_eq_zero
    (P : MvPolynomial σ K)
    (hP : ∀ a : σ → k,
      MvPolynomial.eval ((algebraMap k K) ∘ a) P = 0) :
    P = 0 := by
  classical
  apply MvPolynomial.funext_set
    (fun _ : σ => Set.range (algebraMap k K))
    (fun _ => Set.infinite_range_of_injective (algebraMap k K).injective)
  intro x hx
  choose a ha using fun i => hx i (Set.mem_univ i)
  have hxa : (algebraMap k K) ∘ a = x := funext ha
  rw [← hxa]
  simpa using hP a

/-- Vanishing on the base-grid principal open cut out by a nonzero base
polynomial implies a polynomial identity over the extension field.-/
theorem eq_zero_of_eval_algebraMap_eq_zero_of_denominator_ne_zero
    (D : MvPolynomial σ k) (P : MvPolynomial σ K) (hD : D ≠ 0)
    (hP : ∀ a : σ → k, MvPolynomial.eval a D ≠ 0 →
      MvPolynomial.eval ((algebraMap k K) ∘ a) P = 0) :
    P = 0 := by
  let f : k →+* K := algebraMap k K
  have hproduct : MvPolynomial.map f D * P = 0 := by
    apply eq_zero_of_eval_algebraMap_eq_zero (k := k)
    intro a
    rw [MvPolynomial.eval_mul]
    by_cases hDa : MvPolynomial.eval a D = 0
    · have hmapDa :
          MvPolynomial.eval (f ∘ a) (MvPolynomial.map f D) = 0 := by
        rw [← MvPolynomial.map_eval, hDa, map_zero]
      rw [hmapDa, zero_mul]
    · rw [hP a hDa, mul_zero]
  have hmapD : MvPolynomial.map f D ≠ 0 := by
    intro h
    apply hD
    apply MvPolynomial.map_injective f f.injective
    simpa only [map_zero] using h
  exact (mul_eq_zero.mp hproduct).resolve_left hmapD

end AlbertLean.Generic.OpenGridIdentity
