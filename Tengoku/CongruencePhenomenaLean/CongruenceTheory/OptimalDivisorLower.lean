import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.CentralizerPair
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.OrbitSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**`thm:optimal-divisor`, lower bound, general `(n,k,p)`**: final assembly from
`vp_stabilizer_le_pair` (`CentralizerPair.lean`), `mixed_support_factorial`
(`MixedSupportFactorial.lean`), and the class-sum divisibility engine
(`OrbitSum.lean`) — the same three-way combination `StrongTwoAdic.lean` used
for `thm:strong`, now for arbitrary `n, k ≥ 1` and prime `p` instead of just
`n = k = 2^s`, `p = 2`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat MvPolynomial

open scoped Classical

lemma mem_compl_of_orbRelPair {n k : ℕ} {g g' : Equiv.Perm (Fin n ⊕ Fin k)}
    (hg : g ∈ (HSetPair n k)ᶜ) (hr : (orbRelPair n k).r g' g) : g' ∈ (HSetPair n k)ᶜ := by
  obtain ⟨h, rfl⟩ := hr
  exact compl_HSetPair_invariant n k h g hg

lemma filter_compl_eq_filter_univ_pair {n k : ℕ} {g : Equiv.Perm (Fin n ⊕ Fin k)}
    (hg : g ∈ (HSetPair n k)ᶜ) :
    (HSetPair n k)ᶜ.filter ((orbRelPair n k).r g) = Finset.univ.filter ((orbRelPair n k).r g) := by
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun hr => mem_compl_of_orbRelPair hg ((orbRelPair n k).iseqv.symm hr)

/-- `n.descFactorial a` times `(n-a)!` recovers `n!`, for `a ≤ n`.-/
lemma descFactorial_mul_factorial_sub (n a : ℕ) (ha : a ≤ n) :
    n.descFactorial a * (n - a)! = n ! := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  rw [show a ! * n.choose a * (n - a)! = n.choose a * a ! * (n - a)! by ring]
  exact Nat.choose_mul_factorial_mul_factorial ha

end CongruenceTheory
