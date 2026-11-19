import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.Centralizer
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.OrbitSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**Theorem `thm:strong`** ("Strong two-adic lifting"), permutation-native
form: final assembly from the orbit-bound valuation lemma, the
centralizer-in-`H` bound, and the general class-sum divisibility engine.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat

open scoped Classical

lemma mem_compl_of_orbRel {n : ℕ} {g g' : Equiv.Perm (Fin n ⊕ Fin n)}
    (hg : g ∈ (HSet n)ᶜ) (hr : (orbRel n).r g' g) : g' ∈ (HSet n)ᶜ := by
  obtain ⟨h, rfl⟩ := hr
  exact compl_HSet_invariant n h g hg

lemma filter_compl_eq_filter_univ {n : ℕ} {g : Equiv.Perm (Fin n ⊕ Fin n)}
    (hg : g ∈ (HSet n)ᶜ) :
    (HSet n)ᶜ.filter ((orbRel n).r g) = Finset.univ.filter ((orbRel n).r g) := by
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun hr => mem_compl_of_orbRel hg ((orbRel n).iseqv.symm hr)

end CongruenceTheory
