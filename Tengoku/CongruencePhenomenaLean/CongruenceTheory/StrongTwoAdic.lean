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

/--
@isnad1 id=mem.2h3v.s8.cbf5faea4c6a from=translated src=- shape=50ebb8cf vocab=82ddebf5
-/
lemma mem_compl_of_orbRel {n : ℕ} {g g' : Equiv.Perm (Fin n ⊕ Fin n)}
    (hg : g ∈ (HSet n)ᶜ) (hr : (orbRel n).r g' g) : g' ∈ (HSet n)ᶜ := by
  obtain ⟨h, rfl⟩ := hr
  exact compl_HSet_invariant n h g hg

/--
@isnad1 id=eq.1h2v.s9.65104fa59711 from=translated src=- shape=124979eb vocab=a2ff152c
-/
lemma filter_compl_eq_filter_univ {n : ℕ} {g : Equiv.Perm (Fin n ⊕ Fin n)}
    (hg : g ∈ (HSet n)ᶜ) :
    (HSet n)ᶜ.filter ((orbRel n).r g) = Finset.univ.filter ((orbRel n).r g) := by
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun hr => mem_compl_of_orbRel hg ((orbRel n).iseqv.symm hr)

end CongruenceTheory
