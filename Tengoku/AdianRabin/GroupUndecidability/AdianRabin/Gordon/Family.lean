import Tengoku.AdianRabin.GroupUndecidability.Host
import Tengoku.AdianRabin.GroupUndecidability.Host.Abelianization
import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.Gordon.Condition
import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.Gordon.Embedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Gordon's Lemma 2.1 and its specialization to the three-nine host. -/

namespace Undecidability.Gordon

def family (P : FP n m) (data : TorsionData P) : ℕ → FP 2 (m + 1) :=
  fun j ↦ transform P data (wordOfNat n j)

end Undecidability.Gordon

namespace Undecidability.Host

/-- Gordon's printed condition (2.1) for the host, using the generator `D`,
whose abelianized image is trivial (and therefore has order one).-/
def gordonCondition21 (datum : Thue.StandingDatum) :
    Gordon.Condition21 (presentationOf datum) where
  p := 1
  selected :=
    ⟨fun _ ↦ (0 : Fin 3), fun _ _ _ ↦ Subsingleton.elim _ _⟩
  q := fun _ ↦ 1
  q_pos := by intro i; omega
  gcd_q := by simp
  exactOrder := by
    intro i
    change orderOf (Abelianization.of
      (PresentedGroup.of (0 : Fin 3) : (presentationOf datum).Group)) = 1
    rw [d_eq_one_in_abelianization datum]
    simp

end Undecidability.Host
