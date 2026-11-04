import Tengoku.ErdosLean.ErdosLean.Erdos956Upper.Statement
import Tengoku.ErdosLean.ErdosLean.Erdos956.Main
import Tengoku.ErdosLean.ErdosLean.Erdos956Upper.Parts.PairSplit
import Tengoku.ErdosLean.ErdosLean.Erdos956Upper.Parts.SideBound
import Tengoku.ErdosLean.ErdosLean.Erdos956Upper.Parts.CrossingLemma
import Tengoku.ErdosLean.ErdosLean.Erdos956Upper.Parts.CrossingCount
import Tengoku.ErdosLean.ErdosLean.Erdos956Upper.Parts.FinalArith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős Problem 956 (JSP-000796): the Erdős–Pach upper bound and `h(n) = Θ(n^{4/3})`

Assembly of the parts in `Parts/`:

`#unitPairs ≤ #upperPairs + #sidePairs` (P5), `#sidePairs ≤ 2n` (P7),
`#upperPairs ≤ e + n` (P14), and the crossing lemma (P13) applied to the upper drawing, whose
crossings are counted in P15, gives `e ≤ 8n/p + p²·4n²`; P16 turns this into `≤ 36 n^{4/3}`.
-/

namespace Erdos956Upper

open Erdos956 Filter Asymptotics

/-- Every admissible configuration of `n` translates has at most `36 n^{4/3}` unit pairs.
@isnad1 id=le.1h2v.s6.58f0e24060b2 from=translated src=- shape=00ce370f vocab=55d0c345
-/
theorem unitPairs_card_le_rpow {C : Set E} {X : Finset E} (hadm : Admissible C X) :
    ((unitPairs C X).card : ℝ) ≤ 36 * (X.card : ℝ) ^ ((4 : ℝ) / 3) := by
  have hS := admissible_sepConfig hadm
  have h1 := unitPairs_card_le hadm
  have h2 := upperPairs_card_le hS
  have h3 := sidePairs_card_le hS
  have h5 := crossDisj_upper_le hS
  have h4 : ∀ p : ℝ, 0 < p → p ≤ 1 / 4 →
      ((upperEdges (diffSet C) X).card : ℝ) ≤
        8 * (X.card : ℝ) / p +
          p ^ 2 * ((crossDisj (upperEdges (diffSet C) X) (upperArc (diffSet C))).card : ℝ) :=
    fun p hp0 hp => crossing_lemma X _ _ (upperEdges_valid hS) (upperEdges_ends hS)
      (upperEdges_avoid hS) (upperEdges_simple hS) (crossAdj_upper_le hS) hp0 hp
  have key := final_arith X.card ((upperPairs (diffSet C) X).card : ℝ)
    ((sidePairs (diffSet C) X).card : ℝ) ((upperEdges (diffSet C) X).card : ℝ)
    ((crossDisj (upperEdges (diffSet C) X) (upperArc (diffSet C))).card : ℝ)
    (by exact_mod_cast h2) (by exact_mod_cast h3) (by exact_mod_cast h5) h4
  calc ((unitPairs C X).card : ℝ)
      ≤ ((upperPairs (diffSet C) X).card : ℝ) + ((sidePairs (diffSet C) X).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ 36 * (X.card : ℝ) ^ ((4 : ℝ) / 3) := key

/-- `h(n) ≤ 36 n^{4/3}` for every `n`.
@isnad1 id=le.0h1v.s5.93cdaa500f70 from=translated src=- shape=65e16f9b vocab=0800823d
-/
theorem h_le (n : ℕ) : (h n : ℝ) ≤ 36 * (n : ℝ) ^ ((4 : ℝ) / 3) := by
  set B : ℝ := 36 * (n : ℝ) ^ ((4 : ℝ) / 3)
  have hB : 0 ≤ B := by positivity
  have hle : h n ≤ ⌊B⌋₊ := by
    unfold h
    apply csSup_le'
    rintro m ⟨C, X, hX, hadm, rfl⟩
    apply Nat.le_floor
    have := unitPairs_card_le_rpow hadm
    rw [hX] at this
    exact this
  calc (h n : ℝ) ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast hle
    _ ≤ B := Nat.floor_le hB

end Erdos956Upper

namespace Erdos956

open Filter Asymptotics

/-- **Erdős–Pach** (Combinatorica 10 (1990)): `h(n) ≪ n^{4/3}`, unconditionally.
@isnad1 id=erdospac.0h0v.s0.336483ae1c06 from=translated src=- shape=45709ebd vocab=336483ae
-/
theorem erdos956_upper : ErdosPachUpperBound := ⟨36, Erdos956Upper.h_le⟩

/-- The upper bound for all large `n`.
@isnad1 id=erdos956.0h0v.s0.774068c38955 from=translated src=- shape=45709ebd vocab=774068c3
-/
theorem erdos956_upperEventually : Erdos956UpperEventually :=
  ⟨36, Eventually.of_forall Erdos956Upper.h_le⟩

/-- `h(n) = Θ(n^{4/3})`.
@isnad1 id=erdos956.0h0v.s0.db4ec47a42ac from=translated src=- shape=45709ebd vocab=db4ec47a
-/
theorem erdos956_theta : Erdos956Theta := erdos956_theta_of_upper erdos956_upper

/-- **Erdős #956, complete answer.**
@isnad1 id=erdos956.0h0v.s0.d1a84d8d0ac3 from=translated src=- shape=45709ebd vocab=d1a84d8d
-/
theorem erdos956_fullAnswer : Erdos956FullAnswer :=
  ⟨erdos956, erdos956_lowerBound, erdos956_allExponents, erdos956_upper,
    erdos956_upperEventually, erdos956_theta⟩

end Erdos956
