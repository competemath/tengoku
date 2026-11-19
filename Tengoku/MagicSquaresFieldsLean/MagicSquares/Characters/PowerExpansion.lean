import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Constants
import Tengoku.Seed.Algebra.BigOperators.Pi
import Tengoku.Seed.Data.Fintype.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators Classical

/-- The linear factors that occur in a character-expansion monomial.-/
def powerExponentSupport {r d : ℕ} (e : Fin r → Fin d) : Finset (Fin r) :=
  Finset.univ.filter (fun i => (e i : ℕ) ≠ 0)

/--
@isnad1 id=iff.0h4v.s5.940f6c6e4dca from=translated src=- shape=3e03c83e vocab=2d6da650
-/
@[simp]
theorem mem_powerExponentSupport {r d : ℕ} (e : Fin r → Fin d) (i : Fin r) :
    i ∈ powerExponentSupport e ↔ (e i : ℕ) ≠ 0 := by
  simp [powerExponentSupport]

/-- There is exactly one empty-support exponent vector.
@isnad1 id=iff.1h3v.s5.e0a8b6cdbcda from=translated src=- shape=1134470e vocab=1e5ce65a
-/
theorem powerExponentSupport_eq_empty_iff {r d : ℕ} (hd : 0 < d)
    (e : Fin r → Fin d) :
    powerExponentSupport e = ∅ ↔ e = fun _ => ⟨0, hd⟩ := by
  simp only [Finset.eq_empty_iff_forall_notMem, mem_powerExponentSupport, not_not]
  constructor
  · intro h
    funext i
    exact Fin.ext (h i)
  · intro h i
    simp [h]

private theorem sum_nonzero_coordinate {r d : ℕ} (hd : 0 < d) (i : Fin r) :
    (∑ e : Fin r → Fin d, if (e i : ℕ) = 0 then (0 : ℝ) else 1) =
      (d : ℝ) ^ (r - 1) * ((d : ℝ) - 1) := by
  have hcard : Fintype.card {j : Fin r // j ≠ i} = r - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hfin : (∑ j : Fin d, if (j : ℕ) = 0 then (0 : ℝ) else 1) = (d : ℝ) - 1 := by
    calc
      _ = ∑ j : Fin d, (1 - if j = ⟨0, hd⟩ then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : (j : ℕ) = 0 ↔ j = ⟨0, hd⟩ :=
          ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
        simp only [hj]
        split_ifs <;> norm_num
      _ = _ := by simp [Finset.sum_sub_distrib]
  calc
    _ = ∑ p : Fin d × ({j : Fin r // j ≠ i} → Fin d),
          if (p.1 : ℕ) = 0 then (0 : ℝ) else 1 :=
      (Equiv.piSplitAt i (fun _ : Fin r => Fin d)).sum_comp
        (fun p => if (p.1 : ℕ) = 0 then (0 : ℝ) else 1)
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      change (∑ _ : ({j : Fin r // j ≠ i} → Fin d),
        ∑ j : Fin d, if (j : ℕ) = 0 then (0 : ℝ) else 1) = _
      rw [hfin]
      simp [hcard]
      ring

/-- The total sharp Weil cost for any number of distinct roots.
@isnad1 id=eq.1h2v.s7.2e145cdaaa17 from=translated src=- shape=2d412487 vocab=6bb33140
-/
theorem sum_powerExponentSupport_cost_general {r d : ℕ} (hd : 0 < d) :
    (∑ e : Fin r → Fin d, ((powerExponentSupport e).card - 1 : ℕ)) =
      (r : ℝ) * (d : ℝ) ^ (r - 1) * ((d : ℝ) - 1) - (d : ℝ) ^ r + 1 := by
  let z : Fin r → Fin d := fun _ => ⟨0, hd⟩
  have hpoint (e : Fin r → Fin d) :
      (((powerExponentSupport e).card - 1 : ℕ) : ℝ) =
        ((powerExponentSupport e).card : ℝ) - 1 + (if e = z then 1 else 0) := by
    by_cases h : e = z
    · subst e
      have hz : powerExponentSupport z = ∅ :=
        (powerExponentSupport_eq_empty_iff hd z).mpr rfl
      simp [hz]
    · have hpos : 1 ≤ (powerExponentSupport e).card := by
        have : powerExponentSupport e ≠ ∅ := by
          exact fun hs => h ((powerExponentSupport_eq_empty_iff hd e).mp hs)
        exact Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr this)
      rw [Nat.cast_sub hpos]
      simp [h]
  have hcard (e : Fin r → Fin d) :
      ((powerExponentSupport e).card : ℝ) =
        ∑ i : Fin r, if (e i : ℕ) = 0 then (0 : ℝ) else 1 := by
    simp [powerExponentSupport, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      ite_not]
  simp_rw [Nat.cast_sum, hpoint, hcard]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_comm]
  simp_rw [sum_nonzero_coordinate hd]
  simp [z]
  ring

/-- The eight-factor specialization gives the Section 14 constant.
@isnad1 id=eq.1h1v.s6.b673f52d0b99 from=translated src=- shape=0851f741 vocab=fc9a9794
-/
theorem sum_powerExponentSupport_cost {d : ℕ} (hd : 0 < d) :
    (∑ e : Fin 8 → Fin d, ((powerExponentSupport e).card - 1 : ℕ)) =
      centerOneC1 d := by
  rw [sum_powerExponentSupport_cost_general hd]
  norm_num [centerOneC1]
  ring

end MagicSquares
