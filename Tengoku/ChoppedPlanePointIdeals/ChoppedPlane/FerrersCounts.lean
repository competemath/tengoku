module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FerrersGrid
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Numerics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Exact point counts for the split Ferrers configurations. -/

namespace ChoppedPlane.Ferrers

open scoped BigOperators

variable {m : ℕ}

/-- The sum of the sizes of the rectangular blocks above the diagonal.-/
def weightedPairs (δ : Fin m → ℕ) : ℕ :=
  ∑ ij : {ij : Fin m × Fin m // ij.1 < ij.2}, δ ij.val.1 * δ ij.val.2

/-- Splitting all ordered pairs into the diagonal and the two orientations of
each strict pair gives the doubled elementary symmetric sum.
@isnad1 id=eq.0h2v.s6.f053384e057e from=translated src=- shape=46ab0f6e vocab=d0065b1e
-/
theorem weightedPairs_square (δ : Fin m → ℕ) :
    (∑ i, δ i) ^ 2 = (∑ i, δ i ^ 2) + 2 * weightedPairs δ := by
  classical
  let w := fun ij : Fin m × Fin m => δ ij.1 * δ ij.2
  have hpoint (ij : Fin m × Fin m) : w ij =
      (if ij.1 = ij.2 then δ ij.1 ^ 2 else 0) +
      (if ij.1 < ij.2 then w ij else 0) +
      (if ij.2 < ij.1 then w ij else 0) := by
    rcases lt_trichotomy ij.1 ij.2 with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_gt h]
    · simp [h, w, pow_two]
    · simp [h, ne_of_gt h, not_lt_of_gt h]
  have hsum : (∑ ij, w ij) =
      (∑ ij : Fin m × Fin m, if ij.1 = ij.2 then δ ij.1 ^ 2 else 0) +
      (∑ ij : Fin m × Fin m, if ij.1 < ij.2 then w ij else 0) +
      (∑ ij : Fin m × Fin m, if ij.2 < ij.1 then w ij else 0) := by
    calc
      _ = ∑ ij : Fin m × Fin m,
          ((if ij.1 = ij.2 then δ ij.1 ^ 2 else 0) +
           (if ij.1 < ij.2 then w ij else 0) +
           (if ij.2 < ij.1 then w ij else 0)) := by
        apply Finset.sum_congr rfl
        intro ij _
        exact hpoint ij
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hdiag : (∑ ij : Fin m × Fin m, if ij.1 = ij.2 then δ ij.1 ^ 2 else 0) =
      ∑ i, δ i ^ 2 := by simp [Fintype.sum_prod_type]
  have hlt : (∑ ij : Fin m × Fin m, if ij.1 < ij.2 then w ij else 0) = weightedPairs δ := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  have hgt : (∑ ij : Fin m × Fin m, if ij.2 < ij.1 then w ij else 0) = weightedPairs δ := by
    rw [← hlt]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (by intro ij; simp [w, mul_comm])
  have htot : (∑ ij : Fin m × Fin m, w ij) = (∑ i, δ i) ^ 2 := by
    rw [pow_two, Fintype.sum_mul_sum]
    exact Fintype.sum_prod_type _
  rw [htot, hdiag, hlt, hgt] at hsum
  omega

/-- The universal exact cardinality identity for any row-degree profile.
@isnad1 id=eq.0h2v.s8.f11df15881bd from=translated src=- shape=d1c793b3 vocab=cde8914a
-/
theorem selected_card_square (δ : Fin m → ℕ) :
    (∑ i, δ i) ^ 2 = (∑ i, δ i ^ 2) + 2 * Fintype.card (SelectedIndex δ) := by
  rw [selected_card]
  exact weightedPairs_square δ

/-- Only the sum of the row degrees and their squares are needed to recover
the desired point count.
@isnad1 id=eq.2h4v.s9.197abdcfe2bb from=translated src=- shape=fe19a284 vocab=e5c6fc94
-/
theorem selected_card_of_sums (δ : Fin m → ℕ) (d r : ℕ)
    (hsum : (∑ i, δ i) = d + 2)
    (hsquares : (∑ i, δ i ^ 2) = d + 2 + 2 * r) :
    Fintype.card (SelectedIndex δ) = (d + 2).choose 2 - r := by
  have hsq := selected_card_square δ
  rw [hsum, hsquares] at hsq
  have hN : 2 * N d = (d + 1) * (d + 2) := by exact_mod_cast twice_N d
  have hcount : Fintype.card (SelectedIndex δ) + r = N d := by nlinarith
  change Fintype.card (SelectedIndex δ) = N d - r
  omega

/-- A positive profile with `r` quadratic rows and `a` linear rows.-/
def positiveProfile (r a : ℕ) : Fin (r + a) → ℕ :=
  fun i => if i.val < r then 2 else 1

/--
@isnad1 id=lt.0h3v.s4.7345f0f8e96c from=translated src=- shape=1977fa55 vocab=66fe43a3
-/
theorem positiveProfile_pos (r a : ℕ) (i : Fin (r + a)) :
    0 < positiveProfile r a i := by
  unfold positiveProfile
  split_ifs <;> omega

/--
@isnad1 id=eq.0h2v.s6.27c39b3f12f8 from=translated src=- shape=e15b502c vocab=e06417c9
-/
theorem positiveProfile_sum (r a : ℕ) :
    (∑ i, positiveProfile r a i) = 2 * r + a := by
  rw [Fin.sum_univ_add]
  have hfirst (i : Fin r) : positiveProfile r a (Fin.castAdd a i) = 2 := by
    simp [positiveProfile, i.isLt]
  have hsecond (i : Fin a) : positiveProfile r a (Fin.natAdd r i) = 1 := by
    simp [positiveProfile]
  simp_rw [hfirst, hsecond]
  simp [mul_comm]

/--
@isnad1 id=eq.0h2v.s6.dd82139e7b2f from=translated src=- shape=a115ad99 vocab=a9808969
-/
theorem positiveProfile_square_sum (r a : ℕ) :
    (∑ i, positiveProfile r a i ^ 2) = 4 * r + a := by
  rw [Fin.sum_univ_add]
  have hfirst (i : Fin r) : positiveProfile r a (Fin.castAdd a i) = 2 := by
    simp [positiveProfile, i.isLt]
  have hsecond (i : Fin a) : positiveProfile r a (Fin.natAdd r i) = 1 := by
    simp [positiveProfile]
  simp_rw [hfirst, hsecond]
  norm_num [mul_comm]

/--
@isnad1 id=eq.1h2v.s6.e3bf637cbbdd from=translated src=- shape=e32dba6f vocab=e3ba5ca3
-/
theorem positiveProfile_row_count {d r : ℕ} (h : 2 * r ≤ d + 2) :
    r + (d + 2 - 2 * r) = d + 2 - r := by omega

/-- For `a = d + 2 - 2r`, the actual selected configuration has the required
number `N(d) - r` of points.
@isnad1 id=eq.1h2v.s12.ea5d6ce89bc1 from=translated src=- shape=722ddbca vocab=130c3930
-/
theorem positiveProfile_selected_card {d r : ℕ} (h : 2 * r ≤ d + 2) :
    Fintype.card (SelectedIndex (positiveProfile r (d + 2 - 2 * r))) =
      (d + 2).choose 2 - r := by
  let a := d + 2 - 2 * r
  have ha : 2 * r + a = d + 2 := by dsimp [a]; omega
  have hsq := selected_card_square (positiveProfile r a)
  rw [positiveProfile_sum, positiveProfile_square_sum] at hsq
  have hN : 2 * N d = (d + 1) * (d + 2) := by exact_mod_cast twice_N d
  have hcount : Fintype.card (SelectedIndex (positiveProfile r a)) + r = N d := by
    nlinarith [hsq, ha, hN]
  change Fintype.card (SelectedIndex (positiveProfile r a)) = N d - r
  omega

/-- The same row multiset ordered so that both endpoint rows are quadratic:
the first `r - 1` rows and the final row have degree two.-/
def endpointProfile (r a : ℕ) : Fin (r + a) → ℕ :=
  fun i => if i.val < r - 1 ∨ i.val + 1 = r + a then 2 else 1

private def endpointPermutation (r a : ℕ) (hr : 0 < r) : Equiv.Perm (Fin (r + a)) :=
  Equiv.swap ⟨r - 1, by omega⟩ ⟨r + a - 1, by omega⟩

private theorem endpointProfile_eq (r a : ℕ) (hr : 0 < r) (i : Fin (r + a)) :
    endpointProfile r a i = positiveProfile r a (endpointPermutation r a hr i) := by
  classical
  let b : Fin (r + a) := ⟨r - 1, by omega⟩
  let l : Fin (r + a) := ⟨r + a - 1, by omega⟩
  change endpointProfile r a i = positiveProfile r a (Equiv.swap b l i)
  by_cases hib : i = b
  · subst i
    rw [Equiv.swap_apply_left]
    simp only [endpointProfile, positiveProfile, b, l]
    split_ifs <;> omega
  by_cases hil : i = l
  · subst i
    rw [Equiv.swap_apply_right]
    simp only [endpointProfile, positiveProfile, b, l]
    split_ifs <;> omega
  rw [Equiv.swap_apply_of_ne_of_ne hib hil]
  have hvb : i.val ≠ r - 1 := by intro h; apply hib; exact Fin.ext h
  have hvl : i.val ≠ r + a - 1 := by intro h; apply hil; exact Fin.ext h
  simp only [endpointProfile, positiveProfile]
  split_ifs <;> omega

/--
@isnad1 id=lt.0h3v.s4.86145f5e60f2 from=translated src=- shape=1977fa55 vocab=9db4a41d
-/
theorem endpointProfile_pos (r a : ℕ) (i : Fin (r + a)) :
    0 < endpointProfile r a i := by
  unfold endpointProfile
  split_ifs <;> omega

/--
@isnad1 id=eq.2h3v.s5.3c4484f240bd from=translated src=- shape=84cefcf7 vocab=a1408e74
-/
theorem endpointProfile_first {r a : ℕ} (hr : 2 ≤ r) (i : Fin (r + a))
    (hi : i.val = 0) : endpointProfile r a i = 2 := by
  simp [endpointProfile, hi, show 0 < r - 1 by omega]

/--
@isnad1 id=eq.1h3v.s5.ef38da6df264 from=translated src=- shape=74308541 vocab=9ad42808
-/
theorem endpointProfile_last {r a : ℕ} (i : Fin (r + a)) (hi : i.val + 1 = r + a) :
    endpointProfile r a i = 2 := by simp [endpointProfile, hi]

/--
@isnad1 id=eq.1h2v.s6.af7be4d616bf from=translated src=- shape=21335cca vocab=4b441a40
-/
theorem endpointProfile_sum (r a : ℕ) (hr : 0 < r) :
    (∑ i, endpointProfile r a i) = 2 * r + a := by
  simp_rw [endpointProfile_eq r a hr]
  rw [Equiv.sum_comp]
  exact positiveProfile_sum r a

/--
@isnad1 id=eq.1h2v.s6.f357fcf52df2 from=translated src=- shape=18d1860e vocab=eb8afea1
-/
theorem endpointProfile_square_sum (r a : ℕ) (hr : 0 < r) :
    (∑ i, endpointProfile r a i ^ 2) = 4 * r + a := by
  exact (Fintype.sum_equiv (endpointPermutation r a hr)
    (fun i => endpointProfile r a i ^ 2) (fun i => positiveProfile r a i ^ 2)
    (fun i => congrArg (fun n : ℕ => n ^ 2) (endpointProfile_eq r a hr i))).trans
    (positiveProfile_square_sum r a)

/--
@isnad1 id=eq.2h2v.s12.4d2d54fff23d from=translated src=- shape=83343132 vocab=918e719a
-/
theorem endpointProfile_selected_card {d r : ℕ} (hr : 0 < r) (h : 2 * r ≤ d + 2) :
    Fintype.card (SelectedIndex (endpointProfile r (d + 2 - 2 * r))) =
      (d + 2).choose 2 - r := by
  apply selected_card_of_sums _ d r
  · rw [endpointProfile_sum r _ hr]
    omega
  · rw [endpointProfile_square_sum r _ hr]
    omega

end ChoppedPlane.Ferrers
