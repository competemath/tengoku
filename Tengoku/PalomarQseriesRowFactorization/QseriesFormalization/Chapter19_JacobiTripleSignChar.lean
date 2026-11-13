import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter19
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter04
import Tengoku.Seed.Analysis.SpecificLimits.Normed
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Characterisation of `jacobiTripleSign`

Two clean closed forms for `jacobiTripleSign` (defined in `Chapter19.lean`
via `List.find?` on triangular indices):

* `jacobiTripleSign_triangular`: `jacobiTripleSign (k*(k+1)/2) = (-1)^k * (2k+1)`.
* `jacobiTripleSign_of_not_triangular`: `jacobiTripleSign n = 0` when no
  `k ≤ n` satisfies `n = k*(k+1)/2`.

These will be needed by both attack routes on the cube convolution
identity (Sylvester combinatorial proof in `Pending/Sylvester_TripleSum`
and the analytic-formal Taylor bridge in `Pending/JacobiCubeAnalyticToFormal`).
Stating them in the main build (rather than inside a Pending file)
keeps the headline target portable.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch19

/-- `n * (n + 1)` is divisible by 2.-/
theorem two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    exact ⟨m * (n + 1), by rw [hm]; ring⟩
  · obtain ⟨m, hm⟩ := ho
    refine ⟨n * (m + 1), ?_⟩
    rw [hm]; ring

/-- `2 * T_n = n * (n + 1)`.-/
theorem two_mul_triangular (n : ℕ) :
    2 * (n * (n + 1) / 2) = n * (n + 1) := by
  rw [Nat.mul_div_cancel' (two_dvd_mul_succ n)]

/-- Triangular numbers strictly increase on ℕ.-/
theorem triangular_strictMono :
    StrictMono (fun k : ℕ => k * (k + 1) / 2) := by
  intro a b hab
  show a * (a + 1) / 2 < b * (b + 1) / 2
  have h1 : a * (a + 1) < b * (b + 1) := by nlinarith
  have ha := two_mul_triangular a
  have hb := two_mul_triangular b
  omega

/-- `k ≤ T_k = k*(k+1)/2`.-/
theorem k_le_triangular (k : ℕ) :
    k ≤ k * (k + 1) / 2 := by
  rcases k with _ | k
  · simp
  · have h1 : 2 * (k + 1) ≤ (k + 1) * (k + 1 + 1) := by nlinarith
    have h2 := two_mul_triangular (k + 1)
    omega

/-! ### Analogous lemmas for `pentagonalSign` (parallels jacobiTripleSign).

For the analytic→formal bridge on the LHS of the cube identity, we also
need bounds and summability for `(pentagonalSign n : ℂ) * q^n`. -/

open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)

/-! ### Pentagonal index function and its injectivity.

For the analytic Euler pentagonal identity in `ℕ`-indexed form, we use
the map `j ↦ j*(3j+1)/2 : ℤ → ℕ` which sends integers to pentagonal
numbers (both `+` and `-` branches).  The map is injective.

This is the bridge from Ch04's bilateral `ℤ`-indexed analytic identity
to the `ℕ`-indexed formal-Taylor form needed for the cube argument. -/

/-- The pentagonal index function `ℤ → ℕ`: `j ↦ j*(3j+1)/2` (as Nat).-/
noncomputable def pentagonalIndex (j : ℤ) : ℕ := (j * (3 * j + 1) / 2).toNat

/-- `j * (3 * j + 1)` is non-negative for any integer `j`.-/
theorem int_j_three_j_plus_one_nonneg (j : ℤ) : 0 ≤ j * (3 * j + 1) := by
  by_cases hj : 0 ≤ j
  · have h1 : 0 ≤ 3 * j + 1 := by linarith
    exact mul_nonneg hj h1
  · push_neg at hj
    have h1 : 3 * j + 1 ≤ -2 := by linarith
    nlinarith

/-- `j * (3 * j + 1)` is divisible by 2.-/
theorem int_two_dvd_j_three_j_plus_one (j : ℤ) : (2 : ℤ) ∣ j * (3 * j + 1) := by
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (3 * j + 1), by rw [hm]; ring⟩
  · refine ⟨j * (3 * m + 2), ?_⟩
    rw [hm]; ring

/-- The pentagonal index function is injective on `ℤ`.

Proof: from `pentagonalIndex j1 = pentagonalIndex j2`, multiply through
to get `j1*(3*j1+1) = j2*(3*j2+1)`, factor as `(j1-j2)(3(j1+j2)+1) = 0`,
and observe `3(j1+j2)+1 = 0` has no integer solution (omega).-/
theorem pentagonalIndex_injective : Function.Injective pentagonalIndex := by
  intro j1 j2 h
  unfold pentagonalIndex at h
  have h1_nn : 0 ≤ j1 * (3 * j1 + 1) / 2 :=
    Int.ediv_nonneg (int_j_three_j_plus_one_nonneg j1) (by norm_num)
  have h2_nn : 0 ≤ j2 * (3 * j2 + 1) / 2 :=
    Int.ediv_nonneg (int_j_three_j_plus_one_nonneg j2) (by norm_num)
  have h_eq : j1 * (3 * j1 + 1) / 2 = j2 * (3 * j2 + 1) / 2 := by
    have hcast : ((j1 * (3 * j1 + 1) / 2 : ℤ).toNat : ℤ) =
        ((j2 * (3 * j2 + 1) / 2 : ℤ).toNat : ℤ) := by
      rw [h]
    rw [Int.toNat_of_nonneg h1_nn, Int.toNat_of_nonneg h2_nn] at hcast
    exact hcast
  have hd1 := int_two_dvd_j_three_j_plus_one j1
  have hd2 := int_two_dvd_j_three_j_plus_one j2
  have h_full : j1 * (3 * j1 + 1) = j2 * (3 * j2 + 1) := by
    have h2mul := congrArg (fun x => 2 * x) h_eq
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)
  have h_factor : (j1 - j2) * (3 * (j1 + j2) + 1) = 0 := by linarith
  rcases mul_eq_zero.mp h_factor with h_diff | h_sum
  · linarith
  · omega

/-- `(pentagonalIndex j : ℤ) = j * (3*j+1) / 2` (lifting `.toNat`).-/
theorem pentagonalIndex_cast (j : ℤ) :
    (pentagonalIndex j : ℤ) = j * (3 * j + 1) / 2 := by
  unfold pentagonalIndex
  rw [Int.toNat_of_nonneg]
  exact Int.ediv_nonneg (int_j_three_j_plus_one_nonneg j) (by norm_num)

/-- For `j < 0`, the pentagonal index has the "negative" form `(-j)*(3*(-j)-1)/2`.-/
theorem pentagonalIndex_neg_form (j : ℤ) :
    (pentagonalIndex j : ℤ) = (-j) * (3 * (-j) - 1) / 2 := by
  rw [pentagonalIndex_cast]
  congr 1
  ring

/-- For `j ≥ 0`, the pentagonal index equals `j.toNat * (3 * j.toNat + 1) / 2`
as a Nat (the "+ pentagonal" form).-/
theorem pentagonalIndex_of_nonneg (j : ℤ) (hj : 0 ≤ j) :
    pentagonalIndex j = j.toNat * (3 * j.toNat + 1) / 2 := by
  unfold pentagonalIndex
  have hj_eq : j = j.toNat := (Int.toNat_of_nonneg hj).symm
  conv_lhs => rw [hj_eq]
  push_cast
  rfl

/-- For `j < 0`, the pentagonal index equals `(-j).toNat * (3 * (-j).toNat - 1) / 2`
as a Nat (the "- pentagonal" form).-/
theorem pentagonalIndex_of_neg (j : ℤ) (hj : j < 0) :
    pentagonalIndex j = (-j).toNat * (3 * (-j).toNat - 1) / 2 := by
  unfold pentagonalIndex
  have hneg_pos : 0 ≤ -j := by linarith
  have hneg_eq : -j = (-j).toNat := (Int.toNat_of_nonneg hneg_pos).symm
  have h_id : j * (3 * j + 1) = (-j) * (3 * (-j) - 1) := by ring
  rw [h_id]
  conv_lhs => rw [hneg_eq]
  have hm_pos : 1 ≤ (-j).toNat := by
    have h1 : 1 ≤ -j := by linarith
    have : ((1 : ℕ) : ℤ) ≤ -j := by exact_mod_cast h1
    omega
  have h3m1 : (3 * (-j).toNat - 1 : ℤ) = (3 * (-j).toNat - 1 : ℕ) := by
    push_cast
    omega
  rw [h3m1]
  rfl

/-- "Plus pentagonal" `k(3k+1)/2` is strictly increasing in `k : ℕ`.-/
theorem plus_pentagonal_strict_mono :
    StrictMono (fun k : ℕ => k * (3 * k + 1) / 2) := by
  intro a b hab
  show a * (3*a+1)/2 < b * (3*b+1)/2
  have h1 : a * (3*a+1) < b * (3*b+1) := by nlinarith
  have hda : 2 ∣ a * (3 * a + 1) := by
    rcases Nat.even_or_odd a with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * a + 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨a * (3 * m + 2), ?_⟩
      rw [hm]; ring
  have hdb : 2 ∣ b * (3 * b + 1) := by
    rcases Nat.even_or_odd b with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * b + 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨b * (3 * m + 2), ?_⟩
      rw [hm]; ring
  have ha : 2 * (a * (3 * a + 1) / 2) = a * (3 * a + 1) :=
    Nat.mul_div_cancel' hda
  have hb : 2 * (b * (3 * b + 1) / 2) = b * (3 * b + 1) :=
    Nat.mul_div_cancel' hdb
  omega

/-- "Minus pentagonal" `k(3k-1)/2` strictly increases for `1 ≤ a < b`.-/
private theorem minus_pentagonal_strict_mono_pos {a b : ℕ}
    (ha : 1 ≤ a) (hab : a < b) :
    a * (3*a-1)/2 < b * (3*b-1)/2 := by
  have hb_pos : 1 ≤ b := by omega
  have h3am1_pos : 1 ≤ 3 * a - 1 := by omega
  have h3bm1_pos : 1 ≤ 3 * b - 1 := by omega
  have h_lt : a * (3 * a - 1) < b * (3 * b - 1) := by
    have h1 : 3 * a - 1 ≤ 3 * b - 1 := by omega
    have h2 : a * (3 * a - 1) ≤ a * (3 * b - 1) := Nat.mul_le_mul_left a h1
    have h3 : a * (3 * b - 1) < b * (3 * b - 1) := by
      have hpos : (3 * b - 1) > 0 := by omega
      exact (Nat.mul_lt_mul_right hpos).mpr hab
    omega
  have hda : 2 ∣ a * (3 * a - 1) := by
    rcases Nat.even_or_odd a with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * a - 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨a * (3 * m + 1), ?_⟩
      rw [hm]
      rw [show 3 * (2 * m + 1) - 1 = 6 * m + 2 by omega]
      ring
  have hdb : 2 ∣ b * (3 * b - 1) := by
    rcases Nat.even_or_odd b with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * b - 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨b * (3 * m + 1), ?_⟩
      rw [hm]
      rw [show 3 * (2 * m + 1) - 1 = 6 * m + 2 by omega]
      ring
  have h_eq_a : 2 * (a * (3 * a - 1) / 2) = a * (3 * a - 1) := Nat.mul_div_cancel' hda
  have h_eq_b : 2 * (b * (3 * b - 1) / 2) = b * (3 * b - 1) := Nat.mul_div_cancel' hdb
  omega

/-- "Minus pentagonal" `k(3k-1)/2` is strictly increasing in `k : ℕ`.-/
theorem minus_pentagonal_strict_mono :
    StrictMono (fun k : ℕ => k * (3 * k - 1) / 2) := by
  intro a b hab
  show a * (3*a-1)/2 < b * (3*b-1)/2
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h
    simp
    have : 1 ≤ b := hab
    by_cases hb1 : b = 1
    · rw [hb1]
    · have hb2 : 1 < b := by omega
      have h_inc := minus_pentagonal_strict_mono_pos
        (show (1 : ℕ) ≤ 1 from le_refl _) hb2
      omega
  · exact minus_pentagonal_strict_mono_pos h hab

/-- **No `k ∈ ℕ` satisfies "minus pentagonal at k" = "plus pentagonal at j > 0"**.

The algebraic fact: if `k(3k-1)/2 = j(3j+1)/2` with `j > 0`, then
`(k+j)(3(k-j) - 1) = 0`, which forces either `k+j = 0` (impossible for
positive `j`) or `3(k-j) = 1` (no integer solution).

Used to show `pentagonalSign`'s first `find?` branch returns `none` when
the index is a strict "+ pentagonal" number.-/
theorem no_minus_pentagonal_eq_plus_pentagonal (j : ℕ) (hj : 0 < j) :
    ∀ k : ℕ, k * (3 * k - 1) / 2 ≠ j * (3 * j + 1) / 2 := by
  intro k heq
  have hdk : 2 ∣ k * (3 * k - 1) := by
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * k - 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨k * (3 * m + 1), ?_⟩
      rw [hm]
      rw [show 3 * (2 * m + 1) - 1 = 6 * m + 2 by omega]
      ring
  have hdj : 2 ∣ j * (3 * j + 1) := by
    rcases Nat.even_or_odd j with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * j + 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨j * (3 * m + 2), ?_⟩
      rw [hm]; ring
  have h_eq_full : k * (3 * k - 1) = j * (3 * j + 1) := by
    have := congrArg (fun x => 2 * x) heq
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp at h_eq_full
    omega
  · have hk1 : 1 ≤ k := hk
    have h_int_eq : (k : ℤ) * (3 * k - 1) = j * (3 * j + 1) := by
      have h_cast_full : ((k * (3 * k - 1) : ℕ) : ℤ) = ((j * (3 * j + 1) : ℕ) : ℤ) := by
        exact_mod_cast h_eq_full
      have h_3km1 : ((3 * k - 1 : ℕ) : ℤ) = 3 * (k : ℤ) - 1 := by push_cast; omega
      have h_lhs : ((k * (3 * k - 1) : ℕ) : ℤ) = (k : ℤ) * (3 * k - 1) := by
        push_cast
        rw [h_3km1]
      have h_rhs : ((j * (3 * j + 1) : ℕ) : ℤ) = (j : ℤ) * (3 * j + 1) := by
        push_cast; ring
      linarith [h_cast_full, h_lhs.symm, h_rhs.symm]
    have h_factor : ((k : ℤ) + j) * (3 * ((k : ℤ) - j) - 1) = 0 := by
      have : (k : ℤ) * (3 * k - 1) - (j : ℤ) * (3 * j + 1) = 0 := by
        rw [h_int_eq]; ring
      nlinarith [this]
    rcases mul_eq_zero.mp h_factor with h_sum | h_diff
    · have hk_pos : (k : ℤ) ≥ 1 := by exact_mod_cast hk1
      have hj_pos : (j : ℤ) ≥ 1 := by exact_mod_cast hj
      omega
    · omega

/-- For `j ≥ 0`, `j.toNat = j.natAbs`.-/
theorem toNat_eq_natAbs_of_nonneg (j : ℤ) (hj : 0 ≤ j) :
    j.toNat = j.natAbs := by
  have h_eq : (j.toNat : ℤ) = (j.natAbs : ℤ) := by
    rw [Int.toNat_of_nonneg hj, Int.natAbs_of_nonneg hj]
  exact_mod_cast h_eq

/-- For `j ≤ 0`, `(-j).toNat = j.natAbs`.-/
theorem neg_toNat_eq_natAbs_of_nonpos (j : ℤ) (hj : j ≤ 0) :
    (-j).toNat = j.natAbs := by
  have h_nn : 0 ≤ -j := by linarith
  rw [Int.natAbs_neg j |>.symm]
  exact toNat_eq_natAbs_of_nonneg (-j) h_nn

/-- `pentagonalIndex (-k) = k * (3*k - 1) / 2` for `k : ℕ`.-/
theorem pentagonalIndex_neg_natCast (k : ℕ) :
    pentagonalIndex (-(k : ℤ)) = k * (3 * k - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; decide
  · have hkz : (-(k : ℤ)) < 0 := by
      have h1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
      linarith
    rw [pentagonalIndex_of_neg _ hkz]
    have : -(-(k : ℤ)) = k := by ring
    rw [this, Int.toNat_natCast]

/-- `pentagonalIndex (k : ℤ) = k * (3*k + 1) / 2` for `k : ℕ`.-/
theorem pentagonalIndex_natCast (k : ℕ) :
    pentagonalIndex (k : ℤ) = k * (3 * k + 1) / 2 := by
  rw [pentagonalIndex_of_nonneg _ (Int.natCast_nonneg k)]
  rw [Int.toNat_natCast]

/-! ### Cube identity via tsum_mul_tsum (analytic side). -/

open QseriesFormalization.PartI.Ch04 (eulerPentagonalInfiniteProduct)

end Ch19
end PartIV
end QseriesFormalization
