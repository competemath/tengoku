import Tengoku.TheIwasawaTowerLawForRamanujanSThirdOrderMockThetaFunction.IwasawaTower.CharacteristicThree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact order of the auxiliary series

Author: Joesph D. Burke III.

This file is deliberately downstream from the weak characteristic-three
induction.  Nothing in the tower-law proof imports or assumes the stronger
`W` result proved here.
-/

noncomputable section

namespace IwasawaTower.Series

open PowerSeries

private theorem delta_sq_hasLeading (N : ℕ) :
    HasLeading (2 * N) 1 (delta N ^ 2) := by
  have hpow : delta N ^ 2 = Y ^ (2 * N) := by
    rw [delta, neg_sq, ← pow_mul]
    congr 1
    omega
  rw [hpow, HasLeading]
  simpa using ModY.refl (2 * N + 1) (Y ^ (2 * N))

private theorem M_one_sub_one_vanishes : Vanishes 1 (M 1 - 1) := by
  have hc : constantCoeff (M 1 - 1) = 0 := by
    rw [map_sub, constantCoeff_M]
    norm_num
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hc
  exact ⟨q, by simpa [Y] using hq⟩

/-- The initial exact order for the second-order logarithmic correction.
@isnad1 id=hasleadi.0h0v.s5.eb15d49668fd from=translated src=- shape=fa5f2107 vocab=a6ad4563
-/
theorem M_three_hasLeading : HasLeading 2 1 (M 3) := by
  have hrec := M_three_block_precise (N := 1) ⟨0, by norm_num⟩
  have hrhs : HasLeading 2 1 (delta 1 ^ 2 * M 1) := by
    obtain ⟨q, hq⟩ := M_one_sub_one_vanishes
    refine ⟨q, ?_⟩
    rw [delta]
    simp only [map_one, one_mul, neg_sq]
    have hm1 : M 1 = 1 + Y * q := by
      rw [eq_add_of_sub_eq hq]
      ring
    rw [hm1]
    ring
  exact HasLeading.of_modY hrec hrhs

set_option maxHeartbeats 1000000 in
/-- For every positive power of three, `M_N` has exact order `N-1` and
leading coefficient one.
@isnad1 id=hasleadi.0h1v.s6.25d8aa174d22 from=translated src=- shape=ea329e2c vocab=58c6639b
-/
theorem M_three_power_hasLeading (a : ℕ) :
    HasLeading (3 ^ (a + 1) - 1) 1 (M (3 ^ (a + 1))) := by
  induction a with
  | zero => simpa using M_three_hasLeading
  | succ a ih =>
      let N := 3 ^ (a + 1)
      have hNpow : ∃ b, N = 3 ^ b := ⟨a + 1, rfl⟩
      have hrec := M_three_block_precise hNpow
      have ihN : HasLeading (N - 1) 1 (M N) := by
        simpa [N] using ih
      have hprod₀ := hasLeading_mul (delta_sq_hasLeading N) ihN
      have hprod : HasLeading (3 * N - 1) 1 (delta N ^ 2 * M N) := by
        have hNpos : 0 < N := by positivity
        have hexp : 2 * N + (N - 1) = 3 * N - 1 := by omega
        simpa only [hexp, one_mul] using hprod₀
      have hmod : ModY (3 * N - 1 + 1) (M (3 * N))
          (delta N ^ 2 * M N) := by
        have hNpos : 0 < N := by positivity
        simpa only [show 3 * N - 1 + 1 = 3 * N by omega] using hrec
      have hnext := HasLeading.of_modY hmod hprod
      simpa [N, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hnext

private theorem one_add_A_sq_A_fourth (N : ℕ) :
    1 + A N ^ 2 + A N ^ 4 = (A N ^ 2 - 1) ^ 2 := by
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  linear_combination hthree * A N ^ 2

private theorem A_fourth_sub_sq (N : ℕ) :
    A N ^ 4 - A N ^ 2 = A N ^ 2 * (A N ^ 2 - 1) := by ring

private theorem A_sq_sub_fourth (N : ℕ) :
    A N ^ 2 - A N ^ 4 = -(A N ^ 2 * (A N ^ 2 - 1)) := by ring

set_option maxHeartbeats 2000000 in
/-- The first level needed by the strong induction: `H_9` vanishes through
degree two.
@isnad1 id=vanishes.0h0v.s3.d11c1f2884e2 from=translated src=- shape=648e8daf vocab=be961e6c
-/
theorem H_nine_vanishes : Vanishes 3 (H 9) := by
  let D := A 3 ^ 2 - 1
  have hD : Vanishes 2 D := by
    simpa [D] using A_three_sq_sub_one_hasLeading.vanishes
  have hDsq : Vanishes 4 (D ^ 2) := by
    have h := hD.pow 2
    convert h using 1 <;> omega
  have hHmain : Vanishes 3 (H 3 * (1 + A 3 ^ 2 + A 3 ^ 4)) := by
    rw [one_add_A_sq_A_fourth]
    exact Vanishes.mono (by omega) (Vanishes.mul_left (H 3) hDsq)
  have hHlog : Vanishes 3 (L 3 * W 3 * (A 3 ^ 2 - A 3 ^ 4)) := by
    simpa [mul_assoc] using
      Vanishes.mul_right (W 3 * (A 3 ^ 2 - A 3 ^ 4)) L_three_vanishes
  have hLsq : Vanishes 6 (L 3 ^ 2) := by
    have h := L_three_vanishes.pow 2
    convert h using 1 <;> omega
  have hInnerL : Vanishes 2 (L 3 ^ 2 * (A 3 ^ 2 + A 3 ^ 4)) :=
    Vanishes.mono (by omega)
      (Vanishes.mul_right (A 3 ^ 2 + A 3 ^ 4) hLsq)
  have hInnerM : Vanishes 2 (M 3 * (A 3 ^ 4 - A 3 ^ 2)) := by
    rw [A_fourth_sub_sq]
    convert Vanishes.mul_left (M 3 * A 3 ^ 2) hD using 1 <;> ring
  have hInner : Vanishes 2
      (A 3 ^ 2 * (L 3 ^ 2 - M 3) + A 3 ^ 4 * (L 3 ^ 2 + M 3)) := by
    have hsum := Vanishes.add hInnerL hInnerM
    convert hsum using 1 <;> ring
  have hF : Vanishes 1 (F 3) := F_three_hasLeading.vanishes
  have hHthird : Vanishes 3
      (F 3 * (A 3 ^ 2 * (L 3 ^ 2 - M 3) +
        A 3 ^ 4 * (L 3 ^ 2 + M 3))) := by
    convert Vanishes.mul hF hInner using 1 <;> omega
  have hrhs : Vanishes 3
      (H 3 * (1 + A 3 ^ 2 + A 3 ^ 4) +
        L 3 * W 3 * (A 3 ^ 2 - A 3 ^ 4) +
        F 3 * (A 3 ^ 2 * (L 3 ^ 2 - M 3) +
          A 3 ^ 4 * (L 3 ^ 2 + M 3))) :=
    Vanishes.add (Vanishes.add hHmain hHlog) hHthird
  exact Vanishes.of_modY_zero
    (ModY.trans (H_three_block_coarse (N := 3) ⟨1, rfl⟩)
      (Vanishes.modY_zero hrhs))

/-- The three assertions propagated in the independent strong induction.-/
structure StrongData (b : ℕ) : Prop where
  wLead : HasLeading (2 * 3 ^ (b + 1) - 1) 1 (W (3 ^ (b + 2)))
  mLead : HasLeading (3 ^ (b + 2) - 1) 1 (M (3 ^ (b + 2)))
  hVanish : Vanishes (3 ^ (b + 1)) (H (3 ^ (b + 2)))

set_option maxHeartbeats 2000000 in
private theorem strong_step (b : ℕ) (ih : StrongData b) : StrongData (b + 1) := by
  let p := 3 ^ (b + 1)
  let N := 3 ^ (b + 2)
  have hNp : N = 3 * p := by simp [N, p, pow_succ, mul_comm]
  have hNpow : ∃ c, N = 3 ^ c := ⟨b + 2, rfl⟩
  have hNpos : 0 < N := by positivity
  let D := A N ^ 2 - 1
  have hbase := tower_data (b + 1)
  have hDlead : HasLeading (2 * p) (-1) D := by
    simpa [D, N, p] using hbase.aLead
  have hD : Vanishes (2 * p) D := hDlead.vanishes
  have hFlead : HasLeading (2 * p - 1) (-1) (F N) := by
    simpa [N, p] using hbase.fLead
  have hF : Vanishes (2 * p - 1) (F N) := hFlead.vanishes
  have hL : Vanishes N (L N) := by simpa [N] using hbase.lVanish
  have hW : Vanishes (2 * p - 1) (W N) := ih.wLead.vanishes
  have hM : Vanishes (N - 1) (M N) := ih.mLead.vanishes
  have hH : Vanishes p (H N) := by simpa [p, N] using ih.hVanish

  have hDsq : Vanishes (4 * p) (D ^ 2) := by
    have h := hD.pow 2
    convert h using 1 <;> omega

  -- Propagate the coarse estimate on H.
  have hHmain : Vanishes N (H N * (1 + A N ^ 2 + A N ^ 4)) := by
    rw [one_add_A_sq_A_fourth]
    have h := Vanishes.mul hH hDsq
    exact Vanishes.mono (by rw [hNp]; omega) h
  have hHlog : Vanishes N (L N * W N * (A N ^ 2 - A N ^ 4)) := by
    simpa [mul_assoc] using
      Vanishes.mul_right (W N * (A N ^ 2 - A N ^ 4)) hL
  have hLsq : Vanishes (2 * N) (L N ^ 2) := by
    have h := hL.pow 2
    convert h using 1 <;> omega
  have hInnerL : Vanishes N (L N ^ 2 * (A N ^ 2 + A N ^ 4)) :=
    Vanishes.mono (by omega)
      (Vanishes.mul_right (A N ^ 2 + A N ^ 4) hLsq)
  have hInnerM : Vanishes (N - 1 + 2 * p)
      (M N * (A N ^ 4 - A N ^ 2)) := by
    rw [A_fourth_sub_sq]
    have h := Vanishes.mul hM hD
    convert Vanishes.mul_left (A N ^ 2) h using 1 <;> ring
  have hInnerM' : Vanishes (N - (2 * p - 1))
      (M N * (A N ^ 4 - A N ^ 2)) := by
    apply Vanishes.mono _ hInnerM
    rw [hNp]
    omega
  have hInner : Vanishes (N - (2 * p - 1))
      (A N ^ 2 * (L N ^ 2 - M N) + A N ^ 4 * (L N ^ 2 + M N)) := by
    have hL' : Vanishes (N - (2 * p - 1))
        (L N ^ 2 * (A N ^ 2 + A N ^ 4)) :=
      Vanishes.mono (by omega) hInnerL
    have hsum := Vanishes.add hL' hInnerM'
    convert hsum using 1 <;> ring
  have hHthird : Vanishes N
      (F N * (A N ^ 2 * (L N ^ 2 - M N) +
        A N ^ 4 * (L N ^ 2 + M N))) := by
    have h := Vanishes.mul hF hInner
    convert h using 1
    rw [hNp]
    omega
  have hHrhs : Vanishes N
      (H N * (1 + A N ^ 2 + A N ^ 4) +
        L N * W N * (A N ^ 2 - A N ^ 4) +
        F N * (A N ^ 2 * (L N ^ 2 - M N) +
          A N ^ 4 * (L N ^ 2 + M N))) :=
    Vanishes.add (Vanishes.add hHmain hHlog) hHthird
  have hHnext : Vanishes N (H (3 * N)) :=
    Vanishes.of_modY_zero
      (ModY.trans (H_three_block_coarse hNpow) (Vanishes.modY_zero hHrhs))

  -- The leading W term is W_N D_N^2.
  have ihWLead : HasLeading (2 * p - 1) 1 (W N) := by
    simpa [N, p] using ih.wLead
  have hDsqLead₀ := hasLeading_pow hDlead 2
  have hWmain₀ := hasLeading_mul ihWLead hDsqLead₀
  have hWmain : HasLeading (2 * N - 1) 1 (W N * D ^ 2) := by
    convert hWmain₀ using 1
    · rw [hNp]
      omega
    · decide
  have hWfactor : 1 + A N ^ 2 + A N ^ 4 = D ^ 2 := by
    simpa [D] using one_add_A_sq_A_fourth N

  -- Every correction in the precise W identity starts at Y^(2N).
  have hAdiffFourth : Vanishes (2 * p) (A N ^ 4 - A N ^ 2) := by
    rw [A_fourth_sub_sq]
    simpa [mul_assoc] using Vanishes.mul_left (A N ^ 2) hD
  have hLogCorrection : Vanishes (2 * N)
      (L N * F N * (A N ^ 4 - A N ^ 2)) := by
    have hFA := Vanishes.mul hF hAdiffFourth
    have hAll := Vanishes.mul hL hFA
    apply Vanishes.mono _
    · simpa [mul_assoc] using hAll
    · rw [hNp]
      have hp : 0 < p := by positivity
      omega
  have hAdiff : Vanishes (2 * p) (A N ^ 2 - A N ^ 4) := by
    rw [A_sq_sub_fourth]
    simpa [mul_assoc] using Vanishes.mul_left (-A N ^ 2) hD
  have hLW : Vanishes p (L N * W N) := by
    exact Vanishes.mono (by rw [hNp]; omega) (Vanishes.mul hL hW)
  have hHminus : Vanishes p (H N - L N * W N) :=
    Vanishes.sub hH hLW
  have hFirstInner : Vanishes (3 * p)
      ((A N ^ 2 - A N ^ 4) * (H N - L N * W N)) := by
    convert Vanishes.mul hAdiff hHminus using 1 <;> omega
  have hLsqPlusM : Vanishes (N - 1) (L N ^ 2 + M N) := by
    exact Vanishes.add (Vanishes.mono (by omega) hLsq) hM
  have hSecondInner₀ : Vanishes (N - 1 + (2 * p - 1))
      ((L N ^ 2 + M N) * F N) :=
    Vanishes.mul hLsqPlusM hF
  have hSecondInner : Vanishes N
      (A N ^ 4 * (L N ^ 2 + M N) * F N) := by
    have hmono : Vanishes N ((L N ^ 2 + M N) * F N) := by
      apply Vanishes.mono _ hSecondInner₀
      rw [hNp]
      omega
    simpa [mul_assoc] using Vanishes.mul_left (A N ^ 4) hmono
  have hDeltaInner : Vanishes N
      ((A N ^ 2 - A N ^ 4) * (H N - L N * W N) -
        A N ^ 4 * (L N ^ 2 + M N) * F N) := by
    have hFirstN : Vanishes N
        ((A N ^ 2 - A N ^ 4) * (H N - L N * W N)) := by
      simpa [hNp] using hFirstInner
    exact Vanishes.sub hFirstN hSecondInner
  have hDeltaCorrection : Vanishes (2 * N)
      (delta N *
        ((A N ^ 2 - A N ^ 4) * (H N - L N * W N) -
          A N ^ 4 * (L N ^ 2 + M N) * F N)) := by
    convert Vanishes.mul (delta_vanishes N) hDeltaInner using 1 <;> omega
  have hCorrections : Vanishes (2 * N)
      (L N * F N * (A N ^ 4 - A N ^ 2) +
        delta N *
          ((A N ^ 2 - A N ^ 4) * (H N - L N * W N) -
            A N ^ 4 * (L N ^ 2 + M N) * F N)) :=
    Vanishes.add hLogCorrection hDeltaCorrection
  have hDrop : ModY (2 * N)
      (W N * (1 + A N ^ 2 + A N ^ 4) +
        L N * F N * (A N ^ 4 - A N ^ 2) +
        delta N *
          ((A N ^ 2 - A N ^ 4) * (H N - L N * W N) -
            A N ^ 4 * (L N ^ 2 + M N) * F N))
      (W N * D ^ 2) := by
    rw [hWfactor]
    simpa [add_assoc] using ModY.add (ModY.refl (2 * N) (W N * D ^ 2))
      (Vanishes.modY_zero hCorrections)
  have hWrec := W_three_block_precise hNpow
  have hWmainMod : ModY (2 * N) (W N * D ^ 2)
      (PowerSeries.C 1 * Y ^ (2 * N - 1)) := by
    simpa only [HasLeading, show 2 * N - 1 + 1 = 2 * N by omega] using hWmain
  have hWchain := ModY.trans hWrec (ModY.trans hDrop hWmainMod)
  have hWnext : HasLeading (2 * N - 1) 1 (W (3 * N)) := by
    simpa only [HasLeading, show 2 * N - 1 + 1 = 2 * N by omega] using hWchain

  refine ⟨?_, ?_, ?_⟩
  · simpa [N, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hWnext
  · simpa [N] using M_three_power_hasLeading (b + 2)
  · simpa [N, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hHnext

/-- Independent simultaneous induction proving the exact strong `W` result.
@isnad1 id=strongda.0h1v.s2.bcda74e60836 from=translated src=- shape=5c11bb93 vocab=1f278ba6
-/
theorem strong_data (b : ℕ) : StrongData b := by
  induction b with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simpa using W_nine_hasLeading
      · simpa using M_three_power_hasLeading 1
      · simpa using H_nine_vanishes
  | succ b ih => simpa [Nat.succ_eq_add_one] using strong_step b ih

end IwasawaTower.Series
