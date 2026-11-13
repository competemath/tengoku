import Tengoku.Rankamplificationtotient.RankAmplification.BFPSPrimePredecessorReduction
import Tengoku.Rankamplificationtotient.RankAmplification.BFPSTotientWeight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Geometric shell summation for the BFPS predecessor-prime reduction This module turns the bounded largest-prime-factor shell estimate into a global finite estimate. -/

namespace RankAmplification

open Finset
open scoped BigOperators Nat.Prime

noncomputable section

/-! ## Exact geometric endpoints -/

/-- The decreasing geometric endpoint `⌊Y / base^i⌋`, with natural division supplying the floor.-/
def bfpsGeometricEndpoint (Y base i : ℕ) : ℕ :=
  Y / base ^ i

@[simp]
theorem bfpsGeometricEndpoint_zero (Y base : ℕ) :
    bfpsGeometricEndpoint Y base 0 = Y := by
  simp [bfpsGeometricEndpoint]

/-- One step divides the preceding endpoint by `base`.-/
theorem bfpsGeometricEndpoint_succ (Y base i : ℕ) :
    bfpsGeometricEndpoint Y base (i + 1) =
      bfpsGeometricEndpoint Y base i / base := by
  simp only [bfpsGeometricEndpoint, pow_succ, Nat.div_div_eq_div_mul]

/-- Geometric endpoints are antitone in the shell index.-/
theorem bfpsGeometricEndpoint_antitone (Y base : ℕ) :
    Antitone (bfpsGeometricEndpoint Y base) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [bfpsGeometricEndpoint_succ]
  exact Nat.div_le_self _ _

theorem bfpsGeometricEndpoint_le_of_le {Y base i j : ℕ} (hij : i ≤ j) :
    bfpsGeometricEndpoint Y base j ≤ bfpsGeometricEndpoint Y base i :=
  bfpsGeometricEndpoint_antitone Y base hij

/-- If the final endpoint is positive, every earlier endpoint is positive.-/
theorem one_le_bfpsGeometricEndpoint_of_le {Y base i K : ℕ}
    (hiK : i ≤ K) (hK : 1 ≤ bfpsGeometricEndpoint Y base K) :
    1 ≤ bfpsGeometricEndpoint Y base i :=
  hK.trans (bfpsGeometricEndpoint_le_of_le hiK)

/-- Before a positive terminal endpoint, consecutive shells are strict when `base ≥ 2`.-/
theorem bfpsGeometricEndpoint_succ_lt {Y base i K : ℕ}
    (hbase : 2 ≤ base) (hiK : i + 1 ≤ K)
    (hK : 1 ≤ bfpsGeometricEndpoint Y base K) :
    bfpsGeometricEndpoint Y base (i + 1) < bfpsGeometricEndpoint Y base i := by
  rw [bfpsGeometricEndpoint_succ]
  apply Nat.div_lt_self
  · exact Nat.zero_lt_of_lt <|
      one_le_bfpsGeometricEndpoint_of_le (Nat.le_trans (Nat.le_add_right i 1) hiK) hK
  · omega

/-- The `i`th exact largest-prime-factor shell.-/
def bfpsGeometricPrimeShell (X Y base i : ℕ) : Finset ℕ :=
  smoothPredecessorPrimeShell X
    (bfpsGeometricEndpoint Y base (i + 1))
    (bfpsGeometricEndpoint Y base i)

@[simp]
theorem mem_bfpsGeometricPrimeShell {X Y base i p : ℕ} :
    p ∈ bfpsGeometricPrimeShell X Y base i ↔
      p.Prime ∧ p ≤ X ∧
        IsSmooth (bfpsGeometricEndpoint Y base i) (p - 1) ∧
        bfpsGeometricEndpoint Y base (i + 1) < largestPrimeFactor (p - 1) := by
  simp [bfpsGeometricPrimeShell]

/-- Distinct geometric shells before a positive terminal endpoint are disjoint.-/
theorem bfpsGeometricPrimeShell_disjoint {X Y base i j K : ℕ}
    (hij : i < j) (hjK : j < K)
    (hK : 1 ≤ bfpsGeometricEndpoint Y base K) :
    Disjoint (bfpsGeometricPrimeShell X Y base i)
      (bfpsGeometricPrimeShell X Y base j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hiData := mem_bfpsGeometricPrimeShell.mp hpi
  have hjData := mem_bfpsGeometricPrimeShell.mp hpj
  have hjLower : 1 ≤ bfpsGeometricEndpoint Y base (j + 1) :=
    one_le_bfpsGeometricEndpoint_of_le (by omega) hK
  have hqUpper : largestPrimeFactor (p - 1) ≤
      bfpsGeometricEndpoint Y base j := by
    exact predecessorShellPrime_le hjLower hpj
  have hend : bfpsGeometricEndpoint Y base j ≤
      bfpsGeometricEndpoint Y base (i + 1) :=
    bfpsGeometricEndpoint_le_of_le (by omega)
  omega

/-! ## Exact telescoping -/

/-- Exact cardinal decomposition into the terminal smooth set and all preceding geometric shells.-/
theorem card_smoothPredecessorPrimeSet_eq_terminal_add_shells
    (X Y base K : ℕ) (hK : 1 ≤ bfpsGeometricEndpoint Y base K) :
    (smoothPredecessorPrimeSet X Y).card =
      (smoothPredecessorPrimeSet X (bfpsGeometricEndpoint Y base K)).card +
        ∑ i ∈ Finset.range K, (bfpsGeometricPrimeShell X Y base i).card := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hKprev : 1 ≤ bfpsGeometricEndpoint Y base K :=
        one_le_bfpsGeometricEndpoint_of_le (Nat.le_succ K) hK
      have hstep := card_smoothPredecessorPrimeSet_eq_add_shell
        (X := X)
        (lo := bfpsGeometricEndpoint Y base (K + 1))
        (hi := bfpsGeometricEndpoint Y base K)
        hK (bfpsGeometricEndpoint_le_of_le (Nat.le_succ K))
      rw [ih hKprev, hstep, Finset.sum_range_succ]
      simp only [bfpsGeometricPrimeShell]
      omega

/-! ## Discharging the weighted smooth-multiplier input -/

/-- The predecessor reduction's weighted sum is a sub-sum of the full finite smooth totient sum.-/
theorem bfpsWeightedSmoothMultiplierSum_le_finiteSmoothTotientWeightSum
    (X Y lo : ℕ) :
    bfpsWeightedSmoothMultiplierSum X Y lo ≤
      finiteSmoothTotientWeightSum Y (X / (lo + 1)) := by
  unfold bfpsWeightedSmoothMultiplierSum finiteSmoothTotientWeightSum
  calc
    (∑ m ∈ bfpsNontrivialSmoothMultiplierSet X Y lo,
        (m : ℝ) / (m.totient : ℝ)) =
        ∑ m ∈ bfpsNontrivialSmoothMultiplierSet X Y lo, totientWeight m := by
      rfl
    _ ≤ ∑ m ∈ finiteSmoothSet Y (X / (lo + 1)), totientWeight m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        have hmData := mem_bfpsNontrivialSmoothMultiplierSet.mp hm
        exact mem_finiteSmoothSet.mpr ⟨by omega, hmData.2.1, hmData.2.2⟩
      · intro m _ _
        unfold totientWeight
        positivity

/-- Fully explicit finite majorant supplied by `BFPSTotientWeight`.-/
def bfpsFiniteTotientWeightMajorant (X Y lo : ℕ) : ℝ :=
  mertensProduct Y * finiteSmoothCount Y (X / (lo + 1))

theorem bfpsWeightedSmoothMultiplierSum_le_finiteMajorant (X Y lo : ℕ) :
    bfpsWeightedSmoothMultiplierSum X Y lo ≤
      bfpsFiniteTotientWeightMajorant X Y lo := by
  exact (bfpsWeightedSmoothMultiplierSum_le_finiteSmoothTotientWeightSum X Y lo).trans
    (finiteSmoothTotientWeightSum_le Y (X / (lo + 1)))

/-- Thus the formerly abstract weighted-multiplier input is now unconditional.-/
theorem hasBFPSWeightedSmoothMultiplierBound_finite :
    HasBFPSWeightedSmoothMultiplierBound bfpsFiniteTotientWeightMajorant := by
  intro X Y lo
  exact bfpsWeightedSmoothMultiplierSum_le_finiteMajorant X Y lo

/-- Explicit logarithmic version of the finite weighted majorant.-/
def bfpsLogSmoothMultiplierMajorant (X Y lo : ℕ) : ℝ :=
  (Real.exp (4 * Real.log 4) * (1 + Real.log Y)) *
    finiteSmoothCount Y (X / (lo + 1))

theorem bfpsWeightedSmoothMultiplierSum_le_logMajorant
    {X Y lo : ℕ} (hY : 3 ≤ Y) :
    bfpsWeightedSmoothMultiplierSum X Y lo ≤
      bfpsLogSmoothMultiplierMajorant X Y lo := by
  exact (bfpsWeightedSmoothMultiplierSum_le_finiteSmoothTotientWeightSum X Y lo).trans
    (finiteSmoothTotientWeightSum_le_log hY)

/-! ## Terminal census and shell majorant sums -/

/-- Subtracting one injects predecessor primes into the corresponding finite smooth set.-/
theorem card_smoothPredecessorPrimeSet_le_finiteSmoothCount (X Y : ℕ) :
    (smoothPredecessorPrimeSet X Y).card ≤ finiteSmoothCount Y X := by
  unfold finiteSmoothCount
  apply Finset.card_le_card_of_injOn (fun p ↦ p - 1)
  · intro p hp
    have hpData := mem_smoothPredecessorPrimeSet.mp hp
    exact mem_finiteSmoothSet.mpr
      ⟨Nat.sub_pos_of_lt hpData.1.one_lt,
        (Nat.sub_le p 1).trans hpData.2.1, hpData.2.2⟩
  · intro p hp q hq hpq
    have hpPrime := (mem_smoothPredecessorPrimeSet.mp hp).1
    have hqPrime := (mem_smoothPredecessorPrimeSet.mp hq).1
    change p - 1 = q - 1 at hpq
    calc
      p = (p - 1) + 1 := (Nat.sub_add_cancel hpPrime.one_le).symm
      _ = (q - 1) + 1 := congrArg (fun n ↦ n + 1) hpq
      _ = q := Nat.sub_add_cancel hqPrime.one_le

/-- Exact finite Mertens-product mass accumulated over the geometric shells.-/
def bfpsGeometricFiniteMajorantSum (X Y base K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range K,
    bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
      bfpsFiniteTotientWeightMajorant X
        (bfpsGeometricEndpoint Y base i)
        (bfpsGeometricEndpoint Y base (i + 1))

/-- The completely explicit logarithmic relaxation of the geometric shell mass.-/
def bfpsGeometricLogMajorantSum (X Y base K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range K,
    bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
      bfpsLogSmoothMultiplierMajorant X
        (bfpsGeometricEndpoint Y base i)
        (bfpsGeometricEndpoint Y base (i + 1))

/-- A single geometric shell, with the smooth multiplier input discharged by the exact finite Mertens product.-/
theorem card_bfpsGeometricPrimeShell_cast_le_finiteMajorant
    {X Y base i K : ℕ} {C : ℝ}
    (hbase : 2 ≤ base) (hiK : i < K)
    (hK : 3 ≤ bfpsGeometricEndpoint Y base K) (hC : 0 ≤ C)
    (hsieve : HasBFPSTwoAffineSieveBound C) :
    ((bfpsGeometricPrimeShell X Y base i).card : ℝ) ≤
      1 + C * bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
        bfpsFiniteTotientWeightMajorant X
          (bfpsGeometricEndpoint Y base i)
          (bfpsGeometricEndpoint Y base (i + 1)) := by
  have hterminal : 1 ≤ bfpsGeometricEndpoint Y base K := by omega
  have hlo : 1 ≤ bfpsGeometricEndpoint Y base (i + 1) :=
    one_le_bfpsGeometricEndpoint_of_le (by omega) hterminal
  have hlohi : bfpsGeometricEndpoint Y base (i + 1) <
      bfpsGeometricEndpoint Y base i :=
    bfpsGeometricEndpoint_succ_lt hbase (by omega) hterminal
  have hhi : 3 ≤ bfpsGeometricEndpoint Y base i :=
    hK.trans (bfpsGeometricEndpoint_le_of_le (by omega))
  exact card_smoothPredecessorPrimeShell_cast_le_majorant
    hlo hlohi hhi hC hsieve hasBFPSWeightedSmoothMultiplierBound_finite

/-- A single geometric shell with the explicit logarithmic smooth-multiplier majorant.-/
theorem card_bfpsGeometricPrimeShell_cast_le_logMajorant
    {X Y base i K : ℕ} {C : ℝ}
    (hbase : 2 ≤ base) (hiK : i < K)
    (hK : 3 ≤ bfpsGeometricEndpoint Y base K) (hC : 0 ≤ C)
    (hsieve : HasBFPSTwoAffineSieveBound C) :
    ((bfpsGeometricPrimeShell X Y base i).card : ℝ) ≤
      1 + C * bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
        bfpsLogSmoothMultiplierMajorant X
          (bfpsGeometricEndpoint Y base i)
          (bfpsGeometricEndpoint Y base (i + 1)) := by
  have hterminal : 1 ≤ bfpsGeometricEndpoint Y base K := by omega
  have hlo : 1 ≤ bfpsGeometricEndpoint Y base (i + 1) :=
    one_le_bfpsGeometricEndpoint_of_le (by omega) hterminal
  have hlohi : bfpsGeometricEndpoint Y base (i + 1) <
      bfpsGeometricEndpoint Y base i :=
    bfpsGeometricEndpoint_succ_lt hbase (by omega) hterminal
  have hhi : 3 ≤ bfpsGeometricEndpoint Y base i :=
    hK.trans (bfpsGeometricEndpoint_le_of_le (by omega))
  calc
    ((bfpsGeometricPrimeShell X Y base i).card : ℝ) ≤
        1 + C * bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
          bfpsWeightedSmoothMultiplierSum X (bfpsGeometricEndpoint Y base i)
            (bfpsGeometricEndpoint Y base (i + 1)) :=
      card_smoothPredecessorPrimeShell_cast_le_weighted hlo hlohi hhi hsieve
    _ ≤ 1 + C * bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
        bfpsLogSmoothMultiplierMajorant X (bfpsGeometricEndpoint Y base i)
          (bfpsGeometricEndpoint Y base (i + 1)) := by
      exact add_le_add (le_refl 1) <|
        mul_le_mul_of_nonneg_left (bfpsWeightedSmoothMultiplierSum_le_logMajorant hhi)
          (mul_nonneg hC (bfpsLogSquaredScale_nonneg _))

/-! ## Global finite BFPS reductions -/

/-- Strongest unconditional finite shell summation available after supplying only the genuinely two-affine sieve estimate.-/
theorem card_smoothPredecessorPrimeSet_cast_le_geometricFiniteMajorant
    {X Y base K : ℕ} {C : ℝ}
    (hbase : 2 ≤ base) (hK : 3 ≤ bfpsGeometricEndpoint Y base K)
    (hC : 0 ≤ C) (hsieve : HasBFPSTwoAffineSieveBound C) :
    ((smoothPredecessorPrimeSet X Y).card : ℝ) ≤
      (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) + K +
        C * bfpsGeometricFiniteMajorantSum X Y base K := by
  have hterminal : 1 ≤ bfpsGeometricEndpoint Y base K := by omega
  have hdecomp := card_smoothPredecessorPrimeSet_eq_terminal_add_shells X Y base K hterminal
  have hdecompReal : ((smoothPredecessorPrimeSet X Y).card : ℝ) =
      ((smoothPredecessorPrimeSet X (bfpsGeometricEndpoint Y base K)).card : ℝ) +
        ∑ i ∈ Finset.range K, ((bfpsGeometricPrimeShell X Y base i).card : ℝ) := by
    exact_mod_cast hdecomp
  rw [hdecompReal]
  calc
    ((smoothPredecessorPrimeSet X (bfpsGeometricEndpoint Y base K)).card : ℝ) +
          ∑ i ∈ Finset.range K, ((bfpsGeometricPrimeShell X Y base i).card : ℝ) ≤
        (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) +
          ∑ i ∈ Finset.range K,
            (1 + C * bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
              bfpsFiniteTotientWeightMajorant X (bfpsGeometricEndpoint Y base i)
                (bfpsGeometricEndpoint Y base (i + 1))) := by
      apply add_le_add
      · exact_mod_cast card_smoothPredecessorPrimeSet_le_finiteSmoothCount X
          (bfpsGeometricEndpoint Y base K)
      · apply Finset.sum_le_sum
        intro i hi
        exact card_bfpsGeometricPrimeShell_cast_le_finiteMajorant
          hbase (Finset.mem_range.mp hi) hK hC hsieve
    _ = (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) + K +
        C * bfpsGeometricFiniteMajorantSum X Y base K := by
      rw [bfpsGeometricFiniteMajorantSum, Finset.sum_add_distrib]
      simp [Finset.mul_sum, mul_assoc]
      ring

/-- Logarithmic, constant-only relaxation of the global finite BFPS shell reduction.-/
theorem card_smoothPredecessorPrimeSet_cast_le_geometricLogMajorant
    {X Y base K : ℕ} {C : ℝ}
    (hbase : 2 ≤ base) (hK : 3 ≤ bfpsGeometricEndpoint Y base K)
    (hC : 0 ≤ C) (hsieve : HasBFPSTwoAffineSieveBound C) :
    ((smoothPredecessorPrimeSet X Y).card : ℝ) ≤
      (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) + K +
        C * bfpsGeometricLogMajorantSum X Y base K := by
  have hterminal : 1 ≤ bfpsGeometricEndpoint Y base K := by omega
  have hdecomp := card_smoothPredecessorPrimeSet_eq_terminal_add_shells X Y base K hterminal
  have hdecompReal : ((smoothPredecessorPrimeSet X Y).card : ℝ) =
      ((smoothPredecessorPrimeSet X (bfpsGeometricEndpoint Y base K)).card : ℝ) +
        ∑ i ∈ Finset.range K, ((bfpsGeometricPrimeShell X Y base i).card : ℝ) := by
    exact_mod_cast hdecomp
  rw [hdecompReal]
  calc
    ((smoothPredecessorPrimeSet X (bfpsGeometricEndpoint Y base K)).card : ℝ) +
          ∑ i ∈ Finset.range K, ((bfpsGeometricPrimeShell X Y base i).card : ℝ) ≤
        (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) +
          ∑ i ∈ Finset.range K,
            (1 + C * bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
              bfpsLogSmoothMultiplierMajorant X (bfpsGeometricEndpoint Y base i)
                (bfpsGeometricEndpoint Y base (i + 1))) := by
      apply add_le_add
      · exact_mod_cast card_smoothPredecessorPrimeSet_le_finiteSmoothCount X
          (bfpsGeometricEndpoint Y base K)
      · apply Finset.sum_le_sum
        intro i hi
        exact card_bfpsGeometricPrimeShell_cast_le_logMajorant
          hbase (Finset.mem_range.mp hi) hK hC hsieve
    _ = (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) + K +
        C * bfpsGeometricLogMajorantSum X Y base K := by
      rw [bfpsGeometricLogMajorantSum, Finset.sum_add_distrib]
      simp [Finset.mul_sum, mul_assoc]
      ring

/-- The one genuinely smooth-number analytic input left after exact shell summation: compress the terminal smooth census and explicit logarithmic shell mass into a chosen global bound.-/
def HasBFPSHildebrandGeometricShellBound
    (bound : ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ X Y base K, 2 ≤ base → 3 ≤ bfpsGeometricEndpoint Y base K →
    (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) +
      bfpsGeometricLogMajorantSum X Y base K ≤ bound X Y base K

/-- Finite BFPS Lemma 2.2 reduction: once a two-affine sieve constant and a named Dickman--Hildebrand compression bound are supplied, the global predecessor-prime count follows.-/
theorem card_smoothPredecessorPrimeSet_cast_le_hildebrandBound
    {X Y base K : ℕ} {C : ℝ}
    {bound : ℕ → ℕ → ℕ → ℕ → ℝ}
    (hbase : 2 ≤ base) (hK : 3 ≤ bfpsGeometricEndpoint Y base K)
    (hC : 1 ≤ C) (hsieve : HasBFPSTwoAffineSieveBound C)
    (hHildebrand : HasBFPSHildebrandGeometricShellBound bound) :
    ((smoothPredecessorPrimeSet X Y).card : ℝ) ≤
      K + C * bound X Y base K := by
  have hglobal := card_smoothPredecessorPrimeSet_cast_le_geometricLogMajorant
    (X := X) hbase hK (by positivity : 0 ≤ C) hsieve
  have hmass := hHildebrand X Y base K hbase hK
  have hcount : 0 ≤ (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) :=
    Nat.cast_nonneg _
  calc
    ((smoothPredecessorPrimeSet X Y).card : ℝ) ≤
        (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) + K +
          C * bfpsGeometricLogMajorantSum X Y base K := hglobal
    _ ≤ K + C *
        ((finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) +
          bfpsGeometricLogMajorantSum X Y base K) := by
      nlinarith
    _ ≤ K + C * bound X Y base K := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hmass (by positivity)) K

end

end RankAmplification
