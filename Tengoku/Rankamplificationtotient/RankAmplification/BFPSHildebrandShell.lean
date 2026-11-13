import Tengoku.Rankamplificationtotient.RankAmplification.BFPSShellSummation
import Tengoku.Seed.Analysis.Complex.ExponentialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite Hildebrand input for BFPS shell summation Pomerance--Shparlinski split primes with smooth predecessor into the shells `(Y / e, Y]`, apply a two-affine sieve, insert a uniform smooth-number estimate, and sum a decreasing logarithmic kernel. -/

namespace RankAmplification

open Finset
open scoped BigOperators

noncomputable section

/-! ## Pointwise smooth densities -/

/-- The multiplier cutoff in geometric shell `i`.-/
def bfpsShellMultiplierCutoff (X Y base i : ℕ) : ℕ :=
  X / (bfpsGeometricEndpoint Y base (i + 1) + 1)

/-- The explicit full-Range-Rankin density, including its checked prime-sum error.-/
def bfpsFullRankinSmoothDensity (R H : ℕ) : ℝ :=
  Real.exp (-rankinU H R * Real.log (rankinU H R) + fullPaperDivisorError R H)

/--
@isnad1 id=lt.0h2v.s4.d8e5985a6baa from=translated src=- shape=5ffe46ab vocab=1425a07e
-/
theorem bfpsFullRankinSmoothDensity_pos (R H : ℕ) :
    0 < bfpsFullRankinSmoothDensity R H := by
  exact Real.exp_pos _

/--
@isnad1 id=le.4h2v.s6.23322025a87d from=translated src=- shape=16c5907b vocab=9c86eff6
-/
theorem finiteSmoothCount_le_fullRankinDensity {R H : ℕ}
    (hH : 0 < H) (hR : 2 ≤ R) (hu : 1 < rankinU H R)
    (huSqrt : rankinU H R ≤ Real.sqrt R) :
    (finiteSmoothCount R H : ℝ) ≤
      H * bfpsFullRankinSmoothDensity R H := by
  exact finiteSmoothCount_le_full_paper_error hH hR hu huSqrt

/-- The elementary all-range fallback `Ψ(H,R) ≤ H`.
@isnad1 id=le.0h2v.s3.9c4d0e24342a from=translated src=- shape=bf83e09e vocab=a73add30
-/
theorem finiteSmoothCount_le_cutoff (R H : ℕ) :
    finiteSmoothCount R H ≤ H := by
  rw [finiteSmoothCount]
  calc
    (finiteSmoothSet R H).card ≤ (Finset.Icc 1 H).card := by
      apply Finset.card_le_card
      intro m hm
      exact Finset.mem_Icc.mpr
        ⟨(mem_finiteSmoothSet.mp hm).1, (mem_finiteSmoothSet.mp hm).2.1⟩
    _ = H := by simp

/-! ## A uniform hybrid Rankin envelope -/

/-- All terminal and shell smooth counts lie in the checked full Rankin range.-/
def BFPSFullRankinShellAdmissible (X Y base K : ℕ) : Prop :=
  0 < X ∧
    1 < rankinU X (bfpsGeometricEndpoint Y base K) ∧
    rankinU X (bfpsGeometricEndpoint Y base K) ≤
      Real.sqrt (bfpsGeometricEndpoint Y base K) ∧
    ∀ i < K,
      0 < bfpsShellMultiplierCutoff X Y base i ∧
      1 < rankinU (bfpsShellMultiplierCutoff X Y base i)
        (bfpsGeometricEndpoint Y base i) ∧
      rankinU (bfpsShellMultiplierCutoff X Y base i)
          (bfpsGeometricEndpoint Y base i) ≤
        Real.sqrt (bfpsGeometricEndpoint Y base i)

/-- A single density dominating the terminal smooth census and every geometric-shell multiplier census.-/
def bfpsHybridUniformShellDensity (X Y base K : ℕ) : ℝ :=
  by
    classical
    exact if BFPSFullRankinShellAdmissible X Y base K then
      bfpsFullRankinSmoothDensity (bfpsGeometricEndpoint Y base K) X +
        ∑ i ∈ Finset.range K,
          bfpsFullRankinSmoothDensity (bfpsGeometricEndpoint Y base i)
            (bfpsShellMultiplierCutoff X Y base i)
    else 1

/--
@isnad1 id=le.0h4v.s4.9470fb1f8a2b from=translated src=- shape=f0c23793 vocab=f9cf294a
-/
theorem bfpsHybridUniformShellDensity_nonneg (X Y base K : ℕ) :
    0 ≤ bfpsHybridUniformShellDensity X Y base K := by
  unfold bfpsHybridUniformShellDensity
  split_ifs
  · exact add_nonneg (bfpsFullRankinSmoothDensity_pos _ _).le <|
      Finset.sum_nonneg fun i _ ↦ (bfpsFullRankinSmoothDensity_pos
        (bfpsGeometricEndpoint Y base i) (bfpsShellMultiplierCutoff X Y base i)).le
  · norm_num

/--
@isnad1 id=eq.1h4v.s5.93c2c879ebf6 from=translated src=- shape=d8b94c9e vocab=a1ab22d2
-/
theorem bfpsHybridUniformShellDensity_eq_rankinSum {X Y base K : ℕ}
    (h : BFPSFullRankinShellAdmissible X Y base K) :
    bfpsHybridUniformShellDensity X Y base K =
      bfpsFullRankinSmoothDensity (bfpsGeometricEndpoint Y base K) X +
        ∑ i ∈ Finset.range K,
          bfpsFullRankinSmoothDensity (bfpsGeometricEndpoint Y base i)
            (bfpsShellMultiplierCutoff X Y base i) := by
  rw [bfpsHybridUniformShellDensity, ite_eq_left h]

/-- The minimal uniform smooth-number input in the Pomerance--Shparlinski shell proof.-/
def HasBFPSTerminalHildebrandSmoothDensity
    (density : ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ X Y base K, 2 ≤ base → 3 ≤ bfpsGeometricEndpoint Y base K →
    0 ≤ density X Y base K ∧
    (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) ≤
      X * density X Y base K ∧
    ∀ i < K,
      (finiteSmoothCount (bfpsGeometricEndpoint Y base i)
          (bfpsShellMultiplierCutoff X Y base i) : ℝ) ≤
        bfpsShellMultiplierCutoff X Y base i * density X Y base K

/-- The hybrid Rankin-or-trivial density is an unconditional instance of the uniform input.
@isnad1 id=hasbfpst.0h0v.s1.5580d2f22eee from=translated src=- shape=49959d42 vocab=438925c5
-/
theorem hasBFPSTerminalHildebrandSmoothDensity_hybrid :
    HasBFPSTerminalHildebrandSmoothDensity bfpsHybridUniformShellDensity := by
  intro X Y base K hbase hK
  refine ⟨bfpsHybridUniformShellDensity_nonneg X Y base K, ?_⟩
  by_cases hadmissible : BFPSFullRankinShellAdmissible X Y base K
  · have hterminalR : 2 ≤ bfpsGeometricEndpoint Y base K := by omega
    have hterminal := finiteSmoothCount_le_fullRankinDensity
      hadmissible.1 hterminalR hadmissible.2.1 hadmissible.2.2.1
    have hterminalDensity :
        bfpsFullRankinSmoothDensity (bfpsGeometricEndpoint Y base K) X ≤
          bfpsHybridUniformShellDensity X Y base K := by
      rw [bfpsHybridUniformShellDensity, ite_eq_left hadmissible]
      exact le_add_of_nonneg_right <| Finset.sum_nonneg fun i _ ↦
        (bfpsFullRankinSmoothDensity_pos (bfpsGeometricEndpoint Y base i)
          (bfpsShellMultiplierCutoff X Y base i)).le
    constructor
    · exact hterminal.trans <|
        mul_le_mul_of_nonneg_left hterminalDensity (by positivity)
    · intro i hiK
      have hiR : 2 ≤ bfpsGeometricEndpoint Y base i := by
        have := hK.trans (bfpsGeometricEndpoint_le_of_le
          (Y := Y) (base := base) (i := i) (j := K) (by omega))
        omega
      have hiAdmissible := hadmissible.2.2.2 i hiK
      have hiSmooth := finiteSmoothCount_le_fullRankinDensity
        hiAdmissible.1 hiR hiAdmissible.2.1 hiAdmissible.2.2
      have hiDensity :
          bfpsFullRankinSmoothDensity (bfpsGeometricEndpoint Y base i)
              (bfpsShellMultiplierCutoff X Y base i) ≤
            bfpsHybridUniformShellDensity X Y base K := by
        rw [bfpsHybridUniformShellDensity, ite_eq_left hadmissible]
        have hsingle := Finset.single_le_sum
          (fun j _ ↦ (bfpsFullRankinSmoothDensity_pos
            (bfpsGeometricEndpoint Y base j)
            (bfpsShellMultiplierCutoff X Y base j)).le)
          (Finset.mem_range.mpr hiK)
        exact hsingle.trans <|
          le_add_of_nonneg_left (bfpsFullRankinSmoothDensity_pos _ _).le
      exact hiSmooth.trans <|
        mul_le_mul_of_nonneg_left hiDensity (by positivity)
  · rw [bfpsHybridUniformShellDensity, ite_eq_right hadmissible]
    constructor
    · simpa using (show
          (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) ≤ X by
        exact_mod_cast finiteSmoothCount_le_cutoff
          (bfpsGeometricEndpoint Y base K) X)
    · intro i hiK
      simp only [mul_one]
      exact_mod_cast finiteSmoothCount_le_cutoff
        (bfpsGeometricEndpoint Y base i) (bfpsShellMultiplierCutoff X Y base i)

/-! ## The decreasing shell kernel -/

/-- The logarithmic kernel left after the sieve scale, Mertens factor, and shell-width cancellation.-/
def bfpsHildebrandLogKernel (R : ℕ) : ℝ :=
  (1 + Real.log R) / (Real.log R) ^ 2

/--
@isnad1 id=le.0h1v.s3.00268aafc01d from=translated src=- shape=b9369acb vocab=0494234f
-/
theorem bfpsHildebrandLogKernel_nonneg (R : ℕ) :
    0 ≤ bfpsHildebrandLogKernel R := by
  unfold bfpsHildebrandLogKernel
  positivity

/--
@isnad1 id=lt.1h1v.s4.9822a681f875 from=translated src=- shape=998257d8 vocab=d08708e8
-/
theorem one_lt_log_nat {R : ℕ} (hR : 3 ≤ R) :
    1 < Real.log R := by
  have hexp : Real.exp 1 < (R : ℝ) :=
    Real.exp_one_lt_three.trans_le (by exact_mod_cast hR)
  have hRpos : 0 < (R : ℝ) := by positivity
  rw [← Real.exp_log hRpos] at hexp
  exact Real.exp_lt_exp.mp hexp

/-- The shell kernel is decreasing on the integer range `R ≥ 3`.
@isnad1 id=le.2h2v.s4.a90d5f59a49e from=translated src=- shape=9a8d8d4a vocab=0494234f
-/
theorem bfpsHildebrandLogKernel_antitone {R S : ℕ} (hR : 3 ≤ R) (hRS : R ≤ S) :
    bfpsHildebrandLogKernel S ≤ bfpsHildebrandLogKernel R := by
  have ha : 1 < Real.log R := one_lt_log_nat hR
  have hab : Real.log R ≤ Real.log S :=
    Real.log_le_log (by positivity) (by exact_mod_cast hRS)
  unfold bfpsHildebrandLogKernel
  apply (div_le_div_iff₀ (sq_pos_of_pos (zero_lt_one.trans <| ha.trans_le hab))
    (sq_pos_of_pos (zero_lt_one.trans ha))).2
  have hfactor : 0 ≤ (Real.log S - Real.log R) *
      (Real.log R + Real.log S + Real.log R * Real.log S) := by
    positivity
  nlinarith

/-! ## Exact shell-width cancellation -/

/-- Natural division loses no more than one geometric block.
@isnad1 id=le.1h4v.s5.ad28c4765846 from=translated src=- shape=af0afc57 vocab=53c79405
-/
theorem bfpsGeometricEndpoint_mul_shellMultiplierCutoff_le
    {X Y base i : ℕ} (hbase : 1 ≤ base) :
    bfpsGeometricEndpoint Y base i * bfpsShellMultiplierCutoff X Y base i ≤
      base * X := by
  have hbasePos : 0 < base := Nat.zero_lt_of_lt hbase
  have hwidth : bfpsGeometricEndpoint Y base i ≤
      base * (bfpsGeometricEndpoint Y base (i + 1) + 1) := by
    rw [bfpsGeometricEndpoint_succ]
    have hlt : bfpsGeometricEndpoint Y base i <
        (bfpsGeometricEndpoint Y base i / base + 1) * base :=
      (Nat.div_lt_iff_lt_mul hbasePos).mp
        (Nat.lt_succ_self (bfpsGeometricEndpoint Y base i / base))
    simpa [Nat.mul_comm] using hlt.le
  calc
    bfpsGeometricEndpoint Y base i * bfpsShellMultiplierCutoff X Y base i ≤
        (base * (bfpsGeometricEndpoint Y base (i + 1) + 1)) *
          bfpsShellMultiplierCutoff X Y base i :=
      Nat.mul_le_mul_right _ hwidth
    _ = base * (bfpsShellMultiplierCutoff X Y base i *
        (bfpsGeometricEndpoint Y base (i + 1) + 1)) := by
      ac_rfl
    _ ≤ base * X := by
      apply Nat.mul_le_mul_left
      exact Nat.div_mul_le_self X (bfpsGeometricEndpoint Y base (i + 1) + 1)

/-- One logarithmic shell term after inserting a common smooth-number density.
@isnad1 id=le.5h6v.s7.f365c7aaeede from=translated src=- shape=08c18fa6 vocab=c419c428
-/
theorem bfpsGeometricLogMajorantTerm_le_uniformDensity
    {X Y base K i : ℕ} {density : ℝ}
    (hbase : 2 ≤ base) (hiK : i < K)
    (hK : 3 ≤ bfpsGeometricEndpoint Y base K) (hdensity : 0 ≤ density)
    (hsmooth :
      (finiteSmoothCount (bfpsGeometricEndpoint Y base i)
          (bfpsShellMultiplierCutoff X Y base i) : ℝ) ≤
        bfpsShellMultiplierCutoff X Y base i * density) :
    bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
        bfpsLogSmoothMultiplierMajorant X (bfpsGeometricEndpoint Y base i)
          (bfpsGeometricEndpoint Y base (i + 1)) ≤
      Real.exp (4 * Real.log 4) * (base : ℝ) * X * density *
        bfpsHildebrandLogKernel (bfpsGeometricEndpoint Y base K) := by
  have hiTerminal : bfpsGeometricEndpoint Y base K ≤
      bfpsGeometricEndpoint Y base i :=
    bfpsGeometricEndpoint_le_of_le (by omega)
  have hiLower : 3 ≤ bfpsGeometricEndpoint Y base i := hK.trans hiTerminal
  have hproductNat := bfpsGeometricEndpoint_mul_shellMultiplierCutoff_le
    (X := X) (Y := Y) (base := base) (i := i) (by omega)
  have hproductReal :
      (bfpsGeometricEndpoint Y base i : ℝ) *
          bfpsShellMultiplierCutoff X Y base i ≤ (base : ℝ) * X := by
    exact_mod_cast hproductNat
  have hkernel := bfpsHildebrandLogKernel_antitone hK hiTerminal
  have hscale : 0 ≤ bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) :=
    bfpsLogSquaredScale_nonneg _
  have hlogFactor : 0 ≤
      Real.exp (4 * Real.log 4) *
        (1 + Real.log (bfpsGeometricEndpoint Y base i)) := by
    positivity
  calc
    bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
        bfpsLogSmoothMultiplierMajorant X (bfpsGeometricEndpoint Y base i)
          (bfpsGeometricEndpoint Y base (i + 1)) =
        bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
          ((Real.exp (4 * Real.log 4) *
            (1 + Real.log (bfpsGeometricEndpoint Y base i))) *
            finiteSmoothCount (bfpsGeometricEndpoint Y base i)
              (bfpsShellMultiplierCutoff X Y base i)) := by
      rw [bfpsLogSmoothMultiplierMajorant, bfpsShellMultiplierCutoff]
    _ ≤ bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
          ((Real.exp (4 * Real.log 4) *
            (1 + Real.log (bfpsGeometricEndpoint Y base i))) *
            (bfpsShellMultiplierCutoff X Y base i * density)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsmooth hlogFactor) hscale
    _ = Real.exp (4 * Real.log 4) *
          ((bfpsGeometricEndpoint Y base i : ℝ) *
            bfpsShellMultiplierCutoff X Y base i) * density *
          bfpsHildebrandLogKernel (bfpsGeometricEndpoint Y base i) := by
      unfold bfpsLogSquaredScale AffinePrimePair.logSquaredScale
        bfpsHildebrandLogKernel
      ring
    _ ≤ Real.exp (4 * Real.log 4) * ((base : ℝ) * X) * density *
          bfpsHildebrandLogKernel (bfpsGeometricEndpoint Y base i) := by
      gcongr
      exact bfpsHildebrandLogKernel_nonneg _
    _ ≤ Real.exp (4 * Real.log 4) * ((base : ℝ) * X) * density *
          bfpsHildebrandLogKernel (bfpsGeometricEndpoint Y base K) := by
      gcongr
    _ = Real.exp (4 * Real.log 4) * (base : ℝ) * X * density *
          bfpsHildebrandLogKernel (bfpsGeometricEndpoint Y base K) := by
      ring

/-! ## Constructor for the remaining shell proposition -/

/-- Closed geometric-shell bound produced by a common terminal/shell smooth density.-/
def bfpsHildebrandGeometricClosedBound
    (density : ℕ → ℕ → ℕ → ℕ → ℝ)
    (X Y base K : ℕ) : ℝ :=
  (X : ℝ) * density X Y base K *
    (1 + (K : ℝ) * Real.exp (4 * Real.log 4) * (base : ℝ) *
      bfpsHildebrandLogKernel (bfpsGeometricEndpoint Y base K))

/-- The strongest closed finite constructor obtainable from the exact common-density input.
@isnad1 id=hasbfpsh.1h1v.s4.14778b49e259 from=translated src=- shape=a916b203 vocab=57948077
-/
theorem hasBFPSHildebrandGeometricShellBound_of_uniformDensity
    {density : ℕ → ℕ → ℕ → ℕ → ℝ}
    (hsmooth : HasBFPSTerminalHildebrandSmoothDensity density) :
    HasBFPSHildebrandGeometricShellBound
      (bfpsHildebrandGeometricClosedBound density) := by
  intro X Y base K hbase hK
  have hdata := hsmooth X Y base K hbase hK
  rw [bfpsGeometricLogMajorantSum]
  calc
    (finiteSmoothCount (bfpsGeometricEndpoint Y base K) X : ℝ) +
          ∑ i ∈ Finset.range K,
            bfpsLogSquaredScale (bfpsGeometricEndpoint Y base i) *
              bfpsLogSmoothMultiplierMajorant X (bfpsGeometricEndpoint Y base i)
                (bfpsGeometricEndpoint Y base (i + 1)) ≤
        (X : ℝ) * density X Y base K +
          ∑ _i ∈ Finset.range K,
            Real.exp (4 * Real.log 4) * (base : ℝ) * X *
              density X Y base K *
                bfpsHildebrandLogKernel (bfpsGeometricEndpoint Y base K) := by
      apply add_le_add hdata.2.1
      apply Finset.sum_le_sum
      intro i hi
      exact bfpsGeometricLogMajorantTerm_le_uniformDensity
        hbase (Finset.mem_range.mp hi) hK hdata.1 (hdata.2.2 i (Finset.mem_range.mp hi))
    _ = bfpsHildebrandGeometricClosedBound density X Y base K := by
      simp [bfpsHildebrandGeometricClosedBound]
      ring

/-- The fully checked Rankin-or-trivial global bound, with no Hildebrand or Dickman premise.-/
def bfpsHybridHildebrandGeometricBound (X Y base K : ℕ) : ℝ :=
  bfpsHildebrandGeometricClosedBound bfpsHybridUniformShellDensity X Y base K

/--
@isnad1 id=hasbfpsh.0h0v.s1.e7c733c0f3d3 from=translated src=- shape=49959d42 vocab=eb269829
-/
theorem hasBFPSHildebrandGeometricShellBound_hybrid :
    HasBFPSHildebrandGeometricShellBound bfpsHybridHildebrandGeometricBound := by
  exact hasBFPSHildebrandGeometricShellBound_of_uniformDensity
    hasBFPSTerminalHildebrandSmoothDensity_hybrid

/-- Explicit global BFPS predecessor-prime estimate obtained from the checked hybrid smooth density.
@isnad1 id=le.4h5v.s6.abf471ba0556 from=translated src=- shape=6ffb9c73 vocab=3eb61d96
-/
theorem card_smoothPredecessorPrimeSet_cast_le_hybridHildebrandBound
    {X Y base K : ℕ} {C : ℝ}
    (hbase : 2 ≤ base) (hK : 3 ≤ bfpsGeometricEndpoint Y base K)
    (hC : 1 ≤ C) (hsieve : HasBFPSTwoAffineSieveBound C) :
    ((smoothPredecessorPrimeSet X Y).card : ℝ) ≤
      K + C * bfpsHybridHildebrandGeometricBound X Y base K := by
  exact card_smoothPredecessorPrimeSet_cast_le_hildebrandBound
    hbase hK hC hsieve hasBFPSHildebrandGeometricShellBound_hybrid

end

end RankAmplification
