import Tengoku.Q1LeanVerification.Q1.RegularRepresentation
import Tengoku.Q1LeanVerification.Q1.FiniteNormBounds
import Tengoku.Q1LeanVerification.Q1.WordLength
import Tengoku.Q1LeanVerification.Q1.LogSRD

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The reduced norm growth function is built from the actual convolution
operators on the full complex ℓ² space. Suprema include the zero coefficient,
whose ratio is zero; the nonzero version is identified on nonempty balls. -/

noncomputable section

namespace Q1

variable {G : Type*} [Group G]

/-- Actual reduced regular norm divided by the counting-measure coefficient
ℓ² norm. Division by zero assigns the zero coefficient the value zero.-/
def reducedRatio (f : G →₀ ℂ) : ℝ :=
  ‖regularConvolution f‖ / coefficientL2Norm f

/-- All reduced norm ratios with support contained in the specified finite set.-/
def reducedRatios (B : Finset G) : Set ℝ :=
  {x | ∃ f : G →₀ ℂ, f.support ⊆ B ∧ reducedRatio f = x}

/-- The actual reduced-norm growth constant on a finite support set.-/
def reducedBallRho (B : Finset G) : ℝ := sSup (reducedRatios B)

/-- The same construction on the specified ambient length balls.-/
def reducedRho (L : LengthBall G) (r : ℕ) : ℝ := reducedBallRho (L.ball r)

/-- Finite-support Cauchy--Schwarz controls the actual convolution norm.
@isnad1 id=le.0h2v.s11.747c321b1e0c from=translated src=- shape=f14a329c vocab=3d2ea8ab
-/
theorem norm_regularConvolution_le_sqrt_card (f : G →₀ ℂ) :
    ‖regularConvolution f‖ ≤ Real.sqrt (f.support.card : ℝ) * coefficientL2Norm f := by
  have hn : 0 ≤ coefficientL2Norm f := norm_nonneg _
  calc
    ‖regularConvolution f‖ ≤ ∑ g ∈ f.support, ‖f g‖ := norm_regularConvolution_le f
    _ ≤ Real.sqrt (f.support.card : ℝ) * Real.sqrt (∑ g ∈ f.support, ‖f g‖ ^ 2) :=
      sum_norm_le_sqrt_card_mul_sqrt_sum f.support f
    _ = Real.sqrt (f.support.card : ℝ) * coefficientL2Norm f := by
      rw [← coefficientL2Norm_sq, Real.sqrt_sq hn]

/-- The ambient support set, rather than any intrinsic subgroup ball, controls
all ratios used to define rho.
@isnad1 id=le.1h3v.s5.74eda16d46fd from=translated src=- shape=8a89d61e vocab=6a4c89dc
-/
theorem reducedRatio_le_sqrt_card (B : Finset G) (f : G →₀ ℂ) (hf : f.support ⊆ B) :
    reducedRatio f ≤ Real.sqrt (B.card : ℝ) := by
  have hcard : (f.support.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card hf
  apply ratio_le_sqrt_card_of_norm_bound _ _ _ (norm_nonneg _)
  exact (norm_regularConvolution_le_sqrt_card f).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcard) (norm_nonneg _))

/--
@isnad1 id=bddabove.0h2v.s3.c944550255fa from=translated src=- shape=17969803 vocab=f265f406
-/
theorem reducedRatios_bddAbove (B : Finset G) : BddAbove (reducedRatios B) := by
  refine ⟨Real.sqrt (B.card : ℝ), ?_⟩
  rintro x ⟨f, hf, rfl⟩
  exact reducedRatio_le_sqrt_card B f hf

/--
@isnad1 id=nonempty.0h2v.s3.a4340ce44624 from=translated src=- shape=17969803 vocab=e5fb9cf7
-/
theorem reducedRatios_nonempty (B : Finset G) : (reducedRatios B).Nonempty :=
  ⟨reducedRatio 0, 0, by simp, rfl⟩

/--
@isnad1 id=le.0h2v.s4.321a36ee073f from=translated src=- shape=fb054a95 vocab=fac27b86
-/
theorem reducedRatio_nonneg (f : G →₀ ℂ) : 0 ≤ reducedRatio f :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/--
@isnad1 id=le.1h3v.s5.2056be880d06 from=translated src=- shape=5a33b3a7 vocab=fef7f28c
-/
theorem reducedRatio_le_rho (B : Finset G) (f : G →₀ ℂ) (hf : f.support ⊆ B) :
    reducedRatio f ≤ reducedBallRho B :=
  le_csSup (reducedRatios_bddAbove B) ⟨f, hf, rfl⟩

/--
@isnad1 id=le.0h2v.s4.af03eb4db097 from=translated src=- shape=38fc717e vocab=7d9e3596
-/
theorem reducedBallRho_nonneg (B : Finset G) : 0 ≤ reducedBallRho B :=
  (reducedRatio_nonneg 0).trans (reducedRatio_le_rho B 0 (by simp))

/--
@isnad1 id=le.0h2v.s4.5bc93c20d69f from=translated src=- shape=3d1a20af vocab=2b946366
-/
theorem reducedBallRho_le_sqrt_card (B : Finset G) :
    reducedBallRho B ≤ Real.sqrt (B.card : ℝ) := by
  apply csSup_le (reducedRatios_nonempty B)
  rintro x ⟨f, hf, rfl⟩
  exact reducedRatio_le_sqrt_card B f hf

/--
@isnad1 id=le.1h3v.s5.e45b302b39dd from=translated src=- shape=43044cdd vocab=7d9e3596
-/
theorem reducedBallRho_mono {A B : Finset G} (h : A ⊆ B) :
    reducedBallRho A ≤ reducedBallRho B := by
  apply csSup_le_csSup (reducedRatios_bddAbove B) (reducedRatios_nonempty A)
  rintro x ⟨f, hf, rfl⟩
  exact ⟨f, hf.trans h, rfl⟩

/--
@isnad1 id=eq.0h2v.s4.c5d776aa30ad from=translated src=- shape=44ceda02 vocab=b739b25a
-/
@[simp] theorem reducedRatio_single_one (g : G) :
    reducedRatio (Finsupp.single g (1 : ℂ)) = 1 := by
  simp [reducedRatio]

/--
@isnad1 id=le.1h2v.s4.329bae34178c from=translated src=- shape=7ec6a4bb vocab=e3f6673c
-/
theorem one_le_reducedBallRho (B : Finset G) (hB : B.Nonempty) :
    1 ≤ reducedBallRho B := by
  obtain ⟨g, hg⟩ := hB
  have hs : (Finsupp.single g (1 : ℂ)).support ⊆ B := by simpa using hg
  simpa using reducedRatio_le_rho B (Finsupp.single g (1 : ℂ)) hs

/-- The defining reduced-norm estimate, including the zero coefficient.
@isnad1 id=le.1h3v.s11.40f7ff802e7e from=translated src=- shape=d32ab3e2 vocab=d5e516d5
-/
theorem norm_regularConvolution_le_rho_mul (B : Finset G) (f : G →₀ ℂ)
    (hf : f.support ⊆ B) :
    ‖regularConvolution f‖ ≤ reducedBallRho B * coefficientL2Norm f := by
  by_cases hz : coefficientL2Norm f = 0
  · simpa [hz] using norm_regularConvolution_le_sqrt_card f
  · have hp : 0 < coefficientL2Norm f := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (div_le_iff₀ hp).mp (reducedRatio_le_rho B f hf)

/--
@isnad1 id=le.0h3v.s4.31ae6a5e5248 from=translated src=- shape=1a56e260 vocab=6313622c
-/
theorem one_le_reducedRho (L : LengthBall G) (r : ℕ) : 1 ≤ reducedRho L r := by
  apply one_le_reducedBallRho
  exact ⟨1, (L.mem_ball 1 r).mpr (by simp [L.length_one])⟩

/--
@isnad1 id=le.0h3v.s4.0560313bfa6c from=translated src=- shape=1a56e260 vocab=6313622c
-/
theorem reducedRho_nonneg (L : LengthBall G) (r : ℕ) : 0 ≤ reducedRho L r :=
  zero_le_one.trans (one_le_reducedRho L r)

/--
@isnad1 id=le.0h3v.s4.077b05884562 from=translated src=- shape=0e26ee41 vocab=a4ae2aa0
-/
theorem reducedRho_le_sqrt_card (L : LengthBall G) (r : ℕ) :
    reducedRho L r ≤ Real.sqrt ((L.ball r).card : ℝ) :=
  reducedBallRho_le_sqrt_card (L.ball r)

/--
@isnad1 id=monotone.0h2v.s4.d790c3042fc6 from=translated src=- shape=ffbea78d vocab=b4e2a824
-/
theorem reducedRho_monotone (L : LengthBall G) : Monotone (reducedRho L) := by
  intro r s hrs
  apply reducedBallRho_mono
  intro g hg
  exact (L.mem_ball g s).mpr (((L.mem_ball g r).mp hg).trans hrs)

/-- Polynomial rapid decay for the actual reduced-norm growth function.-/
def ReducedRD (L : LengthBall G) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d : ℝ, 0 ≤ d ∧
    ∀ r : ℕ, reducedRho L r ≤ C * (1 + (r : ℝ)) ^ d

/-- Ordinary sub-rapid decay for the actual reduced-norm growth function.-/
def ReducedSRD (L : LengthBall G) : Prop :=
  Filter.Tendsto (fun n : ℕ => Real.log (reducedRho L n) / (n : ℝ))
    Filter.atTop (nhds 0)

/--
@isnad1 id=iff.0h2v.s4.bf7342f983c9 from=translated src=- shape=1bc6754a vocab=30accc74
-/
theorem reducedSRD_iff_ordinarySRD (L : LengthBall G) :
    ReducedSRD L ↔ OrdinarySRD (reducedRho L) :=
  (ordinarySRD_iff_log_limit (reducedRho L) (one_le_reducedRho L)).symm

/--
@isnad1 id=reduceds.1h2v.s4.67617925161f from=translated src=- shape=93e860ac vocab=36b55fe9
-/
theorem ReducedRD.subrapid {L : LengthBall G} (h : ReducedRD L) : ReducedSRD L := by
  obtain ⟨C, _, d, _, hbound⟩ := h
  exact (reducedSRD_iff_ordinarySRD L).mpr
    (ordinarySRD_of_polynomial_bound (reducedRho L) C d hbound)

/-- The original nonzero-coefficient ratio set.-/
def nonzeroReducedRatios (B : Finset G) : Set ℝ :=
  {x | ∃ f : G →₀ ℂ, f ≠ 0 ∧ f.support ⊆ B ∧ reducedRatio f = x}

/--
@isnad1 id=le.0h2v.s4.86f7179aff5c from=translated src=- shape=140f7f7d vocab=3195a1a3
-/
theorem nonzeroReducedRatios_subset (B : Finset G) :
    nonzeroReducedRatios B ⊆ reducedRatios B := by
  rintro x ⟨f, _, hf, rfl⟩
  exact ⟨f, hf, rfl⟩

/--
@isnad1 id=bddabove.0h2v.s3.d4f3c1b07a9c from=translated src=- shape=17969803 vocab=c2effa02
-/
theorem nonzeroReducedRatios_bddAbove (B : Finset G) :
    BddAbove (nonzeroReducedRatios B) :=
  (reducedRatios_bddAbove B).mono (nonzeroReducedRatios_subset B)

/--
@isnad1 id=mem.1h2v.s4.cd8a98fd97f9 from=translated src=- shape=13a04217 vocab=c8992430
-/
theorem one_mem_nonzeroReducedRatios (B : Finset G) (hB : B.Nonempty) :
    1 ∈ nonzeroReducedRatios B := by
  obtain ⟨g, hg⟩ := hB
  refine ⟨Finsupp.single g 1, by simp, by simpa using hg, reducedRatio_single_one g⟩

/-- Including the zero coefficient does not change the exact original
nonzero-coefficient supremum on any nonempty ball.
@isnad1 id=eq.1h2v.s4.a0de3b5b8b4c from=translated src=- shape=4b75364a vocab=f2bf5eba
-/
theorem reducedBallRho_eq_sSup_nonzero (B : Finset G) (hB : B.Nonempty) :
    reducedBallRho B = sSup (nonzeroReducedRatios B) := by
  have hb := nonzeroReducedRatios_bddAbove B
  have h1 : 1 ≤ sSup (nonzeroReducedRatios B) :=
    le_csSup hb (one_mem_nonzeroReducedRatios B hB)
  apply le_antisymm
  · apply csSup_le (reducedRatios_nonempty B)
    rintro x ⟨f, hf, rfl⟩
    by_cases hz : f = 0
    · simpa [hz, reducedRatio] using zero_le_one.trans h1
    · exact le_csSup hb ⟨f, hz, hf, rfl⟩
  · exact csSup_le_csSup (reducedRatios_bddAbove B)
      ⟨1, one_mem_nonzeroReducedRatios B hB⟩ (nonzeroReducedRatios_subset B)

end Q1
