import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_CarrierPins
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open IsDedekindDomain NumberField Matrix MeasureTheory

open scoped ENNReal

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

variable {K : Type*} [NormedField K]

def topNormSq (g : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖g 0 0‖ ^ 2 + ‖g 0 1‖ ^ 2

def rowNormSq (g : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2

def localHeight (g : GL (Fin 2) K) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowNormSq (g : Matrix (Fin 2) (Fin 2) K)

def xWindowSq (g : GL (Fin 2) K) : ℝ :=
  topNormSq (g : Matrix (Fin 2) (Fin 2) K) / rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
    - localHeight g ^ 2

/--
@isnad1 id=eq.0h1v.s6.c97c1409e9dc from=translated src=- shape=25f4ccf3 vocab=31d031a6
-/
theorem rowNormSq_one : rowNormSq (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  unfold rowNormSq
  rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq]
  simp

/--
@isnad1 id=eq.0h1v.s7.4b431536916a from=translated src=- shape=694be4a8 vocab=e84c67d3
-/
theorem localHeight_one : localHeight (1 : GL (Fin 2) K) = 1 := by
  unfold localHeight
  rw [show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, rowNormSq_one,
    Matrix.det_one]
  simp

/--
@isnad1 id=eq.0h1v.s7.54baf3bc653b from=translated src=- shape=694be4a8 vocab=8eb12a87
-/
theorem xWindowSq_one : xWindowSq (1 : GL (Fin 2) K) = 0 := by
  unfold xWindowSq topNormSq
  rw [show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, rowNormSq_one,
    localHeight_one, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
  simp

variable (F : Type) [Field F] [NumberField F]

def archHeight (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ v : InfinitePlace F, localHeight (AdelicLevel.archComponent F v g) ^ v.mult

/--
@isnad1 id=eq.0h1v.s7.6905e829abd2 from=translated src=- shape=14eac179 vocab=83c3f413
-/
theorem archHeight_one : archHeight F (1 : GL (Fin 2) (InfiniteAdeleRing F)) = 1 := by
  unfold archHeight
  simp [map_one, localHeight_one]

def integralWindowedSiegelSet (c u : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | AdelicLevel.glFin (𝓞 F) F g ∈ AdelicLevel.finiteIntegralGL2 (𝓞 F) F ∧ c ≤ archHeight F (AdelicLevel.glArch (𝓞 F) F g) ∧
    ∀ v : InfinitePlace F, xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) ≤ u ^ 2}

def globalTranslate (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  globalPoints (𝓞 F) F γ * g

def siegelOverlapSet (c u : ℝ) : Set (GL (Fin 2) F) :=
  {γ | ∃ g ∈ integralWindowedSiegelSet F c u,
    globalTranslate F γ g ∈ integralWindowedSiegelSet F c u}

def WindowedSiegelProperty (c u : ℝ) : Prop :=
  (((QuotientGroup.mk : GL (Fin 2) F → GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F))) ''
    siegelOverlapSet F c u).Finite

def WindowedAdelicReduction (c u : ℝ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, ∃ γ : GL (Fin 2) F,
    globalTranslate F γ g ∈ integralWindowedSiegelSet F c u

/--
@isnad1 id=mem.1h3v.s7.939fb67f5b61 from=translated src=- shape=782f89a1 vocab=120a0bf2
-/
theorem one_mem_integralWindowedSiegelSet {c u : ℝ} (hc : c ≤ 1) :
    (1 : AdelicGL2 (𝓞 F) F) ∈ integralWindowedSiegelSet F c u := by
  refine ⟨?_, ?_, fun v => ?_⟩
  · rw [map_one]
    exact one_mem _
  · rw [map_one, archHeight_one]
    exact hc
  · rw [map_one, map_one, xWindowSq_one]
    exact sq_nonneg u

section Invariance

variable {K : Type*} [NormedField K]

/--
@isnad1 id=or.0h2v.s8.8d580a38cc08 from=translated src=- shape=9a33ff8a vocab=8300a5e6
-/
theorem bottom_row_ne_zero (g : GL (Fin 2) K) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∨ (g : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) K) 1 0) 0 with h0 | h0
  · rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) K) 1 1) 0 with h1 | h1
    · exact absurd (by rw [Matrix.det_fin_two, h0, h1]; ring)
        (Matrix.GeneralLinearGroup.det_ne_zero g)
    · exact Or.inr h1
  · exact Or.inl h0

/--
@isnad1 id=lt.0h2v.s6.8d93e226124f from=translated src=- shape=69350396 vocab=7c47596b
-/
theorem rowNormSq_pos (g : GL (Fin 2) K) :
    0 < rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowNormSq
  rcases bottom_row_ne_zero g with h | h
  · exact add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.2 h) 2) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (norm_pos_iff.2 h) 2)

/--
@isnad1 id=eq.2h4v.s9.1f02a001ff5e from=translated src=- shape=bf244b1c vocab=ccd12931
-/
theorem rowNormSq_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    rowNormSq ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ ^ 2 * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hbot : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowNormSq
  rw [hcoe, hbot 0, hbot 1, norm_mul, norm_mul, mul_pow, mul_pow]
  ring

/--
@isnad1 id=eq.2h4v.s9.00c53f31b319 from=translated src=- shape=4725d219 vocab=11ab9492
-/
theorem topNormSq_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (g : GL (Fin 2) K) :
    topNormSq ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ ^ 2 * topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have htop : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 0 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 0 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h00, h01]
    ring
  unfold topNormSq
  rw [hcoe, htop 0, htop 1, norm_mul, norm_mul, mul_pow, mul_pow]
  ring

/--
@isnad1 id=eq.5h4v.s9.f468d08bee98 from=translated src=- shape=b567128d vocab=e11c63a9
-/
theorem localHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    localHeight (s * g) = localHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖z‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [hcoe, Matrix.det_mul, hdets, norm_mul, norm_pow]
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  have hrow := rowNormSq_scalar_entries_mul h10 h11 g
  unfold localHeight
  rw [hdet, hrow,
    div_eq_div_iff (mul_pos hz2 (rowNormSq_pos g)).ne' (rowNormSq_pos g).ne']
  ring

/--
@isnad1 id=eq.5h4v.s9.81c97f795844 from=translated src=- shape=b567128d vocab=1ecd2680
-/
theorem xWindowSq_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    xWindowSq (s * g) = xWindowSq g := by
  have hz2 : (‖z‖ ^ 2 : ℝ) ≠ 0 := (pow_pos (norm_pos_iff.2 hz) 2).ne'
  unfold xWindowSq
  rw [topNormSq_scalar_entries_mul h00 h01 g, rowNormSq_scalar_entries_mul h10 h11 g,
    localHeight_scalar_entries_mul hz h00 h01 h10 h11 g,
    mul_div_mul_left _ _ hz2]

end Invariance

section AdelicInvariance

variable (F : Type) [Field F] [NumberField F]

/--
@isnad1 id=eq.5h3v.s11.db2def7e4202 from=translated src=- shape=a282483e vocab=a7c152c3
-/
theorem glFin_scalar_eq_one {s : AdelicGL2 (𝓞 F) F} {w : AdeleRing (𝓞 F) F}
    (hwf : w.2 = 1)
    (h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = w)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = w) :
    AdelicLevel.glFin (𝓞 F) F s = 1 := by
  have h00' : ((s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 = 1 := by
    rw [h00, hwf]
  have h01' : ((s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2 = 0 := by
    rw [h01]; rfl
  have h10' : ((s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 = 0 := by
    rw [h10]; rfl
  have h11' : ((s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 = 1 := by
    rw [h11, hwf]
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [AdelicLevel.glFin_apply, h00', h01', h10', h11']

/--
@isnad1 id=eq.5h4v.s9.6caa89eace29 from=translated src=- shape=cb0720db vocab=7a273d4c
-/
theorem archHeight_scalar_entries_mul {s : GL (Fin 2) (InfiniteAdeleRing F)}
    {z : InfiniteAdeleRing F} (hz : ∀ v : InfinitePlace F, z v ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 = z)
    (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F (s * g) = archHeight F g := by
  unfold archHeight
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [map_mul]
  congr 1
  refine localHeight_scalar_entries_mul (hz v) ?_ ?_ ?_ ?_ (AdelicLevel.archComponent F v g)
  · rw [AdelicLevel.archComponent_apply, h00]
  · rw [AdelicLevel.archComponent_apply, h01]
    rfl
  · rw [AdelicLevel.archComponent_apply, h10]
    rfl
  · rw [AdelicLevel.archComponent_apply, h11]

/--
@isnad1 id=mem.7h6v.s10.b47ed906aa1e from=translated src=- shape=3f2ae8e0 vocab=e46776aa
-/
theorem scalar_smul_mem_integralWindowedSiegelSet {c u : ℝ}
    {s : AdelicGL2 (𝓞 F) F} {w : AdeleRing (𝓞 F) F}
    (hwf : w.2 = 1) (hwa : ∀ v : InfinitePlace F, w.1 v ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = w)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = w)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ integralWindowedSiegelSet F c u) :
    s * g ∈ integralWindowedSiegelSet F c u := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hglFin : AdelicLevel.glFin (𝓞 F) F s = 1 := glFin_scalar_eq_one F hwf h00 h01 h10 h11
  have harch00 : ((AdelicLevel.glArch (𝓞 F) F s : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0 = w.1 := by
    rw [AdelicLevel.glArch_apply, h00]
  have harch01 : ((AdelicLevel.glArch (𝓞 F) F s : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 1 = 0 := by
    rw [AdelicLevel.glArch_apply, h01]
    rfl
  have harch10 : ((AdelicLevel.glArch (𝓞 F) F s : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0 := by
    rw [AdelicLevel.glArch_apply, h10]
    rfl
  have harch11 : ((AdelicLevel.glArch (𝓞 F) F s : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 = w.1 := by
    rw [AdelicLevel.glArch_apply, h11]
  refine ⟨?_, ?_, fun v => ?_⟩
  · rw [map_mul, hglFin, one_mul]
    exact h1
  · rw [map_mul, archHeight_scalar_entries_mul F hwa harch00 harch01 harch10 harch11]
    exact h2
  · rw [map_mul, map_mul]
    have hcomp00 : ((AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F s) : GL (Fin 2) (v.Completion)) :
        Matrix (Fin 2) (Fin 2) (v.Completion)) 0 0 = w.1 v := by
      rw [AdelicLevel.archComponent_apply, harch00]
    have hcomp01 : ((AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F s) : GL (Fin 2) (v.Completion)) :
        Matrix (Fin 2) (Fin 2) (v.Completion)) 0 1 = 0 := by
      rw [AdelicLevel.archComponent_apply, harch01]
      rfl
    have hcomp10 : ((AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F s) : GL (Fin 2) (v.Completion)) :
        Matrix (Fin 2) (Fin 2) (v.Completion)) 1 0 = 0 := by
      rw [AdelicLevel.archComponent_apply, harch10]
      rfl
    have hcomp11 : ((AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F s) : GL (Fin 2) (v.Completion)) :
        Matrix (Fin 2) (Fin 2) (v.Completion)) 1 1 = w.1 v := by
      rw [AdelicLevel.archComponent_apply, harch11]
    rw [xWindowSq_scalar_entries_mul (hwa v) hcomp00 hcomp01 hcomp10 hcomp11]
    exact h3 v

end AdelicInvariance

section Positivity

variable {K : Type*} [NormedField K]

/--
@isnad1 id=lt.0h2v.s5.c67848ed74bd from=translated src=- shape=0ac22ba1 vocab=8ba39c1e
-/
theorem localHeight_pos (g : GL (Fin 2) K) : 0 < localHeight g := by
  refine div_pos ?_ (rowNormSq_pos g)
  rw [norm_pos_iff]
  exact Matrix.GeneralLinearGroup.det_ne_zero g

end Positivity

variable (F : Type) [Field F] [NumberField F]

/--
@isnad1 id=lt.0h2v.s5.e106108b2204 from=translated src=- shape=6f28b6d9 vocab=d0c76d83
-/
theorem archHeight_pos (g : GL (Fin 2) (InfiniteAdeleRing F)) : 0 < archHeight F g := by
  unfold archHeight
  exact Finset.prod_pos fun v _ => pow_pos (localHeight_pos _) _

def MeasureZeroOrInfiniteAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    (μ : Measure (AdelicGL2 (𝓞 F) F)) (c u : ℝ) : Prop :=
  μ (integralWindowedSiegelSet F c u) = 0 ∨ μ (integralWindowedSiegelSet F c u) = ⊤

/--
@isnad1 id=not.1h1v.s5.f1d470587394 from=translated src=- shape=bc6dfa0e vocab=c68c50ef
-/
theorem not_pos_and_lt_top_of_eq_zero_or_top {x : ℝ≥0∞} (h : x = 0 ∨ x = ⊤) :
    ¬(0 < x ∧ x < ⊤) := by
  rcases h with h | h <;> simp [h]

/--
@isnad1 id=not.1h4v.s7.abac45982eb6 from=translated src=- shape=968ddeae vocab=8432769e
-/
theorem not_pos_and_lt_top_of_measureZeroOrInfiniteAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    {μ : Measure (AdelicGL2 (𝓞 F) F)}
    {c u : ℝ} (h : MeasureZeroOrInfiniteAt F μ c u) :
    ¬(0 < μ (integralWindowedSiegelSet F c u) ∧ μ (integralWindowedSiegelSet F c u) < ⊤) :=
  not_pos_and_lt_top_of_eq_zero_or_top h

end WindowedSiegel

end AutomorphicForm

end
