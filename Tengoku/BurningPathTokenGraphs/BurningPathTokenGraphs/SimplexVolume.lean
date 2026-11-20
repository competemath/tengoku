import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeVolumeLower
import Tengoku.Seed.Analysis.SpecialFunctions.Integrability.Basic
import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Volume of the ordered simplex

This proves the ordered-simplex volume normalization
`vol {0 ≤ x₁ ≤ ⋯ ≤ xₖ ≤ L} = L^k / k!`.
-/

open MeasureTheory

namespace BurningPath

/--
@isnad1 id=measurab.0h2v.s4.2648a55362d0 from=translated src=- shape=663d86fd vocab=b3347267
-/
theorem measurableSet_orderedSimplex (k : ℕ) (L : ℝ) :
    MeasurableSet (orderedSimplex k L) := by
  rw [show orderedSimplex k L =
      {x | ∀ i, 0 ≤ x i ∧ x i ≤ L} ∩ {x | Monotone x} by rfl]
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦
      (measurableSet_le measurable_const (measurable_pi_apply i)).inter
        (measurableSet_le (measurable_pi_apply i) measurable_const)
  · change MeasurableSet {x : Fin k → ℝ | ∀ i j, i ≤ j → x i ≤ x j}
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_
    by_cases hij : i ≤ j
    · simpa [hij] using
        measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
    · simp [hij]

private noncomputable def splitLast (k : ℕ) :
    (Fin (k + 1) → ℝ) ≃ᵐ ℝ × (Fin k → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℝ) (Fin.last k)

@[simp]
private theorem splitLast_fst (k : ℕ) (x : Fin (k + 1) → ℝ) :
    (splitLast k x).1 = x (Fin.last k) := by
  rfl

@[simp]
private theorem splitLast_snd (k : ℕ) (x : Fin (k + 1) → ℝ) (i : Fin k) :
    (splitLast k x).2 i = x i.castSucc := by
  simp [splitLast, MeasurableEquiv.piFinSuccAbove_apply,
    Fin.insertNthEquiv, Fin.init]

@[simp]
private theorem splitLast_symm_last (k : ℕ) (p : ℝ × (Fin k → ℝ)) :
    (splitLast k).symm p (Fin.last k) = p.1 := by
  have h :
      (splitLast k ((splitLast k).symm p)).1 = p.1 :=
    congrArg Prod.fst ((splitLast k).apply_symm_apply p)
  rw [splitLast_fst] at h
  exact h

@[simp]
private theorem splitLast_symm_castSucc (k : ℕ) (p : ℝ × (Fin k → ℝ))
    (i : Fin k) :
    (splitLast k).symm p i.castSucc = p.2 i := by
  have h :
      (splitLast k ((splitLast k).symm p)).2 i = p.2 i :=
    congrArg (fun q : ℝ × (Fin k → ℝ) ↦ q.2 i)
      ((splitLast k).apply_symm_apply p)
  rw [splitLast_snd] at h
  exact h

private theorem splitLast_image_orderedSimplex (k : ℕ) (L : ℝ) :
    splitLast k '' orderedSimplex (k + 1) L =
      {p : ℝ × (Fin k → ℝ) |
        p.1 ∈ Set.Icc (0 : ℝ) L ∧ p.2 ∈ orderedSimplex k p.1} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · exact hx.1 (Fin.last k)
    · constructor
      · intro i
        constructor
        · simpa using (hx.1 i.castSucc).1
        · simpa using hx.2 (Fin.le_last i.castSucc)
      · intro i j hij
        simpa using hx.2 (Fin.castSucc_le_castSucc_iff.mpr hij)
  · intro hp
    refine ⟨(splitLast k).symm p, ?_, (splitLast k).apply_symm_apply p⟩
    constructor
    · intro i
      cases i using Fin.lastCases with
      | last =>
          simpa only [splitLast_symm_last, Set.mem_Icc] using hp.1
      | cast j =>
        constructor
        · simpa using (hp.2.1 j).1
        · simpa only [splitLast_symm_castSucc] using
            (hp.2.1 j).2.trans hp.1.2
    · intro i j hij
      cases i using Fin.lastCases with
      | last =>
          have hj : j = Fin.last k := le_antisymm (Fin.le_last j) hij
          subst j
          exact le_rfl
      | cast i' =>
          cases j using Fin.lastCases with
          | last =>
              simpa only [splitLast_symm_castSucc, splitLast_symm_last] using
                (hp.2.1 i').2
          | cast j' =>
              have hij' : i' ≤ j' := Fin.castSucc_le_castSucc_iff.mp hij
              simpa only [splitLast_symm_castSucc] using hp.2.2 hij'

private theorem setLIntegral_pow_div_factorial (k : ℕ) {L : ℝ}
    (hL : 0 ≤ L) :
    ∫⁻ y : ℝ in Set.Icc 0 L,
        ENNReal.ofReal (y ^ k / (k.factorial : ℝ)) =
      ENNReal.ofReal (L ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
  rw [setLIntegral_congr Ioc_ae_eq_Icc.symm]
  have hint :
      IntegrableOn (fun y : ℝ ↦ y ^ k / (k.factorial : ℝ))
        (Set.Ioc 0 L) :=
    (intervalIntegral.intervalIntegrable_pow k).1.div_const _
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc 0 L)]
        (fun y : ℝ ↦ y ^ k / (k.factorial : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact div_nonneg (pow_nonneg hy.1.le k) (by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_div, integral_pow]
  rw [zero_pow (by omega : k + 1 ≠ 0), sub_zero]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The exact volume formula `vol(Δ_L) = L^k / k!`.
@isnad1 id=eq.1h2v.s6.73047fa93b7c from=translated src=- shape=056b6f1a vocab=6f187098
-/
theorem volume_orderedSimplex (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    volume (orderedSimplex k L) =
      ENNReal.ofReal (L ^ k / (k.factorial : ℝ)) := by
  induction k generalizing L with
  | zero =>
      have hset : orderedSimplex 0 L = realCube 0 L := by
        ext x
        constructor
        · exact fun hx ↦ hx.1
        · intro hx
          exact ⟨hx, fun i ↦ isEmptyElim i⟩
      rw [hset, volume_realCube hL]
      norm_num
  | succ k ih =>
      let e := splitLast k
      let S := e '' orderedSimplex (k + 1) L
      have hS : MeasurableSet S := by
        exact e.measurableSet_image.mpr
          (measurableSet_orderedSimplex (k + 1) L)
      have hpre : e ⁻¹' S = orderedSimplex (k + 1) L := by
        exact e.injective.preimage_image _
      have hpres :
          MeasurePreserving e volume volume := by
        simpa [e, splitLast] using
          (volume_preserving_piFinSuccAbove
            (fun _ : Fin (k + 1) ↦ ℝ) (Fin.last k))
      calc
        volume (orderedSimplex (k + 1) L) =
            volume (e ⁻¹' S) := by rw [hpre]
        _ = volume S :=
          hpres.measure_preimage hS.nullMeasurableSet
        _ = ∫⁻ y : ℝ, volume (Prod.mk y ⁻¹' S) :=
          by
            change (volume.prod volume) S = _
            exact Measure.prod_apply hS
        _ = ∫⁻ y : ℝ in Set.Icc 0 L,
            volume (orderedSimplex k y) := by
          have hfiber (y : ℝ) :
              volume (Prod.mk y ⁻¹' S) =
                Set.indicator (Set.Icc 0 L)
                  (fun z : ℝ ↦ volume (orderedSimplex k z)) y := by
            rw [show S =
                {p : ℝ × (Fin k → ℝ) |
                  p.1 ∈ Set.Icc (0 : ℝ) L ∧
                    p.2 ∈ orderedSimplex k p.1} by
              simpa [S, e] using splitLast_image_orderedSimplex k L]
            have hpreimage :
                Prod.mk y ⁻¹'
                    {p : ℝ × (Fin k → ℝ) |
                      p.1 ∈ Set.Icc (0 : ℝ) L ∧
                        p.2 ∈ orderedSimplex k p.1} =
                  {a : Fin k → ℝ |
                    (0 ≤ y ∧ y ≤ L) ∧ a ∈ orderedSimplex k y} := by
              ext a
              simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc]
            rw [hpreimage]
            by_cases hy : y ∈ Set.Icc (0 : ℝ) L
            · have hy' : 0 ≤ y ∧ y ≤ L := by
                simpa only [Set.mem_Icc] using hy
              rw [show
                  {a : Fin k → ℝ |
                    (0 ≤ y ∧ y ≤ L) ∧ a ∈ orderedSimplex k y} =
                    orderedSimplex k y by
                ext a
                simp [hy']]
              simp [hy]
            · have hy' : ¬(0 ≤ y ∧ y ≤ L) := by
                simpa only [Set.mem_Icc] using hy
              rw [show
                  {a : Fin k → ℝ |
                    (0 ≤ y ∧ y ≤ L) ∧ a ∈ orderedSimplex k y} =
                    ∅ by
                ext a
                simp [hy']]
              simp [hy]
          simp_rw [hfiber]
          exact lintegral_indicator measurableSet_Icc _
        _ = ∫⁻ y : ℝ in Set.Icc 0 L,
            ENNReal.ofReal (y ^ k / (k.factorial : ℝ)) := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro y hy
          exact ih hy.1
        _ = ENNReal.ofReal
            (L ^ (k + 1) / ((k + 1).factorial : ℝ)) :=
          setLIntegral_pow_div_factorial k hL

end BurningPath
