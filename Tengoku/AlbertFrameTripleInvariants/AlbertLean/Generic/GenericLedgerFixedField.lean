import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericFieldChart
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ReciprocalFixedField
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualLiteralLedgerDictionary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms generic_orientation_ne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rootSum_eq_S` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms base_mem_chartField` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generic_ledgerField_eq_invariantField` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generic_ledgerField_degree_two` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section

namespace AlbertLean.Generic.GenericLedgerFixedField

open Matrix
open AlbertLean.Generic.ChartBridge
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Residual.NormalizedOrbitSection
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Generic.GenericNormalizedFrameChart
open AlbertLean.Generic.GenericDeterminantOpen
open AlbertLean.Generic.GenericFieldChart
open AlbertLean.Generic.NestedReciprocalField
open AlbertLean.Generic.ResidualLiteralLedgerDictionary
open AlbertLean.Generic.ResidualLedgerMomentField

universe u
variable (k : Type u) [Field k] [CharZero k]

def gaugeGenerators : Set (FunctionField k) :=
  Set.range (algebraMap k (FunctionField k)) ∪
    { includeBase k (ι k (GenericDeterminantOpen.a k)),
      includeBase k (ι k (GenericDeterminantOpen.b k)),
      includeBase k (ι k (GenericDeterminantOpen.c k)) }

def gaugeBase : Subfield (FunctionField k) := Subfield.closure (gaugeGenerators k)

/--
@isnad1 id=mem.0h1v.s10.7f7d603825d4 from=translated src=- shape=bacc5321 vocab=8b6813bf
-/
theorem gauge_mem_a : (genericChart k).z1 ∈ gaugeBase k := by
  apply Subfield.subset_closure
  change includeBase k (ι k (GenericDeterminantOpen.a k)) ∈ gaugeGenerators k
  exact Or.inr (Or.inl rfl)

/--
@isnad1 id=mem.0h1v.s10.02950301c44c from=translated src=- shape=bacc5321 vocab=bd1a9f23
-/
theorem gauge_mem_b : (genericChart k).r2 ∈ gaugeBase k := by
  apply Subfield.subset_closure
  change includeBase k (ι k (GenericDeterminantOpen.b k)) ∈ gaugeGenerators k
  exact Or.inr (Or.inr (Or.inl rfl))

/--
@isnad1 id=mem.0h1v.s10.b595668bd0a3 from=translated src=- shape=bacc5321 vocab=4ad2bb30
-/
theorem gauge_mem_c : (genericChart k).z2 ∈ gaugeBase k := by
  apply Subfield.subset_closure
  change includeBase k (ι k (GenericDeterminantOpen.c k)) ∈ gaugeGenerators k
  exact Or.inr (Or.inr (Or.inr rfl))

/--
@isnad1 id=ne.0h1v.s9.27dc11c2a781 from=translated src=- shape=805f1cc7 vocab=2c10cac2
-/
theorem generic_orientation_ne : orientation (genericChart k) ≠ 0 := by
  change orientation (GenericNormalizedFrameChart.insert (genericOpen k)) ≠ 0
  rw [insert_orientation]
  have hbridge :
      (fieldParameters k).c - (fieldParameters k).a * (fieldParameters k).b =
        includeBase k (ι k (GenericDeterminantOpen.c k -
          GenericDeterminantOpen.a k * GenericDeterminantOpen.b k)) := by
    simp only [fieldParameters, baseParameters, map_sub, map_mul]
  change (fieldParameters k).c - (fieldParameters k).a * (fieldParameters k).b ≠ 0
  rw [hbridge]
  apply (map_ne_zero (includeBase k)).mpr
  intro hι
  have h : GenericDeterminantOpen.c k - GenericDeterminantOpen.a k *
      GenericDeterminantOpen.b k = 0 := by
    apply iota_injective k
    simpa using hι
  have hh := congrArg (witnessEval k) h
  simp [GenericDeterminantOpen.a, GenericDeterminantOpen.b,
    GenericDeterminantOpen.c, gaugeX, GenericDeterminantOpen.x,
    witnessEval, witnessValue] at hh
  norm_num at hh

/--
@isnad1 id=eq.0h1v.s11.d01f83f34e9f from=translated src=- shape=625c7d04 vocab=74bfd1ba
-/
theorem rootSum_eq_S :
    deltaX (genericChart k).s1 (genericChart k).s2
        (genericChart k).c1 (genericChart k).c2 +
      deltaStarA (genericChart k).s1 (genericChart k).s2
        (genericChart k).c1 (genericChart k).c2 =
      S (Base k) (Matrix.det (rationalM k)) := by
  change deltaX (GenericNormalizedFrameChart.insert (genericOpen k)).s1 (GenericNormalizedFrameChart.insert (genericOpen k)).s2
      (GenericNormalizedFrameChart.insert (genericOpen k)).c1 (GenericNormalizedFrameChart.insert (genericOpen k)).c2 +
    deltaStarA (GenericNormalizedFrameChart.insert (genericOpen k)).s1 (GenericNormalizedFrameChart.insert (genericOpen k)).s2
      (GenericNormalizedFrameChart.insert (genericOpen k)).c1 (GenericNormalizedFrameChart.insert (genericOpen k)).c2 = _
  rw [deltaX_eq_det_XMatrix, deltaStarA_eq_det_AMatrix]
  change Matrix.det (residualPairOfChart (GenericNormalizedFrameChart.insert (genericOpen k))).X +
    Matrix.det (residualPairOfChart (GenericNormalizedFrameChart.insert (genericOpen k))).A = _
  rw [insert_residualPair]
  change Matrix.det (X0 (fieldParameters k).Delta) +
    Matrix.det (moment (fieldParameters k) * X0Inv (fieldParameters k).Delta) = _
  rw [det_X0, Matrix.det_mul, det_X0Inv, fieldParameters_detMoment]
  rfl

/--
@isnad1 id=eq.0h1v.s9.10b8d5c5e385 from=translated src=- shape=0ce5918c vocab=4b8ebba5
-/
theorem ledger_eq_chart :
    ledgerField (gaugeBase k) (encoderA (genericChart k))
        (encoderB (genericChart k)) = chartField (gaugeBase k) (genericChart k) := by
  apply ledgerField_eq_chartField
  · exact (gaugeBase k).one_mem
  · exact gauge_mem_a k
  · exact gauge_mem_b k
  · exact gauge_mem_c k
  · exact generic_orientation_ne k
  · exact (genericChart_source_fixedSpectrum k).2.2.1
  · exact (genericChart_source_fixedSpectrum k).2.2.2.2.2

/-! Use named membership facts, keeping the nested generator union local. -/

private theorem chart_base {z : FunctionField k} (hz : z ∈ gaugeBase k) :
    z ∈ chartField (gaugeBase k) (genericChart k) :=
  Subfield.subset_closure (Or.inl hz)

private theorem chart_diagA (i : Fin 3) :
    (genericChart k).diagA i ∈ chartField (gaugeBase k) (genericChart k) :=
  Subfield.subset_closure (Or.inr (Or.inl (Or.inl (Or.inl ⟨i,rfl⟩))))

private theorem chart_diagB (i : Fin 3) :
    (genericChart k).diagB i ∈ chartField (gaugeBase k) (genericChart k) :=
  Subfield.subset_closure (Or.inr (Or.inl (Or.inl (Or.inr ⟨i,rfl⟩))))

private theorem chart_matrix (i j : Fin 4) :
    matrixM (genericChart k) i j ∈ chartField (gaugeBase k) (genericChart k) :=
  Subfield.subset_closure (Or.inr (Or.inl (Or.inr ⟨(i,j),rfl⟩)))

private theorem generic_matrix (i j : Fin 4) :
    matrixM (genericChart k) i j = includeBase k (rationalM k i j) := by
  change matrixM (GenericNormalizedFrameChart.insert (genericOpen k)) i j = _
  rw [insert_matrixM]
  change moment (fieldParameters k) i j = _
  rw [fieldParameters_moment]
  rfl

private theorem include_constant (z : k) :
    includeBase k (ι k (MvPolynomial.C z)) = algebraMap k (FunctionField k) z := by
  change algebraMap (Base k) (FunctionField k)
    (algebraMap (BasePolynomial k) (Base k) (algebraMap k (BasePolynomial k) z)) = _
  rw [← IsScalarTower.algebraMap_apply k (BasePolynomial k) (Base k),
    ← IsScalarTower.algebraMap_apply k (Base k) (FunctionField k)]

/--
@isnad1 id=mem.0h2v.s11.0bf48d6f4822 from=translated src=- shape=bad5418e vocab=e9a3fc9b
-/
theorem baseVariable_mem_chartField (v : BaseVar) :
    includeBase k (ι k (MvPolynomial.X v)) ∈
      chartField (gaugeBase k) (genericChart k) := by
  rcases v with i | (i | ⟨⟨i,j⟩,h⟩)
  · fin_cases i
    · exact chart_diagA k 0
    · exact chart_diagA k 1
    · exact chart_diagB k 0
    · exact chart_diagB k 1
  · fin_cases i
    · exact chart_base k (gauge_mem_a k)
    · exact chart_base k (gauge_mem_b k)
    · exact chart_base k (gauge_mem_c k)
  · have hh := chart_matrix k i j
    rw [generic_matrix] at hh
    simpa only [rationalM, dite_eq_right h, offX, x] using hh

/--
@isnad1 id=mem.0h2v.s11.387b32fabc2b from=translated src=- shape=5a9cafbc vocab=c8f70a1e
-/
theorem polynomial_mem_chartField (p : BasePolynomial k) :
    includeBase k (ι k p) ∈ chartField (gaugeBase k) (genericChart k) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [include_constant]
      exact chart_base k (Subfield.subset_closure (Or.inl ⟨a,rfl⟩))
  | add p q hp hq =>
      simpa only [map_add] using
        (chartField (gaugeBase k) (genericChart k)).add_mem hp hq
  | mul_X p v hp =>
      simpa only [map_mul] using
        (chartField (gaugeBase k) (genericChart k)).mul_mem hp
          (baseVariable_mem_chartField k v)

/--
@isnad1 id=mem.0h2v.s10.d8a590b05525 from=translated src=- shape=15c33e28 vocab=16dd03e5
-/
theorem base_mem_chartField (b : Base k) :
    includeBase k b ∈ chartField (gaugeBase k) (genericChart k) := by
  obtain ⟨p,q,hq,rfl⟩ := IsFractionRing.div_surjective (BasePolynomial k) b
  rw [map_div₀]
  exact Subfield.div_mem _ (polynomial_mem_chartField k p)
    (polynomial_mem_chartField k q)

private theorem invariant_base (b : Base k) :
    includeBase k b ∈ invariantField (Base k) (Matrix.det (rationalM k)) :=
  Subfield.subset_closure (Or.inl ⟨b,rfl⟩)

private theorem gauge_le_invariant :
    gaugeBase k ≤ invariantField (Base k) (Matrix.det (rationalM k)) := by
  apply Subfield.closure_le.2
  change gaugeGenerators k ⊆ _
  rintro z (⟨z,rfl⟩ | hz)
  · rw [← include_constant]
    exact invariant_base k _
  · rcases hz with rfl | rfl | rfl <;> exact invariant_base k _

/--
@isnad1 id=eq.0h1v.s8.78cb8e122f6b from=translated src=- shape=8d6d4749 vocab=a41ef5bb
-/
theorem chart_eq_invariant :
    chartField (gaugeBase k) (genericChart k) =
      invariantField (Base k) (Matrix.det (rationalM k)) := by
  apply le_antisymm
  · apply Subfield.closure_le.2
    change (gaugeBase k : Set (FunctionField k)) ∪ chartCells (genericChart k) ⊆ _
    rintro z (hz | hz)
    · exact gauge_le_invariant k hz
    · rcases hz with ((⟨i,rfl⟩ | ⟨i,rfl⟩) | ⟨⟨i,j⟩,rfl⟩) | hz
      · fin_cases i
        · exact invariant_base k _
        · exact invariant_base k _
        · change -includeBase k _ - includeBase k _ ∈ _
          exact Subfield.sub_mem _ (Subfield.neg_mem _ (invariant_base k _))
            (invariant_base k _)
      · fin_cases i
        · exact invariant_base k _
        · exact invariant_base k _
        · change -includeBase k _ - includeBase k _ ∈ _
          exact Subfield.sub_mem _ (Subfield.neg_mem _ (invariant_base k _))
            (invariant_base k _)
      · change matrixM (genericChart k) i j ∈ _
        rw [generic_matrix]
        exact invariant_base k _
      · rw [Set.mem_singleton_iff.mp hz, rootSum_eq_S]
        exact Subfield.subset_closure (Or.inr rfl)
  · apply Subfield.closure_le.2
    change Set.range (algebraMap (Base k) (FunctionField k)) ∪
      {S (Base k) (Matrix.det (rationalM k))} ⊆ _
    rintro z (⟨b,rfl⟩ | hz)
    · exact base_mem_chartField k b
    · rw [Set.mem_singleton_iff.mp hz, ← rootSum_eq_S]
      exact Subfield.subset_closure (Or.inr (Or.inr rfl))

/--
@isnad1 id=eq.0h1v.s9.8a741ba09857 from=translated src=- shape=e33a895d vocab=1ece148f
-/
theorem generic_ledgerField_eq_invariantField :
    ledgerField (gaugeBase k) (encoderA (genericChart k))
        (encoderB (genericChart k)) =
      invariantField (Base k) (Matrix.det (rationalM k)) := by
  rw [ledger_eq_chart, chart_eq_invariant]

/-- Degree two over the actual ledger with the displayed gauge coordinates adjoined.
@isnad1 id=eq.0h1v.s12.6bb3f18a6af2 from=translated src=- shape=0dc6996d vocab=a2e1d4ef
-/
theorem generic_ledgerField_degree_two :
    Module.finrank
      (ledgerField (gaugeBase k) (encoderA (genericChart k))
        (encoderB (genericChart k))) (FunctionField k) = 2 := by
  rw [generic_ledgerField_eq_invariantField]
  exact invariantField_degree_two (Base k) (Matrix.det (rationalM k))
    (det_rationalM_ne_zero k)

end AlbertLean.Generic.GenericLedgerFixedField
