import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.OneSidedPolynomial
import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.TracePowers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {K : Omega → Omega → Real}

/--
@isnad1 id=good.1h3v.s5.0107475b12ca from=translated src=- shape=8cfc412f vocab=e8690847
-/
lemma good_degCentered_of_goodK (hK : GoodK K) :
    Good (degCentered K mu) := by
  have hdegree : Good (degree K mu) := by
    have heq : degree K mu = kernelOp K mu (fun _ : Omega => 1) := by
      funext x
      simp [degree, kernelOp]
    rw [heq]
    exact good_kernelOp_goodK (mu := mu) hK good_one
  exact good_sub hdegree
    (OddCycleBound.DenseRegion.good_const (Omega := Omega) (edgeDensity K mu))

/--
@isnad1 id=eq.1h3v.s5.ca3a3227fd24 from=translated src=- shape=5c4fd67d vocab=83df70ba
-/
lemma mean_degCentered_of_goodK (hK : GoodK K) :
    mean mu (degCentered K mu) = 0 := by
  have hdegree : Good (degree K mu) := by
    have heq : degree K mu = kernelOp K mu (fun _ : Omega => 1) := by
      funext x
      simp [degree, kernelOp]
    rw [heq]
    exact good_kernelOp_goodK (mu := mu) hK good_one
  simp [mean, degCentered, edgeDensity, integral_sub, hdegree.integrable]

/--
@isnad1 id=goodk.1h3v.s5.741978fe06c7 from=translated src=- shape=1ef70e5d vocab=9075e40f
-/
lemma centeredKernel_goodK_of_goodK (hK : GoodK K) :
    GoodK (centeredKernel K mu) := by
  have hdegree : Good (degree K mu) := by
    have heq : degree K mu = kernelOp K mu (fun _ : Omega => 1) := by
      funext x
      simp [degree, kernelOp]
    rw [heq]
    exact good_kernelOp_goodK (mu := mu) hK good_one
  refine ⟨?_, ?_⟩
  · exact (((hK.meas.sub (hdegree.meas.measurable.comp measurable_fst)).sub
      (hdegree.meas.measurable.comp measurable_snd)).add measurable_const)
  · obtain ⟨C, hC0, hKC⟩ := hK.bdd
    refine ⟨3 * C + |edgeDensity K mu|,
      add_nonneg (mul_nonneg (by norm_num) hC0) (abs_nonneg _), ?_⟩
    intro x y
    unfold centeredKernel
    have hdegx : |degree K mu x| ≤ C := by
      unfold degree
      calc
        |∫ z, K x z ∂mu| ≤ ∫ z, |K x z| ∂mu :=
          abs_integral_le_integral_abs
        _ ≤ ∫ _z, C ∂mu := by
              exact integral_mono
                (hK.integrable_row x).abs (integrable_const _)
                (fun z => hKC x z)
        _ = C := by simp
    have hdegy : |degree K mu y| ≤ C := by
      unfold degree
      calc
        |∫ z, K y z ∂mu| ≤ ∫ z, |K y z| ∂mu :=
          abs_integral_le_integral_abs
        _ ≤ ∫ _z, C ∂mu := by
              exact integral_mono
                (hK.integrable_row y).abs (integrable_const _)
                (fun z => hKC y z)
        _ = C := by simp
    calc
      |K x y - degree K mu x - degree K mu y + edgeDensity K mu| ≤
          |K x y| + |degree K mu x| + |degree K mu y| +
            |edgeDensity K mu| := by
              calc
                _ ≤ |K x y - degree K mu x - degree K mu y| +
                    |edgeDensity K mu| := abs_add_le _ _
                _ ≤ (|K x y - degree K mu x| + |degree K mu y|) +
                    |edgeDensity K mu| :=
                      add_le_add (abs_sub _ _) (le_refl _)
                _ ≤ (|K x y| + |degree K mu x| + |degree K mu y|) +
                    |edgeDensity K mu| :=
                      add_le_add (add_le_add (abs_sub _ _) (le_refl _))
                        (le_refl _)
      _ ≤ C + C + C + |edgeDensity K mu| := by linarith [hKC x y]
      _ = 3 * C + |edgeDensity K mu| := by ring

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=eq.0h5v.s6.b68f31fd5842 from=translated src=- shape=b3130f08 vocab=8b4769b3
-/
theorem kernel_eq_block_decomposition (K : Omega → Omega → Real) (x y : Omega) :
    K x y = edgeDensity K mu + degCentered K mu x +
      degCentered K mu y + centeredKernel K mu x y := by
  unfold degCentered centeredKernel
  ring

/--
@isnad1 id=eq.1h4v.s5.3fd2b6cf5a4b from=translated src=- shape=8921801a vocab=68fcadbc
-/
theorem integral_centeredKernel_row (hK : GoodK K) (x : Omega) :
    ∫ y, centeredKernel K mu x y ∂mu = 0 := by
  have hdegree : Good (degree K mu) := by
    have heq : degree K mu = kernelOp K mu (fun _ : Omega => 1) := by
      funext z
      simp [degree, kernelOp]
    rw [heq]
    exact good_kernelOp_goodK (mu := mu) hK good_one
  unfold centeredKernel
  have hrow : Integrable (fun y => K x y) mu := hK.integrable_row x
  have hdegreeX : Integrable (fun _ : Omega => degree K mu x) mu :=
    integrable_const _
  have hedge : Integrable (fun _ : Omega => edgeDensity K mu) mu :=
    integrable_const _
  calc
    (∫ y, K x y - degree K mu x - degree K mu y +
        edgeDensity K mu ∂mu) =
        (∫ y, K x y - degree K mu x - degree K mu y ∂mu) +
          ∫ _y : Omega, edgeDensity K mu ∂mu := by
            exact integral_add
              ((hrow.sub hdegreeX).sub hdegree.integrable) hedge
    _ = ((∫ y, K x y - degree K mu x ∂mu) -
          ∫ y, degree K mu y ∂mu) +
          ∫ _y : Omega, edgeDensity K mu ∂mu := by
            exact congrArg
              (fun z : Real => z + ∫ _y : Omega, edgeDensity K mu ∂mu)
              (integral_sub (hrow.sub hdegreeX) hdegree.integrable)
    _ = (((∫ y, K x y ∂mu) -
          ∫ _y : Omega, degree K mu x ∂mu) -
          ∫ y, degree K mu y ∂mu) +
          ∫ _y : Omega, edgeDensity K mu ∂mu := by
            exact congrArg
              (fun z : Real => (z - ∫ y, degree K mu y ∂mu) +
                ∫ _y : Omega, edgeDensity K mu ∂mu)
              (integral_sub hrow hdegreeX)
    _ = 0 := by
      simp [degree, edgeDensity, mean]

/--
@isnad1 id=eq.2h4v.s6.8696e2b03681 from=translated src=- shape=86ea2529 vocab=68fcadbc
-/
theorem integral_centeredKernel_col
    (hK : GoodK K) (hsymm : ∀ x y, K x y = K y x) (y : Omega) :
    ∫ x, centeredKernel K mu x y ∂mu = 0 := by
  have hcentSymm : ∀ x y, centeredKernel K mu x y = centeredKernel K mu y x := by
    intro x z
    unfold centeredKernel
    rw [hsymm x z]
    ring
  calc
    (∫ x, centeredKernel K mu x y ∂mu) =
        ∫ x, centeredKernel K mu y x ∂mu := by
          exact integral_congr_ae (ae_of_all _ fun x => hcentSymm x y)
    _ = 0 := integral_centeredKernel_row hK y

/--
@isnad1 id=eq.1h3v.s5.00dbca060c23 from=translated src=- shape=b646de78 vocab=c87d8656
-/
theorem trace_centeredKernel (hK : GoodK K) :
    trace mu (centeredKernel K mu) = trace mu K - edgeDensity K mu := by
  have hg := good_degCentered_of_goodK (mu := mu) hK
  have hmean := mean_degCentered_of_goodK (mu := mu) hK
  unfold trace
  calc
    (∫ x, centeredKernel K mu x x ∂mu) =
        ∫ x, K x x - edgeDensity K mu -
          2 * degCentered K mu x ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            unfold centeredKernel degCentered
            ring
    _ = (∫ x, K x x ∂mu) - edgeDensity K mu -
          2 * ∫ x, degCentered K mu x ∂mu := by
            have hdiag : Integrable (fun x => K x x) mu := hK.diag_integrable
            have hconst : Integrable (fun _x : Omega => edgeDensity K mu) mu :=
              integrable_const _
            have htwo : Integrable (fun x => 2 * degCentered K mu x) mu :=
              hg.integrable.const_mul 2
            calc
              (∫ x, K x x - edgeDensity K mu -
                  2 * degCentered K mu x ∂mu) =
                  (∫ x, K x x - edgeDensity K mu ∂mu) -
                    ∫ x, 2 * degCentered K mu x ∂mu := by
                      exact integral_sub (hdiag.sub hconst) htwo
              _ = ((∫ x, K x x ∂mu) -
                    ∫ _x : Omega, edgeDensity K mu ∂mu) -
                    ∫ x, 2 * degCentered K mu x ∂mu := by
                      rw [integral_sub hdiag hconst]
              _ = (∫ x, K x x ∂mu) - edgeDensity K mu -
                    2 * ∫ x, degCentered K mu x ∂mu := by
                      rw [integral_const, integral_const_mul]
                      simp
    _ = (∫ x, K x x ∂mu) - edgeDensity K mu := by
          change (∫ x, K x x ∂mu) - edgeDensity K mu - 2 *
            mean mu (degCentered K mu) = _
          rw [hmean]
          ring

/--
@isnad1 id=eq.1h3v.s5.ee40c50e9b75 from=translated src=- shape=70a8c1c8 vocab=44205b37
-/
theorem trace_eq_edgeDensity_add_centeredTrace (hK : GoodK K) :
    trace mu K = edgeDensity K mu + trace mu (centeredKernel K mu) := by
  rw [trace_centeredKernel hK]
  ring

end OddCycleBound.IntermediateRegion
