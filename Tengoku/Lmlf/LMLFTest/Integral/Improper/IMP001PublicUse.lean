import Tengoku.Lmlf.LMLF.Integral.Improper.Basic
import Tengoku.Lmlf.LMLF.Integral.Improper.Bochner
import Tengoku.Lmlf.LMLF.Integral.Improper.Abel
import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals
import Tengoku.Seed.Analysis.SpecificLimits.Normed
import Tengoku.Seed.Order.Filter.AtTopBot.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Public-use regressions for the IMP-001 exact signatures.

These proofs use only the public IMP API and separately declared Mathlib support.
-/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace LMLFTest.Integral.Improper.IMP001PublicUse

open LMLF.Integral

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- IMP-R20: arbitrary `S`, with both T06 side conditions derived from a
separate flat bound and `h > 0`.
@isnad1 id=hasimpro.4h7v.s8.b0cee16d1517 from=translated src=- shape=35a9e47d vocab=76df8ccd
-/
theorem r20_arbitrary_S_from_bounded_primitive
    {g F : ℝ → E} {k h L : ℝ} {S : Finset ℝ}
    (hF : IsFiniteExceptionalPrimitive g k S F)
    (hh : 0 < h) (_hL : 0 ≤ L)
    (hflat : ∀ t, k ≤ t → ‖F t‖ ≤ L) :
    HasImproperIntegralAtTopExcept
      (fun t => Real.exp (-h * t) • g t) k S
      (h • ∫ t in Ioi k, Real.exp (-h * t) • F t) := by
  have hscalar : Continuous (fun t : ℝ => Real.exp (-h * t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hFcont : ContinuousOn F (Ioi k) :=
    hF.2.1.mono (fun _ ht => show k ≤ _ from ht.le)
  have hwcont : ContinuousOn (fun t => Real.exp (-h * t) • F t) (Ioi k) :=
    hscalar.continuousOn.smul hFcont
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-h * t)) (Ioi k) := by
    simpa using integrableOn_exp_mul_Ioi (a := -h) (neg_lt_zero.mpr hh) k
  have hmajorant :
      Integrable (fun t : ℝ => L * Real.exp (-h * t)) (volume.restrict (Ioi k)) :=
    hexp.const_mul L
  have hwInt : IntegrableOn (fun t => Real.exp (-h * t) • F t) (Ioi k) := by
    refine hmajorant.mono' (hwcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      Real.exp (-h * t) * ‖F t‖ ≤ Real.exp (-h * t) * L :=
        mul_le_mul_of_nonneg_left (hflat t ht.le) (Real.exp_pos _).le
      _ = L * Real.exp (-h * t) := mul_comm _ _
  have hexp0 : Tendsto (fun t : ℝ => Real.exp (-h * t)) atTop (nhds 0) := by
    have hscale : Tendsto (fun t : ℝ => h * t) atTop atTop :=
      tendsto_id.const_mul_atTop hh
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale).congr' ?_
    exact Eventually.of_forall fun t => by
      simp only [Function.comp_apply, neg_mul]
  have hwLim : Tendsto (fun t => Real.exp (-h * t) • F t) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun t => Real.exp (-h * t) * L)
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_ge_atTop k] with t ht
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hflat t ht) (Real.exp_pos _).le
    · simpa using hexp0.mul_const L
  exact hF.hasImproperIntegralAtTopExcept_exp_smul h hwInt hwLim

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A finite limit and continuity give a flat bound, but the bound is derived
outside T08 and is not a field of either public predicate.
@isnad1 id=ex.2h4v.s6.b3ec560433c1 from=translated src=- shape=3ccc9317 vocab=fadbcc0f
-/
theorem flat_bound_of_continuousOn_Ici_of_tendsto
    {F : ℝ → E} {k : ℝ} {I : E}
    (hcont : ContinuousOn F (Ici k)) (hlim : Tendsto F atTop (nhds I)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, k ≤ t → ‖F t‖ ≤ L := by
  rcases (Metric.tendsto_atTop.1 hlim 1 zero_lt_one) with ⟨N, hN⟩
  let r : ℝ := max k N
  have hcomp : IsCompact (F '' Icc k r) :=
    isCompact_Icc.image_of_continuousOn
      (hcont.mono fun _ ht => ht.1)
  rcases isBounded_iff_forall_norm_le.mp hcomp.isBounded with ⟨C, hC⟩
  refine ⟨max C (‖I‖ + 1), ?_, ?_⟩
  · exact le_trans (norm_nonneg I)
      (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _))
  · intro t hkt
    by_cases htr : t ≤ r
    · exact (hC (F t) ⟨t, ⟨hkt, htr⟩, rfl⟩).trans (le_max_left _ _)
    · have hNt : N ≤ t :=
        (le_max_right k N).trans (le_of_lt (lt_of_not_ge htr))
      have hdist : ‖F t - I‖ ≤ 1 := by
        simpa [dist_eq_norm] using (hN t hNt).le
      calc
        ‖F t‖ = ‖(F t - I) + I‖ := by rw [sub_add_cancel]
        _ ≤ ‖F t - I‖ + ‖I‖ := norm_add_le _ _
        _ ≤ ‖I‖ + 1 := by linarith
        _ ≤ max C (‖I‖ + 1) := le_max_right _ _

/-- Historical partial IMP-R24 evidence from the frozen harness: changing only
the initial-point value preserves the T07 bridge. It does not claim full R24.
@isnad1 id=hasimpro.2h5v.s6.6b4b1377c62f from=translated src=- shape=9b5ac784 vocab=bfcc9333
-/
theorem r07_initial_point_value_irrelevant
    (f : ℝ → E) (k : ℝ) (S : Finset ℝ) (z : E)
    (hS : ∀ c ∈ S, k < c) (hf : IntegrableOn f (Ioi k)) :
    HasImproperIntegralAtTopExcept
      (Function.update f k z) k S (∫ t in Ioi k, f t) := by
  have heq : Set.EqOn (Function.update f k z) f (Ioi k) := by
    intro t ht
    have hkt : k < t := ht
    exact Function.update_of_ne (a := t) (a' := k) (ne_of_gt hkt) z f
  have hu : IntegrableOn (Function.update f k z) (Ioi k) :=
    hf.congr_fun heq.symm measurableSet_Ioi
  have hrel :=
    HasImproperIntegralAtTopExcept.of_integrableOn_Ioi
      (Function.update f k z) k S hS hu
  rw [setIntegral_congr_fun measurableSet_Ioi heq] at hrel
  exact hrel

/-- T03 retains the literal `biUnion` and supports a distinct complete output
codomain.
@isnad1 id=hasimpro.1h9v.s8.59811dcc0c2c from=translated src=- shape=fe6f5cf7 vocab=ee0b498f
-/
theorem r03_cross_codomain_literal_union
    {A : Type*} (s : Finset A) (f : A → ℝ → E)
    (S : A → Finset ℝ) (I : A → E) (T : A → E →L[ℝ] H) {k : ℝ}
    (h : ∀ i ∈ s, HasImproperIntegralAtTopExcept (f i) k (S i) (I i)) :
    HasImproperIntegralAtTopExcept
      (fun t => ∑ i ∈ s, T i (f i t)) k
      (s.biUnion S) (∑ i ∈ s, T i (I i)) :=
  HasImproperIntegralAtTopExcept.finset_clm s f S I T h

/-- A one-model finite subtraction instance used by the source-shaped chain.
It is proved only through T03; no relation representation is opened.
@isnad1 id=hasimpro.2h8v.s8.b5491a85081a from=translated src=- shape=fa4ea9f7 vocab=224b2d92
-/
theorem subtract_one_model
    {q m : ℝ → E} {k : ℝ} {S : Finset ℝ} {Q M : E}
    (U : E →L[ℝ] E)
    (hq : HasImproperIntegralAtTopExcept q k S Q)
    (hm : HasImproperIntegralAtTopExcept m k ∅ M) :
    HasImproperIntegralAtTopExcept
      (fun t => q t - U (m t)) k S (Q - U M) := by
  let f : Fin 2 → ℝ → E := ![q, m]
  let sets : Fin 2 → Finset ℝ := ![S, ∅]
  let vals : Fin 2 → E := ![Q, M]
  let maps : Fin 2 → E →L[ℝ] E := ![ContinuousLinearMap.id ℝ E, -U]
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      HasImproperIntegralAtTopExcept (f i) k (sets i) (vals i) := by
    intro i _
    fin_cases i
    · simpa [f, sets, vals] using hq
    · simpa [f, sets, vals] using hm
  have hunion : (Finset.univ : Finset (Fin 2)).biUnion sets = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · simpa [sets] using hi
      · simp [sets] at hi
    · intro hx
      exact ⟨0, by simpa [sets] using hx⟩
  have hcomb := HasImproperIntegralAtTopExcept.finset_clm
    (Finset.univ : Finset (Fin 2)) f sets vals maps hs
  rw [hunion] at hcomb
  simpa [f, vals, maps, Fin.sum_univ_two, sub_eq_add_neg] using hcomb

/-- A one-model finite recombination instance used by the source-shaped chain.
@isnad1 id=hasimpro.2h8v.s8.e19c494c27c2 from=translated src=- shape=fa4ea9f7 vocab=e2792bbc
-/
theorem add_one_model
    {r m : ℝ → E} {k : ℝ} {S : Finset ℝ} {R M : E}
    (U : E →L[ℝ] E)
    (hr : HasImproperIntegralAtTopExcept r k S R)
    (hm : HasImproperIntegralAtTopExcept m k ∅ M) :
    HasImproperIntegralAtTopExcept
      (fun t => r t + U (m t)) k S (R + U M) := by
  let f : Fin 2 → ℝ → E := ![r, m]
  let sets : Fin 2 → Finset ℝ := ![S, ∅]
  let vals : Fin 2 → E := ![R, M]
  let maps : Fin 2 → E →L[ℝ] E := ![ContinuousLinearMap.id ℝ E, U]
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      HasImproperIntegralAtTopExcept (f i) k (sets i) (vals i) := by
    intro i _
    fin_cases i
    · simpa [f, sets, vals] using hr
    · simpa [f, sets, vals] using hm
  have hunion : (Finset.univ : Finset (Fin 2)).biUnion sets = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · simpa [sets] using hi
      · simp [sets] at hi
    · intro hx
      exact ⟨0, by simpa [sets] using hx⟩
  have hcomb := HasImproperIntegralAtTopExcept.finset_clm
    (Finset.univ : Finset (Fin 2)) f sets vals maps hs
  rw [hunion] at hcomb
  simpa [f, vals, maps, Fin.sum_univ_two] using hcomb

/-- T04 has the exact `J + I` orientation; T08 then extracts an existential
primitive, and its flat bound is proved by the separate theorem above.
@isnad1 id=ex.4h6v.s7.d89e27f62dba from=translated src=- shape=b5b1fcf1 vocab=d60f13b4
-/
theorem r04_split_then_r08_extract_and_bound
    (f : ℝ → E) {a k : ℝ} (S : Finset ℝ) (I : E)
    (hak : a ≤ k) (hS : ∀ c ∈ S, k < c)
    (hf : IntervalIntegrable f volume a k)
    (hrel : HasImproperIntegralAtTopExcept
      f a S ((∫ t in a..k, f t) + I)) :
    ∃ F : ℝ → E, ∃ L : ℝ,
      IsFiniteExceptionalPrimitive f k S F ∧
      Tendsto F atTop (nhds I) ∧
      0 ≤ L ∧ ∀ t, k ≤ t → ‖F t‖ ≤ L := by
  have htail : HasImproperIntegralAtTopExcept f k S I :=
    (HasImproperIntegralAtTopExcept.split_regular f S I hak hS hf).mp hrel
  rcases hasImproperIntegralAtTopExcept_iff_exists_primitive.mp htail with
    ⟨F, hprim, hlim⟩
  rcases flat_bound_of_continuousOn_Ici_of_tendsto hprim.2.1 hlim with
    ⟨L, hL, hflat⟩
  exact ⟨F, L, hprim, hlim, hL, hflat⟩

/-- A bounded, complete source-shaped path through the public IMP API.
@isnad1 id=ex.8h8v.s11.e4ab3ffd05e3 from=translated src=- shape=08659653 vocab=68d6aa6e
-/
theorem source_shaped_public_chain_one_model
    (q m : ℝ → E) (U : E →L[ℝ] E) (S : Finset ℝ)
    (QX : E) {k h : ℝ}
    (hSk : ∀ c ∈ S, k < c) (h0k : 0 ≤ k) (hh : 0 < h)
    (hsource : HasImproperIntegralAtTopExcept q 0 S QX)
    (hmodelX : IntegrableOn m (Ioi 0))
    (hlocalX : IntervalIntegrable (fun t => q t - U (m t)) volume 0 k)
    (hlocalTarget : IntervalIntegrable
      (fun t => Real.exp (-h * t) • (q t - U (m t))) volume 0 k)
    (hmodelTarget : IntegrableOn
      (fun t => Real.exp (-h * t) • m t) (Ioi 0)) :
    ∃ F : ℝ → E, ∃ L : ℝ,
      IsFiniteExceptionalPrimitive
          (fun t => q t - U (m t)) k S F ∧
      Tendsto F atTop
        (nhds (QX - U (∫ t in Ioi 0, m t) -
          ∫ t in (0 : ℝ)..k, q t - U (m t))) ∧
      0 ≤ L ∧
      (∀ t, k ≤ t → ‖F t‖ ≤ L) ∧
      HasImproperIntegralAtTopExcept
        (fun t =>
          Real.exp (-h * t) • (q t - U (m t)) +
            U (Real.exp (-h * t) • m t))
        0 S
        ((∫ t in (0 : ℝ)..k, Real.exp (-h * t) • (q t - U (m t))) +
          h • (∫ t in Ioi k, Real.exp (-h * t) • F t) +
          U (∫ t in Ioi 0, Real.exp (-h * t) • m t)) := by
  have hmX : HasImproperIntegralAtTopExcept
      m 0 ∅ (∫ t in Ioi 0, m t) :=
    HasImproperIntegralAtTopExcept.of_integrableOn_Ioi
      m 0 ∅ (by simp) hmodelX
  have hrem0 : HasImproperIntegralAtTopExcept
      (fun t => q t - U (m t)) 0 S
      (QX - U (∫ t in Ioi 0, m t)) :=
    subtract_one_model U hsource hmX
  let JX : E := ∫ t in (0 : ℝ)..k, q t - U (m t)
  let TX : E := QX - U (∫ t in Ioi 0, m t) - JX
  have hrem0' : HasImproperIntegralAtTopExcept
      (fun t => q t - U (m t)) 0 S (JX + TX) := by
    simpa [JX, TX, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrem0
  have htail : HasImproperIntegralAtTopExcept
      (fun t => q t - U (m t)) k S TX :=
    (HasImproperIntegralAtTopExcept.split_regular
      (fun t => q t - U (m t)) S TX h0k hSk hlocalX).mp hrem0'
  rcases hasImproperIntegralAtTopExcept_iff_exists_primitive.mp htail with
    ⟨F, hprim, hlim⟩
  rcases flat_bound_of_continuousOn_Ici_of_tendsto hprim.2.1 hlim with
    ⟨L, hL, hflat⟩
  have hweightedTail :=
    r20_arbitrary_S_from_bounded_primitive hprim hh hL hflat
  have hweightedFull : HasImproperIntegralAtTopExcept
      (fun t => Real.exp (-h * t) • (q t - U (m t))) 0 S
      ((∫ t in (0 : ℝ)..k, Real.exp (-h * t) • (q t - U (m t))) +
        h • ∫ t in Ioi k, Real.exp (-h * t) • F t) :=
    (HasImproperIntegralAtTopExcept.split_regular
      (fun t => Real.exp (-h * t) • (q t - U (m t))) S
      (h • ∫ t in Ioi k, Real.exp (-h * t) • F t)
      h0k hSk hlocalTarget).mpr hweightedTail
  have hmTarget : HasImproperIntegralAtTopExcept
      (fun t => Real.exp (-h * t) • m t) 0 ∅
      (∫ t in Ioi 0, Real.exp (-h * t) • m t) :=
    HasImproperIntegralAtTopExcept.of_integrableOn_Ioi
      (fun t => Real.exp (-h * t) • m t) 0 ∅ (by simp) hmodelTarget
  have hfinal := add_one_model U hweightedFull hmTarget
  exact ⟨F, L, hprim, by simpa [TX, JX] using hlim, hL, hflat, by
    simpa [add_assoc] using hfinal⟩

section NegativeTypeShapeChecks

end NegativeTypeShapeChecks

end LMLFTest.Integral.Improper.IMP001PublicUse
