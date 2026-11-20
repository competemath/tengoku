import Tengoku.Lmlf.LMLF.Integral.Improper.Bochner
import Tengoku.Seed.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Analytic regression IMP-R24: changing an integrand at the initial endpoint and
at every member of the finite exceptional set preserves the public IMP-001
relations.
-/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace LMLFTest.Integral.Improper

open LMLF.Integral

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
private theorem endpoint_ae_eq
    {f ftilde : ℝ → E} {k : ℝ} {S : Finset ℝ}
    (hEq : Set.EqOn f ftilde ({k} ∪ (↑S : Set ℝ))ᶜ) :
    f =ᵐ[volume] ftilde := by
  have hfinite : ({k} ∪ (↑S : Set ℝ)).Finite :=
    Set.finite_singleton k |>.union S.finite_toSet
  filter_upwards [hfinite.countable.ae_notMem volume] with t ht
  exact hEq ht

omit [CompleteSpace E] in
/-- REG.50: interval integrability and the (possibly totalized) interval
integral are invariant under arbitrary changes on `{k} ∪ S`.-/
theorem finiteEndpoint_interval_invariance
    {f ftilde : ℝ → E} {k a b : ℝ} {S : Finset ℝ}
    (hEq : Set.EqOn f ftilde ({k} ∪ (↑S : Set ℝ))ᶜ) :
    (IntervalIntegrable f volume a b ↔
      IntervalIntegrable ftilde volume a b) ∧
      (∫ t in a..b, f t) = ∫ t in a..b, ftilde t := by
  have hae := endpoint_ae_eq hEq
  constructor
  · exact intervalIntegrable_congr_ae (ae_restrict_of_ae hae)
  · exact intervalIntegral.integral_congr_ae
      (hae.mono fun _ ht _ ↦ ht)

omit [CompleteSpace E] in
/-- REG.51: honest integrability and the set-integral value on the open ray
are invariant under arbitrary changes on `{k} ∪ S`.-/
theorem finiteEndpoint_Ioi_invariance
    {f ftilde : ℝ → E} {k : ℝ} {S : Finset ℝ}
    (hEq : Set.EqOn f ftilde ({k} ∪ (↑S : Set ℝ))ᶜ) :
    (IntegrableOn f (Ioi k) ↔ IntegrableOn ftilde (Ioi k)) ∧
      (∫ t in Ioi k, f t) = ∫ t in Ioi k, ftilde t := by
  have hae := endpoint_ae_eq hEq
  constructor
  · exact integrableOn_congr_fun_ae (ae_restrict_of_ae hae)
  · exact setIntegral_congr_ae measurableSet_Ioi
      (hae.mono fun _ ht _ ↦ ht)

/-- REG.53: for every fixed `F`, the complete public T05 statement is
invariant under arbitrary changes of the integrand on `{k} ∪ S`.-/
theorem finiteEndpoint_primitive_iff
    {f ftilde F : ℝ → E} {k : ℝ} {S : Finset ℝ}
    (hEq : Set.EqOn f ftilde ({k} ∪ (↑S : Set ℝ))ᶜ) :
    IsFiniteExceptionalPrimitive f k S F ↔
      IsFiniteExceptionalPrimitive ftilde k S F := by
  have hinterval (a b : ℝ) :=
    finiteEndpoint_interval_invariance (a := a) (b := b) hEq
  constructor
  · intro hF
    refine ⟨hF.1, hF.2.1, hF.2.2.1, ?_⟩
    intro a b hka hab hdis
    rcases hF.2.2.2 hka hab hdis with ⟨hInt, hinc⟩
    exact ⟨(hinterval a b).1.mp hInt, hinc.trans (hinterval a b).2⟩
  · intro hF
    refine ⟨hF.1, hF.2.1, hF.2.2.1, ?_⟩
    intro a b hka hab hdis
    rcases hF.2.2.2 hka hab hdis with ⟨hInt, hinc⟩
    exact ⟨(hinterval a b).1.mpr hInt, hinc.trans (hinterval a b).2.symm⟩

/-- REG.54: the complete existential right-hand side of public T08 is
invariant, using the same primitive witness in either direction.-/
theorem finiteEndpoint_exists_primitive_iff
    {f ftilde : ℝ → E} {k : ℝ} {S : Finset ℝ} {I : E}
    (hEq : Set.EqOn f ftilde ({k} ∪ (↑S : Set ℝ))ᶜ) :
    (∃ F : ℝ → E,
        IsFiniteExceptionalPrimitive f k S F ∧
          Tendsto F atTop (nhds I)) ↔
      ∃ F : ℝ → E,
        IsFiniteExceptionalPrimitive ftilde k S F ∧
          Tendsto F atTop (nhds I) := by
  constructor
  · rintro ⟨F, hF, hlim⟩
    exact ⟨F, (finiteEndpoint_primitive_iff hEq).mp hF, hlim⟩
  · rintro ⟨F, hF, hlim⟩
    exact ⟨F, (finiteEndpoint_primitive_iff hEq).mpr hF, hlim⟩

/-- REG.52 / IMP-R24: T01 is invariant at every proposed value. The proof
uses only the public T08 equivalence and the fixed-primitive transport above;
it does not inspect T01's private component representation.-/
theorem finiteEndpoint_update_iff
    {f ftilde : ℝ → E} {k : ℝ} {S : Finset ℝ} {I : E}
    (hEq : Set.EqOn f ftilde ({k} ∪ (↑S : Set ℝ))ᶜ) :
    HasImproperIntegralAtTopExcept f k S I ↔
      HasImproperIntegralAtTopExcept ftilde k S I := by
  calc
    HasImproperIntegralAtTopExcept f k S I ↔
        ∃ F : ℝ → E,
          IsFiniteExceptionalPrimitive f k S F ∧
            Tendsto F atTop (nhds I) :=
      hasImproperIntegralAtTopExcept_iff_exists_primitive
    _ ↔ ∃ F : ℝ → E,
          IsFiniteExceptionalPrimitive ftilde k S F ∧
            Tendsto F atTop (nhds I) :=
      finiteEndpoint_exists_primitive_iff hEq
    _ ↔ HasImproperIntegralAtTopExcept ftilde k S I :=
      hasImproperIntegralAtTopExcept_iff_exists_primitive.symm

/-- The explicit two-sided T07 regression. Integrability of either endpoint
version gives honest `IntegrableOn` witnesses for both versions, their set
integrals agree, and public T07 supplies both corresponding T01 relations.-/
theorem finiteEndpoint_t07_transport
    {f ftilde : ℝ → E} {k : ℝ} {S : Finset ℝ}
    (hEq : Set.EqOn f ftilde ({k} ∪ (↑S : Set ℝ))ᶜ)
    (hS : ∀ c ∈ S, k < c)
    (hInt : IntegrableOn f (Ioi k) ∨ IntegrableOn ftilde (Ioi k)) :
    IntegrableOn f (Ioi k) ∧
      IntegrableOn ftilde (Ioi k) ∧
      (∫ t in Ioi k, f t) = ∫ t in Ioi k, ftilde t ∧
      HasImproperIntegralAtTopExcept f k S (∫ t in Ioi k, f t) ∧
      HasImproperIntegralAtTopExcept ftilde k S
        (∫ t in Ioi k, ftilde t) := by
  have hIoi := finiteEndpoint_Ioi_invariance hEq
  have hf : IntegrableOn f (Ioi k) := hInt.elim id hIoi.1.mpr
  have hftilde : IntegrableOn ftilde (Ioi k) := hIoi.1.mp hf
  exact ⟨hf, hftilde, hIoi.2,
    HasImproperIntegralAtTopExcept.of_integrableOn_Ioi f k S hS hf,
    HasImproperIntegralAtTopExcept.of_integrableOn_Ioi ftilde k S hS hftilde⟩

end LMLFTest.Integral.Improper
