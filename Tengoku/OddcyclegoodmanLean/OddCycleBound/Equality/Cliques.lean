import Tengoku.OddcyclegoodmanLean.OddCycleBound.Equality.SpectralStep
import Tengoku.OddcyclegoodmanLean.OddCycleBound.KPartite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The clique decomposition in the proof of Proposition 6.2

Let `U` be an a.e. `q`-regular graphon (`q > 0`) that is `{0,1}`-valued a.e. and satisfies
`∫ U(x,z) U(z,y) dz = q U(x,y)` for a.e. `(x,y)` (equation `eq:equal-neighbourhoods`).
Instead of the paper's iterative block construction we use the relation "the neighbourhoods
`N(x)` and `N(y)` agree up to a null set": it is an equivalence relation, `U` is a.e. the
indicator of this relation, almost every class has measure `q`, and a maximal family of
pairwise inequivalent points of this kind indexes the classes. This yields a measurable,
measure-preserving `φ : Ω → Fin k` with `kq = 1` and `U(x,y) = [φ x = φ y]` a.e.
-/

open MeasureTheory
open scoped ENNReal

namespace OddCycleBound.Equality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- `x` and `y` have the same neighbourhood up to a null set.-/
def SameNbhd (μ : Measure Ω) (U : Ω → Ω → ℝ) (x y : Ω) : Prop := ∀ᵐ z ∂μ, U x z = U y z

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=samenbhd.1h5v.s5.213607277606 from=translated src=- shape=37c1ccbd vocab=736f01c3
-/
lemma SameNbhd.symm {x y : Ω} (h : SameNbhd μ U x y) : SameNbhd μ U y x :=
  h.mono fun _ hz => hz.symm

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=samenbhd.2h6v.s5.046735439f45 from=translated src=- shape=1f4368d4 vocab=736f01c3
-/
lemma SameNbhd.trans {x y z : Ω} (h1 : SameNbhd μ U x y) (h2 : SameNbhd μ U y z) :
    SameNbhd μ U x z := by
  filter_upwards [h1, h2] with w hw1 hw2
  rw [hw1, hw2]

/--
@isnad1 id=measurab.1h3v.s6.6da9d9c6c058 from=translated src=- shape=0258669d vocab=3669d7d6
-/
lemma measurableSet_sameNbhd (hU : Measurable (Function.uncurry U)) :
    MeasurableSet {p : Ω × Ω | SameNbhd μ U p.1 p.2} := by
  set D : Set ((Ω × Ω) × Ω) := {r | U r.1.1 r.2 ≠ U r.1.2 r.2} with hDdef
  have hD : MeasurableSet D := by
    have h1 : Measurable fun r : (Ω × Ω) × Ω => U r.1.1 r.2 :=
      hU.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun r : (Ω × Ω) × Ω => U r.1.2 r.2 :=
      hU.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (measurableSet_eq_fun h1 h2).compl
  have hmeas := measurable_measure_prodMk_left (ν := μ) hD
  have hset : {p : Ω × Ω | SameNbhd μ U p.1 p.2} =
      (fun p => μ (Prod.mk p ⁻¹' D)) ⁻¹' {0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, SameNbhd, ae_iff,
      hDdef]
    rfl
  rw [hset]
  exact hmeas (measurableSet_singleton 0)

/-- The neighbourhood class of `x`.-/
def nbhdClass (μ : Measure Ω) (U : Ω → Ω → ℝ) (x : Ω) : Set Ω := {y | SameNbhd μ U x y}

/--
@isnad1 id=measurab.1h4v.s5.080e903c7dbb from=translated src=- shape=d934c252 vocab=9f276c26
-/
lemma measurableSet_nbhdClass (hU : Measurable (Function.uncurry U)) (x : Ω) :
    MeasurableSet (nbhdClass μ U x) :=
  measurable_prodMk_left (measurableSet_sameNbhd (μ := μ) hU)

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=disjoint.1h5v.s6.897dcc750977 from=translated src=- shape=61d2cd1d vocab=88e22d6b
-/
lemma disjoint_nbhdClass {x y : Ω} (h : ¬ SameNbhd μ U x y) :
    Disjoint (nbhdClass μ U x) (nbhdClass μ U y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h (SameNbhd.trans hzx (SameNbhd.symm hzy))

open Classical in
/-- Under the hypotheses of the clique decomposition, `U` is a.e. the indicator of the relation
`SameNbhd`.
@isnad1 id=eventual.5h4v.s8.645390986e73 from=translated src=- shape=13be35f5 vocab=393e3b47
-/
lemma ae_eq_ite_sameNbhd (hU : IsGraphon U μ) {q : ℝ} (hq : 0 < q)
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q)
    (h01 : ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = 0 ∨ U p.1 p.2 = 1)
    (hsq : ∀ᵐ p ∂(μ.prod μ), comp μ U U p.1 p.2 = q * U p.1 p.2) :
    ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = if SameNbhd μ U p.1 p.2 then 1 else 0 := by
  have hGU := goodK_of_isGraphon hU
  have hrow : ∀ᵐ x ∂μ, (∀ᵐ z ∂μ, U x z = 0 ∨ U x z = 1) ∧ degree U μ x = q := by
    filter_upwards [Measure.ae_ae_of_ae_prod h01, hdeg] with x hx1 hx2 using ⟨hx1, hx2⟩
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hrow
  have hsnd := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hrow
  filter_upwards [h01, hsq, hfst, hsnd] with p h1 h2 h3 h4
  obtain ⟨x, y⟩ := p
  simp only at h1 h2 h3 h4 ⊢
  have hsq_row : ∀ w, (∀ᵐ z ∂μ, U w z = 0 ∨ U w z = 1) → degree U μ w = q →
      ∫ z, U w z * U w z ∂μ = q := fun w hw hdw => by
    rw [← hdw, degree]
    refine integral_congr_ae (hw.mono fun z hz => ?_)
    rcases hz with h | h <;> simp [h]
  have hxx := hsq_row x h3.1 h3.2
  have hyy := hsq_row y h4.1 h4.2
  have hxy : ∫ z, U x z * U y z ∂μ = q * U x y := by
    rw [← h2]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hU.symm y z]
  have hIx := hGU.integrable_row (μ := μ) x
  have hIy := hGU.integrable_row (μ := μ) y
  have hmul : ∀ a b : Ω, Integrable (fun z => U a z * U b z) μ := fun a b =>
    integrable_Uf hU ⟨(hGU.meas.comp measurable_prodMk_left).stronglyMeasurable,
      ⟨1, zero_le_one, fun z => by
        show |U b z| ≤ 1
        rw [abs_of_nonneg (hU.nonneg b z)]; exact hU.le_one b z⟩⟩ a
  have hD : ∫ z, (U x z - U y z) ^ 2 ∂μ = 2 * q - 2 * q * U x y := by
    have e : (fun z => (U x z - U y z) ^ 2) =
        fun z => U x z * U x z - 2 * (U x z * U y z) + U y z * U y z := by
      funext z; ring
    have hJ1 : Integrable (fun z => 2 * (U x z * U y z)) μ := (hmul x y).const_mul _
    have hJ : Integrable (fun z => U x z * U x z - 2 * (U x z * U y z)) μ := (hmul x x).sub hJ1
    rw [e, integral_add hJ (hmul y y), integral_sub (hmul x x) hJ1, integral_const_mul, hxx, hyy,
      hxy]
    ring
  have hIsq : Integrable (fun z => (U x z - U y z) ^ 2) μ := by
    have e : (fun z => (U x z - U y z) ^ 2) =
        fun z => U x z * U x z - 2 * (U x z * U y z) + U y z * U y z := by
      funext z; ring
    rw [e]
    have hJ1 : Integrable (fun z => 2 * (U x z * U y z)) μ := (hmul x y).const_mul _
    have hJ : Integrable (fun z => U x z * U x z - 2 * (U x z * U y z)) μ := (hmul x x).sub hJ1
    exact hJ.add (hmul y y)
  rcases h1 with h | h
  · rw [h, ite_eq_right]
    intro hsame
    have h0 : ∫ z, (U x z - U y z) ^ 2 ∂μ = 0 := by
      refine integral_eq_zero_of_ae (hsame.mono fun z hz => ?_)
      simp [hz]
    rw [hD, h] at h0
    linarith
  · rw [h, ite_eq_left]
    have h0 : ∫ z, (U x z - U y z) ^ 2 ∂μ = 0 := by rw [hD, h]; ring
    rw [integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hIsq] at h0
    filter_upwards [h0] with z hz
    have : (U x z - U y z) ^ 2 = 0 := hz
    have := pow_eq_zero_iff two_ne_zero |>.mp this
    linarith

/--
@isnad1 id=eventual.5h4v.s7.279e7df0c225 from=translated src=- shape=42ca4845 vocab=4d5973ec
-/
lemma ae_measureReal_nbhdClass (hU : IsGraphon U μ) {q : ℝ} (hq : 0 < q)
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q)
    (h01 : ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = 0 ∨ U p.1 p.2 = 1)
    (hsq : ∀ᵐ p ∂(μ.prod μ), comp μ U U p.1 p.2 = q * U p.1 p.2) :
    ∀ᵐ x ∂μ, μ.real (nbhdClass μ U x) = q := by
  have hchar := ae_eq_ite_sameNbhd hU hq hdeg h01 hsq
  filter_upwards [Measure.ae_ae_of_ae_prod hchar, hdeg] with x hx hdx
  rw [← hdx, degree, integral_congr_ae hx,
    ← integral_indicator_one (measurableSet_nbhdClass (μ := μ) hU.meas x)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases h : SameNbhd μ U x y
  · simp [Set.indicator, nbhdClass, h]
  · simp [Set.indicator, nbhdClass, h]

section Family

variable (μ U) in
/-- A family of `n` pairwise inequivalent points whose classes have measure `q`.-/
def GoodFamily (q : ℝ) (n : ℕ) : Prop :=
  ∃ e : Fin n → Ω, (∀ i, μ.real (nbhdClass μ U (e i)) = q) ∧
    Pairwise fun i j => ¬ SameNbhd μ U (e i) (e j)

/--
@isnad1 id=eq.3h6v.s6.b8945c62ffee from=translated src=- shape=4e3ce279 vocab=bdd2217d
-/
lemma measureReal_iUnion_family (hU : Measurable (Function.uncurry U)) {q : ℝ} {n : ℕ}
    {e : Fin n → Ω} (he : ∀ i, μ.real (nbhdClass μ U (e i)) = q)
    (hdist : Pairwise fun i j => ¬ SameNbhd μ U (e i) (e j)) :
    μ.real (⋃ i, nbhdClass μ U (e i)) = n * q := by
  rw [measureReal_iUnion_fintype (fun i j hij => disjoint_nbhdClass (hdist hij))
    (fun i => measurableSet_nbhdClass hU (e i))]
  simp [he]

/--
@isnad1 id=le.2h5v.s6.bcb57143e6da from=translated src=- shape=d98b216f vocab=c056118e
-/
lemma GoodFamily.card_mul_le (hU : Measurable (Function.uncurry U)) {q : ℝ} {n : ℕ}
    (h : GoodFamily μ U q n) : (n : ℝ) * q ≤ 1 := by
  obtain ⟨e, he, hdist⟩ := h
  rw [← measureReal_iUnion_family hU he hdist]
  exact measureReal_le_one

end Family

end OddCycleBound.Equality
