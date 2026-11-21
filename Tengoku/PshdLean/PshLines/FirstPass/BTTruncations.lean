import Tengoku.PshdLean.PshLines.FirstPass.MongeAmpere
import Tengoku.PshdLean.PshLines.LocalPshDiscControl

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual extended-real PSH truncations

Truncate before taking `toReal`: at a pole the representative is `-k`, not
`max 0 (-k)`. Strict superlevel loci are Borel; they need not be ordinary open
sets. No Bedford–Taylor existence or locality theorem is imported here.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology

namespace PshLines.FirstPass.MongeAmpere

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}

/-- The maximum is taken in the extended reals, including at poles.-/
def truncation (u : ComplexModel n → EReal) (k : ℕ) (z : ComplexModel n) : EReal :=
  max (u z) ((-(k : ℝ) : ℝ) : EReal)

/-- The real representative of the already truncated potential.-/
def truncationReal (u : ComplexModel n → EReal) (k : ℕ) (z : ComplexModel n) : ℝ :=
  (truncation u k z).toReal

/-- The strict truncation locus inside the given domain.-/
def strictTruncationLocus (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → EReal) (k : ℕ) : Set (ComplexModel n) :=
  {z | z ∈ Ω ∧ ((-(k : ℝ) : ℝ) : EReal) < u z}

/--
@isnad1 id=le.0h4v.s5.e9f347d688c0 from=translated src=- shape=573246dc vocab=718e16f6
-/
theorem truncation_lower_bound (u : ComplexModel n → EReal) (k : ℕ)
    (z : ComplexModel n) : ((-(k : ℝ) : ℝ) : EReal) ≤ truncation u k z :=
  le_max_right _ _

/--
@isnad1 id=ne.0h4v.s4.5bb5fa74143b from=translated src=- shape=b94962ba vocab=32911a4c
-/
theorem truncation_ne_bot (u : ComplexModel n → EReal) (k : ℕ)
    (z : ComplexModel n) : truncation u k z ≠ ⊥ :=
  ne_of_gt ((EReal.bot_lt_coe _).trans_le (truncation_lower_bound u k z))

/--
@isnad1 id=ne.2h5v.s8.75cd093c3fa2 from=translated src=- shape=b1ea66b4 vocab=957e5b1d
-/
theorem truncation_ne_top (hu : PlurisubharmonicOn u Ω) (k : ℕ)
    {z : ComplexModel n} (hz : z ∈ Ω) : truncation u k z ≠ ⊤ := by
  exact ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hu z hz).ne_top)
    (EReal.coe_lt_top _))

/--
@isnad1 id=eq.2h5v.s8.df614974abc0 from=translated src=- shape=45eba0d1 vocab=bd44037e
-/
theorem coe_truncationReal (hu : PlurisubharmonicOn u Ω) (k : ℕ)
    {z : ComplexModel n} (hz : z ∈ Ω) :
    (truncationReal u k z : EReal) = truncation u k z :=
  EReal.coe_toReal (truncation_ne_top hu k hz) (truncation_ne_bot u k z)

/--
@isnad1 id=plurisub.1h4v.s8.1bb33514aa01 from=translated src=- shape=84782134 vocab=5e4df783
-/
theorem truncation_plurisubharmonicOn (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    PlurisubharmonicOn (truncation u k) Ω :=
  hu.max (fun z _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) z)

/--
@isnad1 id=plurisub.1h4v.s8.3cdf490ed738 from=translated src=- shape=1750d955 vocab=57600e23
-/
theorem truncationReal_plurisubharmonicOn (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    PlurisubharmonicOn (fun z => (truncationReal u k z : EReal)) Ω := by
  intro z hz
  apply (truncation_plurisubharmonicOn hu k z hz).congr
  filter_upwards [Ω.isOpen.mem_nhds hz] with w hw
  exact (coe_truncationReal hu k hw).symm

/--
@isnad1 id=eq.1h4v.s5.c016d4e22306 from=translated src=- shape=39f342e5 vocab=86ac4c64
-/
@[simp] theorem truncation_at_pole (k : ℕ) {z : ComplexModel n} (hz : u z = ⊥) :
    truncation u k z = ((-(k : ℝ) : ℝ) : EReal) := by
  simp [truncation, hz]

/--
@isnad1 id=eq.1h4v.s5.99f1e8200cb9 from=translated src=- shape=f82d5d84 vocab=f3fb303e
-/
theorem truncationReal_at_pole (k : ℕ) {z : ComplexModel n} (hz : u z = ⊥) :
    truncationReal u k z = -(k : ℝ) := by
  unfold truncationReal
  rw [truncation_at_pole k hz]
  exact EReal.toReal_coe _

/--
@isnad1 id=eqon.0h4v.s5.21070bc60b91 from=translated src=- shape=e9e856d6 vocab=ea012d03
-/
theorem truncation_eq_on_strictLocus (k : ℕ) :
    EqOn (truncation u k) u (strictTruncationLocus Ω u k) :=
  fun _ hz => max_eq_left hz.2.le

/--
@isnad1 id=eqon.0h4v.s6.b972885bd58b from=translated src=- shape=698e9970 vocab=3d35a087
-/
theorem truncationReal_eq_on_strictLocus (k : ℕ) :
    EqOn (truncationReal u k) (fun z => (u z).toReal)
      (strictTruncationLocus Ω u k) :=
  fun _ hz => congrArg EReal.toReal (truncation_eq_on_strictLocus k hz)

/--
@isnad1 id=not.1h5v.s6.9eddf9e1dcad from=translated src=- shape=e1d3a085 vocab=eaf1fd27
-/
theorem pole_not_mem_strictLocus (k : ℕ) {z : ComplexModel n} (hz : u z = ⊥) :
    z ∉ strictTruncationLocus Ω u k := by
  simp [strictTruncationLocus, hz]

/--
@isnad1 id=antitone.0h3v.s4.5df4c26d39b2 from=translated src=- shape=504747a3 vocab=ab220d67
-/
theorem truncation_antitone (u : ComplexModel n → EReal) (z : ComplexModel n) :
    Antitone (fun k => truncation u k z) := by
  intro k l hkl
  apply max_le_max le_rfl
  exact EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))

/--
@isnad1 id=antitone.2h4v.s8.859b49d6cc6e from=translated src=- shape=2837855f vocab=466dbd8f
-/
theorem truncationReal_antitone (hu : PlurisubharmonicOn u Ω)
    {z : ComplexModel n} (hz : z ∈ Ω) : Antitone (fun k => truncationReal u k z) := by
  intro k l hkl
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncationReal hu l hz, coe_truncationReal hu k hz]
  exact truncation_antitone u z hkl

/--
@isnad1 id=monotone.0h3v.s6.e51b1b1756b8 from=translated src=- shape=5a984a11 vocab=51c42e2a
-/
theorem strictTruncationLocus_mono (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → EReal) : Monotone (strictTruncationLocus Ω u) := by
  intro k l hkl z hz
  refine ⟨hz.1, lt_of_le_of_lt ?_ hz.2⟩
  exact EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))

/--
@isnad1 id=eq.1h4v.s5.c7ed7c1860d7 from=translated src=- shape=023c959a vocab=447c277e
-/
theorem truncation_truncation (u : ComplexModel n → EReal) {k l : ℕ}
    (hkl : k ≤ l) : truncation (truncation u l) k = truncation u k := by
  funext z
  have h : ((-(l : ℝ) : ℝ) : EReal) ≤ ((-(k : ℝ) : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))
  simp only [truncation, max_assoc, max_eq_right h]

/-- Nested truncation, expressed in the finite real representatives on Ω.
@isnad1 id=eq.3h6v.s8.b4a2460bc326 from=translated src=- shape=d27ad4cc vocab=7e92b9cf
-/
theorem truncationReal_nested (hu : PlurisubharmonicOn u Ω) {k l : ℕ}
    (hkl : k ≤ l) {z : ComplexModel n} (hz : z ∈ Ω) :
    max (truncationReal u l z) (-(k : ℝ)) = truncationReal u k z := by
  apply EReal.coe_injective
  have hmax (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
    · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.mpr h)]
  rw [hmax, coe_truncationReal hu l hz, coe_truncationReal hu k hz]
  exact congrFun (truncation_truncation u hkl) z

/--
@isnad1 id=eq.2h5v.s8.5e58e2baa4b8 from=translated src=- shape=f834fdeb vocab=d2012d93
-/
theorem strictLocus_eq_truncationReal_superlevel (hu : PlurisubharmonicOn u Ω)
    {k l : ℕ} (hkl : k ≤ l) :
    strictTruncationLocus Ω u k = {z | z ∈ Ω ∧ -(k : ℝ) < truncationReal u l z} := by
  ext z
  by_cases hz : z ∈ Ω
  · have h : ((-(l : ℝ) : ℝ) : EReal) ≤ ((-(k : ℝ) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))
    simp only [strictTruncationLocus, mem_ofPred_eq, hz, true_and]
    rw [← EReal.coe_lt_coe_iff, coe_truncationReal hu l hz]
    simp only [truncation, lt_max_iff, not_lt.mpr h, or_false]
  · simp [strictTruncationLocus, hz]

/-- Borel measurability comes from upper semicontinuity on the open subtype,
not from a claim that a strict superlevel set is ordinary open.
@isnad1 id=measurab.1h4v.s8.7d61cd31ce8b from=translated src=- shape=dbbb2834 vocab=dffdd328
-/
theorem measurableSet_strictTruncationLocus (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    MeasurableSet (strictTruncationLocus Ω u k) := by
  have hsc : UpperSemicontinuousOn (fun z : Ω => u z) univ :=
    hu.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun z _ => z.property)
  have hm : Measurable (fun z : Ω => u z) :=
    (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  have hs := Ω.isOpen.measurableSet.subtype_image
    (hm measurableSet_Ioi : MeasurableSet {z : Ω | ((-(k : ℝ) : ℝ) : EReal) < u z})
  convert hs using 1
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩

/-- Compact upper bounds and the truncation floor give local absolute bounds.
@isnad1 id=islocall.1h4v.s7.ef5d4411fbcf from=translated src=- shape=f733147d vocab=66ee7011
-/
theorem truncationReal_isLocallyBoundedPshOn (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    IsLocallyBoundedPshOn Ω (truncationReal u k) := by
  refine ⟨truncationReal_plurisubharmonicOn hu k, ?_⟩
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hz)
  have hclosed : closedBall z (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC0, hC⟩ := hu.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z (r / 2)) hclosed
  refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
    ball_subset_closedBall.trans hclosed, C + (k : ℝ), ?_⟩
  intro w hw
  have hwΩ := hclosed (ball_subset_closedBall hw)
  have hlo : -(k : ℝ) ≤ truncationReal u k w := by
    apply EReal.coe_le_coe_iff.mp
    rw [coe_truncationReal hu k hwΩ]
    exact truncation_lower_bound u k w
  have hhi : truncationReal u k w ≤ C := by
    apply EReal.coe_le_coe_iff.mp
    rw [coe_truncationReal hu k hwΩ]
    exact max_le (hC w (ball_subset_closedBall hw))
      (EReal.coe_le_coe_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  exact abs_le.mpr ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) k]⟩

/-- The strict levels exhaust precisely the domain outside the pole set.
This order-theoretic identity also holds for arbitrary extended-real functions.
@isnad1 id=eq.0h3v.s7.3659b244f7aa from=translated src=- shape=227314ee vocab=2527685b
-/
theorem iUnion_strictTruncationLocus (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → EReal) :
    (⋃ k, strictTruncationLocus Ω u k) = {z | z ∈ Ω ∧ u z ≠ ⊥} := by
  ext z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    exact ⟨hk.1, ne_of_gt ((EReal.bot_lt_coe (-(k : ℝ))).trans hk.2)⟩
  · rintro ⟨hz, hu⟩
    obtain ⟨r, _, hr⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hu)
    obtain ⟨k, hk⟩ := exists_nat_gt (-r)
    refine mem_iUnion.mpr ⟨k, hz, ?_⟩
    exact (EReal.coe_lt_coe_iff.mpr (show -(k : ℝ) < r by linarith)).trans hr

end PshLines.FirstPass.MongeAmpere
