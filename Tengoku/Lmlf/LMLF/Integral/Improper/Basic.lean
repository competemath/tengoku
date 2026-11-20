import Tengoku.Seed.Data.Finset.Sort
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace LMLF.Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def HasImproperIntegralTailFromBreaks
    [CompleteSpace E] (f : ℝ → E) (c : ℝ) : List ℝ → E → Prop
  | [], I =>
      ∃ d : ℝ, ∃ L R : E, c < d ∧
        (∀ {a b : ℝ}, c < a → a ≤ b →
          IntervalIntegrable f volume a b) ∧
        Tendsto (fun a => ∫ t in a..d, f t)
          (nhdsWithin c (Ioi c)) (nhds L) ∧
        Tendsto (fun b => ∫ t in d..b, f t) atTop (nhds R) ∧
        I = L + R
  | d :: ds, I =>
      ∃ p : ℝ, ∃ L R J : E, c < p ∧ p < d ∧
        (∀ {a b : ℝ}, c < a → a ≤ b → b < d →
          IntervalIntegrable f volume a b) ∧
        Tendsto (fun a => ∫ t in a..p, f t)
          (nhdsWithin c (Ioi c)) (nhds L) ∧
        Tendsto (fun b => ∫ t in p..b, f t)
          (nhdsWithin d (Iio d)) (nhds R) ∧
        HasImproperIntegralTailFromBreaks f d ds J ∧
        I = L + R + J

private def HasImproperIntegralAtTopBreaks
    [CompleteSpace E] (f : ℝ → E) (k : ℝ) : List ℝ → E → Prop
  | [], I =>
      (∀ {b : ℝ}, k ≤ b → IntervalIntegrable f volume k b) ∧
      Tendsto (fun b => ∫ t in k..b, f t) atTop (nhds I)
  | c :: cs, I =>
      ∃ L J : E, k < c ∧
        (∀ {b : ℝ}, k ≤ b → b < c →
          IntervalIntegrable f volume k b) ∧
        Tendsto (fun b => ∫ t in k..b, f t)
          (nhdsWithin c (Iio c)) (nhds L) ∧
        HasImproperIntegralTailFromBreaks f c cs J ∧
        I = L + J

/-- IMP-001-T01.-/
def HasImproperIntegralAtTopExcept
    [CompleteSpace E] (f : ℝ → E) (k : ℝ) (S : Finset ℝ) (I : E) : Prop :=
  (∀ c ∈ S, k < c) ∧
    HasImproperIntegralAtTopBreaks f k (S.sort (· ≤ ·)) I

/-- IMP-001-T05.-/
def IsFiniteExceptionalPrimitive
    [CompleteSpace E] (g : ℝ → E) (k : ℝ) (S : Finset ℝ) (F : ℝ → E) : Prop :=
  (∀ c ∈ S, k < c) ∧
    ContinuousOn F (Ici k) ∧
    F k = 0 ∧
    ∀ {a b : ℝ}, k ≤ a → a ≤ b →
      Disjoint (Icc a b) (↑S : Set ℝ) →
      IntervalIntegrable g volume a b ∧
        F b - F a = ∫ t in a..b, g t

private def IsTailPrimitiveFromBreaks
    [CompleteSpace E] (f : ℝ → E) (c : ℝ) (cs : List ℝ) (F : ℝ → E) : Prop :=
  ContinuousOn F (Ici c) ∧
    F c = 0 ∧
    ∀ {a b : ℝ}, c < a → a ≤ b →
      Disjoint (Icc a b) (↑cs.toFinset : Set ℝ) →
      IntervalIntegrable f volume a b ∧
        F b - F a = ∫ t in a..b, f t

omit [NormedSpace ℝ E] in
private theorem intervalIntegrable_anchor
    [CompleteSpace E] {f : ℝ → E} {c d p x : ℝ}
    (hcp : c < p) (hpd : p < d) (hcx : c < x) (hxd : x < d)
    (hInt : ∀ {a b : ℝ}, c < a → a ≤ b → b < d →
      IntervalIntegrable f volume a b) :
    IntervalIntegrable f volume p x := by
  rcases le_total p x with hpx | hxp
  · exact hInt hcp hpx hxd
  · exact (hInt hcx hxp hpd).symm

private def boundedComponentPrimitive
    [CompleteSpace E] (f : ℝ → E) (c d p : ℝ) (L R : E) (x : ℝ) : E :=
  if x ≤ c then 0 else if d ≤ x then L + R else L + ∫ t in p..x, f t

private theorem boundedComponentPrimitive_spec
    [CompleteSpace E] {f : ℝ → E} {c d p : ℝ} {L R : E}
    (hcp : c < p) (hpd : p < d)
    (hInt : ∀ {a b : ℝ}, c < a → a ≤ b → b < d →
      IntervalIntegrable f volume a b)
    (hL : Tendsto (fun a => ∫ t in a..p, f t)
      (nhdsWithin c (Ioi c)) (nhds L))
    (hR : Tendsto (fun b => ∫ t in p..b, f t)
      (nhdsWithin d (Iio d)) (nhds R)) :
    let P := boundedComponentPrimitive f c d p L R
    ContinuousOn P (Icc c d) ∧ P c = 0 ∧ P d = L + R ∧
      (∀ {a b : ℝ}, c < a → a ≤ b → b < d →
        IntervalIntegrable f volume a b ∧
          P b - P a = ∫ t in a..b, f t) := by
  let P := boundedComponentPrimitive f c d p L R
  change ContinuousOn P (Icc c d) ∧ P c = 0 ∧ P d = L + R ∧ _
  have hcd : c < d := hcp.trans hpd
  have hPc : P c = 0 := by simp [P, boundedComponentPrimitive]
  have hPd : P d = L + R := by
    simp [P, boundedComponentPrimitive, not_le_of_gt hcd]
  have hPmid : ∀ {x : ℝ}, c < x → x < d →
      P x = L + ∫ t in p..x, f t := by
    intro x hcx hxd
    simp [P, boundedComponentPrimitive, not_le_of_gt hcx, not_le_of_gt hxd]
  have hcont : ContinuousOn P (Icc c d) := by
    intro x hx
    rcases hx with ⟨hcx, hxd⟩
    rcases eq_or_lt_of_le hcx with rfl | hcx'
    · apply (continuousWithinAt_Ioi_iff_Ici.mp ?_).mono Icc_subset_Ici_self
      rw [ContinuousWithinAt, hPc]
      have ht := hL.neg.const_add L
      have ht' : Tendsto (fun x => L + -(∫ t in x..p, f t))
          (nhdsWithin c (Ioi c)) (nhds 0) := by simpa using ht
      exact ht'.congr' (by
        filter_upwards [eventually_mem_nhdsWithin,
          eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hcd)] with y hyc hyd
        show L + -(∫ t in y..p, f t) = P y
        rw [hPmid hyc hyd]
        rw [intervalIntegral.integral_symm p y]
        simp only [neg_neg])
    · rcases eq_or_lt_of_le hxd with rfl | hxd'
      · apply (continuousWithinAt_Iio_iff_Iic.mp ?_).mono Icc_subset_Iic_self
        rw [ContinuousWithinAt, hPd]
        exact (hR.const_add L).congr' (by
          filter_upwards [eventually_mem_nhdsWithin,
            eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hcd)] with y hyd hyc
          rw [hPmid hyc hyd])
      · have hl : c < (c + min p x) / 2 := by
          have : c < min p x := lt_min hcp hcx'
          linarith
        have hlx : (c + min p x) / 2 < x := by
          have : min p x ≤ x := min_le_right _ _
          linarith
        have hp_l : (c + min p x) / 2 ≤ p := by
          have : min p x ≤ p := min_le_left _ _
          linarith
        have hr : (max p x + d) / 2 < d := by
          have : max p x < d := max_lt hpd hxd'
          linarith
        have hxr : x < (max p x + d) / 2 := by
          have : x ≤ max p x := le_max_right _ _
          linarith
        have hp_r : p ≤ (max p x + d) / 2 := by
          have : p ≤ max p x := le_max_left _ _
          linarith
        have hlocalInt : IntervalIntegrable f volume
            ((c + min p x) / 2) ((max p x + d) / 2) :=
          hInt hl (hlx.le.trans hxr.le) hr
        have hbaseOn :=
          (intervalIntegral.continuousOn_primitive_interval' hlocalInt
            (by simpa [uIcc_of_le (hlx.le.trans hxr.le)] using ⟨hp_l, hp_r⟩)).const_add L
        have hnb : [[(c + min p x) / 2, (max p x + d) / 2]] ∈ nhds x := by
          rw [uIcc_of_le (hlx.le.trans hxr.le)]
          exact Icc_mem_nhds hlx hxr
        have hbase : ContinuousAt (fun y => L + ∫ t in p..y, f t) x :=
          hbaseOn.continuousAt hnb
        exact (hbase.congr (by
          filter_upwards [Ioo_mem_nhds hcx' hxd'] with y hy
          exact (hPmid hy.1 hy.2).symm)).continuousWithinAt
  refine ⟨hcont, hPc, hPd, ?_⟩
  intro a b hca hab hbd
  have habInt := hInt hca hab hbd
  have hpaInt := intervalIntegrable_anchor hcp hpd hca (hab.trans_lt hbd) hInt
  have hpbInt := intervalIntegrable_anchor hcp hpd (hca.trans_le hab) hbd hInt
  refine ⟨habInt, ?_⟩
  change P b - P a = _
  rw [hPmid (hca.trans_le hab) hbd, hPmid hca (hab.trans_lt hbd)]
  simpa [add_sub_add_left_eq_sub] using
    intervalIntegral.integral_interval_sub_left hpbInt hpaInt

private def finalComponentPrimitive
    [CompleteSpace E] (f : ℝ → E) (c p : ℝ) (L : E) (x : ℝ) : E :=
  if x ≤ c then 0 else L + ∫ t in p..x, f t

private theorem finalComponentPrimitive_spec
    [CompleteSpace E] {f : ℝ → E} {c p : ℝ} {L R : E}
    (hcp : c < p)
    (hInt : ∀ {a b : ℝ}, c < a → a ≤ b →
      IntervalIntegrable f volume a b)
    (hL : Tendsto (fun a => ∫ t in a..p, f t)
      (nhdsWithin c (Ioi c)) (nhds L))
    (hR : Tendsto (fun b => ∫ t in p..b, f t) atTop (nhds R)) :
    let P := finalComponentPrimitive f c p L
    ContinuousOn P (Ici c) ∧ P c = 0 ∧
      (∀ {a b : ℝ}, c < a → a ≤ b →
        IntervalIntegrable f volume a b ∧
          P b - P a = ∫ t in a..b, f t) ∧
      Tendsto P atTop (nhds (L + R)) := by
  let P := finalComponentPrimitive f c p L
  change ContinuousOn P (Ici c) ∧ P c = 0 ∧ _
  have hPc : P c = 0 := by simp [P, finalComponentPrimitive]
  have hPmid : ∀ {x : ℝ}, c < x → P x = L + ∫ t in p..x, f t := by
    intro x hcx
    simp [P, finalComponentPrimitive, not_le_of_gt hcx]
  have hcont : ContinuousOn P (Ici c) := by
    intro x hcx
    change c ≤ x at hcx
    rcases eq_or_lt_of_le hcx with rfl | hcx'
    · apply continuousWithinAt_Ioi_iff_Ici.mp
      rw [ContinuousWithinAt, hPc]
      have ht := hL.neg.const_add L
      have ht' : Tendsto (fun x => L + -(∫ t in x..p, f t))
          (nhdsWithin c (Ioi c)) (nhds 0) := by simpa using ht
      exact ht'.congr' (by
        filter_upwards [eventually_mem_nhdsWithin] with y hyc
        show L + -(∫ t in y..p, f t) = P y
        rw [hPmid hyc]
        rw [intervalIntegral.integral_symm p y]
        simp only [neg_neg])
    · have hl : c < (c + min p x) / 2 := by
        have : c < min p x := lt_min hcp hcx'
        linarith
      have hlx : (c + min p x) / 2 < x := by
        have : min p x ≤ x := min_le_right _ _
        linarith
      have hp_l : (c + min p x) / 2 ≤ p := by
        have : min p x ≤ p := min_le_left _ _
        linarith
      let r := max p x + 1
      have hxr : x < r := by
        dsimp [r]
        have : x ≤ max p x := le_max_right _ _
        linarith
      have hp_r : p ≤ r := by
        dsimp [r]
        have : p ≤ max p x := le_max_left _ _
        linarith
      have hlocalInt : IntervalIntegrable f volume ((c + min p x) / 2) r :=
        hInt hl (hlx.le.trans hxr.le)
      have hbaseOn :=
        (intervalIntegral.continuousOn_primitive_interval' hlocalInt
          (by simpa [uIcc_of_le (hlx.le.trans hxr.le)] using ⟨hp_l, hp_r⟩)).const_add L
      have hnb : [[(c + min p x) / 2, r]] ∈ nhds x := by
        rw [uIcc_of_le (hlx.le.trans hxr.le)]
        exact Icc_mem_nhds hlx hxr
      have hbase : ContinuousAt (fun y => L + ∫ t in p..y, f t) x :=
        hbaseOn.continuousAt hnb
      exact (hbase.congr (by
        filter_upwards [Ioi_mem_nhds hcx'] with y hy
        exact (hPmid hy).symm)).continuousWithinAt
  have hinc : ∀ {a b : ℝ}, c < a → a ≤ b →
      IntervalIntegrable f volume a b ∧ P b - P a = ∫ t in a..b, f t := by
    intro a b hca hab
    have habInt := hInt hca hab
    have hpaInt : IntervalIntegrable f volume p a := by
      rcases le_total p a with hpa | hap
      · exact hInt hcp hpa
      · exact (hInt hca hap).symm
    have hpbInt : IntervalIntegrable f volume p b := by
      rcases le_total p b with hpb | hbp
      · exact hInt hcp hpb
      · exact (hInt (hca.trans_le hab) hbp).symm
    refine ⟨habInt, ?_⟩
    rw [hPmid (hca.trans_le hab), hPmid hca]
    simpa [add_sub_add_left_eq_sub] using
      intervalIntegral.integral_interval_sub_left hpbInt hpaInt
  have hlim : Tendsto P atTop (nhds (L + R)) :=
    (hR.const_add L).congr' (by
      filter_upwards [eventually_gt_atTop c] with x hx
      exact (hPmid hx).symm)
  exact ⟨hcont, hPc, hinc, hlim⟩

private def initialComponentPrimitive
    [CompleteSpace E] (f : ℝ → E) (k c : ℝ) (L : E) (x : ℝ) : E :=
  if c ≤ x then L else ∫ t in k..x, f t

private theorem initialComponentPrimitive_spec
    [CompleteSpace E] {f : ℝ → E} {k c : ℝ} {L : E}
    (hkc : k < c)
    (hInt : ∀ {b : ℝ}, k ≤ b → b < c → IntervalIntegrable f volume k b)
    (hL : Tendsto (fun b => ∫ t in k..b, f t)
      (nhdsWithin c (Iio c)) (nhds L)) :
    let P := initialComponentPrimitive f k c L
    ContinuousOn P (Icc k c) ∧ P k = 0 ∧ P c = L ∧
      ∀ {a b : ℝ}, k ≤ a → a ≤ b → b < c →
        IntervalIntegrable f volume a b ∧
          P b - P a = ∫ t in a..b, f t := by
  let P := initialComponentPrimitive f k c L
  change ContinuousOn P (Icc k c) ∧ P k = 0 ∧ P c = L ∧ _
  have hPk : P k = 0 := by
    simp [P, initialComponentPrimitive, not_le_of_gt hkc]
  have hPc : P c = L := by simp [P, initialComponentPrimitive]
  have hPleft : ∀ {x : ℝ}, x < c → P x = ∫ t in k..x, f t := by
    intro x hxc
    simp [P, initialComponentPrimitive, not_le_of_gt hxc]
  have hcont : ContinuousOn P (Icc k c) := by
    intro x hx
    rcases hx with ⟨hkx, hxc⟩
    rcases eq_or_lt_of_le hxc with rfl | hxc'
    · apply (continuousWithinAt_Iio_iff_Iic.mp ?_).mono Icc_subset_Iic_self
      rw [ContinuousWithinAt, hPc]
      exact hL.congr' (by
        filter_upwards [eventually_mem_nhdsWithin] with y hy
        exact (hPleft hy).symm)
    · let r := (x + c) / 2
      have hxr : x < r := by dsimp [r]; linarith
      have hrc : r < c := by dsimp [r]; linarith
      have hkr : k ≤ r := hkx.trans hxr.le
      have hlocalInt : IntervalIntegrable f volume k r := hInt hkr hrc
      have hbaseOn := intervalIntegral.continuousOn_primitive_interval' (a := k) hlocalInt
        left_mem_uIcc
      have hnb : [[k, r]] ∈ nhdsWithin x (Icc k c) := by
        rw [uIcc_of_le hkr]
        refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2
          ⟨Iio r, Iio_mem_nhds hxr, ?_⟩
        rintro y ⟨hyr, hyk, _⟩
        exact ⟨hyk, hyr.le⟩
      have hxmem : x ∈ [[k, r]] := by
        rw [uIcc_of_le hkr]
        exact ⟨hkx, hxr.le⟩
      have hbase : ContinuousWithinAt (fun y => ∫ t in k..y, f t) (Icc k c) x :=
        (hbaseOn x hxmem).mono_of_mem_nhdsWithin hnb
      exact hbase.congr_of_eventuallyEq (by
        filter_upwards [eventually_mem_nhdsWithin,
          eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hxc')] with y _ hy
        exact hPleft hy) (hPleft hxc')
  refine ⟨hcont, hPk, hPc, ?_⟩
  intro a b hka hab hbc
  have hkb : k ≤ b := hka.trans hab
  have hkbInt := hInt hkb hbc
  have hkaInt := hInt hka (hab.trans_lt hbc)
  refine ⟨hkaInt.symm.trans hkbInt, ?_⟩
  change P b - P a = _
  rw [hPleft hbc, hPleft (hab.trans_lt hbc)]
  exact intervalIntegral.integral_interval_sub_left hkbInt hkaInt

private def glueComponentPrimitives
    [CompleteSpace E] (d : ℝ) (A B : ℝ → E) (C : E) (x : ℝ) : E :=
  if x ≤ d then A x else C + B x

private theorem forwardTailPrimitive
    [CompleteSpace E] {f : ℝ → E} {c : ℝ} {cs : List ℝ} {I : E}
    (hsort : cs.SortedLT) (hc : ∀ x ∈ cs, c < x)
    (himp : HasImproperIntegralTailFromBreaks f c cs I) :
    ∃ F : ℝ → E, IsTailPrimitiveFromBreaks f c cs F ∧
      Tendsto F atTop (nhds I) := by
  induction cs generalizing c I with
  | nil =>
      rcases himp with ⟨p, L, R, hcp, hInt, hL, hR, rfl⟩
      let P := finalComponentPrimitive f c p L
      have hspec := finalComponentPrimitive_spec hcp hInt hL hR
      change ContinuousOn P (Ici c) ∧ P c = 0 ∧ _ ∧
        Tendsto P atTop (nhds (L + R)) at hspec
      refine ⟨P, ⟨hspec.1, hspec.2.1, ?_⟩, hspec.2.2.2⟩
      intro a b hca hab _
      exact hspec.2.2.1 hca hab
  | cons d ds ih =>
      rcases himp with ⟨p, L, R, J, hcp, hpd, hInt, hL, hR, htail, rfl⟩
      have hpw : (d :: ds).Pairwise (fun x y : ℝ => x < y) :=
        List.sortedLT_iff_pairwise.mp hsort
      have hdsSort : ds.SortedLT := List.sortedLT_iff_pairwise.mpr
        (List.pairwise_cons.mp hpw).2
      have hd_ds : ∀ x ∈ ds, d < x := (List.pairwise_cons.mp hpw).1
      rcases ih hdsSort hd_ds htail with ⟨H, hH, hHlim⟩
      let P := boundedComponentPrimitive f c d p L R
      have hP := boundedComponentPrimitive_spec hcp hpd hInt hL hR
      change ContinuousOn P (Icc c d) ∧ P c = 0 ∧ P d = L + R ∧ _ at hP
      let G := glueComponentPrimitives d P H (P d)
      have hGleft : ∀ x ∈ Icc c d, G x = P x := by
        intro x hx
        simp [G, glueComponentPrimitives, hx.2]
      have hGright : ∀ x ∈ Ici d, G x = P d + H x := by
        intro x hx
        change d ≤ x at hx
        rcases eq_or_lt_of_le hx with rfl | hdx
        · simp [G, glueComponentPrimitives, hH.2.1]
        · simp [G, glueComponentPrimitives, not_le_of_gt hdx]
      have hGcontLeft : ContinuousOn G (Icc c d) := hP.1.congr hGleft
      have hGcontRight : ContinuousOn G (Ici d) :=
        (hH.1.const_add (P d)).congr hGright
      have hunion : Icc c d ∪ Ici d = Ici c := by
        ext x
        simp only [mem_union, mem_Icc, mem_Ici]
        constructor
        · rintro (⟨hcx, _⟩ | hdx)
          · exact hcx
          · exact (hcp.trans hpd).le.trans hdx
        · intro hcx
          rcases le_total x d with hxd | hdx
          · exact Or.inl ⟨hcx, hxd⟩
          · exact Or.inr hdx
      have hGcont : ContinuousOn G (Ici c) := by
        rw [← hunion]
        exact hGcontLeft.union_of_isClosed hGcontRight isClosed_Icc isClosed_Ici
      have hGc : G c = 0 := by
        rw [hGleft c ⟨le_rfl, hcp.le.trans hpd.le⟩, hP.2.1]
      have hGinc : ∀ {a b : ℝ}, c < a → a ≤ b →
          Disjoint (Icc a b) (↑(d :: ds).toFinset : Set ℝ) →
          IntervalIntegrable f volume a b ∧ G b - G a = ∫ t in a..b, f t := by
        intro a b hca hab hdis
        have hdnot : d ∉ Icc a b := by
          intro hdmem
          exact Set.disjoint_left.1 hdis hdmem (by simp)
        have hside : b < d ∨ d < a := by
          by_cases hbd : b < d
          · exact Or.inl hbd
          · by_cases hda : d < a
            · exact Or.inr hda
            · exact False.elim (hdnot ⟨le_of_not_gt hda, le_of_not_gt hbd⟩)
        rcases hside with hbd | hda
        · rcases hP.2.2.2 hca hab hbd with ⟨hint, heq⟩
          refine ⟨hint, ?_⟩
          rw [hGleft b ⟨hca.le.trans hab, hbd.le⟩,
            hGleft a ⟨hca.le, hab.trans hbd.le⟩]
          exact heq
        · have hdis' : Disjoint (Icc a b) (↑ds.toFinset : Set ℝ) :=
            hdis.mono_right (by intro x hx; simp only [List.toFinset_cons, Finset.mem_coe,
              Finset.mem_insert]; exact Or.inr hx)
          rcases hH.2.2 hda hab hdis' with ⟨hint, heq⟩
          refine ⟨hint, ?_⟩
          rw [hGright b (hda.le.trans hab), hGright a hda.le]
          simpa [add_sub_add_left_eq_sub] using heq
      have hGlim : Tendsto G atTop (nhds (L + R + J)) := by
        rw [← hP.2.2.1]
        exact (hHlim.const_add (P d)).congr' (by
          filter_upwards [eventually_gt_atTop d] with x hdx
          exact (hGright x hdx.le).symm)
      exact ⟨G, ⟨hGcont, hGc, hGinc⟩, hGlim⟩

private theorem properAtTopPrimitive_spec
    [CompleteSpace E] {f : ℝ → E} {k : ℝ} {I : E}
    (hInt : ∀ {b : ℝ}, k ≤ b → IntervalIntegrable f volume k b)
    (hlim : Tendsto (fun b => ∫ t in k..b, f t) atTop (nhds I)) :
    let P := fun x => ∫ t in k..x, f t
    ContinuousOn P (Ici k) ∧ P k = 0 ∧
      (∀ {a b : ℝ}, k ≤ a → a ≤ b →
        IntervalIntegrable f volume a b ∧
          P b - P a = ∫ t in a..b, f t) ∧
      Tendsto P atTop (nhds I) := by
  let P := fun x => ∫ t in k..x, f t
  change ContinuousOn P (Ici k) ∧ P k = 0 ∧ _
  have hPk : P k = 0 := by simp [P]
  have hcont : ContinuousOn P (Ici k) := by
    intro x hkx
    change k ≤ x at hkx
    let r := x + 1
    have hxr : x < r := by dsimp [r]; linarith
    have hkr : k ≤ r := hkx.trans hxr.le
    have hbaseOn := intervalIntegral.continuousOn_primitive_interval' (a := k)
      (hInt hkr) left_mem_uIcc
    have hnb : [[k, r]] ∈ nhdsWithin x (Ici k) := by
      rw [uIcc_of_le hkr]
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2
        ⟨Iio r, Iio_mem_nhds hxr, ?_⟩
      rintro y ⟨hyr, hyk⟩
      exact ⟨hyk, hyr.le⟩
    have hxmem : x ∈ [[k, r]] := by
      rw [uIcc_of_le hkr]
      exact ⟨hkx, hxr.le⟩
    exact (hbaseOn x hxmem).mono_of_mem_nhdsWithin hnb
  have hinc : ∀ {a b : ℝ}, k ≤ a → a ≤ b →
      IntervalIntegrable f volume a b ∧ P b - P a = ∫ t in a..b, f t := by
    intro a b hka hab
    have hkbInt := hInt (hka.trans hab)
    have hkaInt := hInt hka
    refine ⟨hkaInt.symm.trans hkbInt, ?_⟩
    exact intervalIntegral.integral_interval_sub_left hkbInt hkaInt
  exact ⟨hcont, hPk, hinc, hlim⟩

private theorem forwardInitialPrimitive
    [CompleteSpace E] {f : ℝ → E} {k : ℝ} {cs : List ℝ} {I : E}
    (hsort : cs.SortedLT) (hk : ∀ x ∈ cs, k < x)
    (himp : HasImproperIntegralAtTopBreaks f k cs I) :
    ∃ F : ℝ → E,
      ContinuousOn F (Ici k) ∧ F k = 0 ∧
      (∀ {a b : ℝ}, k ≤ a → a ≤ b →
        Disjoint (Icc a b) (↑cs.toFinset : Set ℝ) →
        IntervalIntegrable f volume a b ∧ F b - F a = ∫ t in a..b, f t) ∧
      Tendsto F atTop (nhds I) := by
  cases cs with
  | nil =>
      have hspec := properAtTopPrimitive_spec himp.1 himp.2
      let P := fun x => ∫ t in k..x, f t
      change ContinuousOn P (Ici k) ∧ P k = 0 ∧ _ ∧
        Tendsto P atTop (nhds I) at hspec
      refine ⟨P, hspec.1, hspec.2.1, ?_, hspec.2.2.2⟩
      intro a b hka hab _
      exact hspec.2.2.1 hka hab
  | cons c cs =>
      rcases himp with ⟨L, J, hkc, hInt, hL, htail, rfl⟩
      have hpw : (c :: cs).Pairwise (fun x y : ℝ => x < y) :=
        List.sortedLT_iff_pairwise.mp hsort
      have hcsSort : cs.SortedLT := List.sortedLT_iff_pairwise.mpr
        (List.pairwise_cons.mp hpw).2
      have hc_cs : ∀ x ∈ cs, c < x := (List.pairwise_cons.mp hpw).1
      rcases forwardTailPrimitive hcsSort hc_cs htail with ⟨H, hH, hHlim⟩
      let P := initialComponentPrimitive f k c L
      have hP := initialComponentPrimitive_spec hkc hInt hL
      change ContinuousOn P (Icc k c) ∧ P k = 0 ∧ P c = L ∧ _ at hP
      let G := glueComponentPrimitives c P H (P c)
      have hGleft : ∀ x ∈ Icc k c, G x = P x := by
        intro x hx
        simp [G, glueComponentPrimitives, hx.2]
      have hGright : ∀ x ∈ Ici c, G x = P c + H x := by
        intro x hx
        change c ≤ x at hx
        rcases eq_or_lt_of_le hx with rfl | hcx
        · simp [G, glueComponentPrimitives, hH.2.1]
        · simp [G, glueComponentPrimitives, not_le_of_gt hcx]
      have hGcontLeft : ContinuousOn G (Icc k c) := hP.1.congr hGleft
      have hGcontRight : ContinuousOn G (Ici c) :=
        (hH.1.const_add (P c)).congr hGright
      have hunion : Icc k c ∪ Ici c = Ici k := by
        ext x
        simp only [mem_union, mem_Icc, mem_Ici]
        constructor
        · rintro (⟨hkx, _⟩ | hcx)
          · exact hkx
          · exact hkc.le.trans hcx
        · intro hkx
          rcases le_total x c with hxc | hcx
          · exact Or.inl ⟨hkx, hxc⟩
          · exact Or.inr hcx
      have hGcont : ContinuousOn G (Ici k) := by
        rw [← hunion]
        exact hGcontLeft.union_of_isClosed hGcontRight isClosed_Icc isClosed_Ici
      have hGk : G k = 0 := by rw [hGleft k ⟨le_rfl, hkc.le⟩, hP.2.1]
      have hGinc : ∀ {a b : ℝ}, k ≤ a → a ≤ b →
          Disjoint (Icc a b) (↑(c :: cs).toFinset : Set ℝ) →
          IntervalIntegrable f volume a b ∧ G b - G a = ∫ t in a..b, f t := by
        intro a b hka hab hdis
        have hcnot : c ∉ Icc a b := by
          intro hcmem
          exact Set.disjoint_left.1 hdis hcmem (by simp)
        have hside : b < c ∨ c < a := by
          by_cases hbc : b < c
          · exact Or.inl hbc
          · by_cases hca : c < a
            · exact Or.inr hca
            · exact False.elim (hcnot ⟨le_of_not_gt hca, le_of_not_gt hbc⟩)
        rcases hside with hbc | hca
        · rcases hP.2.2.2 hka hab hbc with ⟨hint, heq⟩
          refine ⟨hint, ?_⟩
          rw [hGleft b ⟨hka.trans hab, hbc.le⟩,
            hGleft a ⟨hka, hab.trans hbc.le⟩]
          exact heq
        · have hdis' : Disjoint (Icc a b) (↑cs.toFinset : Set ℝ) :=
            hdis.mono_right (by intro x hx; simp only [List.toFinset_cons, Finset.mem_coe,
              Finset.mem_insert]; exact Or.inr hx)
          rcases hH.2.2 hca hab hdis' with ⟨hint, heq⟩
          refine ⟨hint, ?_⟩
          rw [hGright b (hca.le.trans hab), hGright a hca.le]
          simpa [add_sub_add_left_eq_sub] using heq
      have hGlim : Tendsto G atTop (nhds (L + J)) := by
        rw [← hP.2.2.1]
        exact (hHlim.const_add (P c)).congr' (by
          filter_upwards [eventually_gt_atTop c] with x hcx
          exact (hGright x hcx.le).symm)
      exact ⟨G, hGcont, hGk, hGinc, hGlim⟩

private def normalizedTail
    [CompleteSpace E] (F : ℝ → E) (d : ℝ) (x : ℝ) : E := F x - F d

private theorem reverseTailPrimitive
    [CompleteSpace E] {f : ℝ → E} {c : ℝ} {cs : List ℝ}
    {F : ℝ → E} {I : E}
    (hsort : cs.SortedLT) (hc : ∀ x ∈ cs, c < x)
    (hF : IsTailPrimitiveFromBreaks f c cs F)
    (hlim : Tendsto F atTop (nhds I)) :
    HasImproperIntegralTailFromBreaks f c cs I := by
  induction cs generalizing c F I with
  | nil =>
      let p := c + 1
      have hcp : c < p := by dsimp [p]; linarith
      have hFright : Tendsto F (nhdsWithin c (Ioi c)) (nhds 0) := by
        rw [← hF.2.1]
        exact (hF.1 c self_mem_Ici).mono Ioi_subset_Ici_self
      have hInt : ∀ {a b : ℝ}, c < a → a ≤ b →
          IntervalIntegrable f volume a b := by
        intro a b hca hab
        exact (hF.2.2 hca hab (by simp)).1
      have hleft : Tendsto (fun a => ∫ t in a..p, f t)
          (nhdsWithin c (Ioi c)) (nhds (F p)) := by
        have ht : Tendsto (fun a => F p + -F a) (nhdsWithin c (Ioi c))
            (nhds (F p)) := by simpa using hFright.neg.const_add (F p)
        exact ht.congr' (by
          filter_upwards [eventually_mem_nhdsWithin,
            eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hcp)] with a hca hap
          have heq := (hF.2.2 hca (le_of_lt hap) (by simp)).2
          simpa [sub_eq_add_neg] using heq)
      have hright : Tendsto (fun b => ∫ t in p..b, f t) atTop
          (nhds (I - F p)) := by
        exact (hlim.sub_const (F p)).congr' (by
          filter_upwards [eventually_ge_atTop p] with b hpb
          exact (hF.2.2 hcp hpb (by simp)).2)
      refine ⟨p, F p, I - F p, hcp, hInt, hleft, hright, ?_⟩
      simp
  | cons d ds ih =>
      have hpw : (d :: ds).Pairwise (fun x y : ℝ => x < y) :=
        List.sortedLT_iff_pairwise.mp hsort
      have hdsSort : ds.SortedLT := List.sortedLT_iff_pairwise.mpr
        (List.pairwise_cons.mp hpw).2
      have hd_ds : ∀ x ∈ ds, d < x := (List.pairwise_cons.mp hpw).1
      have hcd : c < d := hc d (by simp)
      let p := (c + d) / 2
      have hcp : c < p := by dsimp [p]; linarith
      have hpd : p < d := by dsimp [p]; linarith
      have hregular : ∀ {a b : ℝ}, c < a → a ≤ b → b < d →
          Disjoint (Icc a b) (↑(d :: ds).toFinset : Set ℝ) := by
        intro a b hca hab hbd
        rw [Set.disjoint_left]
        intro x hx hmem
        simp only [List.toFinset_cons, Finset.mem_coe, Finset.mem_insert] at hmem
        rcases hmem with rfl | hxds
        · exact (not_le_of_gt hbd) hx.2
        · exact (not_lt_of_ge hx.2)
            (hbd.trans (hd_ds x (List.mem_toFinset.mp hxds)))
      have hInt : ∀ {a b : ℝ}, c < a → a ≤ b → b < d →
          IntervalIntegrable f volume a b := by
        intro a b hca hab hbd
        exact (hF.2.2 hca hab (hregular hca hab hbd)).1
      have hFright : Tendsto F (nhdsWithin c (Ioi c)) (nhds 0) := by
        rw [← hF.2.1]
        exact (hF.1 c self_mem_Ici).mono Ioi_subset_Ici_self
      have hleft : Tendsto (fun a => ∫ t in a..p, f t)
          (nhdsWithin c (Ioi c)) (nhds (F p)) := by
        have ht : Tendsto (fun a => F p + -F a) (nhdsWithin c (Ioi c))
            (nhds (F p)) := by simpa using hFright.neg.const_add (F p)
        exact ht.congr' (by
          filter_upwards [eventually_mem_nhdsWithin,
            eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hcp)] with a hca hap
          have heq := (hF.2.2 hca (le_of_lt hap)
            (hregular hca (le_of_lt hap) hpd)).2
          simpa [sub_eq_add_neg] using heq)
      have hFatD : Tendsto F (nhdsWithin d (Iio d)) (nhds (F d)) :=
        ((hF.1 d hcd.le).continuousAt (Ici_mem_nhds hcd)).tendsto.mono_left
          inf_le_left
      have hright : Tendsto (fun b => ∫ t in p..b, f t)
          (nhdsWithin d (Iio d)) (nhds (F d - F p)) := by
        exact (hFatD.sub_const (F p)).congr' (by
          filter_upwards [eventually_mem_nhdsWithin,
            eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hpd)] with b hbd hpb
          exact (hF.2.2 hcp (le_of_lt hpb)
            (hregular hcp (le_of_lt hpb) hbd)).2)
      let H := normalizedTail F d
      have hHcont : ContinuousOn H (Ici d) := by
        apply (hF.1.mono ?_).sub continuousOn_const
        exact Ici_subset_Ici.2 hcd.le
      have hHd : H d = 0 := by simp [H, normalizedTail]
      have hHinc : ∀ {a b : ℝ}, d < a → a ≤ b →
          Disjoint (Icc a b) (↑ds.toFinset : Set ℝ) →
          IntervalIntegrable f volume a b ∧ H b - H a = ∫ t in a..b, f t := by
        intro a b hda hab hdis
        have hdis' : Disjoint (Icc a b) (↑(d :: ds).toFinset : Set ℝ) := by
          rw [Set.disjoint_left]
          intro x hx hmem
          simp only [List.toFinset_cons, Finset.mem_coe, Finset.mem_insert] at hmem
          rcases hmem with rfl | hxds
          · exact (not_le_of_gt hda) hx.1
          · exact Set.disjoint_left.1 hdis hx hxds
        rcases hF.2.2 (hcd.trans hda) hab hdis' with ⟨hint, heq⟩
        refine ⟨hint, ?_⟩
        simpa [H, normalizedTail, sub_sub_sub_cancel_right] using heq
      have hHlim : Tendsto H atTop (nhds (I - F d)) := hlim.sub_const (F d)
      have hH : IsTailPrimitiveFromBreaks f d ds H := ⟨hHcont, hHd, hHinc⟩
      have htail := ih hdsSort hd_ds hH hHlim
      refine ⟨p, F p, F d - F p, I - F d, hcp, hpd, hInt,
        hleft, hright, htail, ?_⟩
      abel

private theorem reverseInitialPrimitive
    [CompleteSpace E] {f : ℝ → E} {k : ℝ} {cs : List ℝ}
    {F : ℝ → E} {I : E}
    (hsort : cs.SortedLT) (hk : ∀ x ∈ cs, k < x)
    (hcont : ContinuousOn F (Ici k)) (hFk : F k = 0)
    (hinc : ∀ {a b : ℝ}, k ≤ a → a ≤ b →
      Disjoint (Icc a b) (↑cs.toFinset : Set ℝ) →
      IntervalIntegrable f volume a b ∧ F b - F a = ∫ t in a..b, f t)
    (hlim : Tendsto F atTop (nhds I)) :
    HasImproperIntegralAtTopBreaks f k cs I := by
  cases cs with
  | nil =>
      refine ⟨?_, ?_⟩
      · intro b hkb
        exact (hinc (a := k) (b := b) le_rfl hkb (by simp)).1
      · exact hlim.congr' (by
          filter_upwards [eventually_ge_atTop k] with b hkb
          have heq := (hinc (a := k) (b := b) le_rfl hkb (by simp)).2
          simpa [hFk] using heq)
  | cons c cs =>
      have hpw : (c :: cs).Pairwise (fun x y : ℝ => x < y) :=
        List.sortedLT_iff_pairwise.mp hsort
      have hcsSort : cs.SortedLT := List.sortedLT_iff_pairwise.mpr
        (List.pairwise_cons.mp hpw).2
      have hc_cs : ∀ x ∈ cs, c < x := (List.pairwise_cons.mp hpw).1
      have hkc : k < c := hk c (by simp)
      have hregular : ∀ {b : ℝ}, k ≤ b → b < c →
          Disjoint (Icc k b) (↑(c :: cs).toFinset : Set ℝ) := by
        intro b hkb hbc
        rw [Set.disjoint_left]
        intro x hx hmem
        simp only [List.toFinset_cons, Finset.mem_coe, Finset.mem_insert] at hmem
        rcases hmem with rfl | hxcs
        · exact (not_le_of_gt hbc) hx.2
        · exact (not_lt_of_ge hx.2)
            (hbc.trans (hc_cs x (List.mem_toFinset.mp hxcs)))
      have hInt : ∀ {b : ℝ}, k ≤ b → b < c →
          IntervalIntegrable f volume k b := by
        intro b hkb hbc
        exact (hinc (a := k) (b := b) le_rfl hkb (hregular hkb hbc)).1
      have hFatC : Tendsto F (nhdsWithin c (Iio c)) (nhds (F c)) :=
        ((hcont c hkc.le).continuousAt (Ici_mem_nhds hkc)).tendsto.mono_left inf_le_left
      have hleft : Tendsto (fun b => ∫ t in k..b, f t)
          (nhdsWithin c (Iio c)) (nhds (F c)) := by
        exact hFatC.congr' (by
          filter_upwards [eventually_mem_nhdsWithin,
            eventually_nhdsWithin_of_eventually_nhds (Ici_mem_nhds hkc)] with b hbc hkb
          have heq := (hinc (a := k) (b := b) le_rfl hkb (hregular hkb hbc)).2
          simpa [hFk] using heq)
      let H := normalizedTail F c
      have hHcont : ContinuousOn H (Ici c) := by
        apply (hcont.mono (Ici_subset_Ici.2 hkc.le)).sub continuousOn_const
      have hHc : H c = 0 := by simp [H, normalizedTail]
      have hHinc : ∀ {a b : ℝ}, c < a → a ≤ b →
          Disjoint (Icc a b) (↑cs.toFinset : Set ℝ) →
          IntervalIntegrable f volume a b ∧ H b - H a = ∫ t in a..b, f t := by
        intro a b hca hab hdis
        have hdis' : Disjoint (Icc a b) (↑(c :: cs).toFinset : Set ℝ) := by
          rw [Set.disjoint_left]
          intro x hx hmem
          simp only [List.toFinset_cons, Finset.mem_coe, Finset.mem_insert] at hmem
          rcases hmem with rfl | hxcs
          · exact (not_le_of_gt hca) hx.1
          · exact Set.disjoint_left.1 hdis hx hxcs
        rcases hinc (hkc.le.trans hca.le) hab hdis' with ⟨hint, heq⟩
        refine ⟨hint, ?_⟩
        simpa [H, normalizedTail, sub_sub_sub_cancel_right] using heq
      have hHlim : Tendsto H atTop (nhds (I - F c)) := hlim.sub_const (F c)
      have hH : IsTailPrimitiveFromBreaks f c cs H := ⟨hHcont, hHc, hHinc⟩
      have htail := reverseTailPrimitive hcsSort hc_cs hH hHlim
      refine ⟨F c, I - F c, hkc, hInt, hleft, htail, ?_⟩
      simp

/-- IMP-001-T08.
@isnad1 id=iff.0h5v.s6.f9134ac59ba4 from=translated src=- shape=3e0dfdeb vocab=d46d867d
-/
theorem hasImproperIntegralAtTopExcept_iff_exists_primitive
    [CompleteSpace E] {f : ℝ → E} {k : ℝ} {S : Finset ℝ} {I : E} :
    HasImproperIntegralAtTopExcept f k S I ↔
      ∃ F : ℝ → E,
        IsFiniteExceptionalPrimitive f k S F ∧
          Tendsto F atTop (nhds I) := by
  constructor
  · intro himp
    have hsort : (S.sort (· ≤ ·)).SortedLT := S.sortedLT_sort
    have hk : ∀ x ∈ S.sort (· ≤ ·), k < x := by
      intro x hx
      exact himp.1 x ((S.mem_sort (· ≤ ·)).mp hx)
    rcases forwardInitialPrimitive hsort hk himp.2 with
      ⟨F, hcont, hFk, hinc, hlim⟩
    refine ⟨F, ⟨himp.1, hcont, hFk, ?_⟩, hlim⟩
    intro a b hka hab hdis
    apply hinc hka hab
    simpa only [S.sort_toFinset (· ≤ ·)] using hdis
  · rintro ⟨F, hF, hlim⟩
    refine ⟨hF.1, ?_⟩
    have hsort : (S.sort (· ≤ ·)).SortedLT := S.sortedLT_sort
    have hk : ∀ x ∈ S.sort (· ≤ ·), k < x := by
      intro x hx
      exact hF.1 x ((S.mem_sort (· ≤ ·)).mp hx)
    apply reverseInitialPrimitive hsort hk hF.2.1 hF.2.2.1
    · intro a b hka hab hdis
      apply hF.2.2.2 hka hab
      simpa only [S.sort_toFinset (· ≤ ·)] using hdis
    · exact hlim

private theorem atTopComponentValue_eq_of_anchor_le
    [CompleteSpace E] {f : ℝ → E} {c p q : ℝ} {Lp Rp Lq Rq : E}
    (hcp : c < p) (hpq : p ≤ q)
    (hInt : ∀ {a b : ℝ}, c < a → a ≤ b →
      IntervalIntegrable f volume a b)
    (hpL : Tendsto (fun a => ∫ t in a..p, f t)
      (nhdsWithin c (Ioi c)) (nhds Lp))
    (hpR : Tendsto (fun b => ∫ t in p..b, f t) atTop (nhds Rp))
    (hqL : Tendsto (fun a => ∫ t in a..q, f t)
      (nhdsWithin c (Ioi c)) (nhds Lq))
    (hqR : Tendsto (fun b => ∫ t in q..b, f t) atTop (nhds Rq)) :
    Lp + Rp = Lq + Rq := by
  have hcq : c < q := hcp.trans_le hpq
  have hpqInt : IntervalIntegrable f volume p q := hInt hcp hpq
  have hleft :
      (∀ᶠ a in nhdsWithin c (Ioi c),
        (∫ t in a..p, f t) + ∫ t in p..q, f t = ∫ t in a..q, f t) := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hcp)] with a hca hap
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt hca (le_of_lt hap)) hpqInt
  have hLq : Lq = Lp + ∫ t in p..q, f t :=
    tendsto_nhds_unique hqL ((hpL.add_const (∫ t in p..q, f t)).congr' hleft)
  have hright :
      (∀ᶠ b in atTop,
        (∫ t in p..q, f t) + ∫ t in q..b, f t = ∫ t in p..b, f t) := by
    filter_upwards [eventually_ge_atTop q] with b hqb
    exact intervalIntegral.integral_add_adjacent_intervals hpqInt (hInt hcq hqb)
  have hRp : Rp = (∫ t in p..q, f t) + Rq :=
    tendsto_nhds_unique hpR
      ((hqR.const_add (∫ t in p..q, f t)).congr' hright)
  rw [hLq, hRp]
  simp only [add_assoc]

private theorem atTopComponentValue_unique
    [CompleteSpace E] {f : ℝ → E} {c p q : ℝ} {Lp Rp Lq Rq : E}
    (hcp : c < p) (hcq : c < q)
    (hInt : ∀ {a b : ℝ}, c < a → a ≤ b →
      IntervalIntegrable f volume a b)
    (hpL : Tendsto (fun a => ∫ t in a..p, f t)
      (nhdsWithin c (Ioi c)) (nhds Lp))
    (hpR : Tendsto (fun b => ∫ t in p..b, f t) atTop (nhds Rp))
    (hqL : Tendsto (fun a => ∫ t in a..q, f t)
      (nhdsWithin c (Ioi c)) (nhds Lq))
    (hqR : Tendsto (fun b => ∫ t in q..b, f t) atTop (nhds Rq)) :
    Lp + Rp = Lq + Rq := by
  rcases le_total p q with hpq | hqp
  · exact atTopComponentValue_eq_of_anchor_le hcp hpq hInt hpL hpR hqL hqR
  · exact (atTopComponentValue_eq_of_anchor_le hcq hqp hInt hqL hqR hpL hpR).symm

private theorem boundedComponentValue_eq_of_anchor_le
    [CompleteSpace E] {f : ℝ → E} {c d p q : ℝ} {Lp Rp Lq Rq : E}
    (hcp : c < p) (hpq : p ≤ q) (hqd : q < d)
    (hInt : ∀ {a b : ℝ}, c < a → a ≤ b → b < d →
      IntervalIntegrable f volume a b)
    (hpL : Tendsto (fun a => ∫ t in a..p, f t)
      (nhdsWithin c (Ioi c)) (nhds Lp))
    (hpR : Tendsto (fun b => ∫ t in p..b, f t)
      (nhdsWithin d (Iio d)) (nhds Rp))
    (hqL : Tendsto (fun a => ∫ t in a..q, f t)
      (nhdsWithin c (Ioi c)) (nhds Lq))
    (hqR : Tendsto (fun b => ∫ t in q..b, f t)
      (nhdsWithin d (Iio d)) (nhds Rq)) :
    Lp + Rp = Lq + Rq := by
  have hcq : c < q := hcp.trans_le hpq
  have hpd : p < d := lt_of_le_of_lt hpq hqd
  have hpqInt : IntervalIntegrable f volume p q := hInt hcp hpq hqd
  have hleft :
      (∀ᶠ a in nhdsWithin c (Ioi c),
        (∫ t in a..p, f t) + ∫ t in p..q, f t = ∫ t in a..q, f t) := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hcp)] with a hca hap
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt hca (le_of_lt hap) hpd) hpqInt
  have hLq : Lq = Lp + ∫ t in p..q, f t :=
    tendsto_nhds_unique hqL ((hpL.add_const (∫ t in p..q, f t)).congr' hleft)
  have hright :
      (∀ᶠ b in nhdsWithin d (Iio d),
        (∫ t in p..q, f t) + ∫ t in q..b, f t = ∫ t in p..b, f t) := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hqd)] with b hbd hqb
    exact intervalIntegral.integral_add_adjacent_intervals hpqInt
      (hInt hcq (le_of_lt hqb) hbd)
  have hRp : Rp = (∫ t in p..q, f t) + Rq :=
    tendsto_nhds_unique hpR
      ((hqR.const_add (∫ t in p..q, f t)).congr' hright)
  rw [hLq, hRp]
  simp only [add_assoc]

private theorem boundedComponentValue_unique
    [CompleteSpace E] {f : ℝ → E} {c d p q : ℝ} {Lp Rp Lq Rq : E}
    (hcp : c < p) (hpd : p < d) (hcq : c < q) (hqd : q < d)
    (hInt : ∀ {a b : ℝ}, c < a → a ≤ b → b < d →
      IntervalIntegrable f volume a b)
    (hpL : Tendsto (fun a => ∫ t in a..p, f t)
      (nhdsWithin c (Ioi c)) (nhds Lp))
    (hpR : Tendsto (fun b => ∫ t in p..b, f t)
      (nhdsWithin d (Iio d)) (nhds Rp))
    (hqL : Tendsto (fun a => ∫ t in a..q, f t)
      (nhdsWithin c (Ioi c)) (nhds Lq))
    (hqR : Tendsto (fun b => ∫ t in q..b, f t)
      (nhdsWithin d (Iio d)) (nhds Rq)) :
    Lp + Rp = Lq + Rq := by
  rcases le_total p q with hpq | hqp
  · exact boundedComponentValue_eq_of_anchor_le
      hcp hpq hqd hInt hpL hpR hqL hqR
  · exact (boundedComponentValue_eq_of_anchor_le
      hcq hqp hpd hInt hqL hqR hpL hpR).symm

private theorem HasImproperIntegralTailFromBreaks.unique
    [CompleteSpace E] {f : ℝ → E} {c : ℝ} {breaks : List ℝ} {I J : E}
    (hI : HasImproperIntegralTailFromBreaks f c breaks I)
    (hJ : HasImproperIntegralTailFromBreaks f c breaks J) : I = J := by
  induction breaks generalizing c I J with
  | nil =>
      rcases hI with ⟨p, Lp, Rp, hcp, hInt, hpL, hpR, rfl⟩
      rcases hJ with ⟨q, Lq, Rq, hcq, _, hqL, hqR, rfl⟩
      exact atTopComponentValue_unique hcp hcq hInt hpL hpR hqL hqR
  | cons d ds ih =>
      rcases hI with ⟨p, Lp, Rp, Ip, hcp, hpd, hInt, hpL, hpR, htailI, rfl⟩
      rcases hJ with ⟨q, Lq, Rq, Iq, hcq, hqd, _, hqL, hqR, htailJ, rfl⟩
      have hcomponent : Lp + Rp = Lq + Rq :=
        boundedComponentValue_unique hcp hpd hcq hqd hInt hpL hpR hqL hqR
      have htail : Ip = Iq := ih htailI htailJ
      rw [hcomponent, htail]

private theorem HasImproperIntegralAtTopBreaks.unique
    [CompleteSpace E] {f : ℝ → E} {k : ℝ} {breaks : List ℝ} {I J : E}
    (hI : HasImproperIntegralAtTopBreaks f k breaks I)
    (hJ : HasImproperIntegralAtTopBreaks f k breaks J) : I = J := by
  induction breaks generalizing k I J with
  | nil =>
      exact tendsto_nhds_unique hI.2 hJ.2
  | cons c cs _ =>
      rcases hI with ⟨LI, II, _, _, hLI, htailI, rfl⟩
      rcases hJ with ⟨LJ, IJ, _, _, hLJ, htailJ, rfl⟩
      have hleft : LI = LJ := tendsto_nhds_unique hLI hLJ
      have htail : II = IJ := HasImproperIntegralTailFromBreaks.unique htailI htailJ
      rw [hleft, htail]

/-- IMP-001-T02.
@isnad1 id=eq.2h6v.s5.583d92de0ae9 from=translated src=- shape=7772f32d vocab=08c592ca
-/
theorem HasImproperIntegralAtTopExcept.unique
    [CompleteSpace E] {f : ℝ → E} {k : ℝ} {S : Finset ℝ} {I J : E}
    (hI : HasImproperIntegralAtTopExcept f k S I)
    (hJ : HasImproperIntegralAtTopExcept f k S J) : I = J :=
  HasImproperIntegralAtTopBreaks.unique hI.2 hJ.2

private theorem IsFiniteExceptionalPrimitive.weaken
    [CompleteSpace E] {f : ℝ → E} {k : ℝ} {S U : Finset ℝ} {F : ℝ → E}
    (hF : IsFiniteExceptionalPrimitive f k S F)
    (hSU : S ⊆ U) (hU : ∀ c ∈ U, k < c) :
    IsFiniteExceptionalPrimitive f k U F := by
  refine ⟨hU, hF.2.1, hF.2.2.1, ?_⟩
  intro a b hka hab hdis
  apply hF.2.2.2 hka hab
  exact hdis.mono_right (by
    intro c hc
    exact hSU (by simpa using hc))

/-- IMP-001-T03.
@isnad1 id=hasimpro.1h9v.s8.8a4ade661d6f from=translated src=- shape=9b0b837d vocab=ee0b498f
-/
theorem HasImproperIntegralAtTopExcept.finset_clm
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace E] [CompleteSpace H]
    {A : Type*} (s : Finset A) (f : A → ℝ → E)
    (S : A → Finset ℝ) (I : A → E) (T : A → E →L[ℝ] H) {k : ℝ}
    (h : ∀ i ∈ s, HasImproperIntegralAtTopExcept (f i) k (S i) (I i)) :
    HasImproperIntegralAtTopExcept
      (fun t => ∑ i ∈ s, T i (f i t)) k
      (s.biUnion S) (∑ i ∈ s, T i (I i)) := by
  classical
  let F : A → ℝ → E := fun i =>
    if hi : i ∈ s then
      Classical.choose
        (hasImproperIntegralAtTopExcept_iff_exists_primitive.mp (h i hi))
    else 0
  have hF : ∀ i ∈ s, IsFiniteExceptionalPrimitive (f i) k (S i) (F i) := by
    intro i hi
    simpa [F, hi] using
      (Classical.choose_spec
        (hasImproperIntegralAtTopExcept_iff_exists_primitive.mp (h i hi))).1
  have hFlim : ∀ i ∈ s, Tendsto (F i) atTop (nhds (I i)) := by
    intro i hi
    simpa [F, hi] using
      (Classical.choose_spec
        (hasImproperIntegralAtTopExcept_iff_exists_primitive.mp (h i hi))).2
  have hU : ∀ c ∈ s.biUnion S, k < c := by
    intro c hc
    simp only [Finset.mem_biUnion] at hc
    rcases hc with ⟨i, hi, hc⟩
    exact (hF i hi).1 c hc
  have hFU : ∀ i ∈ s,
      IsFiniteExceptionalPrimitive (f i) k (s.biUnion S) (F i) := by
    intro i hi
    apply IsFiniteExceptionalPrimitive.weaken (hF i hi) _ hU
    intro c hc
    simp only [Finset.mem_biUnion]
    exact ⟨i, hi, hc⟩
  apply hasImproperIntegralAtTopExcept_iff_exists_primitive.mpr
  refine ⟨fun t => ∑ i ∈ s, T i (F i t), ?_, ?_⟩
  · refine ⟨hU, ?_, ?_, ?_⟩
    · apply continuousOn_finsetSum
      intro i hi
      exact (T i).continuous.comp_continuousOn (hFU i hi).2.1
    · apply Finset.sum_eq_zero
      intro i hi
      rw [(hFU i hi).2.2.1, map_zero]
    · intro a b hka hab hdis
      have hpiece : ∀ i ∈ s,
          IntervalIntegrable (fun t => T i (f i t)) volume a b ∧
            T i (F i b) - T i (F i a) =
              ∫ t in a..b, T i (f i t) := by
        intro i hi
        rcases (hFU i hi).2.2.2 hka hab hdis with ⟨hint, hinc⟩
        have hmap : IntervalIntegrable (fun t => T i (f i t)) volume a b :=
          ⟨(T i).integrable_comp hint.1, (T i).integrable_comp hint.2⟩
        refine ⟨hmap, ?_⟩
        rw [← (T i).map_sub, hinc, (T i).intervalIntegral_comp_comm hint]
      have hsumInt := IntervalIntegrable.sum s (fun i hi => (hpiece i hi).1)
      have hsumInt' : IntervalIntegrable
          (fun t => ∑ i ∈ s, T i (f i t)) volume a b := by
        exact hsumInt.congr (fun t _ => by simp)
      refine ⟨hsumInt', ?_⟩
      change (∑ i ∈ s, T i (F i b)) - (∑ i ∈ s, T i (F i a)) =
        ∫ t in a..b, ∑ i ∈ s, T i (f i t)
      rw [intervalIntegral.integral_finsetSum
        (fun i hi => (hpiece i hi).1)]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i hi => (hpiece i hi).2
  · apply tendsto_finsetSum s
    intro i hi
    exact (T i).continuous.continuousAt.tendsto.comp (hFlim i hi)

/-- IMP-001-T04.
@isnad1 id=iff.3h6v.s7.025c7e541dd6 from=translated src=- shape=5d5d6b45 vocab=4bb3ec53
-/
theorem HasImproperIntegralAtTopExcept.split_regular
    [CompleteSpace E] (f : ℝ → E) {a k : ℝ} (S : Finset ℝ) (I : E)
    (hak : a ≤ k) (hS : ∀ c ∈ S, k < c)
    (hf : IntervalIntegrable f volume a k) :
    HasImproperIntegralAtTopExcept f a S ((∫ t in a..k, f t) + I) ↔
      HasImproperIntegralAtTopExcept f k S I := by
  constructor
  · intro himp
    rcases hasImproperIntegralAtTopExcept_iff_exists_primitive.mp himp with
      ⟨G, hG, hGlim⟩
    have hdisPrefix : Disjoint (Icc a k) (↑S : Set ℝ) := by
      rw [Set.disjoint_left]
      intro x hx hxS
      exact (not_lt_of_ge hx.2) (hS x hxS)
    have hGk : G k = ∫ t in a..k, f t := by
      have hinc := (hG.2.2.2 le_rfl hak hdisPrefix).2
      simpa [hG.2.2.1] using hinc
    let F := normalizedTail G k
    have hF : IsFiniteExceptionalPrimitive f k S F := by
      refine ⟨hS, ?_, ?_, ?_⟩
      · exact (hG.2.1.mono (Ici_subset_Ici.2 hak)).sub continuousOn_const
      · simp [F, normalizedTail]
      · intro u v hku huv hdis
        rcases hG.2.2.2 (hak.trans hku) huv hdis with ⟨hint, hinc⟩
        refine ⟨hint, ?_⟩
        simpa [F, normalizedTail, sub_sub_sub_cancel_right] using hinc
    have hFlim : Tendsto F atTop (nhds I) := by
      have ht := hGlim.sub_const (G k)
      change Tendsto (fun x => G x - G k) atTop (nhds I)
      simpa [hGk] using ht
    exact hasImproperIntegralAtTopExcept_iff_exists_primitive.mpr ⟨F, hF, hFlim⟩
  · intro himp
    rcases hasImproperIntegralAtTopExcept_iff_exists_primitive.mp himp with
      ⟨F, hF, hFlim⟩
    let P := fun x => ∫ t in a..x, f t
    let J := ∫ t in a..k, f t
    let G := glueComponentPrimitives k P F J
    have hPcont : ContinuousOn P (Icc a k) := by
      simpa [P, uIcc_of_le hak] using
        (intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc)
    have hGleft : ∀ x ∈ Icc a k, G x = P x := by
      intro x hx
      simp [G, glueComponentPrimitives, hx.2]
    have hGright : ∀ x ∈ Ici k, G x = J + F x := by
      intro x hx
      change k ≤ x at hx
      rcases eq_or_lt_of_le hx with rfl | hkx
      · simp [G, glueComponentPrimitives, P, J, hF.2.2.1]
      · simp [G, glueComponentPrimitives, not_le_of_gt hkx]
    have hGcontLeft : ContinuousOn G (Icc a k) := hPcont.congr hGleft
    have hGcontRight : ContinuousOn G (Ici k) :=
      (hF.2.1.const_add J).congr hGright
    have hunion : Icc a k ∪ Ici k = Ici a := by
      ext x
      simp only [mem_union, mem_Icc, mem_Ici]
      constructor
      · rintro (⟨hax, _⟩ | hkx)
        · exact hax
        · exact hak.trans hkx
      · intro hax
        rcases le_total x k with hxk | hkx
        · exact Or.inl ⟨hax, hxk⟩
        · exact Or.inr hkx
    have hGcont : ContinuousOn G (Ici a) := by
      rw [← hunion]
      exact hGcontLeft.union_of_isClosed hGcontRight isClosed_Icc isClosed_Ici
    have hGa : G a = 0 := by
      rw [hGleft a ⟨le_rfl, hak⟩]
      simp [P]
    have hGinc : ∀ {u v : ℝ}, a ≤ u → u ≤ v →
        Disjoint (Icc u v) (↑S : Set ℝ) →
        IntervalIntegrable f volume u v ∧ G v - G u = ∫ t in u..v, f t := by
      intro u v hau huv hdis
      by_cases hvk : v ≤ k
      · have hAu : IntervalIntegrable f volume a u :=
          hf.mono_set (by
            rw [uIcc_of_le hau, uIcc_of_le hak]
            exact Icc_subset_Icc le_rfl (huv.trans hvk))
        have hAv : IntervalIntegrable f volume a v :=
          hf.mono_set (by
            rw [uIcc_of_le (hau.trans huv), uIcc_of_le hak]
            exact Icc_subset_Icc le_rfl hvk)
        have huvInt : IntervalIntegrable f volume u v :=
          hf.mono_set (by
            rw [uIcc_of_le huv, uIcc_of_le hak]
            exact Icc_subset_Icc hau hvk)
        refine ⟨huvInt, ?_⟩
        rw [hGleft v ⟨hau.trans huv, hvk⟩,
          hGleft u ⟨hau, huv.trans hvk⟩]
        change (∫ t in a..v, f t) - ∫ t in a..u, f t = _
        exact intervalIntegral.integral_interval_sub_left hAv hAu
      · by_cases hku : k ≤ u
        · rcases hF.2.2.2 hku huv hdis with ⟨hint, hinc⟩
          refine ⟨hint, ?_⟩
          rw [hGright v (hku.trans huv), hGright u hku]
          simpa [add_sub_add_left_eq_sub] using hinc
        · have huk : u ≤ k := le_of_not_ge hku
          have hkv : k ≤ v := (lt_of_not_ge hvk).le
          have hAu : IntervalIntegrable f volume a u :=
            hf.mono_set (by
              rw [uIcc_of_le hau, uIcc_of_le hak]
              exact Icc_subset_Icc le_rfl huk)
          have hukInt : IntervalIntegrable f volume u k :=
            hf.mono_set (by
              rw [uIcc_of_le huk, uIcc_of_le hak]
              exact Icc_subset_Icc hau le_rfl)
          have hdisRight : Disjoint (Icc k v) (↑S : Set ℝ) :=
            hdis.mono_left (Icc_subset_Icc huk le_rfl)
          rcases hF.2.2.2 le_rfl hkv hdisRight with ⟨hkvInt, hright⟩
          have hleft : P k - P u = ∫ t in u..k, f t := by
            change (∫ t in a..k, f t) - ∫ t in a..u, f t = _
            exact intervalIntegral.integral_interval_sub_left hf hAu
          refine ⟨hukInt.trans hkvInt, ?_⟩
          rw [hGright v hkv, hGleft u ⟨hau, huk⟩]
          calc
            J + F v - P u = (P k - P u) + (F v - F k) := by
              rw [hF.2.2.1]
              rw [show J = P k by rfl]
              abel
            _ = (∫ t in u..k, f t) + ∫ t in k..v, f t := by
              rw [hleft, hright]
            _ = ∫ t in u..v, f t :=
              intervalIntegral.integral_add_adjacent_intervals hukInt hkvInt
    have hGlim : Tendsto G atTop (nhds (J + I)) :=
      (hFlim.const_add J).congr' (by
        filter_upwards [eventually_ge_atTop k] with x hkx
        exact (hGright x hkx).symm)
    apply hasImproperIntegralAtTopExcept_iff_exists_primitive.mpr
    exact ⟨G, ⟨fun c hc => hak.trans_lt (hS c hc), hGcont, hGa, hGinc⟩,
      by simpa [J] using hGlim⟩

end LMLF.Integral
