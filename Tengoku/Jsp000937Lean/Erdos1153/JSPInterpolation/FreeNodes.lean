import Tengoku.Jsp000937Lean.Erdos1153.JSPInterpolation.Definitions
import Tengoku.Jsp000937Lean.Erdos1153.JSPInterpolation.Canonical
import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.EquioscillatingHeight
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JSP-000936 / JSP-000937: arbitrary, freely chosen interpolation nodes

Every public competitor below has type `NodeFamily (d + 2)`.  Its only
constraints are pairwise distinctness and membership in [-1,1].  There is
NO assumption that the extreme nodes equal -1 and 1, or that the original
enumeration is increasing.

The canonical endpoint array is a reference shape, not a restriction on
competitors.  Sorting, affine transport, both exterior intervals, the
actual maximum, and the actual minimum of the gap maxima are addressed.

The difficult de Boor--Pinkus theorem is imported from Ethan Yang's pinned
MIT-licensed project; it is not postulated as a new axiom here.

Verification for the pinned revision is recorded in README.md. Run the
supplied verify.sh to reproduce the target and axiom checks.
-/

namespace JSPFreeNodes

open Erdos1153 Erdos1153.DeBoorPinkus

noncomputable section

/-! ## Elementary maximum and finite-minimum interfaces -/

/--
@isnad1 id=le.2h5v.s5.397c720fb21b from=translated src=- shape=87730385 vocab=a80f8ff3
-/
lemma value_le_interval_max {n : ℕ} (nodes : NodeFamily n)
    {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    lebesgueFunction nodes x ≤ lebesgueOn nodes a b := by
  obtain ⟨t, _ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [heq]
  exact hmax x hx

/--
@isnad1 id=iff.1h5v.s5.9b9819fe0ff3 from=translated src=- shape=84dfb4ee vocab=a80f8ff3
-/
lemma interval_max_le_iff {n : ℕ} (nodes : NodeFamily n)
    {a b U : ℝ} (hab : a ≤ b) :
    lebesgueOn nodes a b ≤ U ↔
      ∀ x ∈ Set.Icc a b, lebesgueFunction nodes x ≤ U := by
  constructor
  · intro h x hx
    exact (value_le_interval_max nodes hab hx).trans h
  · intro h
    obtain ⟨t, ht, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
    rw [heq]
    exact h t ht

/--
@isnad1 id=le.0h3v.s5.863589f08172 from=translated src=- shape=7a4475de vocab=27cca75e
-/
lemma orderedMinPeak_le {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) : orderedMinPeak nodes ≤ gapHeight nodes i := by
  classical
  exact csInf_le (Set.finite_range (fun j : Fin (d + 1) => gapHeight nodes j)).bddBelow
    (Set.mem_range_self i)

/--
@isnad1 id=iff.0h3v.s5.13ebdfa04e22 from=translated src=- shape=b4c47547 vocab=27cca75e
-/
lemma le_orderedMinPeak_iff {d : ℕ} (nodes : OrderedNodes (d + 2)) (L : ℝ) :
    L ≤ orderedMinPeak nodes ↔ ∀ i : Fin (d + 1), L ≤ gapHeight nodes i := by
  constructor
  · intro h i
    exact h.trans (orderedMinPeak_le nodes i)
  · intro h
    apply le_csInf
    · exact ⟨gapHeight nodes (0 : Fin (d + 1)), ⟨0, rfl⟩⟩
    · rintro _ ⟨i, rfl⟩
      exact h i

/--
@isnad1 id=le.0h3v.s6.242cbf53d05f from=translated src=- shape=9e63f318 vocab=d3ac60d5
-/
lemma gap_le_amplification {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) : gapHeight nodes i ≤ amplification nodes.toNodeFamily := by
  change lebesgueOn nodes.toNodeFamily
      (nodes.point (gapLeftIndex i)) (nodes.point (gapRightIndex i)) ≤
    lebesgueOn nodes.toNodeFamily (-1) 1
  apply (interval_max_le_iff nodes.toNodeFamily (gap_left_lt_right nodes i).le).2
  intro x hx
  apply value_le_interval_max nodes.toNodeFamily (by norm_num)
  exact ⟨(nodes.neg_one_le _).trans hx.1, hx.2.trans (nodes.le_one _)⟩

/-! ## Sorting does not remove or constrain any node configurations -/

/--
@isnad1 id=eq.1h3v.s4.e348fde33837 from=translated src=- shape=6324c611 vocab=ff604cbf
-/
lemma ordered_ext {n : ℕ} {s t : OrderedNodes n}
    (h : ∀ i, s.point i = t.point i) : s = t := by
  have hbase : s.toNodeFamily = t.toNodeFamily := NodeFamily.ext (funext h)
  cases s
  cases t
  cases hbase
  rfl

/--
@isnad1 id=eq.0h3v.s4.29f7a2cd801d from=translated src=- shape=11b1d970 vocab=c96a80e4
-/
lemma sorted_ordered_point {n : ℕ} (s : OrderedNodes n) (i : Fin n) :
    s.toNodeFamily.sorted.point i = s.point i := by
  have h := Finset.orderEmbOfFin_unique
    (NodeFamily.card_nodeFinset s.toNodeFamily)
    (fun k => (NodeFamily.mem_nodeFinset s.toNodeFamily _).2 ⟨k, rfl⟩)
    s.strictMono
  exact (congrFun h i).symm

/--
@isnad1 id=eq.0h2v.s3.260c56d7c34b from=translated src=- shape=6ddf6d3e vocab=5935beba
-/
@[simp]
lemma sorted_of_ordered {n : ℕ} (s : OrderedNodes n) :
    s.toNodeFamily.sorted = s :=
  ordered_ext (sorted_ordered_point s)

/--
@isnad1 id=eq.0h4v.s6.89eeb85e7f30 from=translated src=- shape=44a029df vocab=11c722dd
-/
@[simp]
lemma sorted_endpoint_array {d : ℕ} {A B : ℝ} (s : EndpointArray d A B) :
    s.toNodeFamily.sorted = s.toOrderedNodes :=
  sorted_of_ordered s.toOrderedNodes

/--
@isnad1 id=eq.0h2v.s4.88f3fb5c2b02 from=translated src=- shape=12bf1150 vocab=4969e8f6
-/
lemma amplification_sorted {n : ℕ} (nodes : NodeFamily n) :
    amplification nodes.sorted.toNodeFamily = amplification nodes :=
  NodeFamily.lebesgueOn_sorted nodes (-1) 1

/-! ## The actual extreme nodes, which are NOT assumed to be -1 and 1 -/

def left {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ :=
  nodes.point (endpointLeftIndex d)

def right {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ :=
  nodes.point (endpointRightIndex d)

/-- Regard a free ordered family as an endpoint array at its OWN endpoints.-/
def frame {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    EndpointArray d (left nodes) (right nodes) where
  toOrderedNodes := nodes
  left_endpoint := rfl
  right_endpoint := rfl

/--
@isnad1 id=le.0h3v.s6.f3fa43f613ac from=translated src=- shape=2c4fb015 vocab=7fb280bb
-/
lemma left_le_point {d : ℕ} (nodes : OrderedNodes (d + 2)) (i : Fin (d + 2)) :
    left nodes ≤ nodes.point i := by
  apply nodes.strictMono.monotone
  change (endpointLeftIndex d).val ≤ i.val
  simp

/--
@isnad1 id=le.0h3v.s6.74b94a8cb0fe from=translated src=- shape=0bac5587 vocab=cab7c413
-/
lemma point_le_right {d : ℕ} (nodes : OrderedNodes (d + 2)) (i : Fin (d + 2)) :
    nodes.point i ≤ right nodes := by
  apply nodes.strictMono.monotone
  change i.val ≤ (endpointRightIndex d).val
  simp only [endpointRightIndex_val]
  omega

/-! ## A genuine affine bijection, and transport of the literal products -/

/-- The increasing affine map taking -1 to A and 1 to B.-/
def affine (A B t : ℝ) : ℝ :=
  (A + B) / 2 + ((B - A) / 2) * t

/-- Its inverse when A < B.-/
def unaffine (A B x : ℝ) : ℝ :=
  (x - (A + B) / 2) / ((B - A) / 2)

/--
@isnad1 id=eq.0h2v.s4.f084f24d0c51 from=translated src=- shape=09ec87b6 vocab=8221e83b
-/
@[simp]
lemma affine_neg_one (A B : ℝ) : affine A B (-1) = A := by
  unfold affine
  ring

/--
@isnad1 id=eq.0h2v.s4.0e487da55f68 from=translated src=- shape=bc06ed63 vocab=a5e2db7d
-/
@[simp]
lemma affine_one (A B : ℝ) : affine A B 1 = B := by
  unfold affine
  ring

/--
@isnad1 id=strictmo.1h2v.s4.e8996c3c2a5d from=translated src=- shape=5b6270ae vocab=461718ae
-/
lemma affine_strictMono {A B : ℝ} (hAB : A < B) : StrictMono (affine A B) := by
  have hs : (0 : ℝ) < (B - A) / 2 := by linarith
  intro u v huv
  change (A + B) / 2 + ((B - A) / 2) * u <
    (A + B) / 2 + ((B - A) / 2) * v
  simpa only [add_comm] using
    (add_lt_add_left (mul_lt_mul_of_pos_left huv hs) ((A + B) / 2))

/--
@isnad1 id=eq.1h3v.s4.52d6652d4a97 from=translated src=- shape=cb0c62df vocab=b8d7856a
-/
lemma affine_unaffine {A B : ℝ} (hAB : A < B) (x : ℝ) :
    affine A B (unaffine A B x) = x := by
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith)
  have hcancel (c s : ℝ) (hs' : s ≠ 0) : c + s * ((x - c) / s) = x := by
    field_simp [hs']
    <;> ring
  exact hcancel _ _ hs

/--
@isnad1 id=eq.1h3v.s4.c8ec04ecf39c from=translated src=- shape=cb0c62df vocab=b8d7856a
-/
lemma unaffine_affine {A B : ℝ} (hAB : A < B) (t : ℝ) :
    unaffine A B (affine A B t) = t := by
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith)
  have hcancel (c s : ℝ) (hs' : s ≠ 0) : (c + s * t - c) / s = t := by
    field_simp [hs']
    <;> ring
  exact hcancel _ _ hs

/--
@isnad1 id=mem.2h5v.s5.d648166ced2d from=translated src=- shape=c703d657 vocab=092bfd5d
-/
lemma affine_mem_Icc {A B u v t : ℝ} (hAB : A < B)
    (ht : t ∈ Set.Icc u v) : affine A B t ∈ Set.Icc (affine A B u) (affine A B v) :=
  ⟨(affine_strictMono hAB).monotone ht.1, (affine_strictMono hAB).monotone ht.2⟩

/--
@isnad1 id=mem.2h5v.s5.e3c282163875 from=translated src=- shape=cc20831f vocab=9e54a13d
-/
lemma unaffine_mem_Icc {A B u v x : ℝ} (hAB : A < B)
    (hx : x ∈ Set.Icc (affine A B u) (affine A B v)) :
    unaffine A B x ∈ Set.Icc u v := by
  constructor
  · by_contra h
    have hlt := affine_strictMono hAB (lt_of_not_ge h)
    rw [affine_unaffine hAB x] at hlt
    exact (not_lt_of_ge hx.1) hlt
  · by_contra h
    have hlt := affine_strictMono hAB (lt_of_not_ge h)
    rw [affine_unaffine hAB x] at hlt
    exact (not_lt_of_ge hx.2) hlt

/-- An actual affine copy of the canonical array in ANY admissible [A,B].-/
def affineNodes {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) : EndpointArray d A B where
  point i := affine A B (opt.point i)
  injective := (affine_strictMono hAB.2.1).injective.comp opt.injective
  mem_Icc i := by
    have hi := affine_mem_Icc hAB.2.1 (opt.mem_Icc i)
    rw [affine_neg_one, affine_one] at hi
    exact ⟨hAB.1.trans hi.1, hi.2.trans hAB.2.2⟩
  strictMono := (affine_strictMono hAB.2.1).comp opt.strictMono
  left_endpoint := by rw [opt.left_endpoint, affine_neg_one]
  right_endpoint := by rw [opt.right_endpoint, affine_one]

/--
@isnad1 id=eq.1h5v.s7.e396e30111e8 from=translated src=- shape=34bbe43f vocab=6e429337
-/
@[simp]
lemma affineNodes_point {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (i : Fin (d + 2)) :
    (affineNodes opt hAB).point i = affine A B (opt.point i) := rfl

/--
@isnad1 id=eq.1h6v.s7.3718ca0234b5 from=translated src=- shape=e5f15819 vocab=66067479
-/
lemma lagrangeFundamental_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (k : Fin (d + 2)) (t : ℝ) :
    lagrangeFundamental (affineNodes opt hAB).toNodeFamily k (affine A B t) =
      lagrangeFundamental opt.toNodeFamily k t := by
  classical
  unfold lagrangeFundamental
  apply Finset.prod_congr rfl
  intro j _hj
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith [hAB.2.1])
  change (affine A B t - affine A B (opt.point j)) /
      (affine A B (opt.point k) - affine A B (opt.point j)) =
    (t - opt.point j) / (opt.point k - opt.point j)
  have hdiff (u v : ℝ) : affine A B u - affine A B v = ((B - A) / 2) * (u - v) := by
    unfold affine
    ring
  rw [hdiff, hdiff]
  -- Cancel the common nonzero slope directly.  No field_simp normalization
  -- or polynomial reasoning about an inverse of B-A is needed.
  exact mul_div_mul_left _ _ hs

/--
@isnad1 id=eq.1h5v.s6.640ea0998f9b from=translated src=- shape=8a1e96a5 vocab=63f922cc
-/
lemma lebesgueFunction_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (t : ℝ) :
    lebesgueFunction (affineNodes opt hAB).toNodeFamily (affine A B t) =
      lebesgueFunction opt.toNodeFamily t := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro k _hk
  rw [lagrangeFundamental_affine]

/-- Invariance of interval maxima, proved by transporting both maximizers.
@isnad1 id=eq.2h6v.s7.87829ec4b78d from=translated src=- shape=8f3ad9bb vocab=213f13e6
-/
lemma lebesgueOn_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) {a b : ℝ} (hab : a ≤ b) :
    lebesgueOn (affineNodes opt hAB).toNodeFamily (affine A B a) (affine A B b) =
      lebesgueOn opt.toNodeFamily a b := by
  obtain ⟨u, hu, hu_eq, hu_max⟩ := exists_lebesgueOn_eq_and_ge
    (affineNodes opt hAB).toNodeFamily ((affine_strictMono hAB.2.1).monotone hab)
  obtain ⟨t, ht, ht_eq, ht_max⟩ := exists_lebesgueOn_eq_and_ge opt.toNodeFamily hab
  apply le_antisymm
  · rw [hu_eq, ht_eq]
    have hv := unaffine_mem_Icc hAB.2.1 hu
    rw [← affine_unaffine hAB.2.1 u, lebesgueFunction_affine]
    exact ht_max (unaffine A B u) hv
  · rw [hu_eq, ht_eq]
    have h := hu_max (affine A B t) (affine_mem_Icc hAB.2.1 ht)
    rw [lebesgueFunction_affine] at h
    exact h

/--
@isnad1 id=eq.1h5v.s6.c1d587a0dd7c from=translated src=- shape=9e943879 vocab=b41f205c
-/
lemma height_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (i : Fin (d + 1)) :
    (affineNodes opt hAB).height i = opt.height i := by
  unfold EndpointArray.height gapHeight
  simpa only [affineNodes_point] using
    (lebesgueOn_affine opt hAB (gap_left_lt_right opt.toOrderedNodes i).le)

/--
@isnad1 id=equiosci.2h4v.s5.e5cd211e8a45 from=translated src=- shape=54392000 vocab=a8a47083
-/
lemma equioscillates_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) {A B : ℝ} (hAB : AdmissibleInterval A B) :
    Equioscillates (affineNodes opt hAB) := by
  intro i j
  rw [height_affine, height_affine]
  exact hopt i j

/-! ## Explicit affine shape, and its equivalent c + scale*x description -/

/-- Only the relative positions are fixed. The two extreme nodes are free.-/
def HasShape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) : Prop :=
  ∀ i, nodes.sorted.point i =
    affine (left nodes.sorted) (right nodes.sorted) (opt.point i)

/--
@isnad1 id=iff.0h3v.s7.8c048f30e560 from=translated src=- shape=1702ea5a vocab=9d283fd1
-/
lemma frame_eq_affine_iff {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    frame nodes.sorted = affineNodes opt (frame nodes.sorted).admissibleInterval ↔
      HasShape opt nodes := by
  constructor
  · intro h i
    exact congrArg (fun s : EndpointArray d (left nodes.sorted) (right nodes.sorted) =>
      s.point i) h
  · intro h
    apply EndpointArray.ext
    exact h

/-- The shape condition is literally a positive affine image fitting in [-1,1].
@isnad1 id=iff.0h3v.s7.95a7329aa836 from=translated src=- shape=4cfc52f4 vocab=bf346c82
-/
lemma hasShape_iff_affine_copy {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    HasShape opt nodes ↔
      ∃ c scale : ℝ, 0 < scale ∧ |c| + scale ≤ 1 ∧
        ∀ i, nodes.sorted.point i = c + scale * opt.point i := by
  constructor
  · intro h
    let a := left nodes.sorted
    let b := right nodes.sorted
    let c := (a + b) / 2
    let scale := (b - a) / 2
    have hab : a < b := (frame nodes.sorted).endpoints_lt
    have ha : -1 ≤ a := (frame nodes.sorted).neg_one_le_left
    have hb : b ≤ 1 := (frame nodes.sorted).right_le_one
    refine ⟨c, scale, ?_, ?_, ?_⟩
    · dsimp [scale]
      linarith
    · rcases le_total 0 c with hc | hc
      · rw [abs_of_nonneg hc]
        dsimp [c, scale]
        linarith
      · rw [abs_of_nonpos hc]
        dsimp [c, scale]
        linarith
    · exact h
  · rintro ⟨c, scale, _hscale, _hfit, hpoints⟩
    have ha := hpoints (endpointLeftIndex d)
    have hb := hpoints (endpointRightIndex d)
    rw [opt.left_endpoint] at ha
    rw [opt.right_endpoint] at hb
    change left nodes.sorted = c + scale * (-1) at ha
    change right nodes.sorted = c + scale * 1 at hb
    have hc : (left nodes.sorted + right nodes.sorted) / 2 = c := by linarith
    have hs : (right nodes.sorted - left nodes.sorted) / 2 = scale := by linarith
    intro i
    change nodes.sorted.point i =
      (left nodes.sorted + right nodes.sorted) / 2 +
        ((right nodes.sorted - left nodes.sorted) / 2) * opt.point i
    rw [hc, hs]
    exact hpoints i

/-! ## Bounds that already range over every free-node family -/

/--
@isnad1 id=eq.1h2v.s7.e693e1da674f from=translated src=- shape=96dd7866 vocab=e4db81ac
-/
lemma canonical_amplification {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) :
    amplification opt.toNodeFamily = opt.height 0 :=
  ClassicalBound.lebesgueOn_eq_height_zero_of_equioscillates opt hopt

/--
@isnad1 id=eq.1h2v.s6.3ffd9d9a6b05 from=translated src=- shape=da0d6198 vocab=ca358a32
-/
lemma canonical_minPeak {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) : minPeak opt.toNodeFamily = opt.height 0 := by
  change orderedMinPeak opt.toOrderedNodes.toNodeFamily.sorted = opt.height 0
  rw [sorted_of_ordered]
  apply le_antisymm
  · exact orderedMinPeak_le opt.toOrderedNodes 0
  · apply (le_orderedMinPeak_iff opt.toOrderedNodes (opt.height 0)).2
    intro i
    exact (hopt i 0).symm.le

/-! ## Auxiliary internal-gap equality classification -/

/-! ## Exterior intervals: upper tests for 936, lower tests for 937 -/

/-- To the left of all nodes, moving farther left can only increase the
Lebesgue function.  This is proved factor by factor, not assumed.
@isnad1 id=le.2h4v.s5.ff78acf8f84d from=translated src=- shape=1737c244 vocab=69fc1619
-/
lemma lebesgue_left_exterior {n : ℕ} (nodes : NodeFamily n) {u v : ℝ}
    (huv : u ≤ v) (hv : ∀ i, v ≤ nodes.point i) :
    lebesgueFunction nodes v ≤ lebesgueFunction nodes u := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_le_sum
  intro k _hk
  simp only [lagrangeFundamental, Finset.abs_prod, abs_div]
  apply Finset.prod_le_prod
  · intro j _hj
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j _hj
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonpos (sub_nonpos.mpr (hv j)),
      abs_of_nonpos (sub_nonpos.mpr (huv.trans (hv j)))]
    linarith

/-- To the right of all nodes, moving farther right can only increase the
Lebesgue function.
@isnad1 id=le.2h4v.s5.dbce3448a5c7 from=translated src=- shape=8f9e1160 vocab=69fc1619
-/
lemma lebesgue_right_exterior {n : ℕ} (nodes : NodeFamily n) {u v : ℝ}
    (huv : u ≤ v) (hu : ∀ i, nodes.point i ≤ u) :
    lebesgueFunction nodes u ≤ lebesgueFunction nodes v := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_le_sum
  intro k _hk
  simp only [lagrangeFundamental, Finset.abs_prod, abs_div]
  apply Finset.prod_le_prod
  · intro j _hj
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j _hj
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonneg (sub_nonneg.mpr (hu j)),
      abs_of_nonneg (sub_nonneg.mpr ((hu j).trans huv))]
    exact sub_le_sub_right huv _

/-- Pointwise control on the WHOLE ambient interval from all internal peaks
and the two ambient endpoint values.
@isnad1 id=le.3h3v.s7.791b9830d9c7 from=translated src=- shape=f6f1c39a vocab=a21abcf7
-/
lemma full_interval_bound_of_gaps_and_endpoints {d : ℕ}
    (nodes : OrderedNodes (d + 2)) (U : ℝ)
    (hgaps : ∀ i : Fin (d + 1), gapHeight nodes i ≤ U)
    (hleft : lebesgueFunction nodes.toNodeFamily (-1) ≤ U)
    (hright : lebesgueFunction nodes.toNodeFamily 1 ≤ U) :
    amplification nodes.toNodeFamily ≤ U := by
  apply (interval_max_le_iff nodes.toNodeFamily (by norm_num : (-1 : ℝ) ≤ 1)).2
  intro x hx
  rcases le_total x (left nodes) with hxl | hlx
  · exact (lebesgue_left_exterior nodes.toNodeFamily hx.1
      (fun i => hxl.trans (left_le_point nodes i))).trans hleft
  · rcases le_total (right nodes) x with hrx | hxr
    · exact (lebesgue_right_exterior nodes.toNodeFamily hx.2
        (fun i => (point_le_right nodes i).trans hrx)).trans hright
    · obtain ⟨i, hi⟩ := ClassicalBound.exists_closedGap_of_mem_Icc
        (frame nodes) ⟨hlx, hxr⟩
      exact (DeBoorPinkus.lebesgueFunction_le_height (frame nodes) i hi).trans (hgaps i)

/-! ## JSP-000936: exact equality classification over arbitrary node families -/

/-! ## A normalized-coordinate version of the two exterior tests -/

/-- Affine invariance from the literal point equations alone.  No equality
of EndpointArray structures, sorting proofs, or interval certificates is
transported through lebesgueFunction.
@isnad1 id=eq.2h6v.s5.11ed3da7a64e from=translated src=- shape=737614e3 vocab=8ff4a604
-/
lemma lebesgueFunction_affine_of_points {n : ℕ}
    (source target : NodeFamily n) {A B : ℝ} (hAB : A < B)
    (hpoint : ∀ i, source.point i = affine A B (target.point i)) (t : ℝ) :
    lebesgueFunction source (affine A B t) = lebesgueFunction target t := by
  classical
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith)
  have hdiff (u v : ℝ) :
      affine A B u - affine A B v = ((B - A) / 2) * (u - v) := by
    unfold affine
    ring
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro k _hk
  apply congrArg abs
  unfold lagrangeFundamental
  apply Finset.prod_congr rfl
  intro j _hj
  rw [hpoint j, hpoint k, hdiff, hdiff]
  exact mul_div_mul_left _ _ hs

/--
@isnad1 id=eq.1h4v.s7.a965e443143f from=translated src=- shape=d90e5876 vocab=9b9b3ef7
-/
lemma lebesgueFunction_of_shape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) (hshape : HasShape opt nodes) (t : ℝ) :
    lebesgueFunction nodes (affine (left nodes.sorted) (right nodes.sorted) t) =
      lebesgueFunction opt.toNodeFamily t := by
  calc
    lebesgueFunction nodes (affine (left nodes.sorted) (right nodes.sorted) t) =
        lebesgueFunction nodes.sorted.toNodeFamily
          (affine (left nodes.sorted) (right nodes.sorted) t) :=
      (NodeFamily.lebesgueFunction_sorted nodes _).symm
    _ = lebesgueFunction opt.toNodeFamily t :=
      lebesgueFunction_affine_of_points nodes.sorted.toNodeFamily opt.toNodeFamily
        (frame nodes.sorted).endpoints_lt hshape t

/--
@isnad1 id=eq.1h4v.s7.9e8e0054f9bf from=translated src=- shape=08ee9fca vocab=c361cc62
-/
lemma lebesgueFunction_of_shape_inverse {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) (hshape : HasShape opt nodes) (x : ℝ) :
    lebesgueFunction nodes x = lebesgueFunction opt.toNodeFamily
      (unaffine (left nodes.sorted) (right nodes.sorted) x) := by
  have h := lebesgueFunction_of_shape opt nodes hshape
    (unaffine (left nodes.sorted) (right nodes.sorted) x)
  rwa [affine_unaffine (frame nodes.sorted).endpoints_lt] at h

/-! ## Public, assumption-free conclusions for the two prize problems -/

/-- The n=1 edge case of minimax: every single node has amplification one.
There are no INTERNAL adjacent gaps for n=1; the all-gap extension has
two exterior intervals, each with constant Lebesgue function one.
@isnad1 id=eq.0h2v.s4.165590b7396a from=translated src=- shape=c24049f2 vocab=f5757059
-/
lemma single_node_lebesgue (nodes : NodeFamily 1) (x : ℝ) :
    lebesgueFunction nodes x = 1 := by
  classical
  have hfund (k : Fin 1) : lagrangeFundamental nodes k x = 1 := by
    have herase : (Finset.univ : Finset (Fin 1)).erase k = ∅ := by
      apply Finset.ext
      intro j
      have hjk : j = k := Subsingleton.elim j k
      simp [hjk]
    simp only [lagrangeFundamental, herase, Finset.prod_empty]
  simp [lebesgueFunction, hfund]

/--
@isnad1 id=eq.0h1v.s4.1a55ec3ca8fc from=translated src=- shape=1e0028ff vocab=9815f495
-/
lemma single_node_amplification (nodes : NodeFamily 1) :
    amplification nodes = 1 := by
  obtain ⟨x, _hx, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
  exact heq.trans (single_node_lebesgue nodes x)

/--
@isnad1 id=isminimi.0h1v.s3.35d6f91a029c from=translated src=- shape=9315f4f4 vocab=9f7fb5ec
-/
theorem jsp_000936_one_node (nodes : NodeFamily 1) : IsMinimizer nodes := by
  intro other
  calc
    amplification nodes = 1 := single_node_amplification nodes
    _ ≤ 1 := le_rfl
    _ = amplification other := (single_node_amplification other).symm

/-! ## Closed public targets whose competitor types contain no fixed endpoints -/

/--
@isnad1 id=isnormal.1h2v.s6.65ecb72c1841 from=translated src=- shape=e7629662 vocab=d2179dcc
-/
lemma canonical_is_normalized {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) : IsNormalizedEquioscillating opt.toNodeFamily := by
  unfold IsNormalizedEquioscillating
  simp only [sorted_endpoint_array]
  exact ⟨opt.left_endpoint, opt.right_endpoint, hopt⟩

/--
@isnad1 id=iff.0h3v.s6.62565b9e03dc from=translated src=- shape=11a86a69 vocab=6db2f13c
-/
lemma hasShape_iff_admissibleAffineCopy {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    HasShape opt nodes ↔ AdmissibleAffineCopy opt.toNodeFamily nodes := by
  simpa only [AdmissibleAffineCopy, sorted_of_ordered] using
    (hasShape_iff_affine_copy opt nodes)

end
end JSPFreeNodes
