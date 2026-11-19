import Tengoku.Linearhadwiger.HadwigerLean.Hypergraph.Indexed
import Tengoku.Linearhadwiger.HadwigerLean.Probability.FiniteBernoulli
import Tengoku.Linearhadwiger.HadwigerLean.Coloring.Fractional
import Tengoku.Linearhadwiger.HadwigerLean.Coloring.PairLoad
import Tengoku.Linearhadwiger.HadwigerLean.Quantitative.UnionBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Low-codegree rounding

The sampling part of the paper's rounding lemma is independent of the token/dummy
construction. We first connect finite Bernoulli marks on indexed edge copies to the
degrees and codegrees of the sampled multihypergraph.
-/

namespace HadwigerLean.LowCodegreeRounding

variable {W E : Type*} [DecidableEq W] [DecidableEq E] [Fintype E]

/-- Retain precisely the marked active edge copies.-/
def sampledHypergraph (H : IndexedHypergraph W E) (ω : E → Bool) :
    IndexedHypergraph W E :=
  H.restrictEdges (H.edges.filter fun e => ω e) (Finset.filter_subset _ _)

omit [DecidableEq W] [DecidableEq E] [Fintype E] in
/--
@isnad1 id=isunifor.1h5v.s4.796fd7479817 from=translated src=- shape=edfa5643 vocab=e45f2727
-/
theorem sampled_uniform (H : IndexedHypergraph W E) (ω : E → Bool)
    {r : ℕ} (hunif : H.IsUniform r) :
    (sampledHypergraph H ω).IsUniform r := by
  intro e he
  exact hunif e (Finset.filter_subset _ _ he)

section TokenDummy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Original vertices, color tokens, and dummy vertices live in disjoint summands.-/
abbrev TokenDummyVertex (V : Type*) (p z : ℕ) := V ⊕ (Fin p ⊕ Fin z)

/-- Edge-copy labels retain the stable set, token, and dummy subset.-/
abbrev TokenDummyLabel (G : SimpleGraph V) (p z : ℕ) :=
  StableSet G × (Fin p × Finset (Fin z))

/-- The endpoint set of a token/dummy edge copy.-/
noncomputable def tokenDummyEdge (G : SimpleGraph V) {p z : ℕ}
    (e : TokenDummyLabel G p z) : Finset (TokenDummyVertex V p z) := by
  classical
  exact (e.1.1.image Sum.inl) ∪
    {Sum.inr (Sum.inl e.2.1)} ∪
    (e.2.2.image (fun d => Sum.inr (Sum.inr d)))

/-- Keep only labels whose dummy count makes the edge size m+2.-/
noncomputable def tokenDummyHypergraph (G : SimpleGraph V) (m p z : ℕ) :
    IndexedHypergraph (TokenDummyVertex V p z) (TokenDummyLabel G p z) := by
  classical
  exact
    { vertices := Finset.univ
      edges := Finset.univ.filter
        (fun e => e.1.1.card + e.2.2.card = m + 1)
      edge := tokenDummyEdge G
      edge_subset := by
        intro e he
        exact Finset.subset_univ _ }

omit [Fintype V] in
/--
@isnad1 id=iff.0h6v.s6.32c01ac18bc1 from=translated src=- shape=11cb83d3 vocab=8caacf5a
-/
@[simp] theorem original_mem_tokenDummyEdge (G : SimpleGraph V) {p z : ℕ}
    (e : TokenDummyLabel G p z) (v : V) :
    Sum.inl v ∈ tokenDummyEdge G e ↔ v ∈ e.1.1 := by
  classical
  simp [tokenDummyEdge]

omit [Fintype V] in
/--
@isnad1 id=iff.0h6v.s6.6c3467fc85b0 from=translated src=- shape=a5ee0663 vocab=35d4048f
-/
@[simp] theorem token_mem_tokenDummyEdge (G : SimpleGraph V) {p z : ℕ}
    (e : TokenDummyLabel G p z) (c : Fin p) :
    Sum.inr (Sum.inl c) ∈ tokenDummyEdge G e ↔ c = e.2.1 := by
  classical
  simp [tokenDummyEdge]

omit [Fintype V] in
/--
@isnad1 id=iff.0h6v.s6.d64fbb111809 from=translated src=- shape=28d30ad4 vocab=47732521
-/
@[simp] theorem dummy_mem_tokenDummyEdge (G : SimpleGraph V) {p z : ℕ}
    (e : TokenDummyLabel G p z) (d : Fin z) :
    Sum.inr (Sum.inr d) ∈ tokenDummyEdge G e ↔ d ∈ e.2.2 := by
  classical
  simp [tokenDummyEdge]

omit [Fintype V] in
/--
@isnad1 id=eq.0h5v.s6.234cedd88f1d from=translated src=- shape=2eb2728d vocab=1285bf38
-/
theorem tokenDummyEdge_card (G : SimpleGraph V) {p z : ℕ}
    (e : TokenDummyLabel G p z) :
    (tokenDummyEdge G e).card = e.1.1.card + 1 + e.2.2.card := by
  classical
  have hAB :
      Disjoint (e.1.1.image (Sum.inl : V → TokenDummyVertex V p z))
        ({Sum.inr (Sum.inl e.2.1)} : Finset (TokenDummyVertex V p z)) := by
    simp [Finset.disjoint_left]
  have hABC :
      Disjoint
        ((e.1.1.image (Sum.inl : V → TokenDummyVertex V p z)) ∪
          {Sum.inr (Sum.inl e.2.1)})
        (e.2.2.image (fun d : Fin z =>
          (Sum.inr (Sum.inr d) : TokenDummyVertex V p z))) := by
    simp [Finset.disjoint_left]
  unfold tokenDummyEdge
  rw [Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB]
  have hinj : Function.Injective
      (fun d : Fin z => (Sum.inr (Sum.inr d) : TokenDummyVertex V p z)) := by
    intro a b h
    exact Sum.inr.inj (Sum.inr.inj h)
  simp [Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ hinj]

/--
@isnad1 id=isunifor.0h5v.s5.ff41f9a305ce from=translated src=- shape=66f8e855 vocab=4be38610
-/
theorem tokenDummy_uniform (G : SimpleGraph V) (m p z : ℕ) :
    (tokenDummyHypergraph G m p z).IsUniform (m + 2) := by
  classical
  intro e he
  have hvalid : e.1.1.card + e.2.2.card = m + 1 :=
    (Finset.mem_filter.mp he).2
  change (tokenDummyEdge G e).card = m + 2
  rw [tokenDummyEdge_card]
  omega

end TokenDummy

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section PartialTokenColoring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A partial token assignment gives each unassigned vertex a private color.-/
noncomputable def tokenOrPrivateColor {p : ℕ} (f : V → Option (Fin p))
    (v : V) : Fin p ⊕ {u : V // f u = none} :=
  match h : f v with
  | none => Sum.inr ⟨v, h⟩
  | some c => Sum.inl c

omit [Fintype V] [DecidableEq V] in
/--
@isnad1 id=eq.1h4v.s6.0dc7795e22e0 from=translated src=- shape=c1927038 vocab=20a1e77a
-/
@[simp] theorem tokenOrPrivateColor_none {p : ℕ} (f : V → Option (Fin p))
    (v : V) (h : f v = none) :
    tokenOrPrivateColor f v = Sum.inr ⟨v, h⟩ := by
  unfold tokenOrPrivateColor
  split <;> simp_all

omit [Fintype V] [DecidableEq V] in
/--
@isnad1 id=eq.1h5v.s6.793f5037aff1 from=translated src=- shape=7e38954f vocab=588edf0b
-/
@[simp] theorem tokenOrPrivateColor_some {p : ℕ} (f : V → Option (Fin p))
    (v : V) (c : Fin p) (h : f v = some c) :
    tokenOrPrivateColor f v = Sum.inl c := by
  unfold tokenOrPrivateColor
  split <;> simp_all

omit [DecidableEq V] in
/-- A proper partial assignment of color tokens extends using one private
color for each unassigned vertex.
@isnad1 id=colorabl.1h4v.s6.89ae71fb69f7 from=translated src=- shape=3281a3ac vocab=29d7b9d8
-/
theorem colorable_of_partial_token (G : SimpleGraph V) {p : ℕ}
    (f : V → Option (Fin p))
    (hproper : ∀ {v w : V}, G.Adj v w → ∀ c : Fin p,
      f v = some c → f w ≠ some c) :
    G.Colorable (p + Fintype.card {v : V // f v = none}) := by
  classical
  let C : G.Coloring (Fin p ⊕ {v : V // f v = none}) :=
    SimpleGraph.Coloring.mk (tokenOrPrivateColor f) (by
      intro v w hvw heq
      cases hfv : f v with
      | none =>
        rw [tokenOrPrivateColor_none f v hfv] at heq
        cases hfw : f w with
        | none =>
          rw [tokenOrPrivateColor_none f w hfw] at heq
          have hvw' : v = w := congrArg Subtype.val (Sum.inr.inj heq)
          exact (G.ne_of_adj hvw) hvw'
        | some c =>
          rw [tokenOrPrivateColor_some f w c hfw] at heq
          cases heq
      | some c =>
        rw [tokenOrPrivateColor_some f v c hfv] at heq
        cases hfw : f w with
        | none =>
          rw [tokenOrPrivateColor_none f w hfw] at heq
          cases heq
        | some d =>
          rw [tokenOrPrivateColor_some f w d hfw] at heq
          have hcd : c = d := Sum.inl.inj heq
          subst d
          exact hproper hvw c hfv hfw)
  simpa using C.colorable
end PartialTokenColoring

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section MatchingExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Distinct edges of a matching cannot use the same color token.
@isnad1 id=eq.4h8v.s7.bf8660b3b52e from=translated src=- shape=5d4874cf vocab=4bfeab36
-/
theorem matching_token_injective (G : SimpleGraph V) (m p z : ℕ)
    (M : Finset (TokenDummyLabel G p z))
    (hM : (tokenDummyHypergraph G m p z).IsMatching M)
    {e f : TokenDummyLabel G p z} (he : e ∈ M) (hf : f ∈ M)
    (hcolor : e.2.1 = f.2.1) : e = f := by
  classical
  by_contra hne
  have hdisj := hM.2 he hf hne
  have heTok :
      Sum.inr (Sum.inl e.2.1) ∈
        (tokenDummyHypergraph G m p z).edge e := by
    change Sum.inr (Sum.inl e.2.1) ∈ tokenDummyEdge G e
    simp
  have hfTok :
      Sum.inr (Sum.inl e.2.1) ∈
        (tokenDummyHypergraph G m p z).edge f := by
    change Sum.inr (Sum.inl e.2.1) ∈ tokenDummyEdge G f
    simp [hcolor]
  exact (Finset.disjoint_left.mp hdisj) heTok hfTok

/-- Assign a covered original vertex the token of one edge that covers it.-/
noncomputable def matchingPartialToken {p z : ℕ}
    {G : SimpleGraph V} (M : Finset (TokenDummyLabel G p z))
    (v : V) : Option (Fin p) :=
  if h : ∃ e ∈ M, v ∈ e.1.1 then some (Classical.choose h).2.1 else none

omit [Fintype V] in
/-- Assigned tokens always arise from a selected stable set containing the vertex.
@isnad1 id=ex.1h7v.s7.b8565566f35f from=translated src=- shape=45d31b09 vocab=e1f5a282
-/
theorem matchingPartialToken_some {p z : ℕ}
    {G : SimpleGraph V} (M : Finset (TokenDummyLabel G p z))
    {v : V} {c : Fin p} (hc : matchingPartialToken M v = some c) :
    ∃ e ∈ M, v ∈ e.1.1 ∧ e.2.1 = c := by
  classical
  unfold matchingPartialToken at hc
  split at hc
  · rename_i h
    obtain ⟨he, hv⟩ := Classical.choose_spec h
    refine ⟨Classical.choose h, he, hv, ?_⟩
    exact Option.some.inj hc
  · simp at hc

omit [Fintype V] in
/-- Unassigned vertices are exactly those omitted by all selected stable sets.
@isnad1 id=iff.0h6v.s6.7675fa1cbe14 from=translated src=- shape=6222ba48 vocab=42c8e854
-/
theorem matchingPartialToken_none_iff {p z : ℕ}
    {G : SimpleGraph V} (M : Finset (TokenDummyLabel G p z))
    (v : V) :
    matchingPartialToken M v = none ↔
      ∀ e ∈ M, v ∉ e.1.1 := by
  classical
  constructor
  · intro hf e he hv
    have hex : ∃ a ∈ M, v ∈ a.1.1 := ⟨e, he, hv⟩
    simp [matchingPartialToken, hex] at hf
  · intro h
    have hex : ¬ ∃ e ∈ M, v ∈ e.1.1 := by
      rintro ⟨e, he, hv⟩
      exact h e he hv
    simp [matchingPartialToken, hex]

/-- Edges in a token/dummy matching induce a proper partial token coloring.
@isnad1 id=ne.3h9v.s6.5000b280c6c9 from=translated src=- shape=f8bfb999 vocab=81e6f1f8
-/
theorem matchingPartialToken_proper (G : SimpleGraph V) (m p z : ℕ)
    (M : Finset (TokenDummyLabel G p z))
    (hM : (tokenDummyHypergraph G m p z).IsMatching M) :
    ∀ {v w : V}, G.Adj v w → ∀ c : Fin p,
      matchingPartialToken M v = some c →
      matchingPartialToken M w ≠ some c := by
  intro v w hvw c hvc hwc
  obtain ⟨e, he, hve, hec⟩ := matchingPartialToken_some M hvc
  obtain ⟨f, hf, hwf, hfc⟩ := matchingPartialToken_some M hwc
  have hef : e = f := matching_token_injective G m p z M hM he hf
    (hec.trans hfc.symm)
  subst f
  exact (e.1.2.2 hve hwf (G.ne_of_adj hvw)) hvw

/-- A matching gives a coloring using its tokens and one color per
uncovered original vertex.
@isnad1 id=colorabl.1h6v.s6.fcaaabb88a0a from=translated src=- shape=12ef50b1 vocab=fdd29184
-/
theorem colorable_of_tokenDummy_matching (G : SimpleGraph V) (m p z : ℕ)
    (M : Finset (TokenDummyLabel G p z))
    (hM : (tokenDummyHypergraph G m p z).IsMatching M) :
    G.Colorable
      (p + Fintype.card {v : V // matchingPartialToken M v = none}) := by
  exact colorable_of_partial_token G (matchingPartialToken M)
    (matchingPartialToken_proper G m p z M hM)
/-- Private colors for original vertices are bounded by all vertices left
uncovered by the hypergraph matching.
@isnad1 id=le.1h6v.s7.5bb113fc936a from=translated src=- shape=1cc2e6d7 vocab=3e493dfe
-/
theorem private_color_count_le_uncovered (G : SimpleGraph V) (m p z : ℕ)
    (M : Finset (TokenDummyLabel G p z))
    (hM : (tokenDummyHypergraph G m p z).IsMatching M) :
    Fintype.card {v : V // matchingPartialToken M v = none} ≤
      (tokenDummyHypergraph G m p z).vertices.card -
        ((tokenDummyHypergraph G m p z).covered M).card := by
  classical
  let H := tokenDummyHypergraph G m p z
  let emb : {v : V // matchingPartialToken M v = none} →
      {w : TokenDummyVertex V p z // w ∈ H.vertices \ H.covered M} :=
    fun v => ⟨Sum.inl v.1, by
      apply Finset.mem_sdiff.mpr
      constructor
      · change Sum.inl v.1 ∈ Finset.univ
        simp
      · intro hc
        obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hc
        have hvS : v.1 ∈ e.1.1 := by
          exact (original_mem_tokenDummyEdge G e v.1).mp hve
        exact ((matchingPartialToken_none_iff M v.1).mp v.2) e he hvS⟩
  have hinj : Function.Injective emb := by
    intro a b hab
    apply Subtype.ext
    exact Sum.inl.inj (congrArg Subtype.val hab)
  have hcard := Fintype.card_le_of_injective emb hinj
  change Fintype.card {v : V // matchingPartialToken M v = none} ≤
    Fintype.card (↥(H.vertices \ H.covered M)) at hcard
  rw [Fintype.card_coe,
    Finset.card_sdiff_of_subset (H.covered_subset_vertices hM.1)] at hcard
  exact hcard
/-- The precise matching input needed for token/dummy rounding. A future
application of the almost-perfect matching theorem will establish this from
the sampled degree and codegree estimates.-/
def MatchingHypothesis (G : SimpleGraph V) (m p z : ℕ) (ξ : ℝ) : Prop :=
  ∃ M : Finset (TokenDummyLabel G p z),
    (tokenDummyHypergraph G m p z).IsMatching M ∧
      (1 - ξ) *
        ((tokenDummyHypergraph G m p z).vertices.card : ℝ) ≤
      (((tokenDummyHypergraph G m p z).covered M).card : ℝ)

/-- Conditional rounding: an almost-perfect token/dummy matching produces
a coloring whose number of private colors is at most ξ times the enlarged
vertex count.
@isnad1 id=ex.1h6v.s6.6750f7755597 from=translated src=- shape=04fcc483 vocab=8bf58fc2
-/
theorem colorable_of_MatchingHypothesis (G : SimpleGraph V) (m p z : ℕ)
    (ξ : ℝ) (hmatch : MatchingHypothesis G m p z ξ) :
    ∃ k : ℕ,
      G.Colorable (p + k) ∧
        (k : ℝ) ≤ ξ *
          ((tokenDummyHypergraph G m p z).vertices.card : ℝ) := by
  classical
  obtain ⟨M, hM, hcovered⟩ := hmatch
  let H := tokenDummyHypergraph G m p z
  let k := Fintype.card {v : V // matchingPartialToken M v = none}
  refine ⟨k, colorable_of_tokenDummy_matching G m p z M hM, ?_⟩
  have hprivate : k ≤ H.vertices.card - (H.covered M).card :=
    private_color_count_le_uncovered G m p z M hM
  have hcovLe : (H.covered M).card ≤ H.vertices.card :=
    Finset.card_le_card (H.covered_subset_vertices hM.1)
  have hreal : (k : ℝ) ≤
      (H.vertices.card : ℝ) - ((H.covered M).card : ℝ) := by
    exact_mod_cast hprivate
  change (1 - ξ) * (H.vertices.card : ℝ) ≤
      ((H.covered M).card : ℝ) at hcovered
  change (k : ℝ) ≤ ξ * (H.vertices.card : ℝ)
  nlinarith
/-- Final arithmetic step of the rounding lemma: token count is within one
of fractional cost, and the matching leaves enough slack for the extra
private colors.
@isnad1 id=le.4h8v.s7.3ccaa17b1ca6 from=translated src=- shape=6d56fc58 vocab=da9c39c7
-/
theorem chromatic_le_of_MatchingHypothesis (G : SimpleGraph V)
    (m p z : ℕ) (ξ γ : ℝ) (x : StableSet G → ℝ)
    (hmatch : MatchingHypothesis G m p z ξ)
    (hpCost : (p : ℝ) ≤ fractionalCost G x + 1)
    (hsize : ξ * ((tokenDummyHypergraph G m p z).vertices.card : ℝ) ≤
      γ * (Fintype.card V : ℝ) / 2)
    (hlarge : 2 ≤ γ * (Fintype.card V : ℝ)) :
    (chromatic G : ℝ) ≤ fractionalCost G x +
      γ * (Fintype.card V : ℝ) := by
  obtain ⟨k, hcolor, hk⟩ :=
    colorable_of_MatchingHypothesis G m p z ξ hmatch
  have hchrom : chromatic G ≤ p + k :=
    (chromatic_le_iff_colorable G (p + k)).2 hcolor
  have hchromR : (chromatic G : ℝ) ≤ (p : ℝ) + (k : ℝ) := by
    exact_mod_cast hchrom
  nlinarith
end MatchingExtraction

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section DummyNormalization

/-- The fixed-size subsets of `Fin z` are counted by the binomial coefficient.
@isnad1 id=eq.0h2v.s5.ab9448f56ce3 from=translated src=- shape=380f9a0d vocab=298377d3
-/
theorem card_dummy_subsets (z j : ℕ) :
    (Finset.univ.filter (fun T : Finset (Fin z) => T.card = j)).card =
      Nat.choose z j := by
  classical
  have hset : (Finset.univ.filter (fun T : Finset (Fin z) => T.card = j)) =
      (Finset.univ : Finset (Fin z)).powersetCard j := by
    ext T
    simp [Finset.mem_powersetCard, eq_comm]
  rw [hset, Finset.card_powersetCard]
  simp

/-- Uniformly distributing unit mass among all `j`-subsets of `Fin z`
produces total mass one.
@isnad1 id=eq.1h2v.s6.81dc81c1f766 from=translated src=- shape=918584b7 vocab=08e363e0
-/
theorem sum_dummy_recip_choose (z j : ℕ) (hj : j ≤ z) :
    (∑ T : Finset (Fin z),
      if T.card = j then (1 : ℝ) / (Nat.choose z j : ℝ) else 0) = 1 := by
  classical
  have hjR : (Nat.choose z j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  rw [Finset.sum_ite]
  simp [hjR]

/-- Among all `j`-subsets of `Fin z`, the fraction containing a fixed
dummy vertex is `j/z`.
@isnad1 id=eq.3h3v.s7.6c98d3d274d8 from=translated src=- shape=c1a286b9 vocab=05a23da9
-/
theorem sum_dummy_mem_recip_choose (z j : ℕ) (hz : 0 < z)
    (hj : 0 < j) (hjz : j ≤ z) (d : Fin z) :
    (∑ T : Finset (Fin z),
      if T.card = j ∧ d ∈ T then
        (1 : ℝ) / (Nat.choose z j : ℝ) else 0) =
      (j : ℝ) / (z : ℝ) := by
  classical
  have hset :
      (Finset.univ.filter (fun T : Finset (Fin z) => T.card = j ∧ d ∈ T)) =
        ((Finset.univ : Finset (Fin z)).powersetCard j).filter
          (fun T => ({d} : Finset (Fin z)) ⊆ T) := by
    ext T
    simp [Finset.mem_powersetCard]
  have hcard :
      (Finset.univ.filter (fun T : Finset (Fin z) => T.card = j ∧ d ∈ T)).card =
        Nat.choose (z - 1) (j - 1) := by
    rw [hset, Finset.card_filter_powersetCard_subset]
    · simp
    · simp
    · simpa only [Finset.card_singleton] using (Nat.succ_le_iff.mpr hj)
  have hnat :
      z * Nat.choose (z - 1) (j - 1) =
        j * Nat.choose z j := by
    obtain ⟨z', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz.ne'
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    simpa [Nat.succ_eq_add_one, mul_comm (Nat.choose (z' + 1) (j' + 1)) (j' + 1)] using
      Nat.add_one_mul_choose_eq z' j'
  have hnatR :
      (z : ℝ) * (Nat.choose (z - 1) (j - 1) : ℝ) =
        (j : ℝ) * (Nat.choose z j : ℝ) := by
    exact_mod_cast hnat
  have hzR : (z : ℝ) ≠ 0 := by exact_mod_cast hz.ne'
  have hjR : (Nat.choose z j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjz).ne'
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
    hcard, nsmul_eq_mul]
  field_simp
  nlinarith
/-- Scaling the fixed-dummy incidence identity by a real mass.
@isnad1 id=eq.3h4v.s7.ae7485994d5b from=translated src=- shape=4be3107e vocab=af2bfda5
-/
theorem sum_dummy_mem_scaled (z j : ℕ) (hz : 0 < z)
    (hj : 0 < j) (hjz : j ≤ z) (d : Fin z) (a : ℝ) :
    (∑ T : Finset (Fin z),
      if T.card = j ∧ d ∈ T then
        a / (Nat.choose z j : ℝ) else 0) =
      a * ((j : ℝ) / (z : ℝ)) := by
  classical
  calc
    (∑ T : Finset (Fin z),
      if T.card = j ∧ d ∈ T then
        a / (Nat.choose z j : ℝ) else 0) =
      a * (∑ T : Finset (Fin z),
        if T.card = j ∧ d ∈ T then
          (1 : ℝ) / (Nat.choose z j : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases h : T.card = j ∧ d ∈ T <;>
        simp [h, div_eq_mul_inv]
    _ = a * ((j : ℝ) / (z : ℝ)) := by
      rw [sum_dummy_mem_recip_choose z j hz hj hjz d]
/-- The dummy and token choices have total weight equal to their stable-set
weight.
@isnad1 id=eq.2h4v.s6.7312cd18dfa3 from=translated src=- shape=5fd6f8ec vocab=6b1cb96b
-/
theorem sum_token_dummy_weight (p z j : ℕ) (hp : 0 < p) (hj : j ≤ z)
    (x : ℝ) :
    (∑ _ : Fin p, ∑ T : Finset (Fin z),
      if T.card = j then
        x / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0) = x := by
  classical
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hjR : (Nat.choose z j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj).ne'
  have hinner :
      (∑ T : Finset (Fin z),
        if T.card = j then
          x / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0) =
      (Nat.choose z j : ℝ) *
        (x / ((p : ℝ) * (Nat.choose z j : ℝ))) := by
    rw [Finset.sum_ite]
    simp
  calc
    (∑ _ : Fin p, ∑ T : Finset (Fin z),
      if T.card = j then
        x / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0) =
        (p : ℝ) *
          ((Nat.choose z j : ℝ) *
            (x / ((p : ℝ) * (Nat.choose z j : ℝ)))) := by
      simp [hinner]
    _ = x := by field_simp

end DummyNormalization

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section WeightedTokenDummy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's weight on an active token/dummy edge copy, zero on
inactive labels.-/
noncomputable def tokenDummyWeight (G : SimpleGraph V) (m p z : ℕ)
    (x : StableSet G → ℝ) (e : TokenDummyLabel G p z) : ℝ :=
  if e ∈ (tokenDummyHypergraph G m p z).edges then
    x e.1 / ((p : ℝ) * (Nat.choose z e.2.2.card : ℝ))
  else 0

/--
@isnad1 id=le.1h7v.s6.68e50d7e3e84 from=translated src=- shape=4bf06637 vocab=2d618213
-/
theorem tokenDummyWeight_nonneg (G : SimpleGraph V) (m p z : ℕ)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (e : TokenDummyLabel G p z) :
    0 ≤ tokenDummyWeight G m p z x e := by
  classical
  unfold tokenDummyWeight
  split
  · exact div_nonneg (hx e.1) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact le_refl _

/-- For each stable set, its mass is split uniformly over every token and
valid dummy subset.
@isnad1 id=eq.3h7v.s7.34156bbe260c from=translated src=- shape=f35181c0 vocab=380c8511
-/
theorem sum_tokenDummyWeight_fixed_stable (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (S : StableSet G)
    (hS : S.1.card ≤ m) :
    (∑ c : Fin p, ∑ T : Finset (Fin z),
      tokenDummyWeight G m p z x (S, c, T)) = x S := by
  classical
  let j := m + 1 - S.1.card
  have hj : j ≤ z := by dsimp [j]; omega
  have hterm (c : Fin p) (T : Finset (Fin z)) :
      tokenDummyWeight G m p z x (S, c, T) =
        if T.card = j then
          x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0 := by
    have hiff : S.1.card + T.card = m + 1 ↔ T.card = j := by
      dsimp [j]
      omega
    unfold tokenDummyWeight
    simp only [tokenDummyHypergraph, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hT : T.card = j
    · have hvalid : S.1.card + T.card = m + 1 := hiff.mpr hT
      rw [ite_eq_left hvalid, ite_eq_left hT, hT]
    · have hnotvalid : ¬ S.1.card + T.card = m + 1 :=
        fun hv => hT (hiff.mp hv)
      rw [ite_eq_right hnotvalid, ite_eq_right hT]
  calc
    (∑ c : Fin p, ∑ T : Finset (Fin z),
      tokenDummyWeight G m p z x (S, c, T)) =
      ∑ c : Fin p, ∑ T : Finset (Fin z),
        if T.card = j then
          x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro T hT
      exact hterm c T
    _ = x S := sum_token_dummy_weight p z j hp hj (x S)

/-- For a fixed stable set, active edge copies are exactly the dummy
subsets of the required cardinality.
@isnad1 id=eq.1h9v.s8.9a6d50721356 from=translated src=- shape=ce423210 vocab=a1e6e1e8
-/
theorem tokenDummyWeight_fixed_stable_eq (G : SimpleGraph V)
    (m p z : ℕ) (x : StableSet G → ℝ) (S : StableSet G)
    (hS : S.1.card ≤ m) (c : Fin p) (T : Finset (Fin z)) :
    tokenDummyWeight G m p z x (S, c, T) =
      if T.card = m + 1 - S.1.card then
        x S / ((p : ℝ) *
          (Nat.choose z (m + 1 - S.1.card) : ℝ)) else 0 := by
  classical
  have hiff : S.1.card + T.card = m + 1 ↔
      T.card = m + 1 - S.1.card := by omega
  unfold tokenDummyWeight
  simp only [tokenDummyHypergraph, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hT : T.card = m + 1 - S.1.card
  · have hvalid : S.1.card + T.card = m + 1 := hiff.mpr hT
    rw [ite_eq_left hvalid, ite_eq_left hT, hT]
  · have hnotvalid : ¬ S.1.card + T.card = m + 1 :=
      fun hv => hT (hiff.mp hv)
    rw [ite_eq_right hnotvalid, ite_eq_right hT]
/-- A fixed dummy vertex receives the fraction `j/z` of the mass of a
stable set, where `j = m+1-|S|` is its dummy count.
@isnad1 id=eq.3h8v.s7.82e58709698e from=translated src=- shape=ef6ebdbb vocab=dd2bc19e
-/
theorem sum_tokenDummyWeight_fixed_dummy (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (S : StableSet G)
    (hS : S.1.card ≤ m) (d : Fin z) :
    (∑ c : Fin p, ∑ T : Finset (Fin z),
      if d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) =
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) := by
  classical
  let j := m + 1 - S.1.card
  have hj : 0 < j := by dsimp [j]; omega
  have hjz : j ≤ z := by dsimp [j]; omega
  have hzpos : 0 < z := by omega
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hterm (c : Fin p) (T : Finset (Fin z)) :
      (if d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) =
        if T.card = j ∧ d ∈ T then
          x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0 := by
    rw [tokenDummyWeight_fixed_stable_eq G m p z x S hS c T]
    by_cases hd : d ∈ T <;> by_cases hT : T.card = j <;>
      simp [hd, hT, j, and_comm]
  calc
    (∑ c : Fin p, ∑ T : Finset (Fin z),
      if d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) =
        ∑ c : Fin p, ∑ T : Finset (Fin z),
          if T.card = j ∧ d ∈ T then
            x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro T hT
      exact hterm c T
    _ = (p : ℝ) * ((x S / (p : ℝ)) * ((j : ℝ) / (z : ℝ))) := by
      have hinner :
          (∑ T : Finset (Fin z),
            if T.card = j ∧ d ∈ T then
              x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0) =
            (x S / (p : ℝ)) * ((j : ℝ) / (z : ℝ)) := by
        calc
          (∑ T : Finset (Fin z),
            if T.card = j ∧ d ∈ T then
              x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0) =
              ∑ T : Finset (Fin z),
                if T.card = j ∧ d ∈ T then
                  (x S / (p : ℝ)) / (Nat.choose z j : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro T hT
            by_cases h : T.card = j ∧ d ∈ T <;>
              simp [h, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]
          _ = (x S / (p : ℝ)) * ((j : ℝ) / (z : ℝ)) :=
            sum_dummy_mem_scaled z j hzpos hj hjz d (x S / (p : ℝ))
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [hinner]
    _ = x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) := by
      dsimp [j]
      field_simp
/-- Each individual token receives an equal `1/p` share of the weight
of a fixed stable set.
@isnad1 id=eq.3h8v.s7.e0680c0acbc2 from=translated src=- shape=15b773f9 vocab=35e97de0
-/
theorem sum_tokenDummyWeight_fixed_token (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (S : StableSet G)
    (hS : S.1.card ≤ m) (c : Fin p) :
    (∑ T : Finset (Fin z),
      tokenDummyWeight G m p z x (S, c, T)) = x S / (p : ℝ) := by
  classical
  let Y := ∑ T : Finset (Fin z), tokenDummyWeight G m p z x (S, c, T)
  have hsame (d : Fin p) :
      (∑ T : Finset (Fin z), tokenDummyWeight G m p z x (S, d, T)) = Y := by
    apply Finset.sum_congr rfl
    intro T hT
    simp [tokenDummyWeight, tokenDummyHypergraph]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have htotal : (p : ℝ) * Y = x S := by
    calc
      (p : ℝ) * Y = ∑ d : Fin p, Y := by simp
      _ = ∑ d : Fin p, ∑ T : Finset (Fin z),
          tokenDummyWeight G m p z x (S, d, T) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact (hsame d).symm
      _ = x S := sum_tokenDummyWeight_fixed_stable G m p z hp hz x S hS
  apply (eq_div_iff hpR).2
  change Y * (p : ℝ) = x S
  simpa [mul_comm] using htotal
/-- Any predicate depending only on the stable-set coordinate preserves
the full stable-set weight after token/dummy splitting.
@isnad1 id=eq.3h7v.s7.b5f279f2d4b9 from=translated src=- shape=61e4015a vocab=568ac103
-/
theorem sum_tokenDummyWeight_stable_pred (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (P : StableSet G → Prop) [DecidablePred P] :
    (∑ e : TokenDummyLabel G p z,
      if P e.1 then tokenDummyWeight G m p z x e else 0) =
      ∑ S : StableSet G, if P S then x S else 0 := by
  classical
  calc
    (∑ e : TokenDummyLabel G p z,
      if P e.1 then tokenDummyWeight G m p z x e else 0) =
        ∑ S : StableSet G, ∑ c : Fin p, ∑ T : Finset (Fin z),
          if P S then tokenDummyWeight G m p z x (S, c, T) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.sum_prod_type]
    _ = ∑ S : StableSet G, if P S then x S else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hP : P S
      · simp only [hP, ite_true]
        exact sum_tokenDummyWeight_fixed_stable G m p z hp hz x S (hstable S)
      · simp [hP]

/-- Restricting to active edges yields the same stable-coordinate sum.
@isnad1 id=eq.3h7v.s7.20f0123d460d from=translated src=- shape=922713bc vocab=1ac585cd
-/
theorem tokenDummy_weighted_stable_pred (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (P : StableSet G → Prop) [DecidablePred P] :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e : TokenDummyLabel G p z => P e.1)).sum (tokenDummyWeight G m p z x)) =
      ∑ S : StableSet G, if P S then x S else 0 := by
  classical
  let H := tokenDummyHypergraph G m p z
  change (H.edges.filter (fun e => P e.1)).sum
    (tokenDummyWeight G m p z x) = _
  rw [Finset.sum_filter]
  calc
    (∑ e ∈ H.edges,
      if P e.1 then tokenDummyWeight G m p z x e else 0) =
        ∑ e : TokenDummyLabel G p z,
          if P e.1 then tokenDummyWeight G m p z x e else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.edges)
      intro e heuniv henot
      simp [tokenDummyWeight, H, henot]
    _ = ∑ S : StableSet G, if P S then x S else 0 :=
      sum_tokenDummyWeight_stable_pred G m p z hp hz x hstable P
/-- Exact original-original weighted codegree is the fractional pair load.
@isnad1 id=eq.3h8v.s9.fd5a509a3c47 from=translated src=- shape=03f5febe vocab=ff1c5df6
-/
theorem tokenDummy_weighted_original_codegree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m) (u v : V) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inl u ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) =
      ∑ S : StableSet G, if u ∈ S.1 ∧ v ∈ S.1 then x S else 0 := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hfilter :
      H.edges.filter (fun e => Sum.inl u ∈ H.edge e ∧ Sum.inl v ∈ H.edge e) =
        H.edges.filter (fun e : TokenDummyLabel G p z =>
          u ∈ e.1.1 ∧ v ∈ e.1.1) := by
    ext e
    simp only [Finset.mem_filter]
    change (e ∈ H.edges ∧ Sum.inl u ∈ tokenDummyEdge G e ∧
      Sum.inl v ∈ tokenDummyEdge G e) ↔
      (e ∈ H.edges ∧ u ∈ e.1.1 ∧ v ∈ e.1.1)
    simp
  change (H.edges.filter (fun e => Sum.inl u ∈ H.edge e ∧
    Sum.inl v ∈ H.edge e)).sum (tokenDummyWeight G m p z x) = _
  rw [hfilter]
  exact tokenDummy_weighted_stable_pred G m p z hp hz x hstable
    (fun S => u ∈ S.1 ∧ v ∈ S.1)

/-- Exact weighted degree at each original vertex.
@isnad1 id=eq.3h7v.s7.ec11f9250985 from=translated src=- shape=e8616bec vocab=d45275a3
-/
theorem sum_tokenDummyWeight_original (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m) (v : V) :
    (∑ e : TokenDummyLabel G p z,
      if v ∈ e.1.1 then tokenDummyWeight G m p z x e else 0) =
      vertexLoad G x v := by
  classical
  calc
    (∑ e : TokenDummyLabel G p z,
      if v ∈ e.1.1 then tokenDummyWeight G m p z x e else 0) =
        ∑ S : StableSet G, ∑ c : Fin p, ∑ T : Finset (Fin z),
          if v ∈ S.1 then tokenDummyWeight G m p z x (S, c, T) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.sum_prod_type]
    _ = ∑ S : StableSet G, if v ∈ S.1 then x S else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hv : v ∈ S.1
      · simp only [hv, ite_true]
        exact sum_tokenDummyWeight_fixed_stable G m p z hp hz x S (hstable S)
      · simp [hv]
    _ = vertexLoad G x v := rfl
/-- Summing over all edge-copy labels, a fixed token receives total
weight equal to the fractional cost divided by the token count.
@isnad1 id=eq.3h7v.s7.5feaeefdaebe from=translated src=- shape=dd12865b vocab=2aca24d5
-/
theorem sum_tokenDummyWeight_token (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m) (c : Fin p) :
    (∑ e : TokenDummyLabel G p z,
      if c = e.2.1 then tokenDummyWeight G m p z x e else 0) =
      fractionalCost G x / (p : ℝ) := by
  classical
  calc
    (∑ e : TokenDummyLabel G p z,
      if c = e.2.1 then tokenDummyWeight G m p z x e else 0) =
        ∑ S : StableSet G, ∑ d : Fin p, ∑ T : Finset (Fin z),
          if c = d then tokenDummyWeight G m p z x (S, d, T) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.sum_prod_type]
    _ = ∑ S : StableSet G, ∑ T : Finset (Fin z),
          tokenDummyWeight G m p z x (S, c, T) := by
      apply Finset.sum_congr rfl
      intro S hS
      simp
    _ = ∑ S : StableSet G, x S / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact sum_tokenDummyWeight_fixed_token G m p z hp hz x S (hstable S) c
    _ = fractionalCost G x / (p : ℝ) := by
      simp [fractionalCost, div_eq_mul_inv, Finset.sum_mul]
/-- Summing over all labels, a fixed dummy vertex receives the weighted
average of the required dummy counts.
@isnad1 id=eq.3h7v.s8.4b909dd0b851 from=translated src=- shape=be1636ca vocab=bcee3395
-/
theorem sum_tokenDummyWeight_dummy (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m) (d : Fin z) :
    (∑ e : TokenDummyLabel G p z,
      if d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
      ∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) := by
  classical
  calc
    (∑ e : TokenDummyLabel G p z,
      if d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
        ∑ S : StableSet G, ∑ c : Fin p, ∑ T : Finset (Fin z),
          if d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.sum_prod_type]
    _ = ∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact sum_tokenDummyWeight_fixed_dummy G m p z hp hz x S (hstable S) d

/-- Exact fractional vertex loads count weighted incidences as the number
of original vertices.
@isnad1 id=eq.1h3v.s6.1537aa5deb35 from=translated src=- shape=7582db6a vocab=6956f6f3
-/
theorem sum_stable_card_weight_eq_vertices (G : SimpleGraph V)
    (x : StableSet G → ℝ)
    (hload : ∀ v, vertexLoad G x v = 1) :
    (∑ S : StableSet G, (S.1.card : ℝ) * x S) =
      (Fintype.card V : ℝ) := by
  classical
  have h := weighted_vertexLoad_eq G x (fun _ => (1 : ℝ))
  have hleft : (∑ v : V, (1 : ℝ) * vertexLoad G x v) =
      (Fintype.card V : ℝ) := by
    simp [hload]
  have hright :
      (∑ S : StableSet G, x S * ∑ v ∈ S.1, (1 : ℝ)) =
        ∑ S : StableSet G, (S.1.card : ℝ) * x S := by
    apply Finset.sum_congr rfl
    intro S hS
    simp [mul_comm]
  rw [hleft, hright] at h
  exact h.symm
/-- The dummy-vertex load numerator is `(m+1)τ-n` when every original
vertex has fractional load one.
@isnad1 id=eq.2h5v.s7.7ac739bf9091 from=translated src=- shape=babc5bbe vocab=39dbb0c9
-/
theorem sum_dummy_mass_eq (G : SimpleGraph V) (m z : ℕ)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1) :
    (∑ S : StableSet G,
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ))) =
      (((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ)) / (z : ℝ) := by
  classical
  have hsum :
      (∑ S : StableSet G,
        (((m + 1 : ℕ) : ℝ) * x S - (S.1.card : ℝ) * x S)) =
      (((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [sum_stable_card_weight_eq_vertices G x hload]
    rfl
  calc
    (∑ S : StableSet G,
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ))) =
        ∑ S : StableSet G,
          ((((m + 1 : ℕ) : ℝ) * x S - (S.1.card : ℝ) * x S) *
            (z : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hle : S.1.card ≤ m + 1 := (hstable S).trans (Nat.le_succ m)
      rw [Nat.cast_sub hle]
      push_cast
      rw [div_eq_mul_inv]
      ring
    _ = (∑ S : StableSet G,
          (((m + 1 : ℕ) : ℝ) * x S - (S.1.card : ℝ) * x S)) *
            (z : ℝ)⁻¹ := by rw [Finset.sum_mul]
    _ = (((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ)) / (z : ℝ) := by
      rw [hsum, div_eq_mul_inv]
/-- Exact weighted degree at a dummy vertex in the active hypergraph.
@isnad1 id=eq.3h7v.s8.0e350116d1f8 from=translated src=- shape=cc819131 vocab=78aa2a42
-/
theorem tokenDummy_weighted_dummy_degree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m) (d : Fin z) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inr d) ∈
        (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) =
      ∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hfilter :
      H.edges.filter (fun e => Sum.inr (Sum.inr d) ∈ H.edge e) =
        H.edges.filter (fun e : TokenDummyLabel G p z => d ∈ e.2.2) := by
    ext e
    simp only [Finset.mem_filter]
    change (e ∈ H.edges ∧ Sum.inr (Sum.inr d) ∈ tokenDummyEdge G e) ↔
      (e ∈ H.edges ∧ d ∈ e.2.2)
    simp
  change (H.edges.filter (fun e => Sum.inr (Sum.inr d) ∈ H.edge e)).sum
    (tokenDummyWeight G m p z x) = _
  rw [hfilter, Finset.sum_filter]
  calc
    (∑ e ∈ H.edges,
      if d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
        ∑ e : TokenDummyLabel G p z,
          if d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.edges)
      intro e heuniv henot
      simp [tokenDummyWeight, H, henot]
    _ = ∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) :=
      sum_tokenDummyWeight_dummy G m p z hp hz x hstable d
/-- Paper's exact weighted dummy degree under unit original loads.
@isnad1 id=eq.4h7v.s8.e1da82a4773c from=translated src=- shape=39301fa3 vocab=f5fdf42b
-/
theorem tokenDummy_weighted_dummy_degree_exact (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1) (d : Fin z) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inr d) ∈
        (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) =
      (((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ)) / (z : ℝ) := by
  rw [tokenDummy_weighted_dummy_degree G m p z hp hz x hstable d,
    sum_dummy_mass_eq G m z x hstable hload]
/-- The weighted degree in the active indexed hypergraph equals the exact
fractional vertex load.
@isnad1 id=eq.3h7v.s8.1f8eb4ef9026 from=translated src=- shape=aebe29b4 vocab=be3ddc2f
-/
theorem tokenDummy_weighted_original_degree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m) (v : V) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) = vertexLoad G x v := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hfilter :
      H.edges.filter (fun e => Sum.inl v ∈ H.edge e) =
        H.edges.filter (fun e : TokenDummyLabel G p z => v ∈ e.1.1) := by
    ext e
    simp only [Finset.mem_filter]
    change (e ∈ H.edges ∧ Sum.inl v ∈ tokenDummyEdge G e) ↔
      (e ∈ H.edges ∧ v ∈ e.1.1)
    simp
  change (H.edges.filter (fun e => Sum.inl v ∈ H.edge e)).sum
    (tokenDummyWeight G m p z x) = vertexLoad G x v
  rw [hfilter, Finset.sum_filter]
  calc
    (∑ e ∈ H.edges,
      if v ∈ e.1.1 then tokenDummyWeight G m p z x e else 0) =
        ∑ e : TokenDummyLabel G p z,
          if v ∈ e.1.1 then tokenDummyWeight G m p z x e else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.edges)
      intro e heuniv henot
      simp [tokenDummyWeight, H, henot]
    _ = vertexLoad G x v :=
      sum_tokenDummyWeight_original G m p z hp hz x hstable v
/-- The weighted degree at each token is the fractional cost divided by
the number of tokens.
@isnad1 id=eq.3h7v.s8.ff1c246b6735 from=translated src=- shape=d02f38ee vocab=02615758
-/
theorem tokenDummy_weighted_token_degree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m) (c : Fin p) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inl c) ∈
        (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) = fractionalCost G x / (p : ℝ) := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hfilter :
      H.edges.filter (fun e => Sum.inr (Sum.inl c) ∈ H.edge e) =
        H.edges.filter (fun e : TokenDummyLabel G p z => c = e.2.1) := by
    ext e
    simp only [Finset.mem_filter]
    change (e ∈ H.edges ∧ Sum.inr (Sum.inl c) ∈ tokenDummyEdge G e) ↔
      (e ∈ H.edges ∧ c = e.2.1)
    simp
  change (H.edges.filter (fun e => Sum.inr (Sum.inl c) ∈ H.edge e)).sum
    (tokenDummyWeight G m p z x) = fractionalCost G x / (p : ℝ)
  rw [hfilter, Finset.sum_filter]
  calc
    (∑ e ∈ H.edges,
      if c = e.2.1 then tokenDummyWeight G m p z x e else 0) =
        ∑ e : TokenDummyLabel G p z,
          if c = e.2.1 then tokenDummyWeight G m p z x e else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.edges)
      intro e heuniv henot
      simp [tokenDummyWeight, H, henot]
    _ = fractionalCost G x / (p : ℝ) :=
      sum_tokenDummyWeight_token G m p z hp hz x hstable c
/-- Sample every active edge copy at `n` times its normalized weight.-/
noncomputable def tokenDummySampleProbability (G : SimpleGraph V)
    (m p z : ℕ) (n : ℝ) (x : StableSet G → ℝ)
    (e : TokenDummyLabel G p z) : ℝ :=
  n * tokenDummyWeight G m p z x e

/-- Exact expected sampled original-original codegree.
@isnad1 id=eq.3h9v.s9.d3a1448dedc7 from=translated src=- shape=5b671bbf vocab=aa3cabfc
-/
theorem tokenDummy_expected_original_codegree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (n : ℝ) (u v : V) :
    FiniteBernoulli.mean (tokenDummySampleProbability G m p z n x)
      ((tokenDummyHypergraph G m p z).edges.filter
        (fun e => Sum.inl u ∈ (tokenDummyHypergraph G m p z).edge e ∧
          Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e)) =
      n * (∑ S : StableSet G,
        if u ∈ S.1 ∧ v ∈ S.1 then x S else 0) := by
  classical
  unfold FiniteBernoulli.mean tokenDummySampleProbability
  rw [← Finset.mul_sum]
  rw [tokenDummy_weighted_original_codegree G m p z hp hz x hstable u v]
/-- Exact expected sampled degree at an original vertex.
@isnad1 id=eq.3h8v.s8.a5870f2b4247 from=translated src=- shape=a1539ab1 vocab=59ab3557
-/
theorem tokenDummy_expected_original_degree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (n : ℝ) (v : V) :
    FiniteBernoulli.mean (tokenDummySampleProbability G m p z n x)
      ((tokenDummyHypergraph G m p z).edges.filter
        (fun e => Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e)) =
      n * vertexLoad G x v := by
  classical
  unfold FiniteBernoulli.mean tokenDummySampleProbability
  rw [← Finset.mul_sum]
  rw [tokenDummy_weighted_original_degree G m p z hp hz x hstable v]

/-- Exact expected sampled degree at each color token.
@isnad1 id=eq.3h8v.s8.c0fb33d60185 from=translated src=- shape=2e83f18a vocab=96452b1a
-/
theorem tokenDummy_expected_token_degree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (n : ℝ) (c : Fin p) :
    FiniteBernoulli.mean (tokenDummySampleProbability G m p z n x)
      ((tokenDummyHypergraph G m p z).edges.filter
        (fun e => Sum.inr (Sum.inl c) ∈
          (tokenDummyHypergraph G m p z).edge e)) =
      n * (fractionalCost G x / (p : ℝ)) := by
  classical
  unfold FiniteBernoulli.mean tokenDummySampleProbability
  rw [← Finset.mul_sum]
  rw [tokenDummy_weighted_token_degree G m p z hp hz x hstable c]
/-- Exact expected sampled degree at each dummy vertex under unit
original loads.
@isnad1 id=eq.4h8v.s8.907baeee9c8e from=translated src=- shape=134af6ba vocab=69f59131
-/
theorem tokenDummy_expected_dummy_degree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (n : ℝ) (d : Fin z) :
    FiniteBernoulli.mean (tokenDummySampleProbability G m p z n x)
      ((tokenDummyHypergraph G m p z).edges.filter
        (fun e => Sum.inr (Sum.inr d) ∈
          (tokenDummyHypergraph G m p z).edge e)) =
      n * ((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ)) / (z : ℝ)) := by
  classical
  unfold FiniteBernoulli.mean tokenDummySampleProbability
  rw [← Finset.mul_sum]
  rw [tokenDummy_weighted_dummy_degree_exact G m p z hp hz x hstable hload d]
/-- Under exact fractional loads, each original vertex has expected
sampled degree `n`.
@isnad1 id=eq.4h8v.s8.e0aa701e7a9c from=translated src=- shape=2dd483fd vocab=12b25208
-/
theorem tokenDummy_expected_original_degree_exact (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (n : ℝ) (v : V) :
    FiniteBernoulli.mean (tokenDummySampleProbability G m p z n x)
      ((tokenDummyHypergraph G m p z).edges.filter
        (fun e => Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e)) = n := by
  rw [tokenDummy_expected_original_degree G m p z hp hz x hstable n v,
    hload v, mul_one]
end WeightedTokenDummy

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section MixedCodegrees

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fixed token receives exactly a `1/p` share of every stable-coordinate
subfamily.
@isnad1 id=eq.3h8v.s8.bf09c367c09c from=translated src=- shape=25044734 vocab=447c5c5a
-/
theorem sum_tokenDummyWeight_token_stable_pred (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (P : StableSet G → Prop) [DecidablePred P] (c : Fin p) :
    (∑ e : TokenDummyLabel G p z,
      if P e.1 ∧ c = e.2.1 then tokenDummyWeight G m p z x e else 0) =
      (∑ S : StableSet G, if P S then x S else 0) / (p : ℝ) := by
  classical
  calc
    (∑ e : TokenDummyLabel G p z,
      if P e.1 ∧ c = e.2.1 then tokenDummyWeight G m p z x e else 0) =
        ∑ S : StableSet G, ∑ d : Fin p, ∑ T : Finset (Fin z),
          if P S ∧ c = d then tokenDummyWeight G m p z x (S, d, T) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.sum_prod_type]
    _ = ∑ S : StableSet G,
          if P S then ∑ T : Finset (Fin z),
            tokenDummyWeight G m p z x (S, c, T) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hP : P S <;> simp [hP]
    _ = ∑ S : StableSet G, if P S then x S / (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hP : P S
      · simp only [hP, ite_true]
        exact sum_tokenDummyWeight_fixed_token G m p z hp hz x S (hstable S) c
      · simp [hP]
    _ = (∑ S : StableSet G, if P S then x S else 0) / (p : ℝ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul]

end MixedCodegrees

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section OriginalTokenCodegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The original-token weighted codegree is the fractional vertex load
shared equally over all tokens.
@isnad1 id=eq.3h8v.s9.2404a60649e0 from=translated src=- shape=fca15023 vocab=d5b28aa7
-/
theorem tokenDummy_weighted_original_token_codegree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (v : V) (c : Fin p) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inl c) ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) = vertexLoad G x v / (p : ℝ) := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hfilter :
      H.edges.filter (fun e => Sum.inl v ∈ H.edge e ∧
        Sum.inr (Sum.inl c) ∈ H.edge e) =
      H.edges.filter (fun e : TokenDummyLabel G p z =>
        v ∈ e.1.1 ∧ c = e.2.1) := by
    ext e
    simp only [Finset.mem_filter]
    change (e ∈ H.edges ∧ Sum.inl v ∈ tokenDummyEdge G e ∧
      Sum.inr (Sum.inl c) ∈ tokenDummyEdge G e) ↔
      (e ∈ H.edges ∧ v ∈ e.1.1 ∧ c = e.2.1)
    simp
  change (H.edges.filter (fun e => Sum.inl v ∈ H.edge e ∧
    Sum.inr (Sum.inl c) ∈ H.edge e)).sum
    (tokenDummyWeight G m p z x) = _
  rw [hfilter, Finset.sum_filter]
  calc
    (∑ e ∈ H.edges,
      if v ∈ e.1.1 ∧ c = e.2.1 then tokenDummyWeight G m p z x e else 0) =
        ∑ e : TokenDummyLabel G p z,
          if v ∈ e.1.1 ∧ c = e.2.1 then tokenDummyWeight G m p z x e else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.edges)
      intro e heuniv henot
      simp [tokenDummyWeight, H, henot]
    _ = vertexLoad G x v / (p : ℝ) :=
      sum_tokenDummyWeight_token_stable_pred G m p z hp hz x hstable
        (fun S => v ∈ S.1) c

/-- Expected original-token codegree under independent edge-copy sampling.
@isnad1 id=eq.3h9v.s9.067ba9421f62 from=translated src=- shape=07e8c6d1 vocab=60e84c9b
-/
theorem tokenDummy_expected_original_token_codegree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (n : ℝ) (v : V) (c : Fin p) :
    FiniteBernoulli.mean (tokenDummySampleProbability G m p z n x)
      ((tokenDummyHypergraph G m p z).edges.filter
        (fun e => Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e ∧
          Sum.inr (Sum.inl c) ∈ (tokenDummyHypergraph G m p z).edge e)) =
      n * (vertexLoad G x v / (p : ℝ)) := by
  classical
  unfold FiniteBernoulli.mean tokenDummySampleProbability
  rw [← Finset.mul_sum]
  rw [tokenDummy_weighted_original_token_codegree G m p z hp hz x hstable v c]

end OriginalTokenCodegree

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section DummyStablePredicate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fixed dummy receives the same `j/z` share from any family selected
by its stable-set coordinate.
@isnad1 id=eq.3h8v.s8.4fefc857a230 from=translated src=- shape=a55f4915 vocab=13ee6961
-/
theorem sum_tokenDummyWeight_dummy_stable_pred (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (P : StableSet G → Prop) [DecidablePred P] (d : Fin z) :
    (∑ e : TokenDummyLabel G p z,
      if P e.1 ∧ d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
      ∑ S : StableSet G,
        if P S then x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) else 0 := by
  classical
  calc
    (∑ e : TokenDummyLabel G p z,
      if P e.1 ∧ d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
        ∑ S : StableSet G, ∑ c : Fin p, ∑ T : Finset (Fin z),
          if P S ∧ d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.sum_prod_type]
    _ = ∑ S : StableSet G,
          if P S then ∑ c : Fin p, ∑ T : Finset (Fin z),
            if d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hP : P S <;> simp [hP]
    _ = ∑ S : StableSet G,
          if P S then x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hP : P S
      · simp only [hP, ite_true]
        exact sum_tokenDummyWeight_fixed_dummy G m p z hp hz x S (hstable S) d
      · simp [hP]

end DummyStablePredicate

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section OriginalDummyCodegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact original-dummy weighted codegree before applying the dummy-count
bound.
@isnad1 id=eq.3h8v.s9.e03d603223ec from=translated src=- shape=fb43bfce vocab=ff29b92b
-/
theorem tokenDummy_weighted_original_dummy_codegree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (v : V) (d : Fin z) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inr d) ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) =
      ∑ S : StableSet G,
        if v ∈ S.1 then x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) else 0 := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hfilter :
      H.edges.filter (fun e => Sum.inl v ∈ H.edge e ∧
        Sum.inr (Sum.inr d) ∈ H.edge e) =
      H.edges.filter (fun e : TokenDummyLabel G p z =>
        v ∈ e.1.1 ∧ d ∈ e.2.2) := by
    ext e
    simp only [Finset.mem_filter]
    change (e ∈ H.edges ∧ Sum.inl v ∈ tokenDummyEdge G e ∧
      Sum.inr (Sum.inr d) ∈ tokenDummyEdge G e) ↔
      (e ∈ H.edges ∧ v ∈ e.1.1 ∧ d ∈ e.2.2)
    simp
  change (H.edges.filter (fun e => Sum.inl v ∈ H.edge e ∧
    Sum.inr (Sum.inr d) ∈ H.edge e)).sum
    (tokenDummyWeight G m p z x) = _
  rw [hfilter, Finset.sum_filter]
  calc
    (∑ e ∈ H.edges,
      if v ∈ e.1.1 ∧ d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
        ∑ e : TokenDummyLabel G p z,
          if v ∈ e.1.1 ∧ d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.edges)
      intro e heuniv henot
      simp [tokenDummyWeight, H, henot]
    _ = _ := sum_tokenDummyWeight_dummy_stable_pred G m p z hp hz x hstable
      (fun S => v ∈ S.1) d

end OriginalDummyCodegree

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section OriginalDummyBound

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The nonempty stable-set condition makes every edge use at most `m`
dummy vertices.
@isnad1 id=le.4h8v.s9.feb08730ee07 from=translated src=- shape=bf3bf7b5 vocab=ea676fd7
-/
theorem tokenDummy_weighted_original_dummy_codegree_le (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (v : V) (d : Fin z) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inl v ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inr d) ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) ≤
      vertexLoad G x v * ((m : ℝ) / (z : ℝ)) := by
  classical
  rw [tokenDummy_weighted_original_dummy_codegree G m p z hp hz x hstable v d]
  have hterm (S : StableSet G) :
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) ≤
        x S * ((m : ℝ) / (z : ℝ)) := by
    have hcard : 0 < S.1.card := S.2.1.card_pos
    have hnat : m + 1 - S.1.card ≤ m := by omega
    have hreal : ((m + 1 - S.1.card : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hreal (Nat.cast_nonneg z)) (hx S)
  calc
    (∑ S : StableSet G,
      if v ∈ S.1 then x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) else 0) ≤
      ∑ S : StableSet G,
        if v ∈ S.1 then x S * ((m : ℝ) / (z : ℝ)) else 0 := by
      apply Finset.sum_le_sum
      intro S hS
      by_cases hv : v ∈ S.1
      · simpa [hv] using hterm S
      · simp [hv]
    _ = vertexLoad G x v * ((m : ℝ) / (z : ℝ)) := by
      simp [vertexLoad, Finset.sum_mul, ite_mul]

end OriginalDummyBound

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section TokenDummyPair

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fixed token receives `1/p` of each fixed-dummy incidence mass.
@isnad1 id=eq.3h9v.s7.faab0a1873fd from=translated src=- shape=6cd40b3c vocab=dd2bc19e
-/
theorem sum_tokenDummyWeight_fixed_token_dummy (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (S : StableSet G)
    (hS : S.1.card ≤ m) (c : Fin p) (d : Fin z) :
    (∑ T : Finset (Fin z),
      if d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) =
      (x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ))) / (p : ℝ) := by
  classical
  let Y := ∑ T : Finset (Fin z),
    if d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0
  have hsame (c' : Fin p) :
      (∑ T : Finset (Fin z),
        if d ∈ T then tokenDummyWeight G m p z x (S, c', T) else 0) = Y := by
    apply Finset.sum_congr rfl
    intro T hT
    simp [tokenDummyWeight, tokenDummyHypergraph]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have htotal : (p : ℝ) * Y =
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) := by
    calc
      (p : ℝ) * Y = ∑ c' : Fin p, Y := by simp
      _ = ∑ c' : Fin p, ∑ T : Finset (Fin z),
          if d ∈ T then tokenDummyWeight G m p z x (S, c', T) else 0 := by
        apply Finset.sum_congr rfl
        intro c' hc'
        exact (hsame c').symm
      _ = _ := sum_tokenDummyWeight_fixed_dummy G m p z hp hz x S hS d
  apply (eq_div_iff hpR).2
  change Y * (p : ℝ) = _
  simpa [mul_comm] using htotal

end TokenDummyPair

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section TokenDummyCodegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The token-dummy weighted codegree is a `1/p` share of a dummy degree.
@isnad1 id=eq.3h8v.s9.469fc034c721 from=translated src=- shape=da30a7fd vocab=b8e01377
-/
theorem tokenDummy_weighted_token_dummy_codegree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (c : Fin p) (d : Fin z) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inl c) ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inr d) ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) =
      (∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ))) / (p : ℝ) := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hfilter :
      H.edges.filter (fun e => Sum.inr (Sum.inl c) ∈ H.edge e ∧
        Sum.inr (Sum.inr d) ∈ H.edge e) =
      H.edges.filter (fun e : TokenDummyLabel G p z =>
        c = e.2.1 ∧ d ∈ e.2.2) := by
    ext e
    simp only [Finset.mem_filter]
    change (e ∈ H.edges ∧ Sum.inr (Sum.inl c) ∈ tokenDummyEdge G e ∧
      Sum.inr (Sum.inr d) ∈ tokenDummyEdge G e) ↔
      (e ∈ H.edges ∧ c = e.2.1 ∧ d ∈ e.2.2)
    simp
  change (H.edges.filter (fun e => Sum.inr (Sum.inl c) ∈ H.edge e ∧
    Sum.inr (Sum.inr d) ∈ H.edge e)).sum (tokenDummyWeight G m p z x) = _
  rw [hfilter, Finset.sum_filter]
  calc
    (∑ e ∈ H.edges,
      if c = e.2.1 ∧ d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
        ∑ e : TokenDummyLabel G p z,
          if c = e.2.1 ∧ d ∈ e.2.2 then tokenDummyWeight G m p z x e else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.edges)
      intro e heuniv henot
      simp [tokenDummyWeight, H, henot]
    _ = ∑ S : StableSet G, ∑ T : Finset (Fin z),
          if d ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.sum_prod_type]
      calc
        (∑ c' : Fin p, ∑ T : Finset (Fin z),
          if c = c' ∧ d ∈ T then tokenDummyWeight G m p z x (S, c', T) else 0) =
            ∑ c' : Fin p,
              if c = c' then ∑ T : Finset (Fin z),
                if d ∈ T then tokenDummyWeight G m p z x (S, c', T) else 0 else 0 := by
          apply Finset.sum_congr rfl
          intro c' hc'
          by_cases hcc : c = c' <;> simp [hcc]
        _ = _ := by simp
    _ = ∑ S : StableSet G,
          (x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ))) / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact sum_tokenDummyWeight_fixed_token_dummy G m p z hp hz x S (hstable S) c d
    _ = _ := by simp [div_eq_mul_inv, Finset.sum_mul]

/-- With exact unit original loads, token-dummy codegree has the paper's
closed formula.
@isnad1 id=eq.4h8v.s9.04975a9e2d2f from=translated src=- shape=81192756 vocab=a0d957f3
-/
theorem tokenDummy_weighted_token_dummy_codegree_exact (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (c : Fin p) (d : Fin z) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inl c) ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inr d) ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) =
      ((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ)) / (z : ℝ)) / (p : ℝ) := by
  rw [tokenDummy_weighted_token_dummy_codegree G m p z hp hz x hstable c d,
    sum_dummy_mass_eq G m z x hstable hload]

end TokenDummyCodegree

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section TwoDummyCounting

/-- Number of `j`-subsets of `Fin z` containing two distinct fixed
vertices.
@isnad1 id=eq.2h4v.s7.5d08c7730a00 from=translated src=- shape=5b2f706b vocab=e122d4cb
-/
theorem card_dummy_subsets_two_mem (z j : ℕ) (d d' : Fin z)
    (hne : d ≠ d') (hj : 2 ≤ j) :
    (Finset.univ.filter (fun T : Finset (Fin z) =>
      T.card = j ∧ d ∈ T ∧ d' ∈ T)).card =
      Nat.choose (z - 2) (j - 2) := by
  classical
  have htwo : ({d, d'} : Finset (Fin z)).card = 2 := by
    simp [hne]
  have hset :
      (Finset.univ.filter (fun T : Finset (Fin z) =>
        T.card = j ∧ d ∈ T ∧ d' ∈ T)) =
      ((Finset.univ : Finset (Fin z)).powersetCard j).filter
        (fun T => ({d,d'} : Finset (Fin z)) ⊆ T) := by
    ext T
    simp [Finset.mem_powersetCard, Finset.insert_subset_iff,
      Finset.singleton_subset_iff]
  rw [hset, Finset.card_filter_powersetCard_subset]
  · simp [htwo]
  · simp
  · simpa [htwo] using hj

end TwoDummyCounting

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

/-- The double-incidence binomial identity, obtained by applying the
one-incidence identity twice.
@isnad1 id=eq.2h2v.s6.dc4984d225bd from=translated src=- shape=f59eed85 vocab=005aed2a
-/
theorem choose_two_incidence (z j : ℕ) (hz : 2 ≤ z) (hj : 2 ≤ j) :
    z * (z - 1) * Nat.choose (z - 2) (j - 2) =
      j * (j - 1) * Nat.choose z j := by
  have h1 :
      (z - 1) * Nat.choose (z - 2) (j - 2) =
        (j - 1) * Nat.choose (z - 1) (j - 1) := by
    have h := Nat.add_one_mul_choose_eq (z - 2) (j - 2)
    have hz1 : z - 2 + 1 = z - 1 := by omega
    have hj1 : j - 2 + 1 = j - 1 := by omega
    simpa [hz1, hj1, mul_comm] using h
  have h2 :
      z * Nat.choose (z - 1) (j - 1) =
        j * Nat.choose z j := by
    have h := Nat.add_one_mul_choose_eq (z - 1) (j - 1)
    have hz1 : z - 1 + 1 = z := by omega
    have hj1 : j - 1 + 1 = j := by omega
    simpa [hz1, hj1, mul_comm] using h
  calc
    z * (z - 1) * Nat.choose (z - 2) (j - 2) =
      z * ((z - 1) * Nat.choose (z - 2) (j - 2)) := by ring
    _ = z * ((j - 1) * Nat.choose (z - 1) (j - 1)) := by rw [h1]
    _ = (j - 1) * (z * Nat.choose (z - 1) (j - 1)) := by ring
    _ = (j - 1) * (j * Nat.choose z j) := by rw [h2]
    _ = j * (j - 1) * Nat.choose z j := by ring

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

/-- Fraction of `j`-subsets containing two fixed distinct dummy vertices.
@isnad1 id=eq.3h4v.s8.60363e235971 from=translated src=- shape=46d8fc90 vocab=99375bed
-/
theorem sum_dummy_two_mem_recip_choose (z j : ℕ)
    (hj : 2 ≤ j) (hjz : j ≤ z) (d d' : Fin z) (hne : d ≠ d') :
    (∑ T : Finset (Fin z),
      if T.card = j ∧ d ∈ T ∧ d' ∈ T then
        (1 : ℝ) / (Nat.choose z j : ℝ) else 0) =
      ((j : ℝ) * ((j - 1 : ℕ) : ℝ)) /
        ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) := by
  classical
  have hz : 2 ≤ z := hj.trans hjz
  have hcard := card_dummy_subsets_two_mem z j d d' hne hj
  have hnat := choose_two_incidence z j hz hj
  have hnatR :
      (z : ℝ) * ((z - 1 : ℕ) : ℝ) *
        (Nat.choose (z - 2) (j - 2) : ℝ) =
      (j : ℝ) * ((j - 1 : ℕ) : ℝ) * (Nat.choose z j : ℝ) := by
    exact_mod_cast hnat
  have hzR : (z : ℝ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
  have hz1R : ((z - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : z - 1 ≠ 0)
  have hjR : (Nat.choose z j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjz).ne'
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
    hcard, nsmul_eq_mul]
  field_simp
  nlinarith [hnatR]

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

/-- Scale the two-dummy incidence formula by a real mass.
@isnad1 id=eq.3h5v.s8.7c3c2b498582 from=translated src=- shape=28c36226 vocab=99375bed
-/
theorem sum_dummy_two_mem_scaled (z j : ℕ)
    (hj : 2 ≤ j) (hjz : j ≤ z) (d d' : Fin z) (hne : d ≠ d') (a : ℝ) :
    (∑ T : Finset (Fin z),
      if T.card = j ∧ d ∈ T ∧ d' ∈ T then
        a / (Nat.choose z j : ℝ) else 0) =
      a * (((j : ℝ) * ((j - 1 : ℕ) : ℝ)) /
        ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
  classical
  calc
    (∑ T : Finset (Fin z),
      if T.card = j ∧ d ∈ T ∧ d' ∈ T then
        a / (Nat.choose z j : ℝ) else 0) =
      a * (∑ T : Finset (Fin z),
        if T.card = j ∧ d ∈ T ∧ d' ∈ T then
          (1 : ℝ) / (Nat.choose z j : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      by_cases h : T.card = j ∧ d ∈ T ∧ d' ∈ T <;>
        simp [h, div_eq_mul_inv]
    _ = _ := by rw [sum_dummy_two_mem_recip_choose z j hj hjz d d' hne]

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section FixedTwoDummyWeight

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fixed stable-set mass is shared between two distinct dummy vertices
with the usual sampling-without-replacement factor.
@isnad1 id=eq.4h9v.s8.1e210983cff1 from=translated src=- shape=b7f2cd04 vocab=dd2bc19e
-/
theorem sum_tokenDummyWeight_fixed_two_dummy (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (S : StableSet G)
    (hS : S.1.card ≤ m) (d d' : Fin z) (hne : d ≠ d') :
    (∑ c : Fin p, ∑ T : Finset (Fin z),
      if d ∈ T ∧ d' ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) =
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
        (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
        ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
  classical
  let j := m + 1 - S.1.card
  have hj : 0 < j := by dsimp [j]; omega
  have hjz : j ≤ z := by dsimp [j]; omega
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hterm (c : Fin p) (T : Finset (Fin z)) :
      (if d ∈ T ∧ d' ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) =
        if T.card = j ∧ d ∈ T ∧ d' ∈ T then
          x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0 := by
    rw [tokenDummyWeight_fixed_stable_eq G m p z x S hS c T]
    by_cases hd : d ∈ T <;> by_cases hd' : d' ∈ T <;>
      by_cases hT : T.card = j <;> simp [hd, hd', hT, j]
  change (∑ c : Fin p, ∑ T : Finset (Fin z),
      if d ∈ T ∧ d' ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) =
      x S * (((j : ℝ) * ((j - 1 : ℕ) : ℝ)) /
        ((z : ℝ) * ((z - 1 : ℕ) : ℝ)))
  by_cases hj2 : 2 ≤ j
  · have hinner :
        (∑ T : Finset (Fin z),
          if T.card = j ∧ d ∈ T ∧ d' ∈ T then
            x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0) =
          (x S / (p : ℝ)) * (((j : ℝ) * ((j - 1 : ℕ) : ℝ)) /
            ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
      calc
        (∑ T : Finset (Fin z),
          if T.card = j ∧ d ∈ T ∧ d' ∈ T then
            x S / ((p : ℝ) * (Nat.choose z j : ℝ)) else 0) =
          ∑ T : Finset (Fin z),
            if T.card = j ∧ d ∈ T ∧ d' ∈ T then
              (x S / (p : ℝ)) / (Nat.choose z j : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro T hT
            by_cases h : T.card = j ∧ d ∈ T ∧ d' ∈ T <;>
              simp [h, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]
        _ = _ := sum_dummy_two_mem_scaled z j hj2 hjz d d' hne (x S / (p : ℝ))
    calc
      (∑ c : Fin p, ∑ T : Finset (Fin z),
        if d ∈ T ∧ d' ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) =
        (p : ℝ) * ((x S / (p : ℝ)) *
          (((j : ℝ) * ((j - 1 : ℕ) : ℝ)) /
            ((z : ℝ) * ((z - 1 : ℕ) : ℝ)))) := by
          simp_rw [hterm]
          simp only [hinner, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ = _ := by field_simp
  · have hj1 : j = 1 := by omega
    have hno (T : Finset (Fin z)) :
        ¬(T.card = j ∧ d ∈ T ∧ d' ∈ T) := by
      rintro ⟨hcard, hd, hd'⟩
      have hsub : ({d, d'} : Finset (Fin z)) ⊆ T := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hd
        · exact hd'
      have hle := Finset.card_le_card hsub
      have htwo : ({d, d'} : Finset (Fin z)).card = 2 := by simp [hne]
      omega
    have hzero :
        (∑ c : Fin p, ∑ T : Finset (Fin z),
          if d ∈ T ∧ d' ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      apply Finset.sum_eq_zero
      intro T hT
      rw [hterm c T, ite_eq_right (hno T)]
    rw [hzero, hj1]
    norm_num

end FixedTwoDummyWeight

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section TwoDummyWeight

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact mass of all labels containing two distinct dummy vertices.
@isnad1 id=eq.4h8v.s9.145b8894ea56 from=translated src=- shape=8bf2306d vocab=bcee3395
-/
theorem sum_tokenDummyWeight_two_dummy (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (d d' : Fin z) (hne : d ≠ d') :
    (∑ e : TokenDummyLabel G p z,
      if d ∈ e.2.2 ∧ d' ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
      ∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
          (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
  classical
  calc
    (∑ e : TokenDummyLabel G p z,
      if d ∈ e.2.2 ∧ d' ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
        ∑ S : StableSet G, ∑ c : Fin p, ∑ T : Finset (Fin z),
          if d ∈ T ∧ d' ∈ T then tokenDummyWeight G m p z x (S, c, T) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.sum_prod_type]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      exact sum_tokenDummyWeight_fixed_two_dummy G m p z hp hz x S (hstable S) d d' hne

/-- The active token/dummy hypergraph has the same two-dummy mass.
@isnad1 id=eq.4h8v.s9.cf181c97e6d6 from=translated src=- shape=457ca219 vocab=78aa2a42
-/
theorem tokenDummy_weighted_two_dummy_codegree (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (d d' : Fin z) (hne : d ≠ d') :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inr d) ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inr d') ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) =
      ∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
          (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hfilter :
      H.edges.filter (fun e => Sum.inr (Sum.inr d) ∈ H.edge e ∧
        Sum.inr (Sum.inr d') ∈ H.edge e) =
      H.edges.filter (fun e : TokenDummyLabel G p z =>
        d ∈ e.2.2 ∧ d' ∈ e.2.2) := by
    ext e
    simp only [Finset.mem_filter]
    change (e ∈ H.edges ∧ Sum.inr (Sum.inr d) ∈ tokenDummyEdge G e ∧
      Sum.inr (Sum.inr d') ∈ tokenDummyEdge G e) ↔
      (e ∈ H.edges ∧ d ∈ e.2.2 ∧ d' ∈ e.2.2)
    simp
  change (H.edges.filter (fun e => Sum.inr (Sum.inr d) ∈ H.edge e ∧
    Sum.inr (Sum.inr d') ∈ H.edge e)).sum (tokenDummyWeight G m p z x) = _
  rw [hfilter, Finset.sum_filter]
  calc
    (∑ e ∈ H.edges,
      if d ∈ e.2.2 ∧ d' ∈ e.2.2 then tokenDummyWeight G m p z x e else 0) =
        ∑ e : TokenDummyLabel G p z,
          if d ∈ e.2.2 ∧ d' ∈ e.2.2 then tokenDummyWeight G m p z x e else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.edges)
      intro e heuniv henot
      simp [tokenDummyWeight, H, henot]
    _ = _ := sum_tokenDummyWeight_two_dummy G m p z hp hz x hstable d d' hne

end TwoDummyWeight

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section TwoDummyBound

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dummy-dummy weighted codegree is bounded by the maximum dummy
count squared times fractional cost.
@isnad1 id=le.6h8v.s9.e9347f81f6ef from=translated src=- shape=108fc25e vocab=a1751f56
-/
theorem tokenDummy_weighted_two_dummy_codegree_le (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z) (hz2 : 2 ≤ z)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (d d' : Fin z) (hne : d ≠ d') :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inr d) ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inr d') ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) ≤
      fractionalCost G x *
        (((m : ℝ) * ((m - 1 : ℕ) : ℝ)) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
  classical
  rw [tokenDummy_weighted_two_dummy_codegree G m p z hp hz x hstable d d' hne]
  have hterm (S : StableSet G) :
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
          (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) ≤
        x S * (((m : ℝ) * ((m - 1 : ℕ) : ℝ)) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
    have hcard : 0 < S.1.card := S.2.1.card_pos
    have hj : m + 1 - S.1.card ≤ m := by omega
    have hjpred : (m + 1 - S.1.card) - 1 ≤ m - 1 :=
      Nat.sub_le_sub_right hj 1
    have hprod : (m + 1 - S.1.card) * ((m + 1 - S.1.card) - 1) ≤
        m * (m - 1) := Nat.mul_le_mul hj hjpred
    have hprodR :
        (((m + 1 - S.1.card : ℕ) : ℝ) *
          (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ)) ≤
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast hprod
    have hden : 0 ≤ (z : ℝ) * ((z - 1 : ℕ) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hprodR hden) (hx S)
  calc
    (∑ S : StableSet G,
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
        (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
        ((z : ℝ) * ((z - 1 : ℕ) : ℝ)))) ≤
      ∑ S : StableSet G,
        x S * (((m : ℝ) * ((m - 1 : ℕ) : ℝ)) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro S hS
      exact hterm S
    _ = fractionalCost G x *
      (((m : ℝ) * ((m - 1 : ℕ) : ℝ)) /
        ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) := by
      simp [fractionalCost, Finset.sum_mul]

end TwoDummyBound

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section TwoTokenCodegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No edge copy contains two distinct color tokens.
@isnad1 id=eq.1h8v.s8.61f0d2b29a97 from=translated src=- shape=df4e9e3a vocab=75fd0531
-/
theorem tokenDummy_weighted_two_token_codegree (G : SimpleGraph V)
    (m p z : ℕ) (x : StableSet G → ℝ)
    (c c' : Fin p) (hne : c ≠ c') :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inl c) ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inl c') ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) = 0 := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hempty :
      H.edges.filter (fun e => Sum.inr (Sum.inl c) ∈ H.edge e ∧
        Sum.inr (Sum.inl c') ∈ H.edge e) = ∅ := by
    ext e
    constructor
    · intro hm
      obtain ⟨he, hc, hc'⟩ := Finset.mem_filter.mp hm
      have h1 : c = e.2.1 := by
        exact (token_mem_tokenDummyEdge G e c).mp hc
      have h2 : c' = e.2.1 := by
        exact (token_mem_tokenDummyEdge G e c').mp hc'
      exact False.elim (hne (h1.trans h2.symm))
    · intro hm
      simp at hm
  change (H.edges.filter (fun e => Sum.inr (Sum.inl c) ∈ H.edge e ∧
    Sum.inr (Sum.inl c') ∈ H.edge e)).sum (tokenDummyWeight G m p z x) = 0
  rw [hempty]
  simp

end TwoTokenCodegree

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section SampledConcentration

variable {W E : Type*} [DecidableEq W] [DecidableEq E] [Fintype E]

end SampledConcentration

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section GoodSample

variable {W E : Type*} [DecidableEq W] [DecidableEq E] [Fintype E]

end GoodSample

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section PairConstraintBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Pair LP rows control every distinct pair: adjacent pairs have zero
stable-set weight, and nonadjacent pairs have an explicit LP row.
@isnad1 id=le.3h6v.s8.357d101e5669 from=translated src=- shape=635d63d5 vocab=16ba02b4
-/
theorem pair_mass_le_of_isPairConstrained (G : SimpleGraph V)
    (δ : ℝ) (hδ : 0 ≤ δ) (x : StableSet G → ℝ)
    (hx : IsPairConstrainedColoring G δ x)
    (u v : V) (hne : u ≠ v) :
    (∑ S : StableSet G, if u ∈ S.1 ∧ v ∈ S.1 then x S else 0) ≤ δ := by
  classical
  rw [← pairLoad_pair G x u v]
  by_cases hadj : G.Adj u v
  · have hzero : pairLoad G x {u, v} = 0 := by
      rw [pairLoad_pair]
      apply Finset.sum_eq_zero
      intro S hS
      have hnot : ¬ (u ∈ S.1 ∧ v ∈ S.1) := by
        rintro ⟨hu, hv⟩
        exact (S.2.2 hu hv hne) hadj
      simp [hnot]
    rw [hzero]
    exact hδ
  · have hindep : G.IsIndepSet ({u, v} : Set V) := by
      rw [G.isIndepSet_iff]
      intro a ha b hb hab
      have ha' : a = u ∨ a = v := by simpa using ha
      have hb' : b = u ∨ b = v := by simpa using hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact False.elim (hab rfl)
      · exact hadj
      · intro h
        exact hadj h.symm
      · exact False.elim (hab rfl)
    let q : NonedgePair G := ⟨{u, v}, by
      constructor
      · simp [hne]
      · simpa using hindep⟩
    exact hx.2 q

end PairConstraintBridge

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section UniformCodegreeBudget

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All six distinct vertex-pair types meet one weighted codegree budget
when the four mixed/dummy ratios and the LP pair tolerance do.
@isnad1 id=le.13h10v.s9.a3c495b492a8 from=translated src=- shape=275a2b12 vocab=0438a0c4
-/
theorem tokenDummy_weighted_codegree_le (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z) (hz2 : 2 ≤ z)
    (δ B : ℝ) (hδ : 0 ≤ δ)
    (x : StableSet G → ℝ)
    (hx : IsPairConstrainedColoring G δ x)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hOO : δ ≤ B)
    (hOT : (1 : ℝ) / (p : ℝ) ≤ B)
    (hOD : (m : ℝ) / (z : ℝ) ≤ B)
    (hTD : (((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ)) / (z : ℝ)) / (p : ℝ)) ≤ B)
    (hDD : fractionalCost G x *
        (((m : ℝ) * ((m - 1 : ℕ) : ℝ)) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) ≤ B)
    (a b : TokenDummyVertex V p z) (hab : a ≠ b) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => a ∈ (tokenDummyHypergraph G m p z).edge e ∧
        b ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) ≤ B := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hswap (a b : TokenDummyVertex V p z) :
      (H.edges.filter (fun e => a ∈ H.edge e ∧ b ∈ H.edge e)).sum
        (tokenDummyWeight G m p z x) =
      (H.edges.filter (fun e => b ∈ H.edge e ∧ a ∈ H.edge e)).sum
        (tokenDummyWeight G m p z x) := by
    congr 1
    ext e
    simp [and_comm]
  have hB : 0 ≤ B := hδ.trans hOO
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      have huv : u ≠ v := by
        intro heq
        apply hab
        simp [heq]
      calc
        _ = ∑ S : StableSet G,
          if u ∈ S.1 ∧ v ∈ S.1 then x S else 0 :=
          tokenDummy_weighted_original_codegree G m p z hp hz x hstable u v
        _ ≤ δ := pair_mass_le_of_isPairConstrained G δ hδ x hx u v huv
        _ ≤ B := hOO
    | inr q =>
      cases q with
      | inl c =>
        calc
          _ = vertexLoad G x u / (p : ℝ) :=
            tokenDummy_weighted_original_token_codegree G m p z hp hz x hstable u c
          _ = (1 : ℝ) / (p : ℝ) := by rw [hload u]
          _ ≤ B := hOT
      | inr d =>
        calc
          _ ≤ vertexLoad G x u * ((m : ℝ) / (z : ℝ)) :=
            tokenDummy_weighted_original_dummy_codegree_le
              G m p z hp hz x hx.1.1 hstable u d
          _ = (m : ℝ) / (z : ℝ) := by rw [hload u, one_mul]
          _ ≤ B := hOD
  | inr q =>
    cases q with
    | inl c =>
      cases b with
      | inl u =>
        calc
          _ = (H.edges.filter (fun e => Sum.inl u ∈ H.edge e ∧
              Sum.inr (Sum.inl c) ∈ H.edge e)).sum
              (tokenDummyWeight G m p z x) := hswap _ _
          _ = vertexLoad G x u / (p : ℝ) :=
            tokenDummy_weighted_original_token_codegree G m p z hp hz x hstable u c
          _ = (1 : ℝ) / (p : ℝ) := by rw [hload u]
          _ ≤ B := hOT
      | inr q' =>
        cases q' with
        | inl c' =>
          have hcc : c ≠ c' := by
            intro heq
            apply hab
            simp [heq]
          calc
            _ = 0 := tokenDummy_weighted_two_token_codegree G m p z x c c' hcc
            _ ≤ B := hB
        | inr d =>
          calc
            _ = (((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
              (Fintype.card V : ℝ)) / (z : ℝ)) / (p : ℝ)) :=
              tokenDummy_weighted_token_dummy_codegree_exact
                G m p z hp hz x hstable hload c d
            _ ≤ B := hTD
    | inr d =>
      cases b with
      | inl u =>
        calc
          _ = (H.edges.filter (fun e => Sum.inl u ∈ H.edge e ∧
              Sum.inr (Sum.inr d) ∈ H.edge e)).sum
              (tokenDummyWeight G m p z x) := hswap _ _
          _ ≤ vertexLoad G x u * ((m : ℝ) / (z : ℝ)) :=
            tokenDummy_weighted_original_dummy_codegree_le
              G m p z hp hz x hx.1.1 hstable u d
          _ = (m : ℝ) / (z : ℝ) := by rw [hload u, one_mul]
          _ ≤ B := hOD
      | inr q' =>
        cases q' with
        | inl c =>
          calc
            _ = (H.edges.filter (fun e => Sum.inr (Sum.inl c) ∈ H.edge e ∧
                Sum.inr (Sum.inr d) ∈ H.edge e)).sum
                (tokenDummyWeight G m p z x) := hswap _ _
            _ = (((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
              (Fintype.card V : ℝ)) / (z : ℝ)) / (p : ℝ)) :=
              tokenDummy_weighted_token_dummy_codegree_exact
                G m p z hp hz x hstable hload c d
            _ ≤ B := hTD
        | inr d' =>
          have hdd : d ≠ d' := by
            intro heq
            apply hab
            simp [heq]
          exact (tokenDummy_weighted_two_dummy_codegree_le
            G m p z hp hz hz2 x hx.1.1 hstable d d' hdd).trans hDD

end UniformCodegreeBudget

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

/-- Every interior binomial coefficient is at least the row number.
@isnad1 id=le.2h2v.s4.6e7b58967093 from=translated src=- shape=02ddb093 vocab=9e20b754
-/
theorem choose_ge_self_of_pos_lt : ∀ z j : ℕ,
    0 < j → j < z → z ≤ Nat.choose z j := by
  intro z
  induction z with
  | zero =>
      intro j hj hjz
      omega
  | succ z ih =>
      intro j hj hjz
      by_cases hlast : j = z
      · subst j
        simp
      · have hjlt : j < z := by omega
        have hprev : z ≤ Nat.choose z j := ih j hj hjlt
        have hpos : 0 < Nat.choose z (j - 1) :=
          Nat.choose_pos (by omega)
        have hrec : Nat.choose (z + 1) j =
            Nat.choose z (j - 1) + Nat.choose z j := by
          cases j with
          | zero => omega
          | succ k =>
              simpa [Nat.succ_eq_add_one] using
                Nat.choose_succ_succ' z k
        omega

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section SampleProbability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty stable-set column has weight at most one under exact unit
vertex loads and nonnegative column weights.
@isnad1 id=le.2h4v.s6.1fbba92b6bca from=translated src=- shape=afca533f vocab=530e2e70
-/
theorem stable_weight_le_one_of_exact_load (G : SimpleGraph V)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hload : ∀ v, vertexLoad G x v = 1) (S : StableSet G) :
    x S ≤ 1 := by
  classical
  obtain ⟨v, hv⟩ := S.2.1
  have hle : (if v ∈ S.1 then x S else 0) ≤ vertexLoad G x v := by
    unfold vertexLoad
    have hnonneg : ∀ T ∈ (Finset.univ : Finset (StableSet G)),
        0 ≤ (if v ∈ T.1 then x T else 0) := by
      intro T hT
      by_cases hTv : v ∈ T.1
      · simp [hTv, hx T]
      · simp [hTv]
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (StableSet G)))
      (f := fun T : StableSet G => if v ∈ T.1 then x T else 0)
      hnonneg (Finset.mem_univ S)
  simpa [hv, hload v] using hle

/-- Under the paper's token and dummy count lower bounds, every edge-copy
sampling parameter is a genuine probability.
@isnad1 id=and.7h8v.s7.222d878615a2 from=translated src=- shape=abee78ff vocab=3f4faaed
-/
theorem tokenDummySampleProbability_bounds (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (n : ℝ) (hn : 0 ≤ n) (hnpz : n ≤ (p : ℝ) * (z : ℝ))
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (e : TokenDummyLabel G p z) :
    0 ≤ tokenDummySampleProbability G m p z n x e ∧
      tokenDummySampleProbability G m p z n x e ≤ 1 := by
  classical
  constructor
  · exact mul_nonneg hn (tokenDummyWeight_nonneg G m p z x hx e)
  · unfold tokenDummySampleProbability tokenDummyWeight
    by_cases he : e ∈ (tokenDummyHypergraph G m p z).edges
    · rw [ite_eq_left he]
      have hvalid : e.1.1.card + e.2.2.card = m + 1 :=
        (Finset.mem_filter.mp he).2
      have hcard : 0 < e.1.1.card := e.1.2.1.card_pos
      have hS : e.1.1.card ≤ m := hstable e.1
      have hj : 0 < e.2.2.card := by omega
      have hjlt : e.2.2.card < z := by omega
      have hchoose : z ≤ Nat.choose z e.2.2.card :=
        choose_ge_self_of_pos_lt z e.2.2.card hj hjlt
      have hchooseR : (z : ℝ) ≤ (Nat.choose z e.2.2.card : ℝ) := by
        exact_mod_cast hchoose
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
      have hden : 0 < (p : ℝ) * (Nat.choose z e.2.2.card : ℝ) := by
        have hzR : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
        exact mul_pos hpR (lt_of_lt_of_le hzR hchooseR)
      have hweight := stable_weight_le_one_of_exact_load G x hx hload e.1
      have hprod : (p : ℝ) * (z : ℝ) ≤
          (p : ℝ) * (Nat.choose z e.2.2.card : ℝ) :=
        mul_le_mul_of_nonneg_left hchooseR hpR.le
      calc
        n * (x e.1 / ((p : ℝ) * (Nat.choose z e.2.2.card : ℝ))) =
          n * x e.1 / ((p : ℝ) * (Nat.choose z e.2.2.card : ℝ)) := by ring
        _ ≤ 1 := by
          apply (div_le_iff₀ hden).2
          nlinarith [mul_le_mul_of_nonneg_left hweight hn]
    · rw [ite_eq_right he, mul_zero]
      exact zero_le_one

end SampleProbability

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section SampledMatchingTransfer

variable {W E : Type*} [DecidableEq W] [DecidableEq E] [Fintype E]

omit [DecidableEq W] [DecidableEq E] [Fintype E] in
/-- A matching found after Bernoulli sampling is a matching in the
original indexed hypergraph.
@isnad1 id=ismatchi.1h5v.s4.08e8daf8bc87 from=translated src=- shape=f93c828e vocab=a67de3c1
-/
theorem sampled_matching_lift (H : IndexedHypergraph W E)
    (ω : E → Bool) (M : Finset E)
    (hM : (sampledHypergraph H ω).IsMatching M) :
    H.IsMatching M := by
  constructor
  · exact hM.1.trans (Finset.filter_subset _ _)
  · exact hM.2

omit [DecidableEq E] [Fintype E] in
/-- Sampling changes which copies are active but preserves the endpoint
set of every edge copy, hence the covered set of a fixed matching.
@isnad1 id=eq.0h5v.s5.0417ababc5f6 from=translated src=- shape=546ea6c1 vocab=a64ea6eb
-/
theorem sampled_covered_eq (H : IndexedHypergraph W E)
    (ω : E → Bool) (M : Finset E) :
    (sampledHypergraph H ω).covered M = H.covered M := rfl

end SampledMatchingTransfer

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The auxiliary hypergraph has the original vertices, one vertex per
token, and one vertex per dummy.
@isnad1 id=eq.0h5v.s5.5a68f48193eb from=translated src=- shape=3d24e0ca vocab=7541b3f9
-/
theorem tokenDummy_vertices_card (G : SimpleGraph V) (m p z : ℕ) :
    (tokenDummyHypergraph G m p z).vertices.card = Fintype.card V + p + z := by
  classical
  simp [tokenDummyHypergraph, TokenDummyVertex, Fintype.card_sum, Nat.add_assoc]

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

/-- The exact degree/codegree union budget is dominated by the paper-sized
single exponential budget. `N` counts vertices and `P` counts distinct pairs.
@isnad1 id=le.8h5v.s8.2b367e81a513 from=translated src=- shape=11e21fad vocab=597a0a46
-/
theorem sampled_budget_le_paper_budget (r n μ N P : ℝ)
    (hr : 2 ≤ r) (hn : 1 ≤ n) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hN0 : 0 ≤ N) (hP0 : 0 ≤ P)
    (hN : N ≤ r * n + 2) (hP : P ≤ N ^ 2) :
    2 * N * Real.exp (-(μ ^ 2 * n / 256)) +
        P * Real.exp (-(μ * n / 16)) ≤
      8 * r ^ 2 * n ^ 2 * Real.exp (-(μ ^ 2 * n / 256)) := by
  have hn0 : 0 ≤ n := by linarith
  have hμ0 : 0 ≤ μ := hμ.le
  have hμsq : μ ^ 2 ≤ μ := by
    nlinarith [mul_nonneg hμ0 (sub_nonneg.mpr hμ1)]
  have hμsqn : μ ^ 2 * n ≤ μ * n :=
    mul_le_mul_of_nonneg_right hμsq hn0
  have harg : -(μ * n / 16) ≤ -(μ ^ 2 * n / 256) := by
    nlinarith [hμsqn, mul_nonneg hμ0 hn0]
  have hq : Real.exp (-(μ * n / 16)) ≤
      Real.exp (-(μ ^ 2 * n / 256)) := Real.exp_le_exp.mpr harg
  have hq0 : 0 ≤ Real.exp (-(μ ^ 2 * n / 256)) := (Real.exp_pos _).le
  let t := r * n
  have ht : 2 ≤ t := by
    dsimp [t]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hn)]
  have hN2 : N ≤ 2 * t := by
    dsimp [t]
    linarith
  have hNsq : N ^ 2 ≤ (2 * t) ^ 2 := by
    have ht0 : 0 ≤ 2 * t := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hN2) (add_nonneg hN0 ht0)]
  have htt : t ≤ t ^ 2 := by
    have ht0 : 0 ≤ t := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) ht0]
  have hmid : 2 * N + N ^ 2 ≤ 8 * r ^ 2 * n ^ 2 := by
    dsimp [t] at hN2 hNsq htt
    nlinarith
  have hcode : P * Real.exp (-(μ * n / 16)) ≤
      N ^ 2 * Real.exp (-(μ ^ 2 * n / 256)) :=
    (mul_le_mul_of_nonneg_left hq hP0).trans
      (mul_le_mul_of_nonneg_right hP hq0)
  have hsize := mul_le_mul_of_nonneg_right hmid hq0
  nlinarith

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section UnionBudgetInstantiation

variable {W E : Type*} [DecidableEq W]

/-- The number of ordered distinct active vertex pairs is at most the
square of the active vertex count.
@isnad1 id=le.0h3v.s6.2f7ea3cfd54b from=translated src=- shape=5f36e776 vocab=39d7021f
-/
theorem card_distinct_active_pairs_le_sq (H : IndexedHypergraph W E) :
    ((((H.vertices.product H.vertices).filter
      (fun q : W × W => q.1 ≠ q.2)).card : ℝ)) ≤
      (H.vertices.card : ℝ) ^ 2 := by
  classical
  have hnat :
      ((H.vertices.product H.vertices).filter
        (fun q : W × W => q.1 ≠ q.2)).card ≤
        H.vertices.card ^ 2 := by
    calc
      _ ≤ (H.vertices.product H.vertices).card :=
        Finset.card_filter_le _ _
      _ = H.vertices.card ^ 2 := by
        simp [pow_two]
  exact_mod_cast hnat

/-- The explicit quantitative exponential estimate implies the precise
finite union budget needed for a simultaneous good sample.
@isnad1 id=lt.6h6v.s8.dec29aeaf48d from=translated src=- shape=8c61fc7b vocab=4e257d2c
-/
theorem sampled_exact_union_budget_lt_one (H : IndexedHypergraph W E)
    (r : ℕ) (n μ : ℝ)
    (hr : 2 ≤ r) (hn : 1 ≤ n) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hN : (H.vertices.card : ℝ) ≤ (r : ℝ) * n + 2)
    (hscale : 1000000 * (r : ℝ) ^ 4 ≤ μ ^ 4 * n) :
    2 * (H.vertices.card : ℝ) *
        Real.exp (-((μ * n / 8) ^ 2) / (4 * n)) +
      (((H.vertices.product H.vertices).filter
        (fun q : W × W => q.1 ≠ q.2)).card : ℝ) *
        Real.exp (-(μ * n / 2) / 8) < 1 := by
  let N : ℝ := H.vertices.card
  let P : ℝ := ((H.vertices.product H.vertices).filter
    (fun q : W × W => q.1 ≠ q.2)).card
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hP : P ≤ N ^ 2 := card_distinct_active_pairs_le_sq H
  have hcomp := sampled_budget_le_paper_budget
    (r : ℝ) n μ N P hrR hn hμ hμ1 hN0 hP0 hN hP
  have hpaper := HadwigerLean.Theorem2.sampled_union_budget_lt_one
    hrR hμ hscale
  have hbudget :
      2 * N * Real.exp (-(μ ^ 2 * n / 256)) +
        P * Real.exp (-(μ * n / 16)) < 1 :=
    lt_of_le_of_lt hcomp hpaper
  have hn0 : n ≠ 0 := by linarith
  have hdegExp : -((μ * n / 8) ^ 2) / (4 * n) =
      -(μ ^ 2 * n / 256) := by
    field_simp
    ring
  have hcodeExp : -(μ * n / 2) / 8 = -(μ * n / 16) := by ring
  simpa only [N, P, hdegExp, hcodeExp] using hbudget

end UnionBudgetInstantiation

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section FractionalCostBounds

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact original loads and nonempty columns imply that fractional cost
is at most the number of original vertices.
@isnad1 id=le.2h3v.s6.b84daf196a28 from=translated src=- shape=f82377a2 vocab=8520bdfa
-/
theorem fractionalCost_le_card_of_exact_load (G : SimpleGraph V)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hload : ∀ v, vertexLoad G x v = 1) :
    fractionalCost G x ≤ (Fintype.card V : ℝ) := by
  classical
  calc
    fractionalCost G x = ∑ S : StableSet G, x S := rfl
    _ ≤ ∑ S : StableSet G, (S.1.card : ℝ) * x S := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard : 1 ≤ (S.1.card : ℝ) := by
        exact_mod_cast S.2.1.card_pos
      nlinarith [mul_le_mul_of_nonneg_right hcard (hx S)]
    _ = (Fintype.card V : ℝ) := sum_stable_card_weight_eq_vertices G x hload

/-- If every stable set has size at most `m`, the vertex count is at
most `m` times the fractional cost.
@isnad1 id=le.3h4v.s6.6e6ce40ae22f from=translated src=- shape=17967681 vocab=1dd179c3
-/
theorem card_le_m_mul_fractionalCost (G : SimpleGraph V)
    (m : ℕ) (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1) :
    (Fintype.card V : ℝ) ≤ (m : ℝ) * fractionalCost G x := by
  classical
  calc
    (Fintype.card V : ℝ) =
        ∑ S : StableSet G, (S.1.card : ℝ) * x S :=
      (sum_stable_card_weight_eq_vertices G x hload).symm
    _ ≤ ∑ S : StableSet G, (m : ℝ) * x S := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard : (S.1.card : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hstable S
      exact mul_le_mul_of_nonneg_right hcard (hx S)
    _ = (m : ℝ) * fractionalCost G x := by
      simp [fractionalCost, Finset.mul_sum]

end FractionalCostBounds

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

/-- Rounding a positive mass `a` to a denominator `b ∈ [a,a+1]`
loses at most `m` from an `n`-scaled unit degree when `m*a ≥ n`.
@isnad1 id=and.6h4v.s7.781b540e5e45 from=translated src=- shape=4b680b3b vocab=1b82c742
-/
theorem scaled_rounded_ratio_between (n m a b : ℝ)
    (hm : 0 ≤ m) (hn : m ≤ n) (hma : n ≤ m * a)
    (hb : 0 < b) (hab : a ≤ b) (hba : b ≤ a + 1) :
    n - m ≤ n * (a / b) ∧ n * (a / b) ≤ n := by
  have hn0 : 0 ≤ n := by linarith
  have hnm : 0 ≤ n - m := by linarith
  have hleft := mul_le_mul_of_nonneg_left hba hnm
  have hbound : (n - m) * b ≤ n * a := by nlinarith
  have hlow : n - m ≤ n * a / b := (le_div_iff₀ hb).2 hbound
  have hright := mul_le_mul_of_nonneg_left hab hn0
  have hupp : n * a / b ≤ n := (div_le_iff₀ hb).2 (by nlinarith)
  constructor
  · calc
      n - m ≤ n * a / b := hlow
      _ = n * (a / b) := by ring
  · calc
      n * (a / b) = n * a / b := by ring
      _ ≤ n := hupp

end HadwigerLean.LowCodegreeRounding
namespace HadwigerLean.LowCodegreeRounding

section SampledMeanRegularity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every auxiliary vertex has expected sampled degree between `n-m`
and `n`, provided token and dummy counts round their ideal masses up
by at most one.
@isnad1 id=and.10h7v.s9.732592887e92 from=translated src=- shape=68b349ad vocab=f34beac5
-/
theorem tokenDummy_expected_degree_between (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hnlarge : m ≤ Fintype.card V)
    (hTlower : fractionalCost G x ≤ (p : ℝ))
    (hTupper : (p : ℝ) ≤ fractionalCost G x + 1)
    (hZlower : ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ) ≤ (z : ℝ))
    (hZupper : (z : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ) + 1)
    (a : TokenDummyVertex V p z) :
    (Fintype.card V : ℝ) - (m : ℝ) ≤
      FiniteBernoulli.mean
        (tokenDummySampleProbability G m p z (Fintype.card V : ℝ) x)
        ((tokenDummyHypergraph G m p z).edges.filter
          (fun e => a ∈ (tokenDummyHypergraph G m p z).edge e)) ∧
    FiniteBernoulli.mean
        (tokenDummySampleProbability G m p z (Fintype.card V : ℝ) x)
        ((tokenDummyHypergraph G m p z).edges.filter
          (fun e => a ∈ (tokenDummyHypergraph G m p z).edge e)) ≤
      (Fintype.card V : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  let τ := fractionalCost G x
  let A := ((m + 1 : ℕ) : ℝ) * τ - n
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmn : (m : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hnlarge
  have hnτ : n ≤ (m : ℝ) * τ :=
    card_le_m_mul_fractionalCost G m x hx hstable hload
  have hτA : τ ≤ A := by
    dsimp [A]
    push_cast
    nlinarith
  have hnA : n ≤ (m : ℝ) * A := by
    have hmul := mul_le_mul_of_nonneg_left hτA hm0
    nlinarith
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hzR : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hTreg : n - (m : ℝ) ≤ n * (τ / (p : ℝ)) ∧
      n * (τ / (p : ℝ)) ≤ n :=
    scaled_rounded_ratio_between n (m : ℝ) τ (p : ℝ)
      hm0 hmn hnτ hpR hTlower hTupper
  have hZreg : n - (m : ℝ) ≤ n * (A / (z : ℝ)) ∧
      n * (A / (z : ℝ)) ≤ n :=
    scaled_rounded_ratio_between n (m : ℝ) A (z : ℝ)
      hm0 hmn hnA hzR hZlower hZupper
  cases a with
  | inl v =>
      rw [tokenDummy_expected_original_degree_exact G m p z hp hz x hstable hload n v]
      exact ⟨by linarith, le_rfl⟩
  | inr q =>
      cases q with
      | inl c =>
          rw [tokenDummy_expected_token_degree G m p z hp hz x hstable n c]
          exact hTreg
      | inr d =>
          rw [tokenDummy_expected_dummy_degree G m p z hp hz x hstable hload n d]
          exact hZreg

end SampledMeanRegularity

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

/-- The probability of including a second dummy, conditional on a first,
is at most `(m-1)/(z-1)` when the edge uses at most `m` dummies.
@isnad1 id=le.1h3v.s7.e1c6a8cb57dd from=translated src=- shape=11c64a05 vocab=60687568
-/
theorem two_dummy_ratio_le_single_times (j m z : ℕ) (hj : j ≤ m) :
    ((j : ℝ) * ((j - 1 : ℕ) : ℝ)) /
        ((z : ℝ) * ((z - 1 : ℕ) : ℝ)) ≤
      ((j : ℝ) / (z : ℝ)) *
        (((m - 1 : ℕ) : ℝ) / ((z - 1 : ℕ) : ℝ)) := by
  have hpred : ((j - 1 : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right hj 1
  have hdiv : ((j - 1 : ℕ) : ℝ) / ((z - 1 : ℕ) : ℝ) ≤
      ((m - 1 : ℕ) : ℝ) / ((z - 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hpred (Nat.cast_nonneg _)
  have hjz : 0 ≤ (j : ℝ) / (z : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hdiv hjz
  simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- For `z ≥ m+1`, the conditional second-dummy ratio is no larger
than `m/z`.
@isnad1 id=le.2h2v.s6.acc59ddcd571 from=translated src=- shape=28c23f9b vocab=3bde4f44
-/
theorem pred_ratio_le_ratio (m z : ℕ) (hm : 1 ≤ m) (hz : m + 1 ≤ z) :
    (((m - 1 : ℕ) : ℝ) / ((z - 1 : ℕ) : ℝ)) ≤
      (m : ℝ) / (z : ℝ) := by
  have hz1 : 1 ≤ z := by omega
  have hzc : (m : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast (by omega : m ≤ z)
  have hmc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm]
    norm_num
  have hzc' : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
    rw [Nat.cast_sub hz1]
    norm_num
  rw [hmc, hzc']
  apply (div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < z - 1))
    (by exact_mod_cast (by omega : 0 < z))).2
  nlinarith

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section SharpTwoDummyBound

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dummy-dummy codegree is at most `m/z` once dummy weighted
degrees are at most one. This improves the coarse paper bound.
@isnad1 id=le.8h8v.s9.d3b010e2b6dc from=translated src=- shape=75bbce30 vocab=f5fdf42b
-/
theorem tokenDummy_weighted_two_dummy_codegree_le_m_div_z
    (G : SimpleGraph V) (m p z : ℕ)
    (hm : 1 ≤ m) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hZlower : ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ) ≤ (z : ℝ))
    (d d' : Fin z) (hne : d ≠ d') :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => Sum.inr (Sum.inr d) ∈ (tokenDummyHypergraph G m p z).edge e ∧
        Sum.inr (Sum.inr d') ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) ≤ (m : ℝ) / (z : ℝ) := by
  classical
  rw [tokenDummy_weighted_two_dummy_codegree G m p z hp hz x hstable d d' hne]
  let K : ℝ := ((m - 1 : ℕ) : ℝ) / ((z - 1 : ℕ) : ℝ)
  have hterm (S : StableSet G) :
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
          (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) ≤
        (x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ))) * K := by
    have hcard : 0 < S.1.card := S.2.1.card_pos
    have hj : m + 1 - S.1.card ≤ m := by omega
    calc
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
          (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ))) ≤
        x S * ((((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ)) * K) :=
          mul_le_mul_of_nonneg_left
            (two_dummy_ratio_le_single_times (m + 1 - S.1.card) m z hj) (hx S)
      _ = _ := by ring
  have hsum :
      (∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
          (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
          ((z : ℝ) * ((z - 1 : ℕ) : ℝ)))) ≤
        (∑ S : StableSet G,
          x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ))) * K := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro S hS
    exact hterm S
  have hzR : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hdiv :
      (((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ)) / (z : ℝ) ≤ 1 :=
    (div_le_one hzR).2 hZlower
  have hK0 : 0 ≤ K :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    (∑ S : StableSet G,
      x S * (((m + 1 - S.1.card : ℕ) : ℝ) *
        (((m + 1 - S.1.card : ℕ) - 1 : ℕ) : ℝ) /
        ((z : ℝ) * ((z - 1 : ℕ) : ℝ)))) ≤
      (∑ S : StableSet G,
        x S * (((m + 1 - S.1.card : ℕ) : ℝ) / (z : ℝ))) * K := hsum
    _ = ((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ)) / (z : ℝ)) * K := by
      rw [sum_dummy_mass_eq G m z x hstable hload]
    _ ≤ K := by nlinarith [mul_le_mul_of_nonneg_right hdiv hK0]
    _ ≤ (m : ℝ) / (z : ℝ) := pred_ratio_le_ratio m z hm hz

end SharpTwoDummyBound

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section SharpUniformCodegreeBudget

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All weighted pair codegrees are bounded by the largest of the
LP tolerance, reciprocal token count, and dummy ratio.
@isnad1 id=le.13h10v.s9.c18fb242f5e9 from=translated src=- shape=c07cdf17 vocab=0438a0c4
-/
theorem tokenDummy_weighted_codegree_le_sharp (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z) (hz2 : 2 ≤ z)
    (δ B : ℝ) (hδ : 0 ≤ δ)
    (x : StableSet G → ℝ)
    (hx : IsPairConstrainedColoring G δ x)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hOO : δ ≤ B)
    (hOT : (1 : ℝ) / (p : ℝ) ≤ B)
    (hOD : (m : ℝ) / (z : ℝ) ≤ B)
    (hm : 1 ≤ m)
    (hZlower : ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ) ≤ (z : ℝ))
    (a b : TokenDummyVertex V p z) (hab : a ≠ b) :
    (((tokenDummyHypergraph G m p z).edges.filter
      (fun e => a ∈ (tokenDummyHypergraph G m p z).edge e ∧
        b ∈ (tokenDummyHypergraph G m p z).edge e)).sum
      (tokenDummyWeight G m p z x)) ≤ B := by
  classical
  let H := tokenDummyHypergraph G m p z
  have hswap (a b : TokenDummyVertex V p z) :
      (H.edges.filter (fun e => a ∈ H.edge e ∧ b ∈ H.edge e)).sum
        (tokenDummyWeight G m p z x) =
      (H.edges.filter (fun e => b ∈ H.edge e ∧ a ∈ H.edge e)).sum
        (tokenDummyWeight G m p z x) := by
    congr 1
    ext e
    simp [and_comm]
  have hB : 0 ≤ B := hδ.trans hOO
  have hTD : (((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ)) / (z : ℝ)) / (p : ℝ)) ≤ B := by
    have hzR : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
    have hpR : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
    exact (div_le_div_of_nonneg_right
      ((div_le_one hzR).2 hZlower) hpR).trans hOT
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      have huv : u ≠ v := by
        intro heq
        apply hab
        simp [heq]
      calc
        _ = ∑ S : StableSet G,
          if u ∈ S.1 ∧ v ∈ S.1 then x S else 0 :=
          tokenDummy_weighted_original_codegree G m p z hp hz x hstable u v
        _ ≤ δ := pair_mass_le_of_isPairConstrained G δ hδ x hx u v huv
        _ ≤ B := hOO
    | inr q =>
      cases q with
      | inl c =>
        calc
          _ = vertexLoad G x u / (p : ℝ) :=
            tokenDummy_weighted_original_token_codegree G m p z hp hz x hstable u c
          _ = (1 : ℝ) / (p : ℝ) := by rw [hload u]
          _ ≤ B := hOT
      | inr d =>
        calc
          _ ≤ vertexLoad G x u * ((m : ℝ) / (z : ℝ)) :=
            tokenDummy_weighted_original_dummy_codegree_le
              G m p z hp hz x hx.1.1 hstable u d
          _ = (m : ℝ) / (z : ℝ) := by rw [hload u, one_mul]
          _ ≤ B := hOD
  | inr q =>
    cases q with
    | inl c =>
      cases b with
      | inl u =>
        calc
          _ = (H.edges.filter (fun e => Sum.inl u ∈ H.edge e ∧
              Sum.inr (Sum.inl c) ∈ H.edge e)).sum
              (tokenDummyWeight G m p z x) := hswap _ _
          _ = vertexLoad G x u / (p : ℝ) :=
            tokenDummy_weighted_original_token_codegree G m p z hp hz x hstable u c
          _ = (1 : ℝ) / (p : ℝ) := by rw [hload u]
          _ ≤ B := hOT
      | inr q' =>
        cases q' with
        | inl c' =>
          have hcc : c ≠ c' := by
            intro heq
            apply hab
            simp [heq]
          calc
            _ = 0 := tokenDummy_weighted_two_token_codegree G m p z x c c' hcc
            _ ≤ B := hB
        | inr d =>
          calc
            _ = (((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
              (Fintype.card V : ℝ)) / (z : ℝ)) / (p : ℝ)) :=
              tokenDummy_weighted_token_dummy_codegree_exact
                G m p z hp hz x hstable hload c d
            _ ≤ B := hTD
    | inr d =>
      cases b with
      | inl u =>
        calc
          _ = (H.edges.filter (fun e => Sum.inl u ∈ H.edge e ∧
              Sum.inr (Sum.inr d) ∈ H.edge e)).sum
              (tokenDummyWeight G m p z x) := hswap _ _
          _ ≤ vertexLoad G x u * ((m : ℝ) / (z : ℝ)) :=
            tokenDummy_weighted_original_dummy_codegree_le
              G m p z hp hz x hx.1.1 hstable u d
          _ = (m : ℝ) / (z : ℝ) := by rw [hload u, one_mul]
          _ ≤ B := hOD
      | inr q' =>
        cases q' with
        | inl c =>
          calc
            _ = (H.edges.filter (fun e => Sum.inr (Sum.inl c) ∈ H.edge e ∧
                Sum.inr (Sum.inr d) ∈ H.edge e)).sum
                (tokenDummyWeight G m p z x) := hswap _ _
            _ = (((((m + 1 : ℕ) : ℝ) * fractionalCost G x -
              (Fintype.card V : ℝ)) / (z : ℝ)) / (p : ℝ)) :=
              tokenDummy_weighted_token_dummy_codegree_exact
                G m p z hp hz x hstable hload c d
            _ ≤ B := hTD
        | inr d' =>
          have hdd : d ≠ d' := by
            intro heq
            apply hab
            simp [heq]
          exact (tokenDummy_weighted_two_dummy_codegree_le_m_div_z
            G m p z hm hp hz x hx.1.1 hstable hload hZlower d d' hdd).trans hOD

end SharpUniformCodegreeBudget

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section SharpSampledCodegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Multiplying the sharp weighted codegree bound by the sampling scale
bounds every expected sampled codegree.
@isnad1 id=le.14h11v.s9.5c1d8d3ee8e3 from=translated src=- shape=b148d3e3 vocab=6a7247cb
-/
theorem tokenDummy_expected_codegree_le_sharp (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z) (hz2 : 2 ≤ z)
    (δ B n : ℝ) (hδ : 0 ≤ δ) (hn : 0 ≤ n)
    (x : StableSet G → ℝ)
    (hx : IsPairConstrainedColoring G δ x)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hOO : δ ≤ B)
    (hOT : (1 : ℝ) / (p : ℝ) ≤ B)
    (hOD : (m : ℝ) / (z : ℝ) ≤ B)
    (hm : 1 ≤ m)
    (hZlower : ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ) ≤ (z : ℝ))
    (a b : TokenDummyVertex V p z) (hab : a ≠ b) :
    FiniteBernoulli.mean (tokenDummySampleProbability G m p z n x)
      ((tokenDummyHypergraph G m p z).edges.filter
        (fun e => a ∈ (tokenDummyHypergraph G m p z).edge e ∧
          b ∈ (tokenDummyHypergraph G m p z).edge e)) ≤ n * B := by
  classical
  unfold FiniteBernoulli.mean tokenDummySampleProbability
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (tokenDummy_weighted_codegree_le_sharp G m p z hp hz hz2
      δ B hδ x hx hstable hload hOO hOT hOD hm hZlower a b hab) hn

end SharpSampledCodegree

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

/-- If `a` is at least `n/m`, the sample-size scale makes `m/a`
small enough for the codegree budget.
@isnad1 id=le.5h4v.s7.c5b46a390ccc from=translated src=- shape=01b95b99 vocab=d8b90f1e
-/
theorem ratio_le_quarter_of_size (m a n μ : ℝ)
    (hm : 1 ≤ m) (ha : 0 < a) (hμ : 0 ≤ μ)
    (hsize : n ≤ m * a) (hscale : 4 * m ^ 2 ≤ μ * n) :
    m / a ≤ μ / 4 := by
  have hmpos : 0 < m := by linarith
  have hscaled : μ * n ≤ μ * (m * a) :=
    mul_le_mul_of_nonneg_left hsize hμ
  have hcancel : 4 * m ≤ μ * a := by
    apply (mul_le_mul_iff_of_pos_left hmpos).mp
    calc
      m * (4 * m) = 4 * m ^ 2 := by ring
      _ ≤ μ * n := hscale
      _ ≤ μ * (m * a) := hscaled
      _ = m * (μ * a) := by ring
  apply (div_le_iff₀ ha).2
  nlinarith

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section TokenDummyRatioBudget

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper-scale order assumption controls both non-original
weighted pair-codegree ratios.
@isnad1 id=and.10h7v.s8.eab6a972f075 from=translated src=- shape=153e53e5 vocab=8072d296
-/
theorem tokenDummy_scalar_codegree_budget (G : SimpleGraph V)
    (m p z : ℕ) (hm : 1 ≤ m) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hTlower : fractionalCost G x ≤ (p : ℝ))
    (hZlower : ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ) ≤ (z : ℝ))
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hscale : 4 * (m : ℝ) ^ 2 ≤ μ * (Fintype.card V : ℝ)) :
    (1 : ℝ) / (p : ℝ) ≤ μ / 4 ∧
      (m : ℝ) / (z : ℝ) ≤ μ / 4 := by
  let n : ℝ := Fintype.card V
  let τ := fractionalCost G x
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hzR : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hmn : n ≤ (m : ℝ) * τ :=
    card_le_m_mul_fractionalCost G m x hx hstable hload
  have hTA : τ ≤ (((m + 1 : ℕ) : ℝ) * τ - n) := by
    dsimp [n] at hmn
    push_cast
    nlinarith
  have hmp : n ≤ (m : ℝ) * (p : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hTlower hm0
    dsimp [τ] at hmn
    nlinarith
  have hmz : n ≤ (m : ℝ) * (z : ℝ) := by
    have hAz : τ ≤ (z : ℝ) := hTA.trans hZlower
    have hmul := mul_le_mul_of_nonneg_left hAz hm0
    nlinarith
  have hpbound : (m : ℝ) / (p : ℝ) ≤ μ / 4 :=
    ratio_le_quarter_of_size _ _ _ _ hmR hpR hμ hmp hscale
  have hzbound : (m : ℝ) / (z : ℝ) ≤ μ / 4 :=
    ratio_le_quarter_of_size _ _ _ _ hmR hzR hμ hmz hscale
  constructor
  · exact (div_le_div_of_nonneg_right hmR hpR.le).trans hpbound
  · exact hzbound

end TokenDummyRatioBudget

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section ConcreteSampledCodegree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every distinct sampled vertex pair has expected codegree at most
`μ n/4` under the LP pair constraint and the paper-scale order bound.
@isnad1 id=le.11h9v.s9.38f187d30fc5 from=translated src=- shape=c51efbed vocab=963e49d5
-/
theorem tokenDummy_expected_codegree_le_quarter (G : SimpleGraph V)
    (m p z : ℕ) (hm : 1 ≤ m) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hTlower : fractionalCost G x ≤ (p : ℝ))
    (hZlower : ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
      (Fintype.card V : ℝ) ≤ (z : ℝ))
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hx : IsPairConstrainedColoring G (μ / 4) x)
    (hscale : 4 * (m : ℝ) ^ 2 ≤ μ * (Fintype.card V : ℝ))
    (a b : TokenDummyVertex V p z) (hab : a ≠ b) :
    FiniteBernoulli.mean
      (tokenDummySampleProbability G m p z (Fintype.card V : ℝ) x)
      ((tokenDummyHypergraph G m p z).edges.filter
        (fun e => a ∈ (tokenDummyHypergraph G m p z).edge e ∧
          b ∈ (tokenDummyHypergraph G m p z).edge e)) ≤
      μ * (Fintype.card V : ℝ) / 4 := by
  have hratios := tokenDummy_scalar_codegree_budget G m p z hm hp hz
    x hx.1.1 hstable hload hTlower hZlower μ hμ hscale
  have hz2 : 2 ≤ z := by omega
  calc
    _ ≤ (Fintype.card V : ℝ) * (μ / 4) :=
      tokenDummy_expected_codegree_le_sharp G m p z hp hz hz2
        (μ / 4) (μ / 4) (Fintype.card V : ℝ)
        (by linarith) (Nat.cast_nonneg _) x hx hstable hload
        le_rfl hratios.1 hratios.2 hm hZlower a b hab
    _ = μ * (Fintype.card V : ℝ) / 4 := by ring

end ConcreteSampledCodegree

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

/-- The large order hypothesis used for the union bound also covers
the elementary degree and codegree scales needed in rounding.
@isnad1 id=and.4h3v.s7.a87b0a09a020 from=translated src=- shape=55365e8b vocab=5092686c
-/
theorem paper_scale_implies_rounding_scales (m : ℕ) (n μ : ℝ)
    (hm : 1 ≤ m) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hscale : 1000000 * (((m + 2 : ℕ) : ℝ) ^ 4) ≤ μ ^ 4 * n) :
    4 * (m : ℝ) ^ 2 ≤ μ * n ∧
      8 * (m : ℝ) ≤ μ * n ∧
      1 ≤ n ∧ (m : ℝ) ≤ n := by
  let r : ℝ := (m + 2 : ℕ)
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hrR : (m : ℝ) ≤ r := by
    dsimp [r]
    push_cast
    linarith
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hr2m : (m : ℝ) ^ 2 ≤ r ^ 2 := by gcongr
  have hr4 : r ^ 2 ≤ r ^ 4 := by
    calc
      r ^ 2 = r ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hr2 (sq_nonneg r)
      _ = r ^ 4 := by ring
  have hr4pos : 0 < r ^ 4 := by nlinarith [hr2]
  have hμ2 : μ ^ 2 ≤ μ := by
    nlinarith [mul_nonneg hμ.le (sub_nonneg.mpr hμ1)]
  have hμ2one : μ ^ 2 ≤ 1 := hμ2.trans hμ1
  have hμ4 : μ ^ 4 ≤ μ ^ 2 := by
    calc
      μ ^ 4 = μ ^ 2 * μ ^ 2 := by ring
      _ ≤ μ ^ 2 * 1 := mul_le_mul_of_nonneg_left hμ2one (sq_nonneg μ)
      _ = μ ^ 2 := by ring
  have hμ4le : μ ^ 4 ≤ μ := hμ4.trans hμ2
  have hμ4pos : 0 < μ ^ 4 := pow_pos hμ _
  have hnpos : 0 < n := by
    by_contra! hn
    have hnonpos : μ ^ 4 * n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hμ4pos.le hn
    nlinarith [hscale]
  have hμn : μ ^ 4 * n ≤ μ * n :=
    mul_le_mul_of_nonneg_right hμ4le hnpos.le
  have hmain : 1000000 * r ^ 4 ≤ μ * n := hscale.trans hμn
  have hquad : 4 * (m : ℝ) ^ 2 ≤ 1000000 * r ^ 4 := by
    nlinarith [hr2m, hr4, sq_nonneg r]
  have hlin : 8 * (m : ℝ) ≤ 1000000 * r ^ 4 := by
    have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ (m : ℝ))
        (sub_nonneg.mpr hmR)]
    nlinarith [hm2, hr2m, hr4, sq_nonneg r]
  have hμnle : μ * n ≤ n :=
    (mul_le_mul_of_nonneg_right hμ1 hnpos.le).trans_eq (one_mul n)
  refine ⟨hquad.trans hmain, hlin.trans hmain, ?_, ?_⟩
  · nlinarith [hlin.trans hmain]
  · nlinarith [hlin.trans hmain]

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section TokenDummyVertexBudget

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rounded token and dummy counts keep the enlarged vertex set below
`(m+2)n+2`, the finite union-bound budget.
@isnad1 id=le.4h6v.s7.b300213f75d1 from=translated src=- shape=4f68f5e5 vocab=ca9bc2cf
-/
theorem tokenDummy_vertex_count_le (G : SimpleGraph V)
    (m p z : ℕ) (x : StableSet G → ℝ)
    (hx : ∀ S, 0 ≤ x S)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hTupper : (p : ℝ) ≤ fractionalCost G x + 1)
    (hZupper : (z : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ) + 1) :
    ((tokenDummyHypergraph G m p z).vertices.card : ℝ) ≤
      ((m + 2 : ℕ) : ℝ) * (Fintype.card V : ℝ) + 2 := by
  have hτn := fractionalCost_le_card_of_exact_load G x hx hload
  have hmul := mul_le_mul_of_nonneg_left hτn
    (Nat.cast_nonneg (m + 2) : 0 ≤ ((m + 2 : ℕ) : ℝ))
  rw [tokenDummy_vertices_card]
  push_cast at hZupper hmul ⊢
  nlinarith

end TokenDummyVertexBudget

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section ConcreteSampleValidity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ideal token count and the dummy count force the normalization
`n/(p·z)` below one for every active edge copy.
@isnad1 id=and.6h7v.s7.f395696d06ed from=translated src=- shape=ed431dc2 vocab=01a6bb75
-/
theorem tokenDummySampleProbability_bounds_of_exact_load (G : SimpleGraph V)
    (m p z : ℕ) (hp : 0 < p) (hz : m + 1 ≤ z)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (hTlower : fractionalCost G x ≤ (p : ℝ)) :
    ∀ e : TokenDummyLabel G p z,
      0 ≤ tokenDummySampleProbability G m p z (Fintype.card V : ℝ) x e ∧
        tokenDummySampleProbability G m p z (Fintype.card V : ℝ) x e ≤ 1 := by
  have hmn := card_le_m_mul_fractionalCost G m x hx hstable hload
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmp := mul_le_mul_of_nonneg_left hTlower hm0
  have hmz : (m : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast (by omega : m ≤ z)
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
  have hzp := mul_le_mul_of_nonneg_right hmz hp0
  have hnpz : (Fintype.card V : ℝ) ≤ (p : ℝ) * (z : ℝ) := by
    nlinarith [hmn, hmp, hzp]
  intro e
  exact tokenDummySampleProbability_bounds G m p z hp hz
    (Fintype.card V : ℝ) (Nat.cast_nonneg _) hnpz
    x hx hstable hload e

end ConcreteSampleValidity

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section ConcreteGoodSample

variable {V : Type*} [Fintype V] [DecidableEq V]

end ConcreteGoodSample

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

/-- A pointwise real upper bound also bounds a finite maximum of
natural values.
@isnad1 id=le.2h4v.s6.1ed0de25fba4 from=translated src=- shape=8f26953e vocab=a284554d
-/
theorem natCast_finset_sup_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (B : ℝ)
    (hB : 0 ≤ B) (h : ∀ i ∈ s, (f i : ℝ) ≤ B) :
    ((s.sup f : ℕ) : ℝ) ≤ B := by
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert i s hi ih =>
      have hI : (f i : ℝ) ≤ B := h i (Finset.mem_insert_self ..)
      have hS : ∀ j ∈ s, (f j : ℝ) ≤ B := by
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sup_insert] using
        (max_le hI (ih hS))
end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section SampledMatchingInput

variable {W E : Type*} [DecidableEq W] [DecidableEq E] [Fintype E]

omit [DecidableEq E] [Fintype E] in
/-- The sampled degree and codegree estimates imply the nearly-regular
conditions used by the matching theorem, with the actual maximum degree.
@isnad1 id=and.7h7v.s8.bee53ceed2dc from=translated src=- shape=5327d79f vocab=f6240f45
-/
theorem sampled_paper_bounds_imply_matching_hypotheses
    (H : IndexedHypergraph W E) (ω : E → Bool) (n m μ : ℝ)
    (hn : 0 < n) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hverts : H.vertices.Nonempty)
    (hsmall : 8 * m ≤ μ * n)
    (hdegree : ∀ v ∈ H.vertices,
      n - m - μ * n / 8 < ((sampledHypergraph H ω).degree v : ℝ) ∧
        ((sampledHypergraph H ω).degree v : ℝ) < n + μ * n / 8)
    (hcodegree : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices,
      u ≠ v →
        ((sampledHypergraph H ω).codegree u v : ℝ) < μ * n / 2) :
    0 < ((sampledHypergraph H ω).maxDegree : ℝ) ∧
      (∀ v ∈ (sampledHypergraph H ω).vertices,
        (1 - μ) * ((sampledHypergraph H ω).maxDegree : ℝ) ≤
          ((sampledHypergraph H ω).degree v : ℝ)) ∧
      ((sampledHypergraph H ω).maxCodegree : ℝ) ≤
        μ * ((sampledHypergraph H ω).maxDegree : ℝ) := by
  classical
  let K := sampledHypergraph H ω
  let D : ℝ := (1 + μ / 8) * n
  have hDge : n ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg hμ.le hn.le]
  have hDpos : 0 < D := lt_of_lt_of_le hn hDge
  have hmin (v : W) (hv : v ∈ H.vertices) :
      (1 - μ / 4) * n ≤ (K.degree v : ℝ) := by
    have hl := (hdegree v hv).1
    change n - m - μ * n / 8 < (K.degree v : ℝ) at hl
    nlinarith [hsmall]
  have hupper (v : W) (hv : v ∈ H.vertices) :
      (K.degree v : ℝ) ≤ D := by
    have hu := (hdegree v hv).2
    change (K.degree v : ℝ) < n + μ * n / 8 at hu
    dsimp [D]
    nlinarith
  have hmax : (K.maxDegree : ℝ) ≤ D := by
    change (((H.vertices.sup K.degree : ℕ) : ℝ) ≤ D)
    exact natCast_finset_sup_le H.vertices K.degree D hDpos.le hupper
  obtain ⟨v₀, hv₀⟩ := hverts
  have hmaxlower : (1 - μ / 4) * n ≤ (K.maxDegree : ℝ) := by
    have hle : K.degree v₀ ≤ K.maxDegree := K.degree_le_maxDegree hv₀
    exact (hmin v₀ hv₀).trans (by exact_mod_cast hle)
  have hmaxpos : 0 < (K.maxDegree : ℝ) := by
    have hcoef : 0 < 1 - μ / 4 := by linarith
    exact lt_of_lt_of_le (mul_pos hcoef hn) hmaxlower
  have hcompare : (1 - μ) * D ≤ (1 - μ / 4) * n := by
    have hμn : 0 ≤ μ * n := mul_nonneg hμ.le hn.le
    have hμ2n : 0 ≤ μ ^ 2 * n := mul_nonneg (sq_nonneg μ) hn.le
    dsimp [D]
    nlinarith
  have hdegreeRelative (v : W) (hv : v ∈ K.vertices) :
      (1 - μ) * (K.maxDegree : ℝ) ≤ (K.degree v : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hmax (sub_nonneg.mpr hμ1)
    exact (hscaled.trans hcompare).trans (hmin v hv)
  have hhalf : μ * n / 2 ≤ μ * ((1 - μ / 4) * n) := by
    have hcoef : (1 : ℝ) / 2 ≤ 1 - μ / 4 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcoef
      (mul_nonneg hμ.le hn.le)
    nlinarith
  have hhalfmax : μ * n / 2 ≤ μ * (K.maxDegree : ℝ) :=
    hhalf.trans (mul_le_mul_of_nonneg_left hmaxlower hμ.le)
  have hcodeRelative (u v : W) (hu : u ∈ K.vertices)
      (hv : v ∈ K.vertices) (hne : u ≠ v) :
      (K.codegree u v : ℝ) ≤ μ * (K.maxDegree : ℝ) :=
    (hcodegree u hu v hv hne).le.trans hhalfmax
  have hB0 : 0 ≤ μ * (K.maxDegree : ℝ) :=
    mul_nonneg hμ.le (Nat.cast_nonneg _)
  have hmaxCodegree : (K.maxCodegree : ℝ) ≤ μ * (K.maxDegree : ℝ) := by
    change (((K.vertices.sup (fun u =>
      (K.vertices.erase u).sup (K.codegree u)) : ℕ) : ℝ) ≤ _)
    apply natCast_finset_sup_le K.vertices
      (fun u => (K.vertices.erase u).sup (K.codegree u))
      (μ * (K.maxDegree : ℝ)) hB0
    intro u hu
    apply natCast_finset_sup_le (K.vertices.erase u) (K.codegree u)
      (μ * (K.maxDegree : ℝ)) hB0
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    exact hcodeRelative u v hu hv'.2 hv'.1.symm
  exact ⟨hmaxpos, hdegreeRelative, hmaxCodegree⟩

end SampledMatchingInput

end HadwigerLean.LowCodegreeRounding
