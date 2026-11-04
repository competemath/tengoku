import Tengoku.DeletionCodesLean.DeletionCode.SupportComponents
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Data.Fintype.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms gram_injective_of_simple` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms no_common_bubble_gram` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bubble_support_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rule_value_at_gram` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rule_support_eq_edge_union` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms signed_generating_implies_generating` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms signed_support_edge_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms supported_iff_signed_incident` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms signed_supported_graph_setoid_eq` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Finite word spectra and the signed-support interface for generating families.

The spectrum counts actual finite L-window occurrences. A bubble contributes
positive-path counts minus negative-path counts. Vertex simplicity gives at
most one occurrence of each gram on either path. The endpoint-intersection
condition and unequal path lengths rule out a gram shared by both paths.
Vertex disjointness between bubbles of one rule then prevents cancellation.

The geometric assumptions below are structural catalogue conditions: simple
paths, common vertices only at the two aligned endpoints, unequal path lengths,
and no shared vertex between distinct bubbles of a rule. The manuscript's
catalogue requires the first, second, and fourth conditions; its two local word
lengths differ by one, giving the third. This module does not construct the
catalogue from A d^rho B, formalize linear independence, or prove the final count.
-/

namespace DeletionCode.SignedSupport

open Windows RootSelection
open scoped BigOperators

abbrev Gram (L : ℕ) := Fin L → Bool

def gram (p : Letters) (L i : ℕ) : Gram L := fun q => p (i + q.val)

/-- All L-windows of the finite word of length L+D.-/
def windowSet (p : Letters) (L D : ℕ) : Set (Gram L) :=
  Set.range (fun i : Fin (D + 1) => gram p L i.val)

/-- The integral count of a gram among all valid windows of a word of length L+D.-/
noncomputable def pathSpectrum (p : Letters) (L D : ℕ) (g : Gram L) : ℤ := by
  classical
  exact ∑ i : Fin (D + 1), if gram p L i.val = g then 1 else 0

/-- The base-word spectrum checks bounds explicitly, including when n < L.-/
noncomputable def wordSpectrum (x : Letters) (n L : ℕ) (g : Gram L) : ℤ := by
  classical
  exact ∑ i : Fin (n + 1), if i.val + L ≤ n ∧ gram x L i.val = g then 1 else 0

/--
@isnad1 id=iff.0h5v.s4.0962c9b34427 from=translated src=- shape=fca6dbc0 vocab=412faf75
-/
theorem gram_eq_iff_agree (p q : Letters) (L i j : ℕ) :
    gram p L i = gram q L j ↔ Agree p i q j L := by
  constructor
  · intro h r hr
    exact congrFun h ⟨r, hr⟩
  · intro h
    funext r
    exact h r.val r.isLt

/--
@isnad1 id=eq.1h9v.s5.0bdf8e872e26 from=translated src=- shape=30f0f265 vocab=9824defe
-/
theorem gram_eq_source_vertices {B : Type*} (F : Family B) (L : ℕ)
    (a b : B) (sa sb : Bool) (i j : ℕ)
    (h : gram (F.path a sa) L i = gram (F.path b sb) L j) :
    SupportComponents.vertex F L a sa i = SupportComponents.vertex F L b sb j := by
  funext q
  exact congrFun h ⟨q.val, by have := q.isLt; omega⟩

/--
@isnad1 id=eq.1h9v.s6.3f4b189189b5 from=translated src=- shape=df07d7be vocab=a11742fc
-/
theorem gram_eq_target_vertices {B : Type*} (F : Family B) (L : ℕ)
    (a b : B) (sa sb : Bool) (i j : ℕ)
    (h : gram (F.path a sa) L i = gram (F.path b sb) L j) :
    SupportComponents.vertex F L a sa (i + 1) =
      SupportComponents.vertex F L b sb (j + 1) := by
  funext q
  have he := congrFun h ⟨q.val + 1, by have := q.isLt; omega⟩
  simpa only [gram, SupportComponents.vertex, Nat.add_assoc, Nat.add_comm 1 q.val] using he

/-- Genuine path geometry, before any conclusion about spectra or cancellation.-/
structure BubbleGeometry {B : Type*} (F : Family B) (L : ℕ) : Prop where
  simple : ∀ b side, Function.Injective
    (fun i : Fin (F.extra b side + 2) => SupportComponents.vertex F L b side i.val)
  endpoints : ∀ b i j, i ≤ F.extra b false + 1 → j ≤ F.extra b true + 1 →
    SupportComponents.vertex F L b false i = SupportComponents.vertex F L b true j →
      (i = 0 ∧ j = 0) ∨ (i = F.extra b false + 1 ∧ j = F.extra b true + 1)
  differentLengths : ∀ b, F.extra b false ≠ F.extra b true

/--
@isnad1 id=injectiv.1h5v.s6.47ee066beb12 from=translated src=- shape=475f65ac vocab=e1445467
-/
theorem gram_injective_of_simple {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (side : Bool) :
    Function.Injective (fun i : Fin (F.extra b side + 1) => gram (F.path b side) L i.val) := by
  intro i j hij
  have he := gram_eq_source_vertices F L b b side side i.val j.val hij
  have hi := i.isLt
  have hj := j.isLt
  have hindices := H.simple b side
    (a₁ := ⟨i.val, by omega⟩) (a₂ := ⟨j.val, by omega⟩) he
  exact Fin.ext (congrArg (fun z : Fin (F.extra b side + 2) => z.val) hindices)

/-- A shared edge would force both paths to consist of the same single edge,
contradicting their unequal lengths.
@isnad1 id=false.3h5v.s6.4b1da0b6af06 from=translated src=- shape=a2dd727b vocab=6ac953bb
-/
theorem no_common_bubble_gram {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L)
    (hn : g ∈ windowSet (F.path b false) L (F.extra b false))
    (hp : g ∈ windowSet (F.path b true) L (F.extra b true)) : False := by
  obtain ⟨i, hi⟩ := hn
  obtain ⟨j, hj⟩ := hp
  have hiBound := i.isLt
  have hjBound := j.isLt
  have he : gram (F.path b false) L i.val = gram (F.path b true) L j.val :=
    hi.trans hj.symm
  have hs := H.endpoints b i.val j.val (by omega) (by omega)
    (gram_eq_source_vertices F L b b false true i.val j.val he)
  have hi0 : i.val = 0 := by
    rcases hs with ⟨hi0, hj0⟩ | ⟨hiEnd, hjEnd⟩
    · exact hi0
    · omega
  have hj0 : j.val = 0 := by
    rcases hs with ⟨hi0, hj0⟩ | ⟨hiEnd, hjEnd⟩
    · exact hj0
    · omega
  have ht := H.endpoints b (i.val + 1) (j.val + 1) (by omega) (by omega)
    (gram_eq_target_vertices F L b b false true i.val j.val he)
  rcases ht with ⟨hzero, _⟩ | ⟨hEndN, hEndP⟩
  · omega
  · exact H.differentLengths b (by omega)

/--
@isnad1 id=eq.2h4v.s6.14748e4febd3 from=translated src=- shape=b46ec9ff vocab=62bd4ed4
-/
theorem pathSpectrum_eq_one (p : Letters) (L D : ℕ) (g : Gram L)
    (hinj : Function.Injective (fun i : Fin (D + 1) => gram p L i.val))
    (hg : g ∈ windowSet p L D) : pathSpectrum p L D g = 1 := by
  classical
  obtain ⟨i, hi⟩ := hg
  rw [← hi]
  simp only [pathSpectrum, hinj.eq_iff]
  have hsingle := Finset.sum_eq_single (s := Finset.univ)
    (f := fun j : Fin (D + 1) => if j = i then (1 : ℤ) else 0) i
    (fun j _ hji => ite_eq_right hji)
    (fun hnot => False.elim (hnot (Finset.mem_univ i)))
  exact hsingle.trans (by simp)

/--
@isnad1 id=eq.1h4v.s5.8e909ab8b48e from=translated src=- shape=d647e299 vocab=922e90d4
-/
theorem pathSpectrum_eq_zero (p : Letters) (L D : ℕ) (g : Gram L)
    (hg : g ∉ windowSet p L D) : pathSpectrum p L D g = 0 := by
  classical
  unfold pathSpectrum
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (fun he => hg ⟨i, he⟩)

/-- The actual signed spectrum difference of a bubble.-/
noncomputable def bubbleSpectrum {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (g : Gram L) : ℤ :=
  pathSpectrum (F.path b true) L (F.extra b true) g -
    pathSpectrum (F.path b false) L (F.extra b false) g

def HasGram {B : Type*} (F : Family B) (L : ℕ) (b : B) (g : Gram L) : Prop :=
  ∃ side, g ∈ windowSet (F.path b side) L (F.extra b side)

/--
@isnad1 id=eq.2h5v.s5.9f0355442575 from=translated src=- shape=54e7dbc4 vocab=9675e4d1
-/
theorem bubble_negative_value {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L)
    (hn : g ∈ windowSet (F.path b false) L (F.extra b false)) :
    bubbleSpectrum F L b g = -1 := by
  have hp : g ∉ windowSet (F.path b true) L (F.extra b true) :=
    no_common_bubble_gram F L H b g hn
  rw [bubbleSpectrum, pathSpectrum_eq_zero _ _ _ _ hp,
    pathSpectrum_eq_one _ _ _ _ (gram_injective_of_simple F L H b false) hn]
  decide

/--
@isnad1 id=eq.2h5v.s5.67040829cd10 from=translated src=- shape=cf3f2077 vocab=9154be54
-/
theorem bubble_positive_value {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L)
    (hp : g ∈ windowSet (F.path b true) L (F.extra b true)) :
    bubbleSpectrum F L b g = 1 := by
  have hn : g ∉ windowSet (F.path b false) L (F.extra b false) :=
    fun hn => no_common_bubble_gram F L H b g hn hp
  rw [bubbleSpectrum,
    pathSpectrum_eq_one _ _ _ _ (gram_injective_of_simple F L H b true) hp,
    pathSpectrum_eq_zero _ _ _ _ hn]
  decide

/--
@isnad1 id=iff.1h5v.s5.0c39fdc27b39 from=translated src=- shape=af12b2f9 vocab=fe34e64a
-/
theorem bubble_support_iff {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L) :
    bubbleSpectrum F L b g ≠ 0 ↔ HasGram F L b g := by
  classical
  constructor
  · intro h
    by_contra hnone
    have hn : g ∉ windowSet (F.path b false) L (F.extra b false) :=
      fun hg => hnone ⟨false, hg⟩
    have hp : g ∉ windowSet (F.path b true) L (F.extra b true) :=
      fun hg => hnone ⟨true, hg⟩
    apply h
    rw [bubbleSpectrum, pathSpectrum_eq_zero _ _ _ _ hp,
      pathSpectrum_eq_zero _ _ _ _ hn]
    rfl
  · rintro ⟨side, hg⟩
    cases side with
    | false => rw [bubble_negative_value F L H b g hg]; decide
    | true => rw [bubble_positive_value F L H b g hg]; decide

/-- Different bubbles of this rule have no common vertex on either path.-/
def VertexDisjointOn {B : Type*} (F : Family B) (L : ℕ) (S : Finset B) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ sa sb i j,
    i ≤ F.extra a sa + 1 → j ≤ F.extra b sb + 1 →
    SupportComponents.vertex F L a sa i ≠ SupportComponents.vertex F L b sb j

/--
@isnad1 id=false.6h7v.s6.2c2bc7901c60 from=translated src=- shape=a3b5cac3 vocab=0d00d26a
-/
theorem no_common_rule_gram {B : Type*} (F : Family B) (L : ℕ) (S : Finset B)
    (hdis : VertexDisjointOn F L S) (a b : B) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (g : Gram L) (hga : HasGram F L a g) (hgb : HasGram F L b g) :
    False := by
  obtain ⟨sa, i, hi⟩ := hga
  obtain ⟨sb, j, hj⟩ := hgb
  have hiBound := i.isLt
  have hjBound := j.isLt
  exact hdis a ha b hb hab sa sb i.val j.val (by omega) (by omega)
    (gram_eq_source_vertices F L a b sa sb i.val j.val (hi.trans hj.symm))

noncomputable def ruleSpectrum {B : Type*} (F : Family B) (L : ℕ)
    (S : Finset B) (g : Gram L) : ℤ :=
  ∑ b ∈ S, bubbleSpectrum F L b g

/-- Every gram in a bubble retains that bubble's coefficient in the whole rule.
@isnad1 id=eq.4h6v.s5.adfcd1fee199 from=translated src=- shape=427a0780 vocab=f2994764
-/
theorem rule_value_at_gram {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (b : B) (hb : b ∈ S) (g : Gram L) (hg : HasGram F L b g) :
    ruleSpectrum F L S g = bubbleSpectrum F L b g := by
  classical
  unfold ruleSpectrum
  apply Finset.sum_eq_single b
  · intro a ha hab
    by_contra hnonzero
    exact no_common_rule_gram F L S hdis a b ha hb hab g
      ((bubble_support_iff F L H a g).mp hnonzero) hg
  · intro hnot
    exact False.elim (hnot hb)

/--
@isnad1 id=eq.4h6v.s6.a449d39633e6 from=translated src=- shape=79cf29d8 vocab=3feea908
-/
theorem rule_negative_of_window {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (b : B) (hb : b ∈ S) (g : Gram L)
    (hg : g ∈ windowSet (F.path b false) L (F.extra b false)) :
    ruleSpectrum F L S g = -1 := by
  rw [rule_value_at_gram F L H S hdis b hb g ⟨false, hg⟩]
  exact bubble_negative_value F L H b g hg

/--
@isnad1 id=iff.2h5v.s5.347aaeedf30f from=translated src=- shape=5ed112fd vocab=7bf6a7ec
-/
theorem rule_support_iff {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (g : Gram L) :
    ruleSpectrum F L S g ≠ 0 ↔ ∃ b ∈ S, HasGram F L b g := by
  classical
  constructor
  · intro h
    by_contra hnone
    apply h
    unfold ruleSpectrum
    apply Finset.sum_eq_zero
    intro b hb
    by_contra hnonzero
    exact hnone ⟨b, hb, (bubble_support_iff F L H b g).mp hnonzero⟩
  · rintro ⟨b, hb, hg⟩
    rw [rule_value_at_gram F L H S hdis b hb g hg]
    exact (bubble_support_iff F L H b g).mpr hg

/-- The signed support is exactly the union of actual windows, without cancellation.
@isnad1 id=eq.2h4v.s6.e2975539454d from=translated src=- shape=302db603 vocab=82273ad7
-/
theorem rule_support_eq_edge_union {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S) :
    {g | ruleSpectrum F L S g ≠ 0} = {g | ∃ b ∈ S, HasGram F L b g} := by
  ext g
  exact rule_support_iff F L H S hdis g

/--
@isnad1 id=ex.1h4v.s5.7d1d1a2c4b86 from=translated src=- shape=cf4da135 vocab=6023accb
-/
theorem wordSpectrum_nonzero_occurs (x : Letters) (n L : ℕ) (g : Gram L)
    (h : wordSpectrum x n L g ≠ 0) : ∃ a, a + L ≤ n ∧ gram x L a = g := by
  classical
  by_contra hnone
  apply h
  unfold wordSpectrum
  apply Finset.sum_eq_zero
  intro a ha
  exact ite_eq_right (fun hh => hnone ⟨a.val, hh⟩)

/-- Bubble occurrences of one rule are precisely the family members with its rank.-/
def ruleBubbles {B : Type*} [Fintype B] (F : Family B) (i : ℕ) : Finset B :=
  Finset.univ.filter (fun b => F.rank b = i)

/-- The signed-coordinate generating condition from the manuscript.
Linear independence is not needed for the provenance implication below.-/
def SignedGenerating {B : Type*} [Fintype B] (F : Family B)
    (x : Letters) (n L : ℕ) : Prop :=
  ∀ i g, ruleSpectrum F L (ruleBubbles F i) g = -1 →
    wordSpectrum x n L g ≠ 0 ∨
      ∃ j, j < i ∧ ruleSpectrum F L (ruleBubbles F j) g ≠ 0

/-- The concrete word-level generating premise is derived from signed spectra
and catalogue geometry, not assumed as another provenance hypothesis.
@isnad1 id=generati.3h5v.s5.116cdf3b44b3 from=translated src=- shape=a49a96f1 vocab=a2e114d5
-/
theorem signed_generating_implies_generating {B : Type*} [Fintype B]
    (F : Family B) (x : Letters) (n L : ℕ)
    (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (hgen : SignedGenerating F x n L) : F.Generating x n L := by
  intro b i hi
  let g : Gram L := gram (F.path b false) L i
  have hb : b ∈ ruleBubbles F (F.rank b) := by simp [ruleBubbles]
  have hneg : g ∈ windowSet (F.path b false) L (F.extra b false) :=
    ⟨⟨i, by omega⟩, rfl⟩
  have hvalue := rule_negative_of_window F L H (ruleBubbles F (F.rank b))
    (hdis (F.rank b)) b hb g hneg
  rcases hgen (F.rank b) g hvalue with hbase | ⟨j, hj, hsupplier⟩
  · obtain ⟨a, ha, hagree⟩ := wordSpectrum_nonzero_occurs x n L g hbase
    exact Or.inl ⟨a, ha, (gram_eq_iff_agree x (F.path b false) L a i).mp hagree⟩
  · obtain ⟨a, ha, side, offset, hgram⟩ :=
      (rule_support_iff F L H (ruleBubbles F j) (hdis j) g).mp hsupplier
    have hrank : F.rank a = j := (Finset.mem_filter.mp ha).2
    have hoffset := offset.isLt
    refine Or.inr ⟨a, side, offset.val, by omega, by omega, ?_⟩
    exact (gram_eq_iff_agree (F.path b false) (F.path a side) L i offset.val).mp
      hgram.symm

/-- Prefix and gramSuffix vertices of an actual finite gram. The definitions are
total even at L=0, where the vertex index type is empty.-/
def gramPrefix {L : ℕ} (g : Gram L) : SupportComponents.Vertex L :=
  fun q => g ⟨q.val, by have := q.isLt; omega⟩

def gramSuffix {L : ℕ} (g : Gram L) : SupportComponents.Vertex L :=
  fun q => g ⟨q.val + 1, by have := q.isLt; omega⟩

/--
@isnad1 id=eq.0h6v.s5.430e3c66cc74 from=translated src=- shape=038941cc vocab=8f688216
-/
theorem prefix_gram {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (side : Bool) (i : ℕ) :
    gramPrefix (gram (F.path b side) L i) = SupportComponents.vertex F L b side i := rfl

/--
@isnad1 id=eq.0h6v.s5.08ebd116f333 from=translated src=- shape=a637bd24 vocab=5759ed98
-/
theorem suffix_gram {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (side : Bool) (i : ℕ) :
    gramSuffix (gram (F.path b side) L i) = SupportComponents.vertex F L b side (i + 1) := by
  funext q
  change F.path b side (i + (q.val + 1)) = F.path b side ((i + 1) + q.val)
  congr 1
  omega

/-- Edges present in at least one rule's signed support, without summing rules
against one another. This is the manuscript's unsigned support union S(G).-/
def signedSupportEdge {B : Type*} [Fintype B] (F : Family B) (L : ℕ)
    (u v : SupportComponents.Vertex L) : Prop :=
  ∃ (i : ℕ) (g : Gram L), ruleSpectrum F L (ruleBubbles F i) g ≠ 0 ∧
    u = gramPrefix g ∧ v = gramSuffix g

/-- The actual signed-support graph has precisely the consecutive-window edges
used by SupportComponents. No cancellation is assumed in this identification.
@isnad1 id=iff.2h5v.s5.ac7d7d1f03e5 from=translated src=- shape=ba1fea88 vocab=d263c476
-/
theorem signed_support_edge_iff {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (u v : SupportComponents.Vertex L) :
    signedSupportEdge F L u v ↔ SupportComponents.Edge F L u v := by
  constructor
  · rintro ⟨rank, g, hg, hu, hv⟩
    obtain ⟨b, hb, side, i, hi⟩ :=
      (rule_support_iff F L H (ruleBubbles F rank) (hdis rank) g).mp hg
    have hbound := i.isLt
    refine ⟨b, side, i.val, by omega, ?_, ?_⟩
    · rw [← hi] at hu
      simpa only [prefix_gram] using hu
    · rw [← hi] at hv
      simpa only [suffix_gram] using hv
  · rintro ⟨b, side, i, hi, hu, hv⟩
    let g := gram (F.path b side) L i
    have hb : b ∈ ruleBubbles F (F.rank b) := by simp [ruleBubbles]
    have hg : HasGram F L b g := ⟨side, ⟨i, by omega⟩, rfl⟩
    refine ⟨F.rank b, g,
      (rule_support_iff F L H (ruleBubbles F (F.rank b)) (hdis (F.rank b)) g).mpr
        ⟨b, hb, hg⟩, ?_, ?_⟩
    · exact hu.trans (prefix_gram F L b side i).symm
    · exact hv.trans (suffix_gram F L b side i).symm

/-- The path vertex union is exactly the incident-vertex set of the signed
support union. In particular the restriction excludes every ambient outsider.
@isnad1 id=iff.2h4v.s5.92c2563d6e28 from=translated src=- shape=9c93e77d vocab=89780688
-/
theorem supported_iff_signed_incident {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (v : SupportComponents.Vertex L) :
    (∃ b, SupportComponents.HasVertex F L b v) ↔
      ∃ w, signedSupportEdge F L v w ∨ signedSupportEdge F L w v := by
  constructor
  · rintro ⟨b, side, i, hi, hv⟩
    by_cases hbefore : i ≤ F.extra b side
    · refine ⟨SupportComponents.vertex F L b side (i + 1), Or.inl ?_⟩
      apply (signed_support_edge_iff F L H hdis _ _).mpr
      exact ⟨b, side, i, hbefore, hv, rfl⟩
    · have hlast : i = F.extra b side + 1 := by omega
      refine ⟨SupportComponents.vertex F L b side (F.extra b side), Or.inr ?_⟩
      apply (signed_support_edge_iff F L H hdis _ _).mpr
      refine ⟨b, side, F.extra b side, le_rfl, rfl, ?_⟩
      simpa only [hlast] using hv
  · rintro ⟨w, h | h⟩
    · obtain ⟨b, hv, _⟩ := SupportComponents.edge_owners F L
        ((signed_support_edge_iff F L H hdis _ _).mp h)
      exact ⟨b, hv⟩
    · obtain ⟨b, _, hv⟩ := SupportComponents.edge_owners F L
        ((signed_support_edge_iff F L H hdis _ _).mp h)
      exact ⟨b, hv⟩

def SignedGraphConnected {B : Type*} [Fintype B] (F : Family B) (L : ℕ) :
    SupportComponents.Vertex L → SupportComponents.Vertex L → Prop :=
  Relation.EqvGen (signedSupportEdge F L)

/--
@isnad1 id=iff.2h5v.s5.93ab74e2a3d3 from=translated src=- shape=ba1fea88 vocab=aeb8b77d
-/
theorem signed_graph_connected_iff {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (u v : SupportComponents.Vertex L) :
    SignedGraphConnected F L u v ↔ SupportComponents.GraphConnected F L u v := by
  have heq : signedSupportEdge F L = SupportComponents.Edge F L := by
    funext a b
    exact propext (signed_support_edge_iff F L H hdis a b)
  unfold SignedGraphConnected SupportComponents.GraphConnected
  rw [heq]

def signedSupportedGraphSetoid {B : Type*} [Fintype B] (F : Family B) (L : ℕ) :
    Setoid (SupportComponents.SupportedVertex F L) where
  r := fun u v => SignedGraphConnected F L u.val v.val
  iseqv := ⟨fun v => Relation.EqvGen.refl v.val,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

/-- Hence the existing supported-graph component quotient counts exactly the
components of the signed support union, with the same incident vertex set.
@isnad1 id=eq.2h3v.s5.0e393674f821 from=translated src=- shape=2a4eb082 vocab=13f53a59
-/
theorem signed_supported_graph_setoid_eq {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i)) :
    signedSupportedGraphSetoid F L = SupportComponents.supportedGraphSetoid F L := by
  apply Setoid.ext
  intro u v
  exact signed_graph_connected_iff F L H hdis u.val v.val

end DeletionCode.SignedSupport
