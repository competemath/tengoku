import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace GN

noncomputable section

/-- A partition of an integer set into nonempty blocks of size at most three,
with every block sum a nonnegative integral power of three.-/
def GoodOn (s : Finset ℤ) (blocks : Finset (Finset ℤ)) : Prop :=
  blocks.biUnion id = s ∧
  (∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c) ∧
  ∀ b ∈ blocks, b.Nonempty ∧ b.card ≤ 3 ∧ ∃ k : ℕ, b.sum id = (3 : ℤ)^k

/-- Existence of a good partition of a specified finite integer set.-/
def HasGood (s : Finset ℤ) : Prop := ∃ blocks, GoodOn s blocks

/-- The positive integer interval {1,...,n}; n=0 gives the empty set.-/
def interval (n : ℕ) : Finset ℤ := Finset.Icc 1 (n : ℤ)

/-- The three conditions on a single good block.-/
def GoodBlock (b : Finset ℤ) : Prop :=
  b.Nonempty ∧ b.card ≤ 3 ∧ ∃ k : ℕ, b.sum id = (3 : ℤ)^k

/--
@isnad1 id=eq.0h0v.s3.7104bab333a7 from=translated src=- shape=54ac7564 vocab=5a5614ee
-/
@[simp] theorem interval_zero : interval 0 = ∅ := by simp [interval]

 /--
 @isnad1 id=goodbloc.2h3v.s5.26b2e5b03fd4 from=translated src=- shape=599ad8f2 vocab=92ae0f8e
 -/
 theorem GoodOn.block {s : Finset ℤ} {blocks : Finset (Finset ℤ)}
    (h : GoodOn s blocks) {b : Finset ℤ} (hb : b ∈ blocks) : GoodBlock b := h.2.2 b hb

 /--
 @isnad1 id=le.2h3v.s5.ef9ab625db0f from=translated src=- shape=8f0aa2b9 vocab=fe3ef3f3
 -/
 theorem GoodOn.subset {s : Finset ℤ} {blocks : Finset (Finset ℤ)}
    (h : GoodOn s blocks) {b : Finset ℤ} (hb : b ∈ blocks) : b ⊆ s := by
  intro x hx
  rw [← h.1]
  exact Finset.mem_biUnion.mpr ⟨b, hb, hx⟩

 /--
 @isnad1 id=goodon.0h0v.s3.e6bbaca773c0 from=translated src=- shape=240163bb vocab=45d508e9
 -/
 theorem goodOn_empty : GoodOn ∅ ∅ := by simp [GoodOn]

 /--
 @isnad1 id=hasgood.0h0v.s2.eb37dbd80c7c from=translated src=- shape=ed5d6145 vocab=f1d165eb
 -/
 theorem hasGood_empty : HasGood ∅ := ⟨∅, goodOn_empty⟩

 /--
 @isnad1 id=goodon.3h4v.s5.0a687fd24e54 from=translated src=- shape=40786b37 vocab=cb3a5513
 -/
 theorem GoodOn.union {s t : Finset ℤ} {bs cs : Finset (Finset ℤ)}
    (hs : GoodOn s bs) (ht : GoodOn t cs) (hst : Disjoint s t) :
    GoodOn (s ∪ t) (bs ∪ cs) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.union_biUnion, hs.1, ht.1]
  · intro b hb c hc hbc
    rcases Finset.mem_union.mp hb with hb | hb <;>
      rcases Finset.mem_union.mp hc with hc | hc
    · exact hs.2.1 b hb c hc hbc
    · exact hst.mono (hs.subset hb) (ht.subset hc)
    · exact hst.symm.mono (ht.subset hb) (hs.subset hc)
    · exact ht.2.1 b hb c hc hbc
  · intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hs.2.2 b hb
    · exact ht.2.2 b hb

 /--
 @isnad1 id=hasgood.3h2v.s4.920dafb0804b from=translated src=- shape=11371947 vocab=7abd60e6
 -/
 theorem HasGood.union {s t : Finset ℤ} (hs : HasGood s) (ht : HasGood t)
    (hst : Disjoint s t) : HasGood (s ∪ t) := by
  obtain ⟨bs, hbs⟩ := hs
  obtain ⟨cs, hcs⟩ := ht
  exact ⟨bs ∪ cs, hbs.union hcs hst⟩

 /--
 @isnad1 id=goodon.1h1v.s4.43e97a50382d from=translated src=- shape=a72d4548 vocab=7117cde8
 -/
 theorem GoodBlock.goodOn {b : Finset ℤ} (hb : GoodBlock b) : GoodOn b {b} := by
  simpa [GoodOn, GoodBlock] using hb

 /--
 @isnad1 id=hasgood.1h1v.s3.81a9328a7d25 from=translated src=- shape=4c88451a vocab=deaf45f4
 -/
 theorem GoodBlock.hasGood {b : Finset ℤ} (hb : GoodBlock b) : HasGood b :=
  ⟨{b}, hb.goodOn⟩

 /--
 @isnad1 id=goodbloc.0h1v.s4.d8a4275808a9 from=translated src=- shape=d06deee1 vocab=0d3c4c23
 -/
 theorem goodBlock_singleton (k : ℕ) : GoodBlock {(3 : ℤ)^k} := by
  refine ⟨by simp, by simp, k, ?_⟩
  simp

 /--
 @isnad1 id=goodbloc.2h3v.s5.da0dcc9dfd70 from=translated src=- shape=0d309645 vocab=c743c51c
 -/
 theorem goodBlock_pair {x y : ℤ} (hxy : x ≠ y) {k : ℕ}
    (hs : x + y = (3 : ℤ)^k) : GoodBlock {x, y} := by
  refine ⟨by simp, ?_, k, ?_⟩
  · simp [Finset.card_insert_of_notMem, hxy]
  · simpa [Finset.sum_insert, hxy] using hs

 /--
 @isnad1 id=goodbloc.4h4v.s6.698bf3dcd761 from=translated src=- shape=b9e10083 vocab=c743c51c
 -/
 theorem goodBlock_triple {x y z : ℤ} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) {k : ℕ} (hs : x + y + z = (3 : ℤ)^k) :
    GoodBlock {x, y, z} := by
  refine ⟨by simp, ?_, k, ?_⟩
  · simp [Finset.card_insert_of_notMem, hxy, hxz, hyz]
  · simpa [Finset.sum_insert, hxy, hxz, hyz, add_assoc] using hs

/-- Assemble an indexed family of disjoint good blocks.
@isnad1 id=goodon.2h3v.s6.0fb8a1db8cc0 from=translated src=- shape=6f395817 vocab=c6208de8
-/
 theorem goodOn_image {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → Finset ℤ) (hgood : ∀ i ∈ u, GoodBlock (f i))
    (hdisj : ∀ i ∈ u, ∀ j ∈ u, i ≠ j → Disjoint (f i) (f j)) :
    GoodOn (u.biUnion f) (u.image f) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp
  · intro b hb c hc hbc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact hdisj i hi j hj (fun hij => hbc (congrArg f hij))
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact hgood i hi

 /--
 @isnad1 id=hasgood.2h3v.s6.ac2e521814a2 from=translated src=- shape=571c0b0d vocab=796e5de6
 -/
 theorem hasGood_biUnion {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → Finset ℤ) (hgood : ∀ i ∈ u, GoodBlock (f i))
    (hdisj : ∀ i ∈ u, ∀ j ∈ u, i ≠ j → Disjoint (f i) (f j)) :
    HasGood (u.biUnion f) := ⟨u.image f, goodOn_image u f hgood hdisj⟩

end

end GN
