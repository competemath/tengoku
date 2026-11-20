import Tengoku.GnmLean.GN.Transfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace GN
noncomputable section

/-- Literal source partition for the critical offset two.-/
def smallSource2 : Finset (Finset ℤ) := {{1,2}}

/-- Literal source partition for the critical offset five.-/
def smallSource5 : Finset (Finset ℤ) := {{1,2}, {3}, {4,5}}

/-- Literal source partition for the critical offset eight.-/
def smallSource8 : Finset (Finset ℤ) := {{1,8}, {2,7}, {3,6}, {4,5}}

/-- Signed frame for offset two and partner one.-/
def smallFrame2 : Finset (Finset ℤ) := {{-3,1,2}}

/-- Signed frame for offset five and partner four.-/
def smallFrame5 : Finset (Finset ℤ) := {{-9,4,5}, {-3,1,2}, {-2,-1,3}}

/-- Signed frame for offset eight and partner one.-/
def smallFrame8 : Finset (Finset ℤ) :=
  {{-9,4,5}, {-7,1,6}, {-6,-2,8}, {-5,2,3}, {-4,-3,7}}

 /--
 @isnad1 id=goodon.0h0v.s3.c3d7f7cf7b0f from=translated src=- shape=06f63001 vocab=191a4f22
 -/
 theorem smallSource2_good : GoodOn (interval 2) smallSource2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp [smallSource2, interval]
    omega
  · intro b hb c hc hbc
    simp only [smallSource2, Finset.mem_singleton] at hb hc
    subst b c
    exact (hbc rfl).elim
  · intro b hb
    simp only [smallSource2, Finset.mem_singleton] at hb
    subst b
    exact goodBlock_pair (by norm_num) (k := 1) (by norm_num)

 /--
 @isnad1 id=goodon.0h0v.s3.467c352c5cad from=translated src=- shape=06f63001 vocab=58cbd232
 -/
 theorem smallSource5_good : GoodOn (interval 5) smallSource5 := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp [smallSource5, interval]
    omega
  · intro b hb c hc hbc
    simp only [smallSource5, Finset.mem_insert, Finset.mem_singleton] at hb hc
    rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
      simp_all [Finset.disjoint_left]
  · intro b hb
    simp only [smallSource5, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact goodBlock_pair (by norm_num) (k := 1) (by norm_num)
    · exact goodBlock_singleton 1
    · exact goodBlock_pair (by norm_num) (k := 2) (by norm_num)

 /--
 @isnad1 id=goodon.0h0v.s3.6b9875d266b9 from=translated src=- shape=06f63001 vocab=f2b0e1d1
 -/
 theorem smallSource8_good : GoodOn (interval 8) smallSource8 := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp [smallSource8, interval]
    omega
  · intro b hb c hc hbc
    simp only [smallSource8, Finset.mem_insert, Finset.mem_singleton] at hb hc
    rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;> simp_all [Finset.disjoint_left]
  · intro b hb
    simp only [smallSource8, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl <;>
      exact goodBlock_pair (by norm_num) (k := 2) (by norm_num)

 /--
 @isnad1 id=zeropart.0h0v.s3.3731ae8aab66 from=translated src=- shape=0e05262d vocab=6ece4b0d
 -/
 theorem smallFrame2_zero : ZeroPartition (signedVertices 2 1) smallFrame2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [signedVertices, Finset.mem_union, mem_neg_image, Finset.mem_erase,
      Finset.mem_Icc, Finset.mem_singleton]
    simp [smallFrame2]
    omega
  · intro b hb c hc hbc
    simp only [smallFrame2, Finset.mem_singleton] at hb hc
    subst b c
    exact (hbc rfl).elim
  · intro b hb
    simp only [smallFrame2, Finset.mem_singleton] at hb
    subst b
    norm_num

 /--
 @isnad1 id=zeropart.0h0v.s3.64c19a411fa5 from=translated src=- shape=0e05262d vocab=1c60f7d5
 -/
 theorem smallFrame5_zero : ZeroPartition (signedVertices 5 4) smallFrame5 := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [signedVertices, Finset.mem_union, mem_neg_image, Finset.mem_erase,
      Finset.mem_Icc, Finset.mem_singleton]
    simp [smallFrame5]
    omega
  · intro b hb c hc hbc
    simp only [smallFrame5, Finset.mem_insert, Finset.mem_singleton] at hb hc
    rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
      simp_all [Finset.disjoint_left]
  · intro b hb
    simp only [smallFrame5, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> norm_num

 /--
 @isnad1 id=zeropart.0h0v.s3.d5c6baa1a998 from=translated src=- shape=0e05262d vocab=a600c979
 -/
 theorem smallFrame8_zero : ZeroPartition (signedVertices 8 1) smallFrame8 := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [signedVertices, Finset.mem_union, mem_neg_image, Finset.mem_erase,
      Finset.mem_Icc, Finset.mem_singleton]
    simp [smallFrame8]
    omega
  · intro b hb c hc hbc
    simp only [smallFrame8, Finset.mem_insert, Finset.mem_singleton] at hb hc
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all [Finset.disjoint_left]
  · intro b hb
    simp only [smallFrame8, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> norm_num

 /--
 @isnad1 id=hasgood.2h2v.s5.d97e1e9939ee from=translated src=- shape=1b203e92 vocab=b84d9107
 -/
 theorem critical_offset_two {P t : ℕ} (hP : P = 3^t) (hPr : 2*2 < P) :
    HasGood (interval (P+2)) := by
  exact critical_transfer hP hPr smallSource2_good
    (b := {1,2}) (a := 1) (by simp [smallSource2])
    (by simp) (by simp) (by norm_num) smallFrame2_zero

 /--
 @isnad1 id=hasgood.2h2v.s5.094770c7ee41 from=translated src=- shape=1b203e92 vocab=b84d9107
 -/
 theorem critical_offset_five {P t : ℕ} (hP : P = 3^t) (hPr : 2*5 < P) :
    HasGood (interval (P+5)) := by
  exact critical_transfer hP hPr smallSource5_good
    (b := {4,5}) (a := 4) (by simp [smallSource5])
    (by simp) (by simp) (by norm_num) smallFrame5_zero

 /--
 @isnad1 id=hasgood.2h2v.s5.562be47e9fca from=translated src=- shape=1b203e92 vocab=b84d9107
 -/
 theorem critical_offset_eight {P t : ℕ} (hP : P = 3^t) (hPr : 2*8 < P) :
    HasGood (interval (P+8)) := by
  exact critical_transfer hP hPr smallSource8_good
    (b := {1,8}) (a := 1) (by simp [smallSource8])
    (by simp) (by simp) (by norm_num) smallFrame8_zero

/-- Every critical offset below eleven is supplied by an explicit certificate.
@isnad1 id=hasgood.4h3v.s6.560c4f30b0d9 from=translated src=- shape=da4bfeb0 vocab=af9e758b
-/
theorem critical_small_extension {P r t : ℕ} (hP : P = 3^t) (hPr : 2*r < P)
    (hsmall : r < 11) (hmod : r % 3 = 2) : HasGood (interval (P+r)) := by
  have hr : r = 2 ∨ r = 5 ∨ r = 8 := by omega
  rcases hr with rfl | rfl | rfl
  · exact critical_offset_two hP hPr
  · exact critical_offset_five hP hPr
  · exact critical_offset_eight hP hPr

end
end GN
