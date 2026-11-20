import Tengoku.GnmLean.GN.Langford

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace GN
noncomputable section

/-! Explicit near-minimal extended Langford pairings. The affine coefficients
were found independently by a finite search; the theorems below prove their
validity for every integer q ≥ 4. No search result is assumed by the proof. -/

def near1OddLow (q h : ℤ) : Finset (ℤ × ℤ) :=
  hingedPairs (2*q+3) 2 (q-2) h ∪
  {(4,3*q+4)} ∪
  hingedPairs (3*q+3) 2 0 h ∪
  affinePairs (3*q+5) (6*q+7) (q-3) ∪
  {(4*q+5,8*q+5)} ∪
  hingedPairs (4*q+3) 2 0 h ∪
  affinePairs 5 (4*q+7) (q-2) ∪
  {(3*q+2,8*q+3)} ∪
  affinePairs (q+4) (6*q+6) (q-2) ∪
  {(1,6*q+2)} ∪
  {(3,6*q+5)}

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.f6d0f9b43007 from=translated src=- shape=3ec6e1b9 vocab=71022e48
-/
theorem near1OddLow_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 4*q+4 ≤ h ∧ h ≤ 6*q ∨ h = 6*q+4 ∨ h = 8*q+4) (heven : h%2 = 0) :
    pairEndpoints (near1OddLow q h) = (Finset.Icc 1 (8*q+5)).erase h := by
  ext x
  simp only [near1OddLow, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s6.ef05b959e3e2 from=translated src=- shape=70575ca2 vocab=5b78cee8
-/
theorem near1OddLow_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near1OddLow q h) = Finset.Icc (2*q+1) (6*q+2) := by
  ext x
  simp only [near1OddLow, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.c6845f424520 from=translated src=- shape=b5b1b387 vocab=8aa3357e
-/
theorem near1OddLow_card (q h : ℤ) (hq : 4 ≤ q) :
    (near1OddLow q h).card ≤ (4*q+2).toNat := by
  have hc : (near1OddLow q h).card ≤ (q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-3+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat := by
    unfold near1OddLow hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s7.2101efc71333 from=translated src=- shape=f542f4eb vocab=555f9e93
-/
theorem near1OddLow_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 4*q+4 ≤ h ∧ h ≤ 6*q ∨ h = 6*q+4 ∨ h = 8*q+4) (heven : h%2 = 0) :
    LangfordPairing (2*q+1) (6*q+2) h (near1OddLow q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near1OddLow_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near1OddLow_differences q h hq
  · convert near1OddLow_card q h hq using 1; congr 1; omega

def near1OddHigh (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(4*q+4,6*q+5)} ∪
  affinePairs (2*q+5) (4*q+7) (q-3) ∪
  {(3,3*q+3)} ∪
  {(q+4,4*q+5)} ∪
  hingedPairs (3*q+4) 2 (q-2) h ∪
  hingedPairs (4*q+3) 2 0 h ∪
  affinePairs 4 (4*q+6) (q-1) ∪
  affinePairs (q+5) (6*q+7) (q-1) ∪
  {(1,6*q+3)}

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.d81607a8139b from=translated src=- shape=f8217cdd vocab=30bfbded
-/
theorem near1OddHigh_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 6*q+6 ≤ h ∧ h ≤ 8*q+2) (heven : h%2 = 0) :
    pairEndpoints (near1OddHigh q h) = (Finset.Icc 1 (8*q+5)).erase h := by
  ext x
  simp only [near1OddHigh, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s6.94b1bffcb71c from=translated src=- shape=70575ca2 vocab=8b988054
-/
theorem near1OddHigh_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near1OddHigh q h) = Finset.Icc (2*q+1) (6*q+2) := by
  ext x
  simp only [near1OddHigh, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.40b820d281da from=translated src=- shape=b5b1b387 vocab=525644ca
-/
theorem near1OddHigh_card (q h : ℤ) (hq : 4 ≤ q) :
    (near1OddHigh q h).card ≤ (4*q+2).toNat := by
  have hc : (near1OddHigh q h).card ≤ (0+1 : ℤ).toNat+(q-3+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(0+1 : ℤ).toNat := by
    unfold near1OddHigh hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s7.00367aea0721 from=translated src=- shape=0517ba6c vocab=e8530b16
-/
theorem near1OddHigh_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 6*q+6 ≤ h ∧ h ≤ 8*q+2) (heven : h%2 = 0) :
    LangfordPairing (2*q+1) (6*q+2) h (near1OddHigh q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near1OddHigh_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near1OddHigh_differences q h hq
  · convert near1OddHigh_card q h hq using 1; congr 1; omega

def near1OddGap (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(q+2,3*q+3)} ∪
  hingedPairs (2*q+4) 2 (q-3) h ∪
  hingedPairs (3*q+2) 2 0 h ∪
  affinePairs (3*q+4) (6*q+5) q ∪
  affinePairs 3 (4*q+5) (q-2) ∪
  affinePairs (q+3) (6*q+4) q ∪
  {(1,6*q+3)}

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.ff61221f6c8d from=translated src=- shape=2f9aedab vocab=faf40a04
-/
theorem near1OddGap_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ h = 6*q+2) (heven : h%2 = 0) :
    pairEndpoints (near1OddGap q h) = (Finset.Icc 1 (8*q+5)).erase h := by
  ext x
  simp only [near1OddGap, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s6.bdc049d908d1 from=translated src=- shape=70575ca2 vocab=67e969ca
-/
theorem near1OddGap_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near1OddGap q h) = Finset.Icc (2*q+1) (6*q+2) := by
  ext x
  simp only [near1OddGap, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.9301baef32ae from=translated src=- shape=b5b1b387 vocab=2cc1ec95
-/
theorem near1OddGap_card (q h : ℤ) (hq : 4 ≤ q) :
    (near1OddGap q h).card ≤ (4*q+2).toNat := by
  have hc : (near1OddGap q h).card ≤ (0+1 : ℤ).toNat+(q-3+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(q+1 : ℤ).toNat+(0+1 : ℤ).toNat := by
    unfold near1OddGap hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s7.01d1130682ff from=translated src=- shape=7c94b1eb vocab=988243dd
-/
theorem near1OddGap_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ h = 6*q+2) (heven : h%2 = 0) :
    LangfordPairing (2*q+1) (6*q+2) h (near1OddGap q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near1OddGap_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near1OddGap_differences q h hq
  · convert near1OddGap_card q h hq using 1; congr 1; omega

def near2EvenHigh (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(4*q+3,6*q+3)} ∪
  {(1,2*q+2)} ∪
  affinePairs (2*q+3) (4*q+5) (q-2) ∪
  hingedPairs (3*q+3) 2 (q-1) h ∪
  affinePairs 3 (4*q+4) (q-1) ∪
  {(3*q+2,8*q+3)} ∪
  affinePairs (q+3) (6*q+5) (q-2)

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.f09cd7358d59 from=translated src=- shape=f8217cdd vocab=37d8706a
-/
theorem near2EvenHigh_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 6*q+4 ≤ h ∧ h ≤ 8*q+2) (heven : h%2 = 0) :
    pairEndpoints (near2EvenHigh q h) = (Finset.Icc 1 (8*q+3)).erase h := by
  ext x
  simp only [near2EvenHigh, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s5.16a8c8d70135 from=translated src=- shape=62fd5964 vocab=055371ba
-/
theorem near2EvenHigh_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near2EvenHigh q h) = Finset.Icc (2*q) (6*q) := by
  ext x
  simp only [near2EvenHigh, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.c069dad94552 from=translated src=- shape=b5b1b387 vocab=2512ba29
-/
theorem near2EvenHigh_card (q h : ℤ) (hq : 4 ≤ q) :
    (near2EvenHigh q h).card ≤ (4*q+1).toNat := by
  have hc : (near2EvenHigh q h).card ≤ (0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat := by
    unfold near2EvenHigh hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s7.e1955060a997 from=translated src=- shape=e1a442fb vocab=cdbaf1fb
-/
theorem near2EvenHigh_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 6*q+4 ≤ h ∧ h ≤ 8*q+2) (heven : h%2 = 0) :
    LangfordPairing (2*q) (6*q) h (near2EvenHigh q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near2EvenHigh_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near2EvenHigh_differences q h hq
  · convert near2EvenHigh_card q h hq using 1; congr 1; omega

def near2EvenLow (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(6*q+3,8*q+3)} ∪
  hingedPairs (2*q+3) 2 (q-2) h ∪
  hingedPairs (3*q+2) 2 0 h ∪
  {(q+2,4*q+3)} ∪
  affinePairs (3*q+3) (6*q+5) (q-2) ∪
  {(1,4*q+2)} ∪
  affinePairs 3 (4*q+5) (q-2) ∪
  affinePairs (q+3) (6*q+4) (q-1)

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.8815a9d1f2a3 from=translated src=- shape=f8217cdd vocab=cae07822
-/
theorem near2EvenLow_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 4*q+4 ≤ h ∧ h ≤ 6*q+2) (heven : h%2 = 0) :
    pairEndpoints (near2EvenLow q h) = (Finset.Icc 1 (8*q+3)).erase h := by
  ext x
  simp only [near2EvenLow, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s5.568162913b4c from=translated src=- shape=62fd5964 vocab=c10f54b3
-/
theorem near2EvenLow_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near2EvenLow q h) = Finset.Icc (2*q) (6*q) := by
  ext x
  simp only [near2EvenLow, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.f7e97c838fcf from=translated src=- shape=b5b1b387 vocab=3ed023a2
-/
theorem near2EvenLow_card (q h : ℤ) (hq : 4 ≤ q) :
    (near2EvenLow q h).card ≤ (4*q+1).toNat := by
  have hc : (near2EvenLow q h).card ≤ (0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(q-1+1 : ℤ).toNat := by
    unfold near2EvenLow hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s7.c623b48e1d48 from=translated src=- shape=e1a442fb vocab=bd0e7561
-/
theorem near2EvenLow_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 4*q+4 ≤ h ∧ h ≤ 6*q+2) (heven : h%2 = 0) :
    LangfordPairing (2*q) (6*q) h (near2EvenLow q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near2EvenLow_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near2EvenLow_differences q h hq
  · convert near2EvenLow_card q h hq using 1; congr 1; omega

def near2EvenCenter (q h : ℤ) : Finset (ℤ × ℤ) :=
  hingedPairs (2*q+2) 2 0 h ∪
  {(6*q+1,8*q+2)} ∪
  affinePairs (2*q+3) (4*q+5) (q-3) ∪
  {(q+1,4*q+1)} ∪
  affinePairs (3*q+2) (6*q+3) (q-2) ∪
  {(4*q+3,8*q+3)} ∪
  affinePairs 3 (4*q+4) (q-3) ∪
  {(3*q+1,8*q)} ∪
  affinePairs (q+2) (6*q+2) (q-2) ∪
  {(1,6*q)} ∪
  {(2*q+1,8*q+1)}

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.b20fe4ee52ed from=translated src=- shape=2f9aedab vocab=b4318ced
-/
theorem near2EvenCenter_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ h = 4*q+2) (heven : h%2 = 0) :
    pairEndpoints (near2EvenCenter q h) = (Finset.Icc 1 (8*q+3)).erase h := by
  ext x
  simp only [near2EvenCenter, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s5.183971d5d6dd from=translated src=- shape=62fd5964 vocab=125a8426
-/
theorem near2EvenCenter_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near2EvenCenter q h) = Finset.Icc (2*q) (6*q) := by
  ext x
  simp only [near2EvenCenter, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.d485fc9df744 from=translated src=- shape=b5b1b387 vocab=c99aafe9
-/
theorem near2EvenCenter_card (q h : ℤ) (hq : 4 ≤ q) :
    (near2EvenCenter q h).card ≤ (4*q+1).toNat := by
  have hc : (near2EvenCenter q h).card ≤ (0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-3+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-3+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat := by
    unfold near2EvenCenter hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s6.2d325975d042 from=translated src=- shape=9a9c8070 vocab=4ab78aa7
-/
theorem near2EvenCenter_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ h = 4*q+2) (heven : h%2 = 0) :
    LangfordPairing (2*q) (6*q) h (near2EvenCenter q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near2EvenCenter_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near2EvenCenter_differences q h hq
  · convert near2EvenCenter_card q h hq using 1; congr 1; omega

def near2OddLow (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(6*q+6,8*q+7)} ∪
  hingedPairs (2*q+4) 2 (q-2) h ∪
  hingedPairs (3*q+3) 2 0 h ∪
  {(q+3,4*q+5)} ∪
  affinePairs (3*q+4) (6*q+7) (q-1) ∪
  {(1,4*q+4)} ∪
  affinePairs 3 (4*q+7) (q-1) ∪
  affinePairs (q+4) (6*q+8) (q-1)

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.3ede32285d25 from=translated src=- shape=f8217cdd vocab=da6637b3
-/
theorem near2OddLow_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 4*q+6 ≤ h ∧ h ≤ 6*q+4) (heven : h%2 = 0) :
    pairEndpoints (near2OddLow q h) = (Finset.Icc 1 (8*q+7)).erase h := by
  ext x
  simp only [near2OddLow, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s6.dd05de3471b8 from=translated src=- shape=70575ca2 vocab=af338d48
-/
theorem near2OddLow_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near2OddLow q h) = Finset.Icc (2*q+1) (6*q+3) := by
  ext x
  simp only [near2OddLow, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.c74b74cae53d from=translated src=- shape=b5b1b387 vocab=e16fa727
-/
theorem near2OddLow_card (q h : ℤ) (hq : 4 ≤ q) :
    (near2OddLow q h).card ≤ (4*q+3).toNat := by
  have hc : (near2OddLow q h).card ≤ (0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(q-1+1 : ℤ).toNat := by
    unfold near2OddLow hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s7.9d1757eb915a from=translated src=- shape=0517ba6c vocab=f6e543fe
-/
theorem near2OddLow_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ 4*q+6 ≤ h ∧ h ≤ 6*q+4) (heven : h%2 = 0) :
    LangfordPairing (2*q+1) (6*q+3) h (near2OddLow q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near2OddLow_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near2OddLow_differences q h hq
  · convert near2OddLow_card q h hq using 1; congr 1; omega

def near2OddCenter (q h : ℤ) : Finset (ℤ × ℤ) :=
  hingedPairs (2*q+3) 2 0 h ∪
  {(6*q+3,8*q+5)} ∪
  hingedPairs (2*q+5) 2 (q-3) h ∪
  {(q+2,4*q+3)} ∪
  hingedPairs (3*q+4) 2 (q-2) h ∪
  {(4*q+6,8*q+7)} ∪
  affinePairs 3 (4*q+5) (q-2) ∪
  {(3*q+3,8*q+4)} ∪
  affinePairs (q+3) (6*q+5) (q-1) ∪
  {(2*q+4,8*q+6)} ∪
  {(1,6*q+4)}

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.4c65c2ed30ba from=translated src=- shape=7b1379fd vocab=15b5d5a2
-/
theorem near2OddCenter_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ h = 4*q+4 ∨ 6*q+6 ≤ h ∧ h ≤ 8*q+2) (heven : h%2 = 0) :
    pairEndpoints (near2OddCenter q h) = (Finset.Icc 1 (8*q+7)).erase h := by
  ext x
  simp only [near2OddCenter, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s6.2e99646cc1ce from=translated src=- shape=70575ca2 vocab=606002ff
-/
theorem near2OddCenter_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near2OddCenter q h) = Finset.Icc (2*q+1) (6*q+3) := by
  ext x
  simp only [near2OddCenter, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.0fced7d55bd4 from=translated src=- shape=b5b1b387 vocab=df9c3ad0
-/
theorem near2OddCenter_card (q h : ℤ) (hq : 4 ≤ q) :
    (near2OddCenter q h).card ≤ (4*q+3).toNat := by
  have hc : (near2OddCenter q h).card ≤ (0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-3+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat := by
    unfold near2OddCenter hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s7.4335eaaa4d4f from=translated src=- shape=b7fecda8 vocab=7f656c62
-/
theorem near2OddCenter_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ h = 4*q+4 ∨ 6*q+6 ≤ h ∧ h ≤ 8*q+2) (heven : h%2 = 0) :
    LangfordPairing (2*q+1) (6*q+3) h (near2OddCenter q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near2OddCenter_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near2OddCenter_differences q h hq
  · convert near2OddCenter_card q h hq using 1; congr 1; omega

def near2OddEnd (q h : ℤ) : Finset (ℤ × ℤ) :=
  {(4*q+4,6*q+5)} ∪
  {(1,2*q+3)} ∪
  affinePairs (2*q+4) (4*q+7) (q-2) ∪
  hingedPairs (3*q+4) 2 (q-2) h ∪
  hingedPairs (4*q+3) 2 0 h ∪
  {(4*q+5,8*q+7)} ∪
  affinePairs 3 (4*q+6) (q-1) ∪
  {(3*q+3,8*q+6)} ∪
  affinePairs (q+3) (6*q+7) (q-1)

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.3h2v.s7.59ef4b95ff53 from=translated src=- shape=2f9aedab vocab=a1620fd7
-/
theorem near2OddEnd_endpoints (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ h = 8*q+4) (heven : h%2 = 0) :
    pairEndpoints (near2OddEnd q h) = (Finset.Icc 1 (8*q+7)).erase h := by
  ext x
  simp only [near2OddEnd, pairEndpoints_union, pairEndpoints_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, hingedPairs,
    mem_pairEndpoints_pivotAffinePairs, mem_pairEndpoints_affinePairs,
    Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : x = h
  · subst x
    omega
  by_cases hz : x = 2
  · subst x
    omega
  simp only [hz, false_and, or_false]
  clear hh heven
  omega

set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.1h2v.s6.6e89e4dbdd1d from=translated src=- shape=70575ca2 vocab=26385b65
-/
theorem near2OddEnd_differences (q h : ℤ) (hq : 4 ≤ q) :
    pairDifferences (near2OddEnd q h) = Finset.Icc (2*q+1) (6*q+3) := by
  ext x
  simp only [near2OddEnd, pairDifferences_union, pairDifferences_singleton, Finset.mem_singleton, Finset.mem_union,
    mem_pairDifferences_hingedPairs, mem_pairDifferences_affinePairs, Finset.mem_Icc]
  omega

/--
@isnad1 id=le.1h2v.s5.4112f24cb8d0 from=translated src=- shape=b5b1b387 vocab=f6c1ac90
-/
theorem near2OddEnd_card (q h : ℤ) (hq : 4 ≤ q) :
    (near2OddEnd q h).card ≤ (4*q+3).toNat := by
  have hc : (near2OddEnd q h).card ≤ (0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(q-2+1 : ℤ).toNat+(0+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-1+1 : ℤ).toNat+(0+1 : ℤ).toNat+(q-1+1 : ℤ).toNat := by
    unfold near2OddEnd hingedPairs
    repeat' apply card_union_le_of_le
    all_goals first | exact card_affinePairs_le _ _ _ |
      exact card_pivotAffinePairs_le _ _ _ _ _ | simp
  omega

/--
@isnad1 id=langford.3h2v.s7.ccf9026a59e4 from=translated src=- shape=7c94b1eb vocab=2f45f9fb
-/
theorem near2OddEnd_pairing (q h : ℤ) (hq : 4 ≤ q)
    (hh : h = 2 ∨ h = 8*q+4) (heven : h%2 = 0) :
    LangfordPairing (2*q+1) (6*q+3) h (near2OddEnd q h) := by
  constructor
  · omega
  · omega
  · omega
  · convert near2OddEnd_endpoints q h hq hh heven using 1; congr 2; omega
  · exact near2OddEnd_differences q h hq
  · convert near2OddEnd_card q h hq using 1; congr 1; omega

private theorem near2_even_upper {q h : ℤ} (hq : 4 ≤ q)
    (hh : 4*q+2 ≤ h ∧ h ≤ 8*q+2) (hp : h%2 = 0) :
    ∃ ps, LangfordPairing (2*q) (6*q) h ps := by
  by_cases hc : h = 4*q+2
  · exact ⟨_, near2EvenCenter_pairing q h hq (by omega) hp⟩
  by_cases hl : h ≤ 6*q+2
  · exact ⟨_, near2EvenLow_pairing q h hq (by omega) hp⟩
  · exact ⟨_, near2EvenHigh_pairing q h hq (by omega) hp⟩

private theorem near2_even_exists {q h : ℤ} (hq : 4 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+3) (hp : h%2 = 0) :
    ∃ ps, LangfordPairing (2*q) (6*q) h ps := by
  by_cases hu : 4*q+2 ≤ h
  · exact near2_even_upper hq (by omega) hp
  · obtain ⟨ps, hps⟩ := near2_even_upper (h := 8*q+4-h) hq (by omega) (by omega)
    have hr := hps.reflect
    have he : 2*(6*q-2*q+1)+2-(8*q+4-h) = h := by omega
    rw [he] at hr
    exact ⟨_, hr⟩

private theorem near2_odd_upper {q h : ℤ} (hq : 4 ≤ q)
    (hh : 4*q+4 ≤ h ∧ h ≤ 8*q+6) (hp : h%2 = 0) :
    ∃ ps, LangfordPairing (2*q+1) (6*q+3) h ps := by
  by_cases he : h = 8*q+6
  · have hr := (near2OddEnd_pairing q 2 hq (Or.inl rfl) (by omega)).reflect
    have heq : 2*(6*q+3-(2*q+1)+1)+2-2 = h := by omega
    rw [heq] at hr
    exact ⟨_, hr⟩
  by_cases hend : h = 8*q+4
  · exact ⟨_, near2OddEnd_pairing q h hq (by omega) hp⟩
  by_cases hc : h = 4*q+4 ∨ 6*q+6 ≤ h
  · exact ⟨_, near2OddCenter_pairing q h hq (by omega) hp⟩
  · exact ⟨_, near2OddLow_pairing q h hq (by omega) hp⟩

private theorem near2_odd_exists {q h : ℤ} (hq : 4 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+7) (hp : h%2 = 0) :
    ∃ ps, LangfordPairing (2*q+1) (6*q+3) h ps := by
  by_cases hu : 4*q+4 ≤ h
  · exact near2_odd_upper hq (by omega) hp
  · obtain ⟨ps, hps⟩ := near2_odd_upper (h := 8*q+8-h) hq (by omega) (by omega)
    have hr := hps.reflect
    have he : 2*(6*q+3-(2*q+1)+1)+2-(8*q+8-h) = h := by omega
    rw [he] at hr
    exact ⟨_, hr⟩

/-- Every allowed hole has a pairing of excess two, for every defect d≥8.
@isnad1 id=ex.3h2v.s6.5a5e87baa720 from=translated src=- shape=505649bb vocab=dd5ad13d
-/
theorem exists_near2_langford {d h : ℤ} (hd : 8 ≤ d)
    (hh : 1 ≤ h ∧ h ≤ 4*d+3) (hp : h%2 = 0) :
    ∃ ps, LangfordPairing d (3*d) h ps := by
  let q := d/2
  have hq : 4 ≤ q := by dsimp [q]; omega
  have hdq : d = 2*q ∨ d = 2*q+1 := by dsimp [q]; omega
  rcases hdq with he | he
  · obtain ⟨ps, hps⟩ := near2_even_exists (q := q) hq (by omega) hp
    have hk : 6*q = 3*d := by omega
    rw [← he, hk] at hps
    exact ⟨ps, hps⟩
  · obtain ⟨ps, hps⟩ := near2_odd_exists (q := q) hq (by omega) hp
    have hk : 6*q+3 = 3*d := by omega
    rw [← he, hk] at hps
    exact ⟨ps, hps⟩

private theorem near1_odd_upper {q h : ℤ} (hq : 4 ≤ q)
    (hh : 4*q+4 ≤ h ∧ h ≤ 8*q+4) (hp : h%2 = 0) :
    ∃ ps, LangfordPairing (2*q+1) (6*q+2) h ps := by
  by_cases hg : h = 6*q+2
  · exact ⟨_, near1OddGap_pairing q h hq (by omega) hp⟩
  by_cases hl : h ≤ 6*q+4 ∨ h = 8*q+4
  · exact ⟨_, near1OddLow_pairing q h hq (by omega) hp⟩
  · exact ⟨_, near1OddHigh_pairing q h hq (by omega) hp⟩

/-- The odd-defect half of the excess-one family.
@isnad1 id=ex.3h2v.s7.07220fad68b7 from=translated src=- shape=20b0f678 vocab=dd5ad13d
-/
theorem near1_odd_exists {q h : ℤ} (hq : 4 ≤ q)
    (hh : 1 ≤ h ∧ h ≤ 8*q+5) (hp : h%2 = 0) :
    ∃ ps, LangfordPairing (2*q+1) (6*q+2) h ps := by
  by_cases hu : 4*q+4 ≤ h
  · exact near1_odd_upper hq (by omega) hp
  · obtain ⟨ps, hps⟩ := near1_odd_upper (h := 8*q+6-h) hq (by omega) (by omega)
    have hr := hps.reflect
    have he : 2*(6*q+2-(2*q+1)+1)+2-(8*q+6-h) = h := by omega
    rw [he] at hr
    exact ⟨_, hr⟩

end
end GN
