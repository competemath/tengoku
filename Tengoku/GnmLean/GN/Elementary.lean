import Tengoku.GnmLean.GN.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace GN

noncomputable section

/-- Complementary pairs partition an interval symmetric about an odd power of three.
@isnad1 id=hasgood.2h3v.s6.144ca4034a01 from=translated src=- shape=76e3bea4 vocab=6f542052
-/
theorem hasGood_complement_interval {k : ℕ} {h lo : ℤ}
    (hp : (3 : ℤ)^k = 2 * h + 1) (hlo : lo ≤ h + 1) :
    HasGood (Finset.Icc lo (2 * h + 1 - lo)) := by
  have hfamily := hasGood_biUnion (Finset.Icc lo h)
    (fun x : ℤ => ({x, 2 * h + 1 - x} : Finset ℤ))
    (by
      intro x hx
      have hx' := Finset.mem_Icc.mp hx
      apply goodBlock_pair (by omega) (k := k)
      omega)
    (by
      intro x hx y hy hxy
      have hx' := Finset.mem_Icc.mp hx
      have hy' := Finset.mem_Icc.mp hy
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
      omega)
  convert hfamily using 1
  ext z
  simp only [Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    by_cases hzh : z ≤ h
    · exact ⟨z, ⟨hz.1, hzh⟩, Or.inl rfl⟩
    · exact ⟨2 * h + 1 - z, by omega, Or.inr (by omega)⟩
  · rintro ⟨x, hx, hz⟩
    omega

/-- Add one contiguous interval above an already partitioned positive interval.
@isnad1 id=hasgood.3h2v.s5.ec3eea873b45 from=translated src=- shape=d928189a vocab=942fd167
-/
theorem HasGood.append_interval {m n : ℕ} (hmn : m ≤ n)
    (hs : HasGood (interval m))
    (ht : HasGood (Finset.Icc ((m : ℤ) + 1) (n : ℤ))) :
    HasGood (interval n) := by
  have hd : Disjoint (interval m) (Finset.Icc ((m : ℤ) + 1) (n : ℤ)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [interval, Finset.mem_Icc] at hx hx'
    omega
  have hu := hs.union ht hd
  convert hu using 1
  ext x
  simp only [interval, Finset.mem_union, Finset.mem_Icc]
  omega

/-- Extend a good prefix by complementary pairs with prescribed power-of-three sum.
@isnad1 id=hasgood.3h3v.s6.12defd55ffe3 from=translated src=- shape=2ee461c1 vocab=070e3bfe
-/
theorem complement_pair_extension {m n k : ℕ} (hmn : m ≤ n)
    (hsum : (m : ℤ) + (n : ℤ) + 1 = (3 : ℤ)^k)
    (hs : HasGood (interval m)) : HasGood (interval n) := by
  have hpodd : Odd ((3 : ℤ)^k) := (by decide : Odd (3 : ℤ)).pow
  obtain ⟨h, hh⟩ := hpodd
  have hp : (3 : ℤ)^k = 2 * h + 1 := by omega
  have hlo : (m : ℤ) + 1 ≤ h + 1 := by omega
  have ht := hasGood_complement_interval hp hlo
  have hend : 2 * h + 1 - ((m : ℤ) + 1) = (n : ℤ) := by omega
  rw [hend] at ht
  exact hs.append_interval hmn ht

/-- First family in the explicit symmetric zero-triple construction, translated by P.-/
def symmA (P q i : ℤ) : Finset ℤ :=
  {P - 3*q + i, P + 1 + i, P + 3*q - 1 - 2*i}

/-- Second family in the explicit symmetric zero-triple construction, translated by P.-/
def symmB (P q i : ℤ) : Finset ℤ :=
  {P - 2*q + i, P - q + i, P + 3*q - 2*i}

 /--
 @isnad1 id=goodbloc.2h4v.s5.8bbbb717cd6c from=translated src=- shape=3d9596a1 vocab=54e241ad
 -/
 theorem goodBlock_symmA {P q i : ℤ} {k : ℕ} (hp : P = (3 : ℤ)^k)
    (hi : 0 ≤ i ∧ i < q) : GoodBlock (symmA P q i) := by
  apply goodBlock_triple (by omega) (by omega) (by omega) (k := k + 1)
  rw [pow_succ, ← hp]
  ring

 /--
 @isnad1 id=goodbloc.2h4v.s5.dfaf47e420df from=translated src=- shape=3d9596a1 vocab=61b6d52b
 -/
 theorem goodBlock_symmB {P q i : ℤ} {k : ℕ} (hp : P = (3 : ℤ)^k)
    (hi : 0 ≤ i ∧ i < q) : GoodBlock (symmB P q i) := by
  apply goodBlock_triple (by omega) (by omega) (by omega) (k := k + 1)
  rw [pow_succ, ← hp]
  ring

 /--
 @isnad1 id=disjoint.3h4v.s5.250ab172c898 from=translated src=- shape=310dcaf4 vocab=c63bf3ce
 -/
 theorem symmA_disjoint {P q i j : ℤ} (hi : 0 ≤ i ∧ i < q)
    (hj : 0 ≤ j ∧ j < q) (hij : i ≠ j) : Disjoint (symmA P q i) (symmA P q j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  simp only [symmA, Finset.mem_insert, Finset.mem_singleton] at hx hx'
  omega

 /--
 @isnad1 id=disjoint.3h4v.s5.ff98cf35f55e from=translated src=- shape=310dcaf4 vocab=d87a2a33
 -/
 theorem symmB_disjoint {P q i j : ℤ} (hi : 0 ≤ i ∧ i < q)
    (hj : 0 ≤ j ∧ j < q) (hij : i ≠ j) : Disjoint (symmB P q i) (symmB P q j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  simp only [symmB, Finset.mem_insert, Finset.mem_singleton] at hx hx'
  omega

 /--
 @isnad1 id=disjoint.2h4v.s5.a1774fe2e105 from=translated src=- shape=bafdf95e vocab=b6473654
 -/
 theorem symmAB_disjoint {P q i j : ℤ} (hi : 0 ≤ i ∧ i < q)
    (hj : 0 ≤ j ∧ j < q) : Disjoint (symmA P q i) (symmB P q j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  simp only [symmA, symmB, Finset.mem_insert, Finset.mem_singleton] at hx hx'
  omega

/-- The two triple families cover precisely the symmetric interval with its center removed.
@isnad1 id=eq.1h2v.s7.32bb28573435 from=translated src=- shape=4c9342e5 vocab=08fb7012
-/
theorem symmetric_core_coverage (P q : ℤ) (hq : 0 ≤ q) :
    (Finset.Ico 0 q).biUnion (symmA P q) ∪
      (Finset.Ico 0 q).biUnion (symmB P q) =
    (Finset.Icc (P - 3*q) (P + 3*q)).erase P := by
  ext z
  simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_Ico, symmA, symmB,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨i, hi, hz⟩ | ⟨i, hi, hz⟩) <;> omega
  · intro hz
    by_cases hneg : z < P
    · by_cases hfirst : z < P - 2*q
      · exact Or.inl ⟨z - P + 3*q, by omega, Or.inl (by omega)⟩
      · by_cases hsecond : z < P - q
        · exact Or.inr ⟨z - P + 2*q, by omega, Or.inl (by omega)⟩
        · exact Or.inr ⟨z - P + q, by omega, Or.inr (Or.inl (by omega))⟩
    · by_cases hlow : z ≤ P + q
      · exact Or.inl ⟨z - P - 1, by omega, Or.inr (Or.inl (by omega))⟩
      · by_cases hparity : (P + 3*q - z) % 2 = 0
        · exact Or.inr ⟨(P + 3*q - z) / 2, by omega,
            Or.inr (Or.inr (by omega))⟩
        · exact Or.inl ⟨(P + 3*q - 1 - z) / 2, by omega,
            Or.inr (Or.inr (by omega))⟩

/-- The symmetric interval minus its center is partitioned by good triples.
@isnad1 id=hasgood.2h3v.s6.743a629f99a5 from=translated src=- shape=fb7adddd vocab=ef27d40c
-/
theorem hasGood_symmetric_core {P q : ℤ} {k : ℕ} (hp : P = (3 : ℤ)^k)
    (hq : 0 ≤ q) : HasGood ((Finset.Icc (P - 3*q) (P + 3*q)).erase P) := by
  have ha := hasGood_biUnion (Finset.Ico 0 q) (symmA P q)
    (fun i hi => goodBlock_symmA hp (Finset.mem_Ico.mp hi))
    (fun i hi j hj hij => symmA_disjoint (Finset.mem_Ico.mp hi) (Finset.mem_Ico.mp hj) hij)
  have hb := hasGood_biUnion (Finset.Ico 0 q) (symmB P q)
    (fun i hi => goodBlock_symmB hp (Finset.mem_Ico.mp hi))
    (fun i hi j hj hij => symmB_disjoint (Finset.mem_Ico.mp hi) (Finset.mem_Ico.mp hj) hij)
  have hd : Disjoint ((Finset.Ico 0 q).biUnion (symmA P q))
      ((Finset.Ico 0 q).biUnion (symmB P q)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx'
    exact Finset.disjoint_left.mp
      (symmAB_disjoint (Finset.mem_Ico.mp hi) (Finset.mem_Ico.mp hj)) hxi hxj
  simpa only [symmetric_core_coverage P q hq] using ha.union hb hd

/-- Complete the symmetric core with a singleton or an outer triple.
@isnad1 id=hasgood.3h3v.s6.9788a3b240f1 from=translated src=- shape=02eed4e6 vocab=5a374c8d
-/
theorem hasGood_symmetric_interval {P r : ℤ} {k : ℕ}
    (hp : P = (3 : ℤ)^k) (hr : 0 ≤ r) (hmod : r % 3 = 0 ∨ r % 3 = 1) :
    HasGood (Finset.Icc (P - r) (P + r)) := by
  have hq : 0 ≤ r / 3 := by omega
  have hc := hasGood_symmetric_core hp hq
  rcases hmod with hmod | hmod
  · have heq : r = 3 * (r / 3) := by omega
    have hs : HasGood ({P} : Finset ℤ) := by
      rw [hp]
      exact (goodBlock_singleton k).hasGood
    have hd : Disjoint ((Finset.Icc (P - 3*(r/3)) (P + 3*(r/3))).erase P)
        ({P} : Finset ℤ) := by simp
    have hu := hc.union hs hd
    convert hu using 1
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    omega
  · have heq : r = 3 * (r / 3) + 1 := by omega
    have hs : HasGood ({P-r, P, P+r} : Finset ℤ) := by
      apply GoodBlock.hasGood
      apply goodBlock_triple (by omega) (by omega) (by omega) (k := k + 1)
      rw [pow_succ, ← hp]
      ring
    have hd : Disjoint ((Finset.Icc (P - 3*(r/3)) (P + 3*(r/3))).erase P)
        ({P-r, P, P+r} : Finset ℤ) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      simp only [Finset.mem_erase, Finset.mem_Icc] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      omega
    have hu := hc.union hs hd
    convert hu using 1
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton]
    omega

/-- The lower noncritical step in the strong induction on the target interval.
@isnad1 id=hasgood.4h3v.s6.9292bce63635 from=translated src=- shape=236ebed7 vocab=5226683d
-/
theorem lower_symmetric_extension {P r k : ℕ} (hp : P = 3^k)
    (hPr : 2*r < P) (hmod : r % 3 = 0 ∨ r % 3 = 1)
    (hs : HasGood (interval (P-r-1))) : HasGood (interval (P+r)) := by
  have hp' : (P : ℤ) = (3 : ℤ)^k := by exact_mod_cast hp
  have hm' : (r : ℤ) % 3 = 0 ∨ (r : ℤ) % 3 = 1 := by omega
  have ht := hasGood_symmetric_interval hp' (by omega : 0 ≤ (r : ℤ)) hm'
  have hleft : ((P-r-1 : ℕ) : ℤ) + 1 = (P : ℤ) - (r : ℤ) := by omega
  have hright : ((P+r : ℕ) : ℤ) = (P : ℤ) + (r : ℤ) := by omega
  apply HasGood.append_interval (m := P-r-1) (by omega) hs
  simpa only [hleft, hright] using ht

/-- The upper complement-pair step in the strong induction.
@isnad1 id=hasgood.4h3v.s6.6847634d977c from=translated src=- shape=afe9ceac vocab=59c2f20b
-/
theorem upper_pair_extension {P n k : ℕ} (hp : P = 3^k)
    (hlower : 3*P < 2*n) (hupper : n < 3*P)
    (hs : HasGood (interval (3*P-n-1))) : HasGood (interval n) := by
  have hp' : (P : ℤ) = (3 : ℤ)^k := by exact_mod_cast hp
  apply complement_pair_extension (m := 3*P-n-1) (k := k+1) (by omega) ?_ hs
  rw [pow_succ, ← hp']
  omega

end

end GN
