import Tengoku.GnmLean.GN.Signed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace GN
noncomputable section

/-- The vertices occupied by a finite collection of pairs.-/
def pairEndpoints (ps : Finset (ℤ × ℤ)) : Finset ℤ :=
  ps.biUnion fun p => {p.1, p.2}

/-- Positive differences, before checking that the pairs are ordered.-/
def pairDifferences (ps : Finset (ℤ × ℤ)) : Finset ℤ :=
  ps.image fun p => p.2-p.1

/-- A certificate for a pairing with consecutive differences and one prescribed
unused position. The upper bound on the number of pairs, together with endpoint
coverage, forces each vertex to occur exactly once.-/
structure LangfordPairing (d k h : ℤ) (ps : Finset (ℤ × ℤ)) : Prop where
  defect_pos : 1 ≤ d
  order_nonempty : d ≤ k
  hole_mem : 1 ≤ h ∧ h ≤ 2*(k-d+1)+1
  endpoints : pairEndpoints ps = (Finset.Icc 1 (2*(k-d+1)+1)).erase h
  differences : pairDifferences ps = Finset.Icc d k
  card_le : ps.card ≤ (k-d+1).toNat

/-- A row of the affine tables: `(a+j,b+2j)`, for `0≤j≤n`.-/
def affinePairs (a b n : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 0 n).image fun j => (a+j,b+2*j)

/--
@isnad1 id=eq.0h2v.s5.9ff404a4e5a4 from=translated src=- shape=5e9465e7 vocab=44f97a6a
-/
@[simp] theorem pairEndpoints_union (ps qs : Finset (ℤ × ℤ)) :
    pairEndpoints (ps ∪ qs) = pairEndpoints ps ∪ pairEndpoints qs := by
  ext x
  simp [pairEndpoints]
  aesop

/--
@isnad1 id=eq.0h2v.s5.0237040fb8aa from=translated src=- shape=54609f4c vocab=31c5fc5a
-/
@[simp] theorem pairEndpoints_singleton (a b : ℤ) :
    pairEndpoints {(a,b)} = {a,b} := by
  simp [pairEndpoints]

/--
@isnad1 id=eq.0h2v.s5.1d9f7bcb5ea6 from=translated src=- shape=5e9465e7 vocab=95bd796f
-/
@[simp] theorem pairDifferences_union (ps qs : Finset (ℤ × ℤ)) :
    pairDifferences (ps ∪ qs) = pairDifferences ps ∪ pairDifferences qs := by
  exact Finset.image_union _ _

/--
@isnad1 id=eq.0h2v.s5.45e9da5b638e from=translated src=- shape=408fc4e2 vocab=b1179d7d
-/
@[simp] theorem pairDifferences_singleton (a b : ℤ) :
    pairDifferences {(a,b)} = {b-a} := by
  simp [pairDifferences]

/--
@isnad1 id=iff.0h4v.s6.df49c9aea831 from=translated src=- shape=269610db vocab=deb035ef
-/
theorem mem_pairEndpoints_affinePairs (a b n x : ℤ) :
    x ∈ pairEndpoints (affinePairs a b n) ↔
      (a ≤ x ∧ x ≤ a+n) ∨
      (b ≤ x ∧ x ≤ b+2*n ∧ (x-b)%2=0) := by
  simp only [pairEndpoints, affinePairs, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, ⟨j, hj, rfl⟩, hx⟩
    rcases hx with hx | hx <;> dsimp only at hx
    · left; omega
    · right; omega
  · rintro (hx | hx)
    · refine ⟨(a+(x-a),b+2*(x-a)), ⟨x-a, ?_, rfl⟩, Or.inl ?_⟩ <;> (try dsimp) <;> omega
    · refine ⟨(a+(x-b)/2,b+2*((x-b)/2)), ⟨(x-b)/2, ?_, rfl⟩, Or.inr ?_⟩ <;>
        (try dsimp) <;> omega

/--
@isnad1 id=iff.0h4v.s5.9871b2b985da from=translated src=- shape=09efa9d2 vocab=dce0777e
-/
theorem mem_pairDifferences_affinePairs (a b n x : ℤ) :
    x ∈ pairDifferences (affinePairs a b n) ↔ b-a ≤ x ∧ x ≤ b-a+n := by
  simp only [pairDifferences, affinePairs, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨p, ⟨j, hj, rfl⟩, hx⟩
    dsimp only at hx
    omega
  · intro hx
    refine ⟨(a+(x-(b-a)),b+2*(x-(b-a))), ⟨x-(b-a), ?_, rfl⟩, ?_⟩ <;>
      (try dsimp) <;> omega

/--
@isnad1 id=le.0h3v.s4.f14cb5ad1fd7 from=translated src=- shape=ac3243e4 vocab=a1041eda
-/
theorem card_affinePairs_le (a b n : ℤ) :
    (affinePairs a b n).card ≤ (n+1).toNat := by
  unfold affinePairs
  exact (Finset.card_image_le).trans_eq (by simp)

/--
@isnad1 id=le.2h4v.s6.b7909781a7c2 from=translated src=- shape=826e97df vocab=fc0b8c56
-/
theorem card_union_le_of_le {ps qs : Finset (ℤ × ℤ)} {m n : ℕ}
    (hp : ps.card ≤ m) (hq : qs.card ≤ n) : (ps ∪ qs).card ≤ m+n :=
  (Finset.card_union_le ps qs).trans (Nat.add_le_add hp hq)

/-- Pivot an affine row into a currently unused position `z`. Sorting the
pivoted pair as `(z,a+j)` preserves positive differences when `b=2a-z`.-/
def pivotAffinePairs (a b n h z : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 0 n).image fun j =>
    if b+2*j=h then (z,a+j) else (a+j,b+2*j)

/--
@isnad1 id=iff.0h6v.s7.d4e2a0efc370 from=translated src=- shape=2a8699f6 vocab=e07e5669
-/
theorem mem_pairEndpoints_pivotAffinePairs (a b n h z x : ℤ) :
    x ∈ pairEndpoints (pivotAffinePairs a b n h z) ↔
      (a ≤ x ∧ x ≤ a+n) ∨
      (b ≤ x ∧ x ≤ b+2*n ∧ (x-b)%2=0 ∧ x ≠ h) ∨
      (x=z ∧ b ≤ h ∧ h ≤ b+2*n ∧ (h-b)%2=0) := by
  simp only [pairEndpoints, pivotAffinePairs, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, ⟨j, hj, rfl⟩, hx⟩
    by_cases he : b+2*j=h
    · simp only [ite_eq_left he] at hx
      rcases hx with hx | hx <;> (try dsimp only at hx)
      · right; right; omega
      · left; omega
    · simp only [ite_eq_right he] at hx
      rcases hx with hx | hx <;> (try dsimp only at hx)
      · left; omega
      · right; left; omega
  · rintro (hx | hx | hx)
    · refine ⟨_, ⟨x-a, ?_, rfl⟩, ?_⟩
      · omega
      · split_ifs <;> simp only [Prod.fst, Prod.snd] <;> omega
    · refine ⟨_, ⟨(x-b)/2, ?_, rfl⟩, ?_⟩
      · omega
      · split_ifs <;> simp only [Prod.fst, Prod.snd] <;> omega
    · refine ⟨_, ⟨(h-b)/2, ?_, rfl⟩, ?_⟩
      · omega
      · split_ifs <;> simp only [Prod.fst, Prod.snd] <;> omega

/--
@isnad1 id=iff.1h6v.s6.aa5480a678b7 from=translated src=- shape=9b99d1fb vocab=da78ff1a
-/
theorem mem_pairDifferences_pivotAffinePairs (a b n h z x : ℤ)
    (hb : b=2*a-z) :
    x ∈ pairDifferences (pivotAffinePairs a b n h z) ↔
      b-a ≤ x ∧ x ≤ b-a+n := by
  simp only [pairDifferences, pivotAffinePairs, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨p, ⟨j, hj, rfl⟩, hx⟩
    split_ifs at hx <;> dsimp only at hx <;> omega
  · intro hx
    refine ⟨_, ⟨x-(b-a), ?_, rfl⟩, ?_⟩
    · omega
    · split_ifs <;> simp only [Prod.fst, Prod.snd] <;> omega

/--
@isnad1 id=le.0h5v.s5.ba823f1f96c7 from=translated src=- shape=7b5ea6be vocab=9f1c1de9
-/
theorem card_pivotAffinePairs_le (a b n h z : ℤ) :
    (pivotAffinePairs a b n h z).card ≤ (n+1).toNat := by
  unfold pivotAffinePairs
  exact (Finset.card_image_le).trans_eq (by simp)

/-- The pivot relation is incorporated in the parameters of a hinged row.-/
def hingedPairs (a z n h : ℤ) : Finset (ℤ × ℤ) :=
  pivotAffinePairs a (2*a-z) n h z

/--
@isnad1 id=iff.0h5v.s5.6dc4384e83ae from=translated src=- shape=232d32ce vocab=08c30574
-/
theorem mem_pairDifferences_hingedPairs (a z n h x : ℤ) :
    x ∈ pairDifferences (hingedPairs a z n h) ↔ a-z ≤ x ∧ x ≤ a-z+n := by
  rw [hingedPairs, mem_pairDifferences_pivotAffinePairs a (2*a-z) n h z x rfl]
  omega

/-- Reverse the positions of every pair, preserving their positive differences.-/
def reflectPairs (N : ℤ) (ps : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  ps.image fun p => (N+1-p.2,N+1-p.1)

/--
@isnad1 id=iff.0h3v.s5.d4beef418786 from=translated src=- shape=bf5f7aff vocab=4f4165d8
-/
theorem mem_pairEndpoints_reflectPairs (N : ℤ) (ps : Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ pairEndpoints (reflectPairs N ps) ↔ N+1-x ∈ pairEndpoints ps := by
  simp only [pairEndpoints, reflectPairs, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx⟩
    refine ⟨q,hq,?_⟩
    rcases hx with hx | hx <;> dsimp only at hx
    · right; omega
    · left; omega
  · rintro ⟨p,hp,hx⟩
    refine ⟨_,⟨p,hp,rfl⟩,?_⟩
    rcases hx with hx | hx
    · right; dsimp only; omega
    · left; dsimp only; omega

/--
@isnad1 id=eq.0h2v.s4.76f440ad8bd6 from=translated src=- shape=a44df95f vocab=1a4e2119
-/
theorem pairDifferences_reflectPairs (N : ℤ) (ps : Finset (ℤ × ℤ)) :
    pairDifferences (reflectPairs N ps) = pairDifferences ps := by
  unfold pairDifferences reflectPairs
  rw [Finset.image_image]
  congr 1
  funext p
  change (N+1-p.1)-(N+1-p.2)=p.2-p.1
  ring

/--
@isnad1 id=langford.1h4v.s6.6807e8cb6b8d from=translated src=- shape=c3ceaeb7 vocab=5bbe3ce0
-/
theorem LangfordPairing.reflect {d k h : ℤ} {ps : Finset (ℤ × ℤ)}
    (hp : LangfordPairing d k h ps) :
    LangfordPairing d k (2*(k-d+1)+2-h) (reflectPairs (2*(k-d+1)+1) ps) := by
  constructor
  · exact hp.defect_pos
  · exact hp.order_nonempty
  · have := hp.hole_mem; omega
  · ext x
    rw [mem_pairEndpoints_reflectPairs,hp.endpoints]
    simp only [Finset.mem_erase,Finset.mem_Icc]
    omega
  · rw [pairDifferences_reflectPairs,hp.differences]
  · exact (Finset.card_image_le).trans hp.card_le

end
end GN
