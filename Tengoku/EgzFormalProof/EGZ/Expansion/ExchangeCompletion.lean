import Tengoku.EgzFormalProof.EGZ.Expansion.Subweights

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Completing a family of disjoint exchanges to a zero sum

A family of exchanges which covers a quotient fibre can be combined with
prescribed filler counts. Disjointness of multiset positions is expressed by
a pointwise capacity bound on all reserved multiplicities.
-/

open scoped BigOperators

namespace EGZ.Expansion

noncomputable def vectorSum {G : Type*} [AddCommMonoid G] [Fintype G]
    (u : G → ℕ) : G := ∑ v, u v • v

/--
@isnad1 id=eq.0h3v.s6.38ee1d514aa7 from=translated src=- shape=69b6a18d vocab=4f35bd5c
-/
theorem vectorSum_add {G : Type*} [AddCommMonoid G] [Fintype G]
    (u w : G → ℕ) : vectorSum (u + w) = vectorSum u + vectorSum w := by
  simp [vectorSum, add_nsmul, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h3v.s5.0c59a0cb2123 from=translated src=- shape=393f5ab0 vocab=ecdf4707
-/
theorem vectorSum_sum {I G : Type*} [Fintype I] [Fintype G] [AddCommMonoid G]
    (u : I → G → ℕ) : vectorSum (∑ i, u i) = ∑ i, vectorSum (u i) := by
  simp only [vectorSum, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/--
@isnad1 id=eq.0h4v.s7.205c571b8898 from=translated src=- shape=285e617b vocab=16506a95
-/
theorem map_vectorSum {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    [Fintype G] [Fintype H] (π : G →+ H) (u : G → ℕ) :
    π (vectorSum u) = vectorSum (pushWeight π u) := by
  rw [vectorSum, map_sum]
  simp only [map_nsmul]
  exact (sum_pushWeight π u id).symm

noncomputable def choiceWeight {I G : Type*} [Fintype I]
    (left right : I → G → ℕ) (choice : I → Bool) : G → ℕ :=
  ∑ i, if choice i then left i else right i

/--
@isnad1 id=le.0h5v.s6.c8ad40aae3fc from=translated src=- shape=42526043 vocab=8e8362b4
-/
theorem choiceWeight_le {I G : Type*} [Fintype I]
    (left right : I → G → ℕ) (choice : I → Bool) :
    choiceWeight left right choice ≤ (∑ i, left i) + ∑ i, right i := by
  intro v
  simp only [choiceWeight, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases choice i <;> simp

/--
@isnad1 id=eq.1h5v.s6.8369fca03b14 from=translated src=- shape=5a8450b5 vocab=8c878273
-/
theorem natMass_choiceWeight {I G : Type*} [Fintype I] [Fintype G]
    (left right : I → G → ℕ) (choice : I → Bool)
    (h : ∀ i, natMass (left i) = natMass (right i)) :
    natMass (choiceWeight left right choice) = natMass (∑ i, left i) := by
  simp only [natMass, choiceWeight, Finset.sum_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hc : choice i
  · simpa only [hc, Bool.false_eq_true, ↓reduceIte, natMass] using (h i).symm
  · simp only [↓reduceIte]

/--
@isnad1 id=eq.0h5v.s7.8541feeb0d4c from=translated src=- shape=2fdb520a vocab=0c72aeb7
-/
theorem vectorSum_choiceWeight {I G : Type*} [Fintype I] [Fintype G] [AddCommGroup G]
    (left right : I → G → ℕ) (choice : I → Bool) :
    vectorSum (choiceWeight left right choice) = vectorSum (∑ i, right i) +
      ∑ i, if choice i then vectorSum (left i) - vectorSum (right i) else 0 := by
  simp only [vectorSum, choiceWeight, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => lhs; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases choice i <;> simp

/-- A full quotient fibre of possible exchange sums gives a zero sum once
the remaining prescribed counts fit outside all reserved positions.
@isnad1 id=ex.6h8v.s9.e1f4d2378d12 from=translated src=- shape=24e6c73b vocab=aec52a52
-/
theorem complete_exchange_family {G H I : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H] [Fintype I]
    (π : G →+ H) (w : G → ℕ) (a : H → ℕ) (left right : I → G → ℕ)
    (hcapacity : (∑ i, left i) + ∑ i, right i ≤ w)
    (hmass : ∀ i, natMass (left i) = natMass (right i))
    (hlo : pushWeight π (∑ i, left i) ≤ a)
    (hhi : a + pushWeight π (∑ i, right i) ≤ pushWeight π w)
    (hzero : vectorSum a = 0)
    (hcover : ∀ v : G, π v = π (vectorSum (∑ i, left i)) →
      ∃ c : I → Bool, vectorSum (choiceWeight left right c) = v) :
    ∃ u : G → ℕ, u ≤ w ∧ natMass u = natMass a ∧ vectorSum u = 0 := by
  classical
  let L : G → ℕ := ∑ i, left i
  let R : G → ℕ := ∑ i, right i
  let rest := w - (L + R)
  let b := a - pushWeight π L
  have hb : b ≤ pushWeight π rest := by
    rw [show pushWeight π rest = pushWeight π w -
        (pushWeight π L + pushWeight π R) by
      dsimp only [rest]
      rw [pushWeight_sub π hcapacity, pushWeight_add]]
    intro q
    have h₁ := hlo q
    have h₂ := hhi q
    change a q - pushWeight π L q ≤
      pushWeight π w q - (pushWeight π L q + pushWeight π R q)
    change pushWeight π L q ≤ a q at h₁
    change a q + pushWeight π R q ≤ pushWeight π w q at h₂
    omega
  obtain ⟨filler, hfiller, hcounts⟩ := exists_subweight_pushWeight π rest b hb
  have hadd : pushWeight π (filler + L) = a := by
    rw [pushWeight_add, hcounts]
    funext q
    exact Nat.sub_add_cancel (hlo q)
  have hmass_total : natMass filler + natMass L = natMass a := by
    have h := congrArg natMass hadd
    rw [natMass_pushWeight] at h
    simpa only [natMass, Pi.add_apply, Finset.sum_add_distrib] using h
  have hsum_total : π (vectorSum filler) + π (vectorSum L) = 0 := by
    rw [← map_add, ← vectorSum_add, map_vectorSum, hadd]
    exact hzero
  have htarget : π (-vectorSum filler) = π (vectorSum L) := by
    rw [map_neg]
    exact neg_eq_iff_add_eq_zero.mpr hsum_total
  obtain ⟨choice, hchoice⟩ := hcover (-vectorSum filler) htarget
  refine ⟨choiceWeight left right choice + filler, ?_, ?_, ?_⟩
  · intro v
    have hc := choiceWeight_le left right choice v
    have hf := hfiller v
    have hw := hcapacity v
    change filler v ≤ w v - (L v + R v) at hf
    change L v + R v ≤ w v at hw
    change choiceWeight left right choice v ≤ L v + R v at hc
    change choiceWeight left right choice v + filler v ≤ w v
    omega
  · have hc := natMass_choiceWeight left right choice hmass
    change natMass (choiceWeight left right choice) = natMass L at hc
    simpa only [natMass, Pi.add_apply, Finset.sum_add_distrib, add_comm] using
      (congrArg (fun n ↦ n + natMass filler) hc).trans (by omega :
        natMass L + natMass filler = natMass a)
  · rw [vectorSum_add, hchoice, neg_add_cancel]

/-- The equivalent form used by translation growth: binary sums of the
exchange differences cover the quotient kernel.
@isnad1 id=ex.7h8v.s9.0415dac5798f from=translated src=- shape=c692d9c4 vocab=4298063f
-/
theorem complete_exchange_family_of_differences {G H I : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H] [Fintype I]
    (π : G →+ H) (w : G → ℕ) (a : H → ℕ) (left right : I → G → ℕ)
    (hcapacity : (∑ i, left i) + ∑ i, right i ≤ w)
    (hmass : ∀ i, natMass (left i) = natMass (right i))
    (hquotient : ∀ i, π (vectorSum (left i)) = π (vectorSum (right i)))
    (hlo : pushWeight π (∑ i, left i) ≤ a)
    (hhi : a + pushWeight π (∑ i, right i) ≤ pushWeight π w)
    (hzero : vectorSum a = 0)
    (hcover : ∀ v : G, π v = 0 → ∃ c : I → Bool,
      (∑ i, if c i then vectorSum (left i) - vectorSum (right i) else 0) = v) :
    ∃ u : G → ℕ, u ≤ w ∧ natMass u = natMass a ∧ vectorSum u = 0 := by
  apply complete_exchange_family π w a left right hcapacity hmass hlo hhi hzero
  intro v hv
  have hbase : π (vectorSum (∑ i, right i)) = π (vectorSum (∑ i, left i)) := by
    simp only [vectorSum_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (hquotient i).symm
  obtain ⟨c, hc⟩ := hcover (v - vectorSum (∑ i, right i)) (by rw [map_sub, hbase, hv, sub_self])
  refine ⟨c, ?_⟩
  rw [vectorSum_choiceWeight, hc]
  abel

end EGZ.Expansion
