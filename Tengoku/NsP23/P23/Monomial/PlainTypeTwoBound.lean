import Tengoku.NsP23.P23.Monomial.PlainSmallPresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Monomial
noncomputable section
open Classical

def plainPairAxisCap (p q : PlainExp) (i : Fin 3) : PlainExp :=
  Finsupp.single i (max (p i) (q i) + 1)

def plainPairCross (p q : PlainExp) (ij : Fin 3 × Fin 3) : PlainExp :=
  Finsupp.single ij.1 (p ij.1 + 1) + Finsupp.single ij.2 (q ij.2 + 1)

def plainPairOppositeDirections (p q : PlainExp) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter (fun ij => p ij.1 < q ij.1 ∧ q ij.2 < p ij.2)

/--
@isnad1 id=le.0h2v.s4.8fa2ac6ce36a from=translated src=- shape=55235272 vocab=ea40137a
-/
theorem plainPair_opposite_card_le_two (p q : PlainExp) :
    (plainPairOppositeDirections p q).card ≤ 2 := by
  let P := Finset.univ.filter (fun i : Fin 3 => p i < q i)
  let N := Finset.univ.filter (fun i : Fin 3 => q i < p i)
  have he : plainPairOppositeDirections p q = P ×ˢ N := by
    ext ij; simp [plainPairOppositeDirections,P,N]
  have hd : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro i hp hn
    simp only [P,N,Finset.mem_filter,Finset.mem_univ,true_and] at hp hn
    omega
  have hu : P.card + N.card ≤ 3 := by
    rw [← Finset.card_union_of_disjoint hd]
    have hh := Finset.card_le_card (Finset.subset_univ (P ∪ N))
    simpa using hh
  rw [he,Finset.card_product]
  have hp : P.card=0 ∨ P.card=1 ∨ P.card=2 ∨ P.card=3 := by omega
  rcases hp with hp | hp | hp | hp <;> rw [hp] <;> simp_all <;> omega

private theorem plainPair_killed_eq_of_border {p q m w : PlainExp}
    (hm : m ∈ plainBorderFinset {p,q}) (hw : plainDivides w m)
    (hk : w ∉ plainStandardSet {p,q}) : m=w := by
  have hh := (plain_border_iff_minimalKilled {p,q} m).mp hm
  by_contra hn
  exact hk (hh.2 w hw (Ne.symm hn))

/--
@isnad1 id=le.0h2v.s7.316700b33186 from=translated src=- shape=d1de2cf9 vocab=5e305724
-/
theorem plainPair_border_subset (p q : PlainExp) :
    plainBorderFinset {p,q} ⊆
      (Finset.univ.image (plainPairAxisCap p q)) ∪
      ((plainPairOppositeDirections p q).image (plainPairCross p q)) := by
  intro m hm
  have hk := ((mem_plainBorderFinset_iff {p,q} m).mp hm).1
  have hnp : ¬plainDivides m p := fun h => hk ⟨p,by simp,h⟩
  have hnq : ¬plainDivides m q := fun h => hk ⟨q,by simp,h⟩
  simp only [plainDivides,not_forall] at hnp hnq
  obtain ⟨i,hi⟩ := hnp
  obtain ⟨j,hj⟩ := hnq
  have hi' : p i < m i := by omega
  have hj' : q j < m j := by omega
  have cap (k : Fin 3) (hk : max (p k) (q k) < m k) :
      m ∈ Finset.univ.image (plainPairAxisCap p q) := by
    have hd : plainDivides (plainPairAxisCap p q k) m := by
      intro l
      by_cases he : k=l
      · subst l; simp [plainPairAxisCap]; omega
      · simp [plainPairAxisCap,Finsupp.single_apply,he]
    have hz : plainPairAxisCap p q k ∉ plainStandardSet {p,q} := by
      rintro ⟨r,hr,hd⟩
      have hh := hd k
      simp only [Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> simp [plainPairAxisCap] at hh <;> omega
    have he := plainPair_killed_eq_of_border hm hd hz
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ k,he.symm⟩
  by_cases hpi : p i < q i
  · by_cases hqj : q j < p j
    · have hij : i ≠ j := by intro he; subst j; omega
      have hd : plainDivides (plainPairCross p q (i,j)) m := by
        intro l
        by_cases hil : i=l <;> by_cases hjl : j=l <;>
          simp [plainPairCross,Finsupp.single_apply,hil,hjl] <;> subst_vars <;> omega
      have hz : plainPairCross p q (i,j) ∉ plainStandardSet {p,q} := by
        rintro ⟨r,hr,hd⟩
        simp only [Finset.mem_insert,Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · have hh := hd i; simp [plainPairCross,Finsupp.single_apply,hij,Ne.symm hij] at hh
        · have hh := hd j; simp [plainPairCross,Finsupp.single_apply,hij,Ne.symm hij] at hh
      have he := plainPair_killed_eq_of_border hm hd hz
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(i,j),by simp [plainPairOppositeDirections,hpi,hqj],he.symm⟩
    · apply Finset.mem_union_left
      apply cap j
      simp only [max_lt_iff]; omega
  · apply Finset.mem_union_left
    apply cap i
    simp only [max_lt_iff]; omega

/--
@isnad1 id=le.0h2v.s5.ea8061fa41b3 from=translated src=- shape=41dc0d48 vocab=af49c37c
-/
theorem plain_pair_border_card_le_five (p q : PlainExp) :
    (plainBorderFinset {p,q}).card ≤ 5 := by
  have h := Finset.card_le_card (plainPair_border_subset p q)
  have hu := Finset.card_union_le
    (Finset.univ.image (plainPairAxisCap p q))
    ((plainPairOppositeDirections p q).image (plainPairCross p q))
  have ha := Finset.card_image_le (f := plainPairAxisCap p q) (s := Finset.univ)
  have hc := Finset.card_image_le (f := plainPairCross p q)
    (s := plainPairOppositeDirections p q)
  have ho := plainPair_opposite_card_le_two p q
  have hu3 : (Finset.univ : Finset (Fin 3)).card=3 := by simp
  omega

/--
@isnad1 id=le.3h1v.s5.8994bf66ce14 from=translated src=- shape=d724c1ac vocab=470e4002
-/
theorem plain_type_two_border_card_le_five (R : Finset PlainExp)
    (_ha : PlainRootAntichain R) (h2 : R.card=2) (_hv : PlainVariablesSurvive R) :
    (plainBorderFinset R).card ≤ 5 := by
  obtain ⟨p,q,_,rfl⟩ := Finset.card_eq_two.mp h2
  exact plain_pair_border_card_le_five p q

end
end P23.Monomial
