import Tengoku.NsP23.P23.Semigroup.NearlyGorenstein
import Tengoku.NsP23.P23.Monomial.PlainMonomialIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Additive tail sources in the genuine chosen-base kernel. Arbitrary
factorizations are used throughout; the degree map is not assumed injective. -/
namespace P23.Semigroup
noncomputable section
open scoped BigOperators
open FourGeneratedNumericalSemigroup P23.Monomial

variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

def TailInH (h : ℕ) : Prop := ∃ u : PlainExp, tailDegree D i u = h

def TailInK (h : ℕ) : Prop :=
  TailInH D i h ∧ ∃ γ : D.Gamma, h = D.n i + γ.1

def IsTailSource (h : ℕ) : Prop :=
  TailInK D i h ∧ ∀ j : Fin 3, ¬∃ k : ℕ, TailInK D i k ∧ h=D.tailGen i j+k

/--
@isnad1 id=tailinh.0h2v.s4.5f7853219d11 from=translated src=- shape=751db40f vocab=9c53aeee
-/
theorem tailInH_zero : TailInH D i 0 := ⟨0, tailDegree_zero D i⟩

/--
@isnad1 id=tailinh.0h3v.s4.61bc2ed0f596 from=translated src=- shape=351f5eba vocab=be86a3f8
-/
theorem tailInH_tailGen (j : Fin 3) : TailInH D i (D.tailGen i j) :=
  ⟨Finsupp.single j 1, by simp⟩

/--
@isnad1 id=tailinh.2h4v.s5.f6bf14f08b6f from=translated src=- shape=2c53b180 vocab=bd699e9d
-/
theorem tailInH_add {h r : ℕ} (hh : TailInH D i h) (hr : TailInH D i r) :
    TailInH D i (h+r) := by
  obtain ⟨u,hu⟩ := hh
  obtain ⟨v,hv⟩ := hr
  exact ⟨u+v, by rw [tailDegree_add,hu,hv]⟩

/--
@isnad1 id=not.0h2v.s4.f066211e59c8 from=translated src=- shape=de774b71 vocab=44fe559f
-/
theorem not_tailInH_base : ¬TailInH D i (D.n i) := by
  rintro ⟨u,hu⟩
  exact D.minimal i (extendTailExponent i u) (extendTailExponent_base i u)
    ((weightedDegree_extendTailExponent D i u).trans hu)

/--
@isnad1 id=lt.1h3v.s5.65e6c6cb0fae from=translated src=- shape=6623e98f vocab=0a4dc5f4
-/
theorem tailDegree_pos_of_ne_zero (u : PlainExp) (hu : u≠0) :
    0<tailDegree D i u := by
  obtain ⟨j,hj⟩ := Finsupp.ne_iff.mp hu
  have hp : 0<u j := Nat.pos_of_ne_zero hj
  have hterm : u j * D.tailGen i j ≤ tailDegree D i u := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact lt_of_lt_of_le (Nat.mul_pos hp (D.tailGen_positive i j)) hterm

/--
@isnad1 id=tailink.2h4v.s5.6dcf7878b40c from=translated src=- shape=9a7ea607 vocab=53c99229
-/
theorem tailInK_add_tailInH {h r : ℕ} (hh : TailInK D i h) (hr : TailInH D i r) :
    TailInK D i (h+r) := by
  obtain ⟨hh,γ,hγ⟩ := hh
  obtain ⟨u,hu⟩ := hr
  refine ⟨tailInH_add D i hh ⟨u,hu⟩, γ+tailDegreeGamma D i u, ?_⟩
  change h+r=D.n i+(γ.1+tailDegree D i u)
  rw [hγ,hu]
  omega

/--
@isnad1 id=iff.0h4v.s6.409852e79f42 from=translated src=- shape=9d0c0e90 vocab=67709025
-/
theorem truncatedAperyMonomial_eq_zero_iff_not_isApery
    {k : Type*} [Field k] (s : D.Gamma) :
    truncatedAperyMonomial (k := k) D i s=0 ↔ ¬D.IsApery i s := by
  classical
  by_cases hs : D.IsApery i s
  · constructor
    · intro hz
      have hc := congrArg (fun x : AperyArtin k D i => x.coeff ⟨s,hs⟩) hz
      simp [truncatedAperyMonomial,hs] at hc
    · intro hn
      exact False.elim (hn hs)
  · simp [truncatedAperyMonomial,hs]

/--
@isnad1 id=iff.0h4v.s9.e59aea6048e3 from=translated src=- shape=8cbccdb4 vocab=ea89da8e
-/
theorem tail_monomial_mem_chosenBaseDefiningIdeal_iff
    {k : Type*} [Field k] (u : PlainExp) :
    MvPolynomial.monomial u (1 : k) ∈ chosenBaseDefiningIdeal (k := k) D i ↔
      TailInK D i (tailDegree D i u) := by
  classical
  change tailPolyToChosenBase (k := k) D i (MvPolynomial.monomial u 1)=0 ↔ _
  have he := tailPolyToChosenBase_monomial (k := k) D i u 1
  simp only [one_smul] at he
  have hz : tailPolyToChosenBase (k := k) D i (MvPolynomial.monomial u 1)=0 ↔
      truncatedAperyMonomial (k := k) D i (tailDegreeGamma D i u)=0 := by
    constructor
    · intro h
      rw [←he,h,map_zero]
    · intro h
      apply (chosenBaseEquivApery (k := k) D i).injective
      rw [he,h,map_zero]
  rw [hz,truncatedAperyMonomial_eq_zero_iff_not_isApery]
  constructor
  · intro hn
    obtain ⟨γ,hγ⟩ := not_not.mp hn
    refine ⟨⟨u,rfl⟩,γ,?_⟩
    exact congrArg Subtype.val hγ
  · rintro ⟨_,γ,hγ⟩ ha
    apply ha
    exact ⟨γ,Subtype.ext hγ⟩

/--
@isnad1 id=iff.0h3v.s5.5a77ab8bfc56 from=translated src=- shape=136a8816 vocab=f219864d
-/
theorem isTailSource_iff_no_nonzero_tail_predecessor (h : ℕ) :
    IsTailSource D i h ↔ TailInK D i h ∧
      ¬∃ k r : ℕ, TailInK D i k ∧ TailInH D i r ∧ r≠0 ∧ h=k+r := by
  classical
  constructor
  · rintro ⟨hh,hmin⟩
    refine ⟨hh,?_⟩
    rintro ⟨k,r,hk,⟨u,hu⟩,hr,he⟩
    have hune : u≠0 := by intro hz; subst u; simp at hu; exact hr hu.symm
    obtain ⟨j,hj⟩ := Finsupp.ne_iff.mp hune
    have hjpos : 0<u j := Nat.pos_of_ne_zero hj
    let v : PlainExp := u-Finsupp.single j 1
    have huv : u=Finsupp.single j 1+v := by
      ext l
      by_cases hl : l=j
      · subst l
        simp only [Finsupp.add_apply,Finsupp.single_eq_same,v,Finsupp.tsub_apply]
        exact (Nat.add_sub_of_le hjpos).symm
      · simp [v,Finsupp.single_apply,hl]
    have hrdeg : r=D.tailGen i j+tailDegree D i v := by
      rw [←hu,huv,tailDegree_add,tailDegree_single,one_mul]
    apply hmin j
    exact ⟨k+tailDegree D i v,
      tailInK_add_tailInH D i hk ⟨v,rfl⟩,by omega⟩
  · rintro ⟨hh,hmin⟩
    refine ⟨hh,?_⟩
    rintro j ⟨k,hk,he⟩
    apply hmin
    exact ⟨k,D.tailGen i j,hk,tailInH_tailGen D i j,
      Nat.ne_of_gt (D.tailGen_positive i j),by omega⟩

/-- Minimal original generators have no predecessor by another generator.
@isnad1 id=ne.1h4v.s6.27380e7b91fb from=translated src=- shape=87a710d7 vocab=97f06581
-/
theorem generator_not_add_other (j l : Fin 4) (hjl : j≠l) (γ : D.Gamma) :
    D.n j≠D.n l+γ.1 := by
  classical
  intro he
  obtain ⟨u,hu⟩ := (D.mem_Gamma_iff γ.1).mp γ.2
  have hut : u j=0 := by
    by_contra hn
    have hone : 1≤u j := Nat.one_le_iff_ne_zero.mpr hn
    have hterm : u j*D.n j≤D.weightedDegree u := by
      apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hmul : D.n j≤u j*D.n j := by
      simpa only [one_mul] using Nat.mul_le_mul_right (D.n j) hone
    have hp := D.positive l
    omega
  let v := generatorFactorization l+u
  have hvzero : v j=0 := by
    simp [v,generatorFactorization,Finsupp.single_apply,hjl.symm,hut]
  have hvdeg : D.weightedDegree v=D.n j := by
    change weightedDegreeOf D.n (generatorFactorization l+u)=D.n j
    rw [weightedDegreeOf_add]
    change D.weightedDegree (generatorFactorization l)+D.weightedDegree u=D.n j
    rw [D.weightedDegree_generatorFactorization,hu]
    exact he.symm
  exact D.minimal j v hvzero hvdeg

def aperySocleDegree (s : D.AperySocleIndex i) : ℕ := s.1.1.1

structure TailSocleTopPattern (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  top : ℕ
  byTail : Fin 3 ≃ D.AperySocleIndex i
  top_eq : ∀ j, top=aperySocleDegree D i (byTail j)+D.tailGen i j

namespace TailSocleTopPattern
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4} (P : TailSocleTopPattern D i)

/--
@isnad1 id=injectiv.0h3v.s6.182ad5f75802 from=translated src=- shape=09b79dd5 vocab=51ad72e3
-/
theorem socleDegree_injective :
    Function.Injective (fun j => aperySocleDegree D i (P.byTail j)) := by
  intro j l h
  change aperySocleDegree D i (P.byTail j)=aperySocleDegree D i (P.byTail l) at h
  apply D.tailGen_injective i
  have hj := P.top_eq j
  have hl := P.top_eq l
  omega

/--
@isnad1 id=injectiv.0h3v.s7.1e96690abab4 from=translated src=- shape=e010ac15 vocab=41cb8e7e
-/
theorem pseudoFrobenius_injective : Function.Injective
    (fun j => (D.pseudoFrobeniusEquivAperySocle i).symm (P.byTail j)) :=
  (D.pseudoFrobeniusEquivAperySocle i).symm.injective.comp P.byTail.injective

/--
@isnad1 id=ne.0h4v.s5.738927f95ceb from=translated src=- shape=a8a0800d vocab=d936c829
-/
theorem top_ne_base_add_tail (j : Fin 3) : P.top≠D.n i+D.tailGen i j := by
  intro he
  have hj := P.top_eq j
  have hd : aperySocleDegree D i (P.byTail j)=D.n i := by omega
  have hs : (P.byTail j).1.1=D.base i := Subtype.ext hd
  exact D.base_not_isApery i (hs ▸ (P.byTail j).1.2)

end TailSocleTopPattern

/--
@isnad1 id=eq.0h3v.s6.0e7f60c0d81e from=translated src=- shape=42162c3e vocab=d963fedb
-/
theorem pf_inverse_degree (s : D.AperySocleIndex i) :
    ((D.pseudoFrobeniusEquivAperySocle i).symm s).1 =
      (aperySocleDegree D i s : ℤ)-(D.n i : ℤ) := rfl

/--
@isnad1 id=ex.1h3v.s7.82e337dff31f from=translated src=- shape=ea5d6da5 vocab=2b3cbccc
-/
theorem exists_selected_tail_ng_relations (P : TailSocleTopPattern D i)
    (hn : SemigroupNearlyGorenstein D) :
    ∃ s : Fin 3, ∀ t : Fin 3, t≠s → ∃ γ : D.Gamma,
      D.n i+D.tailGen i t=D.tailGen i s+γ.1 := by
  obtain ⟨f,hf⟩ := exists_base_ngWitness D hn i
  let s := P.byTail.symm (D.pseudoFrobeniusEquivAperySocle i f)
  have hfs : (D.pseudoFrobeniusEquivAperySocle i).symm (P.byTail s)=f := by
    simp [s]
  have hfval : f.1=(aperySocleDegree D i (P.byTail s) : ℤ)-(D.n i : ℤ) := by
    rw [←hfs,pf_inverse_degree]
  refine ⟨s,?_⟩
  intro t _
  let g := (D.pseudoFrobeniusEquivAperySocle i).symm (P.byTail t)
  obtain ⟨γ,hγ⟩ := hf g
  have hgval : g.1=(aperySocleDegree D i (P.byTail t) : ℤ)-(D.n i : ℤ) :=
    pf_inverse_degree D i (P.byTail t)
  have hstop := P.top_eq s
  have httop := P.top_eq t
  change (γ.1 : ℤ)=(D.n i : ℤ)+f.1-g.1 at hγ
  refine ⟨γ,?_⟩
  omega

/-- The relation witness has no base predecessor, so every factorization is
base-free by the frozen generic Apéry factorization API.
@isnad1 id=isapery.2h5v.s6.4e4e7dfab92a from=translated src=- shape=d39c3312 vocab=18a0158f
-/
theorem gamma_isApery_of_ng_tail_relation (s t : Fin 3) (hst : s≠t)
    (γ : D.Gamma) (he : D.n i+D.tailGen i t=D.tailGen i s+γ.1) :
    D.IsApery i γ := by
  rintro ⟨δ,hδ⟩
  have hv := congrArg Subtype.val hδ
  change γ.1=D.n i+δ.1 at hv
  have hbad : D.tailGen i t=D.tailGen i s+δ.1 := by omega
  exact generator_not_add_other D (D.tailIndex i t) (D.tailIndex i s)
    (fun h => hst ((D.tailIndex_injective i h).symm)) δ hbad

/--
@isnad1 id=eq.3h6v.s7.aef6634755ac from=translated src=- shape=98ce35a4 vocab=9e47d0db
-/
theorem ng_tail_factorization_base_zero (s t : Fin 3) (hst : s≠t)
    (γ : D.Gamma) (he : D.n i+D.tailGen i t=D.tailGen i s+γ.1)
    (u : Fin 4 →₀ ℕ) (hu : D.weightedDegree u=γ.1) : u i=0 :=
  D.apery_factorization_base_eq_zero i
    (gamma_isApery_of_ng_tail_relation D i s t hst γ he) u hu

/--
@isnad1 id=ex.2h5v.s7.e763d1f5fd03 from=translated src=- shape=6a0c976c vocab=fa339802
-/
theorem exists_tail_factorization_containing_selected (s t : Fin 3) (hst : s≠t)
    (γ : D.Gamma) (he : D.n i+D.tailGen i t=D.tailGen i s+γ.1) :
    ∃ u : PlainExp, tailDegree D i u=D.n i+D.tailGen i t ∧ 0<u s := by
  obtain ⟨v,hv⟩ := exists_tailExponent_of_isApery D i
    (gamma_isApery_of_ng_tail_relation D i s t hst γ he)
  refine ⟨Finsupp.single s 1+v,?_,?_⟩
  · rw [tailDegree_add,tailDegree_single,one_mul,hv]
    exact he.symm
  · simp

/--
@isnad1 id=istailso.2h5v.s7.27361fd8d49e from=translated src=- shape=9c6363cb vocab=5cffd022
-/
theorem source_of_ng_tail_relation (s t : Fin 3) (hst : s≠t)
    (γ : D.Gamma) (he : D.n i+D.tailGen i t=D.tailGen i s+γ.1) :
    IsTailSource D i (D.n i+D.tailGen i t) := by
  obtain ⟨u,hu,_⟩ := exists_tail_factorization_containing_selected D i s t hst γ he
  refine ⟨⟨⟨u,hu⟩,D.tail i t,rfl⟩,?_⟩
  rintro j ⟨k,⟨hk,δ,hδ⟩,hj⟩
  have hbad : D.tailGen i t=D.tailGen i j+δ.1 := by omega
  by_cases htj : t=j
  · subst j
    have hkq : k=D.n i := by omega
    exact not_tailInH_base D i (hkq ▸ hk)
  · exact generator_not_add_other D (D.tailIndex i t) (D.tailIndex i j)
      (fun h => htj (D.tailIndex_injective i h)) δ hbad

structure TwoTailSources (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  selected : Fin 3
  first : Fin 3
  second : Fin 3
  first_ne_selected : first≠selected
  second_ne_selected : second≠selected
  first_ne_second : first≠second
  first_source : IsTailSource D i (D.n i+D.tailGen i first)
  second_source : IsTailSource D i (D.n i+D.tailGen i second)
  first_factorization : PlainExp
  second_factorization : PlainExp
  first_degree : tailDegree D i first_factorization=D.n i+D.tailGen i first
  second_degree : tailDegree D i second_factorization=D.n i+D.tailGen i second
  first_contains_selected : 0<first_factorization selected
  second_contains_selected : 0<second_factorization selected
  degrees_ne : D.n i+D.tailGen i first≠D.n i+D.tailGen i second

/--
@isnad1 id=nonempty.1h3v.s4.8a3f93a83962 from=translated src=- shape=4e3017eb vocab=baae40a4
-/
theorem exists_two_tail_sources (P : TailSocleTopPattern D i)
    (hn : SemigroupNearlyGorenstein D) : Nonempty (TwoTailSources D i) := by
  obtain ⟨s,hs⟩ := exists_selected_tail_ng_relations D i P hn
  have hother : ∃ a b : Fin 3, a≠s ∧ b≠s ∧ a≠b := by
    fin_cases s
    · exact ⟨1,2,by norm_num [Fin.ext_iff],by norm_num [Fin.ext_iff],
        by norm_num [Fin.ext_iff]⟩
    · exact ⟨0,2,by norm_num [Fin.ext_iff],by norm_num [Fin.ext_iff],
        by norm_num [Fin.ext_iff]⟩
    · exact ⟨0,1,by norm_num [Fin.ext_iff],by norm_num [Fin.ext_iff],
        by norm_num [Fin.ext_iff]⟩
  obtain ⟨a,b,has,hbs,hab⟩ := hother
  obtain ⟨γa,ha⟩ := hs a has
  obtain ⟨γb,hb⟩ := hs b hbs
  obtain ⟨ua,hua,husa⟩ :=
    exists_tail_factorization_containing_selected D i s a has.symm γa ha
  obtain ⟨ub,hub,husb⟩ :=
    exists_tail_factorization_containing_selected D i s b hbs.symm γb hb
  refine ⟨{
    selected := s, first := a, second := b
    first_ne_selected := has, second_ne_selected := hbs, first_ne_second := hab
    first_source := source_of_ng_tail_relation D i s a has.symm γa ha
    second_source := source_of_ng_tail_relation D i s b hbs.symm γb hb
    first_factorization := ua, second_factorization := ub
    first_degree := hua, second_degree := hub
    first_contains_selected := husa, second_contains_selected := husb
    degrees_ne := ?_ }⟩
  intro h
  apply hab
  apply D.tailGen_injective i
  omega

/-- Source => displayed monomial. No converse and no uniqueness of arbitrary
tail factorizations is asserted. Minimality of the display is not needed.
@isnad1 id=mem.4h5v.s9.6ef19dac00ab from=translated src=- shape=18078d4f vocab=5869195d
-/
theorem source_factorization_eq_displayed_monomial (G : Finset PlainExp)
    (hI : plainMonomialIdeal ℚ G=chosenBaseDefiningIdeal (k := ℚ) D i)
    {d : ℕ} (hs : IsTailSource D i d) (u : PlainExp) (hu : tailDegree D i u=d)
    (hm : MvPolynomial.monomial u (1 : ℚ) ∈ plainMonomialIdeal ℚ G) : u∈G := by
  classical
  obtain ⟨g,hg,hgu⟩ := (monomial_mem_plainMonomialIdeal_iff ℚ G u).mp hm
  by_cases he : g=u
  · simpa [he] using hg
  · let w : PlainExp := u-g
    have huw : u=g+w := by
      ext j
      simp only [Finsupp.add_apply,Finsupp.tsub_apply,w]
      exact (Nat.add_sub_of_le (hgu j)).symm
    have hw : w≠0 := by
      intro hz
      apply he
      simpa [hz] using huw.symm
    have hgm : MvPolynomial.monomial g (1 : ℚ) ∈ plainMonomialIdeal ℚ G :=
      (monomial_mem_plainMonomialIdeal_iff ℚ G g).mpr ⟨g,hg,plainDivides_refl g⟩
    have hgK : TailInK D i (tailDegree D i g) :=
      (tail_monomial_mem_chosenBaseDefiningIdeal_iff D i g).mp (hI ▸ hgm)
    have hfull := (isTailSource_iff_no_nonzero_tail_predecessor D i d).mp hs
    apply False.elim
    apply hfull.2
    refine ⟨tailDegree D i g,tailDegree D i w,hgK,⟨w,rfl⟩,
      Nat.ne_of_gt (tailDegree_pos_of_ne_zero D i w hw),?_⟩
    rw [←hu,huw,tailDegree_add]

end
end P23.Semigroup
