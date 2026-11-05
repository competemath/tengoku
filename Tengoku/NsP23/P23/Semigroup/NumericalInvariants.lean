import Tengoku.NsP23.P23.Semigroup.PseudoFrobenius
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Semigroup.FourGeneratedNumericalSemigroup
noncomputable section
open scoped BigOperators
variable (D : FourGeneratedNumericalSemigroup)

/--
@isnad1 id=ne.0h2v.s4.ee14e9abe2e1 from=translated src=- shape=360a1ae1 vocab=22e7753a
-/
theorem generator_ne_one (j : Fin 4) : D.n j ≠ 1 := by
  intro hj
  let k : Fin 4 := if j=0 then 1 else 0
  have hkj : k≠j := by
    dsimp [k]; split_ifs with h
    · subst j; decide
    · exact Ne.symm h
  let u : Fin 4 →₀ ℕ := Finsupp.single j (D.n k)
  have huk : u k=0 := by simp [u,hkj]
  apply D.minimal k u huk
  change (∑ x : Fin 4, (Finsupp.single j (D.n k)) x * D.n x)=D.n k
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro x _ hx
    simp [hx]
  · simp

/--
@isnad1 id=ex.0h1v.s5.fc90aa10df98 from=translated src=- shape=3fd46417 vocab=f46b422f
-/
theorem exists_minimum_generator : ∃ m : Fin 4,∀ j,D.n m≤D.n j := by
  obtain ⟨m,_,hm⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 4)) D.n
    Finset.univ_nonempty
  exact ⟨m,fun j=>hm j (Finset.mem_univ j)⟩

/--
@isnad1 id=le.3h3v.s6.51c6c09fc4ce from=translated src=- shape=d3170dc4 vocab=103481b8
-/
theorem minimum_generator_le {m : Fin 4} (hm : ∀ j,D.n m≤D.n j)
    {s : ℕ} (hs : s ∈ D.Gamma) (hpos : 0 < s) : D.n m ≤ s := by
  obtain ⟨u,hu⟩ := (D.mem_Gamma_iff s).mp hs
  have hne : u≠0 := by intro hz; subst u; simp at hu; omega
  obtain ⟨j,hj⟩ := Finsupp.ne_iff.mp hne
  have hp : 1≤u j := Nat.one_le_iff_ne_zero.mpr hj
  have hterm : u j*D.n j≤D.weightedDegree u := by
    apply Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  have hmul : D.n j≤u j*D.n j := by
    simpa using Nat.mul_le_mul_right (D.n j) hp
  rw [hu] at hterm
  exact (hm j).trans (hmul.trans hterm)

/--
@isnad1 id=not.0h1v.s4.945dc8c0f480 from=translated src=- shape=8bb8c2b7 vocab=882f2ce1
-/
theorem one_not_mem_Gamma : 1∉D.Gamma := by
  intro h
  obtain ⟨m,hm⟩ := D.exists_minimum_generator
  have hle := D.minimum_generator_le hm h (by omega)
  have hp := D.positive m
  exact D.generator_ne_one m (by omega)

/--
@isnad1 id=nonempty.0h1v.s2.56480bb4135c from=translated src=- shape=1a6c1393 vocab=fc5b93e7
-/
theorem gapFinset_nonempty : D.gapFinset.Nonempty :=
  ⟨1,(D.mem_gapFinset 1).mpr D.one_not_mem_Gamma⟩

def frobenius : ℕ := D.gapFinset.max' D.gapFinset_nonempty
def genus : ℕ := D.gapFinset.card

/--
@isnad1 id=mem.0h1v.s4.3df45d022c2d from=translated src=- shape=b5ca9b95 vocab=ec41da0f
-/
theorem frobenius_mem_gapFinset : D.frobenius∈D.gapFinset :=
  Finset.max'_mem _ _

/--
@isnad1 id=le.1h2v.s4.13f39dc25474 from=translated src=- shape=7199cbab vocab=9ded128d
-/
theorem gap_le_frobenius {s : ℕ} (hs : s∈D.gapFinset) : s≤D.frobenius :=
  Finset.le_max' _ _ hs

/--
@isnad1 id=not.0h1v.s4.593276c9b3c6 from=translated src=- shape=1467e363 vocab=42749f59
-/
theorem frobenius_not_mem_Gamma : D.frobenius∉D.Gamma :=
  (D.mem_gapFinset _).mp D.frobenius_mem_gapFinset

/--
@isnad1 id=mem.1h2v.s5.acf7a62e9df4 from=translated src=- shape=b3399546 vocab=da0ce86c
-/
theorem frobenius_lt_imp_mem_Gamma {s : ℕ} (hs : D.frobenius<s) : s∈D.Gamma := by
  by_contra hn
  have := D.gap_le_frobenius ((D.mem_gapFinset s).mpr hn)
  omega

/--
@isnad1 id=ispseudo.0h1v.s3.75e70a8cae28 from=translated src=- shape=fc43ad4a vocab=acf4dfba
-/
theorem frobenius_isPseudoFrobenius : D.IsPseudoFrobenius (D.frobenius : ℤ) := by
  refine ⟨by simpa using D.frobenius_not_mem_Gamma,?_⟩
  intro s hs
  have hp : 0<s.1 := by
    by_contra hn
    apply hs
    exact Subtype.ext (show s.1=0 by omega)
  have hmem := D.frobenius_lt_imp_mem_Gamma (s:=D.frobenius+s.1) (by omega)
  simpa using (D.intInGamma_natCast _).mpr hmem

def frobeniusPF : D.PseudoFrobeniusIndex := ⟨D.frobenius,D.frobenius_isPseudoFrobenius⟩

/--
@isnad1 id=lt.0h2v.s4.11880efa4b71 from=translated src=- shape=c84b9d84 vocab=79a3ec97
-/
theorem pseudoFrobenius_pos (f : D.PseudoFrobeniusIndex) : 0<f.1 := by
  obtain ⟨m,hm⟩ := D.exists_minimum_generator
  by_contra hn
  have hn' : f.1≤0 := by omega
  have hne : f.1≠0 := by intro hz; exact f.2.1 (hz ▸ D.intInGamma_zero)
  have hf : f.1<0 := by omega
  obtain ⟨s,hs⟩ := (D.isPseudoFrobenius_iff_generators f.1).mp f.2 |>.2 m
  have hslt : s.1<D.n m := by omega
  have hs0 : s.1=0 := by
    by_contra hh
    have := D.minimum_generator_le hm s.2 (Nat.pos_of_ne_zero hh)
    omega
  have he : f.1=-(D.n m : ℤ) := by omega
  let k := D.tailIndex m 0
  obtain ⟨g,hg⟩ := (D.isPseudoFrobenius_iff_generators f.1).mp f.2 |>.2 k
  apply D.tail_isApery m 0
  refine ⟨g,Subtype.ext ?_⟩
  change D.n k=D.n m+g.1
  omega

def pseudoFrobeniusNat (f : D.PseudoFrobeniusIndex) : ℕ := f.1.toNat

/--
@isnad1 id=eq.0h2v.s4.d861f12ef9ac from=translated src=- shape=d7c7d4ef vocab=bf691b15
-/
@[simp] theorem pseudoFrobeniusNat_cast (f : D.PseudoFrobeniusIndex) :
    (D.pseudoFrobeniusNat f : ℤ)=f.1 :=
  Int.toNat_of_nonneg (le_of_lt (D.pseudoFrobenius_pos f))

/--
@isnad1 id=mem.0h2v.s4.86c9bc2f72e8 from=translated src=- shape=4ad308ba vocab=bab7df17
-/
theorem pseudoFrobeniusNat_mem_gapFinset (f : D.PseudoFrobeniusIndex) :
    D.pseudoFrobeniusNat f∈D.gapFinset := by
  apply (D.mem_gapFinset _).mpr
  intro hm
  apply f.2.1
  simpa using (D.intInGamma_natCast _).mpr hm

/--
@isnad1 id=le.0h2v.s3.ccf795ad0739 from=translated src=- shape=df9e97da vocab=ccf3f7ca
-/
theorem pseudoFrobeniusNat_le_frobenius (f : D.PseudoFrobeniusIndex) :
    D.pseudoFrobeniusNat f≤D.frobenius :=
  D.gap_le_frobenius (D.pseudoFrobeniusNat_mem_gapFinset f)

/--
@isnad1 id=le.0h2v.s4.87d94f9159c7 from=translated src=- shape=184b8393 vocab=68ec0eae
-/
theorem pseudoFrobenius_le_frobenius (f : D.PseudoFrobeniusIndex) :
    f.1≤(D.frobenius : ℤ) := by
  have := D.pseudoFrobeniusNat_le_frobenius f
  rw [←D.pseudoFrobeniusNat_cast f]
  exact_mod_cast this

/--
@isnad1 id=injectiv.0h1v.s3.a2ded13a71df from=translated src=- shape=64d36d98 vocab=fb77221d
-/
theorem pseudoFrobeniusNat_injective : Function.Injective D.pseudoFrobeniusNat := by
  intro f g h
  apply Subtype.ext
  simpa using congrArg (fun a : ℕ=>(a:ℤ)) h

def pseudoFrobeniusSum : ℤ := ∑ f : D.PseudoFrobeniusIndex,f.1

/--
@isnad1 id=eq.0h2v.s5.506b23aa6b9d from=translated src=- shape=5d8d1896 vocab=a6e4e4d6
-/
theorem pseudoFrobeniusSum_erase (h : D.PseudoFrobeniusIndex) :
    ∑ f ∈ (Finset.univ : Finset D.PseudoFrobeniusIndex).erase h,f.1 =
      D.pseudoFrobeniusSum-h.1 := by
  classical
  have hh := Finset.sum_erase_add (Finset.univ : Finset D.PseudoFrobeniusIndex)
    (fun f=>f.1) (Finset.mem_univ h)
  change (∑ f ∈ Finset.univ.erase h,f.1)+h.1=D.pseudoFrobeniusSum at hh
  omega

end
end P23.Semigroup.FourGeneratedNumericalSemigroup
