import Tengoku.NsP23.P23.Semigroup.PseudoFrobenius
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Semigroup.FourGeneratedNumericalSemigroup
noncomputable section
open scoped BigOperators
variable (D : FourGeneratedNumericalSemigroup)

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

theorem exists_minimum_generator : ∃ m : Fin 4,∀ j,D.n m≤D.n j := by
  obtain ⟨m,_,hm⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 4)) D.n
    Finset.univ_nonempty
  exact ⟨m,fun j=>hm j (Finset.mem_univ j)⟩

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

theorem one_not_mem_Gamma : 1∉D.Gamma := by
  intro h
  obtain ⟨m,hm⟩ := D.exists_minimum_generator
  have hle := D.minimum_generator_le hm h (by omega)
  have hp := D.positive m
  exact D.generator_ne_one m (by omega)

theorem gapFinset_nonempty : D.gapFinset.Nonempty :=
  ⟨1,(D.mem_gapFinset 1).mpr D.one_not_mem_Gamma⟩

def frobenius : ℕ := D.gapFinset.max' D.gapFinset_nonempty
def genus : ℕ := D.gapFinset.card

theorem frobenius_mem_gapFinset : D.frobenius∈D.gapFinset :=
  Finset.max'_mem _ _

theorem gap_le_frobenius {s : ℕ} (hs : s∈D.gapFinset) : s≤D.frobenius :=
  Finset.le_max' _ _ hs

theorem frobenius_not_mem_Gamma : D.frobenius∉D.Gamma :=
  (D.mem_gapFinset _).mp D.frobenius_mem_gapFinset

theorem frobenius_lt_imp_mem_Gamma {s : ℕ} (hs : D.frobenius<s) : s∈D.Gamma := by
  by_contra hn
  have := D.gap_le_frobenius ((D.mem_gapFinset s).mpr hn)
  omega

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

@[simp] theorem pseudoFrobeniusNat_cast (f : D.PseudoFrobeniusIndex) :
    (D.pseudoFrobeniusNat f : ℤ)=f.1 :=
  Int.toNat_of_nonneg (le_of_lt (D.pseudoFrobenius_pos f))

theorem pseudoFrobeniusNat_mem_gapFinset (f : D.PseudoFrobeniusIndex) :
    D.pseudoFrobeniusNat f∈D.gapFinset := by
  apply (D.mem_gapFinset _).mpr
  intro hm
  apply f.2.1
  simpa using (D.intInGamma_natCast _).mpr hm

theorem pseudoFrobeniusNat_le_frobenius (f : D.PseudoFrobeniusIndex) :
    D.pseudoFrobeniusNat f≤D.frobenius :=
  D.gap_le_frobenius (D.pseudoFrobeniusNat_mem_gapFinset f)

theorem pseudoFrobenius_le_frobenius (f : D.PseudoFrobeniusIndex) :
    f.1≤(D.frobenius : ℤ) := by
  have := D.pseudoFrobeniusNat_le_frobenius f
  rw [←D.pseudoFrobeniusNat_cast f]
  exact_mod_cast this

theorem pseudoFrobeniusNat_injective : Function.Injective D.pseudoFrobeniusNat := by
  intro f g h
  apply Subtype.ext
  simpa using congrArg (fun a : ℕ=>(a:ℤ)) h

def pseudoFrobeniusSum : ℤ := ∑ f : D.PseudoFrobeniusIndex,f.1

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
