import Tengoku.NsP23.P23.Semigroup.NumericalInvariants
import Tengoku.NsP23.P23.Semigroup.AperyResidues

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Semigroup.FourGeneratedNumericalSemigroup
noncomputable section
open scoped BigOperators
variable (D : FourGeneratedNumericalSemigroup)

instance aperyIndexFintype (i : Fin 4) : Fintype (D.AperyIndex i) := Fintype.ofFinite _

def aperyOfResidue (i : Fin 4) (r : Fin (D.n i)) : D.AperyIndex i :=
  (aperyResidueEquiv D i).symm (r.1 : ZMod (D.n i))

/--
@isnad1 id=eq.0h3v.s5.e27c491afd72 from=translated src=- shape=f7c8d0ad vocab=b317e19f
-/
theorem aperyOfResidue_residue (i : Fin 4) (r : Fin (D.n i)) :
    aperyResidue D i (D.aperyOfResidue i r)=(r.1 : ZMod (D.n i)) :=
  (aperyResidueEquiv D i).apply_symm_apply _

/--
@isnad1 id=eq.0h3v.s6.10730b71e15e from=translated src=- shape=c6874401 vocab=5d75f1ef
-/
theorem aperyOfResidue_mod (i : Fin 4) (r : Fin (D.n i)) :
    (D.aperyOfResidue i r).1.1 % D.n i=r.1 := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mp (D.aperyOfResidue_residue i r)
  simpa [Nat.ModEq,Nat.mod_eq_of_lt r.isLt] using h

def aperyQuotient (i : Fin 4) (r : Fin (D.n i)) : ℕ :=
  (D.aperyOfResidue i r).1.1 / D.n i

/--
@isnad1 id=eq.0h3v.s7.37c05fe14d59 from=translated src=- shape=4f9ffc2d vocab=8a138e39
-/
theorem apery_residue_decomposition (i : Fin 4) (r : Fin (D.n i)) :
    (D.aperyOfResidue i r).1.1=r.1+D.n i*D.aperyQuotient i r := by
  have h := Nat.mod_add_div (D.aperyOfResidue i r).1.1 (D.n i)
  rw [D.aperyOfResidue_mod i r] at h
  exact h.symm

/--
@isnad1 id=iff.0h4v.s5.83ab31301cd8 from=translated src=- shape=4caabf32 vocab=a453cad9
-/
theorem gap_iff_lt_aperyQuotient (i : Fin 4) (r : Fin (D.n i)) (k : ℕ) :
    r.1+D.n i*k∈D.gapFinset ↔ k<D.aperyQuotient i r := by
  rw [D.mem_gapFinset]
  let s := D.aperyOfResidue i r
  have hs := D.apery_residue_decomposition i r
  have hq := D.positive i
  constructor
  · intro hnot
    by_contra hn
    have hk : D.aperyQuotient i r≤k := by omega
    let g : D.Gamma := s.1+(k-D.aperyQuotient i r) • D.base i
    have hmul := congrArg (fun x : ℕ=>D.n i*x)
      (Nat.add_sub_of_le hk : D.aperyQuotient i r+(k-D.aperyQuotient i r)=k)
    have he : g.1=r.1+D.n i*k := by
      change s.1.1+(k-D.aperyQuotient i r)*D.n i=_
      change s.1.1=r.1+D.n i*D.aperyQuotient i r at hs
      nlinarith
    exact hnot (he ▸ g.2)
  · intro hk hmem
    apply s.2
    let g : D.Gamma := ⟨r.1+D.n i*k,hmem⟩+
      (D.aperyQuotient i r-k-1) • D.base i
    refine ⟨g,Subtype.ext ?_⟩
    change s.1.1=D.n i+(r.1+D.n i*k+(D.aperyQuotient i r-k-1)*D.n i)
    have hsum : (D.aperyQuotient i r-k-1)+k+1=D.aperyQuotient i r := by omega
    have hmul := congrArg (fun x : ℕ=>D.n i*x) hsum
    change s.1.1=r.1+D.n i*D.aperyQuotient i r at hs
    nlinarith

def residueGap (i : Fin 4) (x : Σ r : Fin (D.n i),Fin (D.aperyQuotient i r)) :
    ↥D.gapFinset :=
  ⟨x.1.1+D.n i*x.2.1,(D.gap_iff_lt_aperyQuotient i x.1 x.2.1).mpr x.2.isLt⟩

/--
@isnad1 id=bijectiv.0h2v.s5.f86c6607f186 from=translated src=- shape=13d6da25 vocab=2ef258aa
-/
theorem residueGap_bijective (i : Fin 4) : Function.Bijective (D.residueGap i) := by
  constructor
  · rintro ⟨r,k⟩ ⟨t,l⟩ he
    have hv := congrArg Subtype.val he
    change r.1+D.n i*k.1=t.1+D.n i*l.1 at hv
    have hm := congrArg (fun x : ℕ=>x % D.n i) hv
    rw [Nat.add_mul_mod_self_left,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt t.isLt] at hm
    have hrt : r=t := Fin.ext hm
    subst t
    have hq := D.positive i
    have hkl : k.1=l.1 := by nlinarith
    have hke : k=l := Fin.ext hkl
    subst l
    rfl
  · intro a
    let r : Fin (D.n i) := ⟨a.1 % D.n i,Nat.mod_lt _ (D.positive i)⟩
    have he : r.1+D.n i*(a.1 / D.n i)=a.1 := Nat.mod_add_div _ _
    have hk : a.1 / D.n i<D.aperyQuotient i r :=
      (D.gap_iff_lt_aperyQuotient i r _).mp (he.symm ▸ a.2)
    exact ⟨⟨r,⟨a.1 / D.n i,hk⟩⟩,Subtype.ext he⟩

def gapResidueEquiv (i : Fin 4) :
    ↥D.gapFinset ≃ Σ r : Fin (D.n i),Fin (D.aperyQuotient i r) :=
  (Equiv.ofBijective (D.residueGap i) (D.residueGap_bijective i)).symm

/--
@isnad1 id=eq.0h2v.s5.ec878fd3e97e from=translated src=- shape=72373160 vocab=4f51b089
-/
theorem genus_eq_sum_aperyQuotient (i : Fin 4) :
    D.genus=∑ r : Fin (D.n i),D.aperyQuotient i r := by
  have h := Fintype.card_congr (D.gapResidueEquiv i)
  simpa [genus,Fintype.card_sigma] using h

/--
@isnad1 id=bijectiv.0h2v.s4.adfc596deacd from=translated src=- shape=8660705f vocab=c20ef1b4
-/
theorem aperyOfResidue_bijective (i : Fin 4) : Function.Bijective (D.aperyOfResidue i) := by
  constructor
  · intro r t h
    have hm := congrArg (fun w : D.AperyIndex i=>w.1.1 % D.n i) h
    rw [D.aperyOfResidue_mod,D.aperyOfResidue_mod] at hm
    exact Fin.ext hm
  · intro w
    let r : Fin (D.n i) := ⟨w.1.1 % D.n i,Nat.mod_lt _ (D.positive i)⟩
    refine ⟨r,aperyResidue_injective D i ?_⟩
    rw [D.aperyOfResidue_residue]
    simp [r,aperyResidue]

def aperyOfResidueEquiv (i : Fin 4) : Fin (D.n i) ≃ D.AperyIndex i :=
  Equiv.ofBijective (D.aperyOfResidue i) (D.aperyOfResidue_bijective i)

private theorem doubled_fin_val_sum (q : ℕ) :
    2*(∑ r : Fin q,(r.1:ℤ))=(q:ℤ)*((q:ℤ)-1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    push_cast
    nlinarith

/--
@isnad1 id=eq.0h2v.s7.96e1a84b14d1 from=translated src=- shape=fa7080a0 vocab=cb95b26a
-/
theorem apery_genus_formula_doubled (i : Fin 4) :
    2*(D.n i:ℤ)*(D.genus:ℤ)=
      2*(∑ w : D.AperyIndex i,(w.1.1:ℤ))-(D.n i:ℤ)*((D.n i:ℤ)-1) := by
  have hs := (D.aperyOfResidueEquiv i).sum_comp (fun w : D.AperyIndex i=>(w.1.1:ℤ))
  have hv : (∑ w : D.AperyIndex i,(w.1.1:ℤ))=
      (∑ r : Fin (D.n i),(r.1:ℤ))+(D.n i:ℤ)*(∑ r : Fin (D.n i),(D.aperyQuotient i r:ℤ)) := by
    rw [←hs]
    change (∑ r : Fin (D.n i),((D.aperyOfResidue i r).1.1:ℤ))=_
    simp_rw [D.apery_residue_decomposition]
    simp [Nat.cast_add,Nat.cast_mul,Finset.sum_add_distrib,Finset.mul_sum]
  have hg : (D.genus:ℤ)=∑ r : Fin (D.n i),(D.aperyQuotient i r:ℤ) := by
    exact_mod_cast D.genus_eq_sum_aperyQuotient i
  have hr := doubled_fin_val_sum (D.n i)
  rw [hv,hg]
  nlinarith

end
end P23.Semigroup.FourGeneratedNumericalSemigroup
