import Tengoku.NsP23.P23.Monomial.PlainLocalSocle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Monomial
noncomputable section
variable {k : Type*} [Field k]
open PlainMonomialArtin

def PlainDirectSocle (R : Finset PlainExp) (hR : R.Nonempty) :
    Submodule k (PlainMonomialArtin k R) where
  carrier := {v | ∀ r ∈ plainAugmentationIdeal (k := k) R hR, r*v=0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw r hr; rw [mul_add,hv r hr,hw r hr,add_zero]
  smul_mem' := by intro t v hv r hr; rw [mul_smul_comm',hv r hr,smul_zero]

theorem plain_root_variable_killed (R : Finset PlainExp) (ha : PlainRootAntichain R)
    (s : PlainExp) (hs : s ∈ R) (j : Fin 3) :
    PXall (k := k) R (plainUnitVector j) * PX R s (plainRootIndex R s hs).2 = 0 := by
  have hn : plainUnitVector j+s ∉ plainStandardFinset R := by
    rintro h
    obtain ⟨t,ht,hst⟩ := (mem_plainStandardFinset R _).mp h
    have hle : plainDivides s t := fun r => le_trans (Nat.le_add_left _ _) (hst r)
    have he := ha s hs t ht hle
    subst t
    have hc := hst j
    simp at hc
  rw [←show PXall (k := k) R s = PX R s (plainRootIndex R s hs).2 by
    exact dite_eq_left (plainRootIndex R s hs).2,←PXall_add]
  simp [PXall,hn]

theorem plain_root_mem_socle (R : Finset PlainExp) (hR : R.Nonempty)
    (ha : PlainRootAntichain R) (s : PlainExp) (hs : s ∈ R) :
    PX (k := k) R s (plainRootIndex R s hs).2 ∈ PlainDirectSocle R hR := by
  intro r hr
  rw [←plainVariableIdeal_eq_augmentationIdeal R hR] at hr
  refine Submodule.span_induction (p := fun r _ => r * PX R s (plainRootIndex R s hs).2=0)
    ?_ ?_ ?_ ?_ hr
  · rintro _ ⟨j,rfl⟩; exact plain_root_variable_killed R ha s hs j
  · simp
  · intro r t _ _ hr ht; rw [add_mul,hr,ht,add_zero]
  · intro a r _ hr; change (a*r)*_=0; rw [mul_assoc,hr,mul_zero]

theorem plain_nonroot_extension (R : Finset PlainExp) (p : PlainMonomialIndex R)
    (hp : p.1 ∉ R) : ∃ j, plainUnitVector j+p.1 ∈ plainStandardFinset R := by
  obtain ⟨s,hs,hps⟩ := (mem_plainStandardFinset R p.1).mp p.2
  have hn : p.1 ≠ s := fun h => hp (h ▸ hs)
  have hex : ∃ j, p.1 j < s j := by
    by_contra h
    push Not at h
    apply hn
    ext j
    exact le_antisymm (hps j) (h j)
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,(mem_plainStandardFinset R _).mpr ⟨s,hs,?_⟩⟩
  intro r
  by_cases hr : r=j
  · subst r; simp; omega
  · simpa [plainUnitVector,Finsupp.single_apply,Ne.symm hr] using hps r

theorem plain_nonroot_coeff_zero (R : Finset PlainExp) (hR : R.Nonempty)
    (v : PlainMonomialArtin k R) (hv : v ∈ PlainDirectSocle R hR)
    (p : PlainMonomialIndex R) (hp : p.1 ∉ R) : v.coeff p=0 := by
  obtain ⟨j,hjp⟩ := plain_nonroot_extension R p hp
  have hj := mem_plainStandardFinset_of_add_mem_left R hjp
  let ji : PlainMonomialIndex R := ⟨plainUnitVector j,hj⟩
  let ti : PlainMonomialIndex R := ⟨plainUnitVector j+p.1,hjp⟩
  have hm : PX (k := k) R ji.1 ji.2 ∈ plainAugmentationIdeal R hR := by
    rw [←plainVariableIdeal_eq_augmentationIdeal R hR]
    simpa [plainVariableIdeal,PXall,hj,ji] using (Ideal.subset_span (s := Set.range
      (fun j : Fin 3 => PXall (k := k) R (plainUnitVector j))) ⟨j,rfl⟩)
  have hz := hv _ hm
  have hc := congrArg (plainCoeffAt (k := k) R ti) hz
  rw [plainCoeffAt_PX_mul R ji p ti rfl] at hc
  simpa using hc

def plainRootBasisVector (R : Finset PlainExp) (s : ↥R) : PlainMonomialArtin k R :=
  PX R s.1 (plainRootIndex R s.1 s.2).2
def plainRootSpan (R : Finset PlainExp) : Submodule k (PlainMonomialArtin k R) :=
  Submodule.span k (Set.range (plainRootBasisVector (k := k) R))

theorem plain_socle_eq_rootSpan (R : Finset PlainExp) (hR : R.Nonempty)
    (ha : PlainRootAntichain R) : PlainDirectSocle (k := k) R hR = plainRootSpan R := by
  apply le_antisymm
  · intro v hv
    rw [basis_expansion v]
    apply Submodule.sum_mem
    intro p _
    by_cases hp : p.1 ∈ R
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨p.1,hp⟩,rfl⟩
    · simp [plain_nonroot_coeff_zero R hR v hv p hp]
  · apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    exact plain_root_mem_socle R hR ha s.1 s.2

theorem plain_rootBasis_independent (R : Finset PlainExp) :
    LinearIndependent k (plainRootBasisVector (k := k) R) := by
  let f : ↥R → PlainMonomialIndex R := fun s => plainRootIndex R s.1 s.2
  have hinj : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun p : PlainMonomialIndex R => p.1) h
  exact (monomialBasis k R).linearIndependent.comp f hinj

def plainDirectType (k : Type*) [Field k] (R : Finset PlainExp) (hR : R.Nonempty) : ℕ :=
  Module.finrank k (PlainDirectSocle (k := k) R hR)

theorem plainDirectType_eq_rootCard (R : Finset PlainExp) (hR : R.Nonempty)
    (ha : PlainRootAntichain R) : plainDirectType k R hR = R.card := by
  unfold plainDirectType
  rw [plain_socle_eq_rootSpan R hR ha]
  unfold plainRootSpan
  rw [finrank_span_eq_card (plain_rootBasis_independent (k := k) R)]
  exact Fintype.card_coe R

end
end P23.Monomial
