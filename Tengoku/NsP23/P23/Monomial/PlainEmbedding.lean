import Tengoku.NsP23.P23.Monomial.PlainLocalSocle
import Tengoku.Seed.RingTheory.Ideal.Cotangent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Monomial
noncomputable section
open scoped BigOperators
variable {k : Type*} [Field k]
open PlainMonomialArtin

abbrev PlainCotangent (k : Type*) [Field k] (R : Finset PlainExp) (hR : R.Nonempty) :=
  (plainAugmentationIdeal (k := k) R hR).Cotangent
def plainEmbeddingDimension (k : Type*) [Field k] (R : Finset PlainExp) (hR : R.Nonempty) : ℕ :=
  Module.finrank k (PlainCotangent k R hR)

abbrev PlainVariableIndex (R : Finset PlainExp) := {j : Fin 3 // plainUnitVector j ∈ plainStandardFinset R}

/--
@isnad1 id=mem.3h3v.s7.b48ca11d65b4 from=translated src=- shape=000efd99 vocab=44e6ab88
-/
theorem plain_PX_mem_augmentation (R : Finset PlainExp) (hR : R.Nonempty)
    (p : PlainExp) (hp : p ∈ plainStandardFinset R) (hn : p ≠ 0) :
    PX (k := k) R p hp ∈ plainAugmentationIdeal R hR := by
  change plainConstantCoeff R hR (PX (k := k) R p hp)=0
  simp [plainConstantCoeff,plainUnitIndex,Ne.symm hn]

/--
@isnad1 id=mem.4h3v.s8.3e1604bdb1d8 from=translated src=- shape=ebbf2a02 vocab=45553775
-/
theorem plain_nonvariable_mem_square (R : Finset PlainExp) (hR : R.Nonempty)
    (p : PlainExp) (hp : p ∈ plainStandardFinset R) (hn : p≠0)
    (hv : ∀ j, p≠plainUnitVector j) :
    PX (k := k) R p hp ∈ (plainAugmentationIdeal R hR)^2 := by
  have hex : ∃ j, 0 < p j := by
    by_contra h
    push Not at h
    apply hn
    ext j
    exact Nat.eq_zero_of_le_zero (h j)
  obtain ⟨j,hj⟩ := hex
  let q := plainPredecessor j p
  have hsum : q+plainUnitVector j=p := plainPredecessor_add_unitVector j p hj
  have hq : q ∈ plainStandardFinset R :=
    mem_plainStandardFinset_of_add_mem_left R (hsum ▸ hp)
  have he : plainUnitVector j ∈ plainStandardFinset R :=
    mem_plainStandardFinset_of_add_mem_right R (hsum ▸ hp)
  have hqn : q≠0 := by intro h; exact hv j (by simpa [h] using hsum.symm)
  have hen : plainUnitVector j≠(0 : PlainExp) := by
    intro h; have := congrArg (fun p : PlainExp => p j) h; simpa using this
  have hm := Ideal.mul_mem_mul (plain_PX_mem_augmentation (k := k) R hR q hq hqn)
    (plain_PX_mem_augmentation (k := k) R hR _ he hen)
  simpa [pow_two,PX_mul_PX,hsum,hp] using hm

/--
@isnad1 id=eq.1h5v.s9.fa0daf5dc12f from=translated src=- shape=6ec46ce7 vocab=6ebf1bb5
-/
theorem plain_variable_coeff_mul_zero (R : Finset PlainExp) (hR : R.Nonempty)
    (j : PlainVariableIndex R) (u v : plainAugmentationIdeal (k := k) R hR) :
    plainCoeffAt (k := k) R ⟨plainUnitVector j.1,j.2⟩ (u.val*v.val)=0 := by
  let ei : PlainMonomialIndex R := ⟨plainUnitVector j.1,j.2⟩
  have hu : plainConstantCoeff R hR u.val=0 := u.2
  have hv : plainConstantCoeff R hR v.val=0 := v.2
  rw [basis_expansion (u : PlainMonomialArtin k R)]
  rw [Finsupp.sum_mul,map_finsuppSum]
  apply Finset.sum_eq_zero
  intro p _
  change plainCoeffAt (k := k) R ei ((u.val.coeff p • PX R p.1 p.2)*v.val)=0
  rw [smul_mul_assoc',map_smul]
  by_cases hp0 : p.1=0
  · have hc : u.val.coeff p=0 := by
      have he : p=plainUnitIndex R hR := Subtype.ext hp0
      simpa [plainConstantCoeff,he] using hu
    simp [hc]
  · have hz : plainCoeffAt R ei (PX R p.1 p.2*v.val)=0 := by
      by_cases hpe : p.1=plainUnitVector j.1
      · have he : p=ei := Subtype.ext hpe
        rw [plainCoeffAt_PX_mul R p (plainUnitIndex R hR) ei (by simp [ei,hpe,plainUnitIndex])]
        exact hv
      · induction v.val using induction_linear with
        | zero => simp
        | add v w hv hw => rw [mul_add,map_add,hv,hw,add_zero]
        | single q r =>
          rw [←smul_PX r R q.1 q.2,mul_smul_comm',map_smul,PX_mul_PX]
          have hn : p.1+q.1≠plainUnitVector j.1 := by
            intro h
            rcases plain_variable_is_atom j.1 p.1 q.1 h with hp | hq
            · exact hp0 hp
            · exact hpe (by simpa [hq] using h)
          by_cases hs : p.1+q.1∈plainStandardFinset R <;>
            simp [hs,plainCoeffAt_apply,ei,Ne.symm hn]
    simp [hz]

def plainCotangentCoeff (R : Finset PlainExp) (hR : R.Nonempty)
    (j : PlainVariableIndex R) : PlainCotangent k R hR →ₗ[k] k :=
  Ideal.Cotangent.lift
    ((plainCoeffAt (k := k) R ⟨plainUnitVector j.1,j.2⟩).comp
      ((plainAugmentationIdeal (k := k) R hR).subtype.restrictScalars k))
    (fun u v => plain_variable_coeff_mul_zero R hR j u v)

def plainCotangentVariable (R : Finset PlainExp) (hR : R.Nonempty)
    (j : PlainVariableIndex R) : PlainCotangent k R hR :=
  (plainAugmentationIdeal (k := k) R hR).toCotangent
    ⟨PX R (plainUnitVector j.1) j.2,plain_PX_mem_augmentation R hR _ j.2 (by
      intro h; have := congrArg (fun p : PlainExp => p j.1) h; simpa using this)⟩

/--
@isnad1 id=eq.1h4v.s8.82159682ccdf from=translated src=- shape=9607cb38 vocab=1ce736c6
-/
@[simp] theorem plainCotangentCoeff_variable (R : Finset PlainExp) (hR : R.Nonempty)
    (j l : PlainVariableIndex R) :
    plainCotangentCoeff (k := k) R hR j (plainCotangentVariable R hR l) =
      if l=j then 1 else 0 := by
  change plainCoeffAt (k := k) R ⟨plainUnitVector j.1,j.2⟩
    (PX R (plainUnitVector l.1) l.2) = _
  rw [plainCoeffAt_apply,coeff_PX]
  have he : plainUnitVector j.1=plainUnitVector l.1 ↔ j=l := by
    constructor
    · intro h
      apply Subtype.ext
      by_contra hn
      have hc := congrArg (fun p : PlainExp => p j.1) h
      simp [plainUnitVector,Finsupp.single_apply,Ne.symm hn] at hc
    · rintro rfl; rfl
  simp [he,eq_comm]

/--
@isnad1 id=linearin.1h2v.s6.a92f09bca196 from=translated src=- shape=85b748f7 vocab=ae942d70
-/
theorem plainCotangentVariables_independent (R : Finset PlainExp) (hR : R.Nonempty) :
    LinearIndependent k (plainCotangentVariable (k := k) R hR) := by
  apply linearIndependent_iff'.mpr
  intro s c hz j hj
  have hc := congrArg (plainCotangentCoeff (k := k) R hR j) hz
  simpa [map_sum,hj] using hc

/--
@isnad1 id=eq.1h2v.s8.6827272e597f from=translated src=- shape=445071cd vocab=044b739f
-/
theorem plainCotangentVariables_span (R : Finset PlainExp) (hR : R.Nonempty) :
    Submodule.span k (Set.range (plainCotangentVariable (k := k) R hR)) = ⊤ := by
  apply top_unique
  intro x _
  let I := plainAugmentationIdeal (k := k) R hR
  obtain ⟨v,rfl⟩ := I.toCotangent_surjective x
  let B : PlainMonomialIndex R → I := fun p => if hn : p.1=0 then 0 else
    ⟨PX R p.1 p.2,plain_PX_mem_augmentation R hR p.1 p.2 hn⟩
  have hex : v=v.val.coeff.sum (fun p c => c • B p) := by
    apply Subtype.ext
    change v.val = (I.subtype.restrictScalars k) (v.val.coeff.sum (fun p c => c • B p))
    rw [map_finsuppSum]
    simp only [map_smul,Submodule.subtype_apply]
    conv_lhs => rw [basis_expansion v.val]
    apply Finsupp.sum_congr
    intro p _
    by_cases hp : p.1=0
    · have he : p=plainUnitIndex R hR := Subtype.ext hp
      have hc : v.val.coeff p=0 := by
        have hv : plainConstantCoeff R hR v.val=0 := v.2
        simpa [he,plainConstantCoeff] using hv
      simp [hc,B,hp]
    · simp [B,hp]
  rw [hex,map_finsuppSum]
  apply Submodule.sum_mem
  intro p _
  change (I.toCotangent.restrictScalars k) (v.val.coeff p • B p) ∈ _
  rw [map_smul]
  apply Submodule.smul_mem
  change I.toCotangent (B p) ∈ _
  by_cases hp : p.1=0
  · simp [B,hp]
  · by_cases he : ∃ j, p.1=plainUnitVector j
    · obtain ⟨j,hj⟩ := he
      let ji : PlainVariableIndex R := ⟨j,hj ▸ p.2⟩
      have hb : I.toCotangent (B p) = plainCotangentVariable R hR ji := by
        change I.toCotangent (B p) = I.toCotangent _
        apply congrArg I.toCotangent
        apply Subtype.ext
        simp only [B,dite_eq_right hp]
        change PX R p.1 p.2 = PX R (plainUnitVector j) ji.2
        apply PlainMonomialArtin.ext
        ext q
        simp only [coeff_PX,hj]
      rw [hb]
      exact Submodule.subset_span ⟨ji,rfl⟩
    · have hv : ∀ j, p.1≠plainUnitVector j := fun j h => he ⟨j,h⟩
      have hz : I.toCotangent (B p)=0 := by
        apply (I.toCotangent_eq_zero (B p)).mpr
        simpa [B,hp,I] using plain_nonvariable_mem_square (k := k) R hR p.1 p.2 hp hv
      rw [hz]
      exact Submodule.zero_mem _

def plainCotangentBasis (R : Finset PlainExp) (hR : R.Nonempty) :
    Module.Basis (PlainVariableIndex R) k (PlainCotangent k R hR) :=
  Module.Basis.mk (plainCotangentVariables_independent R hR)
    (plainCotangentVariables_span R hR).ge

/--
@isnad1 id=iff.1h2v.s4.b151e6fe1617 from=translated src=- shape=13ae0617 vocab=0a8d2907
-/
theorem plain_embeddingDimension_eq_three_iff_variablesSurvive (R : Finset PlainExp)
    (hR : R.Nonempty) : plainEmbeddingDimension k R hR=3 ↔ PlainVariablesSurvive R := by
  unfold plainEmbeddingDimension
  rw [Module.finrank_eq_card_basis (plainCotangentBasis (k := k) R hR)]
  classical
  have hcard : Fintype.card (PlainVariableIndex R) =
      (Finset.univ.filter (fun j : Fin 3 => plainUnitVector j ∈ plainStandardFinset R)).card :=
    Fintype.card_subtype _
  rw [hcard]
  change (Finset.univ.filter (fun j : Fin 3 => plainUnitVector j ∈ plainStandardFinset R)).card =
    (Finset.univ : Finset (Fin 3)).card ↔ _
  rw [Finset.card_filter_eq_iff]
  simp [PlainVariablesSurvive,mem_plainStandardFinset]

end
end P23.Monomial
