import Tengoku.NsP23.P23.Monomial.PlainTraceToCentre
import Tengoku.NsP23.P23.Monomial.PlainQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Monomial
noncomputable section
open scoped BigOperators
variable {k : Type*} [Field k]
open PlainMonomialArtin

def plainConstantCoeffAlgHom (R : Finset PlainExp) (hR : R.Nonempty) :
    PlainMonomialArtin k R →ₐ[k] k where
  toFun := plainConstantCoeff R hR
  map_one' := plainConstantCoeff_one R hR
  map_mul' := plainConstantCoeff_mul R hR
  map_zero' := by simp
  map_add' := by simp
  commutes' r := by
    change plainConstantCoeff R hR (r • (1 : PlainMonomialArtin k R)) = r
    simp

def plainAugmentationIdeal (R : Finset PlainExp) (hR : R.Nonempty) :
    Ideal (PlainMonomialArtin k R) := RingHom.ker (plainConstantCoeffAlgHom R hR).toRingHom

theorem plainAugmentationIdeal_isMaximal (R : Finset PlainExp) (hR : R.Nonempty) :
    (plainAugmentationIdeal (k := k) R hR).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro r
  exact ⟨algebraMap k (PlainMonomialArtin k R) r,(plainConstantCoeffAlgHom R hR).commutes r⟩

def plainVariableIdeal (R : Finset PlainExp) : Ideal (PlainMonomialArtin k R) :=
  Ideal.span (Set.range (fun j : Fin 3 => PXall (k := k) R (plainUnitVector j)))

theorem plain_PX_mem_variableIdeal (R : Finset PlainExp) (p : PlainExp)
    (hp : p ∈ plainStandardFinset R) (hn : p ≠ 0) :
    PX (k := k) R p hp ∈ plainVariableIdeal R := by
  have hex : ∃ j, 0 < p j := by
    by_contra h
    push Not at h
    apply hn
    ext j
    exact Nat.eq_zero_of_le_zero (h j)
  obtain ⟨j,hj⟩ := hex
  let q := plainPredecessor j p
  have hq : q ∈ plainStandardFinset R := (mem_plainStandardFinset R q).mpr
    (plainStandard_downward R ((mem_plainStandardFinset R p).mp hp) (plainPredecessor_divides j p))
  have he : plainUnitVector j ∈ plainStandardFinset R := by
    apply mem_plainStandardFinset_of_add_mem_right R (p := q)
    simpa [q,plainPredecessor_add_unitVector j p hj] using hp
  have hv : PX (k := k) R (plainUnitVector j) he ∈ plainVariableIdeal R := by
    simpa [plainVariableIdeal,PXall,he] using (Ideal.subset_span (s := Set.range
      (fun j : Fin 3 => PXall (k := k) R (plainUnitVector j))) ⟨j,rfl⟩)
  have hm := (plainVariableIdeal (k := k) R).mul_mem_left (PX R q hq) hv
  simpa [PX_mul_PX,q,plainPredecessor_add_unitVector j p hj,hp] using hm

theorem plainVariableIdeal_eq_augmentationIdeal (R : Finset PlainExp) (hR : R.Nonempty) :
    plainVariableIdeal (k := k) R = plainAugmentationIdeal R hR := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change plainConstantCoeff R hR (PXall (k := k) R (plainUnitVector j)) = 0
    have hn : (0 : PlainExp) ≠ plainUnitVector j := by
      intro h; have := congrArg (fun p : PlainExp => p j) h; simpa using this
    by_cases hj : plainUnitVector j ∈ plainStandardFinset R <;>
      simp [PXall,hj,plainConstantCoeff,plainUnitIndex,hn]
  · intro v hv
    change plainConstantCoeff R hR v = 0 at hv
    rw [basis_expansion v]
    apply Submodule.sum_mem
    intro p _
    by_cases hp : p.1 = 0
    · have he : p = plainUnitIndex R hR := Subtype.ext hp
      have hc : v.coeff p = 0 := by simpa [he,plainConstantCoeff] using hv
      simp [hc]
    · have hm := plain_PX_mem_variableIdeal (k := k) R p.1 p.2 hp
      simpa [Algebra.smul_def] using (plainVariableIdeal (k := k) R).mul_mem_left
        (algebraMap k (PlainMonomialArtin k R) (v.coeff p)) hm

theorem plain_PXall_nsmul (R : Finset PlainExp) (p : PlainExp) (n : ℕ) :
    PXall (k := k) R (n • p) = (PXall R p)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul,PXall_add,ih,pow_succ]

theorem plain_variable_nilpotent (R : Finset PlainExp) (j : Fin 3) :
    IsNilpotent (PXall (k := k) R (plainUnitVector j)) := by
  let N := (∑ p ∈ plainStandardFinset R, p j) + 1
  have hn : N • plainUnitVector j ∉ plainStandardFinset R := by
    intro h
    have hle := Finset.single_le_sum (fun p _ => Nat.zero_le (p j)) h
    have hc : (N • plainUnitVector j) j = N := by simp
    rw [hc] at hle
    dsimp [N] at hle
    omega
  refine ⟨N,?_⟩
  rw [←plain_PXall_nsmul]
  simp [PXall,hn]

theorem plainIsLocalRing (R : Finset PlainExp) (hR : R.Nonempty) :
    IsLocalRing (PlainMonomialArtin k R) := by
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨plainAugmentationIdeal R hR,plainAugmentationIdeal_isMaximal R hR,?_⟩
  intro I hI
  have hle : plainVariableIdeal (k := k) R ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact (nilpotent_iff_mem_prime.mp (plain_variable_nilpotent R j)) I hI.isPrime
  rw [plainVariableIdeal_eq_augmentationIdeal R hR] at hle
  exact ((plainAugmentationIdeal_isMaximal R hR).eq_of_le hI.ne_top hle).symm

def PlainDirectNearlyGorenstein (k : Type*) [Field k] (R : Finset PlainExp)
    (hR : R.Nonempty) : Prop := plainAugmentationIdeal (k := k) R hR ≤ PlainTraceSubmodule k R

theorem plainMaximalIdeal_eq_augmentationIdeal (R : Finset PlainExp) (hR : R.Nonempty)
    (I : Ideal (PlainMonomialArtin k R)) (hI : I.IsMaximal) :
    I = plainAugmentationIdeal R hR := by
  have hle : plainVariableIdeal (k := k) R ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact (nilpotent_iff_mem_prime.mp (plain_variable_nilpotent R j)) I hI.isPrime
  rw [plainVariableIdeal_eq_augmentationIdeal R hR] at hle
  exact ((plainAugmentationIdeal_isMaximal R hR).eq_of_le hI.ne_top hle).symm

end
end P23.Monomial
