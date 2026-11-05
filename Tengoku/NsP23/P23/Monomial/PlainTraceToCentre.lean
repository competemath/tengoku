import Tengoku.NsP23.P23.Monomial.PlainTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Monomial
noncomputable section
variable {k : Type*} [Field k]

/--
@isnad1 id=plaindir.3h5v.s9.f2057cf6e180 from=translated src=- shape=17ec457a vocab=443b0719
-/
theorem plain_rootSource_isDirectionalCentre (R : Finset PlainExp) (j : Fin 3)
    (hj : plainUnitVector j ∈ plainStandardFinset R)
    (F : PlainOmega k R →ₗ[PlainMonomialArtin k R] PlainMonomialArtin k R)
    (s : PlainExp) (hs : s ∈ R)
    (hc : plainCoeffAt R ⟨plainUnitVector j,hj⟩ (F (PU R (plainRootIndex R s hs))) ≠ 0) :
    PlainDirectionalCentre R j s := by
  refine ⟨hs,?_⟩
  intro r hr hpos
  let q := plainPredecessor j r
  have hqstd : q ∈ plainStandardFinset R := (mem_plainStandardFinset R q).mpr
    ⟨r,hr,plainPredecessor_divides j r⟩
  let qi : PlainMonomialIndex R := ⟨q,hqstd⟩
  let ei : PlainMonomialIndex R := ⟨plainUnitVector j,hj⟩
  let ri := plainRootIndex R r hr
  have hsum : qi.1+ei.1=ri.1 := plainPredecessor_add_unitVector j r hpos
  by_contra hnot
  have hann : PX R qi.1 qi.2 • PU R (plainRootIndex R s hs) = (0 : PlainOmega k R) :=
    (PX_smul_plainRootDual_eq_zero_iff R s hs qi).mpr hnot
  have hz : PX R qi.1 qi.2 * F (PU R (plainRootIndex R s hs)) = 0 := by
    have := F.map_smul (PX R qi.1 qi.2) (PU R (plainRootIndex R s hs))
    rw [hann,map_zero] at this
    exact this.symm
  have hcoeff := congrArg (plainCoeffAt (k := k) R ri) hz
  rw [plainCoeffAt_PX_mul R qi ei ri hsum] at hcoeff
  exact hc (by simpa [ei] using hcoeff)

def PlainVariablesInTrace (k : Type*) [Field k] (R : Finset PlainExp)
    (hv : PlainVariablesSurvive R) : Prop :=
  ∀ j, PX (k := k) R (plainUnitVector j)
    ((mem_plainStandardFinset R _).mpr (hv j)) ∈ PlainTraceSubmodule k R

/--
@isnad1 id=hasplain.5h2v.s5.4788d6d783c4 from=translated src=- shape=3539f14b vocab=9584a8d4
-/
theorem plain_hasDirectionalCentres_of_variablesInTrace (R : Finset PlainExp)
    (hR : R.Nonempty) (hcard : 2 ≤ R.card) (ha : PlainRootAntichain R)
    (hv : PlainVariablesSurvive R) (ht : PlainVariablesInTrace k R hv) :
    HasPlainDirectionalCentres R := by
  intro j
  let hj := (mem_plainStandardFinset R _).mpr (hv j)
  obtain ⟨F,s,hs,hc⟩ := plain_exists_root_image_with_variable_coeff_of_mem_trace
    R hR hcard ha j hj (ht j)
  exact ⟨s,plain_rootSource_isDirectionalCentre R j hj F s hs hc⟩

end
end P23.Monomial
