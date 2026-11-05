import Tengoku.NsP23.P23.Monomial.PlainArtin
import Tengoku.NsP23.P23.Monomial.PlainMonomialIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Monomial
noncomputable section
local instance plainQuotientDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {k : Type*} [Field k]

namespace PlainMonomialArtin
def PXall (R : Finset PlainExp) (p : PlainExp) : PlainMonomialArtin k R :=
  if hp : p ∈ plainStandardFinset R then PX R p hp else 0

/--
@isnad1 id=eq.0h2v.s5.5545f4b5dd82 from=translated src=- shape=1f4cf7c0 vocab=4300b7fb
-/
@[simp] theorem PXall_zero (R : Finset PlainExp) : PXall (k := k) R 0 = 1 := rfl

/--
@isnad1 id=eq.0h4v.s6.a2ef754e2b18 from=translated src=- shape=8de983d1 vocab=4383b287
-/
theorem PXall_add (R : Finset PlainExp) (p q : PlainExp) :
    PXall (k := k) R (p+q) = PXall R p * PXall R q := by
  by_cases hp : p ∈ plainStandardFinset R
  · by_cases hq : q ∈ plainStandardFinset R
    · simp [PXall,hp,hq,PX_mul_PX]
    · have hn : p+q ∉ plainStandardFinset R :=
        fun h => hq (mem_plainStandardFinset_of_add_mem_right R h)
      simp [PXall,hq,hn]
  · have hn : p+q ∉ plainStandardFinset R :=
      fun h => hp (mem_plainStandardFinset_of_add_mem_left R h)
    simp [PXall,hp,hn]

def exponentHom (R : Finset PlainExp) : Multiplicative PlainExp →* PlainMonomialArtin k R where
  toFun p := PXall R p.toAdd
  map_one' := PXall_zero R
  map_mul' p q := PXall_add R p.toAdd q.toAdd
end PlainMonomialArtin

def plainPolyToArtin (k : Type*) [Field k] (R : Finset PlainExp) :
    MvPolynomial (Fin 3) k →ₐ[k] PlainMonomialArtin k R :=
  AddMonoidAlgebra.lift k _ PlainExp (PlainMonomialArtin.exponentHom R)

/--
@isnad1 id=eq.0h4v.s9.9312633fd2f9 from=translated src=- shape=1edcf33e vocab=fd8d1fdd
-/
theorem plainPolyToArtin_monomial (k : Type*) [Field k] (R : Finset PlainExp)
    (p : PlainExp) (r : k) :
    plainPolyToArtin k R (MvPolynomial.monomial p r) =
      r • PlainMonomialArtin.PXall (k := k) R p :=
  AddMonoidAlgebra.lift_single _ p r

/--
@isnad1 id=surjecti.0h2v.s8.931773aa7f7e from=translated src=- shape=06be8090 vocab=ce2b767b
-/
theorem plainPolyToArtin_surjective (k : Type*) [Field k] (R : Finset PlainExp) :
    Function.Surjective (plainPolyToArtin k R) := by
  intro x
  refine ⟨x.coeff.sum (fun p r => MvPolynomial.monomial p.1 r),?_⟩
  rw [map_finsuppSum]
  conv_rhs => rw [basis_expansion x]
  apply Finsupp.sum_congr
  intro p _
  simp [plainPolyToArtin_monomial,PlainMonomialArtin.PXall,p.2]

/--
@isnad1 id=iff.0h2v.s5.210706ce9d53 from=translated src=- shape=27998834 vocab=f702cfc2
-/
theorem killed_iff_border_divisor (R : Finset PlainExp) (p : PlainExp) :
    p ∉ plainStandardSet R ↔ ∃ g ∈ plainBorderFinset R, plainDivides g p := by
  constructor
  · intro hp
    let K := (Set.finite_Iic p).toFinset.filter (fun q => q ∉ plainStandardSet R)
    have hpK : p ∈ K := by simp [K,hp]
    obtain ⟨g,hg,hmin⟩ := K.exists_min_image plainWeight ⟨p,hpK⟩
    have hgp : plainDivides g p := by
      have hle : g ≤ p := by simpa [K] using (Finset.mem_filter.mp hg).1
      exact fun j => hle j
    have hgn := (Finset.mem_filter.mp hg).2
    refine ⟨g,(plain_border_iff_minimalKilled R g).mpr ⟨hgn,?_⟩,hgp⟩
    intro q hqg hqne
    by_contra hqn
    have hqK : q ∈ K := by
      simp only [K,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_Iic]
      exact ⟨plainDivides_trans hqg hgp,hqn⟩
    have hle := hmin q hqK
    have hlt := plainWeight_strict hqg hqne
    omega
  · rintro ⟨g,hg,hgp⟩ hp
    exact ((plain_border_iff_minimalKilled R g).mp hg).1 (plainStandard_downward R hp hgp)

/--
@isnad1 id=eq.0h4v.s8.99952e28b9a7 from=translated src=- shape=9c7f8121 vocab=ace138ba
-/
theorem coeff_plainPolyToArtin (k : Type*) [Field k] (R : Finset PlainExp)
    (f : MvPolynomial (Fin 3) k) (q : PlainMonomialIndex R) :
    (plainPolyToArtin k R f).coeff q = f.coeff q.1 := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [hf,hg]
  | monomial p r =>
    by_cases hp : p ∈ plainStandardFinset R
    · simp [plainPolyToArtin_monomial,PlainMonomialArtin.PXall,hp,
        PlainMonomialArtin.coeff_PX,MvPolynomial.coeff_monomial,Finsupp.single_apply,
        Subtype.ext_iff,eq_comm]
    · have hn : q.1 ≠ p := fun h => hp (h ▸ q.2)
      simp [plainPolyToArtin_monomial,PlainMonomialArtin.PXall,hp,
        MvPolynomial.coeff_monomial,hn,Ne.symm hn]

/--
@isnad1 id=eq.0h2v.s8.613c99900f2c from=translated src=- shape=181d92ff vocab=de4234a6
-/
theorem plainPolyToArtin_kernel (k : Type*) [Field k] (R : Finset PlainExp) :
    RingHom.ker (plainPolyToArtin k R).toRingHom =
      plainMonomialIdeal k (plainBorderFinset R) := by
  ext f
  rw [RingHom.mem_ker,mem_plainMonomialIdeal_iff_support]
  constructor
  · intro hf p hp
    apply (killed_iff_border_divisor R p).mp
    intro hstd
    let q : PlainMonomialIndex R := ⟨p,(mem_plainStandardFinset R p).mpr hstd⟩
    have hc := congrArg (fun x : PlainMonomialArtin k R => x.coeff q) hf
    change (plainPolyToArtin k R f).coeff q = 0 at hc
    rw [coeff_plainPolyToArtin] at hc
    exact (MvPolynomial.mem_support_iff.mp hp) hc
  · intro hf
    apply PlainMonomialArtin.ext
    ext q
    change (plainPolyToArtin k R f).coeff q = 0
    rw [coeff_plainPolyToArtin]
    change f.coeff q.1 = 0
    by_contra hn
    have hb := hf q.1 (MvPolynomial.mem_support_iff.mpr hn)
    exact (killed_iff_border_divisor R q.1).mpr hb
      ((mem_plainStandardFinset R q.1).mp q.2)

def plainQuotientEquiv (k : Type*) [Field k] (R : Finset PlainExp) :
    (MvPolynomial (Fin 3) k ⧸ plainMonomialIdeal k (plainBorderFinset R)) ≃ₐ[k]
      PlainMonomialArtin k R := by
  rw [←plainPolyToArtin_kernel k R]
  exact Ideal.quotientKerAlgEquivOfSurjective (plainPolyToArtin_surjective k R)

/--
@isnad1 id=iff.0h3v.s6.5bd48e50adbc from=translated src=- shape=ed72b06d vocab=0e670b48
-/
theorem plain_PXall_nonzero_iff (R : Finset PlainExp) (p : PlainExp) :
    PlainMonomialArtin.PXall (k := k) R p ≠ 0 ↔ p ∈ plainStandardSet R := by
  classical
  by_cases hp : p ∈ plainStandardFinset R
  · simp [PlainMonomialArtin.PXall, hp, PX_ne_zero,
      (mem_plainStandardFinset R p).mp hp]
  · simp [PlainMonomialArtin.PXall, hp, ← mem_plainStandardFinset R p]

/--
@isnad1 id=iff.0h2v.s6.96782cd3c7d2 from=translated src=- shape=35629d79 vocab=e172c965
-/
theorem plainVariablesSurvive_iff_nonzero (R : Finset PlainExp) :
    PlainVariablesSurvive R ↔
      ∀ j, PlainMonomialArtin.PXall (k := k) R (plainUnitVector j) ≠ 0 := by
  simp only [PlainVariablesSurvive, plain_PXall_nonzero_iff]

end
end P23.Monomial
