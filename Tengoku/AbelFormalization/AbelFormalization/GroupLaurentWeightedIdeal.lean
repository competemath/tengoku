import Tengoku.AbelFormalization.AbelFormalization.GroupLaurentRescaling
import Tengoku.AbelFormalization.AbelFormalization.MultivariateLaurentIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weighted Laurent ideals and the actual rescaled coefficient contraction

The weight of the exponent pair
`(g,d)` is `g + weight ω d`. An explicit coefficient formula identifies the
transported weight projection with exactly that component. Closure under
these actual components makes the rescaled ideal extended from its
coefficient contraction, whose height is unchanged in finite Laurent rank.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

variable {R ι G : Type*} [CommRing R] [AddCommGroup G]

/-- The inverse shear has the corresponding explicit coefficient formula.
@isnad1 id=eq.0h7v.s10.ff4c5616d6ce from=translated src=- shape=83b5ce91 vocab=71f429d8
-/
theorem groupLaurentWeightRescaling_symm_coeff (ω : ι → G)
    (f : AddMonoidAlgebra (MvPolynomial ι R) G) (g : G) (d : ι →₀ ℕ) :
    (((groupLaurentWeightRescaling ω).symm f).coeff g).coeff d =
      (f.coeff (g + Finsupp.weight ω d)).coeff d := by
  rw [groupLaurentWeightRescaling_symm, groupLaurentWeightRescaling_coeff,
    group_finsupp_weight_neg, sub_neg_eq_add]

/-- Projection onto the actual total group weight after the explicit shear.-/
def groupLaurentWeightComponent (ω : ι → G) (α : G)
    (f : AddMonoidAlgebra (MvPolynomial ι R) G) :
    AddMonoidAlgebra (MvPolynomial ι R) G :=
  (groupLaurentWeightRescaling ω).symm
    (AddMonoidAlgebra.single α ((groupLaurentWeightRescaling ω f).coeff α))

/--
@isnad1 id=eq.0h6v.s10.d6af75377ef5 from=translated src=- shape=f7daaf21 vocab=9d127918
-/
@[simp]
theorem groupLaurentWeightComponent_rescaling (ω : ι → G) (α : G)
    (f : AddMonoidAlgebra (MvPolynomial ι R) G) :
    groupLaurentWeightRescaling ω (groupLaurentWeightComponent ω α f) =
      AddMonoidAlgebra.single α ((groupLaurentWeightRescaling ω f).coeff α) :=
  (groupLaurentWeightRescaling ω).apply_symm_apply _

open scoped Classical in
/-- The projection retains precisely the original coefficients of total
weight `α`, including coefficient rings with zero divisors.
@isnad1 id=eq.0h8v.s9.b0367940dddb from=translated src=- shape=1f92a59e vocab=b0c7c43b
-/
theorem groupLaurentWeightComponent_coeff (ω : ι → G) (α : G)
    (f : AddMonoidAlgebra (MvPolynomial ι R) G) (g : G) (d : ι →₀ ℕ) :
    ((groupLaurentWeightComponent ω α f).coeff g).coeff d =
      if g + Finsupp.weight ω d = α then (f.coeff g).coeff d else 0 := by
  classical
  rw [groupLaurentWeightComponent, groupLaurentWeightRescaling_symm_coeff]
  by_cases h : g + Finsupp.weight ω d = α
  · subst α
    simp [groupLaurentWeightRescaling_coeff]
  · simp [AddMonoidAlgebra.coeff_single, h]

/-- The literal rescaled coefficient inclusion into the original Laurent
ring. Its polynomial symbols are the actual weight-zero combinations.-/
def groupLaurentRescaledCoefficientHom (ω : ι → G) :
    MvPolynomial ι R →+* AddMonoidAlgebra (MvPolynomial ι R) G :=
  (groupLaurentWeightRescaling ω).symm.toRingHom.comp
    (groupAlgebraC (MvPolynomial ι R) G)

/--
@isnad1 id=eq.0h5v.s8.6398e5cb4ff4 from=translated src=- shape=0632e7d9 vocab=a95d74ff
-/
@[simp]
theorem groupLaurentRescaledCoefficientHom_X (ω : ι → G) (i : ι) :
    groupLaurentRescaledCoefficientHom (R := R) ω (MvPolynomial.X i) =
      AddMonoidAlgebra.single (-ω i) (MvPolynomial.X i) := by
  change (groupLaurentWeightRescaling ω).symm
    (AddMonoidAlgebra.single 0 (MvPolynomial.X i)) = _
  rw [groupLaurentWeightRescaling_symm]
  exact groupLaurentWeightRescaling_single_X (fun j => -ω j) i

/-- Contract directly along the actual rescaled coefficient inclusion.-/
def groupLaurentRescaledContraction (ω : ι → G)
    (K : Ideal (AddMonoidAlgebra (MvPolynomial ι R) G)) :
    Ideal (MvPolynomial ι R) :=
  K.comap (groupLaurentRescaledCoefficientHom ω)

private theorem rescaling_algEquiv_map_eq_comap_symm {A B : Type*}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (K : Ideal A) :
    K.map e.toRingHom = K.comap e.symm.toRingHom :=
  Ideal.map_comap_of_equiv e.toRingEquiv

/--
@isnad1 id=eq.0h5v.s10.8b035d083fe0 from=translated src=- shape=b869f5f2 vocab=9c66a52a
-/
theorem groupLaurentRescaledContraction_eq (ω : ι → G)
    (K : Ideal (AddMonoidAlgebra (MvPolynomial ι R) G)) :
    groupLaurentRescaledContraction ω K =
      (K.map (groupLaurentWeightRescaling ω).toRingHom).comap
        (groupAlgebraC (MvPolynomial ι R) G) := by
  have he := rescaling_algEquiv_map_eq_comap_symm (R := R)
    (A := AddMonoidAlgebra (MvPolynomial ι R) G)
    (B := AddMonoidAlgebra (MvPolynomial ι R) G)
    (groupLaurentWeightRescaling ω) K
  rw [he, Ideal.comap_comap]
  rfl

/-- An ideal closed under its actual weighted components becomes extended
from precisely its weight-zero contraction after the explicit rescaling.
@isnad1 id=eq.1h5v.s10.0077ebbc5fe0 from=translated src=- shape=cb9b9053 vocab=e1a3da6b
-/
theorem groupLaurentWeightedIdeal_rescaled_eq_map (ω : ι → G)
    (K : Ideal (AddMonoidAlgebra (MvPolynomial ι R) G))
    (hK : ∀ f ∈ K, ∀ α, groupLaurentWeightComponent ω α f ∈ K) :
    K.map (groupLaurentWeightRescaling ω).toRingHom =
      (groupLaurentRescaledContraction ω K).map
        (groupAlgebraC (MvPolynomial ι R) G) := by
  classical
  rw [groupLaurentRescaledContraction_eq]
  apply le_antisymm
  · intro f hf
    apply (groupAlgebra_mem_map_C_iff _ f).mpr
    intro α
    obtain ⟨u, hu, rfl⟩ :=
      (Ideal.mem_map_of_equiv (groupLaurentWeightRescaling ω) f).mp hf
    have hcomponent : AddMonoidAlgebra.single α
        ((groupLaurentWeightRescaling ω u).coeff α) ∈
        K.map (groupLaurentWeightRescaling ω).toRingHom := by
      have hm :=
        Ideal.mem_map_of_mem (groupLaurentWeightRescaling ω).toRingHom (hK u hu α)
      change groupLaurentWeightRescaling ω (groupLaurentWeightComponent ω α u) ∈
        K.map (groupLaurentWeightRescaling ω).toRingHom at hm
      simpa only [groupLaurentWeightComponent_rescaling] using hm
    change groupAlgebraC (MvPolynomial ι R) G
      ((groupLaurentWeightRescaling ω u).coeff α) ∈
        K.map (groupLaurentWeightRescaling ω).toRingHom
    simpa only [groupAlgebra_inverse_single_mul] using
      (K.map (groupLaurentWeightRescaling ω).toRingHom).mul_mem_left
        (AddMonoidAlgebra.single (-α) 1) hcomponent
  · exact Ideal.map_comap_le

end AbelFormalization
