import Tengoku.Seed.Analysis.SpecificLimits.Normed
import Tengoku.Seed.Analysis.Normed.Operator.Mul
import Tengoku.Seed.Analysis.Normed.Operator.Completeness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Division by a small perturbation in a real Banach algebra

A continuous linear operator `Q` which is a left inverse to multiplication
by `s` provides division by every sufficiently small perturbation `f` of `s`.
The quotient is constructed from the convergent Neumann inverse of
`id - Q ∘ mulLeft (s - f)`. The remainder is the actual difference `g - f*q`
and belongs to the kernel of `Q`.

This is an abstract Banach algebra theorem. It does not assert that a space
of analytic coefficients has the required norm, product, or division map.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- The error operator for division by a perturbation of `s`.-/
def divisionPerturbation (Q : B →L[ℝ] B) (s f : B) : B →L[ℝ] B :=
  Q.comp (ContinuousLinearMap.mul ℝ B (s - f))

/--
@isnad1 id=eq.0h5v.s8.c040deb08990 from=translated src=- shape=1267371b vocab=129c0c2f
-/
@[simp]
theorem divisionPerturbation_apply (Q : B →L[ℝ] B) (s f a : B) :
    divisionPerturbation Q s f a = Q ((s - f) * a) := rfl

/--
@isnad1 id=le.0h4v.s8.087e2280478b from=translated src=- shape=a54466df vocab=5b1e31ab
-/
theorem norm_divisionPerturbation_le (Q : B →L[ℝ] B) (s f : B) :
    ‖divisionPerturbation Q s f‖ ≤ ‖Q‖ * ‖s - f‖ := by
  exact (Q.opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_apply_le ℝ B (s - f))
      (norm_nonneg Q))

/-- The invertible operator in the Neumann construction is exactly division
followed by multiplication by the perturbed element.
@isnad1 id=eq.1h5v.s10.6034fbe2f20f from=translated src=- shape=0a68b466 vocab=129c0c2f
-/
theorem one_sub_divisionPerturbation_apply (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (a : B) :
    (1 - divisionPerturbation Q s f : B →L[ℝ] B) a = Q (f * a) := by
  change a - Q ((s - f) * a) = Q (f * a)
  rw [sub_mul, map_sub, hs]
  abel

variable [CompleteSpace B]

/-- The actual quotient operator, obtained from the Neumann inverse.-/
def banachDivisionQuotient (Q : B →L[ℝ] B) (s f : B)
    (hT : ‖divisionPerturbation Q s f‖ < 1) : B →L[ℝ] B :=
  (↑(Units.oneSub (divisionPerturbation Q s f) hT)⁻¹ : B →L[ℝ] B).comp Q

/-- Multiplication by the perturbed element followed by `Q` inverts the
quotient operator on the right-hand side of the division equation.
@isnad1 id=eq.2h5v.s9.a39270af0ada from=translated src=- shape=6a53ca9f vocab=c5be14ea
-/
theorem banachDivisionQuotient_equation (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    Q (f * banachDivisionQuotient Q s f hT g) = Q g := by
  rw [← one_sub_divisionPerturbation_apply Q s f hs]
  have he := congrArg (fun L : B →L[ℝ] B => L (Q g))
    (Units.oneSub (divisionPerturbation Q s f) hT).val_inv
  exact he

/-- The quotient of `f*a` is exactly `a`.
@isnad1 id=eq.2h5v.s9.3155d27e977a from=translated src=- shape=e284329c vocab=c5be14ea
-/
theorem banachDivisionQuotient_mul (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (a : B) :
    banachDivisionQuotient Q s f hT (f * a) = a := by
  change (↑(Units.oneSub (divisionPerturbation Q s f) hT)⁻¹ : B →L[ℝ] B) (Q (f * a)) = a
  rw [← one_sub_divisionPerturbation_apply Q s f hs]
  have he := congrArg (fun L : B →L[ℝ] B => L a)
    (Units.oneSub (divisionPerturbation Q s f) hT).inv_val
  exact he

/-- The constructed quotient makes the actual remainder belong to `ker Q`.
@isnad1 id=eq.2h5v.s9.bcf437cab23b from=translated src=- shape=546485bc vocab=6abee89c
-/
theorem banachDivisionQuotient_spec (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    Q (g - f * banachDivisionQuotient Q s f hT g) = 0 := by
  rw [map_sub, banachDivisionQuotient_equation Q s f hs hT, sub_self]

/-- The vanishing of `Q` on the remainder determines the quotient uniquely.
@isnad1 id=eq.3h6v.s9.58a13f05e278 from=translated src=- shape=085903a1 vocab=6abee89c
-/
theorem banachDivisionQuotient_unique (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1)
    (g q : B) (hq : Q (g - f * q) = 0) :
    q = banachDivisionQuotient Q s f hT g := by
  rw [map_sub, sub_eq_zero] at hq
  calc
    q = banachDivisionQuotient Q s f hT (f * q) :=
      (banachDivisionQuotient_mul Q s f hs hT q).symm
    _ = banachDivisionQuotient Q s f hT g := by
      change (↑(Units.oneSub (divisionPerturbation Q s f) hT)⁻¹ : B →L[ℝ] B) (Q (f * q)) =
        (↑(Units.oneSub (divisionPerturbation Q s f) hT)⁻¹ : B →L[ℝ] B) (Q g)
      rw [hq]

/--
@isnad1 id=existsun.2h5v.s9.0985eac8b079 from=translated src=- shape=30c4edcb vocab=8259d1de
-/
theorem banachDivision_existsUnique (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    ∃! q : B, Q (g - f * q) = 0 :=
  ⟨banachDivisionQuotient Q s f hT g, banachDivisionQuotient_spec Q s f hs hT g,
    fun q hq => banachDivisionQuotient_unique Q s f hs hT g q hq⟩

/-- The actual remainder operator.-/
def banachDivisionRemainder (Q : B →L[ℝ] B) (s f : B)
    (hT : ‖divisionPerturbation Q s f‖ < 1) : B →L[ℝ] B :=
  1 - (ContinuousLinearMap.mul ℝ B f).comp (banachDivisionQuotient Q s f hT)

/--
@isnad1 id=eq.1h5v.s9.5fd9c5325b45 from=translated src=- shape=b9951a11 vocab=a389fd9d
-/
@[simp]
theorem banachDivisionRemainder_apply (Q : B →L[ℝ] B) (s f : B)
    (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    banachDivisionRemainder Q s f hT g = g - f * banachDivisionQuotient Q s f hT g := rfl

/--
@isnad1 id=eq.1h5v.s9.acda3fa5982d from=translated src=- shape=eccd2901 vocab=cad946fd
-/
theorem banachDivision_identity (Q : B →L[ℝ] B) (s f : B)
    (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    g = f * banachDivisionQuotient Q s f hT g + banachDivisionRemainder Q s f hT g := by
  rw [banachDivisionRemainder_apply]
  abel

/--
@isnad1 id=mem.2h5v.s9.c79574d2367c from=translated src=- shape=7b17d53b vocab=ed8c9f2a
-/
theorem banachDivisionRemainder_mem_ker (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    banachDivisionRemainder Q s f hT g ∈ LinearMap.ker Q.toLinearMap :=
  banachDivisionQuotient_spec Q s f hs hT g

/-- Fixed-point form of the quotient, used to bound its norm.
@isnad1 id=eq.2h5v.s10.475f82548c46 from=translated src=- shape=754cb3d2 vocab=ae817424
-/
theorem banachDivisionQuotient_fixed_point (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    banachDivisionQuotient Q s f hT g =
      Q g + divisionPerturbation Q s f (banachDivisionQuotient Q s f hT g) := by
  apply sub_eq_iff_eq_add.mp
  exact (one_sub_divisionPerturbation_apply Q s f hs _).trans
    (banachDivisionQuotient_equation Q s f hs hT g)

/-- The sharper quotient bound in terms of the norm of `Q g`.
@isnad1 id=le.2h5v.s9.e6b72fd508e8 from=translated src=- shape=ddc00037 vocab=7ce140d4
-/
theorem norm_banachDivisionQuotient_le (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    ‖banachDivisionQuotient Q s f hT g‖ ≤ ‖Q g‖ / (1 - ‖divisionPerturbation Q s f‖) := by
  have hnorm : ‖banachDivisionQuotient Q s f hT g‖ ≤
      ‖Q g‖ + ‖divisionPerturbation Q s f‖ * ‖banachDivisionQuotient Q s f hT g‖ := by
    calc
      ‖banachDivisionQuotient Q s f hT g‖ =
          ‖Q g + divisionPerturbation Q s f (banachDivisionQuotient Q s f hT g)‖ :=
        congrArg norm (banachDivisionQuotient_fixed_point Q s f hs hT g)
      _ ≤ ‖Q g‖ + ‖divisionPerturbation Q s f (banachDivisionQuotient Q s f hT g)‖ :=
        norm_add_le _ _
      _ ≤ ‖Q g‖ + ‖divisionPerturbation Q s f‖ * ‖banachDivisionQuotient Q s f hT g‖ :=
        add_le_add le_rfl ((divisionPerturbation Q s f).le_opNorm _)
  apply (le_div_iff₀ (sub_pos.mpr hT)).mpr
  nlinarith

/-- A bound uniform in the right-hand side of the division problem.
@isnad1 id=le.2h5v.s9.5f1472c4db15 from=translated src=- shape=23b9ce80 vocab=7ce140d4
-/
theorem norm_banachDivisionQuotient_le_opNorm (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    ‖banachDivisionQuotient Q s f hT g‖ ≤
      ‖Q‖ * ‖g‖ / (1 - ‖divisionPerturbation Q s f‖) :=
  (norm_banachDivisionQuotient_le Q s f hs hT g).trans
    (div_le_div_of_nonneg_right (Q.le_opNorm g) (sub_pos.mpr hT).le)

/-- The norm of the bounded quotient operator itself.
@isnad1 id=le.2h4v.s9.972bc66e12c2 from=translated src=- shape=dae16064 vocab=7ce140d4
-/
theorem opNorm_banachDivisionQuotient_le (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) :
    ‖banachDivisionQuotient Q s f hT‖ ≤ ‖Q‖ / (1 - ‖divisionPerturbation Q s f‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg Q) (sub_pos.mpr hT).le)
  intro g
  convert norm_banachDivisionQuotient_le_opNorm Q s f hs hT g using 1
  ring

/-- A corresponding bound for the actual remainder.
@isnad1 id=le.2h5v.s9.ce20079a3f53 from=translated src=- shape=eabf4194 vocab=4de0059e
-/
theorem norm_banachDivisionRemainder_le (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hT : ‖divisionPerturbation Q s f‖ < 1) (g : B) :
    ‖banachDivisionRemainder Q s f hT g‖ ≤
      ‖g‖ + ‖f‖ * (‖Q‖ * ‖g‖ / (1 - ‖divisionPerturbation Q s f‖)) := by
  rw [banachDivisionRemainder_apply]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_banachDivisionQuotient_le_opNorm Q s f hs hT g) (norm_nonneg f))))

/-- A sufficient smallness condition expressed directly in `s-f` and `Q`.
@isnad1 id=existsun.2h5v.s9.04125823f615 from=translated src=- shape=567d2ba9 vocab=68ec1dc1
-/
theorem banachDivision_existsUnique_of_norm_mul_lt_one (Q : B →L[ℝ] B) (s f : B)
    (hs : ∀ a : B, Q (s * a) = a) (hsmall : ‖Q‖ * ‖s - f‖ < 1) (g : B) :
    ∃! q : B, Q (g - f * q) = 0 :=
  banachDivision_existsUnique Q s f hs ((norm_divisionPerturbation_le Q s f).trans_lt hsmall) g

end AbelFormalization
