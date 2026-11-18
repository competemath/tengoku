import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Hecke.Coordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeCharacterAnalytic

def additiveFiberEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (π : A →+ B) (hπ : Function.Surjective π) : A ≃ B × π.ker := by
  classical
  let r : B → A := fun b => (hπ b).choose
  have hr : ∀ b, π (r b) = b := fun b => (hπ b).choose_spec
  exact {
    toFun := fun a => (π a, ⟨a - r (π a), by simp [AddMonoidHom.mem_ker, hr]⟩)
    invFun := fun p => p.2 + r p.1
    left_inv := by intro a; simp
    right_inv := by
      rintro ⟨b, k⟩
      have hk : π k = 0 := k.property
      apply Prod.ext
      · simp [hr, hk]
      · apply Subtype.ext
        simp [hr, hk] }

/--
@isnad1 id=eq.1h4v.s7.8d1da8e635e4 from=translated src=- shape=43b7de1b vocab=dfb44208
-/
theorem sum_comp_additiveHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (π : A →+ B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ a, f (π a)) = (Nat.card π.ker : ℂ) * ∑ b, f b := by
  classical
  let : Fintype π.ker := Fintype.ofFinite _
  have hid (a : A) : f (π a) = (fun p : B × π.ker => f p.1) (additiveFiberEquiv π hπ a) := rfl
  simp_rw [hid]
  rw [(additiveFiberEquiv π hπ).bijective.sum_comp (fun p : B × π.ker => f p.1)]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, Nat.card_eq_fintype_card]

/--
@isnad1 id=eq.2h4v.s8.06040046a1c9 from=translated src=- shape=7d99e8e5 vocab=446931e1
-/
theorem sum_residue_pullback_eq_zero {A R : Type*} [AddCommGroup A] [Fintype A]
    [CommRing R] [Fintype R] (π : A →+ R) (hπ : Function.Surjective π)
    (χ : MulChar R ℂ) (hχ : χ ≠ 1) : (∑ a, χ (π a)) = 0 := by
  rw [sum_comp_additiveHom π hπ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

def finCastEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun a := (a : ℕ)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv a := Fin.ext (ZMod.val_natCast_of_lt a.isLt)
  right_inv z := ZMod.natCast_zmod_val z

/--
@isnad1 id=eq.1h1v.s8.572e045b78cc from=translated src=- shape=d592e943 vocab=26b2a7ed
-/
theorem coefficients_sum_eq_zero (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    (∑ a, HeckeFamily.coefficients χ a) = 0 := by
  classical
  let : Finite (HeckeFamily.O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  calc
    (∑ a, HeckeFamily.coefficients χ a) =
        ∑ a, χ.residue (HeckeCoordinates.coordinateQuotientHom χ (e a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact HeckeCoordinates.coefficients_eq_quotient_character χ a
    _ = ∑ a : ZMod χ.period × ZMod χ.period,
        χ.residue (HeckeCoordinates.coordinateQuotientHom χ a) :=
      e.bijective.sum_comp (fun a => χ.residue (HeckeCoordinates.coordinateQuotientHom χ a))
    _ = 0 := sum_residue_pullback_eq_zero
      (HeckeCoordinates.coordinateQuotientHom χ)
      (HeckeCoordinates.coordinateQuotientHom_surjective χ) χ.residue hχ

/--
@isnad1 id=differen.2h2v.s8.56e68004bbdf from=translated src=- shape=b2041ee8 vocab=a88301e0
-/
theorem continuedLattice_differentiableAt_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (HeckeFamily.continuedLattice χ) s :=
  HeckeFamily.continuedLattice_differentiableAt χ hs₀
    (Or.inr (coefficients_sum_eq_zero χ hχ))

/--
@isnad1 id=eq.1h1v.s9.22346dbc298b from=translated src=- shape=5fc26f70 vocab=b012da65
-/
theorem residue_zero_of_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    χ.residue 0 = 0 := by
  rcases subsingleton_or_nontrivial (HeckeFamily.O ⧸ χ.modulus) with h | h
  · let := h
    exfalso
    apply hχ
    apply MulChar.ext'
    intro a
    have ha : a = 1 := Subsingleton.elim _ _
    simp [ha]
  · let := h
    exact χ.residue.map_zero

/--
@isnad1 id=eq.1h1v.s8.3e51163760a0 from=translated src=- shape=1b415cfa vocab=7c583608
-/
theorem coefficients_zero_of_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    HeckeFamily.coefficients χ (0, 0) = 0 := by
  simpa only [HeckeFamily.coefficients, HeckeFamily.elementCoeff,
    HeckeFamily.coordinateElement, Fin.val_zero, Int.natCast_zero, Int.cast_zero,
    zero_mul, zero_add, map_zero] using residue_zero_of_nonprincipal χ hχ

/--
@isnad1 id=differen.1h1v.s8.ab3a5f35cb11 from=translated src=- shape=863b18fd vocab=1b0b77fc
-/
theorem completed_entire_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (HeckeTheta.completed (HeckeFamily.coefficients χ)) := by
  intro s
  exact (HeckeTheta.pair (HeckeFamily.coefficients χ)).differentiableAt_Λ
    (Or.inr (by rw [HeckeTheta.pair_f₀, coefficients_zero_of_nonprincipal χ hχ]))
    (Or.inr (HeckeTheta.pair_g₀_eq_zero _ (coefficients_sum_eq_zero χ hχ)))

/--
@isnad1 id=differen.1h1v.s8.003032c72ba6 from=translated src=- shape=b8bb3e81 vocab=9f07a184
-/
theorem continuedLattice_entire_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) : Differentiable ℂ (HeckeFamily.continuedLattice χ) := by
  exact ((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      Complex.differentiable_one_div_Gamma).mul (completed_entire_nonprincipal χ hχ)

/--
@isnad1 id=eq.0h2v.s5.4bb649ba75e4 from=translated src=- shape=fb1619c1 vocab=2970d76a
-/
theorem continuedLattice_neg_succ (χ : HeckeFamily.Character) (n : ℕ) :
    HeckeFamily.continuedLattice χ (-((n + 1 : ℕ) : ℂ)) = 0 := by
  unfold HeckeFamily.continuedLattice HeckeTheta.latticeL
  rw [Complex.Gamma_neg_nat_eq_zero (n + 1)]
  simp

end SevenEighths.HeckeCharacterAnalytic

end

end OAI
