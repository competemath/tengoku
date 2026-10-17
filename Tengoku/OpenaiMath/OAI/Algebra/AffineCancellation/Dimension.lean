import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Cylinder

namespace OAI

noncomputable section

namespace ComplexCancellation

/--
@isnad1 id=finitety.0h0v.s7.b50fcb2b2f93 from=translated src=- shape=25b03439 vocab=5df4c8e8
-/
theorem finiteType : Algebra.FiniteType ℂ A := inferInstance

/--
@isnad1 id=isdomain.0h0v.s5.d5045cfdea7b from=translated src=- shape=49959d42 vocab=06f2b23d
-/
instance domain : IsDomain A :=
  Function.Injective.isDomain Cylinder.coefficientMap (by
    intro r s hrs
    apply Polynomial.C_injective
    apply Cylinder.equivalence.injective
    simpa only [Cylinder.equivalence, AlgEquiv.ofAlgHom_apply,
      Cylinder.forward_C] using hrs)

/--
@isnad1 id=isnoethe.0h0v.s5.846b3ecb3c70 from=translated src=- shape=49959d42 vocab=679cf584
-/
instance noetherian : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A

/--
@isnad1 id=eq.0h0v.s6.7b08bfb69e90 from=translated src=- shape=8c4e12ea vocab=a594b319
-/
theorem dimension : ringKrullDim A = 4 := by
  have hd : ringKrullDim A + 1 = 5 := by
    rw [← Polynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_of_ringEquiv Cylinder.equivalence.toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add]
    simp
  generalize ringKrullDim A = d at *
  induction d using WithBot.recBotCoe with
  | bot => simp at hd
  | coe d =>
    have hd' : d + 1 = 5 := WithBot.coe_inj.mp (by
      simpa only [WithBot.coe_add, WithBot.coe_one, WithBot.coe_ofNat] using hd)
    induction d using ENat.recTopCoe with
    | top => simp at hd'
    | coe n =>
      have hd'' : n + 1 = 5 := by exact_mod_cast hd'
      have hn : n = 4 := by omega
      subst n
      rfl

/--
@isnad1 id=nonempty.0h0v.s8.906245c5d2b6 from=translated src=- shape=b2c3b67a vocab=a0451930
-/
theorem stabilization : Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) :=
  ⟨Cylinder.equivalence⟩

end ComplexCancellation

end

end OAI
