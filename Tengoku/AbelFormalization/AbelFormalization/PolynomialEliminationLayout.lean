import Tengoku.AbelFormalization.AbelFormalization.PolynomialEliminationHeight
import Tengoku.Seed.Algebra.MvPolynomial.Equiv
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Actual polynomial ring layout for elimination

The flat ring has one distinguished inverse symbol `none`, auxiliary symbols
`some (inl y)`, and retained symbols `some (inr k)`. It is explicitly identified
with the nested ring R[retained][auxiliary][inverse]. The retained contraction
is preserved as an ideal of the same actual retained coefficient ring.
-/

noncomputable section

namespace AbelFormalization

private theorem ringHom_height_map_of_bijective {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Bijective f) (I : Ideal R) :
    (I.map f).height = I.height := (RingEquiv.ofBijective f hf).height_map I

private theorem ringHom_height_comap_of_bijective {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Bijective f) (I : Ideal S) :
    (I.comap f).height = I.height := (RingEquiv.ofBijective f hf).height_comap I

private theorem algEquiv_height_map_toRingHom {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (I : Ideal S) :
    (I.map e.toRingHom).height = I.height :=
  ringHom_height_map_of_bijective e.toRingHom e.bijective I

private theorem algEquiv_height_comap_toRingHom {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (I : Ideal T) :
    (I.comap e.toRingHom).height = I.height :=
  ringHom_height_comap_of_bijective e.toRingHom e.bijective I

variable (B Keep Aux : Type*) [CommRing B]

/-- The flat ring and the ring with retained variables in the coefficients
are genuinely isomorphic as B-algebras.-/
def polynomialEliminationLayout :
    MvPolynomial (Option (Aux ⊕ Keep)) B ≃ₐ[B]
      Polynomial (MvPolynomial Aux (MvPolynomial Keep B)) :=
  (MvPolynomial.optionEquivLeft B (Aux ⊕ Keep)).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.sumAlgEquiv B Aux Keep))

/-- The actual retained-ring inclusion in the flat ring.-/
def polynomialEliminationRetainedFlat :
    MvPolynomial Keep B →+* MvPolynomial (Option (Aux ⊕ Keep)) B :=
  (MvPolynomial.rename (fun k : Keep => some (Sum.inr k))).toRingHom

/-- The actual retained-ring inclusion in the nested ring.-/
def polynomialEliminationRetainedNested :
    MvPolynomial Keep B →+* Polynomial (MvPolynomial Aux (MvPolynomial Keep B)) :=
  Polynomial.C.comp MvPolynomial.C

/-- Embed the entire pre-inverse ring in the flat ring.-/
def polynomialEliminationOldFlat :
    MvPolynomial (Aux ⊕ Keep) B →+* MvPolynomial (Option (Aux ⊕ Keep)) B :=
  (MvPolynomial.rename Option.some).toRingHom

/-- The pre-inverse ring, regrouped with the retained symbols as coefficients.-/
def polynomialEliminationOldNested :
    MvPolynomial (Aux ⊕ Keep) B →+*
      Polynomial (MvPolynomial Aux (MvPolynomial Keep B)) :=
  Polynomial.C.comp (MvPolynomial.sumAlgEquiv B Aux Keep).toRingHom

variable {B Keep Aux}

/--
@isnad1 id=eq.0h4v.s10.b7fb9f3612de from=translated src=- shape=b775cf75 vocab=f07dbb8f
-/
@[simp] theorem polynomialEliminationLayout_C (b : B) :
    polynomialEliminationLayout B Keep Aux (MvPolynomial.C b) =
      Polynomial.C (MvPolynomial.C (MvPolynomial.C b)) := by
  simp [polynomialEliminationLayout]

/--
@isnad1 id=eq.0h3v.s9.6bf526d399ed from=translated src=- shape=22e8e64c vocab=3a81e201
-/
@[simp] theorem polynomialEliminationLayout_X_none :
    polynomialEliminationLayout B Keep Aux (MvPolynomial.X none) = Polynomial.X := by
  simp [polynomialEliminationLayout]

/--
@isnad1 id=eq.0h4v.s10.19620feaeb40 from=translated src=- shape=6fbfd231 vocab=cf2e2d2b
-/
@[simp] theorem polynomialEliminationLayout_X_aux (y : Aux) :
    polynomialEliminationLayout B Keep Aux (MvPolynomial.X (some (Sum.inl y))) =
      Polynomial.C (MvPolynomial.X y) := by
  simp [polynomialEliminationLayout]

/--
@isnad1 id=eq.0h4v.s10.23bcbf38132c from=translated src=- shape=fd99a3ed vocab=e6b38c88
-/
@[simp] theorem polynomialEliminationLayout_X_retained (k : Keep) :
    polynomialEliminationLayout B Keep Aux (MvPolynomial.X (some (Sum.inr k))) =
      Polynomial.C (MvPolynomial.C (MvPolynomial.X k)) := by
  simp [polynomialEliminationLayout]

/--
@isnad1 id=eq.0h4v.s11.51fed6404ab1 from=translated src=- shape=17e291ab vocab=d85f657a
-/
@[simp] theorem polynomialEliminationLayout_symm_C_C_C (b : B) :
    (polynomialEliminationLayout B Keep Aux).symm
      (Polynomial.C (MvPolynomial.C (MvPolynomial.C b))) = MvPolynomial.C b := by
  apply (polynomialEliminationLayout B Keep Aux).injective
  simp

/--
@isnad1 id=eq.0h3v.s10.9c767d43743e from=translated src=- shape=15df6347 vocab=9fea3121
-/
@[simp] theorem polynomialEliminationLayout_symm_X :
    (polynomialEliminationLayout B Keep Aux).symm Polynomial.X = MvPolynomial.X none := by
  apply (polynomialEliminationLayout B Keep Aux).injective
  simp

/--
@isnad1 id=eq.0h4v.s10.247528647b80 from=translated src=- shape=372e01e0 vocab=f439b692
-/
@[simp] theorem polynomialEliminationLayout_symm_C_X (y : Aux) :
    (polynomialEliminationLayout B Keep Aux).symm (Polynomial.C (MvPolynomial.X y)) =
      MvPolynomial.X (some (Sum.inl y)) := by
  apply (polynomialEliminationLayout B Keep Aux).injective
  simp

/--
@isnad1 id=eq.0h4v.s11.8fb2506f9be3 from=translated src=- shape=30baa920 vocab=ede4c026
-/
@[simp] theorem polynomialEliminationLayout_symm_C_C_X (k : Keep) :
    (polynomialEliminationLayout B Keep Aux).symm
      (Polynomial.C (MvPolynomial.C (MvPolynomial.X k))) =
      MvPolynomial.X (some (Sum.inr k)) := by
  apply (polynomialEliminationLayout B Keep Aux).injective
  simp

/--
@isnad1 id=eq.0h4v.s8.b87587076cfa from=translated src=- shape=b1e24d04 vocab=c6d1945a
-/
@[simp] theorem polynomialEliminationRetainedFlat_C (b : B) :
    polynomialEliminationRetainedFlat B Keep Aux (MvPolynomial.C b) = MvPolynomial.C b := by
  simp [polynomialEliminationRetainedFlat]

/--
@isnad1 id=eq.0h4v.s7.b105a574771f from=translated src=- shape=56ed8db3 vocab=c6ad1e5c
-/
@[simp] theorem polynomialEliminationRetainedFlat_X (k : Keep) :
    polynomialEliminationRetainedFlat B Keep Aux (MvPolynomial.X k) =
      MvPolynomial.X (some (Sum.inr k)) := by
  simp [polynomialEliminationRetainedFlat]

/--
@isnad1 id=eq.0h4v.s10.78bb483e81a0 from=translated src=- shape=d7a44302 vocab=bf880589
-/
@[simp] theorem polynomialEliminationRetainedNested_apply (r : MvPolynomial Keep B) :
    polynomialEliminationRetainedNested B Keep Aux r = Polynomial.C (MvPolynomial.C r) := rfl

/-- Regrouping commutes with the exact retained-ring inclusion.
@isnad1 id=eq.0h3v.s10.4acc1b74596e from=translated src=- shape=17507d15 vocab=532195ff
-/
theorem polynomialEliminationLayout_comp_retained :
    (polynomialEliminationLayout B Keep Aux).toRingHom.comp
      (polynomialEliminationRetainedFlat B Keep Aux) =
      polynomialEliminationRetainedNested B Keep Aux := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp
  · intro k
    simp

/--
@isnad1 id=eq.0h4v.s10.c45c3a16e778 from=translated src=- shape=6897efd6 vocab=9a01996e
-/
@[simp] theorem polynomialEliminationLayout_retained (r : MvPolynomial Keep B) :
    polynomialEliminationLayout B Keep Aux (polynomialEliminationRetainedFlat B Keep Aux r) =
      Polynomial.C (MvPolynomial.C r) :=
  RingHom.congr_fun polynomialEliminationLayout_comp_retained r

/-- The pre-inverse inclusion also commutes with regrouping.
@isnad1 id=eq.0h3v.s10.de8285d87f48 from=translated src=- shape=bbc8b361 vocab=2e668d50
-/
theorem polynomialEliminationLayout_comp_old :
    (polynomialEliminationLayout B Keep Aux).toRingHom.comp
      (polynomialEliminationOldFlat B Keep Aux) =
      polynomialEliminationOldNested B Keep Aux := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp [polynomialEliminationOldFlat, polynomialEliminationOldNested]
  · rintro (y | k)
    · simp [polynomialEliminationOldFlat, polynomialEliminationOldNested]
    · simp [polynomialEliminationOldFlat, polynomialEliminationOldNested]

/--
@isnad1 id=eq.0h4v.s11.ed4fd2bd5e23 from=translated src=- shape=32bf750d vocab=11deca49
-/
@[simp] theorem polynomialEliminationLayout_old (P : MvPolynomial (Aux ⊕ Keep) B) :
    polynomialEliminationLayout B Keep Aux (polynomialEliminationOldFlat B Keep Aux P) =
      Polynomial.C (MvPolynomial.sumAlgEquiv B Aux Keep P) :=
  RingHom.congr_fun polynomialEliminationLayout_comp_old P

/-- Mapping the ambient ideal along the actual ring equivalence preserves
its contraction to the retained ring, as an equality of ideals of that ring.
@isnad1 id=eq.0h4v.s10.23ce211204a0 from=translated src=- shape=4ac89030 vocab=f2abe16e
-/
theorem polynomialEliminationLayout_contraction_map
    (Q : Ideal (MvPolynomial (Option (Aux ⊕ Keep)) B)) :
    (Q.map (polynomialEliminationLayout B Keep Aux).toRingHom).comap
      (polynomialEliminationRetainedNested B Keep Aux) =
      Q.comap (polynomialEliminationRetainedFlat B Keep Aux) := by
  rw [← polynomialEliminationLayout_comp_retained, ← Ideal.comap_comap]
  rw [Ideal.comap_map_of_bijective
    (I := Q) (polynomialEliminationLayout B Keep Aux).toRingHom
    (polynomialEliminationLayout B Keep Aux).bijective]

/-- The reverse ideal transport has the same exact retained contraction.
@isnad1 id=eq.0h4v.s11.d890e61a07ec from=translated src=- shape=8ab351f7 vocab=cc8628e5
-/
theorem polynomialEliminationLayout_contraction_comap
    (Q : Ideal (Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))) :
    (Q.comap (polynomialEliminationLayout B Keep Aux).toRingHom).comap
      (polynomialEliminationRetainedFlat B Keep Aux) =
      Q.comap (polynomialEliminationRetainedNested B Keep Aux) := by
  rw [Ideal.comap_comap, polynomialEliminationLayout_comp_retained]

attribute [local irreducible] polynomialEliminationLayout

/-- The ambient ideal height is unchanged by the flat/nested identification.
@isnad1 id=eq.0h4v.s10.fc3ba58c661e from=translated src=- shape=a201f461 vocab=79e7dad3
-/
theorem polynomialEliminationLayout_height_map
    (Q : Ideal (MvPolynomial (Option (Aux ⊕ Keep)) B)) :
    Ideal.height (R := Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))
        (Q.map (polynomialEliminationLayout B Keep Aux).toRingHom) =
      Ideal.height (R := MvPolynomial (Option (Aux ⊕ Keep)) B) Q := by
  have h := algEquiv_height_map_toRingHom (R := B)
    (S := MvPolynomial (Option (Aux ⊕ Keep)) B)
    (T := Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))
    (polynomialEliminationLayout B Keep Aux) Q
  exact h

/--
@isnad1 id=eq.0h4v.s10.4331535e9ed1 from=translated src=- shape=54884182 vocab=b62d1384
-/
theorem polynomialEliminationLayout_height_comap
    (Q : Ideal (Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))) :
    Ideal.height (R := MvPolynomial (Option (Aux ⊕ Keep)) B)
        (Q.comap (polynomialEliminationLayout B Keep Aux).toRingHom) =
      Ideal.height (R := Polynomial (MvPolynomial Aux (MvPolynomial Keep B))) Q := by
  have h := algEquiv_height_comap_toRingHom (R := B)
    (S := MvPolynomial (Option (Aux ⊕ Keep)) B)
    (T := Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))
    (polynomialEliminationLayout B Keep Aux) Q
  exact h

section FiniteAuxiliary

/-- The flat retained contraction is precisely the previous literal
elimination contraction after regrouping; no substitute coefficient ring is used.
@isnad1 id=eq.0h4v.s10.0a2be02b525e from=translated src=- shape=467b0863 vocab=611869a8
-/
theorem polynomialEliminationLayout_eliminationContraction (a : ℕ)
    (Q : Ideal (MvPolynomial (Option (Fin a ⊕ Keep)) B)) :
    polynomialEliminationContraction a
      (Q.map (polynomialEliminationLayout B Keep (Fin a)).toRingHom) =
      Q.comap (polynomialEliminationRetainedFlat B Keep (Fin a)) := by
  unfold polynomialEliminationContraction
  rw [Ideal.comap_comap]
  exact polynomialEliminationLayout_contraction_map Q

variable [IsNoetherianRing B] [Finite Keep]

end FiniteAuxiliary

end AbelFormalization
