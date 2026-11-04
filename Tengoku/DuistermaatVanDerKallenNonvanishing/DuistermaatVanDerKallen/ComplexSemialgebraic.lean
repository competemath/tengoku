import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PolynomialRealParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Semialgebraicity in complex coordinates means semialgebraicity in their
real and imaginary parts. The coordinate identification is a homeomorphism. -/

namespace DuistermaatVanDerKallen
noncomputable section

def realCoordinates {ι : Type*} (z : ι → ℂ) : (ι ⊕ ι) → ℝ :=
  Sum.elim (fun i => (z i).re) (fun i => (z i).im)

/--
@isnad1 id=eq.0h2v.s4.1cb826d8c380 from=translated src=- shape=6b578125 vocab=efac434f
-/
@[simp] theorem complexCoordinates_realCoordinates {ι : Type*} (z : ι → ℂ) :
    complexCoordinates (realCoordinates z) = z := by
  funext i
  apply Complex.ext <;> rfl

/--
@isnad1 id=eq.0h2v.s4.799cfdaaff92 from=translated src=- shape=3bb90e3b vocab=dce48d2d
-/
@[simp] theorem realCoordinates_complexCoordinates {ι : Type*} (x : (ι ⊕ ι) → ℝ) :
    realCoordinates (complexCoordinates x) = x := by
  funext i
  cases i <;> rfl

def complexCoordinatesHomeomorph (ι : Type*) : ((ι ⊕ ι) → ℝ) ≃ₜ (ι → ℂ) where
  toFun := complexCoordinates
  invFun := realCoordinates
  left_inv := realCoordinates_complexCoordinates
  right_inv := complexCoordinates_realCoordinates
  continuous_toFun := by
    apply continuous_pi
    intro i
    change Continuous (fun x : (ι ⊕ ι) → ℝ =>
      Complex.equivRealProdCLM.symm (x (.inl i), x (.inr i)))
    exact Complex.equivRealProdCLM.symm.continuous.comp
      ((continuous_apply (Sum.inl i : ι ⊕ ι)).prodMk (continuous_apply (Sum.inr i : ι ⊕ ι)))
  continuous_invFun := by
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact Complex.continuous_re.comp (continuous_apply i)
    | inr i => exact Complex.continuous_im.comp (continuous_apply i)

/-- The standard real-coordinate meaning of a semialgebraic subset of complex
coordinate space. For finite `ι` this is an ordinary finite-dimensional real set.-/
def IsComplexSemialgebraic {ι : Type*} (S : Set (ι → ℂ)) : Prop :=
  IsSemialgebraic (ι ⊕ ι) (complexCoordinates ⁻¹' S)

namespace IsComplexSemialgebraic
variable {ι : Type*}

/--
@isnad1 id=iscomple.2h3v.s5.9234c8e812eb from=translated src=- shape=895eafe5 vocab=0a527a84
-/
theorem inter {S T : Set (ι → ℂ)} (hS : IsComplexSemialgebraic S) (hT : IsComplexSemialgebraic T) :
    IsComplexSemialgebraic (S ∩ T) := IsSemialgebraic.inter hS hT

/--
@isnad1 id=iscomple.2h3v.s5.48f7cabed06d from=translated src=- shape=895eafe5 vocab=6b269508
-/
theorem union {S T : Set (ι → ℂ)} (hS : IsComplexSemialgebraic S) (hT : IsComplexSemialgebraic T) :
    IsComplexSemialgebraic (S ∪ T) := IsSemialgebraic.union hS hT

/--
@isnad1 id=iscomple.1h2v.s4.570b699b64af from=translated src=- shape=d8d7bd23 vocab=35c5621a
-/
theorem compl {S : Set (ι → ℂ)} (hS : IsComplexSemialgebraic S) : IsComplexSemialgebraic Sᶜ :=
  IsSemialgebraic.compl hS

/--
@isnad1 id=iscomple.1h3v.s5.7f4c8a1422f2 from=translated src=- shape=a8022d8e vocab=45dd34e5
-/
theorem forall_finite {κ : Type*} [Finite κ] (f : κ → Set (ι → ℂ))
    (hf : ∀ k, IsComplexSemialgebraic (f k)) : IsComplexSemialgebraic {z | ∀ k, z ∈ f k} :=
  IsSemialgebraic.forall_finite (fun k => complexCoordinates ⁻¹' f k) hf

/--
@isnad1 id=iscomple.0h2v.s6.b4b2635f2aa4 from=translated src=- shape=769316ef vocab=a67a4623
-/
theorem polynomial_zeroSet (p : MvPolynomial ι ℂ) :
    IsComplexSemialgebraic {z | MvPolynomial.eval z p = 0} := by
  obtain ⟨r, s, hrs⟩ := polynomial_real_parts p
  have he : complexCoordinates ⁻¹' {z | MvPolynomial.eval z p = 0} =
      {x | MvPolynomial.eval x r = 0} ∩ {x | MvPolynomial.eval x s = 0} := by
    ext x
    simp [Complex.ext_iff, (hrs x).1, (hrs x).2]
  unfold IsComplexSemialgebraic
  rw [he]
  exact (IsSemialgebraic.zeroSet r).inter (IsSemialgebraic.zeroSet s)

/--
@isnad1 id=iscomple.1h3v.s5.70e4426e3312 from=translated src=- shape=9100291c vocab=c82014db
-/
theorem coord_norm_le (i : ι) {ε : ℝ} (hε : 0 ≤ ε) :
    IsComplexSemialgebraic {z : ι → ℂ | ‖z i‖ ≤ ε} := by
  have h := IsSemialgebraic.le
    ((MvPolynomial.X (.inl i) : MvPolynomial (ι ⊕ ι) ℝ) ^ 2 + MvPolynomial.X (.inr i) ^ 2)
    (MvPolynomial.C (ε ^ 2))
  simpa [IsComplexSemialgebraic, complexCoordinates_norm_le _ i ε hε] using h

/--
@isnad1 id=iscomple.1h3v.s5.de1b30ba343a from=translated src=- shape=77eae92f vocab=c82014db
-/
theorem coord_norm_eq (i : ι) {ε : ℝ} (hε : 0 ≤ ε) :
    IsComplexSemialgebraic {z : ι → ℂ | ‖z i‖ = ε} := by
  have h := IsSemialgebraic.eq
    ((MvPolynomial.X (.inl i) : MvPolynomial (ι ⊕ ι) ℝ) ^ 2 + MvPolynomial.X (.inr i) ^ 2)
    (MvPolynomial.C (ε ^ 2))
  simpa [IsComplexSemialgebraic, complexCoordinates_norm_eq _ i ε hε] using h

/-- Complex polynomial preimages are semialgebraic in real coordinates.
@isnad1 id=iscomple.1h4v.s6.13e74a4b28ed from=translated src=- shape=f0cb1b31 vocab=d805c9d4
-/
theorem polynomial_preimage {κ : Type*} {S : Set (ι → ℂ)} (hS : IsComplexSemialgebraic S)
    (g : ι → MvPolynomial κ ℂ) :
    IsComplexSemialgebraic ((fun z i => MvPolynomial.eval z (g i)) ⁻¹' S) := by
  choose r s hrs using fun i => polynomial_real_parts (g i)
  let G : (ι ⊕ ι) → MvPolynomial (κ ⊕ κ) ℝ := Sum.elim r s
  have hG (x : (κ ⊕ κ) → ℝ) :
      complexCoordinates (fun i => MvPolynomial.eval x (G i)) =
        fun i => MvPolynomial.eval (complexCoordinates x) (g i) := by
    funext i
    apply Complex.ext
    · exact ((hrs i x).1).symm
    · exact ((hrs i x).2).symm
  have h := IsSemialgebraic.polynomial_preimage hS G
  unfold IsComplexSemialgebraic
  convert h using 1
  ext x
  simp only [Set.mem_preimage, hG]

end IsComplexSemialgebraic
end
end DuistermaatVanDerKallen
