module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.ProfileOperators
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentPairing
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.SymmetricCoordinates
public import Tengoku.Seed.LinearAlgebra.Finsupp.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Actual homogeneous binary polynomial vectors are exactly the nonnegative
Laurent coefficient vectors of the same weighted degree. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module LaurentPairing
variable {K : Type*} [Field K]

/-- Signed homogeneous membership is the literal support-degree condition.
@isnad1 id=iff.0h3v.s8.e24f15e4be45 from=translated src=- shape=7bfa082b vocab=135153dc
-/
theorem mem_signedBinaryForms_iff_coeff (t : ℤ) (f : BinaryRing K) :
    f ∈ signedForms K 2 t ↔ ∀ s : Fin 2 →₀ ℕ,
      f.coeff s ≠ 0 → (s.degree : ℤ) = t := by
  by_cases ht : 0 ≤ t
  · simp only [signedForms, ite_eq_left ht]
    constructor
    · intro hf s hs
      have h := hf hs
      have hnat : s.degree = t.toNat := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h
      omega
    · intro h
      change f.IsHomogeneous t.toNat
      intro s hs
      have hnat : s.degree = t.toNat := by have h' := h s hs; omega
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hnat
  · simp only [signedForms, ite_eq_right ht, Submodule.mem_bot]
    constructor
    · intro hf s hs
      simp [hf] at hs
    · intro h
      apply MvPolynomial.ext
      intro s
      by_contra hs
      have h' := h s (by simpa using hs)
      omega

/-- Flatten the actual coefficient vectors, retaining the component index.-/
def binaryVectorCoefficients : BinaryVector K ≃ₗ[K]
    (Fin 3 × (Fin 2 →₀ ℕ)) →₀ K :=
  (LinearEquiv.piCongrRight fun _ => (AddMonoidAlgebra.coeffLinearEquiv K)).trans
    ((Finsupp.linearEquivFunOnFinite K ((Fin 2 →₀ ℕ) →₀ K) (Fin 3)).symm.trans
      (Finsupp.curryLinearEquiv K).symm)

/--
@isnad1 id=eq.0h4v.s9.99362ac62b54 from=translated src=- shape=fe8f5cf7 vocab=39dddabf
-/
@[simp] theorem binaryVectorCoefficients_apply (m : BinaryVector K)
    (i : Fin 3) (s : Fin 2 →₀ ℕ) :
    binaryVectorCoefficients m (i,s) = (m i).coeff s := by
  rfl

/-- The two binary exponents become the two nonnegative Laurent exponents.-/
def binaryVectorExponent (a : Fin 3 × (Fin 2 →₀ ℕ)) : Fin 3 × (ℤ × ℤ) :=
  (a.1, ((a.2 0 : ℤ), (a.2 1 : ℤ)))

/--
@isnad1 id=injectiv.0h0v.s4.d3602ec0e063 from=translated src=- shape=49ba05a5 vocab=c93daf82
-/
theorem binaryVectorExponent_injective : Function.Injective binaryVectorExponent := by
  intro a b h
  have hi : a.1 = b.1 := by
    simpa only [binaryVectorExponent] using congrArg Prod.fst h
  have h0 : a.2 0 = b.2 0 := by
    have h' := congrArg (fun e : Fin 3 × (ℤ × ℤ) => e.2.1) h
    simpa only [binaryVectorExponent, Int.natCast_inj] using h'
  have h1 : a.2 1 = b.2 1 := by
    have h' := congrArg (fun e : Fin 3 × (ℤ × ℤ) => e.2.2) h
    simpa only [binaryVectorExponent, Int.natCast_inj] using h'
  apply Prod.ext hi
  ext i
  fin_cases i
  · exact h0
  · exact h1

/--
@isnad1 id=iff.0h1v.s6.b45fbabce80a from=translated src=- shape=04bec768 vocab=21bfe778
-/
theorem mem_range_binaryVectorExponent (e : Fin 3 × (ℤ × ℤ)) :
    e ∈ Set.range binaryVectorExponent ↔ 0 ≤ e.2.1 ∧ 0 ≤ e.2.2 := by
  constructor
  · rintro ⟨⟨i,s⟩,rfl⟩
    exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _⟩
  · rintro ⟨ha,hb⟩
    refine ⟨(e.1,Finsupp.single 0 e.2.1.toNat+Finsupp.single 1 e.2.2.toNat),?_⟩
    ext <;> simp [binaryVectorExponent, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]

/-- The actual binary polynomial embedding into the free Laurent coefficient module.-/
def binaryVectorLaurent : BinaryVector K →ₗ[K] FreeLaurent K (Fin 3) :=
  (Finsupp.lmapDomain K K binaryVectorExponent).comp binaryVectorCoefficients.toLinearMap

/--
@isnad1 id=injectiv.0h1v.s8.bc40af5be2c1 from=translated src=- shape=4eba824d vocab=aa7edd1a
-/
theorem binaryVectorLaurent_injective : Function.Injective (binaryVectorLaurent (K := K)) :=
  (Finsupp.mapDomain_injective binaryVectorExponent_injective).comp
    binaryVectorCoefficients.injective

end ChoppedPlane.QWeyl
