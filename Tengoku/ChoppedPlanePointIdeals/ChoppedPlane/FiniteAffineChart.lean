module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Quotient
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HilbertDifference
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HomogeneousSaturation
public import Tengoku.Seed.RingTheory.Finiteness.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Finite affine charts from a homogeneous cut at infinity

A homogeneous ideal which kills a complete degree on `z = 0` makes its
`z = 1` coordinate algebra finite. The proof descends homogeneous forms
and then uses polynomial induction to show that a single degree represents
all affine classes.
-/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- Restriction of a polynomial chart map to a homogeneous degree.-/
def formChartMap (π : Poly K 3 →ₐ[K] A) (N : ℕ) : Forms K 3 N →ₗ[K] A :=
  π.toLinearMap.comp (Forms K 3 N).subtype

/--
@isnad1 id=eq.0h5v.s11.53e285a84899 from=translated src=- shape=8756fabe vocab=48d42485
-/
@[simp] theorem formChartMap_apply (π : Poly K 3 →ₐ[K] A) (N : ℕ)
    (f : Forms K 3 N) : formChartMap π N f = π f.val := rfl

/-- The degree cut on the line at infinity gives homogeneous descent.
@isnad1 id=ex.3h4v.s11.20a42ca7d263 from=translated src=- shape=ccfa747e vocab=940c20b2
-/
theorem exists_form_descent (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (N : ℕ) (hN : 0 < N)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    (f : Forms K 3 N) :
    ∃ g : Forms K 3 (N - 1), f.val - X 2 * g.val ∈ I := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hcut f)
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hb
  let g : Forms K 3 (N - 1) := ⟨homogeneousComponent (N - 1) p,
    homogeneousComponent_mem _ _⟩
  refine ⟨g, ?_⟩
  have hc := congrArg (homogeneousComponent N) hab
  have hm : homogeneousComponent N b = X 2 * g.val := by
    rw [hp]
    have hh := homogeneousComponent_mul_form (N - 1) (X (R := K) 2) p
      (isHomogeneous_X K 2)
    simpa [g, show 1 + (N - 1) = N by omega] using hh
  rw [map_add, homogeneousComponent_eq_self f.property, hm] at hc
  have haN := homogeneousComponent_mem_of_mem hI ha N
  rw [← hc, add_sub_cancel_right]
  exact haN

/-- Degree zero vanishing at infinity annihilates the constant piece.
@isnad1 id=mem.2h3v.s11.79c36a20f54f from=translated src=- shape=0193e834 vocab=9a6b3d1e
-/
theorem form_zero_mem_of_cut (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hcut : ∀ f : Forms K 3 0, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    (f : Forms K 3 0) : f.val ∈ I := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hcut f)
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hb
  have hc := congrArg (homogeneousComponent 0) hab
  have hm : homogeneousComponent 0 b = 0 := by
    rw [hp]
    exact homogeneousComponent_mul_eq_zero_of_lt 0 (by omega)
      (X (R := K) 2) p (isHomogeneous_X K 2)
  rw [map_add, homogeneousComponent_eq_self f.property, hm, add_zero] at hc
  exact hc ▸ homogeneousComponent_mem_of_mem hI ha 0

/-- The image of a fixed homogeneous degree contains all scalar constants.
@isnad1 id=mem.1h5v.s10.ce9db4f197b3 from=translated src=- shape=bb7f110d vocab=3653ef3b
-/
theorem constant_mem_range_formChartMap (π : Poly K 3 →ₐ[K] A)
    (hz : π (X 2) = 1) (N : ℕ) (a : K) :
    algebraMap K A a ∈ LinearMap.range (formChartMap π N) := by
  refine ⟨⟨C a * X 2 ^ N, (isHomogeneous_X_pow 2 N).C_mul a⟩, ?_⟩
  simp [formChartMap_apply, hz]

/-- Degree descent makes the homogeneous image stable under the chart variables.
@isnad1 id=mem.4h7v.s12.3a1477c80a9e from=translated src=- shape=4e78cfa4 vocab=3a99f3db
-/
theorem variable_mul_mem_range_formChartMap (π : Poly K 3 →ₐ[K] A)
    (hz : π (X 2) = 1) (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hker : ∀ f ∈ I, π f = 0) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    (i : Fin 3) (f : Forms K 3 N) :
    π (X i) * formChartMap π N f ∈ LinearMap.range (formChartMap π N) := by
  by_cases hN : N = 0
  · subst N
    have hf := hker f.val (form_zero_mem_of_cut I hI hcut f)
    simp [formChartMap_apply, hf]
  · obtain ⟨g, hg⟩ := exists_form_descent I hI N (by omega) hcut f
    have heq : π f.val = π g.val := by
      have heq := hker (f.val - X 2 * g.val) hg
      simpa [map_sub, map_mul, hz, sub_eq_zero] using heq
    refine ⟨⟨X i * g.val, ?_⟩, ?_⟩
    · simpa [show 1 + (N - 1) = N by omega] using (isHomogeneous_X K i).mul g.property
    · simp [formChartMap_apply, map_mul, heq]

/-- All classes in an affine chart are represented by the one homogeneous degree.
@isnad1 id=surjecti.5h5v.s12.e89cbb9630c0 from=translated src=- shape=c8d9fa0c vocab=523daa72
-/
theorem formChartMap_surjective (π : Poly K 3 →ₐ[K] A)
    (hπ : Function.Surjective π) (hz : π (X 2) = 1)
    (I : Ideal (Poly K 3)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hker : ∀ f ∈ I, π f = 0) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2}) :
    Function.Surjective (formChartMap π N) := by
  have hmem : ∀ p : Poly K 3, π p ∈ LinearMap.range (formChartMap π N) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa using constant_mem_range_formChartMap π hz N a
    | add p q hp hq => simpa only [map_add] using (LinearMap.range _).add_mem hp hq
    | mul_X p i hp =>
      obtain ⟨f, hf⟩ := hp
      simpa [map_mul, hf, mul_comm] using
        variable_mul_mem_range_formChartMap π hz I hI hker N hcut i f
  intro a
  obtain ⟨p, rfl⟩ := hπ a
  exact hmem p

/-- The resulting affine coordinate algebra is finite over the coefficient field.
@isnad1 id=finite.5h5v.s11.327a2ad5a4fb from=translated src=- shape=ea336772 vocab=f6c7f2b6
-/
theorem finite_of_form_cut (π : Poly K 3 →ₐ[K] A)
    (hπ : Function.Surjective π) (hz : π (X 2) = 1)
    (I : Ideal (Poly K 3)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hker : ∀ f ∈ I, π f = 0) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2}) :
    Module.Finite K A :=
  Module.Finite.of_surjective (formChartMap π N)
    (formChartMap_surjective π hπ hz I hI hker N hcut)

/-- A cut in one homogeneous degree contains every later degree as well.
@isnad1 id=mem.2h5v.s11.08a335c766ed from=translated src=- shape=7775ff29 vocab=903fa74d
-/
theorem form_cut_of_le (I : Ideal (Poly K 3)) (N t : ℕ) (hNt : N ≤ t)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    (f : Forms K 3 t) : f.val ∈ I ⊔ Ideal.span {X (R := K) 2} := by
  have hf : f.val ∈ Forms K 3 N * Forms K 3 (t - N) := by
    rw [forms_mul_forms, Nat.add_sub_of_le hNt]
    exact f.property
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro p hp q hq
    exact Ideal.mul_mem_right _ _ (hcut ⟨p, hp⟩)
  · intro p q hp hq
    exact Ideal.add_mem _ hp hq

/-- The same affine chart is represented by every homogeneous degree past the cut.
@isnad1 id=surjecti.6h6v.s12.48e5eb3c1ee9 from=translated src=- shape=75ad73eb vocab=ddf076c8
-/
theorem formChartMap_surjective_of_le (π : Poly K 3 →ₐ[K] A)
    (hπ : Function.Surjective π) (hz : π (X 2) = 1)
    (I : Ideal (Poly K 3)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hker : ∀ f ∈ I, π f = 0) (N t : ℕ) (hNt : N ≤ t)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2}) :
    Function.Surjective (formChartMap π t) :=
  formChartMap_surjective π hπ hz I hI hker t (form_cut_of_le I N t hNt hcut)

/-- Vanishing of the degree after restriction to `z = 0` is exactly the cut
condition used for affine finiteness.
@isnad1 id=mem.3h6v.s11.e5fa01b51325 from=translated src=- shape=74ae3859 vocab=f2ada702
-/
theorem form_cut_of_map {S : Type*} [CommRing S]
    (φ : Poly K 3 →+* S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {X (R := K) 2})
    (I : Ideal (Poly K 3)) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, φ f.val ∈ I.map φ) :
    ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2} := by
  intro f
  have hf : f.val ∈ (I.map φ).comap φ := hcut f
  rw [Ideal.comap_map_of_surjective' φ hφ I, hker] at hf
  exact hf

/--
@isnad1 id=iff.0h4v.s11.fbd14430a0e2 from=translated src=- shape=df530b3e vocab=c32d6733
-/
@[simp] theorem mem_idealFormPiece (I : Ideal (Poly K 3)) (N : ℕ)
    (f : Forms K 3 N) : f ∈ idealFormPiece I N ↔ f.val ∈ I := Iff.rfl

/-- Identifying a homogeneous chart kernel identifies the quotient degree piece.
@isnad1 id=eq.1h5v.s11.0f2c235634cf from=translated src=- shape=e80d6395 vocab=17c4ba9f
-/
theorem ker_formChartMap (π : Poly K 3 →ₐ[K] A) (I : Ideal (Poly K 3)) (N : ℕ)
    (hker : ∀ f : Forms K 3 N, π f.val = 0 ↔ f.val ∈ I) :
    LinearMap.ker (formChartMap π N) = idealFormPiece I N := by
  ext f
  exact hker f

/-- The homogeneous degree quotient is the complete affine coordinate algebra.-/
def formChartQuotientEquiv (π : Poly K 3 →ₐ[K] A)
    (hπ : Function.Surjective π) (hz : π (X 2) = 1)
    (I : Ideal (Poly K 3)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hker : ∀ f ∈ I, π f = 0) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    (hexact : ∀ f : Forms K 3 N, π f.val = 0 ↔ f.val ∈ I) :
    (Forms K 3 N ⧸ idealFormPiece I N) ≃ₗ[K] A :=
  (Submodule.quotEquivOfEq _ _ (ker_formChartMap π I N hexact).symm).trans
    ((formChartMap π N).quotKerEquivOfSurjective
      (formChartMap_surjective π hπ hz I hI hker N hcut))

/--
@isnad1 id=eq.6h6v.s14.98e0a41bd932 from=translated src=- shape=df6ba6ca vocab=9c0f5369
-/
@[simp] theorem formChartQuotientEquiv_mk (π : Poly K 3 →ₐ[K] A)
    (hπ : Function.Surjective π) (hz : π (X 2) = 1)
    (I : Ideal (Poly K 3)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hker : ∀ f ∈ I, π f = 0) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    (hexact : ∀ f : Forms K 3 N, π f.val = 0 ↔ f.val ∈ I) (f : Forms K 3 N) :
    formChartQuotientEquiv π hπ hz I hI hker N hcut hexact ((idealFormPiece I N).mkQ f) =
      π f.val := by
  simp only [formChartQuotientEquiv, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    formChartMap_apply]

/-- The algebra length is the homogeneous Hilbert function in the cut degree.
@isnad1 id=eq.6h5v.s12.9bb962176f38 from=translated src=- shape=4c69e9bd vocab=5ad56f70
-/
theorem finrank_formChartQuotient (π : Poly K 3 →ₐ[K] A)
    (hπ : Function.Surjective π) (hz : π (X 2) = 1)
    (I : Ideal (Poly K 3)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hker : ∀ f ∈ I, π f = 0) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    (hexact : ∀ f : Forms K 3 N, π f.val = 0 ↔ f.val ∈ I) :
    Module.finrank K (Forms K 3 N ⧸ idealFormPiece I N) = Module.finrank K A :=
  (formChartQuotientEquiv π hπ hz I hI hker N hcut hexact).finrank_eq

/-- The actual coordinate algebra on the affine plane chart `z = 1`.-/
abbrev AffineCoordinateAlgebra (I : Ideal (Poly K 3)) :=
  Poly K 2 ⧸ Ideal.map (affineDehom (K := K)).toRingHom I

/-- The plane polynomial ring maps onto its actual affine coordinate algebra.-/
def affineQuotientMap (I : Ideal (Poly K 3)) : Poly K 3 →ₐ[K] AffineCoordinateAlgebra I :=
  (Ideal.Quotient.mkₐ K (Ideal.map (affineDehom (K := K)).toRingHom I)).comp affineDehom

/--
@isnad1 id=eq.0h3v.s12.33ce6736f116 from=translated src=- shape=0aa7ff06 vocab=eece027a
-/
@[simp] theorem affineQuotientMap_apply (I : Ideal (Poly K 3)) (f : Poly K 3) :
    affineQuotientMap I f = Ideal.Quotient.mk _ (affineDehom f) := rfl

/--
@isnad1 id=eq.0h2v.s11.985c1354a62c from=translated src=- shape=393b1016 vocab=5a079c16
-/
@[simp] theorem affineQuotientMap_z (I : Ideal (Poly K 3)) :
    affineQuotientMap I (X 2) = 1 := by
  simp only [affineQuotientMap, AlgHom.comp_apply, affineDehom_X_two, map_one]

/--
@isnad1 id=surjecti.0h2v.s11.b95cdd0fe376 from=translated src=- shape=0cac4921 vocab=44d1c341
-/
theorem affineQuotientMap_surjective (I : Ideal (Poly K 3)) :
    Function.Surjective (affineQuotientMap I) :=
  (Ideal.Quotient.mkₐ_surjective K _).comp affineDehom_surjective

/--
@isnad1 id=eq.1h3v.s11.de69403aa2bd from=translated src=- shape=6405010e vocab=81b7d96a
-/
theorem affineQuotientMap_eq_zero_of_mem (I : Ideal (Poly K 3))
    {f : Poly K 3} (hf : f ∈ I) : affineQuotientMap I f = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf)

/-- Degree `N` maps onto the actual affine coordinate algebra.
@isnad1 id=surjecti.2h3v.s12.0177d7cbd62d from=translated src=- shape=67066ac0 vocab=5be2efff
-/
theorem affineFormMap_surjective (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K)) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2}) :
    Function.Surjective (formChartMap (affineQuotientMap I) N) :=
  formChartMap_surjective (affineQuotientMap I) (affineQuotientMap_surjective I)
    (affineQuotientMap_z I) I hI (fun _ hf => affineQuotientMap_eq_zero_of_mem I hf) N hcut

/-- A homogeneous cut at infinity makes the actual affine algebra finite.
@isnad1 id=finite.2h3v.s11.05ca5cbf3bb5 from=translated src=- shape=4e3e5202 vocab=5962e67e
-/
theorem affineCoordinateAlgebra_finite (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K)) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2}) :
    Module.Finite K (AffineCoordinateAlgebra I) :=
  Module.Finite.of_surjective _ (affineFormMap_surjective I hI N hcut)

/-- Saturation identifies the affine chart kernel on every homogeneous degree.
@isnad1 id=iff.2h4v.s12.9247d69fe4df from=translated src=- shape=c39cf1b1 vocab=36a7f463
-/
theorem affineQuotientMap_form_eq_zero_iff (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hsat : ∀ p, (X 2 : Poly K 3) * p ∈ I → p ∈ I) (N : ℕ)
    (f : Forms K 3 N) : affineQuotientMap I f.val = 0 ↔ f.val ∈ I := by
  rw [affineQuotientMap_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact affineDehom_mem_map_iff I hI hsat f.property

/-- The cut degree quotient of a saturated homogeneous ideal is its complete
actual affine coordinate algebra.-/
def affineFormQuotientEquiv (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hsat : ∀ p, (X 2 : Poly K 3) * p ∈ I → p ∈ I) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2}) :
    (Forms K 3 N ⧸ idealFormPiece I N) ≃ₗ[K] AffineCoordinateAlgebra I :=
  formChartQuotientEquiv (affineQuotientMap I) (affineQuotientMap_surjective I)
    (affineQuotientMap_z I) I hI (fun _ hf => affineQuotientMap_eq_zero_of_mem I hf)
    N hcut (affineQuotientMap_form_eq_zero_iff I hI hsat N)

/--
@isnad1 id=eq.3h4v.s14.f9ee96cbca2f from=translated src=- shape=25091411 vocab=0c3307bb
-/
@[simp] theorem affineFormQuotientEquiv_mk (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hsat : ∀ p, (X 2 : Poly K 3) * p ∈ I → p ∈ I) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    (f : Forms K 3 N) :
    affineFormQuotientEquiv I hI hsat N hcut ((idealFormPiece I N).mkQ f) =
      affineQuotientMap I f.val := by
  exact formChartQuotientEquiv_mk _ _ _ _ _ _ _ _ _ f

/-- The affine algebra's length is the Hilbert function in the cut degree.
@isnad1 id=eq.3h3v.s12.7a707e0cf186 from=translated src=- shape=d790842a vocab=03fa46cd
-/
theorem finrank_affineCoordinateAlgebra (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hsat : ∀ p, (X 2 : Poly K 3) * p ∈ I → p ∈ I) (N : ℕ)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2}) :
    Module.finrank K (AffineCoordinateAlgebra I) =
      Module.finrank K (Forms K 3 N ⧸ idealFormPiece I N) :=
  (affineFormQuotientEquiv I hI hsat N hcut).finrank_eq.symm

/-- The degree quotients remain equal to the same affine algebra in every
later degree.-/
def affineFormQuotientEquivOfLe (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hsat : ∀ p, (X 2 : Poly K 3) * p ∈ I → p ∈ I) (N t : ℕ) (hNt : N ≤ t)
    (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2}) :
    (Forms K 3 t ⧸ idealFormPiece I t) ≃ₗ[K] AffineCoordinateAlgebra I :=
  affineFormQuotientEquiv I hI hsat t (form_cut_of_le I N t hNt hcut)

end ChoppedPlane
