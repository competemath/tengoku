module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylGrading
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QuarticKernelCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The actual symmetric quadratic kernel vectors have weighted binary
degree twice their auxiliary degree, in each of the six cyclic modules. -/

set_option maxHeartbeats 600000

noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
open scoped TensorProduct

variable {K : Type*} [Field K]

/-- Membership in the genuine shifted binary component.-/
def WeightedVector (w : Fin 3 → ℕ) (t : ℤ) (m : BinaryVector K) : Prop :=
  ∀ i, m i ∈ signedForms K 2 (t - w i)

/--
@isnad1 id=weighted.0h3v.s6.f83774be4fd9 from=translated src=- shape=1ab8fba7 vocab=d6e5dc1e
-/
theorem weightedVector_zero (w : Fin 3 → ℕ) (t : ℤ) :
    WeightedVector (K := K) w t 0 := by
  intro i
  exact (signedForms K 2 _).zero_mem

/--
@isnad1 id=weighted.2h5v.s6.d6f8740b41a6 from=translated src=- shape=4af143a9 vocab=3d83710a
-/
theorem weightedVector_add {w : Fin 3 → ℕ} {t : ℤ} {m n : BinaryVector K}
    (hm : WeightedVector w t m) (hn : WeightedVector w t n) :
    WeightedVector w t (m + n) := by
  intro i
  exact (signedForms K 2 _).add_mem (hm i) (hn i)

/--
@isnad1 id=weighted.1h4v.s6.427ed8878762 from=translated src=- shape=9913f2aa vocab=7d6b71b9
-/
theorem weightedVector_neg {w : Fin 3 → ℕ} {t : ℤ} {m : BinaryVector K}
    (hm : WeightedVector w t m) : WeightedVector w t (-m) := by
  intro i
  exact (signedForms K 2 _).neg_mem (hm i)

/--
@isnad1 id=weighted.1h6v.s6.b7220c0a44c4 from=translated src=- shape=30eb3b99 vocab=1b8b0414
-/
theorem weightedVector_sum {ι : Type*} (s : Finset ι) {w : Fin 3 → ℕ} {t : ℤ}
    {m : ι → BinaryVector K} (hm : ∀ i ∈ s, WeightedVector w t (m i)) :
    WeightedVector w t (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedVector_zero w t
  | @insert i s hi hs =>
    rw [Finset.sum_insert hi]
    exact weightedVector_add (hm i (Finset.mem_insert_self i s))
      (hs (fun j hj => hm j (Finset.mem_insert_of_mem hj)))

/--
@isnad1 id=weighted.2h6v.s7.fc13812a59b3 from=translated src=- shape=397e3bb6 vocab=ec1d003f
-/
theorem weightedVector_binary_smul {w : Fin 3 → ℕ} {t : ℤ} {d : ℕ}
    {b : BinaryRing K} {m : BinaryVector K}
    (hb : b.IsHomogeneous d) (hm : WeightedVector w t m) :
    WeightedVector w (t + d) (b • m) := by
  intro i
  change b * m i ∈ signedForms K 2 (t + d - w i)
  have h := homogeneous_mul_mem_signedForms hb (hm i)
  convert h using 1
  congr 1
  omega

section CubicAction
variable (F : BinaryRing K) (Z : End (BinaryRing K) (BinaryVector K))
  (hZ : Z ^ 3 = F • 1)
variable [Module (CyclicCubicRing (BinaryRing K) F) (BinaryVector K)]
  (hcoeff : ∀ (b : BinaryRing K) (m : BinaryVector K), cyclicCoefficientHom F b • m = b • m)
  (hroot : ∀ (m : BinaryVector K), cyclicRoot F • m = Z m)

/-- A scalar has degree `d` when it raises every shifted binary component by `d`.-/
def WeightedScalar (w : Fin 3 → ℕ) (d : ℤ) (r : CyclicCubicRing (BinaryRing K) F) : Prop :=
  ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m → WeightedVector w (t + d) (r • m)

/--
@isnad1 id=weighted.0h4v.s9.9b407febcb8e from=translated src=- shape=39f8556f vocab=14ddb5b1
-/
theorem weightedScalar_zero (w : Fin 3 → ℕ) (d : ℤ) :
    WeightedScalar F w d 0 := by
  intro t m hm
  rw [Module.zero_smul (R := CyclicCubicRing (BinaryRing K) F) m]
  exact weightedVector_zero w (t + d)

/--
@isnad1 id=weighted.2h6v.s9.f5143dd3f91f from=translated src=- shape=cfb09bf9 vocab=603cfa91
-/
theorem weightedScalar_add {w : Fin 3 → ℕ} {d : ℤ} {r s : CyclicCubicRing (BinaryRing K) F}
    (hr : WeightedScalar F w d r) (hs : WeightedScalar F w d s) :
    WeightedScalar F w d (r + s) := by
  intro t m hm
  rw [add_smul]
  exact weightedVector_add (hr t m hm) (hs t m hm)

/--
@isnad1 id=weighted.1h5v.s10.72f9eea716f1 from=translated src=- shape=02891e3e vocab=fadf000e
-/
theorem weightedScalar_neg {w : Fin 3 → ℕ} {d : ℤ} {r : CyclicCubicRing (BinaryRing K) F}
    (hr : WeightedScalar F w d r) : WeightedScalar F w d (-r) := by
  intro t m hm
  rw [neg_smul]
  exact weightedVector_neg (hr t m hm)

/--
@isnad1 id=weighted.0h3v.s9.35bc81b4e55f from=translated src=- shape=9bcc28e5 vocab=14ddb5b1
-/
theorem weightedScalar_one (w : Fin 3 → ℕ) : WeightedScalar F w 0 1 := by
  intro t m hm
  simpa using hm

/--
@isnad1 id=weighted.2h7v.s9.bd96c26dda70 from=translated src=- shape=cbdeb992 vocab=435c28e2
-/
theorem weightedScalar_mul {w : Fin 3 → ℕ} {d e : ℤ} {r s : CyclicCubicRing (BinaryRing K) F}
    (hr : WeightedScalar F w d r) (hs : WeightedScalar F w e s) :
    WeightedScalar F w (d + e) (r * s) := by
  intro t m hm
  rw [mul_smul]
  have h := hr (t + e) (s • m) (hs t m hm)
  simpa only [add_assoc, add_comm, add_left_comm] using h

/--
@isnad1 id=weighted.1h7v.s9.adc8558afc95 from=translated src=- shape=b3da3e80 vocab=9b29d8c2
-/
theorem weightedScalar_sum {ι : Type*} (s : Finset ι) {w : Fin 3 → ℕ} {d : ℤ}
    {r : ι → CyclicCubicRing (BinaryRing K) F} (hr : ∀ i ∈ s, WeightedScalar F w d (r i)) :
    WeightedScalar F w d (∑ i ∈ s, r i) := by
  intro t m hm
  rw [Finset.sum_smul]
  exact weightedVector_sum s (fun i hi => hr i hi t m hm)

/--
@isnad1 id=weighted.1h6v.s9.5a09f5b60020 from=translated src=- shape=444c2218 vocab=29da359b
-/
theorem weightedScalar_pow {w : Fin 3 → ℕ} {d : ℤ} {r : CyclicCubicRing (BinaryRing K) F}
    (hr : WeightedScalar F w d r) (n : ℕ) :
    WeightedScalar F w (n * d) (r ^ n) := by
  induction n with
  | zero => simpa using weightedScalar_one F w
  | succ n ih =>
    rw [pow_succ]
    convert weightedScalar_mul F ih hr using 1
    push_cast
    ring

include hcoeff in
/--
@isnad1 id=weighted.2h5v.s11.1f820a7987a9 from=translated src=- shape=ef34beaf vocab=c747aaa6
-/
theorem weightedScalar_coefficient {w : Fin 3 → ℕ} {d : ℕ} {b : BinaryRing K}
    (hb : b.IsHomogeneous d) :
    WeightedScalar F w d (cyclicCoefficientHom F b) := by
  intro t m hm
  rw [hcoeff]
  exact weightedVector_binary_smul hb hm

include hroot in
/--
@isnad1 id=weighted.2h4v.s11.a429b41af0df from=translated src=- shape=9233f9bb vocab=41a7b578
-/
theorem weightedScalar_root (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) :
    WeightedScalar F w 1 (cyclicRoot F) := by
  intro t m hm
  rw [hroot]
  exact hgraded t m hm

/-- Every coefficient of an auxiliary polynomial has the given binary action degree.-/
def WeightedPolynomial (w : Fin 3 → ℕ) (d : ℤ) (p : Aux (CyclicCubicRing (BinaryRing K) F)) : Prop :=
  ∀ α, WeightedScalar F w d (p.coeff α)

/--
@isnad1 id=weighted.2h7v.s11.762037aeb7f6 from=translated src=- shape=8d3b16a9 vocab=a051657a
-/
theorem weightedPolynomial_mul {w : Fin 3 → ℕ} {d e : ℤ} {p q : Aux (CyclicCubicRing (BinaryRing K) F)}
    (hp : WeightedPolynomial F w d p) (hq : WeightedPolynomial F w e q) :
    WeightedPolynomial F w (d + e) (p * q) := by
  intro α
  classical
  rw [coeff_mul]
  exact weightedScalar_sum F _
    (fun x _ => weightedScalar_mul F (hp x.1) (hq x.2))

/--
@isnad1 id=weighted.0h3v.s10.3027db7bd4c5 from=translated src=- shape=69e3e0d6 vocab=0bb495e6
-/
theorem weightedPolynomial_one (w : Fin 3 → ℕ) :
    WeightedPolynomial F w 0 1 := by
  intro α
  classical
  by_cases h : α = 0
  · subst α
    simpa using weightedScalar_one F w
  · simpa [coeff_one, h, Ne.symm h] using weightedScalar_zero F w 0

/--
@isnad1 id=weighted.1h6v.s11.beea8223121c from=translated src=- shape=b55152d3 vocab=4dac2701
-/
theorem weightedPolynomial_pow {w : Fin 3 → ℕ} {d : ℤ} {p : Aux (CyclicCubicRing (BinaryRing K) F)}
    (hp : WeightedPolynomial F w d p) (n : ℕ) :
    WeightedPolynomial F w (n * d) (p ^ n) := by
  induction n with
  | zero => simpa using weightedPolynomial_one F w
  | succ n ih =>
    rw [pow_succ]
    convert weightedPolynomial_mul F ih hp using 1
    push_cast
    ring

/--
@isnad1 id=weighted.1h5v.s9.8f00b5efb1c6 from=translated src=- shape=fe268019 vocab=bb08ddf5
-/
theorem weightedPolynomial_linearForm {w : Fin 3 → ℕ} {d : ℤ} {a : Fin 3 → CyclicCubicRing (BinaryRing K) F}
    (ha : ∀ i, WeightedScalar F w d (a i)) :
    WeightedPolynomial F w d (linearForm a) := by
  intro α
  classical
  simp only [linearForm, coeff_sum]
  apply weightedScalar_sum F
  intro i _
  rw [C_mul_X_eq_monomial, coeff_monomial]
  split_ifs
  · exact ha i
  · exact weightedScalar_zero F w d

include hcoeff hroot in
/--
@isnad1 id=weighted.3h4v.s12.78210679d186 from=translated src=- shape=a78ec13a vocab=38b463cb
-/
theorem weightedPolynomial_quadraticOne (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) :
    WeightedPolynomial F w 2
      (linearForm (quadraticOne (cyclicCoefficientHom F (binaryU K))
        (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F))) := by
  apply weightedPolynomial_linearForm F (w := w) (d := 2)
  have hu : WeightedScalar F w 1 (cyclicCoefficientHom F (binaryU K)) :=
    weightedScalar_coefficient F hcoeff (isHomogeneous_X K 0)
  have hv : WeightedScalar F w 1 (cyclicCoefficientHom F (binaryV K)) :=
    weightedScalar_coefficient F hcoeff (isHomogeneous_X K 1)
  have hz := weightedScalar_root F Z hroot w hgraded
  intro i
  fin_cases i
  · exact weightedScalar_mul F hv hz
  · exact weightedScalar_mul F hz hu
  · exact weightedScalar_mul F hu hv

include hcoeff hroot in
/--
@isnad1 id=weighted.3h4v.s12.151c7ddc189e from=translated src=- shape=a78ec13a vocab=04d49151
-/
theorem weightedPolynomial_quadraticTwo (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) :
    WeightedPolynomial F w 2
      (linearForm (quadraticTwo (cyclicCoefficientHom F (binaryU K))
        (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F))) := by
  apply weightedPolynomial_linearForm F (w := w) (d := 2)
  have hu : WeightedScalar F w 1 (cyclicCoefficientHom F (binaryU K)) :=
    weightedScalar_coefficient F hcoeff (isHomogeneous_X K 0)
  have hv : WeightedScalar F w 1 (cyclicCoefficientHom F (binaryV K)) :=
    weightedScalar_coefficient F hcoeff (isHomogeneous_X K 1)
  have hz := weightedScalar_root F Z hroot w hgraded
  intro i
  fin_cases i
  · exact weightedScalar_pow F hu 2
  · exact weightedScalar_pow F hv 2
  · exact weightedScalar_neg F (weightedScalar_pow F hz 2)

include hcoeff hroot in
/--
@isnad1 id=weighted.3h6v.s13.ec10ba5dd22d from=translated src=- shape=7c805ea8 vocab=f7755ec8
-/
theorem weightedPolynomial_quadraticSymmetric (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) (n : ℕ) (j : Fin (n + 1)) :
    WeightedPolynomial F w (2 * n)
      (linearForm (quadraticOne (cyclicCoefficientHom F (binaryU K))
          (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (j : ℕ) *
        linearForm (quadraticTwo (cyclicCoefficientHom F (binaryU K))
          (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (n - j)) := by
  have h := weightedPolynomial_mul F
    (weightedPolynomial_pow F (weightedPolynomial_quadraticOne F Z hcoeff hroot w hgraded) j)
    (weightedPolynomial_pow F (weightedPolynomial_quadraticTwo F Z hcoeff hroot w hgraded) (n - j))
  convert h using 1
  have hj : (j : ℕ) ≤ n := by omega
  omega

/-- The literal source basis vector lies in the component of its generator shift.
@isnad1 id=weighted.0h3v.s7.042206b87f8f from=translated src=- shape=7a965706 vocab=7857474e
-/
theorem weightedVector_basis (w : Fin 3 → ℕ) (k : Fin 3) :
    WeightedVector (K := K) w (w k) (Pi.single k 1) := by
  intro i
  by_cases h : k = i
  · subst i
    simp only [Pi.single_eq_same, sub_self]
    change (1 : BinaryRing K) ∈ Forms K 2 0
    exact isHomogeneous_one (Fin 2) K
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    exact (signedForms K 2 _).zero_mem

include hcoeff hroot in
/-- Every entry of the actual symmetric kernel column has its required shifted degree.
@isnad1 id=mem.3h9v.s15.97b139ae7dee from=translated src=- shape=553b6b5f vocab=7227a28f
-/
theorem quadraticSymmetric_coefficient_degree (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) (n : ℕ) (j : Fin (n + 1))
    (α : Fin 3 →₀ ℕ) (i k : Fin 3) :
    tensorCoefficients
      ((linearForm (quadraticOne (cyclicCoefficientHom F (binaryU K))
          (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (j : ℕ) *
        linearForm (quadraticTwo (cyclicCoefficientHom F (binaryU K))
          (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (n - j)) ⊗ₜ[CyclicCubicRing (BinaryRing K) F]
          (Pi.single k (1 : BinaryRing K) : BinaryVector K)) α i ∈
      signedForms K 2 (2 * n + w k - w i) := by
  rw [tensorCoefficients_tmul]
  have h := weightedPolynomial_quadraticSymmetric F Z hcoeff hroot w hgraded n j α
      (w k) (Pi.single k 1) (weightedVector_basis w k) i
  convert h using 1
  congr 1
  omega

end CubicAction

/-- The literal degree-`n` symmetric column of the two quadratic syzygies.-/
def quadraticSymmetricPolynomial (F : BinaryRing K) (n : ℕ) (j : Fin (n + 1)) :
    Aux (CyclicCubicRing (BinaryRing K) F) :=
  linearForm (quadraticOne (cyclicCoefficientHom F (binaryU K))
      (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (j : ℕ) *
    linearForm (quadraticTwo (cyclicCoefficientHom F (binaryU K))
      (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (n - j)

/-- The coefficient certificate in the actual cyclic cubic module, including
its explicit scalar action.
@isnad1 id=mem.2h9v.s12.9250e944c25a from=translated src=- shape=a7b617b9 vocab=d8e1d4b2
-/
theorem cyclic_quadraticSymmetric_coefficient_degree
    (F : BinaryRing K) (Z : End (BinaryRing K) (BinaryVector K))
    (hZ : Z ^ 3 = F • 1) (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) (n : ℕ) (j : Fin (n + 1))
    (α : Fin 3 →₀ ℕ) (i k : Fin 3) :
    letI := cyclicModuleStructure F Z hZ
    (((quadraticSymmetricPolynomial F n j).coeff α •
        (Pi.single k (1 : BinaryRing K) : BinaryVector K)) : BinaryVector K) i ∈
      signedForms K 2 (2 * n + w k - w i) := by
  let _ := cyclicModuleStructure F Z hZ
  simpa only [quadraticSymmetricPolynomial, tensorCoefficients_tmul] using
    quadraticSymmetric_coefficient_degree F Z
      (cyclicModule_coefficient_smul F Z hZ) (cyclicModule_root_smul F Z hZ)
      w hgraded n j α i k

end ChoppedPlane.QWeyl
