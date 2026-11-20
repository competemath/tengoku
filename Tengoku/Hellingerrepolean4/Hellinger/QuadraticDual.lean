import Tengoku.Hellingerrepolean4.Hellinger.QuadraticRadical
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms walsh_phase` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms phase_fourth_moment` (it only prints; the queue checks the axioms of every declaration). -/

/-! Actual polar matrices, inverse matrices, and Fourier duals of quadratic phases. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.QuadraticDual
open F2Model QuadraticRadical ChannelSections

def polarMatrix {n : ℕ} (Q : Form n) : Matrix (Fin n) (Fin n) F2 := LinearMap.BilinForm.toMatrix' Q.polarBilin

/--
@isnad1 id=eq.0h4v.s10.2f9c2a40cb57 from=translated src=- shape=339f21d0 vocab=c5233f01
-/
theorem polarMatrix_bilin {n : ℕ} (Q : Form n) (x y : Cube n) :
    x ⬝ᵥ polarMatrix Q *ᵥ y = Q.polarBilin x y := by
  rw [← Matrix.toBilin'_apply', polarMatrix, Matrix.toBilin'_toMatrix']

/--
@isnad1 id=eq.0h4v.s10.dad670f1a79d from=translated src=- shape=17fcacaa vocab=1b925027
-/
theorem polarMatrix_mulVec {n : ℕ} (Q : Form n) (y : Cube n) (i : Fin n) :
    (polarMatrix Q *ᵥ y) i = Q.polarBilin (Pi.single i 1) y := by
  rw [← polarMatrix_bilin, single_one_dotProduct]

/--
@isnad1 id=issymm.0h2v.s3.3179008be232 from=translated src=- shape=e1abeb28 vocab=ab448d71
-/
theorem polarMatrix_symmetric {n : ℕ} (Q : Form n) : (polarMatrix Q).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, polarMatrix, LinearMap.BilinForm.toMatrix'_apply]
  exact QuadraticMap.polar_comm Q _ _

/--
@isnad1 id=eq.1h2v.s9.086b831b37b5 from=translated src=- shape=bd04f6b1 vocab=48c6fd23
-/
theorem polarMatrix_kernel {n : ℕ} (Q : Form n) (hQ : IsUnit (polarMatrix Q).det) :
    Q.polarBilin.ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  have hAv : polarMatrix Q *ᵥ v = 0 := by
    funext i
    rw [polarMatrix_mulVec]
    change QuadraticMap.polar Q (Pi.single i 1) v = 0
    rw [QuadraticMap.polar_comm]
    exact congrArg (fun l : Cube n →ₗ[F2] F2 => l (Pi.single i 1)) hv
  have h := congrArg (fun w => (polarMatrix Q)⁻¹ *ᵥ w) hAv
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hQ,
    Matrix.one_mulVec, Matrix.mulVec_zero] using h

/-- This is precisely the manuscript convention for the polar matrix, including
an arbitrary constant term in the quadratic polynomial.
@isnad1 id=eq.0h5v.s9.5671eca3d64e from=translated src=- shape=f6ffd3a3 vocab=49f5d7bb
-/
theorem polarMatrix_characterization {n : ℕ} (a : F2) (Q : Form n) (x v : Cube n) :
    (a + Q (x + v)) + (a + Q x) + (a + Q v) + (a + Q 0) =
      x ⬝ᵥ polarMatrix Q *ᵥ v := by
  rw [polarMatrix_bilin]
  have h := QuadraticMap.map_add Q x v
  change Q (x + v) = Q x + Q v + Q.polarBilin x v at h
  rw [h, map_zero]
  ring_nf
  simp only [show (4 : F2) = 0 from rfl, show (2 : F2) = 0 from rfl, mul_zero, add_zero, zero_add]

def walsh {n : ℕ} (f : Cube n → ℝ) (s : Cube n) : ℝ :=
  mean (fun x => f x * sign (s ⬝ᵥ x))

/--
@isnad1 id=eq.0h3v.s5.ece492c0efd0 from=translated src=- shape=b60f948b vocab=6e003645
-/
theorem sign_sum {ι : Type*} (s : Finset ι) (z : ι → F2) :
    sign (∑ i ∈ s, z i) = ∏ i ∈ s, sign (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, sign_add, ih]

/--
@isnad1 id=eq.0h3v.s7.bde9ddac8d7c from=translated src=- shape=837f0eed vocab=5ee1a8d8
-/
theorem sign_dot_bits {n : ℕ} (s x : Fourier.Cube n) :
    sign (bitsEquiv (Fin n) s ⬝ᵥ bitsEquiv (Fin n) x) = Fourier.phase s x := by
  have hs := sign_sum (Finset.univ : Finset (Fin n))
    (fun i => bitEquiv (s i) * bitEquiv (x i))
  change sign (∑ i, bitEquiv (s i) * bitEquiv (x i)) = _
  rw [hs]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> cases x i <;> norm_num [boolSign]

/--
@isnad1 id=eq.0h3v.s7.caadab597f00 from=translated src=- shape=2e2e3c48 vocab=6d974beb
-/
theorem walsh_bits {n : ℕ} (f : Cube n → ℝ) (s : Fourier.Cube n) :
    walsh f (bitsEquiv (Fin n) s) = Fourier.walsh (f ∘ bitsEquiv (Fin n)) s := by
  unfold walsh
  rw [← mean_comp_equiv (bitsEquiv (Fin n))]
  simp only [Function.comp_def, sign_dot_bits, Fourier.walsh]

/--
@isnad1 id=eq.0h5v.s10.16d075c91631 from=translated src=- shape=c21cc594 vocab=44a9c5eb
-/
theorem phase_translation {n : ℕ} (a : F2) (Q : Form n) (x v : Cube n) :
    phase a Q (x + v) = phase a Q x * sign (Q v) * sign (Q.polarBilin x v) := by
  have h := QuadraticMap.map_add Q x v
  change Q (x + v) = Q x + Q v + Q.polarBilin x v at h
  simp only [phase, h, sign_add]
  ring

/-- Translating the genuine Fourier sum produces the inverse-polar quadratic dual.
@isnad1 id=eq.1h4v.s8.3548a554afae from=translated src=- shape=3cdeb319 vocab=d953697d
-/
theorem walsh_phase {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (s : Cube n) :
    walsh (phase a Q) s = walsh (phase a Q) 0 * sign (Q ((polarMatrix Q)⁻¹ *ᵥ s)) := by
  let v := (polarMatrix Q)⁻¹ *ᵥ s
  have hAv : polarMatrix Q *ᵥ v = s := by
    simp [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ]
  have hpol (x : Cube n) : Q.polarBilin x v = s ⬝ᵥ x := by
    rw [← polarMatrix_bilin, hAv, dotProduct_comm]
  have hsign (x : Cube n) : phase a Q (x + v) * sign (Q v) =
      phase a Q x * sign (s ⬝ᵥ x) := by
    rw [phase_translation, hpol]
    calc
      _ = (phase a Q x * sign (s ⬝ᵥ x)) * sign (Q v) ^ 2 := by ring
      _ = _ := by rw [sign_sq, mul_one]
  have hm := mean_comp_equiv (Equiv.addRight v) (phase a Q)
  change mean (fun x => phase a Q (x + v)) = mean (phase a Q) at hm
  have hmean : mean (fun x => phase a Q (x + v) * sign (Q v)) =
      mean (phase a Q) * sign (Q v) := by rw [Fourier.mean_mul_const, hm]
  simp_rw [hsign] at hmean
  simpa [walsh, dotProduct, sign] using hmean

def dualForm {n : ℕ} (Q : Form n) : Form n := Q.comp ((polarMatrix Q)⁻¹).toLin'

/--
@isnad1 id=eq.1h4v.s10.65e4f3e540bf from=translated src=- shape=7662c19a vocab=6f51127b
-/
theorem dualForm_polar {n : ℕ} (Q : Form n) (hQ : IsUnit (polarMatrix Q).det)
    (x y : Cube n) :
    (dualForm Q).polarBilin x y = x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ y := by
  simp only [dualForm, QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply,
    Matrix.toLin'_apply]
  rw [← polarMatrix_bilin, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ,
    Matrix.one_mulVec]
  rw [dotProduct_comm ((polarMatrix Q)⁻¹ *ᵥ x) y]
  have hs := Matrix.dotProduct_transpose_mulVec (polarMatrix Q)⁻¹ x y
  rw [(polarMatrix_symmetric Q).inv.eq] at hs
  exact hs.symm

/--
@isnad1 id=eq.0h2v.s6.4e611aacb089 from=translated src=- shape=93df5a2f vocab=5c708c8b
-/
theorem walsh_zero {n : ℕ} (f : Cube n → ℝ) : walsh f 0 = mean f := by
  simp [walsh, dotProduct]

/--
@isnad1 id=eq.1h3v.s6.f466df863151 from=translated src=- shape=832c9af0 vocab=161ded84
-/
theorem walsh_phase_zero_sq {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) :
    walsh (phase a Q) 0 ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
  have h := Flatness.mean_sq (phase_bent a Q (polarMatrix_kernel Q hQ))
  rw [mean_comp_equiv] at h
  simpa [walsh_zero] using h

/--
@isnad1 id=eq.1h5v.s8.83c5a32f2812 from=translated src=- shape=4bf221b6 vocab=d9a39b06
-/
theorem walsh_phase_pair {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (x s : Cube n) :
    walsh (phase a Q) x * walsh (phase a Q) (x + s) =
      ((2 : ℝ) ^ n)⁻¹ * sign (dualForm Q s) *
        sign (x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ s) := by
  have hd := phase_derivative (0 : F2) (dualForm Q) x s
  simp only [phase, zero_add, dualForm_polar Q hQ] at hd
  rw [walsh_phase a Q hQ x, walsh_phase a Q hQ (x + s)]
  change walsh (phase a Q) 0 * sign (dualForm Q x) *
    (walsh (phase a Q) 0 * sign (dualForm Q (x + s))) = _
  calc
    _ = walsh (phase a Q) 0 ^ 2 *
        (sign (dualForm Q x) * sign (dualForm Q (x + s))) := by ring
    _ = _ := by rw [walsh_phase_zero_sq a Q hQ, hd]; ring

def noiseWeight {n : ℕ} (ρ : ℝ) (x : Cube n) : ℝ :=
  ∏ i, if x i = 0 then 1 else ρ

/--
@isnad1 id=eq.0h3v.s6.5bc9572cfe90 from=translated src=- shape=00aa9f42 vocab=502843b4
-/
theorem noiseWeight_bits {n : ℕ} (ρ : ℝ) (x : Fourier.Cube n) :
    noiseWeight ρ (bitsEquiv (Fin n) x) = ρ ^ Fourier.degree x := by
  rw [Fourier.pow_degree]
  apply Finset.prod_congr rfl
  intro i _
  have hb (b : Bool) : (if bitEquiv b = 0 then (1 : ℝ) else ρ) =
      (if b = true then ρ else 1) := by cases b <;> norm_num
  exact hb (x i)

/--
@isnad1 id=eq.1h3v.s8.60d3acb33f3f from=translated src=- shape=44af1c92 vocab=f0bf2cbc
-/
theorem noise_fourth_moment {n : ℕ} (f : Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply (f ∘ bitsEquiv (Fin n)) x) ^ 4) =
      ∑ s : Cube n, (∑ x : Cube n, (noiseWeight ρ x * walsh f x) *
        (noiseWeight ρ (x + s) * walsh f (x + s))) ^ 2 := by
  rw [FourierProducts.noise_fourth_moment]
  rw [← (bitsEquiv (Fin n)).sum_comp (fun s : Cube n =>
    (∑ x : Cube n, (noiseWeight ρ x * walsh f x) *
      (noiseWeight ρ (x + s) * walsh f (x + s))) ^ 2)]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [← (bitsEquiv (Fin n)).sum_comp (fun x : Cube n =>
    (noiseWeight ρ x * walsh f x) *
      (noiseWeight ρ (x + bitsEquiv (Fin n) s) * walsh f (x + bitsEquiv (Fin n) s)))]
  apply Finset.sum_congr rfl
  intro x _
  rw [← bitsEquiv_translate n x s]
  simp only [noiseWeight_bits, walsh_bits]
  have htrans : Fourier.translate s x = Fourier.translate x s := by
    funext i
    exact Bool.xor_comm _ _
  rw [htrans]

/-- Genuine fourth moment reduced to the inverse-polar character sum.
@isnad1 id=eq.2h4v.s8.003d999205de from=translated src=- shape=b90c3ce4 vocab=924609ec
-/
theorem phase_fourth_moment {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n)) x) ^ 4) =
      ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∑ s : Cube n,
        (∑ x : Cube n, noiseWeight ρ x * noiseWeight ρ (x + s) *
          sign (x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ s)) ^ 2 := by
  rw [noise_fourth_moment]
  have hp (x s : Cube n) :
      (noiseWeight ρ x * walsh (phase a Q) x) *
        (noiseWeight ρ (x + s) * walsh (phase a Q) (x + s)) =
      (((2 : ℝ) ^ n)⁻¹ * sign (dualForm Q s)) *
        (noiseWeight ρ x * noiseWeight ρ (x + s) *
          sign (x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ s)) := by
    calc
      _ = (noiseWeight ρ x * noiseWeight ρ (x + s)) *
        (walsh (phase a Q) x * walsh (phase a Q) (x + s)) := by ring
      _ = _ := by rw [walsh_phase_pair a Q hQ]; ring
  simp_rw [hp, ← Finset.mul_sum, mul_pow, sign_sq, mul_one]
  rw [Finset.mul_sum]

end Hellinger.QuadraticDual
