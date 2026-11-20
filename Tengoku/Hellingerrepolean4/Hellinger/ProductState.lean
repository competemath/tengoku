import Tengoku.Hellingerrepolean4.Hellinger.BooleanNoise
import Tengoku.Hellingerrepolean4.Hellinger.ParitySpectrum
import Tengoku.Hellingerrepolean4.Hellinger.Fourier
import Tengoku.Seed.Analysis.Matrix.Spectrum
import Tengoku.Seed.LinearAlgebra.Matrix.Permutation
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Piecewise

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Concrete product-state matrices in the computational basis.
The entries, tensor action and character eigenvectors are constructed here;
none of their eigenvalue or multiplicity properties is an input hypothesis. -/

set_option autoImplicit false
open scoped BigOperators
open Finset Matrix

namespace Hellinger.ProductState

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool

def oneQubit (c : ℝ) : Matrix Bool Bool ℝ :=
  fun x z => (if x = z then 1 else c) / 2

def state (n : ℕ) (c : ℝ) : Matrix (Cube n) (Cube n) ℝ :=
  fun x z => ∏ i, oneQubit c (x i) (z i)

/--
@isnad1 id=eq.0h3v.s4.521c29cfa779 from=translated src=- shape=ef4233a0 vocab=848b9594
-/
theorem oneQubit_symmetric (c : ℝ) (x z : Bool) :
    oneQubit c x z = oneQubit c z x := by
  simp [oneQubit, eq_comm]

/--
@isnad1 id=ishermit.0h2v.s5.8ed2ea1c13f5 from=translated src=- shape=47ad473e vocab=48a5799a
-/
theorem state_isHermitian (n : ℕ) (c : ℝ) : (state n c).IsHermitian := by
  ext x z
  simp only [conjTranspose_apply, star_trivial, state]
  exact Finset.prod_congr rfl fun i _ => oneQubit_symmetric c (z i) (x i)

/--
@isnad1 id=eq.0h2v.s5.e5b232e9c22a from=translated src=- shape=430fd960 vocab=ddad1a80
-/
theorem oneQubit_apply_one (c : ℝ) (x : Bool) :
    (oneQubit c *ᵥ (fun _ => 1)) x = (1 + c) / 2 := by
  cases x <;> simp [Matrix.mulVec, dotProduct, oneQubit] <;> ring

/--
@isnad1 id=eq.0h2v.s6.fc3e09166ec8 from=translated src=- shape=0070a208 vocab=4490bf71
-/
theorem oneQubit_apply_sign (c : ℝ) (x : Bool) :
    (oneQubit c *ᵥ boolSign) x = (1 - c) / 2 * boolSign x := by
  cases x <;> simp [Matrix.mulVec, dotProduct, oneQubit, boolSign] <;> ring

/--
@isnad1 id=eq.0h4v.s6.52eb96cd8487 from=translated src=- shape=48453ccb vocab=270ea40d
-/
theorem state_apply_product (n : ℕ) (c : ℝ) (f : Fin n → Bool → ℝ) (x : Cube n) :
    (state n c *ᵥ (fun z => ∏ i, f i (z i))) x =
      ∏ i, (oneQubit c *ᵥ f i) (x i) := by
  simp only [Matrix.mulVec, dotProduct, state]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => oneQubit c (x i) z * f i z)).symm

/--
@isnad1 id=eq.0h4v.s6.6025db60367b from=translated src=- shape=5b592592 vocab=679ea990
-/
theorem product_two_levels (n : ℕ) (S : Finset (Fin n)) (a b : ℝ) :
    (∏ i : Fin n, if i ∈ S then b else a) = a ^ (n - S.card) * b ^ S.card := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hfilter : (Finset.univ.filter fun i : Fin n => i ∉ S) = Finset.univ \ S := by
    ext i
    simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp [mul_comm]

/--
@isnad1 id=eq.0h4v.s7.5a470f5d496c from=translated src=- shape=efd5b999 vocab=bc747f00
-/
theorem state_character (n : ℕ) (S : Finset (Fin n)) (c : ℝ) (x : Cube n) :
    (state n c *ᵥ character n S) x =
      ((1 + c) / 2) ^ (n - S.card) * ((1 - c) / 2) ^ S.card * character n S x := by
  unfold character
  rw [state_apply_product n c (fun i z => if i ∈ S then boolSign z else 1) x]
  have hfactor (i : Fin n) :
      (oneQubit c *ᵥ (fun z => if i ∈ S then boolSign z else 1)) (x i) =
        (if i ∈ S then (1 - c) / 2 else (1 + c) / 2) *
        (if i ∈ S then boolSign (x i) else 1) := by
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, oneQubit_apply_sign]
    · simp only [hi, ite_false, oneQubit_apply_one, mul_one]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, product_two_levels]

def hammingDistance (n : ℕ) (x z : Cube n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ z i).card

/--
@isnad1 id=eq.0h4v.s6.a31fb8607cda from=translated src=- shape=954bdbd4 vocab=c9aab2b6
-/
theorem state_entry (n : ℕ) (c : ℝ) (x z : Cube n) :
    state n c x z = c ^ hammingDistance n x z / (2 : ℝ) ^ n := by
  simp only [state, oneQubit, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Finset.prod_ite]
  simp [hammingDistance]

def antipodalMatrix (n : ℕ) : Matrix (Cube n) (Cube n) ℝ :=
  Equiv.Perm.permMatrix ℝ (antipode n)

/--
@isnad1 id=eq.0h3v.s6.ee436fecfb00 from=translated src=- shape=36b1129f vocab=b30737f3
-/
theorem antipodalMatrix_apply (n : ℕ) (v : Cube n → ℝ) (x : Cube n) :
    (antipodalMatrix n *ᵥ v) x = v (antipode n x) := by
  simp [antipodalMatrix, Matrix.permMatrix_mulVec]

/--
@isnad1 id=eq.0h3v.s6.eb8a392e2865 from=translated src=- shape=9f0c039b vocab=5f93e4ad
-/
theorem character_antipode (n : ℕ) (S : Finset (Fin n)) (x : Cube n) :
    character n S (antipode n x) = (-1 : ℝ) ^ S.card * character n S x := by
  unfold character
  have hfactor (i : Fin n) :
      (if i ∈ S then boolSign ((antipode n x) i) else 1) =
        (if i ∈ S then (-1 : ℝ) else 1) * (if i ∈ S then boolSign (x i) else 1) := by
    by_cases hi : i ∈ S
    · simp [hi, antipode, boolSign_neg]
    · simp [hi]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp

/--
@isnad1 id=eq.0h3v.s6.2b5756e41298 from=translated src=- shape=3a7873c4 vocab=c5c51ed0
-/
theorem antipodalMatrix_character (n : ℕ) (S : Finset (Fin n)) (x : Cube n) :
    (antipodalMatrix n *ᵥ character n S) x = (-1 : ℝ) ^ S.card * character n S x := by
  rw [antipodalMatrix_apply, character_antipode]

def normalization (n : ℕ) : ℝ := (Real.sqrt ((2 : ℝ) ^ n))⁻¹

/--
@isnad1 id=eq.0h1v.s5.f83e2c6f7607 from=translated src=- shape=a80393f4 vocab=17c17ed4
-/
theorem normalization_square (n : ℕ) : normalization n ^ 2 * (2 : ℝ) ^ n = 1 := by
  rw [normalization, inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀]
  positivity

/-- The normalized Walsh basis, as an actual orthogonal matrix.-/
def hadamard (n : ℕ) : Matrix (Cube n) (Cube n) ℝ :=
  fun x s => normalization n * Fourier.phase s x

/--
@isnad1 id=eq.0h1v.s4.7b5bce23e9a1 from=translated src=- shape=ba899254 vocab=07ef164b
-/
theorem hadamard_transpose (n : ℕ) : (hadamard n).transpose = hadamard n := by
  ext x s
  exact congrArg (normalization n * ·) (Fourier.phase_symm x s)

/--
@isnad1 id=eq.0h1v.s6.d71cdf6dd18f from=translated src=- shape=097af835 vocab=990c437b
-/
theorem hadamard_squared (n : ℕ) : hadamard n * hadamard n = 1 := by
  ext x z
  change (∑ s, (normalization n * Fourier.phase s x) *
    (normalization n * Fourier.phase z s)) = (1 : Matrix (Cube n) (Cube n) ℝ) x z
  calc
    _ = normalization n ^ 2 * ∑ s, Fourier.phase x s * Fourier.phase z s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fourier.phase_symm s x]
      ring
    _ = normalization n ^ 2 * (if x = z then (2 : ℝ) ^ n else 0) := by
      rw [Fourier.sum_phase_mul]
    _ = _ := by
      by_cases hxz : x = z
      · subst z
        simp [normalization_square]
      · simp [hxz, Matrix.one_apply_ne hxz]

def hadamardUnitary (n : ℕ) : Matrix.unitaryGroup (Cube n) ℝ :=
  ⟨hadamard n, Matrix.mem_unitaryGroup_iff.mpr (by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      hadamard_transpose] using hadamard_squared n)⟩

/--
@isnad1 id=eq.0h1v.s8.c2075ec89591 from=translated src=- shape=1e5e3ca6 vocab=c266b8cd
-/
theorem hadamardUnitary_coe (n : ℕ) :
    (hadamardUnitary n : Matrix (Cube n) (Cube n) ℝ) = hadamard n := rfl

/--
@isnad1 id=eq.0h4v.s7.6ef618ddae81 from=translated src=- shape=bb9b7bf7 vocab=63d3f371
-/
theorem state_phase (n : ℕ) (s : Cube n) (c : ℝ) (x : Cube n) :
    (state n c *ᵥ Fourier.phase s) x =
      ((1 + c) / 2) ^ (n - Fourier.degree s) *
      ((1 - c) / 2) ^ Fourier.degree s * Fourier.phase s x := by
  have hp : Fourier.phase s = character n (Fourier.support s) :=
    funext (Fourier.phase_character s)
  rw [hp]
  exact state_character n (Fourier.support s) c x

def eigenvalue (n : ℕ) (c : ℝ) (s : Cube n) : ℝ :=
  ((1 + c) / 2) ^ (n - Fourier.degree s) * ((1 - c) / 2) ^ Fourier.degree s

/--
@isnad1 id=eq.0h2v.s7.a8a2f9828130 from=translated src=- shape=55ab8831 vocab=05554cf1
-/
theorem state_mul_hadamard (n : ℕ) (c : ℝ) :
    state n c * hadamard n = hadamard n * Matrix.diagonal (eigenvalue n c) := by
  ext x s
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, hadamard]
  calc
    (∑ z, state n c x z * (normalization n * Fourier.phase s z)) =
        normalization n * (state n c *ᵥ Fourier.phase s) x := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = (normalization n * Fourier.phase s x) * eigenvalue n c s := by
      rw [state_phase]
      unfold eigenvalue
      ring

/--
@isnad1 id=eq.0h2v.s7.e5f5e9453800 from=translated src=- shape=115583b3 vocab=05554cf1
-/
theorem state_diagonalization (n : ℕ) (c : ℝ) :
    hadamard n * state n c * hadamard n = Matrix.diagonal (eigenvalue n c) := by
  rw [Matrix.mul_assoc, state_mul_hadamard, ← Matrix.mul_assoc, hadamard_squared, Matrix.one_mul]

/--
@isnad1 id=eq.0h3v.s6.dbb93ee6860e from=translated src=- shape=da3fcc3d vocab=01386bb4
-/
theorem antipodalMatrix_phase (n : ℕ) (s : Cube n) (x : Cube n) :
    (antipodalMatrix n *ᵥ Fourier.phase s) x =
      (-1 : ℝ) ^ Fourier.degree s * Fourier.phase s x := by
  have hp : Fourier.phase s = character n (Fourier.support s) :=
    funext (Fourier.phase_character s)
  rw [hp]
  exact antipodalMatrix_character n (Fourier.support s) x

/--
@isnad1 id=eq.0h1v.s7.8d67a8aa60b4 from=translated src=- shape=c091871b vocab=cfc3c4ea
-/
theorem antipodalMatrix_mul_hadamard (n : ℕ) :
    antipodalMatrix n * hadamard n =
      hadamard n * Matrix.diagonal (fun s => (-1 : ℝ) ^ Fourier.degree s) := by
  ext x s
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, hadamard]
  calc
    (∑ z, antipodalMatrix n x z * (normalization n * Fourier.phase s z)) =
        normalization n * (antipodalMatrix n *ᵥ Fourier.phase s) x := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = (normalization n * Fourier.phase s x) * ((-1 : ℝ) ^ Fourier.degree s) := by
      rw [antipodalMatrix_phase]
      ring

/--
@isnad1 id=eq.0h1v.s7.35843a52c99c from=translated src=- shape=2a4a8541 vocab=cfc3c4ea
-/
theorem antipodalMatrix_diagonalization (n : ℕ) :
    hadamard n * antipodalMatrix n * hadamard n =
      Matrix.diagonal (fun s => (-1 : ℝ) ^ Fourier.degree s) := by
  rw [Matrix.mul_assoc, antipodalMatrix_mul_hadamard, ← Matrix.mul_assoc,
    hadamard_squared, Matrix.one_mul]

end

end Hellinger.ProductState
