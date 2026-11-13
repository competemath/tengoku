import Tengoku.Nlalib.NLAlib.Matrix.Structured.RadixTwoDFTSplit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A literal radix-two realization of the standard discrete Fourier transform

The input and output permutations are the canonical finite cyclic coordinates.
All root identities used by the recursion are discharged for the standard
negative character. Arithmetic counts refer to the recursive implementation,
with supplied twiddles and permutations free. Source: Golub–Van Loan, §1.4.
-/
noncomputable section

namespace ZMod

/-- The canonical equivalence from finite indices to residues is the natural cast.
@isnad1 id=eq.0h2v.s7.e140b1a5068d from=translated src=- shape=be63ca47 vocab=2f80e219
-/
theorem finEquiv_apply_eq_natCast {n : ℕ} [NeZero n] (j : Fin n) :
    finEquiv n j = (j.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hv : (finEquiv (n + 1) j).val = j.val := rfl
    rw [← hv]
    exact (ZMod.natCast_zmod_val _).symm

end ZMod

namespace NLAlib.RadixTwoFFT

/-- Correctness of the actual recursion in the standard cyclic DFT coordinates.
Source: Golub–Van Loan, §1.4.
atlas: radix-two-fft-realization (partial)
@isnad1 id=eq.0h3v.s9.b0f1c7760464 from=translated src=- shape=baac2a65 vocab=72cd1b5d
-/
theorem run_value_eq_dft (s : ℕ) (x : ZMod (size s) → ℂ) (k : Fin (size s)) :
    (run s (ZMod.stdAddChar (-1 : ZMod (size s)))
      (fun j => x (ZMod.finEquiv (size s) j))).value k =
      ZMod.dft x (ZMod.finEquiv (size s) k) := by
  rw [run_value_eq_polynomialDFT _ _ _ (hasRootSchedule_standardRoot s),
    polynomialDFT, ZMod.dft_apply]
  apply Fintype.sum_equiv (ZMod.finEquiv (size s)).toEquiv
  intro j
  simp only [smul_eq_mul, standardRoot_pow, RingEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, ZMod.finEquiv_apply_eq_natCast,
    Nat.cast_mul]

/-- The forward transform, including the arithmetic counts accumulated by its
actual recursive butterfly calls.-/
def transform (s : ℕ) (x : ZMod (size s) → ℂ) :
    ArithmeticResult (ZMod (size s) → ℂ) :=
  let r := run s (ZMod.stdAddChar (-1 : ZMod (size s)))
    (fun j => x (ZMod.finEquiv (size s) j))
  ⟨fun k => r.value ((ZMod.finEquiv (size s)).symm k), r.mulCount, r.addCount⟩

/-- The literal forward transform is Mathlib's standard negative-exponent DFT.
Source: Golub–Van Loan, §1.4.
atlas: radix-two-fft-realization (partial)
@isnad1 id=eq.0h2v.s8.373979e4e500 from=translated src=- shape=02b3d174 vocab=d2d91fa2
-/
theorem transform_value_eq_dft (s : ℕ) (x : ZMod (size s) → ℂ) :
    (transform s x).value = ZMod.dft x := by
  funext k
  simpa only [transform, RingEquiv.apply_symm_apply] using
    run_value_eq_dft s x ((ZMod.finEquiv (size s)).symm k)

/-- Exact multiplication count for every nontrivial radix-two forward transform.
@isnad1 id=eq.0h2v.s6.3136b865604c from=translated src=- shape=0e2243be vocab=fd639d80
-/
theorem transform_mulCount_succ (s : ℕ) (x : ZMod (size (s + 1)) → ℂ) :
    (transform (s + 1) x).mulCount = (s + 1) * 2 ^ s := by
  exact run_mulCount_succ_eq s (ZMod.stdAddChar (-1 : ZMod (size (s + 1))))
    (fun j => x (ZMod.finEquiv (size (s + 1)) j))

/-- Exact addition/subtraction count, including the length-one base case.
@isnad1 id=eq.0h2v.s5.f3c906fc0479 from=translated src=- shape=37a9478b vocab=f282d22c
-/
theorem transform_addCount (s : ℕ) (x : ZMod (size s) → ℂ) :
    (transform s x).addCount = s * 2 ^ s :=
  run_addCount_eq s _ _

/-- Division-free multiplication-count formula, including the length-one case.
@isnad1 id=eq.0h2v.s5.5e3e758b2b0f from=translated src=- shape=ca9b5ad7 vocab=dd62f1fa
-/
theorem transform_mulCount_twice (s : ℕ) (x : ZMod (size s) → ℂ) :
    2 * (transform s x).mulCount = s * size s := by
  cases s with
  | zero => simp [transform, run]
  | succ s => rw [transform_mulCount_succ, size_eq_two_pow, Nat.pow_succ]; ring

/-- The inverse realization calls the same FFT, reverses the frequency labels,
then performs exactly one scalar multiplication at each output coordinate.-/
def inverseTransform (s : ℕ) (x : ZMod (size s) → ℂ) :
    ArithmeticResult (ZMod (size s) → ℂ) :=
  let r := transform s x
  ⟨fun k => (size s : ℂ)⁻¹ * r.value (-k), r.mulCount + size s, r.addCount⟩

/-- Correctness of the actual inverse FFT, with its normalization.
Source: Golub–Van Loan, §1.4.
atlas: radix-two-fft-realization
@isnad1 id=eq.0h2v.s8.97d527a7729b from=translated src=- shape=38fe6bc2 vocab=658ced52
-/
theorem inverseTransform_value_eq_invDFT (s : ℕ) (x : ZMod (size s) → ℂ) :
    (inverseTransform s x).value = ZMod.dft.symm x := by
  funext k
  simp only [inverseTransform, transform_value_eq_dft, ZMod.invDFT_apply', smul_eq_mul]

/-- The inverse uses the same butterflies plus one output scaling per coordinate.
@isnad1 id=and.0h2v.s5.d67ec90d21a0 from=translated src=- shape=53e11051 vocab=caacb118
-/
theorem inverseTransform_cost (s : ℕ) (x : ZMod (size s) → ℂ) :
    (inverseTransform s x).mulCount = (transform s x).mulCount + size s ∧
      (inverseTransform s x).addCount = (transform s x).addCount := ⟨rfl, rfl⟩

end NLAlib.RadixTwoFFT
