import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace PDT
open Matrix

/-!
# The (2,1) signature of the trace form of K = ℚ[x]/(x³ − x − 1)  (the ρ / 3-space side)

Companion to `PdtSignature` (the quartic Q / 4D side, signature (3,1)). The cubic
ρ = real root of x³ − x − 1 governs 3-space; its trace form has signature (2,1).
Power sums of the roots (Newton, e₁=0, e₂=−1, e₃=1): p₀=3, p₁=0, p₂=2, p₃=3, p₄=2,
so the Gram matrix in the power basis {1,x,x²} is `Mρ = !![3,0,2; 0,2,3; 2,3,2]`
(Mρ_{ij} = p_{i+j}). We prove, all kernel-checked: `det Mρ = −23 = disc(x³−x−1)`,
and an explicit ℚ-congruence `Pρᵀ Mρ Pρ = Dρ = diag(3, 2, −23/6)` with two positive
and one negative diagonal entry, so by Sylvester's law the signature is (2,1).
-/

def Mρ : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,2; 0,2,3; 2,3,2]
def Pρ : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,-2/3; 0,1,-3/2; 0,0,1]
def Dρ : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,0; 0,2,0; 0,0,-23/6]

/--
@isnad1 id=issymm.0h0v.s3.444d8ab06403 from=translated src=- shape=d3a93718 vocab=e4182cd1
-/
theorem Mρ_symm : Mρ.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mρ, Matrix.transpose_apply]

/--
@isnad1 id=eq.0h0v.s5.fe83abb0c562 from=translated src=- shape=e5ac977b vocab=bbf960e8
-/
theorem detMρ : Mρ.det = -23 := by
  simp [Matrix.det_fin_three, Mρ]; norm_num

/--
@isnad1 id=eq.0h0v.s7.311a72e10c8c from=translated src=- shape=a8c27b39 vocab=e16053e9
-/
theorem congruenceρ : Pρ.transpose * Mρ * Pρ = Dρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pρ, Mρ, Dρ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> norm_num

/--
@isnad1 id=eq.0h0v.s4.68cc4c7d8434 from=translated src=- shape=5ca0a7a0 vocab=3d6f5279
-/
theorem detPρ : Pρ.det = 1 := by
  simp [Matrix.det_fin_three, Pρ]

/--
@isnad1 id=isunit.0h0v.s4.bac2b8ca62c5 from=translated src=- shape=4d15e069 vocab=78761f87
-/
theorem Pρ_isUnit : IsUnit Pρ.det := by rw [detPρ]; exact isUnit_one

/--
@isnad1 id=isdiag.0h0v.s3.0daa7124ea8e from=translated src=- shape=d3a93718 vocab=b1ccbead
-/
theorem Dρ_isDiag : Dρ.IsDiag := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Dρ]

/--
@isnad1 id=lt.0h0v.s5.0c74be508920 from=translated src=- shape=2a8c603f vocab=20daf7e3
-/
theorem Dρ00_pos : (0:ℚ) < Dρ 0 0 := by show (0:ℚ) < 3; norm_num
/--
@isnad1 id=lt.0h0v.s5.426774914341 from=translated src=- shape=2a8c603f vocab=20daf7e3
-/
theorem Dρ11_pos : (0:ℚ) < Dρ 1 1 := by show (0:ℚ) < 2; norm_num
/--
@isnad1 id=lt.0h0v.s5.e55d15b995fb from=translated src=- shape=b4dc571a vocab=20daf7e3
-/
theorem Dρ22_neg : Dρ 2 2 < (0:ℚ) := by show (-23/6:ℚ) < 0; norm_num

end PDT
