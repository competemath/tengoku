import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Quaternion

namespace QuaternionAlgebra

section ReducedNorm

variable {R : Type*} [CommRing R] {a b : R}

def nrd (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def trd (x : ℍ[R, a, b]) : R := 2 * x.re

/--
@isnad1 id=eq.0h7v.s7.98c12aaabfbf from=translated src=- shape=394c7116 vocab=e0fc4b46
-/
@[simp] theorem nrd_mk (x₀ x₁ x₂ x₃ : R) :
    nrd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 := rfl

/--
@isnad1 id=eq.0h7v.s6.4740f00676b9 from=translated src=- shape=2963e861 vocab=6164697b
-/
@[simp] theorem trd_mk (x₀ x₁ x₂ x₃ : R) :
    trd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = 2 * x₀ := rfl

/--
@isnad1 id=eq.0h3v.s6.1afe8ddfaeb2 from=translated src=- shape=464f1bf2 vocab=c6fe3211
-/
@[simp] theorem nrd_zero : nrd (0 : ℍ[R, a, b]) = 0 := by simp [nrd]
/--
@isnad1 id=eq.0h3v.s6.4eb92c86ae9e from=translated src=- shape=464f1bf2 vocab=c6fe3211
-/
@[simp] theorem nrd_one : nrd (1 : ℍ[R, a, b]) = 1 := by simp [nrd]
/--
@isnad1 id=eq.0h4v.s6.905747c1c94c from=translated src=- shape=7e926a25 vocab=7d5155d3
-/
@[simp] theorem nrd_neg (x : ℍ[R, a, b]) : nrd (-x) = nrd x := by simp [nrd]
/--
@isnad1 id=eq.0h4v.s6.c68496b188a3 from=translated src=- shape=7e926a25 vocab=f0a691da
-/
@[simp] theorem nrd_star (x : ℍ[R, a, b]) : nrd (star x) = nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp only [star_mk, nrd_mk]; ring
/--
@isnad1 id=eq.0h4v.s6.6cde9cbf7f0b from=translated src=- shape=adf90a4b vocab=ba5b1628
-/
@[simp] theorem nrd_coe (r : R) : nrd ((r : R) : ℍ[R, a, b]) = r ^ 2 := by simp [nrd]

/--
@isnad1 id=eq.0h4v.s7.637d9db2d602 from=translated src=- shape=fd1352dd vocab=036bc2cb
-/
theorem mul_star_eq_coe_nrd (x : ℍ[R, a, b]) : x * star x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

/--
@isnad1 id=eq.0h4v.s7.408f15561f92 from=translated src=- shape=c5463db7 vocab=036bc2cb
-/
theorem star_mul_eq_coe_nrd (x : ℍ[R, a, b]) : star x * x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

/--
@isnad1 id=eq.0h4v.s7.0af468b6b8b6 from=translated src=- shape=fd1352dd vocab=99cc67e6
-/
theorem add_star_eq_coe_trd (x : ℍ[R, a, b]) : x + star x = ((trd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_add_mk, trd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

end ReducedNorm

end QuaternionAlgebra
