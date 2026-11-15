import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open scoped Modular MatrixGroups Pointwise

namespace FLT.SiegelSetCover

/--
@isnad1 id=le.1h1v.s5.2e494d85c21e from=translated src=- shape=15579f16 vocab=5b9e1a02
-/
theorem sqrt_three_div_two_le_im_of_mem_fd {τ : ℍ} (h : τ ∈ 𝒟) :
    Real.sqrt 3 / 2 ≤ τ.im := by
  have h1 : 3 ≤ 4 * τ.im ^ 2 := three_le_four_mul_im_sq_of_mem_fd h
  have h2 : Real.sqrt 3 ≤ 2 * τ.im := by
    rw [Real.sqrt_le_left (by linarith [τ.im_pos])]
    nlinarith
  linarith

/--
@isnad1 id=ex.0h1v.s7.63466adb031f from=translated src=- shape=39872d68 vocab=0e94465d
-/
theorem exists_sqrt_three_div_two_le_im_smul (z : ℍ) :
    ∃ g : SL(2, ℤ), Real.sqrt 3 / 2 ≤ (g • z).im := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  exact ⟨g, sqrt_three_div_two_le_im_of_mem_fd hg⟩

/--
@isnad1 id=ex.0h2v.s9.68cf83f5eeb3 from=translated src=- shape=158470dd vocab=d984210f
-/
theorem exists_out_smul_smul_mem_fd (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ γ ∈ Γ, ∃ q : SL(2, ℤ) ⧸ Γ, Quotient.out q • (γ • z) ∈ 𝒟 := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g
  refine ⟨(h : SL(2, ℤ))⁻¹, Γ.inv_mem h.2, QuotientGroup.mk g, ?_⟩
  rw [hh, mul_smul, smul_inv_smul]
  exact hg

/--
@isnad1 id=ex.0h2v.s9.79cded095a52 from=translated src=- shape=b058d506 vocab=4b105350
-/
theorem exists_smul_mem_iUnion_smul_fd (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ γ ∈ Γ, γ • z ∈ ⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • 𝒟 := by
  obtain ⟨γ, hγ, q, hq⟩ := exists_out_smul_smul_mem_fd Γ z
  exact ⟨γ, hγ, Set.mem_iUnion.mpr ⟨q, Set.mem_inv_smul_set_iff.mpr hq⟩⟩

/--
@isnad1 id=ex.0h2v.s9.d64a1f7247dc from=translated src=- shape=3fe6d5d2 vocab=2721bcad
-/
theorem exists_out_smul_smul_im_ge (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ γ ∈ Γ, ∃ q : SL(2, ℤ) ⧸ Γ,
      Real.sqrt 3 / 2 ≤ (Quotient.out q • (γ • z)).im := by
  obtain ⟨γ, hγ, q, hq⟩ := exists_out_smul_smul_mem_fd Γ z
  exact ⟨γ, hγ, q, sqrt_three_div_two_le_im_of_mem_fd hq⟩

/--
@isnad1 id=finite.0h1v.s6.5bc7b0d416d7 from=translated src=- shape=a5228e88 vocab=4d80c3f7
-/
theorem finite_quotient_gamma0 (N : ℕ) [NeZero N] : Finite (SL(2, ℤ) ⧸ Gamma0 N) :=
  Subgroup.finite_quotient_of_finiteIndex

/--
@isnad1 id=ex.0h2v.s9.8bdc58ea8b61 from=translated src=- shape=d0957cce vocab=03534910
-/
theorem exists_gamma0_smul_mem_iUnion_smul_fd (N : ℕ) (z : ℍ) :
    ∃ γ ∈ Gamma0 N, γ • z ∈ ⋃ q : SL(2, ℤ) ⧸ Gamma0 N, (Quotient.out q)⁻¹ • 𝒟 :=
  exists_smul_mem_iUnion_smul_fd (Gamma0 N) z

private theorem one_le_quadratic_form (c d : ℤ) (h : c ≠ 0 ∨ d ≠ 0) :
    1 ≤ c ^ 2 - c * d + d ^ 2 := by
  have key : 0 < c ^ 2 - c * d + d ^ 2 := by
    rcases h with hc | hd
    · rcases lt_or_gt_of_ne hc with h' | h' <;>
        nlinarith [sq_nonneg (c - 2 * d), Int.add_one_le_iff.mpr h']
    · rcases lt_or_gt_of_ne hd with h' | h' <;>
        nlinarith [sq_nonneg (2 * c - d), Int.add_one_le_iff.mpr h']
  linarith [Int.add_one_le_iff.mpr key]

/--
@isnad1 id=eq.0h0v.s4.f7cf9ccc0f92 from=translated src=- shape=36b490a0 vocab=6923a84b
-/
theorem gate_im_rho : (UpperHalfPlane.ρ).im = Real.sqrt 3 / 2 := rfl

/--
@isnad1 id=mem.0h0v.s3.5e5cc3925686 from=translated src=- shape=d1530203 vocab=eb27051d
-/
theorem gate_rho_mem_fd : UpperHalfPlane.ρ ∈ 𝒟 := by
  constructor
  · show (1 : ℝ) ≤ Complex.normSq (UpperHalfPlane.ρ : ℂ)
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    rw [Complex.normSq_apply,
      show ((UpperHalfPlane.ρ : ℂ)).re = -1 / 2 from rfl,
      show ((UpperHalfPlane.ρ : ℂ)).im = Real.sqrt 3 / 2 from rfl]
    nlinarith
  · show |(UpperHalfPlane.ρ).re| ≤ (1 : ℝ) / 2
    rw [show (UpperHalfPlane.ρ).re = -1 / 2 from rfl]
    rw [abs_le]
    norm_num

/--
@isnad1 id=le.0h1v.s7.f4dca617808f from=translated src=- shape=7aa1572e vocab=e4a4bd71
-/
theorem gate_im_smul_rho_le (g : SL(2, ℤ)) :
    (g • UpperHalfPlane.ρ).im ≤ Real.sqrt 3 / 2 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hcd : (g 1 0 : ℤ) ≠ 0 ∨ (g 1 1 : ℤ) ≠ 0 :=
    (bottom_row_coprime g).ne_zero_or_ne_zero
  have hint : (1 : ℤ) ≤ g 1 0 ^ 2 - g 1 0 * g 1 1 + g 1 1 ^ 2 :=
    one_le_quadratic_form _ _ hcd
  have hden : (1 : ℝ) ≤ Complex.normSq (denom g UpperHalfPlane.ρ) := by
    have heq : Complex.normSq (denom g UpperHalfPlane.ρ) =
        ((g 1 0 ^ 2 - g 1 0 * g 1 1 + g 1 1 ^ 2 : ℤ) : ℝ) := by
      rw [ModularGroup.denom_apply]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      rw [show (UpperHalfPlane.ρ).re = -1 / 2 from rfl,
        show (UpperHalfPlane.ρ).im = Real.sqrt 3 / 2 from rfl]
      push_cast
      linear_combination ((g 1 0 : ℤ) : ℝ) ^ 2 / 4 * h3
    rw [heq]
    exact_mod_cast hint
  rw [ModularGroup.im_smul_eq_div_normSq]
  calc (UpperHalfPlane.ρ).im / Complex.normSq (denom g UpperHalfPlane.ρ)
      ≤ (UpperHalfPlane.ρ).im := by
        refine div_le_self ?_ hden
        rw [gate_im_rho]
        positivity
    _ = Real.sqrt 3 / 2 := gate_im_rho

/--
@isnad1 id=lt.0h0v.s5.4946481e508c from=translated src=- shape=3825b7fd vocab=01c0b07d
-/
theorem gate_one_half_lt_sqrt_three_div_two : (1 : ℝ) / 2 < Real.sqrt 3 / 2 := by
  have : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/--
@isnad1 id=not.0h0v.s7.cdd9c0401585 from=translated src=- shape=d0d9d1f3 vocab=65d1aa3f
-/
theorem gate_S_not_mem_gamma0_two : ModularGroup.S ∉ Gamma0 2 := by
  intro hmem
  rw [Gamma0_mem] at hmem
  exact absurd hmem (by decide)

end FLT.SiegelSetCover
