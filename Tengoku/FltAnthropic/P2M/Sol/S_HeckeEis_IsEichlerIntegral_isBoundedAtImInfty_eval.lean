import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv
import Tengoku.FltAnthropic.Theorems.Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt
import Tengoku.FltAnthropic.Theorems.Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binaryFormRepSL jFactor IsEichlerIntegral jFactor_pow_mul_eval_binaryFormRepSL)
namespace LadderAux2
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial Filter Function
open scoped MatrixGroups Manifold Topology

variable {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)}

def rung (G : ℍ → ↥(BinaryForm ℂ n)) (j : ℕ) (τ : ℍ) : ℂ :=
  MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((MvPolynomial.pderiv 1)^[j] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))

/--
@isnad1 id=eq.0h3v.s9.5c7639f8e14e from=translated src=- shape=10bd5a35 vocab=37a009c7
-/
theorem rung_zero (G : ℍ → ↥(BinaryForm ℂ n)) (τ : ℍ) :
    rung G 0 τ = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) := rfl

/--
@isnad1 id=eq.0h3v.s7.dc72573d407a from=translated src=- shape=70ad559d vocab=31f47573
-/
theorem rung_succ_n (G : ℍ → ↥(BinaryForm ℂ n)) (τ : ℍ) : rung G (n + 1) τ = 0 := by
  rw [rung, MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt ((mem_homogeneousSubmodule n _).mp (G τ).2) 1
    (Nat.lt_succ_self n), map_zero]

/--
@isnad1 id=hasderiv.2h5v.s8.2ee1f52d2086 from=translated src=- shape=f5a06dcc vocab=d714d23f
-/
theorem hasDerivAt_rung (hG : IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n) (τ : ℍ) :
    HasDerivAt (rung G j ∘ ofComplex)
      ((if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - rung G (j + 1) τ) (τ : ℂ) := by
  have h := hG.hasDerivAt_eval_iterate_pderiv hj τ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
  simp only [Function.comp_apply, rung]
  rw [ofComplex_apply_of_im_pos hz]

/--
@isnad1 id=mdiffere.2h4v.s8.7414f902ad34 from=translated src=- shape=46cc7d58 vocab=a5b8c798
-/
theorem mdifferentiable_rung (hG : IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (rung G j) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (hasDerivAt_rung hG hj ⟨z, hz⟩).differentiableAt.differentiableWithinAt

/--
@isnad1 id=eq.0h2v.s5.2d7e7105188e from=translated src=- shape=150d07b6 vocab=ddec7705
-/
theorem ofComplex_coe_add_real (τ : ℍ) (p : ℝ) : ofComplex ((τ : ℂ) + (p : ℂ)) = (p +ᵥ τ) := by
  have him : 0 < ((τ : ℂ) + (p : ℂ)).im := by simpa using τ.im_pos
  rw [ofComplex_apply_of_im_pos him]
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_vadd, add_comm]

section Periodic

variable {h : ℤ}

/--
@isnad1 id=periodic.1h2v.s6.af71678ba0ca from=translated src=- shape=aa996c24 vocab=96040df3
-/
theorem periodic_comp_ofComplex {φ : ℍ → ℂ} {p : ℝ} (hφ : ∀ τ : ℍ, φ (p +ᵥ τ) = φ τ) :
    Periodic (φ ∘ ofComplex) (p : ℂ) := by
  intro z
  simp only [Function.comp_apply]
  rcases lt_or_ge 0 z.im with hz | hz
  · rw [← hφ (ofComplex z), ← ofComplex_coe_add_real (ofComplex z) p,
      ofComplex_apply_of_im_pos hz]
  · have hz' : (z + (p : ℂ)).im ≤ 0 := by simpa using hz
    rw [ofComplex_apply_of_im_nonpos hz', ofComplex_apply_of_im_nonpos hz]

/--
@isnad1 id=eq.1h4v.s12.73e075298f4d from=translated src=- shape=3496369c vocab=1a706e3d
-/
theorem rung_zero_vadd (hT : ∀ τ : ℍ, G ((h : ℝ) +ᵥ τ) = binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) (τ : ℍ) :
    rung G 0 ((h : ℝ) +ᵥ τ) = rung G 0 τ := by
  rw [rung_zero, rung_zero, hT]
  have key := HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL n (ModularGroup.T ^ h) τ (G τ)
  have hj : jFactor (ModularGroup.T ^ h) τ = 1 := by
    simp [jFactor, ModularGroup.coe_T_zpow]
  rw [hj, one_pow, one_mul, UpperHalfPlane.modular_T_zpow_smul] at key
  simpa using key

/--
@isnad1 id=eq.4h6v.s12.9b8a15db1e79 from=translated src=- shape=5ed9b23d vocab=788db8d7
-/
theorem rung_vadd (hG : IsEichlerIntegral n g G) (hper : ∀ τ : ℍ, g ((h : ℝ) +ᵥ τ) = g τ)
    (hT : ∀ τ : ℍ, G ((h : ℝ) +ᵥ τ) = binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    ∀ j : ℕ, j ≤ n + 1 → ∀ τ : ℍ, rung G j ((h : ℝ) +ᵥ τ) = rung G j τ := by
  intro j
  induction j with
  | zero => exact fun _ τ => rung_zero_vadd hT τ
  | succ j ih =>
    intro hj τ
    have hj' : j ≤ n := by omega
    have hperj : Periodic (rung G j ∘ ofComplex) ((h : ℝ) : ℂ) := periodic_comp_ofComplex (ih (by omega))

    have h1 : HasDerivAt (rung G j ∘ ofComplex)
        ((if j = n then ((n.factorial : ℕ) : ℂ) * g ((h : ℝ) +ᵥ τ) else 0) - rung G (j + 1) ((h : ℝ) +ᵥ τ)) (τ : ℂ) := by
      have h0 := hasDerivAt_rung hG hj' ((h : ℝ) +ᵥ τ)
      rw [UpperHalfPlane.coe_vadd, add_comm ((h : ℝ) : ℂ) (τ : ℂ)] at h0
      have h2 := h0.comp_add_const (τ : ℂ) ((h : ℝ) : ℂ)
      have hfun : (fun x : ℂ => (rung G j ∘ ofComplex) (x + ((h : ℝ) : ℂ))) = rung G j ∘ ofComplex := funext hperj
      rwa [hfun] at h2
    have h3 := hasDerivAt_rung hG hj' τ
    have h4 := h1.unique h3
    rw [hper τ] at h4

    have := congrArg (fun w => (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - w) h4
    simpa using this

end Periodic

/--
@isnad1 id=isbounde.6h4v.s12.6c61d0b8ef27 from=translated src=- shape=4565fb51 vocab=6a8b9b20
-/
theorem isBoundedAtImInfty_rung_zero (hG : IsEichlerIntegral n g G) {h : ℤ} (hh : 0 < h)
    (hper : Periodic (g ∘ ofComplex) ((h : ℝ) : ℂ)) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hbdd : IsBoundedAtImInfty g)
    (hT : ∀ τ : ℍ, G ((h : ℝ) +ᵥ τ) = binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    IsBoundedAtImInfty (rung G 0) := by
  have hh' : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hperℍ : ∀ τ : ℍ, g ((h : ℝ) +ᵥ τ) = g τ := by
    intro τ
    have := hper (τ : ℂ)
    simp only [Function.comp_apply] at this
    rw [ofComplex_coe_add_real τ h, ofComplex_apply] at this
    exact this
  have hrper := rung_vadd hG hperℍ hT

  have key : ∀ i : ℕ, i ≤ n + 1 → IsBoundedAtImInfty (rung G (n + 1 - i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      have : rung G (n + 1 - 0) = 0 := funext fun τ => by simpa using rung_succ_n G τ
      rw [this]
      exact UpperHalfPlane.zero_form_isBoundedAtImInfty
    | succ i ih =>
      intro hi
      set j := n + 1 - (i + 1) with hjdef
      have hj : j ≤ n := by omega
      have hj1 : n + 1 - i = j + 1 := by omega
      have ih' : IsBoundedAtImInfty (rung G (j + 1)) := by rw [← hj1]; exact ih (by omega)

      set u : ℍ → ℂ := fun τ => (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0) - rung G (j + 1) τ with hu
      have hu_per : Periodic (u ∘ ofComplex) ((h : ℝ) : ℂ) := by
        apply periodic_comp_ofComplex
        intro τ
        simp only [hu, hperℍ τ, hrper (j + 1) (by omega) τ]
      have hu_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u := by
        have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (rung G (j + 1)) := by
          rcases eq_or_lt_of_le hj with hjn | hjn
          · have : rung G (j + 1) = fun _ => 0 := funext fun τ => by rw [hjn]; exact rung_succ_n G τ
            rw [this]; exact mdifferentiable_const
          · exact mdifferentiable_rung hG (by omega)
        have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0)) := by
          split_ifs
          · exact mdifferentiable_const.mul hhol
          · exact mdifferentiable_const
        exact h1.sub h2
      have hu_bdd : IsBoundedAtImInfty u := by
        have h1 : IsBoundedAtImInfty (fun τ : ℍ => (if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0)) := by
          split_ifs
          · exact hbdd.const_mul_left _
          · exact UpperHalfPlane.zero_form_isBoundedAtImInfty
        exact h1.sub ih'
      have hv : ∀ τ : ℍ, HasDerivAt (rung G j ∘ ofComplex) (u τ) (τ : ℂ) := fun τ => hasDerivAt_rung hG hj τ
      have hv_per : Periodic (rung G j ∘ ofComplex) ((h : ℝ) : ℂ) := periodic_comp_ofComplex (hrper j (by omega))
      exact UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic hh' hu_per hu_hol hu_bdd hv hv_per
  simpa using key (n + 1) le_rfl

end HeckeEis.LadderAux2

end

open scoped MatrixGroups Manifold in

/--
@isnad1 id=isbounde.6h4v.s12.3c96ea02002f from=translated src=- shape=31ac93e5 vocab=1116fcba
-/
theorem solution {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {h : ℤ} (hh : 0 < h)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hbdd : UpperHalfPlane.IsBoundedAtImInfty g)
    (hT : ∀ τ : UpperHalfPlane, G ((h : ℝ) +ᵥ τ) = HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) :=
  HeckeEis.LadderAux2.isBoundedAtImInfty_rung_zero hG hh hper hhol hbdd hT

