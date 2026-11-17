import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand

set_option autoImplicit false

open scoped MatrixGroups ModularForm UpperHalfPlane Manifold Topology Matrix
open ModularForm UpperHalfPlane CongruenceSubgroup Set Filter Function Topology

noncomputable section

namespace EisensteinSeries
export _root_.EisensteinSeries (summable_one_div_norm_rpow eisSummand_SL2_apply summand_bound_of_mem_verticalStrip eisSummand eisSummand_extension_differentiableOn summable_norm_eisSummand r)
namespace FullLattice
open _root_.EisensteinSeries

section Coset

variable (N : ℕ)

def coset (v : Fin 2 → ZMod N) : Set (Fin 2 → ℤ) := {x | ((↑) : ℤ → ZMod N) ∘ x = v}

/--
@isnad1 id=iff.0h3v.s6.410efc313c4d from=translated src=- shape=40b8b8be vocab=cb3b1222
-/
theorem mem_coset {v : Fin 2 → ZMod N} {x : Fin 2 → ℤ} :
    x ∈ coset N v ↔ ((↑) : ℤ → ZMod N) ∘ x = v := Iff.rfl

def red (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)

/--
@isnad1 id=eq.0h2v.s7.a1ef40d33198 from=translated src=- shape=501d32c6 vocab=520c3d02
-/
theorem red_eq (γ : SL(2, ℤ)) :
    red N γ = (γ : Matrix (Fin 2) (Fin 2) ℤ).map ⇑(Int.castRingHom (ZMod N)) := by
  rw [red, Int.coe_castRingHom]

/--
@isnad1 id=eq.0h3v.s8.3fcea7fcf280 from=translated src=- shape=96f4848b vocab=f1f42e2b
-/
theorem red_mul (γ δ : SL(2, ℤ)) : red N (γ * δ) = red N γ * red N δ := by
  rw [red_eq, red_eq, red_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

/--
@isnad1 id=eq.0h1v.s7.de366926646a from=translated src=- shape=4a4f560f vocab=2cf41345
-/
theorem red_one : red N 1 = 1 := by
  rw [red_eq, Matrix.SpecialLinearGroup.coe_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/--
@isnad1 id=eq.0h3v.s7.a9dbc416991d from=translated src=- shape=6da47951 vocab=74a9fdf9
-/
theorem comp_vecMul (x : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    ((↑) : ℤ → ZMod N) ∘ (x ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) = (((↑) : ℤ → ZMod N) ∘ x) ᵥ* red N γ := by
  funext i
  have hi := RingHom.map_vecMul (Int.castRingHom (ZMod N)) (γ : Matrix (Fin 2) (Fin 2) ℤ) x i
  simp only [Int.coe_castRingHom] at hi
  exact hi

/--
@isnad1 id=mem.1h4v.s7.d22763891127 from=translated src=- shape=e498b191 vocab=85f0234b
-/
theorem vecMul_mem_coset {v : Fin 2 → ZMod N} {x : Fin 2 → ℤ} (hx : x ∈ coset N v) (γ : SL(2, ℤ)) :
    x ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) ∈ coset N (v ᵥ* red N γ) := by
  rw [mem_coset, comp_vecMul, (mem_coset N).mp hx]

def cosetEquiv (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : coset N v ≃ coset N (v ᵥ* red N γ) where
  toFun x := ⟨x.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ), vecMul_mem_coset N x.2 γ⟩
  invFun y := ⟨y.1 ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), by
    have h := vecMul_mem_coset N y.2 γ⁻¹
    rwa [Matrix.vecMul_vecMul, ← red_mul, mul_inv_cancel, red_one, Matrix.vecMul_one v] at h⟩
  left_inv x := by
    apply Subtype.ext
    simp only
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.vecMul_one x.1]
  right_inv y := by
    apply Subtype.ext
    simp only
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.vecMul_one y.1]

/--
@isnad1 id=eq.1h2v.s8.d6b2c402ac58 from=translated src=- shape=bdfebd5b vocab=153da2cd
-/
theorem red_eq_one_of_mem_Gamma {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N) : red N γ = 1 := by
  have h := Gamma_mem'.mp hγ
  have h2 := congrArg (fun A : SL(2, ZMod N) => (A : Matrix (Fin 2) (Fin 2) (ZMod N))) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.coe_one] at h2
  rw [red_eq]
  exact h2

end Coset

section Series

variable (N : ℕ) (k : ℤ)

def G (v : Fin 2 → ZMod N) (z : ℍ) : ℂ := ∑' x : coset N v, eisSummand k x z

/--
@isnad1 id=eq.0h4v.s7.fcc6586e98c9 from=translated src=- shape=32142960 vocab=cfbfe882
-/
theorem G_slash_apply (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    (G N k v) ∣[k] γ = G N k (v ᵥ* red N γ) := by
  ext1 z
  simp_rw [SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    G, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (cosetEquiv N v γ).tsum_eq (eisSummand k · z)

def GSIF (v : Fin 2 → ZMod N) : SlashInvariantForm (Gamma N) k where
  toFun := G N k v
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Gamma N), rfl⟩ := hA
    have h1 : (G N k v) ∣[k] A = G N k v := by
      rw [G_slash_apply, red_eq_one_of_mem_Gamma N hA, Matrix.vecMul_one v]
    simpa [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash] using h1

/--
@isnad1 id=eq.0h3v.s8.68a0bd7e4fc5 from=translated src=- shape=019a1e75 vocab=9e1fd5e0
-/
theorem coe_GSIF (v : Fin 2 → ZMod N) : (⇑(GSIF N k v) : ℍ → ℂ) = G N k v := rfl

end Series

section Analytic

variable {N : ℕ} {k : ℤ}

/--
@isnad1 id=tendstol.1h3v.s7.4d3a921adeed from=translated src=- shape=a07d3059 vocab=58b4ccff
-/
theorem G_tendstoLocallyUniformly (hk : 3 ≤ k) (v : Fin 2 → ZMod N) :
    TendstoLocallyUniformly (fun (s : Finset (coset N v)) ↦ (∑ x ∈ s, eisSummand k x ·))
      (G N k v ·) atTop := by
  have hk' : (2 : ℝ) < k := by norm_cast
  have p_sum : Summable fun x : coset N v ↦ ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (coset N v)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, G]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := p_sum.mul_left <| r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))
    (fun p z hz ↦ ?_)).mono HABK
  simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) p hB hz

/--
@isnad1 id=tendstol.1h3v.s9.c9e4eb9bcd27 from=translated src=- shape=3c83545e vocab=172b5b80
-/
theorem G_tendstoLocallyUniformlyOn (hk : 3 ≤ k) (v : Fin 2 → ZMod N) :
    TendstoLocallyUniformlyOn (fun (s : Finset (coset N v)) ↦
      ↑ₕ(fun (z : ℍ) ↦ ∑ x ∈ s, eisSummand k x z)) (↑ₕ(GSIF N k v)) atTop {z : ℂ | 0 < z.im} := by
  rw [← upperHalfPlaneSet, ← range_coe, ← image_univ]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    exact G_tendstoLocallyUniformly hk v
  · simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ, mapsTo_range_iff,
    Set.mem_univ, forall_const]

/--
@isnad1 id=mdiffere.1h3v.s8.9bd5f140be90 from=translated src=- shape=b9c17145 vocab=0ccf67c4
-/
theorem GSIF_mdifferentiable (hk : 3 ≤ k) (v : Fin 2 → ZMod N) : MDiff (GSIF N k v) := by
  intro τ
  suffices DifferentiableAt ℂ (↑ₕGSIF N k v) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z ↦ (comp_ofComplex (GSIF N k v) z).symm
  refine DifferentiableOn.differentiableAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
  exact (G_tendstoLocallyUniformlyOn hk v).differentiableOn
    (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun _ _ ↦ eisSummand_extension_differentiableOn _ _) isOpen_upperHalfPlaneSet

/--
@isnad1 id=le.1h4v.s6.cae28e5fd8d3 from=translated src=- shape=e549bfd3 vocab=ac5c2a56
-/
theorem norm_G_le_tsum_norm (hk : 3 ≤ k) (v : Fin 2 → ZMod N) (z : ℍ) :
    ‖G N k v z‖ ≤ ∑' (x : Fin 2 → ℤ), ‖eisSummand k x z‖ := by
  simp_rw [G]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖) _ (fun _ ↦ norm_nonneg _)
      (summable_norm_eisSummand hk z))

/--
@isnad1 id=isbounde.1h4v.s8.3d390cadb329 from=translated src=- shape=f405be50 vocab=81c9781f
-/
theorem isBoundedAtImInfty_GSIF [NeZero N] (hk : 3 ≤ k) (v : Fin 2 → ZMod N) (A : SL(2, ℤ)) :
    IsBoundedAtImInfty ((⇑(GSIF N k v) : ℍ → ℂ) ∣[k] A) := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨∑'(x : Fin 2 → ℤ), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N))
  rw [coe_GSIF, G_slash_apply, ← coe_GSIF,
    ← SlashInvariantForm.T_zpow_width_invariant N k n (GSIF N k (v ᵥ* red N A)) z, coe_GSIF]
  apply le_trans (norm_G_le_tsum_norm hk (v ᵥ* red N A) _)
  have hk' : (2 : ℝ) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
  · exact_mod_cast (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)

end Analytic

def GMF {k : ℤ} {N : ℕ} [NeZero N] (hk : 3 ≤ k) (v : Fin 2 → ZMod N) :
    ModularForm (Gamma N) k where
  toFun := GSIF N k v
  slash_action_eq' := (GSIF N k v).slash_action_eq'
  holo' := GSIF_mdifferentiable hk v
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ hγ ↦ isBoundedAtImInfty_GSIF hk v γ

/--
@isnad1 id=eq.1h3v.s8.3b4fa3c75c27 from=translated src=- shape=1935218f vocab=0ed08f81
-/
theorem coe_GMF {k : ℤ} {N : ℕ} [NeZero N] (hk : 3 ≤ k) (v : Fin 2 → ZMod N) :
    (⇑(GMF hk v) : ℍ → ℂ) = G N k v := rfl

end EisensteinSeries.FullLattice
open scoped _root_.P2MW.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.EisensteinSeries _root_.P2MW.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.EisensteinSeries.FullLattice
open scoped _root_.P2MW.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.EisensteinSeries

end
open scoped _root_.P2MW.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.EisensteinSeries _root_.P2MW.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.EisensteinSeries.FullLattice

open _root_.EisensteinSeries _root_.P2MW.S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.EisensteinSeries EisensteinSeries.FullLattice in
/--
@isnad1 id=ex.1h2v.s11.3dbc38b7a109 from=translated src=- shape=9cb8bfb1 vocab=105fc48c
-/
theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) :
    ∃ G : (Fin 2 → ZMod N) → ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane),
        G v τ = ∑' x : {x : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ x = v}, EisensteinSeries.eisSummand k x.1 τ) ∧
      (∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)),
        ((⇑(G v) : UpperHalfPlane → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) =
          ⇑(G (Matrix.vecMul v ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N))))) := by
  refine ⟨fun v => GMF hk v, fun v τ => rfl, fun v γ => ?_⟩
  rw [coe_GMF, coe_GMF, ← ModularForm.SL_slash, G_slash_apply]
  rfl
