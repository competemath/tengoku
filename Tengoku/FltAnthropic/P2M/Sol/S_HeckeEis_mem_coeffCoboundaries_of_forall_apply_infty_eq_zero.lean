import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PeriodMap
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_ProjectiveLineMatrixAction
import Tengoku.FltAnthropic.Definitions.Def_IharaIota
import Tengoku.FltAnthropic.Theorems.Thm_Int_exists_modEq_and_modEq_and_isCoprime
import Tengoku.FltAnthropic.Theorems.Thm_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (coeffCocycles coeffCoboundaryMap_apply coeffCoboundaries IsParabolicCocycle redMat projLineAct projLineAct_of_isUnit isUnit_det_redMat_coe projLineAct_one projLineAct_coe_mul projLineRepSL)
open _root_.HeckeEis
namespace Sh1t
open CongruenceSubgroup Matrix ModularCurve
open scoped MatrixGroups

def infty (p : ℕ) : ProjectiveLine (ZMod p) :=
  ⟦⟨((0 : ZMod p), (1 : ZMod p)), isUnimodularRow_one_right (0 : ZMod p)⟩⟧

/--
@isnad1 id=eq.0h4v.s5.21de40f93a1e from=translated src=- shape=7a20b016 vocab=fb990407
-/
theorem redMat_apply (p : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    redMat p M i j = ((M i j : ℤ) : ZMod p) := rfl

/--
@isnad1 id=eq.0h2v.s7.a908a3749c0d from=translated src=- shape=3da4b8eb vocab=a773395a
-/
theorem redMat_det_coe (p : ℕ) (g : SL(2, ℤ)) : (redMat p (g : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 := by
  rw [redMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, g.det_coe, map_one]

/--
@isnad1 id=iff.0h2v.s7.82be583d87d2 from=translated src=- shape=6f65b34d vocab=433d919e
-/
theorem projLineAct_infty_eq_infty_iff (p : ℕ) (g : SL(2, ℤ)) :
    projLineAct p (g : Matrix (Fin 2) (Fin 2) ℤ) (infty p) = infty p ↔ (p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  have hu := isUnit_det_redMat_coe p g
  rw [projLineAct_of_isUnit p _ hu, infty, ProjectiveLine.vecMul_mk]
  constructor
  · intro h
    obtain ⟨w, h1, -⟩ := Quotient.exact h
    simp only [ProjectiveLine.vecMulRow_fst, zero_mul, one_mul, zero_add] at h1

    have h0 : redMat p (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
      have := congrArg (fun t => (↑w⁻¹ : ZMod p) * t) h1
      simpa using this
    rw [redMat_apply] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  · intro hdvd
    apply Quotient.sound
    have h10 : redMat p (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
      rw [redMat_apply]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    have hdet := redMat_det_coe p g
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    refine ⟨Units.mkOfMulEqOne _ _ hdet, ?_, ?_⟩
    · simp only [ProjectiveLine.vecMulRow_fst, zero_mul, one_mul, zero_add, h10, mul_zero]
    · simp only [ProjectiveLine.vecMulRow_snd, zero_mul, one_mul, zero_add, Units.val_mkOfMulEqOne, hdet]

/--
@isnad1 id=iff.1h3v.s9.36a21f9c6dde from=translated src=- shape=ea259a47 vocab=2e085442
-/
theorem projLineAct_infty_eq_infty_iff_mem (N p : ℕ) (hNp : Nat.Coprime N p) (g : Gamma0 N) :
    projLineAct p ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (infty p) = infty p ↔
      (g : SL(2, ℤ)) ∈ Gamma0 (N * p) := by
  rw [projLineAct_infty_eq_infty_iff, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hN : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (Gamma0_mem.mp g.2)
  constructor
  · intro hp
    have := (Nat.isCoprime_iff_coprime.mpr hNp).mul_dvd hN hp
    exact_mod_cast this
  · intro h
    push_cast at h
    exact (dvd_mul_left (p : ℤ) N).trans h

def sl2OfCoprime (m n c d : ℤ) (h : m * c + n * d = 1) : SL(2, ℤ) :=
  ⟨!![n, -m; c, d], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

/--
@isnad1 id=ex.1h3v.s9.6d4a4750fa07 from=translated src=- shape=1cf8f82a vocab=04dc145b
-/
theorem exists_gamma0_projLineAct_infty_eq (N p : ℕ) [NeZero p] (hNp : Nat.Coprime N p)
    (P : ProjectiveLine (ZMod p)) :
    ∃ g : Gamma0 N, projLineAct p ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (infty p) = P := by
  induction P using Quotient.inductionOn with
  | h xy =>
    obtain ⟨⟨x, y⟩, hxy⟩ := xy
    obtain ⟨s, t, hst⟩ := hxy

    set c0 : ℤ := (x.val : ℤ)
    set d0 : ℤ := (y.val : ℤ)
    set s0 : ℤ := (s.val : ℤ)
    set t0 : ℤ := (t.val : ℤ)
    have hc0 : ((c0 : ℤ) : ZMod p) = x := by simp [c0]
    have hd0 : ((d0 : ℤ) : ZMod p) = y := by simp [d0]
    have hs0 : ((s0 : ℤ) : ZMod p) = s := by simp [s0]
    have ht0 : ((t0 : ℤ) : ZMod p) = t := by simp [t0]

    obtain ⟨w, hw⟩ : (p : ℤ) ∣ (s0 * c0 + t0 * d0) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hc0, hd0, hs0, ht0, hst, sub_self]

    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hNp : IsCoprime (N : ℤ) (p : ℤ))
    set c : ℤ := c0 * u * N with hc
    set d : ℤ := d0 * u * N + v * p with hd
    have h3 : ∃ X Y Z : ℤ, X * c + Y * d + Z * ((N : ℤ) * p) = 1 := by
      refine ⟨s0 * u * N, t0 * u * N + v * p, -(u ^ 2 * N * w + u * v * (t0 + d0) - 2 * u * v), ?_⟩
      rw [hc, hd]
      linear_combination ((N : ℤ) ^ 2 * u ^ 2) * hw + ((N : ℤ) * u + p * v + 1) * huv
    obtain ⟨c', d', hc', hd', hcd⟩ := Int.exists_modEq_and_modEq_and_isCoprime h3
    obtain ⟨m, n, hmn⟩ := hcd

    have hmemN : sl2OfCoprime m n c' d' hmn ∈ Gamma0 N := by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      show (N : ℤ) ∣ c'
      have h1 : c' ≡ c [ZMOD (N : ℤ)] := hc'.of_mul_right _
      have h2 : (N : ℤ) ∣ c := ⟨c0 * u, by rw [hc]; ring⟩
      have hh : (N : ℤ) ∣ c' - c := Int.ModEq.dvd h1.symm
      have := dvd_add h2 hh
      rwa [add_sub_cancel] at this
    refine ⟨⟨_, hmemN⟩, ?_⟩

    have hu' := isUnit_det_redMat_coe p (sl2OfCoprime m n c' d' hmn)
    rw [show (((⟨_, hmemN⟩ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = (sl2OfCoprime m n c' d' hmn : Matrix (Fin 2) (Fin 2) ℤ) from rfl,
      projLineAct_of_isUnit p _ hu', infty, ProjectiveLine.vecMul_mk]
    apply Quotient.sound

    have hcp : ((c' : ℤ) : ZMod p) = x := by
      have h1 : c' ≡ c [ZMOD (p : ℤ)] := hc'.of_mul_left _
      rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h1, hc]
      push_cast
      rw [hc0]
      have : ((u : ℤ) : ZMod p) * (N : ZMod p) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod p)) huv
        push_cast at this
        rw [ZMod.natCast_self, mul_zero, add_zero] at this
        exact this
      rw [mul_assoc, this, mul_one]
    have hdp : ((d' : ℤ) : ZMod p) = y := by
      have h1 : d' ≡ d [ZMOD (p : ℤ)] := hd'.of_mul_left _
      rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h1, hd]
      push_cast
      rw [hd0, ZMod.natCast_self, mul_zero, add_zero]
      have : ((u : ℤ) : ZMod p) * (N : ZMod p) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod p)) huv
        push_cast at this
        rw [ZMod.natCast_self, mul_zero, add_zero] at this
        exact this
      rw [mul_assoc, this, mul_one]
    refine ⟨1, ?_, ?_⟩
    · simp only [ProjectiveLine.vecMulRow_fst, zero_mul, one_mul, zero_add, Units.val_one, redMat_apply]
      show (((sl2OfCoprime m n c' d' hmn : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p) = x
      rw [show ((sl2OfCoprime m n c' d' hmn : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = c' from rfl, hcp]
    · simp only [ProjectiveLine.vecMulRow_snd, zero_mul, one_mul, zero_add, Units.val_one, redMat_apply]
      show (((sl2OfCoprime m n c' d' hmn : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p) = y
      rw [show ((sl2OfCoprime m n c' d' hmn : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = d' from rfl, hdp]

end Sh1t
end HeckeEis

namespace HeckeEis
export _root_.HeckeEis (coeffCocycles coeffCoboundaryMap_apply coeffCoboundaries IsParabolicCocycle redMat projLineAct projLineAct_of_isUnit isUnit_det_redMat_coe projLineAct_one projLineAct_coe_mul projLineRepSL)
open _root_.HeckeEis
namespace Sh1
open CongruenceSubgroup Matrix ModularCurve Sh1t Function
open scoped MatrixGroups

variable (N p : ℕ) [NeZero p] (hpN : Nat.Coprime p N) (K : Type*) [CommRing K]

noncomputable abbrev rho : Representation K (Gamma0 N) (ProjectiveLine (ZMod p) → K) :=
  (projLineRepSL p K).comp (Gamma0 N).subtype

noncomputable abbrev act (g : Gamma0 N) (P : (ProjectiveLine (ZMod p))) : (ProjectiveLine (ZMod p)) := projLineAct p ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P

/--
@isnad1 id=eq.0h5v.s10.98f100a236a5 from=translated src=- shape=cbbc53cd vocab=be995d54
-/
theorem act_mul (g h : Gamma0 N) (P : (ProjectiveLine (ZMod p))) : act N p (g * h) P = act N p h (act N p g P) := by
  show projLineAct p (((g : SL(2, ℤ)) * (h : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P = _
  exact projLineAct_coe_mul p _ _ P

/--
@isnad1 id=eq.0h3v.s9.72959e50bdb7 from=translated src=- shape=d44470de vocab=7679a750
-/
theorem act_one (P : (ProjectiveLine (ZMod p))) : act N p 1 P = P := by
  show projLineAct p ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P = P
  rw [Matrix.SpecialLinearGroup.coe_one, projLineAct_one]

/--
@isnad1 id=eq.0h4v.s9.5279efff4e55 from=translated src=- shape=1f002875 vocab=913e8bc8
-/
theorem act_inv_act (g : Gamma0 N) (P : (ProjectiveLine (ZMod p))) : act N p g⁻¹ (act N p g P) = P := by
  rw [← act_mul, mul_inv_cancel, act_one]

/--
@isnad1 id=eq.0h6v.s11.9ae3fd16491e from=translated src=- shape=deac95f2 vocab=6f5e7aaf
-/
theorem rho_apply (g : Gamma0 N) (f : (ProjectiveLine (ZMod p)) → K) (P : (ProjectiveLine (ZMod p))) : (rho N p K g) f P = f (act N p g P) := rfl

include hpN in
/--
@isnad1 id=iff.1h3v.s9.b16c7644b636 from=translated src=- shape=be88c10d vocab=4071d3f7
-/
theorem act_infty_eq_iff (g : Gamma0 N) : act N p g (infty p) = infty p ↔ (g : SL(2, ℤ)) ∈ Gamma0 (N * p) :=
  projLineAct_infty_eq_infty_iff_mem N p hpN.symm g

include hpN in
/--
@isnad1 id=eq.1h3v.s12.8717021dd138 from=translated src=- shape=15473305 vocab=33bc0438
-/
theorem act_iota0_infty (γ : Gamma0 (N * p)) : act N p (Ihara.ι₀ N p γ) (infty p) = infty p :=
  (act_infty_eq_iff N p hpN _).mpr (by rw [Ihara.coe_iota0]; exact γ.2)

variable (σ : (ProjectiveLine (ZMod p)) → Gamma0 N) (hσ : ∀ P : (ProjectiveLine (ZMod p)), act N p (σ P) (infty p) = P)

include hpN hσ in
/--
@isnad1 id=mem.2h5v.s11.df4f09c0e476 from=translated src=- shape=df993269 vocab=e1a65fa7
-/
theorem kappa_mem (P : (ProjectiveLine (ZMod p))) (g : Gamma0 N) : ((σ P * g * (σ (act N p g P))⁻¹ : Gamma0 N) : SL(2, ℤ)) ∈ Gamma0 (N * p) := by
  rw [← act_infty_eq_iff N p hpN]
  rw [act_mul, act_mul, hσ]
  calc act N p (σ (act N p g P))⁻¹ (act N p g P)
      = act N p (σ (act N p g P))⁻¹ (act N p (σ (act N p g P)) (infty p)) := by rw [hσ]
    _ = infty p := act_inv_act N p _ _

noncomputable def kappa (P : (ProjectiveLine (ZMod p))) (g : Gamma0 N) : Gamma0 (N * p) :=
  ⟨((σ P * g * (σ (act N p g P))⁻¹ : Gamma0 N) : SL(2, ℤ)), kappa_mem N p hpN σ hσ P g⟩

/--
@isnad1 id=eq.2h5v.s13.742d17e08a58 from=translated src=- shape=214fc42f vocab=67f9c6e5
-/
theorem iota0_kappa (P : (ProjectiveLine (ZMod p))) (g : Gamma0 N) : Ihara.ι₀ N p (kappa N p hpN σ hσ P g) = σ P * g * (σ (act N p g P))⁻¹ :=
  rfl

include hpN hσ in
/--
@isnad1 id=mem.4h5v.s13.a99e228dc122 from=translated src=- shape=68e4b621 vocab=b402c116
-/
theorem mem_coeffCoboundaries_of_forall_eq_zero {z : Gamma0 N → (ProjectiveLine (ZMod p)) → K} (hz : z ∈ coeffCocycles (rho N p K))
    (hz0 : ∀ γ : Gamma0 (N * p), z (Ihara.ι₀ N p γ) (infty p) = 0) : z ∈ coeffCoboundaries (rho N p K) := by
  refine ⟨fun P => z (σ P) (infty p), ?_⟩
  funext g P
  simp only [coeffCoboundaryMap_apply, Pi.sub_apply, LinearMap.sub_apply, rho_apply]

  have h1 : z (σ P * g) (infty p) = z (σ P) (infty p) + z g P := by
    rw [hz (σ P) g, Pi.add_apply, rho_apply, hσ]
  have h2 : z (σ P * g) (infty p) = z (σ (act N p g P)) (infty p) := by
    have e : σ P * g = Ihara.ι₀ N p (kappa N p hpN σ hσ P g) * σ (act N p g P) := by
      rw [iota0_kappa, inv_mul_cancel_right]
    rw [e, hz, Pi.add_apply, rho_apply, hz0, zero_add, act_iota0_infty N p hpN]

  show z (σ (act N p g P)) (infty p) - z (σ P) (infty p) = z g P
  rw [← h2, h1, add_sub_cancel_left]

noncomputable def zOf (φ : Additive (Gamma0 (N * p)) →+ K) : Gamma0 N → (ProjectiveLine (ZMod p)) → K :=
  fun g P => φ (Additive.ofMul (kappa N p hpN σ hσ P g))

end Sh1
end HeckeEis

end

/--
@isnad1 id=mem.3h4v.s14.a59a48c800c2 from=translated src=- shape=3120175a vocab=ab3458bc
-/
theorem solution (N p : ℕ) [NeZero p] (hpN : Nat.Coprime p N)
    (K : Type*) [CommRing K]
    {z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K}
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hz0 : ∀ γ : CongruenceSubgroup.Gamma0 (N * p),
      z (Ihara.ι₀ N p γ) (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧ : ModularCurve.ProjectiveLine (ZMod p)) = 0) :
    z ∈ HeckeEis.coeffCoboundaries ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) := by
  classical
  choose σ hσ using fun P => HeckeEis.Sh1t.exists_gamma0_projLineAct_infty_eq N p hpN.symm P
  exact HeckeEis.Sh1.mem_coeffCoboundaries_of_forall_eq_zero N p hpN K σ hσ hz hz0
