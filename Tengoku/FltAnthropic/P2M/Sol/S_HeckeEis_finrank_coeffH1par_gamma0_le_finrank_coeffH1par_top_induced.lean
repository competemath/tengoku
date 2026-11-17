import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep

import Tengoku.FltAnthropic.Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.lean`: wrote out 22 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_export`, 4 `p2m_open`, 14 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace HeckeEis
export _root_.HeckeEis (coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff BinaryForm binaryFormRepSL)
namespace UBSol
open _root_.HeckeEis

open Polynomial

/--
@isnad1 id=mem.2h4v.s8.ca6747a8328a from=translated src=- shape=34fa81c6 vocab=c2dafab7
-/
theorem mem_range_of_geomSum_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) {M : ℕ} (hM : 0 < M)
    (v : V) (hv : aeval A (∑ i ∈ Finset.range M, (X : ℂ[X]) ^ i) v = 0) :
    v ∈ LinearMap.range (A - 1) := by
  set Φ : ℂ[X] := ∑ i ∈ Finset.range M, X ^ i with hΦ
  have hndvd : ¬ (X - C (1 : ℂ)) ∣ Φ := by
    intro hdvd
    have h1 : Φ.IsRoot 1 := (Polynomial.dvd_iff_isRoot).mp hdvd
    rw [Polynomial.IsRoot, hΦ, Polynomial.eval_finsetSum] at h1
    simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at h1
    exact (Nat.cast_ne_zero.mpr hM.ne') h1
  have hcop : IsCoprime (X - C (1 : ℂ)) Φ := (Polynomial.irreducible_X_sub_C (1 : ℂ)).coprime_iff_not_dvd.mpr hndvd
  obtain ⟨a, b, hab⟩ := hcop
  have key : v = aeval A (a * (X - C 1)) v := by
    have := congrArg (fun p => aeval A p v) hab
    simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at this
    rw [show aeval A Φ v = 0 from hv, map_zero, add_zero] at this
    rw [map_mul, Module.End.mul_apply]; exact this.symm
  rw [key, mul_comm, map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, one_smul]
  exact LinearMap.mem_range_self _ _

/--
@isnad1 id=mem.2h4v.s8.a2008d718555 from=translated src=- shape=a532d4d0 vocab=313e5766
-/
theorem mem_range_of_sum_pow_apply_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) {M : ℕ} (hM : 0 < M)
    (v : V) (hv : ∑ i ∈ Finset.range M, (A ^ i) v = 0) : v ∈ LinearMap.range (A - 1) := by
  apply mem_range_of_geomSum_eq_zero A hM
  rw [map_sum, LinearMap.coe_sum, Finset.sum_apply]
  simpa only [map_pow, aeval_X] using hv

end HeckeEis.UBSol

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff BinaryForm binaryFormRepSL)
namespace UBSol
open _root_.HeckeEis

open scoped MatrixGroups
open MvPolynomial

variable (N : ℕ) (n : ℕ)

abbrev G2 := SL(2, ℤ)
abbrev Gt : Subgroup SL(2, ℤ) := ⊤
abbrev Γ0 : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma0 N
abbrev X0 := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N
abbrev Vn := ↥(BinaryForm ℂ n)
abbrev ρ : Representation ℂ SL(2, ℤ) (Vn n) := binaryFormRepSL ℂ n
abbrev ρΓ : Representation ℂ ↥(Γ0 N) (Vn n) := (binaryFormRepSL ℂ n).comp (Γ0 N).subtype

section Cosets

variable {N}

/--
@isnad1 id=mem.0h3v.s9.f2cb0e7f1523 from=translated src=- shape=f74aa592 vocab=83daafda
-/
theorem transfer_mem (g : SL(2, ℤ)) (x : X0 N) : (x.out)⁻¹ * (g * (g⁻¹ • x).out) ∈ Γ0 N := by
  rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.coe_smul_out, smul_inv_smul]

def tr (g : SL(2, ℤ)) (x : X0 N) : ↥(Γ0 N) := ⟨(x.out)⁻¹ * (g * (g⁻¹ • x).out), transfer_mem g x⟩

/--
@isnad1 id=eq.0h3v.s9.ae04f4117551 from=translated src=- shape=f1f52987 vocab=6db46694
-/
@[scoped simp] theorem coe_tr (g : SL(2, ℤ)) (x : X0 N) : ((tr g x : ↥(Γ0 N)) : SL(2, ℤ)) = (x.out)⁻¹ * (g * (g⁻¹ • x).out) := rfl

/--
@isnad1 id=eq.0h4v.s10.9001c8053624 from=translated src=- shape=2757f186 vocab=50c1d1aa
-/
theorem tr_mul (g h : SL(2, ℤ)) (x : X0 N) : tr (g * h) x = tr g x * tr h (g⁻¹ • x) := by
  apply Subtype.ext
  simp only [coe_tr, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  group

/--
@isnad1 id=eq.0h3v.s9.2b04aca5494b from=translated src=- shape=538a415f vocab=6db46694
-/
theorem out_mul_tr (g : SL(2, ℤ)) (x : X0 N) : x.out * ((tr g x : ↥(Γ0 N)) : SL(2, ℤ)) = g * (g⁻¹ • x).out := by
  rw [coe_tr, mul_inv_cancel_left]

end Cosets

section Shapiro

variable {N n}
variable (W : Representation ℂ ↥Gt (X0 N → Vn n))
  (hW : ∀ (g : ↥Gt) (f : X0 N → Vn n) (x : X0 N), W g f x = ρ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x)))
include hW

def Sh (z : ↥(Γ0 N) → Vn n) : ↥Gt → X0 N → Vn n := fun g x => ρ n x.out (z (tr (g : SL(2, ℤ)) x))

omit hW in
/--
@isnad1 id=eq.0h5v.s11.fca23ad3118a from=translated src=- shape=030a942a vocab=11cc7880
-/
@[scoped simp] theorem Sh_apply (z : ↥(Γ0 N) → Vn n) (g : ↥Gt) (x : X0 N) : Sh z g x = ρ n x.out (z (tr (g : SL(2, ℤ)) x)) := rfl

omit hW in
/--
@isnad1 id=eq.0h4v.s11.45f77811e791 from=translated src=- shape=783ab6ec vocab=9a120021
-/
theorem Sh_add (z w : ↥(Γ0 N) → Vn n) : Sh (z + w) = Sh z + Sh w := by
  funext g x; simp

omit hW in
/--
@isnad1 id=eq.0h4v.s12.18f865097e4d from=translated src=- shape=783ab6ec vocab=52d9d126
-/
theorem Sh_sub (z w : ↥(Γ0 N) → Vn n) : Sh (z - w) = Sh z - Sh w := by
  funext g x; simp

omit hW in
/--
@isnad1 id=eq.0h4v.s11.b571c56cad4c from=translated src=- shape=04aec3c5 vocab=92da3674
-/
theorem Sh_smul (c : ℂ) (z : ↥(Γ0 N) → Vn n) : Sh (c • z) = c • Sh z := by
  funext g x; simp

/--
@isnad1 id=mem.2h4v.s14.e1cc7d55f04a from=translated src=- shape=6821ae38 vocab=fdb2f726
-/
theorem Sh_mem_coeffCocycles {z : ↥(Γ0 N) → Vn n} (hz : z ∈ coeffCocycles (ρΓ N n)) : Sh z ∈ coeffCocycles W := by
  intro g h
  funext x
  rw [Pi.add_apply, hW, Sh_apply, Sh_apply, Sh_apply]
  rw [show ((g * h : ↥Gt) : SL(2, ℤ)) = (g : SL(2, ℤ)) * (h : SL(2, ℤ)) from rfl, tr_mul, hz]
  rw [map_add]
  rw [add_right_inj]

  show ρ n x.out (ρ n ((tr (g : SL(2, ℤ)) x : ↥(Γ0 N)) : SL(2, ℤ)) (z (tr (h : SL(2, ℤ)) ((g : SL(2, ℤ))⁻¹ • x)))) = _
  rw [← Module.End.mul_apply, ← map_mul, out_mul_tr, map_mul, Module.End.mul_apply]

/--
@isnad1 id=mem.2h4v.s14.439f963fda65 from=translated src=- shape=6821ae38 vocab=d675d7b3
-/
theorem Sh_mem_coeffCoboundaries {z : ↥(Γ0 N) → Vn n} (hz : z ∈ coeffCoboundaries (ρΓ N n)) : Sh z ∈ coeffCoboundaries W := by
  rw [mem_coeffCoboundaries_iff] at hz ⊢
  obtain ⟨v, rfl⟩ := hz
  refine ⟨fun x => ρ n x.out v, funext fun g => funext fun x => ?_⟩
  rw [Pi.sub_apply, hW, Sh_apply, map_sub]
  rw [sub_left_inj]
  show _ = ρ n x.out (ρ n ((tr (g : SL(2, ℤ)) x : ↥(Γ0 N)) : SL(2, ℤ)) v)
  rw [← Module.End.mul_apply (ρ n x.out), ← map_mul, out_mul_tr, map_mul, Module.End.mul_apply]

/--
@isnad1 id=mem.3h4v.s14.c7ea3a48719b from=translated src=- shape=6c3b61a9 vocab=79b951b2
-/
theorem mem_coeffCoboundaries_of_Sh {z : ↥(Γ0 N) → Vn n} (hz : z ∈ coeffCocycles (ρΓ N n))
    (h : Sh z ∈ coeffCoboundaries W) : z ∈ coeffCoboundaries (ρΓ N n) := by
  rw [mem_coeffCoboundaries_iff] at h ⊢
  obtain ⟨F, hF⟩ := h

  set x0 : X0 N := ((1 : SL(2, ℤ)) : X0 N) with hx0
  have hσ0 : x0.out ∈ Γ0 N := by
    have := QuotientGroup.out_eq' x0
    rw [hx0, QuotientGroup.eq] at this
    simpa using this
  set σ0 : ↥(Γ0 N) := ⟨x0.out, hσ0⟩ with hσ0'
  have hfix : ∀ γ : ↥(Γ0 N), ((γ : SL(2, ℤ)))⁻¹ • x0 = x0 := by
    intro γ
    rw [hx0, MulAction.Quotient.smul_coe, QuotientGroup.eq]
    simp

  have key : ∀ γ : ↥(Γ0 N), ρ n x0.out (z (tr (γ : SL(2, ℤ)) x0)) = ρ n (γ : SL(2, ℤ)) (F x0) - F x0 := by
    intro γ
    have := congrFun (congrFun hF ⟨(γ : SL(2, ℤ)), Subgroup.mem_top _⟩) x0
    rw [Pi.sub_apply, hW, Sh_apply] at this
    simp only [hfix] at this
    exact this.symm

  have htr : ∀ γ : ↥(Γ0 N), tr (γ : SL(2, ℤ)) x0 = σ0⁻¹ * γ * σ0 := by
    intro γ
    apply Subtype.ext
    rw [coe_tr, hfix]
    simp [hσ0', mul_assoc]
  refine ⟨ρΓ N n σ0⁻¹ (F x0), funext fun δ => ?_⟩

  have hk := key (σ0 * δ * σ0⁻¹)
  rw [htr, show σ0⁻¹ * (σ0 * δ * σ0⁻¹) * σ0 = δ by group] at hk

  have : z δ = ρ n ((σ0 : ↥(Γ0 N)) : SL(2, ℤ))⁻¹ (ρ n (((σ0 * δ * σ0⁻¹ : ↥(Γ0 N))) : SL(2, ℤ)) (F x0) - F x0) := by
    rw [← hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [this, map_sub, ← Module.End.mul_apply, ← map_mul]
  refine congrArg₂ (· - ·) ?_ ?_
  swap
  · simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, Subgroup.coe_inv]
  show ρ n ((δ * σ0⁻¹ : ↥(Γ0 N)) : SL(2, ℤ)) (F x0) = _
  rw [← Module.End.mul_apply (ρ n _), ← map_mul]
  congr 2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  group

end Shapiro

end HeckeEis.UBSol
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis

end
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff BinaryForm binaryFormRepSL)
namespace UBSol
open _root_.HeckeEis

open scoped MatrixGroups
open MvPolynomial

section Trace

/--
@isnad1 id=ex.1h1v.s9.00462e339831 from=translated src=- shape=a7ad9cae vocab=7f12adf6
-/
theorem trace_sq_eq_four_iff_exists (g : SL(2, ℤ)) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
      → ∃ (ε δ : SL(2, ℤ)) (h : ℤ), (ε = 1 ∨ ε = -1) ∧ g = ε * (δ * ModularGroup.T ^ h * δ⁻¹) :=
  ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four g

/--
@isnad1 id=eq.0h1v.s7.caba439b977e from=translated src=- shape=3d5f9691 vocab=ce1e7b1b
-/
theorem trace_T_zpow (h : ℤ) : ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]; ring

/--
@isnad1 id=eq.0h2v.s8.de0755c6e285 from=translated src=- shape=5b1ea536 vocab=ff003392
-/
theorem trace_conj (δ g : SL(2, ℤ)) :
    ((δ * g * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

/--
@isnad1 id=eq.1h3v.s9.b5c34ef29890 from=translated src=- shape=a5c520c7 vocab=7f12adf6
-/
theorem trace_sq_of_shape (ε δ : SL(2, ℤ)) (h : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (((ε * (δ * ModularGroup.T ^ h * δ⁻¹) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  rcases hε with rfl | rfl
  · rw [one_mul, trace_conj, trace_T_zpow]; norm_num
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, neg_mul,
      one_mul, Matrix.trace_neg, trace_conj, trace_T_zpow]; norm_num

/--
@isnad1 id=eq.1h2v.s8.54adbb7b9148 from=translated src=- shape=3377a79f vocab=5ddcb8c4
-/
theorem trace_sq_pow (g : SL(2, ℤ)) (hg : ((g : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) (M : ℕ) :
    (((g ^ M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  obtain ⟨ε, δ, h, hε, rfl⟩ := trace_sq_eq_four_iff_exists g hg
  have hcomm : Commute ε (δ * ModularGroup.T ^ h * δ⁻¹) := by
    rcases hε with rfl | rfl
    · exact Commute.one_left _
    · exact (Commute.neg_one_left _)
  rw [hcomm.mul_pow, conj_pow, ← zpow_natCast (ModularGroup.T ^ h) M, ← zpow_mul]
  have hεM : ε ^ M = 1 ∨ ε ^ M = -1 := by
    rcases hε with rfl | rfl
    · left; exact one_pow M
    · rcases neg_one_pow_eq_or SL(2, ℤ) M with h1 | h1
      · left; exact h1
      · right; exact h1
  exact trace_sq_of_shape (ε ^ M) δ (h * M) hεM

/--
@isnad1 id=eq.1h2v.s9.072cc3809279 from=translated src=- shape=d86db793 vocab=61eb9644
-/
theorem trace_sq_conj' (a g : SL(2, ℤ)) (hg : ((g : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    (((a⁻¹ * (g * a) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  have := trace_conj a⁻¹ g
  rw [inv_inv, mul_assoc] at this
  rw [this]; exact hg

end Trace
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

section Power

variable {N : ℕ} [NeZero N]

noncomputable scoped instance fintypeX0 : Fintype (X0 N) := (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

/--
@isnad1 id=ex.0h2v.s8.51371cdae93d from=translated src=- shape=3a6539b0 vocab=deaa9021
-/
theorem exists_pow_smul_eq (g : SL(2, ℤ)) : ∃ M : ℕ, 0 < M ∧ ∀ x : X0 N, g ^ M • x = x := by
  classical
  refine ⟨Fintype.card (Equiv.Perm (X0 N)), Fintype.card_pos, fun x => ?_⟩
  have h : (MulAction.toPermHom SL(2, ℤ) (X0 N) g) ^ Fintype.card (Equiv.Perm (X0 N)) = 1 := pow_card_eq_one
  rw [← map_pow] at h
  have := Equiv.congr_fun h x
  simpa using this

end Power
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

section PowerSum

variable {N n : ℕ} {W : Representation ℂ ↥Gt (X0 N → Vn n)}

/--
@isnad1 id=eq.1h6v.s13.61e0b32125df from=translated src=- shape=f2bb4387 vocab=7d16c221
-/
theorem cocycle_pow {Z : ↥Gt → X0 N → Vn n} (hZ : Z ∈ coeffCocycles W) (g : ↥Gt) (M : ℕ) :
    Z (g ^ M) = ∑ i ∈ Finset.range M, ((W g) ^ i) (Z g) := by
  induction M with
  | zero =>
    rw [pow_zero, Finset.sum_range_zero]
    have h := hZ 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    simpa using h
  | succ M ih =>
    rw [pow_succ', hZ, ih, Finset.sum_range_succ', pow_zero, Module.End.one_apply, add_comm, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ', Module.End.mul_apply]

end PowerSum
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

section Parabolic

variable {N n : ℕ} [NeZero N]
variable (W : Representation ℂ ↥Gt (X0 N → Vn n))
  (hW : ∀ (g : ↥Gt) (f : X0 N → Vn n) (x : X0 N), W g f x = ρ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x)))
include hW

/--
@isnad1 id=mem.2h4v.s14.7e7661f6a5a1 from=translated src=- shape=eec8f370 vocab=f3853c42
-/
theorem Sh_mem_coeffParabolicCocycles {z : ↥(Γ0 N) → Vn n} (hz : z ∈ coeffParabolicCocycles (ρΓ N n)) :
    Sh z ∈ coeffParabolicCocycles W := by
  classical
  refine ⟨Sh_mem_coeffCocycles W hW hz.1, fun g hg => ?_⟩
  obtain ⟨M, hM, hfix⟩ := exists_pow_smul_eq (N := N) (g : SL(2, ℤ))
  have hfix' : ∀ x : X0 N, ((g : SL(2, ℤ)) ^ M)⁻¹ • x = x := fun x => by
    conv_lhs => rw [← hfix x]
    rw [inv_smul_smul]

  have hγ : ∀ x : X0 N, (((tr ((g : SL(2, ℤ)) ^ M) x : ↥(Γ0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
    intro x
    rw [coe_tr, hfix']
    exact trace_sq_conj' _ _ (trace_sq_pow _ hg M)
  choose u hu using fun x => hz.2 (tr ((g : SL(2, ℤ)) ^ M) x) (hγ x)

  set F : X0 N → Vn n := fun x => ρ n x.out (u x) with hF
  set A : Module.End ℂ (X0 N → Vn n) := W g with hA

  have h1 : Sh z (g ^ M) = (A ^ M - 1) F := by
    funext x
    rw [Sh_apply, LinearMap.sub_apply, Module.End.one_apply, hA, ← map_pow, Pi.sub_apply, hW]
    rw [show (((g ^ M : ↥Gt)) : SL(2, ℤ)) = (g : SL(2, ℤ)) ^ M from rfl, hfix']
    have hx := hu x
    rw [LinearMap.sub_apply, Module.End.one_apply] at hx
    rw [← hx, map_sub]
    refine congrArg₂ (· - ·) ?_ rfl
    show ρ n x.out (ρ n ((tr ((g : SL(2, ℤ)) ^ M) x : ↥(Γ0 N)) : SL(2, ℤ)) (u x)) = _
    rw [← Module.End.mul_apply (ρ n x.out), ← map_mul, out_mul_tr, hfix', map_mul, Module.End.mul_apply]

  have h2 := cocycle_pow (Sh_mem_coeffCocycles W hW hz.1) g M

  have h3 : (A ^ M - 1) F = ∑ i ∈ Finset.range M, (A ^ i) ((A - 1) F) := by
    rw [← geom_sum_mul A M, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply]
  have hsum : ∑ i ∈ Finset.range M, (A ^ i) (Sh z g - (A - 1) F) = 0 := by
    simp only [map_sub, Finset.sum_sub_distrib]
    rw [← h2, ← h3, h1, sub_self]
  obtain ⟨w, hw⟩ := mem_range_of_sum_pow_apply_eq_zero A hM _ hsum
  exact ⟨w + F, by rw [map_add, hw, sub_add_cancel]⟩

end Parabolic
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

end HeckeEis.UBSol
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

end
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff BinaryForm binaryFormRepSL)
namespace UBSol
open _root_.HeckeEis

open scoped MatrixGroups
open MvPolynomial

section Final

variable {N n : ℕ} [NeZero N]
variable (W : Representation ℂ ↥Gt (X0 N → Vn n))
  (hW : ∀ (g : ↥Gt) (f : X0 N → Vn n) (x : X0 N), W g f x = ρ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x)))
include hW

omit [NeZero N] hW in

theorem eq_zero_of_apply_S_T {Z : ↥Gt → X0 N → Vn n} (hZ : Z ∈ coeffCocycles W)
    (hS : Z ⟨ModularGroup.S, Subgroup.mem_top _⟩ = 0) (hT : Z ⟨ModularGroup.T, Subgroup.mem_top _⟩ = 0) : Z = 0 := by
  have z1 : Z 1 = 0 := by
    have h := hZ 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    simpa using h
  have zinv : ∀ g : ↥Gt, Z g⁻¹ = -(W g⁻¹ (Z g)) := fun g => by
    have h := hZ g⁻¹ g
    rw [inv_mul_cancel, z1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  funext g
  have hg : (g : SL(2, ℤ)) ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  have key : ∀ x (hx : x ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ))), Z ⟨x, Subgroup.mem_top _⟩ = 0 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hS
      · exact hT
    | one => exact z1
    | mul x y _ _ hx hy =>
      have := hZ ⟨x, Subgroup.mem_top _⟩ ⟨y, Subgroup.mem_top _⟩
      rw [hx, hy, map_zero, add_zero] at this
      exact this
    | inv x _ hx =>
      have := zinv ⟨x, Subgroup.mem_top _⟩
      rw [hx, map_zero, neg_zero] at this
      exact this
  rw [key g hg]; rfl

omit hW in

/--
@isnad1 id=finite.0h1v.s6.5e10775e1771 from=translated src=- shape=1a6c1393 vocab=140f3fb9
-/
theorem finite_binaryForm : Module.Finite ℂ (Vn n) := by
  classical
  rw [Module.Finite.iff_fg, show (BinaryForm ℂ n : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) = MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n from rfl,
    MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single]
  refine Submodule.fg_span (Set.Finite.image _ ?_)

  refine Set.Finite.subset (Set.Finite.image (fun i : ℕ => Finsupp.single (0 : Fin 2) i + Finsupp.single 1 (n - i)) (Set.finite_Iic n)) ?_
  intro d hd
  have hsum : d 0 + d 1 = n := by
    have : d.degree = n := hd
    rw [← this, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  refine ⟨d 0, (by show d 0 ≤ n; omega), ?_⟩
  ext j; fin_cases j
  · simp
  · simp; omega

omit hW in
/--
@isnad1 id=finite.0h3v.s13.0a5b21cbb03b from=translated src=- shape=16df9614 vocab=50f5e998
-/
theorem finite_coeffParabolicCocycles : Module.Finite ℂ ↥(coeffParabolicCocycles W) := by
  haveI : Module.Finite ℂ (Vn n) := finite_binaryForm
  let E : ↥(coeffParabolicCocycles W) →ₗ[ℂ] (X0 N → Vn n) × (X0 N → Vn n) :=
    { toFun := fun Z => ((Z : ↥Gt → X0 N → Vn n) ⟨ModularGroup.S, Subgroup.mem_top _⟩,
                        (Z : ↥Gt → X0 N → Vn n) ⟨ModularGroup.T, Subgroup.mem_top _⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective E fun Z Z' h => ?_
  rw [← sub_eq_zero]
  apply Subtype.ext
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine eq_zero_of_apply_S_T W (Z - Z').2.1 ?_ ?_
  · show (Z : ↥Gt → X0 N → Vn n) _ - (Z' : ↥Gt → X0 N → Vn n) _ = 0
    exact sub_eq_zero.mpr h1
  · show (Z : ↥Gt → X0 N → Vn n) _ - (Z' : ↥Gt → X0 N → Vn n) _ = 0
    exact sub_eq_zero.mpr h2

def ShPC : ↥(coeffParabolicCocycles (ρΓ N n)) →ₗ[ℂ] ↥(coeffParabolicCocycles W) where
  toFun z := ⟨Sh (z : ↥(Γ0 N) → Vn n), Sh_mem_coeffParabolicCocycles W hW z.2⟩
  map_add' z w := by
    apply Subtype.ext
    show Sh ((z : ↥(Γ0 N) → Vn n) + (w : ↥(Γ0 N) → Vn n)) = Sh (z : ↥(Γ0 N) → Vn n) + Sh (w : ↥(Γ0 N) → Vn n)
    exact Sh_add _ _
  map_smul' c z := by
    apply Subtype.ext
    show Sh (c • (z : ↥(Γ0 N) → Vn n)) = c • Sh (z : ↥(Γ0 N) → Vn n)
    exact Sh_smul _ _

/--
@isnad1 id=eq.1h4v.s16.2d2902f9410e from=translated src=- shape=528b984c vocab=b908f9ca
-/
@[scoped simp] theorem coe_ShPC (z : ↥(coeffParabolicCocycles (ρΓ N n))) :
    ((ShPC W hW z : ↥(coeffParabolicCocycles W)) : ↥Gt → X0 N → Vn n) = Sh (z : ↥(Γ0 N) → Vn n) := rfl

/--
@isnad1 id=eq.2h5v.s17.566352a9bc72 from=translated src=- shape=b5f670f1 vocab=0db55624
-/
theorem mk_ShPC_congr {a b : ↥(coeffParabolicCocycles (ρΓ N n))} (h : coeffH1parMk _ a = coeffH1parMk _ b) :
    coeffH1parMk _ (ShPC W hW a) = coeffH1parMk _ (ShPC W hW b) := by
  rw [← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff] at h ⊢
  show Sh (a : ↥(Γ0 N) → Vn n) - Sh (b : ↥(Γ0 N) → Vn n) ∈ coeffCoboundaries W
  rw [← Sh_sub]
  exact Sh_mem_coeffCoboundaries W hW h

def Ψ : coeffH1par (ρΓ N n) →ₗ[ℂ] coeffH1par W where
  toFun x := coeffH1parMk _ (ShPC W hW (Function.surjInv (coeffH1parMk_surjective _) x))
  map_add' x y := by
    rw [← map_add, ← map_add]
    apply mk_ShPC_congr
    rw [map_add, Function.surjInv_eq (coeffH1parMk_surjective _), Function.surjInv_eq (coeffH1parMk_surjective _),
      Function.surjInv_eq (coeffH1parMk_surjective _)]
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul, ← map_smul]
    apply mk_ShPC_congr
    rw [map_smul, Function.surjInv_eq (coeffH1parMk_surjective _), Function.surjInv_eq (coeffH1parMk_surjective _)]

/--
@isnad1 id=eq.1h4v.s16.13346ba484e4 from=translated src=- shape=ebca0f46 vocab=db96db6c
-/
theorem Ψ_mk (z : ↥(coeffParabolicCocycles (ρΓ N n))) : Ψ W hW (coeffH1parMk _ z) = coeffH1parMk _ (ShPC W hW z) := by
  show coeffH1parMk _ (ShPC W hW (Function.surjInv (coeffH1parMk_surjective _) (coeffH1parMk _ z))) = _
  apply mk_ShPC_congr
  rw [Function.surjInv_eq (coeffH1parMk_surjective _)]

/--
@isnad1 id=injectiv.1h3v.s13.2a235a6b85f9 from=translated src=- shape=caecb086 vocab=28c6d933
-/
theorem Ψ_injective : Function.Injective (Ψ W hW) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := coeffH1parMk_surjective _ x
  rw [Ψ_mk, coeffH1parMk_eq_zero_iff, coe_ShPC] at hx
  rw [coeffH1parMk_eq_zero_iff]
  exact mem_coeffCoboundaries_of_Sh W hW z.2.1 hx

/--
@isnad1 id=le.1h3v.s13.dcfabc76527e from=translated src=- shape=7a28b1d7 vocab=eafb740e
-/
theorem main :
    Module.finrank ℂ (coeffH1par (ρΓ N n)) ≤ Module.finrank ℂ (coeffH1par W) := by
  haveI := finite_coeffParabolicCocycles W
  haveI : Module.Finite ℂ (coeffH1par W) := Module.Finite.of_surjective (coeffH1parMk W) (coeffH1parMk_surjective W)
  exact LinearMap.finrank_le_finrank_of_injective (Ψ_injective W hW)

end Final
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

end HeckeEis.UBSol
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

end
open scoped _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis _root_.P2MW.S_HeckeEis_finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced.HeckeEis.UBSol

open scoped MatrixGroups in
/--
@isnad1 id=le.1h3v.s15.c27747b1cd5c from=translated src=- shape=f30139fc vocab=28223f8e
-/
theorem solution (N : ℕ) [NeZero N] (n : ℕ)
    (W : Representation ℂ (⊤ : Subgroup SL(2, ℤ)) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)))
    (hW : ∀ (g : (⊤ : Subgroup SL(2, ℤ))) (f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
      W g f x = HeckeEis.binaryFormRepSL ℂ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x))) :
    Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
      ≤ Module.finrank ℂ (HeckeEis.coeffH1par W) :=
  HeckeEis.UBSol.main W hW

