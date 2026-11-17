import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WittVector_exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WittVector_exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete

set_option autoImplicit false

open Function

universe u v

namespace WittUniv

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime]
variable {k : Type v} [CommRing k] [Algebra 𝓞 k]

local notation "𝕎" => WittVector p

omit hp in

noncomputable def resEquiv (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : k ≃+* ModP 𝓞 p :=
  ((RingHom.quotientKerEquivOfSurjective hk).symm.trans (Ideal.quotEquivOfEq hker))

omit hp in
/--
@isnad1 id=eq.2h4v.s10.e1a1ec19e0d9 from=translated src=- shape=c04beba9 vocab=4c13d81d
-/
theorem resEquiv_symm_mk (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) (x : 𝓞) :
    (resEquiv hk hker).symm (Ideal.Quotient.mk _ x) = algebraMap 𝓞 k x := by
  simp [resEquiv, RingEquiv.symm_trans_apply]

/--
@isnad1 id=not.1h3v.s7.173219a4a781 from=translated src=- shape=a5f67a8d vocab=a0306ea8
-/
theorem not_isUnit_natCast [CharP k p]
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : ¬ IsUnit (p : 𝓞) := by
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one (R := k) hp.out.ne_one
  intro hu
  have hmem : (p : 𝓞) ∈ RingHom.ker (algebraMap 𝓞 k) := hker ▸ Ideal.mem_span_singleton_self _
  have h1 : IsUnit (algebraMap 𝓞 k p) := hu.map _
  rw [RingHom.mem_ker] at hmem
  rw [hmem] at h1
  exact not_isUnit_zero h1

omit hp in

/--
@isnad1 id=perfectr.2h3v.s7.a7db1017357f from=translated src=- shape=84b5dde0 vocab=733ae241
-/
theorem perfectRing_modP [PerfectRing k p] (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    PerfectRing (ModP 𝓞 p) p := by
  refine ⟨?_⟩
  set e := resEquiv hk hker
  have hcomm : ∀ x : ModP 𝓞 p, x ^ p = e ((e.symm x) ^ p) := by
    intro x
    rw [map_pow, RingEquiv.apply_symm_apply]
  have hfun : (fun x : ModP 𝓞 p => x ^ p) = e ∘ (fun y : k => y ^ p) ∘ e.symm := funext hcomm
  rw [hfun]
  exact e.bijective.comp ((PerfectRing.bijective_frobenius (R := k) (p := p)).comp e.symm.bijective)

section Theta

variable [Fact ¬ IsUnit (p : 𝓞)] [PerfectRing (ModP 𝓞 p) p]
variable (hk : Surjective (algebraMap 𝓞 k))
  (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})

noncomputable def tiltEquiv : ModP 𝓞 p ≃+* PreTilt 𝓞 p :=
  (PerfectionMap.id p (ModP 𝓞 p)).equiv

/--
@isnad1 id=eq.0h3v.s9.d9234fbaa2d5 from=translated src=- shape=7a149d8b vocab=930694a3
-/
theorem preTilt_coeff_zero_tiltEquiv (x : ModP 𝓞 p) :
    PreTilt.coeff 0 (tiltEquiv (𝓞 := 𝓞) (p := p) x) = x :=
  (PerfectionMap.id p (ModP 𝓞 p)).comp_equiv x

noncomputable def resTiltEquiv : k ≃+* PreTilt 𝓞 p := (resEquiv hk hker).trans tiltEquiv

/--
@isnad1 id=eq.2h4v.s9.7dff0d8f718b from=translated src=- shape=76bd907f vocab=bf8bed12
-/
theorem preTilt_coeff_zero_resTiltEquiv (c : k) :
    PreTilt.coeff 0 (resTiltEquiv hk hker c) = resEquiv hk hker c := by
  rw [resTiltEquiv, RingEquiv.trans_apply, preTilt_coeff_zero_tiltEquiv]

variable [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]

noncomputable def thetaW : 𝕎 k →+* 𝓞 :=
  (WittVector.fontaineTheta 𝓞 p).comp (WittVector.map (resTiltEquiv hk hker).toRingHom)

/--
@isnad1 id=eq.2h4v.s8.357dcb468171 from=translated src=- shape=5c088717 vocab=74a39029
-/
theorem algebraMap_theta (x : 𝕎 k) : algebraMap 𝓞 k (thetaW hk hker x) = x.coeff 0 := by
  have h1 : Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}) (thetaW hk hker x) =
      resEquiv hk hker (x.coeff 0) := by
    rw [thetaW, RingHom.comp_apply, WittVector.mk_fontaineTheta, WittVector.map_coeff]
    exact preTilt_coeff_zero_resTiltEquiv hk hker _
  have h2 := congrArg (resEquiv hk hker).symm h1
  rwa [resEquiv_symm_mk, RingEquiv.symm_apply_apply] at h2

/--
@isnad1 id=eq.2h3v.s8.23966f0b56af from=translated src=- shape=b0c7d385 vocab=1da3c146
-/
theorem algebraMap_comp_theta :
    (algebraMap 𝓞 k).comp (thetaW hk hker) = WittVector.constantCoeff :=
  RingHom.ext fun x => algebraMap_theta hk hker x

/--
@isnad1 id=surjecti.2h3v.s8.1b868b786c97 from=translated src=- shape=eeef3988 vocab=aa1ca531
-/
theorem theta_surjective : Surjective (thetaW hk hker) := by
  refine (surjective_fontaineTheta ?_).comp
    (WittVector.map_surjective _ (resTiltEquiv hk hker).surjective)
  exact (PerfectRing.bijective_frobenius (R := ModP 𝓞 p) (p := p)).2

variable [CharP k p] [PerfectRing k p]

/--
@isnad1 id=injectiv.3h3v.s8.57cae86bd738 from=translated src=- shape=e9720121 vocab=2b6b04f7
-/
theorem theta_injective (hp' : (p : 𝓞) ∈ nonZeroDivisors 𝓞) : Injective (thetaW hk hker) := by
  rw [injective_iff_map_eq_zero]
  intro x hx

  have key : ∀ n : ℕ, ∃ y : 𝕎 k, x = (p : 𝕎 k) ^ n * y ∧ thetaW hk hker y = 0 := by
    intro n
    induction n with
    | zero => exact ⟨x, by rw [pow_zero, one_mul], hx⟩
    | succ n ih =>
      obtain ⟨y, rfl, hy⟩ := ih
      have hy0 : y.coeff 0 = 0 := by rw [← algebraMap_theta hk hker y, hy, map_zero]
      have hymem : y ∈ Ideal.span {(p : 𝕎 k)} :=
        (WittVector.mem_span_p_iff_coeff_zero_eq_zero y).2 hy0
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hymem
      refine ⟨z, by rw [← hz, pow_succ]; ring, ?_⟩
      have h1 : thetaW hk hker z * (p : 𝓞) = 0 := by
        rw [← map_natCast (thetaW hk hker) p, ← map_mul, hz, hy]
      exact mem_nonZeroDivisors_iff_right.1 hp' _ h1
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : 𝕎 k)}) (𝕎 k)) x fun n => ?_
  obtain ⟨y, hy, -⟩ := key n
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, hy]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

omit [Fact ¬ IsUnit (p : 𝓞)] [PerfectRing (ModP 𝓞 p) p] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
include hker in

/--
@isnad1 id=mem.3h7v.s9.8672a81beb7c from=translated src=- shape=5e65df29 vocab=057fa809
-/
theorem sub_teichmuller_mem_pow (g g' : 𝕎 k →+* 𝓞)
    (hg : (algebraMap 𝓞 k).comp g = WittVector.constantCoeff)
    (hg' : (algebraMap 𝓞 k).comp g' = WittVector.constantCoeff) (n : ℕ) (c : k) :
    g (WittVector.teichmuller p c) - g' (WittVector.teichmuller p c) ∈
      Ideal.span {(p : 𝓞)} ^ (n + 1) := by

  set d : k := ((frobeniusEquiv k p).symm^[n]) c with hd
  have hcd : d ^ p ^ n = c := iterate_frobeniusEquiv_symm_pow_p_pow k p c n
  have hdiff : (p : 𝓞) ∣ g (WittVector.teichmuller p d) - g' (WittVector.teichmuller p d) := by
    rw [← Ideal.mem_span_singleton, ← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    have h1 := RingHom.congr_fun hg (WittVector.teichmuller p d)
    have h2 := RingHom.congr_fun hg' (WittVector.teichmuller p d)
    simp only [RingHom.comp_apply] at h1 h2
    rw [h1, h2]
  have := dvd_sub_pow_of_dvd_sub hdiff n
  have e1 : g (WittVector.teichmuller p c) = g (WittVector.teichmuller p d) ^ p ^ n := by
    rw [← hcd, map_pow, map_pow]
  have e2 : g' (WittVector.teichmuller p c) = g' (WittVector.teichmuller p d) ^ p ^ n := by
    rw [← hcd, map_pow, map_pow]
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, e1, e2]
  exact this

omit [Fact ¬ IsUnit (p : 𝓞)] [PerfectRing (ModP 𝓞 p) p] in
include hker in
/--
@isnad1 id=eq.3h5v.s8.c3eb9563a701 from=translated src=- shape=111c42fa vocab=f2464a88
-/
theorem ringHom_eq_of_comp_eq (g g' : 𝕎 k →+* 𝓞)
    (hg : (algebraMap 𝓞 k).comp g = WittVector.constantCoeff)
    (hg' : (algebraMap 𝓞 k).comp g' = WittVector.constantCoeff) : g = g' := by
  refine RingHom.ext fun x => ?_
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : 𝓞)})).2 fun n => ?_
  rw [smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact (Submodule.Quotient.eq _).2 Submodule.mem_top
  | succ n =>
    rw [SModEq.sub_mem]

    have hnil : IsNilpotent ((p : 𝓞 ⧸ Ideal.span {(p : 𝓞)} ^ (n + 1))) := by
      refine ⟨n + 1, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)} ^ (n + 1))) p, ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
    have heq := WittVector.eq_of_apply_teichmuller_eq
      ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞)} ^ (n + 1))).comp g)
      ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞)} ^ (n + 1))).comp g') hnil fun c => by
        rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        exact sub_teichmuller_mem_pow hker g g' hg hg' n c
    have := RingHom.congr_fun heq x
    rwa [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at this

end Theta

end WittUniv

open WittUniv in

/--
@isnad1 id=ex.3h3v.s9.318dac11c129 from=translated src=- shape=67551871 vocab=2324d2ce
-/
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] :
    ∃ e : WittVector p k ≃+* 𝓞,
      (algebraMap 𝓞 k).comp e.toRingHom = WittVector.constantCoeff ∧
      ∀ g : WittVector p k →+* 𝓞,
        (algebraMap 𝓞 k).comp g = WittVector.constantCoeff → g = e.toRingHom := by
  haveI : Fact ¬ IsUnit (p : 𝓞) := ⟨not_isUnit_natCast hker⟩
  haveI : PerfectRing (ModP 𝓞 p) p := perfectRing_modP hk hker
  refine ⟨RingEquiv.ofBijective (thetaW hk hker) ⟨theta_injective hk hker hp, theta_surjective hk hker⟩,
    algebraMap_comp_theta hk hker, fun g hg => ?_⟩
  exact ringHom_eq_of_comp_eq hker g _ hg (algebraMap_comp_theta hk hker)
