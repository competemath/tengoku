import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_FormalOmega_exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_span.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_span

set_option autoImplicit false

namespace P8W2

/--
@isnad1 id=surjecti.3h5v.s8.087f96a67578 from=translated src=- shape=103dbaa9 vocab=2839d84f
-/
theorem surjective_of_forall_sub_mem_span {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (ϖ : B)
    (hϖ : ϖ ∈ Set.range f) (N : ℕ) (hN : ϖ ^ N = 0)
    (h : ∀ b : B, ∃ a : A, b - f a ∈ Ideal.span {ϖ}) : Function.Surjective f := by
  obtain ⟨p, hp⟩ := hϖ

  have step : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ Ideal.span {ϖ ^ n} := by
    intro n
    induction n with
    | zero => intro b; exact ⟨0, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a₀, ha₀⟩ := h b
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha₀
      obtain ⟨a₁, ha₁⟩ := ih c
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 ha₁
      refine ⟨a₀ + p * a₁, Ideal.mem_span_singleton'.2 ⟨d, ?_⟩⟩
      rw [map_add, map_mul, hp]

      have e1 : b - (f a₀ + ϖ * f a₁) = ϖ * (c - f a₁) := by rw [← sub_sub, ← hc]; ring
      rw [e1, ← hd]; ring
  intro b
  obtain ⟨a, ha⟩ := step N b
  rw [hN, Ideal.span_singleton_zero, Ideal.mem_bot, sub_eq_zero] at ha
  exact ⟨a, ha.symm⟩

/--
@isnad1 id=surjecti.5h8v.s8.ee763e009473 from=translated src=- shape=51a35f7a vocab=0db56d39
-/
theorem surjective_of_comp_eq_of_ker_le {W B K : Type*} [CommRing W] [CommRing B] [CommRing K]
    (f : W →+* B) (ρ : B →+* K) (c : W →+* K) (hc : Function.Surjective c) (hcomp : ρ.comp f = c)
    (ϖ : B) (hker : RingHom.ker ρ ≤ Ideal.span {ϖ}) (hϖ : ϖ ∈ Set.range f) (N : ℕ) (hN : ϖ ^ N = 0) :
    Function.Surjective f := by
  refine surjective_of_forall_sub_mem_span f ϖ hϖ N hN (fun b => ?_)
  obtain ⟨w, hw⟩ := hc (ρ b)
  refine ⟨w, hker ?_⟩
  rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply, hcomp, hw, sub_self]

end P8W2

namespace OnrWitt

open WittVector

variable {r : ℕ} [Fact r.Prime]
variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] {π : 𝒪}
variable {Onr : Type} [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
variable {k : Type} [Field k] [CharP k r] [PerfectRing k r] {ρ₁ : Onr →+* k}

abbrev I (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (N : ℕ) : Ideal Onr :=
  Ideal.span {algebraMap 𝒪 Onr π ^ N}

/--
@isnad1 id=le.0h4v.s7.a629b5396e12 from=translated src=- shape=24669bea vocab=28528c99
-/
theorem I_le (N : ℕ) : I π Onr (N + 1) ≤ I π Onr N := by
  refine Ideal.span_le.2 ?_
  rintro _ rfl
  exact Ideal.mem_span_singleton'.2 ⟨algebraMap 𝒪 Onr π, by ring⟩

section residue

/--
@isnad1 id=mem.1h5v.s8.ae8b0e6c259b from=translated src=- shape=0dce39b5 vocab=270eb5df
-/
theorem pi_mem_ker (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) : algebraMap 𝒪 Onr π ∈ RingHom.ker ρ₁ := by
  rw [hker]; exact Ideal.mem_span_singleton_self _

/--
@isnad1 id=le.1h6v.s8.3def1434e90f from=translated src=- shape=151da98f vocab=175036e9
-/
theorem I_le_ker (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N : ℕ) : I π Onr (N + 1) ≤ RingHom.ker ρ₁ := by
  refine Ideal.span_le.2 ?_
  rintro _ rfl
  rw [SetLike.mem_coe, pow_succ]
  exact Ideal.mul_mem_left _ _ (pi_mem_ker hker)

def rhoBar (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N : ℕ) : Onr ⧸ I π Onr (N + 1) →+* k :=
  Ideal.Quotient.lift (I π Onr (N + 1)) ρ₁ (fun a ha => I_le_ker hker N ha)

/--
@isnad1 id=eq.1h7v.s9.b7aa0d7e273b from=translated src=- shape=b28ecc73 vocab=b3c06484
-/
@[scoped simp] theorem rhoBar_mk (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N : ℕ) (x : Onr) : rhoBar hker N (Ideal.Quotient.mk _ x) = ρ₁ x :=
  Ideal.Quotient.lift_mk _ _ _

/--
@isnad1 id=surjecti.2h6v.s9.5ea5f396134f from=translated src=- shape=15302860 vocab=2eeb75fa
-/
theorem rhoBar_surjective (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) : Function.Surjective (rhoBar hker N) := by
  intro a
  obtain ⟨x, rfl⟩ := hρ₁ a
  exact ⟨Ideal.Quotient.mk _ x, rhoBar_mk hker N x⟩

/--
@isnad1 id=eq.1h6v.s10.a996ae74bca8 from=translated src=- shape=e539fc09 vocab=b3c06484
-/
theorem ker_rhoBar (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N : ℕ) :
    RingHom.ker (rhoBar hker N) = Ideal.span {Ideal.Quotient.mk (I π Onr (N + 1)) (algebraMap 𝒪 Onr π)} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, rhoBar_mk] at hz
    have hx : x ∈ Ideal.span {algebraMap 𝒪 Onr π} := by rw [← hker]; exact hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ c, by rw [← map_mul, hc]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, rhoBar_mk]
    exact pi_mem_ker hker

/--
@isnad1 id=isnilpot.1h6v.s9.5576e03cbed4 from=translated src=- shape=0634b50c vocab=bdacd56f
-/
theorem isNilpotent_ker_rhoBar (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N : ℕ) : IsNilpotent (RingHom.ker (rhoBar hker N)) := by
  refine ⟨N + 1, ?_⟩
  rw [ker_rhoBar, Ideal.span_singleton_pow, ← map_pow, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

noncomputable def fN (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) : WittVector r k →+* Onr ⧸ I π Onr (N + 1) :=
  (WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker r k (Onr ⧸ I π Onr (N + 1))
    (rhoBar hker N) (rhoBar_surjective hker hρ₁ N) (isNilpotent_ker_rhoBar hker N)).exists.choose

/--
@isnad1 id=eq.2h7v.s8.59294c0f77be from=translated src=- shape=bc58f90d vocab=7ca7f258
-/
theorem rhoBar_comp_fN (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) :
    (rhoBar hker N).comp (fN hker hρ₁ N) = WittVector.constantCoeff :=
  (WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker r k (Onr ⧸ I π Onr (N + 1))
    (rhoBar hker N) (rhoBar_surjective hker hρ₁ N) (isNilpotent_ker_rhoBar hker N)).exists.choose_spec

/--
@isnad1 id=eq.3h8v.s9.6e054814885b from=translated src=- shape=6827ac18 vocab=7ca7f258
-/
theorem fN_unique (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) (g : WittVector r k →+* Onr ⧸ I π Onr (N + 1))
    (hg : (rhoBar hker N).comp g = WittVector.constantCoeff) : g = fN hker hρ₁ N :=
  (WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker r k (Onr ⧸ I π Onr (N + 1))
    (rhoBar hker N) (rhoBar_surjective hker hρ₁ N) (isNilpotent_ker_rhoBar hker N)).unique hg (rhoBar_comp_fN hker hρ₁ N)

/--
@isnad1 id=eq.2h7v.s9.6210c6b2749f from=translated src=- shape=a3139e33 vocab=513a2fc5
-/
theorem factor_comp_fN (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) :
    (Ideal.Quotient.factor (I_le (π := π) (Onr := Onr) (N + 1))).comp (fN hker hρ₁ (N + 1)) = fN hker hρ₁ N := by
  apply fN_unique
  rw [← RingHom.comp_assoc]
  have h : (rhoBar hker N).comp (Ideal.Quotient.factor (I_le (π := π) (Onr := Onr) (N + 1))) = rhoBar hker (N + 1) := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk, rhoBar_mk]
  rw [h, rhoBar_comp_fN]

/--
@isnad1 id=eq.3h9v.s10.6517b0717cb9 from=translated src=- shape=fe94c3f1 vocab=21fae602
-/
theorem rho_eq_constantCoeff (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) (x : Onr) (w : WittVector r k)
    (h : Ideal.Quotient.mk (I π Onr (N + 1)) x = fN hker hρ₁ N w) : ρ₁ x = WittVector.constantCoeff w := by
  rw [← rhoBar_mk hker N x, h, ← RingHom.comp_apply, rhoBar_comp_fN]

end residue

section kernel

/--
@isnad1 id=ex.1h3v.s6.28a628ca4941 from=translated src=- shape=dab8fb11 vocab=554e9f8c
-/
theorem exists_r_eq_mul (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) : ∃ u : 𝒪, ((r : ℕ) : 𝒪) = u * π := by
  have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨u, hu.symm⟩

/--
@isnad1 id=ex.1h3v.s6.9f31e55d7f34 from=translated src=- shape=ea11575d vocab=554e9f8c
-/
theorem exists_pi_eq_mul (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) : ∃ v : 𝒪, π = v * ((r : ℕ) : 𝒪) := by
  have : π ∈ Ideal.span {((r : ℕ) : 𝒪)} := by rw [hunr]; exact Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨v, hv.symm⟩

/--
@isnad1 id=ne.1h4v.s7.a49a850f80bd from=translated src=- shape=4e5b21b6 vocab=120edf14
-/
theorem algebraMap_pi_ne_zero (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) : algebraMap 𝒪 Onr π ≠ 0 := by
  intro h0
  obtain ⟨u, hu⟩ := exists_r_eq_mul hunr
  have : ((r : ℕ) : Onr) = 0 := by
    rw [← map_natCast (algebraMap 𝒪 Onr) r, hu, map_mul, h0, mul_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : r.Prime).ne_zero) this

/--
@isnad1 id=surjecti.3h7v.s9.0051489a71ed from=translated src=- shape=ae42c863 vocab=43ca9e77
-/
theorem fN_surjective (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) : Function.Surjective (fN hker hρ₁ N) := by
  obtain ⟨u, hu⟩ := exists_r_eq_mul hunr
  obtain ⟨v, hv⟩ := exists_pi_eq_mul hunr
  have hrπ : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π} :=
    Ideal.mem_span_singleton'.2 ⟨algebraMap 𝒪 Onr u, by rw [← map_natCast (algebraMap 𝒪 Onr) r, hu, map_mul]⟩
  refine P8W2.surjective_of_comp_eq_of_ker_le (fN hker hρ₁ N) (rhoBar hker N) WittVector.constantCoeff
    (WittVector.constantCoeff_surjective r) (rhoBar_comp_fN hker hρ₁ N)
    ((r : ℕ) : Onr ⧸ I π Onr (N + 1)) ?_ ⟨(r : WittVector r k), map_natCast _ r⟩ (N + 1) ?_
  ·
    rw [ker_rhoBar hker N, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    refine Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ (algebraMap 𝒪 Onr v), ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk (I π Onr (N + 1))) r, ← map_mul, ← map_natCast (algebraMap 𝒪 Onr) r,
      ← map_mul, ← hv]
  · rw [← map_natCast (Ideal.Quotient.mk (I π Onr (N + 1))) r, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    rw [show I π Onr (N + 1) = Ideal.span {algebraMap 𝒪 Onr π} ^ (N + 1) from (Ideal.span_singleton_pow _ _).symm]
    exact Ideal.pow_mem_pow hrπ (N + 1)

/--
@isnad1 id=eq.4h8v.s9.6517501fa83f from=translated src=- shape=4fe8c2aa vocab=ec6605f8
-/
theorem fN_apply_eq_zero_of_mem (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) (w : WittVector r k)
    (hw : w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ (N + 1)}) : fN hker hρ₁ N w = 0 := by
  obtain ⟨u, hu⟩ := exists_r_eq_mul hunr
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hw
  rw [map_mul, map_pow, map_natCast]
  have hr : ((r : ℕ) : Onr ⧸ I π Onr (N + 1)) ^ (N + 1) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (I π Onr (N + 1))) r, ← map_natCast (algebraMap 𝒪 Onr) r, hu, map_mul,
      ← map_pow, mul_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  rw [hr, mul_zero]

/--
@isnad1 id=mem.4h8v.s9.59e9a0fef2dd from=translated src=- shape=c5a64692 vocab=ec6605f8
-/
theorem mem_of_fN_apply_eq_zero (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) : ∀ (N : ℕ) (w : WittVector r k), fN hker hρ₁ N w = 0 →
    w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ (N + 1)} := by
  obtain ⟨u, hu⟩ := exists_r_eq_mul hunr
  obtain ⟨v, hv⟩ := exists_pi_eq_mul hunr
  have hvu : v * u = 1 := by
    have h1 : π = (v * u) * π := by
      conv_lhs => rw [hv, hu]
      ring
    have hπ0 : π ≠ 0 := by
      intro h; apply algebraMap_pi_ne_zero (Onr := Onr) hunr; rw [h, map_zero]
    have := mul_right_cancel₀ hπ0 (h1.symm.trans (one_mul π).symm)
    exact this

  have digit : ∀ (N : ℕ) (w : WittVector r k), fN hker hρ₁ N w = 0 → ∃ w', w = (r : WittVector r k) * w' := by
    intro N w hw
    have h0 : WittVector.constantCoeff w = 0 := by
      rw [← rho_eq_constantCoeff hker hρ₁ N 0 w (by rw [map_zero, hw]), map_zero]
    have hmem : w ∈ Ideal.span {((r : ℕ) : WittVector r k)} := by
      rw [← WittVector.ker_constantCoeff]; exact h0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨c, by rw [← hc, mul_comm]⟩
  intro N
  induction N with
  | zero =>
    intro w hw
    obtain ⟨w', rfl⟩ := digit 0 w hw
    rw [zero_add, pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  | succ N ih =>
    intro w hw
    obtain ⟨w', rfl⟩ := digit (N + 1) _ hw

    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (fN hker hρ₁ (N + 1) w')
    rw [map_mul, map_natCast, ← hy, ← map_natCast (Ideal.Quotient.mk (I π Onr (N + 1 + 1))) r, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem] at hw
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hw

    have hy' : y ∈ I π Onr (N + 1) := by
      have e1 : (algebraMap 𝒪 Onr u * y - c * algebraMap 𝒪 Onr π ^ (N + 1)) * algebraMap 𝒪 Onr π = 0 := by
        have : ((r : ℕ) : Onr) = algebraMap 𝒪 Onr u * algebraMap 𝒪 Onr π := by
          rw [← map_natCast (algebraMap 𝒪 Onr) r, hu, map_mul]
        rw [this] at hc
        rw [sub_mul, pow_succ] at *
        linear_combination (-1 : Onr) * hc
      have e2 : algebraMap 𝒪 Onr u * y = c * algebraMap 𝒪 Onr π ^ (N + 1) := by
        have := (mul_eq_zero.1 e1).resolve_right (algebraMap_pi_ne_zero hunr)
        exact sub_eq_zero.1 this
      have e3 : y = algebraMap 𝒪 Onr v * (algebraMap 𝒪 Onr u * y) := by
        rw [← mul_assoc, ← map_mul, hvu, map_one, one_mul]
      rw [e3, e2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton'.2 ⟨c, rfl⟩)

    have hN : fN hker hρ₁ N w' = 0 := by
      rw [← factor_comp_fN hker hρ₁ N, RingHom.comp_apply, ← hy, Ideal.Quotient.factor_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hy'
    have := ih w' hN
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 this
    refine Ideal.mem_span_singleton'.2 ⟨d, ?_⟩
    rw [← hd]; ring

/--
@isnad1 id=iff.3h8v.s9.a8837ebb8265 from=translated src=- shape=64fe8386 vocab=ec6605f8
-/
theorem fN_apply_eq_zero_iff (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N : ℕ) (w : WittVector r k) :
    fN hker hρ₁ N w = 0 ↔ w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ (N + 1)} :=
  ⟨mem_of_fN_apply_eq_zero hunr hker hρ₁ N w, fN_apply_eq_zero_of_mem hunr hker hρ₁ N w⟩

end kernel

end OnrWitt
open scoped _root_.P2MW.S_CerednikDrinfeld_FormalOmega_exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_span.OnrWitt

/--
@isnad1 id=ex.11h7v.s12.5e150003c65a from=translated src=- shape=8e6e31b0 vocab=1f67e969
-/
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (k : Type) [Field k] [CharP k r] [PerfectRing k r]
    (ρ₁ : Onr →+* k) (hρ₁ : Function.Surjective ρ₁) (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) :
    ∀ N : ℕ, ∃ f : WittVector r k →+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N},
      (0 < N → ∀ (x : Onr) (w : WittVector r k),
          Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x = f w → ρ₁ x = WittVector.constantCoeff w) ∧
      Function.Surjective f ∧
      (∀ w : WittVector r k, f w = 0 ↔ w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ N}) := by
  intro N
  cases N with
  | zero =>

    have htop : Ideal.span {algebraMap 𝒪 Onr π ^ 0} = ⊤ := by rw [pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ 0}) := Ideal.Quotient.subsingleton_iff.2 htop
    refine ⟨(Ideal.Quotient.factor (by rw [htop]; exact le_top)).comp (OnrWitt.fN hker hρ₁ 0), fun h => absurd h (lt_irrefl 0),
      fun y => ⟨0, Subsingleton.elim _ _⟩, fun w => ⟨fun _ => ?_, fun _ => Subsingleton.elim _ _⟩⟩
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  | succ N =>
    exact ⟨OnrWitt.fN hker hρ₁ N, fun _ x w h => OnrWitt.rho_eq_constantCoeff hker hρ₁ N x w h,
      OnrWitt.fN_surjective hunr hker hρ₁ N, fun w => OnrWitt.fN_apply_eq_zero_iff hunr hker hρ₁ N w⟩
