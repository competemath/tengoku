import Tengoku.SquarefreeFugledeLean.FugledeAudit.CyclotomicFourierTransfer
import Tengoku.SquarefreeFugledeLean.FugledeAudit.CRTPairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FugledeAudit

/--
@isnad1 id=isprimit.2h2v.s6.f20bd8b61b3e from=translated src=- shape=421cfe32 vocab=355eb591
-/
theorem standard_character_nonzero_primitive (q : ℕ) [NeZero q]
    (hq : q.Prime) (d : ZMod q) (hd : d ≠ 0) :
    IsPrimitiveRoot (ZMod.stdAddChar d) q := by
  let : Fact q.Prime := ⟨hq⟩
  refine ⟨by simp [← AddChar.map_nsmul_eq_pow], ?_⟩
  intro n hn
  have he : ZMod.stdAddChar ((n : ZMod q) * d) = ZMod.stdAddChar (0 : ZMod q) := by
    simpa [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul] using hn
  have hz := ZMod.injective_stdAddChar he
  exact (ZMod.natCast_eq_zero_iff n q).mp ((mul_eq_zero.mp hz).resolve_right hd)

/--
@isnad1 id=eq.0h3v.s7.2a636bac4543 from=translated src=- shape=0890c344 vocab=7fc90a6c
-/
theorem standard_character_mul_power (q : ℕ) [NeZero q] (x d : ZMod q) :
    ZMod.stdAddChar d ^ x.val = ZMod.stdAddChar (x * d) := by
  rw [← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

/--
@isnad1 id=eq.0h4v.s7.f2b5b97afe30 from=translated src=- shape=e9daeac7 vocab=0b994f5a
-/
theorem dual_crt_sub (q H : ℕ) (ξ μ : ZMod (q * H)) :
    dualCRT q H (ξ - μ) = dualCRT q H ξ - dualCRT q H μ := by
  ext <;> simp [dualCRT, physicalCRT, map_sub, mul_sub]

/-- A zero for two actual, distinct prime-level rows transfers to every
nonzero prime phase. The other CRT coordinate may repeat arbitrarily.
@isnad1 id=eq.5h7v.s10.fd92bdd88b00 from=translated src=- shape=04cd22e1 vocab=7e497575
-/
theorem spectral_pair_weighted_fourier_zero
    (q H : ℕ) [NeZero q] [NeZero H] (hq : q.Prime) (hcop : Nat.Coprime q H)
    (A Λ : Finset (ZMod (q * H))) (h : IsCyclicSpectralPair A Λ)
    (ξ μ : Λ) (r : ℕ)
    (hd : (dualCRT q H ξ.val).1 ≠ (dualCRT q H μ.val).1)
    (hr : (dualCRT q H μ.val).1 ≠ (dualCRT q H ξ.val).1 + (r : ZMod q)) :
    ∑ a : A, ZMod.stdAddChar (physicalCRT q H a.val).1 ^ r *
      cyclicFourierEntry a.val (ξ.val - μ.val) = 0 := by
  classical
  let d : ZMod q := (dualCRT q H ξ.val).1 - (dualCRT q H μ.val).1
  let e : ZMod H := (dualCRT q H ξ.val).2 - (dualCRT q H μ.val).2
  let label : A → Fin q := fun a =>
    ⟨(physicalCRT q H a.val).1.val, ZMod.val_lt _⟩
  let z : A → IntermediateField.adjoin ℚ {ZMod.stdAddChar (1 : ZMod H)} := fun a =>
    ⟨ZMod.stdAddChar ((physicalCRT q H a.val).2 * e),
      standard_character_in_cyclotomic_field H _⟩
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hd
  have hdr : d + (r : ZMod q) ≠ 0 := by
    intro hz
    apply hr
    dsimp [d] at hz
    linear_combination -hz
  have hξμ : ξ.val ≠ μ.val := fun he => hd (congrArg (fun t => (dualCRT q H t).1) he)
  have hzero : ∑ a : A, (z a : ℂ) * ZMod.stdAddChar d ^ (label a).val = 0 := by
    have hz := h.2.2 ξ.val ξ.property μ.val μ.property hξμ
    rw [← Finset.sum_coe_sort] at hz
    convert hz using 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp [z, label]
    rw [standard_character_mul_power, cyclic_fourier_crt_pairing q H hcop, dual_crt_sub]
    simp [d, e, mul_comm]
  have ht := coprime_fibre_fourier_transfer q H hq hcop
    (ZMod.stdAddChar d) (ZMod.stdAddChar (d + (r : ZMod q)))
    (ZMod.stdAddChar (1 : ZMod H))
    (standard_character_nonzero_primitive q hq d hd0)
    (standard_character_nonzero_primitive q hq _ hdr)
    standard_character_primitive_root label z hzero
  convert ht using 1
  apply Finset.sum_congr rfl
  intro a _
  dsimp [z, label]
  rw [standard_character_mul_power, cyclic_fourier_crt_pairing q H hcop, dual_crt_sub,
    ← AddChar.map_nsmul_eq_pow]
  simp only [Prod.fst_sub, Prod.snd_sub, nsmul_eq_mul, mul_add, AddChar.map_add_eq_mul]
  dsimp [d, e]
  rw [mul_comm (r : ZMod q)]
  ring

end FugledeAudit
