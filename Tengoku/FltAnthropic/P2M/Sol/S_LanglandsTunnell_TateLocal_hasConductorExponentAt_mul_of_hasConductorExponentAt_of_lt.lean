import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open LanglandsTunnell.TateLocal in
/--
@isnad1 id=hascondu.3h6v.s11.4f03014e61cd from=translated src=- shape=b7895fb4 vocab=ef4d506f
-/
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (lam nu : (v.adicCompletion K)ˣ →* ℂˣ) (a b : ℕ)
    (hlam : HasConductorExponentAt K v lam a) (hnu : HasConductorExponentAt K v nu b) (hlt : b < a) :
    HasConductorExponentAt K v (lam * nu) a := by
  obtain ⟨hlamTriv, hlamNontriv⟩ := hlam
  obtain ⟨hnuTriv, -⟩ := hnu
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  ·
    rw [MonoidHom.mul_apply, hlamTriv u hu, hnuTriv u (higherUnitsAt_antitone K v hlt.le hu), one_mul]
  · rcases le_or_gt b m with hbm | hmb
    ·
      obtain ⟨u, hu, hne⟩ := hlamNontriv m hm
      exact ⟨u, hu, by rwa [MonoidHom.mul_apply, hnuTriv u (higherUnitsAt_antitone K v hbm hu), mul_one]⟩
    ·
      obtain ⟨u, hu, hne⟩ := hlamNontriv b hlt
      exact ⟨u, higherUnitsAt_antitone K v hmb.le hu, by rwa [MonoidHom.mul_apply, hnuTriv u hu, mul_one]⟩
