import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing

universe v

set_option autoImplicit false

namespace Deformation
export _root_.Deformation (wittHom counit_coeff_of_mem_wittHom wittHomFrobenius coeff_wittHomFrobenius DieudonneModule DieudonneModule.induction_on DieudonneModule.frobenius)
namespace DieudonneModule
export _root_.Deformation.DieudonneModule (of induction_on frobenius frobenius_of map)
namespace S4b
open _root_.Deformation.DieudonneModule open _root_.Deformation

open _root_.Deformation open _root_.P2MW.S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing.Deformation

variable {p : ℕ} [hp : Fact p.Prime] {B : Type v} [CommRing B] [Bialgebra (ZMod p) B]

/--
@isnad1 id=eq.0h6v.s11.acde76cefaa9 from=translated src=- shape=2dea848a vocab=8bdf5bb6
-/
theorem coeff_wittHomFrobenius_iterate {k : ℕ} (x : wittHom (ZMod p) p k B) (n : ℕ) (i : Fin k) :
    (((wittHomFrobenius (ZMod p) p k B)^[n] x : wittHom (ZMod p) p k B) :
      TruncatedWittVector p k B).coeff i = ((x : TruncatedWittVector p k B).coeff i) ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', coeff_wittHomFrobenius, ih, ← pow_mul, ← pow_succ]

/--
@isnad1 id=eq.0h5v.s12.9616bcdf18b6 from=translated src=- shape=50a2a496 vocab=f948c0a1
-/
theorem frobenius_iterate_of {k : ℕ} (x : wittHom (ZMod p) p k B) (n : ℕ) :
    (frobenius (ZMod p) p B)^[n] (of (ZMod p) p B k x) =
      of (ZMod p) p B k ((wittHomFrobenius (ZMod p) p k B)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, frobenius_of]

/--
@isnad1 id=ex.1h2v.s9.50d04c2c4b8f from=translated src=- shape=d1f739ae vocab=846df80c
-/
theorem exists_pow_eq_zero_of_counit_eq_zero [Module.Finite (ZMod p) B] (hB : IsLocalRing B) :
    ∃ N : ℕ, ∀ b : B, Coalgebra.counit (R := ZMod p) b = 0 → b ^ N = 0 := by
  haveI := hB
  haveI : IsArtinianRing B := IsArtinianRing.of_finite (ZMod p) B
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  refine ⟨N, fun b hb => ?_⟩
  have hmem : b ∈ IsLocalRing.maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hu.map (Bialgebra.counitAlgHom (ZMod p) B)
    have h2 : Bialgebra.counitAlgHom (ZMod p) B b = 0 := hb
    rw [h2] at h1
    exact not_isUnit_zero h1
  have : b ^ N ∈ (IsLocalRing.maximalIdeal B) ^ N := Ideal.pow_mem_pow hmem N
  rwa [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this

/--
@isnad1 id=ex.1h2v.s9.7e0f4b762f14 from=translated src=- shape=415b5f08 vocab=ba1ec898
-/
theorem main [Module.Finite (ZMod p) B] (hB : IsLocalRing B) :
    ∃ n : ℕ, ∀ z : DieudonneModule (ZMod p) p B, (frobenius (ZMod p) p B)^[n] z = 0 := by
  obtain ⟨N, hN⟩ := exists_pow_eq_zero_of_counit_eq_zero (p := p) hB
  refine ⟨N, fun z => ?_⟩
  induction z using DieudonneModule.induction_on with
  | ih k x =>
    rw [frobenius_iterate_of]
    have : (wittHomFrobenius (ZMod p) p k B)^[N] x = 0 := by
      refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
      rw [coeff_wittHomFrobenius_iterate, ZeroMemClass.coe_zero, TruncatedWittVector.coeff_zero]
      exact pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le
        (hN _ (counit_coeff_of_mem_wittHom x.2 i))
    rw [this, map_zero]

end Deformation.DieudonneModule.S4b

/--
@isnad1 id=ex.1h2v.s9.7e0f4b762f14 from=translated src=- shape=415b5f08 vocab=ba1ec898
-/
theorem solution
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [Bialgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsLocalRing B) :
    ∃ n : ℕ, ∀ z : Deformation.DieudonneModule (ZMod p) p B,
      (Deformation.DieudonneModule.frobenius (ZMod p) p B)^[n] z = 0 :=
  Deformation.DieudonneModule.S4b.main hB
