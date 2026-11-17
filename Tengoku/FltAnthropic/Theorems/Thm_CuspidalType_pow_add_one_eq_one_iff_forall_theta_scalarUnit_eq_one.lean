import Tengoku.FltAnthropic.Definitions.Def_CuspidalType_IsCuspidalOfType
import Tengoku.FltAnthropic.P2M.Sol.S_CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

local notation α "^+" M:51 => FixedPoints.addSubgroup M α

set_option autoImplicit false

/--
@isnad1 id=iff.0h3v.s11.9114621d61f7 from=translated src=- shape=85961f00 vocab=348c2219
-/
theorem CuspidalType.pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    (θ : (GaloisField q 2)ˣ →* Kˣ) :
    θ ^ (q + 1) = 1 ↔
      ∀ c : (ZMod q)ˣ, θ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1 := by exact @_root_.P2MW.S_CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one.solution q _ K _ θ
