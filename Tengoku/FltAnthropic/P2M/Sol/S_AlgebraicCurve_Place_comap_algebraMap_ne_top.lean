import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_comap_algebraMap_ne_top.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_comap_algebraMap_ne_top

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place)
open _root_.AlgebraicCurve

namespace Place
export _root_.AlgebraicCurve.Place (ext ne_top' toValuationSubring)
open _root_.AlgebraicCurve.Place

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']

variable (w : Place K F')

private theorem rowMain [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'
  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  letI : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  letI : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  have hx : IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2

end Restrict

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_comap_algebraMap_ne_top.AlgebraicCurve in
/--
@isnad1 id=ne.0h4v.s6.6511e94f3837 from=translated src=- shape=2d54b157 vocab=9d2c2f54
-/
theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F'] (w : Place K F') [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ :=
  AlgebraicCurve.Place.rowMain w
