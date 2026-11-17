import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_mem_ratLocalizedAt_iff.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_mem_ratLocalizedAt_iff

namespace GaloisRep
export _root_.GaloisRep (ratLocalizedAt)
namespace FlatSol
open _root_.GaloisRep

/--
@isnad1 id=iff.0h2v.s5.dac7271e7e36 from=translated src=- shape=c7a4012e vocab=9256c41c
-/
theorem mem_ratLocalizedAt_iff_coprime {p : ℕ} (q : ℚ) :
    q ∈ ratLocalizedAt p ↔ q.den.Coprime p :=
  Iff.rfl

/--
@isnad1 id=iff.1h2v.s5.0bdd73cb1a52 from=translated src=- shape=c36e0ae1 vocab=665e5dc6
-/
theorem mem_ratLocalizedAt_iff {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ ratLocalizedAt p ↔ ¬ p ∣ q.den := by
  rw [mem_ratLocalizedAt_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd]

end GaloisRep.FlatSol

/--
@isnad1 id=iff.1h2v.s5.0bdd73cb1a52 from=translated src=- shape=c36e0ae1 vocab=665e5dc6
-/
theorem solution
    {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ¬ p ∣ q.den :=
  GaloisRep.FlatSol.mem_ratLocalizedAt_iff hp q
