import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Chosen segment trajectories and the induced fiber transport maps.
Uniqueness removes dependence on the chosen existence witnesses. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- A fiber in the original nonvanishing-coordinate torus.-/
abbrev LaurentFiber {d : ℕ} (f : MultiLaurent d) (s : ℂ) :=
  {z : Fin d → ℂ // (∀ i, z i ≠ 0) ∧ laurentEval f z = s}

/-- Precisely the exclusion hypothesis for a base segment.-/
def GoodSegment {d : ℕ} (f : MultiLaurent d) (s a : ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, s + t • a ∉
    ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
    asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (laurentDifferentialNorm f)

/--
@isnad1 id=goodsegm.1h4v.s4.66c85b14a84e from=translated src=- shape=ab2706fc vocab=bffc3af3
-/
theorem GoodSegment.reverse {d : ℕ} {f : MultiLaurent d} {s a : ℂ}
    (h : GoodSegment f s a) : GoodSegment f (s + a) (-a) := by
  intro t ht
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have heq : s + a + t • (-a) = s + (1 - t) • a := by
    simp [sub_smul, smul_neg]
    abel
  rw [heq]
  exact h (1 - t) ht'

end
end DuistermaatVanDerKallen
