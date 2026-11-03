import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticTransvection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_common_detour` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_two_step_alignment` (it only prints; the queue checks the axioms of every declaration). -/

/-! A root-free, finite-case detour choice for two nonzero vectors. -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

def IsLeftNondegenerate (omega : BilinForm (K := K) (V := V)) : Prop :=
  ∀ x, x ≠ 0 → ∃ z, omega z x ≠ 0

def IsRightNondegenerate (omega : BilinForm (K := K) (V := V)) : Prop :=
  ∀ y, y ≠ 0 → ∃ z, omega y z ≠ 0

/-! Two nonzero linear functionals have a common nonvanishing point.  The
proof uses only `zx`, `zy`, or `zx + zy`, with no infinitude argument. -/
/--
@isnad1 id=ex.4h5v.s9.e5bf87bac03c from=translated src=- shape=b2217f84 vocab=2199587c
-/
theorem exists_common_detour
    (omega : BilinForm (K := K) (V := V))
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, omega z x ≠ 0 ∧ omega y z ≠ 0 := by
  obtain ⟨zx, hzx⟩ := hleft x hx
  obtain ⟨zy, hzy⟩ := hright y hy
  by_cases hyzx : omega y zx ≠ 0
  · exact ⟨zx, hzx, hyzx⟩
  by_cases hzyx : omega zy x ≠ 0
  · exact ⟨zy, hzyx, hzy⟩
  refine ⟨zx + zy, ?_, ?_⟩
  · simp only [map_add, LinearMap.add_apply, not_ne_iff.mp hzyx, add_zero]
    exact hzx
  · simp only [map_add, LinearMap.add_apply, not_ne_iff.mp hyzx, zero_add]
    exact hzy

/--
@isnad1 id=ex.5h5v.s10.095b108c53e1 from=translated src=- shape=5b723ce6 vocab=6beba67c
-/
theorem exists_two_step_alignment
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z,
      equiv omega halt (y - z) (omega y z)⁻¹
        (equiv omega halt (z - x) (omega z x)⁻¹ x) = y := by
  obtain ⟨z, hzx, hyz⟩ := exists_common_detour omega hleft hright x y hx hy
  exact ⟨z, two_step_align omega halt x z y hzx hyz⟩

end AlbertLean.Generic.SymplecticTransvection
