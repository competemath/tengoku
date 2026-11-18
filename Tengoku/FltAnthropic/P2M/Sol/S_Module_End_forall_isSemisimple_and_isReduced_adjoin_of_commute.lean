import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RRedEngine
section Semisimple

variable {K : Type*} [Field K] [PerfectField K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [PerfectField K] [FiniteDimensional K V] in
/--
@isnad1 id=commute.3h5v.s10.ddbe6e3d3b1b from=translated src=- shape=d20527e4 vocab=6e06c21a
-/
theorem commute_of_mem_adjoin {s : Set (Module.End K V)} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    {x y : Module.End K V} (hx : x ∈ Algebra.adjoin K s) (hy : y ∈ Algebra.adjoin K s) : Commute x y := by
  have h1 := Algebra.adjoin_le_centralizer_centralizer K s hx
  have h2 : y ∈ Subalgebra.centralizer K s := by
    refine (Algebra.adjoin_le (fun z hz => ?_) : Algebra.adjoin K s ≤ Subalgebra.centralizer K s) hy
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro w hw
    exact hcomm w hw z hz
  rw [Subalgebra.mem_centralizer_iff] at h1
  exact (h1 y h2).symm

/--
@isnad1 id=issemisi.3h4v.s9.49049eef67af from=translated src=- shape=7b25e0f7 vocab=dee8cbad
-/
theorem isSemisimple_of_mem_adjoin {s : Set (Module.End K V)}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hs : ∀ x ∈ s, Module.End.IsSemisimple x)
    {a : Module.End K V} (ha : a ∈ Algebra.adjoin K s) : a.IsSemisimple := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Module.End.IsSemisimple_smul r Module.End.isSemisimple_id
  | add x y hx hy ihx ihy => exact Module.End.IsSemisimple.add_of_commute (commute_of_mem_adjoin hcomm hx hy) ihx ihy
  | mul x y hx hy ihx ihy => exact Module.End.IsSemisimple.mul_of_commute (commute_of_mem_adjoin hcomm hx hy) ihx ihy

/--
@isnad1 id=isreduce.2h3v.s10.df011b979592 from=translated src=- shape=baff4716 vocab=a14538d2
-/
theorem isReduced_adjoin {s : Set (Module.End K V)}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hs : ∀ x ∈ s, Module.End.IsSemisimple x) :
    IsReduced (Algebra.adjoin K s) := by
  constructor
  rintro ⟨x, hx⟩ ⟨n, hn⟩
  have hxn : x ^ n = 0 := by
    have := congrArg Subtype.val hn
    simpa using this
  exact Subtype.ext
    (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨n, hxn⟩ (isSemisimple_of_mem_adjoin hcomm hs hx))

end Semisimple

end RRedEngine

/--
@isnad1 id=and.2h3v.s10.383b6262a766 from=translated src=- shape=cd88da99 vocab=a14538d2
-/
theorem solution
    {K : Type*} [Field K] [PerfectField K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {s : Set (Module.End K V)} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (hs : ∀ x ∈ s, Module.End.IsSemisimple x) :
    (∀ a ∈ Algebra.adjoin K s, Module.End.IsSemisimple a) ∧ IsReduced ↥(Algebra.adjoin K s) :=
  ⟨fun _ ha => RRedEngine.isSemisimple_of_mem_adjoin hcomm hs ha, RRedEngine.isReduced_adjoin hcomm hs⟩
