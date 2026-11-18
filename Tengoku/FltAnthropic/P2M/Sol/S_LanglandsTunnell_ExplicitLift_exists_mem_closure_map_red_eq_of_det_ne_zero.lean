import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ExplicitLift
import Tengoku.Seed.Algebra.Group.Submonoid.Membership

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero_impl` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero

set_option autoImplicit false

namespace LanglandsTunnell
namespace P0

open FLT.ExplicitLift Matrix

abbrev Mat : Type := Matrix (Fin 2) (Fin 2) (ℤ√(-2))

def K48 : List Mat := [
  !![⟨1, 0⟩, ⟨0, 0⟩; ⟨0, 0⟩, ⟨1, 0⟩],
  !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩],
  !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩],
  !![⟨0, 0⟩, ⟨-1, 0⟩; ⟨1, 0⟩, ⟨-1, 0⟩],
  !![⟨-1, -1⟩, ⟨0, 1⟩; ⟨-1, 0⟩, ⟨1, 0⟩],
  !![⟨0, 0⟩, ⟨1, 0⟩; ⟨1, 0⟩, ⟨0, -1⟩],
  !![⟨1, 1⟩, ⟨0, -1⟩; ⟨2, 0⟩, ⟨-1, -1⟩],
  !![⟨0, 1⟩, ⟨1, -1⟩; ⟨1, 1⟩, ⟨0, -1⟩],
  !![⟨1, 0⟩, ⟨-1, -1⟩; ⟨0, 0⟩, ⟨-1, 0⟩],
  !![⟨1, -1⟩, ⟨-1, 0⟩; ⟨-1, -1⟩, ⟨0, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 0⟩; ⟨-1, 1⟩, ⟨1, 0⟩],
  !![⟨0, -1⟩, ⟨-1, 1⟩; ⟨-1, 0⟩, ⟨1, 1⟩],
  !![⟨-1, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨2, 0⟩],
  !![⟨-1, 1⟩, ⟨1, 0⟩; ⟨0, 1⟩, ⟨1, 0⟩],
  !![⟨-1, 0⟩, ⟨0, 1⟩; ⟨-1, 0⟩, ⟨1, 1⟩],
  !![⟨-2, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨1, 0⟩],
  !![⟨0, 1⟩, ⟨1, 0⟩; ⟨1, 0⟩, ⟨0, 0⟩],
  !![⟨-1, 1⟩, ⟨2, 0⟩; ⟨0, 1⟩, ⟨1, -1⟩],
  !![⟨0, 1⟩, ⟨1, -1⟩; ⟨1, 0⟩, ⟨-1, -1⟩],
  !![⟨1, 0⟩, ⟨0, 0⟩; ⟨1, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨0, -1⟩; ⟨0, -1⟩, ⟨-1, 0⟩],
  !![⟨2, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-2, 0⟩],
  !![⟨0, -1⟩, ⟨-1, 0⟩; ⟨-1, -1⟩, ⟨-1, 1⟩],
  !![⟨1, -1⟩, ⟨-2, 0⟩; ⟨-1, -1⟩, ⟨-1, 1⟩],
  !![⟨0, -1⟩, ⟨-1, 1⟩; ⟨-1, -1⟩, ⟨0, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 0⟩; ⟨0, 0⟩, ⟨-1, 0⟩],
  !![⟨1, -1⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-2, 0⟩],
  !![⟨1, -1⟩, ⟨-2, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩],
  !![⟨0, -1⟩, ⟨-1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩],
  !![⟨-1, -1⟩, ⟨-1, 1⟩; ⟨-1, 0⟩, ⟨0, 1⟩],
  !![⟨-1, -1⟩, ⟨-1, 1⟩; ⟨-2, 0⟩, ⟨1, 1⟩],
  !![⟨-1, 0⟩, ⟨0, 1⟩; ⟨0, 1⟩, ⟨1, 0⟩],
  !![⟨-2, 0⟩, ⟨1, 1⟩; ⟨-1, 1⟩, ⟨2, 0⟩],
  !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨0, 1⟩, ⟨1, -1⟩],
  !![⟨-1, 1⟩, ⟨1, 0⟩; ⟨1, 1⟩, ⟨0, -1⟩],
  !![⟨-1, 0⟩, ⟨1, 1⟩; ⟨0, 0⟩, ⟨1, 0⟩],
  !![⟨-1, 1⟩, ⟨2, 0⟩; ⟨1, 1⟩, ⟨1, -1⟩],
  !![⟨0, 1⟩, ⟨1, 0⟩; ⟨1, 1⟩, ⟨1, -1⟩],
  !![⟨1, 1⟩, ⟨1, -1⟩; ⟨2, 0⟩, ⟨-1, -1⟩],
  !![⟨1, 1⟩, ⟨1, -1⟩; ⟨1, 0⟩, ⟨0, -1⟩],
  !![⟨1, 0⟩, ⟨0, -1⟩; ⟨1, 0⟩, ⟨-1, -1⟩],
  !![⟨2, 0⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-1, 0⟩],
  !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨1, 0⟩, ⟨0, 0⟩],
  !![⟨1, 1⟩, ⟨0, -1⟩; ⟨1, 0⟩, ⟨-1, 0⟩],
  !![⟨0, 0⟩, ⟨-1, 0⟩; ⟨-1, 0⟩, ⟨0, 1⟩],
  !![⟨-1, -1⟩, ⟨0, 1⟩; ⟨-2, 0⟩, ⟨1, 1⟩],
  !![⟨0, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨1, 0⟩]
]

def W48 : List (List (Fin 2)) := [
  [],
  [0],
  [1],
  [0, 0],
  [0, 1],
  [1, 0],
  [1, 1],
  [0, 0, 1],
  [0, 1, 0],
  [0, 1, 1],
  [1, 0, 0],
  [1, 0, 1],
  [1, 1, 0],
  [1, 1, 1],
  [0, 0, 1, 0],
  [0, 0, 1, 1],
  [0, 1, 0, 0],
  [0, 1, 0, 1],
  [0, 1, 1, 0],
  [0, 1, 1, 1],
  [1, 0, 1, 0],
  [1, 0, 1, 1],
  [1, 1, 0, 0],
  [1, 1, 0, 1],
  [1, 1, 1, 0],
  [1, 1, 1, 1],
  [0, 0, 1, 0, 0],
  [0, 0, 1, 0, 1],
  [0, 0, 1, 1, 0],
  [0, 0, 1, 1, 1],
  [0, 1, 0, 1, 0],
  [0, 1, 0, 1, 1],
  [0, 1, 1, 0, 0],
  [0, 1, 1, 0, 1],
  [0, 1, 1, 1, 0],
  [1, 0, 1, 0, 0],
  [1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0],
  [1, 0, 1, 1, 1],
  [1, 1, 0, 1, 0],
  [1, 1, 0, 1, 1],
  [1, 1, 1, 0, 0],
  [1, 1, 1, 0, 1],
  [1, 1, 1, 1, 0],
  [0, 0, 1, 1, 1, 0],
  [0, 1, 1, 1, 0, 0],
  [1, 0, 1, 1, 1, 0],
  [1, 1, 1, 1, 0, 0]
]

def evalWord : List (Fin 2) → Mat
  | [] => 1
  | 0 :: w => Slift * evalWord w
  | 1 :: w => Tlift * evalWord w

theorem K48_eq_map_evalWord : K48 = W48.map evalWord := by decide

theorem one_mem_K48 : (1 : Mat) ∈ K48 := by decide

theorem Slift_mul_mem_K48 : ∀ k ∈ K48, Slift * k ∈ K48 := by decide

theorem Tlift_mul_mem_K48 : ∀ k ∈ K48, Tlift * k ∈ K48 := by decide

theorem evalWord_mem_closure (w : List (Fin 2)) :
    evalWord w ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) := by
  induction w with
  | nil => exact Submonoid.one_mem _
  | cons a w ih =>
    match a with
    | 0 => exact Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) ih
    | 1 => exact Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) ih

theorem mem_closure_iff_mem_K48 (k : Mat) :
    k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ↔ k ∈ K48 := by
  constructor
  · intro hk
    induction hk using Submonoid.closure_induction_left with
    | one => exact one_mem_K48
    | mul_left x hx y hy ih =>
      rcases hx with rfl | rfl
      · exact Slift_mul_mem_K48 y ih
      · exact Tlift_mul_mem_K48 y ih
  · intro hk
    have h := K48_eq_map_evalWord ▸ hk
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    exact evalWord_mem_closure w

def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

theorem red_eq_redc (z : ℤ√(-2)) : red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [red, redc, Zsqrtd.lift, sub_eq_add_neg]

theorem map_red_eq_map_redc (m : Mat) : m.map red = m.map redc := by
  ext i j; simp [Matrix.map_apply, red_eq_redc]

theorem mem_map_redc_K48_of_det_ne_zero :
    ∀ m : Matrix (Fin 2) (Fin 2) (ZMod 3), m.det ≠ 0 → m ∈ K48.map (·.map redc) := by decide

end LanglandsTunnell.P0

open LanglandsTunnell.P0 in

theorem LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero_impl (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hg : g.det ≠ 0) :
    ∃ M ∈ Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))),
      M.map FLT.ExplicitLift.red = g := by
  obtain ⟨M, hM, hMg⟩ := List.mem_map.1 (mem_map_redc_K48_of_det_ne_zero g hg)
  exact ⟨M, (mem_closure_iff_mem_K48 M).2 hM, by rw [map_red_eq_map_redc]; exact hMg⟩

theorem solution (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hg : g.det ≠ 0) :
    ∃ M ∈ Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))),
      M.map FLT.ExplicitLift.red = g := by
  apply LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero_impl <;> assumption
