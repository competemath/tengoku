import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one

set_option autoImplicit false

/--
@isnad1 id=ex.1h3v.s8.09dd1d8a2012 from=translated src=- shape=678ab084 vocab=9160ed60
-/
theorem solution
    {m : Type} [Fintype m] [DecidableEq m] (n : ℕ)
    (g : Matrix m m ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod n)) :
    ∃ g' : Matrix m m ℤ, IsUnit ((g'.det : ℤ) : ZMod n) ∧
      (g * g').map (Int.castRingHom (ZMod n)) = 1 ∧ (g' * g).map (Int.castRingHom (ZMod n)) = 1 := by
  classical
  let f : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
  let gb : Matrix m m (ZMod n) := g.map f
  have hfdet : ∀ M : Matrix m m ℤ, ((M.det : ℤ) : ZMod n) = (M.map f).det := by
    intro M
    have h := RingHom.map_det f M
    simpa using h
  have hdet : IsUnit gb.det := by
    rw [show gb.det = ((g.det : ℤ) : ZMod n) from (hfdet g).symm]
    exact hg
  let g' : Matrix m m ℤ := (gb⁻¹).map (ZMod.cast : ZMod n → ℤ)
  have hg' : g'.map f = gb⁻¹ := by
    ext i j
    show f (ZMod.cast (gb⁻¹ i j)) = gb⁻¹ i j
    exact ZMod.intCast_zmod_cast (gb⁻¹ i j)
  refine ⟨g', ?_, ?_, ?_⟩
  · rw [hfdet g', hg']
    exact Matrix.isUnit_nonsing_inv_det gb hdet
  · show (g * g').map f = 1
    rw [Matrix.map_mul, hg']
    exact Matrix.mul_nonsing_inv gb hdet
  · show (g' * g).map f = 1
    rw [Matrix.map_mul, hg']
    exact Matrix.nonsing_inv_mul gb hdet
