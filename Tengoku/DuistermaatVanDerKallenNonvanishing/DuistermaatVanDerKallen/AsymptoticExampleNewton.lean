import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AsymptoticExample
import Tengoku.Seed.Analysis.Convex.Combination
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.RepresentativeInvariance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Newton interiority and the complete semantic regression for the manuscript
example, expressed in the same Laurent-polynomial representation as the main
targets. An explicit open box lies in the Newton hull. -/

namespace DuistermaatVanDerKallen
noncomputable section
open scoped BigOperators
open Set

def infinityExampleLaurent (c : ℂ) : MultiLaurent 2 :=
  AddMonoidAlgebra.single 0 c + AddMonoidAlgebra.single ![1, 0] 1 +
  AddMonoidAlgebra.single ![-1, 1] 1 + AddMonoidAlgebra.single ![-1, 0] (-2) +
  AddMonoidAlgebra.single ![-1, -1] 1

def infinityExampleVertex : Fin 3 → (Fin 2 → ℤ) :=
  ![![1, 0], ![-1, 1], ![-1, -1]]

/--
@isnad1 id=eq.0h2v.s6.d4cba4766be9 from=translated src=- shape=b7561f5d vocab=dfec7285
-/
theorem infinityExample_vertex_coeff (c : ℂ) (i : Fin 3) :
    (infinityExampleLaurent c).coeff (infinityExampleVertex i) = 1 := by
  fin_cases i <;> norm_num [infinityExampleLaurent, infinityExampleVertex,
    AddMonoidAlgebra.coeff_single, funext_iff, Fin.forall_fin_two]

/--
@isnad1 id=mem.0h1v.s6.c0075131e2d6 from=translated src=- shape=7559a679 vocab=d1c98993
-/
theorem infinityExample_newton_interior (c : ℂ) :
    (0 : Fin 2 → ℝ) ∈ interior (newtonPolytope (infinityExampleLaurent c)) := by
  let U : Set (Fin 2 → ℝ) := {x | |x 0| < 1 / 4 ∧ |x 1| < 1 / 4}
  have hU : IsOpen U :=
    (isOpen_lt (continuous_apply 0).abs continuous_const).inter
      (isOpen_lt (continuous_apply 1).abs continuous_const)
  apply (mem_interior_iff_mem_nhds).2
  apply Filter.mem_of_superset (hU.mem_nhds (by norm_num [U]))
  intro x hx
  have hx0 := abs_lt.mp hx.1
  have hx1 := abs_lt.mp hx.2
  let w : Fin 3 → ℝ := ![(1 + x 0) / 2, (1 - x 0 + 2 * x 1) / 4,
    (1 - x 0 - 2 * x 1) / 4]
  apply mem_convexHull_of_exists_fintype w (fun i => exponentVector (infinityExampleVertex i))
  · intro i
    fin_cases i <;> dsimp [w] <;> linarith
  · simp [w, Fin.sum_univ_succ]
    ring
  · intro i
    exact ⟨infinityExampleVertex i, Finsupp.mem_support_iff.mpr (by
      rw [infinityExample_vertex_coeff]; exact one_ne_zero), rfl⟩
  · ext i
    fin_cases i <;> simp [w, infinityExampleVertex, exponentVector, Fin.sum_univ_succ] <;> ring

/--
@isnad1 id=eq.1h2v.s5.fb6d64b8f5f1 from=translated src=- shape=538172e7 vocab=5482fd15
-/
theorem infinityExample_laurent_eval (c : ℂ) (z : Fin 2 → ℂ) (hz : ∀ i, z i ≠ 0) :
    laurentEval (infinityExampleLaurent c) z =
      ambientEval (infinityExamplePolynomial c) (torusEmbed z) := by
  rw [laurentEval_eq_hom _ hz]
  simp [infinityExampleLaurent, laurentEvalHom, AddMonoidAlgebra.lift_single,
    torusMonomialHom, Fin.prod_univ_two, infinityExample_eval, torusEmbed]
  field_simp [hz 0, hz 1]
  ring

/--
@isnad1 id=eqon.0h1v.s5.e685549a45c0 from=translated src=- shape=b3e6b072 vocab=2fe91f6d
-/
theorem infinityExample_representative_eqOn (c : ℂ) :
    Set.EqOn (ambientEval (laurentRepresentative (infinityExampleLaurent c)))
      (ambientEval (infinityExamplePolynomial c)) (affineTorus 2) := by
  intro x hx
  rw [← embed_coordinates hx, laurentRepresentative_eval]
  exact infinityExample_laurent_eval c _ (affineTorus_coordinate_ne_zero hx)

/--
@isnad1 id=eq.0h1v.s6.ee2e17d38b81 from=translated src=- shape=4a9d968c vocab=1d5920bb
-/
theorem infinityExample_laurent_function (c : ℂ) :
    laurentOnAffineTorus (infinityExampleLaurent c) =
      fun x : affineTorus 2 => ambientEval (infinityExamplePolynomial c) x.val := by
  funext x
  exact infinityExample_representative_eqOn c x.property

end
end DuistermaatVanDerKallen
