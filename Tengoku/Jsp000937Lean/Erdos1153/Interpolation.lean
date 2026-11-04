import Tengoku.Jsp000937Lean.Erdos1153.NodeOrder
import Tengoku.Seed.Data.Finset.Lattice.Fold

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lagrange interpolation and the Lebesgue inequality

Mathlib's checked `Lagrange.interpolate` operator is specialized here to the
frozen Erdős 1153 node representation.  The principal output is the
pointwise interpolation inequality with either an arbitrary common nodal
bound or the actual finite nodal maximum.
-/

namespace Erdos1153

open Polynomial

noncomputable section

/-- Every polynomial of degree below the number of nodes has its Lagrange
expansion.
@isnad1 id=eq.1h3v.s6.f255e9c4c9d3 from=translated src=- shape=0e5ed4d1 vocab=5b9af641
-/
lemma lagrangeExpansion {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hp : p.degree < n) :
    p = ∑ k : Fin n,
      Polynomial.C (p.eval (nodes.point k)) * lagrangeBasis nodes k := by
  have hp' : p.degree < (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hp
  simpa [lagrangeBasis] using
    (Lagrange.eq_interpolate (s := Finset.univ) nodes.injective.injOn hp')

/-- Pointwise form of the Lagrange expansion.
@isnad1 id=eq.1h4v.s6.991b67344afc from=translated src=- shape=529dd964 vocab=9778e721
-/
lemma eval_lagrangeExpansion {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hp : p.degree < n) (t : ℝ) :
    p.eval t = ∑ k : Fin n,
      p.eval (nodes.point k) * lagrangeFundamental nodes k t := by
  calc
    p.eval t =
        (∑ k : Fin n,
          Polynomial.C (p.eval (nodes.point k)) * lagrangeBasis nodes k).eval t :=
      congrArg (fun q : ℝ[X] => q.eval t) (lagrangeExpansion nodes p hp)
    _ = ∑ k : Fin n,
        p.eval (nodes.point k) * lagrangeFundamental nodes k t := by
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, lagrangeBasis_eval]

/-- The fundamental interpolation inequality with an arbitrary common upper
bound for the absolute nodal values.
@isnad1 id=le.2h5v.s6.82415f13b386 from=translated src=- shape=481f504f vocab=a8c73eaf
-/
lemma abs_eval_le_mul_lebesgueFunction {n : ℕ} (nodes : NodeFamily n)
    (p : ℝ[X]) (hp : p.degree < n) (M t : ℝ)
    (hM : ∀ k : Fin n, |p.eval (nodes.point k)| ≤ M) :
    |p.eval t| ≤ M * lebesgueFunction nodes t := by
  rw [eval_lagrangeExpansion nodes p hp t]
  calc
    |∑ k : Fin n, p.eval (nodes.point k) * lagrangeFundamental nodes k t| ≤
        ∑ k : Fin n, |p.eval (nodes.point k) * lagrangeFundamental nodes k t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n,
        |p.eval (nodes.point k)| * |lagrangeFundamental nodes k t| := by
      simp only [abs_mul]
    _ ≤ ∑ k : Fin n, M * |lagrangeFundamental nodes k t| := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hM k) (abs_nonneg _)
    _ = M * lebesgueFunction nodes t := by
      rw [lebesgueFunction, Finset.mul_sum]

/-- In particular, nodal values bounded by one are controlled by the
Lebesgue function itself.
@isnad1 id=le.2h4v.s6.1e36870eacc2 from=translated src=- shape=628f303f vocab=a5fa630a
-/
lemma abs_eval_le_lebesgueFunction {n : ℕ} (nodes : NodeFamily n)
    (p : ℝ[X]) (hp : p.degree < n) (t : ℝ)
    (hp_nodes : ∀ k : Fin n, |p.eval (nodes.point k)| ≤ 1) :
    |p.eval t| ≤ lebesgueFunction nodes t := by
  simpa only [one_mul] using
    abs_eval_le_mul_lebesgueFunction nodes p hp 1 t hp_nodes

private lemma fin_univ_nonempty_of_pos {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The maximum absolute value of `p` on a nonempty node family.-/
def nodalMax {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X]) (hn : 0 < n) : ℝ :=
  Finset.univ.sup' (fin_univ_nonempty_of_pos hn)
    (fun k : Fin n => |p.eval (nodes.point k)|)

/-- Every nodal absolute value is bounded by `nodalMax`.
@isnad1 id=le.1h4v.s5.5fac4e9ef16b from=translated src=- shape=4ced6b4b vocab=d6aa78df
-/
lemma abs_eval_node_le_nodalMax {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hn : 0 < n) (k : Fin n) :
    |p.eval (nodes.point k)| ≤ nodalMax nodes p hn := by
  unfold nodalMax
  exact Finset.le_sup'
    (f := fun j : Fin n => |p.eval (nodes.point j)|) (Finset.mem_univ k)

/-- The finite nodal maximum is attained.
@isnad1 id=ex.1h3v.s5.ed019d72dc6a from=translated src=- shape=19d6c98f vocab=afadd3d9
-/
lemma exists_nodalMax_eq {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hn : 0 < n) :
    ∃ k : Fin n, nodalMax nodes p hn = |p.eval (nodes.point k)| := by
  simpa only [nodalMax, Finset.mem_univ, true_and] using
    (Finset.exists_mem_eq_sup' (fin_univ_nonempty_of_pos hn)
      (fun k : Fin n => |p.eval (nodes.point k)|))

/-- Pointwise interpolation inequality in the conventional finite-maximum
form.
@isnad1 id=le.2h4v.s6.5060c1aedbe4 from=translated src=- shape=3d4349dd vocab=4b8ce889
-/
lemma abs_eval_le_nodalMax_mul_lebesgueFunction {n : ℕ}
    (nodes : NodeFamily n) (p : ℝ[X]) (hp : p.degree < n)
    (hn : 0 < n) (t : ℝ) :
    |p.eval t| ≤ nodalMax nodes p hn * lebesgueFunction nodes t :=
  abs_eval_le_mul_lebesgueFunction nodes p hp (nodalMax nodes p hn) t
    (abs_eval_node_le_nodalMax nodes p hn)

end

end Erdos1153
