/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CyclicSelfDual
import Tengoku.Seed.LinearAlgebra.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] {N : Submodule ℤ W} {u v : W}

omit [AddCommGroup W] in
/--
@isnad1 id=eq.0h2v.s5.ee5a4097f1b4 from=translated src=- shape=279ee339 vocab=044e32a3
-/
theorem range_fin_one_eq_singleton (v : Fin 1 → W) : Set.range v = {v 0} := by
  have hv : v = fun _ : Fin 1 => v 0 :=
    funext fun i => congrArg v (Subsingleton.elim i 0)
  rw [hv, Set.range_const]

omit [AddCommGroup W] in
/--
@isnad1 id=eq.0h2v.s6.6f8a84481ceb from=translated src=- shape=050b1535 vocab=c7601a5c
-/
theorem range_fin_two_eq_pair (v : Fin 2 → W) : Set.range v = {v 0, v 1} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx :
      x = v 0 ∨ x = v 1) with hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩

/--
@isnad1 id=eq.0h4v.s8.fdfb3b9af6ad from=translated src=- shape=7f1b2fb7 vocab=cccb8239
-/
theorem sup_span_pair (N : Submodule ℤ W) (u v : W) :
    N ⊔ Submodule.span ℤ {u, v} =
      (N ⊔ Submodule.span ℤ {u}) ⊔ (N ⊔ Submodule.span ℤ {v}) := by
  rw [show ({u, v} : Set W) = {u} ∪ {v} by ext; simp [or_comm], Submodule.span_union]
  exact sup_sup_distrib_left _ _ _

/--
@isnad1 id=eq.4h11v.s8.96c3b0d43387 from=translated src=- shape=6ce128a5 vocab=5498f793
-/
theorem sup_span_pair_smul_eq {p a b c d e f : ℤ}
    (hu : p • u ∈ N) (hv : p • v ∈ N)
    (ha : a * b + p * c = 1) (hd : d * e + p * f = 1) :
    N ⊔ Submodule.span ℤ {a • u, d • v} = N ⊔ Submodule.span ℤ {u, v} := by
  rw [sup_span_pair, sup_span_pair,
    sup_span_smul_eq_of_bezout hu ha, sup_span_smul_eq_of_bezout hv hd]

/--
@isnad1 id=eq.3h5v.s8.2a02a6dd4c91 from=translated src=- shape=362de53f vocab=be4c4ac6
-/
theorem sup_span_pair_hadamard_eq {p : ℤ} (hp : IsCoprime 2 p)
    (hu : p • u ∈ N) (hv : p • v ∈ N) :
    N ⊔ Submodule.span ℤ {u + v, u - v} = N ⊔ Submodule.span ℤ {u, v} := by
  let E := N ⊔ Submodule.span ℤ {u + v, u - v}
  have hplus : u + v ∈ E := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hminus : u - v ∈ E := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have h2u : (2 : ℤ) • u ∈ E := by
    rw [show (2 : ℤ) • u = (u + v) + (u - v) by module]
    exact E.add_mem hplus hminus
  have h2v : (2 : ℤ) • v ∈ E := by
    rw [show (2 : ℤ) • v = (u + v) - (u - v) by module]
    exact E.sub_mem hplus hminus
  obtain ⟨a, b, hab⟩ := hp
  have hmem (w : W) (h2w : (2 : ℤ) • w ∈ E) (hpw : p • w ∈ N) : w ∈ E := by
    have heq : w = a • ((2 : ℤ) • w) + b • (p • w) := by
      calc
        w = (a * 2 + b * p) • w := by rw [hab, one_smul]
        _ = _ := by module
    rw [heq]
    exact E.add_mem (E.smul_mem a h2w) (Submodule.mem_sup_left (N.smul_mem b hpw))
  apply le_antisymm
  · have hu' : u ∈ N ⊔ Submodule.span ℤ {u, v} :=
      Submodule.mem_sup_right (Submodule.subset_span (by simp))
    have hv' : v ∈ N ⊔ Submodule.span ℤ {u, v} :=
      Submodule.mem_sup_right (Submodule.subset_span (by simp))
    refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    intro z hz
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz :
      z = u + v ∨ z = u - v) with rfl | rfl
    · exact Submodule.add_mem _ hu' hv'
    · exact Submodule.sub_mem _ hu' hv'
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    intro z hz
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz :
      z = u ∨ z = v) with hz | hz
    · subst z
      exact hmem u h2u hu
    · subst z
      exact hmem v h2v hv

/--
@isnad1 id=eq.0h6v.s9.96e61ac47ad7 from=translated src=- shape=cce978c4 vocab=c314f85a
-/
theorem prod_sup_span_singletons {U : Type*} [AddCommGroup U]
    (N : Submodule ℤ W) (M : Submodule ℤ U) (u : W) (v : U) :
    (N ⊔ Submodule.span ℤ {u}).prod (M ⊔ Submodule.span ℤ {v}) =
      N.prod M ⊔ Submodule.span ℤ {(u, (0 : U)), ((0 : W), v)} := by
  rw [show ({(u, (0 : U)), ((0 : W), v)} : Set (W × U)) =
    {(u, 0)} ∪ {(0, v)} by ext; simp [or_comm], Submodule.span_union]
  simp only [LinearMap.prod_eq_sup_map, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  ac_rfl

end SRG266.Lattice
