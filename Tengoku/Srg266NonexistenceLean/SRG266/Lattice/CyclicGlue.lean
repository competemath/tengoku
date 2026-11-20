/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Glue
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Even

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
variable {N : Submodule ℤ W} {M : Submodule ℤ U} {u : W} {v : U}

def cyclicGlueLattice (N : Submodule ℤ W) (M : Submodule ℤ U) (u : W) (v : U) :
    Submodule ℤ (W × U) := N.prod M ⊔ Submodule.span ℤ {(u, v)}

/--
@isnad1 id=islattic.2h6v.s7.5a5b5f7e97b5 from=translated src=- shape=9084e1df vocab=739f26ec
-/
theorem cyclicGlueLattice_isLattice (hN : IsLattice ℚ N) (hM : IsLattice ℚ M) :
    IsLattice ℚ (cyclicGlueLattice N M u v) := by
  refine ⟨Submodule.FG.sup (isLattice_prod hN hM).fg
    (Submodule.fg_span (Set.finite_singleton _)), ?_⟩
  refine top_unique ?_
  rw [← (isLattice_prod hN hM).spans]
  exact Submodule.span_mono (fun _ hz => Submodule.mem_sup_left hz)

/--
@isnad1 id=isintegr.7h8v.s9.83bd7d631280 from=translated src=- shape=9d2a0749 vocab=572a051a
-/
theorem cyclicGlueLattice_isIntegral (hsB : B.IsSymm) (hsC : C.IsSymm)
    (hN : IsIntegral B N) (hM : IsIntegral C M)
    (hu : u ∈ B.dualSubmodule N) (hv : v ∈ C.dualSubmodule M)
    (hdiag : B u u + C v v ∈ (1 : Submodule ℤ ℚ)) :
    IsIntegral (prodForm B C) (cyclicGlueLattice N M u v) := by
  refine isIntegral_sup_span (prodForm_isSymm hsB hsC) (isIntegral_prod hN hM) ?_ ?_
  · rintro z hz _ (rfl : _ = (u, v))
    rw [prodForm_apply, hsB.eq, hsC.eq]
    exact add_mem (hu z.1 hz.1) (hv z.2 hz.2)
  · rintro _ (rfl : _ = (u, v)) _ (rfl : _ = (u, v))
    exact hdiag

/--
@isnad1 id=iseven.4h4v.s9.fe85b61aedca from=translated src=- shape=9237701d vocab=44e278a0
-/
theorem isEven_sup_span {X : Type*} [AddCommGroup X] [Module ℚ X]
    {F : LinearMap.BilinForm ℚ X} (hs : F.IsSymm) {P : Submodule ℤ X} {s : Set X}
    (hint : IsIntegral F (P ⊔ Submodule.span ℤ s)) (hP : IsEven F P)
    (he : ∀ x ∈ s, ∃ a : ℤ, F x x = 2 * (a : ℚ)) :
    IsEven F (P ⊔ Submodule.span ℤ s) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨i, hi⟩ := hP a ha
  have hspan : IsIntegral F (Submodule.span ℤ s) :=
    fun _ hz _ hw => hint (Submodule.mem_sup_right hz) _ (Submodule.mem_sup_right hw)
  obtain ⟨j, hj⟩ := isEven_of_span F hs hspan he b hb
  obtain ⟨k, hk⟩ := mem_one_iff.mp
    (hint (Submodule.mem_sup_left ha) b (Submodule.mem_sup_right hb))
  refine ⟨i + j + k, ?_⟩
  simp only [map_add, LinearMap.add_apply]
  rw [hs.eq b a, hi, hj, ← hk]
  push_cast
  ring

/--
@isnad1 id=iseven.6h8v.s9.512ab68acfda from=translated src=- shape=1c90fb94 vocab=92c9c3f2
-/
theorem cyclicGlueLattice_isEven (hsB : B.IsSymm) (hsC : C.IsSymm)
    (hint : IsIntegral (prodForm B C) (cyclicGlueLattice N M u v))
    (hN : IsEven B N) (hM : IsEven C M)
    (hdiag : ∃ k : ℤ, B u u + C v v = 2 * (k : ℚ)) :
    IsEven (prodForm B C) (cyclicGlueLattice N M u v) := by
  refine isEven_sup_span (prodForm_isSymm hsB hsC) hint ?_ ?_
  · intro z hz
    obtain ⟨i, hi⟩ := hN z.1 hz.1
    obtain ⟨j, hj⟩ := hM z.2 hz.2
    refine ⟨i + j, ?_⟩
    rw [prodForm_apply, hi, hj]
    push_cast
    ring
  · rintro _ (rfl : _ = (u, v))
    exact hdiag

omit [Module ℚ W] [Module ℚ U] in

/--
@isnad1 id=iff.2h8v.s8.ed8e0d9b59f4 from=translated src=- shape=fc16b4e6 vocab=cb00300d
-/
theorem cyclicGlueLattice_mem_left_iff {p : ℤ}
    (hu : p • u ∈ N) (hv : ∀ a : ℤ, a • v ∈ M ↔ p ∣ a) (x : W) :
    (x, (0 : U)) ∈ cyclicGlueLattice N M u v ↔ x ∈ N := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, heq⟩ := Submodule.mem_sup.mp hx
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hs := congrArg Prod.snd heq
    change a.2 + m • v = 0 at hs
    have hm : m • v ∈ M := by
      rw [eq_neg_of_add_eq_zero_right hs]
      exact M.neg_mem ha.2
    obtain ⟨k, hk⟩ := (hv m).mp hm
    have hmu : m • u ∈ N := by
      have he : m • u = k • (p • u) := by rw [hk]; module
      rw [he]
      exact N.smul_mem k hu
    have hf := congrArg Prod.fst heq
    change a.1 + m • u = x at hf
    rw [← hf]
    exact N.add_mem ha.1 hmu
  · intro hx
    exact Submodule.mem_sup_left ⟨hx, M.zero_mem⟩

omit [Module ℚ W] [Module ℚ U] in
/--
@isnad1 id=iff.2h8v.s8.78a6d64abc05 from=translated src=- shape=3c176743 vocab=cb00300d
-/
theorem cyclicGlueLattice_mem_right_iff {p : ℤ}
    (hu : ∀ a : ℤ, a • u ∈ N ↔ p ∣ a) (hv : p • v ∈ M) (y : U) :
    ((0 : W), y) ∈ cyclicGlueLattice N M u v ↔ y ∈ M := by
  constructor
  · intro hy
    obtain ⟨a, ha, b, hb, heq⟩ := Submodule.mem_sup.mp hy
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hf := congrArg Prod.fst heq
    change a.1 + m • u = 0 at hf
    have hm : m • u ∈ N := by
      rw [eq_neg_of_add_eq_zero_right hf]
      exact N.neg_mem ha.1
    obtain ⟨k, hk⟩ := (hu m).mp hm
    have hmv : m • v ∈ M := by
      have he : m • v = k • (p • v) := by rw [hk]; module
      rw [he]
      exact M.smul_mem k hv
    have hs := congrArg Prod.snd heq
    change a.2 + m • v = y at hs
    rw [← hs]
    exact M.add_mem ha.2 hmv
  · intro hy
    exact Submodule.mem_sup_left ⟨N.zero_mem, hy⟩

end SRG266.Lattice
