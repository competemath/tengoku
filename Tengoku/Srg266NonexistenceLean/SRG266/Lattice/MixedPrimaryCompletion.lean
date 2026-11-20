/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimaryFamilies

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W U : Type*} [AddCommGroup W] [AddCommGroup U]

/--
@isnad1 id=eq.0h8v.s9.000088a19bdf from=translated src=- shape=3b00b456 vocab=8374f492
-/
theorem prod_sup_span_ranges {ι κ : Type*} (N : Submodule ℤ W) (M : Submodule ℤ U)
    (u : ι → W) (v : κ → U) :
    (N ⊔ Submodule.span ℤ (Set.range u)).prod (M ⊔ Submodule.span ℤ (Set.range v)) =
      N.prod M ⊔ Submodule.span ℤ
        (Set.range (Sum.elim (fun i => (u i, (0 : U))) (fun j => ((0 : W), v j)))) := by
  rw [Set.Sum.elim_range, Submodule.span_union]
  simp only [LinearMap.prod_eq_sup_map, Submodule.map_sup, Submodule.map_span,
    ← Set.range_comp]
  ac_rfl

abbrev mixedPrimarySpace (s t : PrimaryShape) :=
  primaryModelSpace .three s × primaryModelSpace .five t

def mixedPrimaryForm (s t : PrimaryShape) : LinearMap.BilinForm ℚ (mixedPrimarySpace s t) :=
  prodForm (primaryModelForm .three s) (primaryModelForm .five t)

def mixedPrimaryBase (s t : PrimaryShape) : Submodule ℤ (mixedPrimarySpace s t) :=
  (primaryModelLattice .three s).prod (primaryModelLattice .five t)

def mixedPrimaryVector (s t : PrimaryShape) : Fin s.arity ⊕ Fin t.arity → mixedPrimarySpace s t :=
  Sum.elim (fun i => (primaryModelVector .three s i, 0))
    (fun j => (0, primaryModelVector .five t j))

def mixedPrimaryPeriod (s t : PrimaryShape) : Fin s.arity ⊕ Fin t.arity → ℤ :=
  Sum.elim (fun _ => 3) (fun _ => 5)

/--
@isnad1 id=eq.0h2v.s8.4301a87ef3c1 from=translated src=- shape=cb656727 vocab=2592b051
-/
theorem mixedPrimary_dual (s t : PrimaryShape) :
    (mixedPrimaryForm s t).dualSubmodule (mixedPrimaryBase s t) =
      mixedPrimaryBase s t ⊔ Submodule.span ℤ (Set.range (mixedPrimaryVector s t)) := by
  rw [mixedPrimaryForm, mixedPrimaryBase, dualSubmodule_prodForm,
    primaryModel_dual, primaryModel_dual]
  exact prod_sup_span_ranges _ _ _ _

/--
@isnad1 id=mem.1h4v.s9.2a1318aa815b from=translated src=- shape=f7203e32 vocab=cc0bdf6b
-/
theorem mixedPrimary_cross (s t : PrimaryShape) (i j : Fin s.arity ⊕ Fin t.arity) (hij : i ≠ j) :
    mixedPrimaryForm s t (mixedPrimaryVector s t i) (mixedPrimaryVector s t j) ∈
      (1 : Submodule ℤ ℚ) := by
  rcases i with i | i <;> rcases j with j | j
  · simpa [mixedPrimaryForm, mixedPrimaryVector, prodForm_apply] using
      primaryModel_cross .three s i j (fun h => hij (congrArg Sum.inl h))
  · simp [mixedPrimaryForm, mixedPrimaryVector, prodForm_apply]
  · simp [mixedPrimaryForm, mixedPrimaryVector, prodForm_apply]
  · simpa [mixedPrimaryForm, mixedPrimaryVector, prodForm_apply] using
      primaryModel_cross .five t i j (fun h => hij (congrArg Sum.inr h))

/--
@isnad1 id=mem.0h3v.s7.2e87805b163b from=translated src=- shape=f5b535ec vocab=76e70e34
-/
theorem mixedPrimary_period (s t : PrimaryShape) (i : Fin s.arity ⊕ Fin t.arity) :
    mixedPrimaryPeriod s t i • mixedPrimaryVector s t i ∈ mixedPrimaryBase s t := by
  rcases i with i | i
  · exact ⟨primaryModel_period .three s i, by simp [mixedPrimaryVector, mixedPrimaryPeriod]⟩
  · exact ⟨by simp [mixedPrimaryVector, mixedPrimaryPeriod], primaryModel_period .five t i⟩

/--
@isnad1 id=eq.0h2v.s6.d4dec8d33c4d from=translated src=- shape=8f2ea3af vocab=be867fbf
-/
theorem mixedPrimary_finrank (s t : PrimaryShape) :
    Module.finrank ℚ (mixedPrimarySpace s t) = primaryModelRank .three s + primaryModelRank .five t := by
  rw [Module.finrank_prod, primaryModel_finrank, primaryModel_finrank]

variable [Module ℚ W] {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}
variable {s t : PrimaryShape}

def mixedPrimarySource (S : PrimaryFamily B N .three s) (T : PrimaryFamily B N .five t) :
    Fin s.arity ⊕ Fin t.arity → W := Sum.elim S.vec T.vec

def mixedPrimaryLattice (S : PrimaryFamily B N .three s) (T : PrimaryFamily B N .five t) :
    Submodule ℤ (W × mixedPrimarySpace s t) :=
  glueLattice N (mixedPrimaryBase s t) (fun i => (mixedPrimarySource S T i, mixedPrimaryVector s t i))

/--
@isnad1 id=eq.1h7v.s8.14832f614241 from=translated src=- shape=2e1a4160 vocab=651a3150
-/
theorem mixedPrimarySource_dual (S : PrimaryFamily B N .three s) (T : PrimaryFamily B N .five t)
    (h : B.dualSubmodule N = torsionPart B N 3 ⊔ torsionPart B N 5) :
    B.dualSubmodule N = N ⊔ Submodule.span ℤ (Set.range (mixedPrimarySource S T)) := by
  rw [h, mixedPrimarySource, Set.Sum.elim_range, Submodule.span_union]
  rw [show torsionPart B N 3 = N ⊔ Submodule.span ℤ (Set.range S.vec) from S.spans,
    show torsionPart B N 5 = N ⊔ Submodule.span ℤ (Set.range T.vec) from T.spans]
  simp only [sup_assoc, sup_left_comm, sup_left_idem]

/--
@isnad1 id=mem.2h9v.s8.403c864b9ba5 from=translated src=- shape=d31f0336 vocab=1dc094c3
-/
theorem mixedPrimarySource_cross (S : PrimaryFamily B N .three s) (T : PrimaryFamily B N .five t)
    (hs : B.IsSymm) (i j : Fin s.arity ⊕ Fin t.arity) (hij : i ≠ j) :
    B (mixedPrimarySource S T i) (mixedPrimarySource S T j) ∈ (1 : Submodule ℤ ℚ) := by
  have hcop : IsCoprime (3 : ℤ) (5 : ℤ) := ⟨2, -1, by norm_num⟩
  rcases i with i | i <;> rcases j with j | j
  · exact S.cross i j (fun h => hij (congrArg Sum.inl h))
  · exact inner_mem_one_of_coprime hs hcop (mem_torsionPart.mp (S.mem i)).1
      (mem_torsionPart.mp (S.mem i)).2 (mem_torsionPart.mp (T.mem j)).1
      (mem_torsionPart.mp (T.mem j)).2
  · exact inner_mem_one_of_coprime hs hcop.symm (mem_torsionPart.mp (T.mem i)).1
      (mem_torsionPart.mp (T.mem i)).2 (mem_torsionPart.mp (S.mem j)).1
      (mem_torsionPart.mp (S.mem j)).2
  · exact T.cross i j (fun h => hij (congrArg Sum.inr h))

/--
@isnad1 id=and.5h7v.s9.61ffe3d2ba9b from=translated src=- shape=788328c1 vocab=47f0d984
-/
theorem complete_mixed_primary (S : PrimaryFamily B N .three s) (T : PrimaryFamily B N .five t)
    (hs : B.IsSymm) (hl : IsLattice ℚ N) (hi : IsIntegral B N) (he : IsEven B N)
    (hd : B.dualSubmodule N = torsionPart B N 3 ⊔ torsionPart B N 5) :
    IsLattice ℚ (mixedPrimaryLattice S T) ∧
      IsEven (prodForm B (mixedPrimaryForm s t)) (mixedPrimaryLattice S T) ∧
      (prodForm B (mixedPrimaryForm s t)).dualSubmodule (mixedPrimaryLattice S T) =
        mixedPrimaryLattice S T := by
  refine complete_even_glue (mixedPrimarySource S T) (mixedPrimaryVector s t) (mixedPrimaryPeriod s t)
    hs (prodForm_isSymm (primaryModel_isSymm .three s) (primaryModel_isSymm .five t))
    hl (isLattice_prod (primaryModel_isLattice .three s) (primaryModel_isLattice .five t))
    hi (isIntegral_prod (primaryModel_isIntegral .three s) (primaryModel_isIntegral .five t))
    he (isEven_prod (primaryModel_isEven .three s) (primaryModel_isEven .five t))
    (mixedPrimarySource_dual S T hd) (mixedPrimary_dual s t) (mixedPrimary_period s t)
    (mixedPrimarySource_cross S T hs) (mixedPrimary_cross s t) ?_ ?_
  · rintro (i | i)
    · obtain ⟨k, hk⟩ := S.norm i
      obtain ⟨l, hl⟩ := primaryModel_matched_norm .three s i
      refine ⟨k + l, ?_⟩
      simp only [mixedPrimarySource, mixedPrimaryVector, Sum.elim_inl, mixedPrimaryForm,
        prodForm_apply, map_zero, add_zero]
      rw [hk]
      push_cast
      linarith
    · obtain ⟨k, hk⟩ := T.norm i
      obtain ⟨l, hl⟩ := primaryModel_matched_norm .five t i
      refine ⟨k + l, ?_⟩
      simp only [mixedPrimarySource, mixedPrimaryVector, Sum.elim_inr, mixedPrimaryForm,
        prodForm_apply, map_zero, zero_add]
      rw [hk]
      push_cast
      linarith
  · rintro (i | i) a ha
    · exact S.unit i a ha
    · exact T.unit i a ha

/--
@isnad1 id=lt.2h5v.s10.d76ec67e1c7e from=translated src=- shape=38b2fb02 vocab=fdd97abd
-/
theorem mixedPrimaryLattice_posDef (hpd : ∀ x : W, x ≠ 0 → 0 < B x x) :
    ∀ z : W × mixedPrimarySpace s t, z ≠ 0 → 0 < prodForm B (mixedPrimaryForm s t) z z :=
  prodForm_posDef hpd (prodForm_posDef (primaryModel_posDef .three s) (primaryModel_posDef .five t))

/--
@isnad1 id=eq.0h3v.s7.54e24b4e07b6 from=translated src=- shape=0321073b vocab=0337b1d2
-/
theorem mixedPrimaryLattice_finrank [Module.Finite ℚ W] :
    Module.finrank ℚ (W × mixedPrimarySpace s t) =
      Module.finrank ℚ W + primaryModelRank .three s + primaryModelRank .five t := by
  rw [Module.finrank_prod, mixedPrimary_finrank, Nat.add_assoc]

/--
@isnad1 id=mem.1h8v.s8.6fc5dc1e9137 from=translated src=- shape=a7ff3c0d vocab=3d9826e0
-/
theorem mem_mixedPrimaryLattice_left (S : PrimaryFamily B N .three s) (T : PrimaryFamily B N .five t)
    {x : W} (hx : x ∈ N) : (x, (0 : mixedPrimarySpace s t)) ∈ mixedPrimaryLattice S T :=
  prod_le_glueLattice ⟨hx, zero_mem _⟩

/--
@isnad1 id=eq.0h6v.s10.4d6098ca7313 from=translated src=- shape=236119cd vocab=a957e08f
-/
theorem mixedPrimaryLattice_left_pair (x y : W) :
    prodForm B (mixedPrimaryForm s t) (x, (0 : mixedPrimarySpace s t)) (y, 0) = B x y := by
  simp [prodForm_apply]

omit [AddCommGroup W] [Module ℚ W] in

/--
@isnad1 id=iff.0h2v.s6.9e0fe3569c10 from=translated src=- shape=e1045bdc vocab=6dccaddb
-/
theorem eight_dvd_mixed_rank_iff (s t : PrimaryShape) :
    8 ∣ 18 + primaryModelRank .three s + primaryModelRank .five t ↔
      (s = .two ∧ t = .zero) ∨ (s = .two ∧ t = .two) ∨
      (s = .four ∧ t = .four) ∨ (s = .four ∧ t = .binary) := by
  cases s <;> cases t <;> decide

end SRG266.Lattice
