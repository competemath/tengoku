import Tengoku.TuzaLean.Tuza.Colored.Family
import Tengoku.TuzaLean.Tuza.Basic.Packing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Triangle types relative to the edges of a maximum packing. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Type j means exactly j edges in the fixed old edge set O.-/
noncomputable def typeFamily (A O : Finset (Sym2 V)) (j : ℕ) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (trianglesOn A).filter (fun T => (T ∩ O).card = j)

/--
@isnad1 id=iff.0h5v.s6.0f1cd6364188 from=translated src=- shape=98a95813 vocab=1bc792d0
-/
@[simp] theorem mem_typeFamily {A O T : Finset (Sym2 V)} {j : ℕ} :
    T ∈ typeFamily A O j ↔ T ∈ trianglesOn A ∧ (T ∩ O).card = j := by
  classical
  simp [typeFamily]

/--
@isnad1 id=le.0h4v.s5.69a635373f31 from=translated src=- shape=9171667c vocab=fabf0260
-/
theorem typeFamily_subset (A O : Finset (Sym2 V)) (j : ℕ) :
    typeFamily A O j ⊆ trianglesOn A := by
  classical
  exact filter_subset _ _

/--
@isnad1 id=eq.0h5v.s6.20abcff7a13b from=translated src=- shape=6b0486d8 vocab=59fcbf59
-/
theorem typeFamily_sdiff (A O C : Finset (Sym2 V)) (j : ℕ) :
    typeFamily (A \ C) O j = residual (typeFamily A O j) C := by
  classical
  ext T
  simp only [typeFamily, mem_filter, trianglesOn_sdiff, mem_residual]
  tauto

/--
@isnad1 id=coloredf.0h3v.s5.35d98a655f32 from=translated src=- shape=3fc69d85 vocab=f774cf7e
-/
theorem typeOne_colored (A O : Finset (Sym2 V)) :
    ColoredFamily (typeFamily A O 1) O := by
  intro T hT
  obtain ⟨ht, hc⟩ := mem_typeFamily.mp hT
  exact ⟨trianglesOn_card ht, hc⟩

/-- In a triangle, two old edges are equivalent to one new edge.
@isnad1 id=eq.0h3v.s5.2282a44cbe79 from=translated src=- shape=21a4d2f5 vocab=ce8acf56
-/
theorem typeTwo_eq_oneRed (A O : Finset (Sym2 V)) :
    typeFamily A O 2 = oneRedTriangles A (A \ O) := by
  ext T
  simp only [mem_typeFamily, mem_oneRedTriangles, mem_trianglesOn]
  constructor
  · rintro ⟨⟨hT, hsub⟩, hold⟩
    refine ⟨hT, hsub, ?_⟩
    have heq : T ∩ (A \ O) = T \ O := by
      ext e
      simp only [mem_inter, mem_sdiff]
      constructor
      · tauto
      · exact fun ⟨he, hno⟩ => ⟨he, hsub he, hno⟩
    rw [heq]
    have hpartition := card_sdiff_add_card_inter T O
    have hcard := hT.card_eq_three
    omega
  · rintro ⟨hT, hsub, hnew⟩
    refine ⟨⟨hT, hsub⟩, ?_⟩
    have heq : T ∩ (A \ O) = T \ O := by
      ext e
      simp only [mem_inter, mem_sdiff]
      constructor
      · tauto
      · exact fun ⟨he, hno⟩ => ⟨he, hsub he, hno⟩
    rw [heq] at hnew
    have hpartition := card_sdiff_add_card_inter T O
    have hcard := hT.card_eq_three
    omega

/--
@isnad1 id=coloredf.0h3v.s5.17ec817c4ad2 from=translated src=- shape=df12bf68 vocab=456dcfce
-/
theorem typeTwo_colored (A O : Finset (Sym2 V)) :
    ColoredFamily (typeFamily A O 2) (A \ O) := by
  rw [typeTwo_eq_oneRed]
  exact oneRedTriangles_colored _ _

/--
@isnad1 id=mem.3h5v.s7.1bbbe902cd7c from=translated src=- shape=dda81859 vocab=23cdfcde
-/
theorem new_edge_forces_typeTwo {A O T : Finset (Sym2 V)}
    (hT : T ∈ trianglesOn A) (hold : 2 ≤ (T ∩ O).card)
    {e : Sym2 V} (he : e ∈ T \ O) : T ∈ typeFamily A O 2 := by
  refine mem_typeFamily.mpr ⟨hT, ?_⟩
  have hnew : 0 < (T \ O).card := card_pos.mpr ⟨e, he⟩
  have hpartition := card_sdiff_add_card_inter T O
  have hcard := trianglesOn_card hT
  omega

/--
@isnad1 id=le.2h4v.s6.db2422fd13c5 from=translated src=- shape=e1be432e vocab=e9647df6
-/
theorem maximumPacking_old_nonempty {A : Finset (Sym2 V)}
    {P : Finset (Finset (Sym2 V))} (hP : IsMaximumPacking (trianglesOn A) P)
    {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    1 ≤ (T ∩ support P).card := by
  exact card_pos.mpr (hP.meets_support hT (trianglesOn_nonempty hT))

/-- After deleting a maximum packing of type-1 triangles, every remaining
triangle has at least two old edges.
@isnad1 id=le.3h5v.s7.bf1a4889d139 from=translated src=- shape=aed14655 vocab=bf05b8d5
-/
theorem old_card_ge_two_after_typeOne {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsMaximumPacking (typeFamily A (support P) 1) Q)
    {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn (A \ support Q)) :
    2 ≤ (T ∩ support P).card := by
  rw [trianglesOn_sdiff] at hT
  obtain ⟨ht, hd⟩ := mem_residual.mp hT
  have hpos := maximumPacking_old_nonempty hP ht
  by_contra hn
  have hone : (T ∩ support P).card = 1 := by omega
  have htype : T ∈ typeFamily A (support P) 1 := mem_typeFamily.mpr ⟨ht, hone⟩
  obtain ⟨e, he⟩ := hQ.meets_support htype (trianglesOn_nonempty ht)
  exact disjoint_left.mp hd (mem_inter.mp he).1 (mem_inter.mp he).2

/-- The old edges left after deleting the type-1 packing are counted exactly.
@isnad1 id=eq.2h4v.s7.0db94acf65fe from=translated src=- shape=de5524b4 vocab=6549c4fc
-/
theorem remaining_old_card {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (support P \ support Q).card + Q.card = 3 * P.card := by
  have hred := hQ.card_redEdges (typeOne_colored A (support P))
  have hpartition := card_sdiff_add_card_inter (support P) (support Q)
  have hp := hP.card_support_uniform (fun T hT => trianglesOn_card (hP.1 hT))
  change (support Q ∩ support P).card = Q.card at hred
  rw [inter_comm] at hred
  omega

/-- A packing in the remaining graph can be combined with the deleted packing.
@isnad1 id=le.2h4v.s6.ee49a823ec6e from=translated src=- shape=d08522a4 vocab=df8b8896
-/
theorem deleted_packing_card_add_le {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (trianglesOn (A \ support P)) Q) :
    P.card + Q.card ≤ packingNumber (trianglesOn A) := by
  have hQ' : IsPacking (trianglesOn A) Q :=
    hQ.mono_family (trianglesOn_mono sdiff_subset)
  have hd : Disjoint (support P) (support Q) := by
    apply disjoint_left.mpr
    intro e heP heQ
    obtain ⟨T, hT, heT⟩ := mem_support.mp heQ
    exact (mem_sdiff.mp ((mem_trianglesOn.mp (hQ.1 hT)).2 heT)).2 heP
  have hPQ := hP.union hQ' hd
  have hdis := disjoint_of_support_disjoint
    (fun T hT => trianglesOn_nonempty (hP.1 hT)) hd
  simpa [card_union_of_disjoint hdis] using hPQ.card_le

end Tuza
