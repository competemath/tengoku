import Tengoku.Seed.Combinatorics.SimpleGraph.Coloring.Vertex
import Tengoku.Seed.Combinatorics.SimpleGraph.Clique

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite graph parameters

The paper uses natural-valued chromatic and independence numbers, with value
zero on the empty graph. Mathlib's `SimpleGraph.chromaticNumber` takes values in
`ℕ∞`; on finite vertex types its `ENat.toNat` is the ordinary chromatic number.
We retain Mathlib's independent-set predicate and enumerate the stable finsets
for later finite linear programs.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- The number of vertices of a graph with finite vertex type.-/
def graphOrder (_G : SimpleGraph V) : ℕ := Fintype.card V

/-- The natural-valued chromatic number of a finite graph.-/
noncomputable def chromatic (G : SimpleGraph V) : ℕ :=
  ENat.toNat G.chromaticNumber

/-- The independence number of a finite graph.-/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  G.indepNum

/-- The finite family of stable vertex sets, including the empty set.-/
noncomputable def stableFinsets (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun s => G.IsIndepSet (s : Set V))

/--
@isnad1 id=eq.0h2v.s4.377054e010cf from=translated src=- shape=702d4805 vocab=c08ad30b
-/
@[simp] theorem graphOrder_eq (G : SimpleGraph V) : graphOrder G = Fintype.card V := rfl

omit [Fintype V] in
/--
@isnad1 id=eq.0h2v.s3.f68881a71392 from=translated src=- shape=49027224 vocab=78aca1b9
-/
theorem chromatic_eq_toNat (G : SimpleGraph V) :
    chromatic G = ENat.toNat G.chromaticNumber := rfl

/--
@isnad1 id=iff.0h3v.s4.69c4db659d1f from=translated src=- shape=bad5920e vocab=73bd0563
-/
theorem chromatic_le_iff_colorable (G : SimpleGraph V) (n : ℕ) :
    chromatic G ≤ n ↔ G.Colorable n := by
  rw [chromatic]
  have h : G.chromaticNumber ≠ ⊤ := by
    exact (G.colorable_of_fintype.chromaticNumber_le.trans_lt (ENat.natCast_lt_top _)).ne
  rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
  constructor
  · intro hc
    calc
      G.chromaticNumber = (ENat.toNat G.chromaticNumber : ℕ∞) := (ENat.natCast_toNat h).symm
      _ ≤ n := by exact_mod_cast hc
  · exact ENat.toNat_le_of_le_natCast

/--
@isnad1 id=colorabl.0h2v.s3.4c726bb9f897 from=translated src=- shape=bb2418e6 vocab=2d1cf359
-/
theorem colorable_chromatic (G : SimpleGraph V) : G.Colorable (chromatic G) := by
  simpa only [chromatic] using G.colorable_chromaticNumber_of_fintype

/--
@isnad1 id=le.0h2v.s4.c7c24602b484 from=translated src=- shape=702d4805 vocab=aea1f823
-/
theorem chromatic_le_card (G : SimpleGraph V) : chromatic G ≤ Fintype.card V :=
  (chromatic_le_iff_colorable G _).2 G.colorable_of_fintype

/--
@isnad1 id=iff.0h2v.s4.702f5d5bf5f1 from=translated src=- shape=52c56212 vocab=b1b8950a
-/
theorem chromatic_eq_zero_iff (G : SimpleGraph V) :
    chromatic G = 0 ↔ IsEmpty V := by
  constructor
  · intro h
    exact SimpleGraph.colorable_zero_iff.mp
      ((chromatic_le_iff_colorable G 0).mp (Nat.le_zero.mpr h))
  · intro h
    apply Nat.eq_zero_of_le_zero
    exact (chromatic_le_iff_colorable G 0).mpr
      (SimpleGraph.colorable_zero_iff.mpr h)

/--
@isnad1 id=le.1h3v.s4.1293c24230da from=translated src=- shape=43044cdd vocab=233c1a48
-/
theorem chromatic_mono {G H : SimpleGraph V} (h : G ≤ H) :
    chromatic G ≤ chromatic H := by
  apply (chromatic_le_iff_colorable G _).2
  exact (colorable_chromatic H).mono_left h

/--
@isnad1 id=iff.0h3v.s5.bcdd7d3fbd15 from=translated src=- shape=0e277bd5 vocab=1cb2a159
-/
@[simp] theorem mem_stableFinsets (G : SimpleGraph V) (s : Finset V) :
    s ∈ stableFinsets G ↔ G.IsIndepSet (s : Set V) := by
  classical
  simp [stableFinsets]

/--
@isnad1 id=le.1h3v.s5.6723a3a01729 from=translated src=- shape=f1b8e06d vocab=b8ce9ecc
-/
theorem stableFinsets_mono {G H : SimpleGraph V} (h : G ≤ H) :
    stableFinsets H ⊆ stableFinsets G := by
  intro s hs
  rw [mem_stableFinsets] at hs ⊢
  intro v hv w hw hvw hadj
  exact hs hv hw hvw (h hadj)

/--
@isnad1 id=mem.2h4v.s6.3f8c7eca199a from=translated src=- shape=f82547b6 vocab=63642e66
-/
theorem stableFinsets_downward (G : SimpleGraph V) {s t : Finset V}
    (hts : t ⊆ s) (hs : s ∈ stableFinsets G) : t ∈ stableFinsets G := by
  rw [mem_stableFinsets] at hs ⊢
  intro v hv w hw hvw
  exact hs (hts hv) (hts hw) hvw

/--
@isnad1 id=le.1h3v.s4.d4e771237e7a from=translated src=- shape=7a8af8b5 vocab=940c2b7d
-/
theorem stable_card_le_independenceNumber (G : SimpleGraph V) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) : s.card ≤ independenceNumber G := by
  exact hs.card_le_indepNum

omit [Fintype V] in
/--
@isnad1 id=ex.0h2v.s4.d2e7566b9069 from=translated src=- shape=37cf7d38 vocab=77110173
-/
theorem exists_stable_card_eq_independenceNumber (G : SimpleGraph V) :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ s.card = independenceNumber G := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  exact ⟨s, hs.isIndepSet, hs.card_eq⟩

/--
@isnad1 id=le.0h2v.s4.74fde33cd7c0 from=translated src=- shape=702d4805 vocab=09c4daab
-/
theorem independenceNumber_le_card (G : SimpleGraph V) :
    independenceNumber G ≤ Fintype.card V := by
  classical
  obtain ⟨s, _, hs⟩ := exists_stable_card_eq_independenceNumber G
  rw [← hs]
  simpa using Finset.card_le_card (Finset.subset_univ s)

/--
@isnad1 id=le.1h3v.s4.450774160f15 from=translated src=- shape=b8fc9364 vocab=2a7eecc7
-/
theorem independenceNumber_antitone {G H : SimpleGraph V} (h : G ≤ H) :
    independenceNumber H ≤ independenceNumber G := by
  obtain ⟨s, hs, hcard⟩ := exists_stable_card_eq_independenceNumber H
  rw [← hcard]
  exact stable_card_le_independenceNumber G
    ((mem_stableFinsets G s).mp
      (stableFinsets_mono h ((mem_stableFinsets H s).mpr hs)))

end HadwigerLean
