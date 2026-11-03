import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairFiniteDephase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms EvenFactorData.aut` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TwoEvenWord.aut` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TwoEvenWord.fixes_diagonalUnit` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TwoEvenWord.apply_diagonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_common_field_twoEven` (it only prints; the queue checks the axioms of every declaration). -/

/-! Common-field dephasing with explicit factors. The root and coefficient-map
assembly retains the resulting two even factors for downstream consumers. -/
noncomputable section
namespace AlbertLean.Generic.SourceVectorPairDephaseProvenance

open AlbertLean.Triality ExteriorSix CoordinateTensor StructuredCubic
open SourceEvenReflections SourceVectorPairDephase SourceEvenAutomorphism
open ResidualLedgerPower
open SourceCoefficientMap SourceVectorCoefficientMap FiniteQuadraticRoots
open AlbertLean.Generic.SourceVectorPairFiniteDephase

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- One lifted even source-automorphism factor together with its exact root
certificate.-/
structure EvenFactorData (L : Type u) [Field L] [CharZero L] where
  A : VCoord L
  B : VCoord L
  rho : L
  hA : nV A ≠ 0
  hB : nV B ≠ 0
  root : rho ^ 2 = nV A * nV B
  rho_ne : rho ≠ 0

/-- The genuine source automorphism represented by one retained factor.-/
def EvenFactorData.aut {L : Type u} [Field L] [CharZero L]
    (p : EvenFactorData L) : ResidualAction.SourceAut (K := L) :=
  evenSourceAut p.A p.B p.rho p.hA p.hB p.root p.rho_ne

/-- The ordered two-even word used by common-field dephasing.  `inner` acts
first, then `outer`.-/
structure TwoEvenWord (L : Type u) [Field L] [CharZero L] where
  inner : EvenFactorData L
  outer : EvenFactorData L

/-- The genuine composed source automorphism for the recorded word.-/
def TwoEvenWord.aut {L : Type u} [Field L] [CharZero L]
    (w : TwoEvenWord L) : ResidualAction.SourceAut (K := L) :=
  sourceAutComp w.outer.aut w.inner.aut

private theorem EvenFactorData.aut_diagonalUnit
    {L : Type u} [Field L] [CharZero L]
    (p : EvenFactorData L) (i : Fin 3) :
    p.aut.linear (diagonalUnit i) = diagonalUnit i := by
  exact evenSourceAut_diagonalUnit p.A p.B p.rho p.hA p.hB p.root p.rho_ne i

private theorem EvenFactorData.aut_apply_diagonal
    {L : Type u} [Field L] [CharZero L]
    (p : EvenFactorData L) (z : JCoord L) :
    ((p.aut.linear z).d1, (p.aut.linear z).d2, (p.aut.linear z).d3) =
      (z.d1, z.d2, z.d3) := by
  exact evenSourceAut_apply_diagonal p.A p.B p.rho p.hA p.hB p.root p.rho_ne z

/-- Both retained factors fix every labelled standard diagonal unit.-/
theorem TwoEvenWord.fixes_diagonalUnit
    {L : Type u} [Field L] [CharZero L]
    (w : TwoEvenWord L) (i : Fin 3) :
    w.aut.linear (diagonalUnit i) = diagonalUnit i := by
  change w.outer.aut.linear (w.inner.aut.linear (diagonalUnit i)) = diagonalUnit i
  rw [w.inner.aut_diagonalUnit, w.outer.aut_diagonalUnit]

/-- Both retained factors preserve all three labelled diagonal coordinates.-/
theorem TwoEvenWord.apply_diagonal
    {L : Type u} [Field L] [CharZero L]
    (w : TwoEvenWord L) (z : JCoord L) :
    ((w.aut.linear z).d1, (w.aut.linear z).d2, (w.aut.linear z).d3) =
      (z.d1, z.d2, z.d3) := by
  change ((w.outer.aut.linear (w.inner.aut.linear z)).d1,
    (w.outer.aut.linear (w.inner.aut.linear z)).d2,
    (w.outer.aut.linear (w.inner.aut.linear z)).d3) = (z.d1, z.d2, z.d3)
  exact (w.outer.aut_apply_diagonal (w.inner.aut.linear z)).trans
    (w.inner.aut_apply_diagonal z)

/-- The accepted common-field construction, with its two lifted even factors
retained rather than forgotten behind an existential source automorphism.-/
theorem exists_common_field_twoEven
    (x y : JCoord K) (ha : nV x.v ≠ 0)
    (hGram : 4 * nV x.v * nV y.v - (BV x.v y.v)^2 ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : CharZero L)
      (f : K →+* L) (sigma : L) (w : TwoEvenWord L),
      Function.Injective f ∧
      sigma ^ 2 = f ((BV x.v y.v)^2 - 4 * nV x.v * nV y.v) ∧
      sigma ≠ 0 ∧
      (w.aut.linear (mapSource f x)).v = targetFirst (f (nV x.v)) ∧
      (w.aut.linear (mapSource f y)).v =
        targetSecond (f (nV x.v)) (f (BV x.v y.v)) sigma := by
  classical
  let d := (BV x.v y.v)^2 - 4 * nV x.v * nV y.v
  have hd : d ≠ 0 := by
    intro hz
    apply hGram
    change (BV x.v y.v)^2 - 4 * nV x.v * nV y.v = 0 at hz
    linear_combination -hz
  obtain ⟨E⟩ := oneRootField_nonempty K d
  letI : CharZero E.Carrier := charZero_of_embedding E.embedding
  let v1 := mapV E.embedding x.v
  let v2 := mapV E.embedding y.v
  have haE : nV v1 ≠ 0 := by
    rw [show nV v1 = E.embedding (nV x.v) from mapV_nV E.embedding x.v]
    exact fun hz => ha (E.embedding.injective (by simpa using hz))
  have hgE : 4 * nV v1 * nV v2 - (BV v1 v2)^2 ≠ 0 := by
    have he : 4 * nV v1 * nV v2 - (BV v1 v2)^2 =
        E.embedding (4 * nV x.v * nV y.v - (BV x.v y.v)^2) := by
      simp only [v1, v2, mapV_nV, mapV_BV, map_sub, map_mul, map_pow,
        map_ofNat]
    rw [he]
    exact fun hz => hGram (E.embedding.injective (by simpa using hz))
  have hsE : E.root ^ 2 = (BV v1 v2)^2 - 4 * nV v1 * nV v2 := by
    simpa only [d, v1, v2, mapV_nV, mapV_BV, map_sub, map_mul, map_pow,
      map_ofNat] using E.root_sq
  obtain ⟨A1, B1, A2, B2, hA1, hB1, hA2, hB2, hv1, hv2⟩ :=
    exists_two_even_pairs_dephasing v1 v2 E.root haE hgE hsE
  let rad : Fin 2 → E.Carrier := ![nV A1 * nV B1, nV A2 * nV B2]
  obtain ⟨F⟩ := rootField_nonempty_of_fintype E.Carrier rad
  letI : CharZero F.Carrier := charZero_of_embedding F.embedding
  let j := F.embedding
  let f := F.embedding.comp E.embedding
  let a1 := mapV j A1
  let b1 := mapV j B1
  let a2 := mapV j A2
  let b2 := mapV j B2
  have nonzero (v : VCoord E.Carrier) (hv : nV v ≠ 0) :
      nV (mapV j v) ≠ 0 := by
    rw [mapV_nV]
    exact fun hz => hv (j.injective (by simpa using hz))
  have ha1 := nonzero A1 hA1
  have hb1 := nonzero B1 hB1
  have ha2 := nonzero A2 hA2
  have hb2 := nonzero B2 hB2
  have hr1 : (F.roots 0)^2 = nV a1 * nV b1 := by
    simpa [a1, b1, j, rad] using F.roots_sq 0
  have hr2 : (F.roots 1)^2 = nV a2 * nV b2 := by
    simpa [a2, b2, j, rad] using F.roots_sq 1
  have rho_nonzero (rho : F.Carrier) (A B : VCoord F.Carrier)
      (hA : nV A ≠ 0) (hB : nV B ≠ 0)
      (hr : rho^2 = nV A * nV B) : rho ≠ 0 := by
    intro hz
    have hzero : nV A * nV B = 0 := by rw [← hr, hz]; simp
    exact mul_ne_zero hA hB hzero
  have hs : (j E.root)^2 = f d := by
    simpa [j, f] using congrArg F.embedding E.root_sq
  have hs0 : j E.root ≠ 0 := by
    intro hz
    have he : f d = 0 := by rw [← hs, hz]; simp
    exact hd (f.injective (by simpa using he))
  have hv1F : evenV a2 b2 (evenV a1 b1 (mapSource f x).v) =
      targetFirst (f (nV x.v)) := by
    have H := congrArg (mapV j) hv1
    simp only [mapV_evenV, mapV_targetFirst, mapV_nV, mapV_comp] at H
    rw [mapSource_v]
    simpa [a1, b1, a2, b2, v1, f, j] using H
  have hv2F : evenV a2 b2 (evenV a1 b1 (mapSource f y).v) =
      targetSecond (f (nV x.v)) (f (BV x.v y.v)) (j E.root) := by
    have H := congrArg (mapV j) hv2
    simp only [mapV_evenV, mapV_targetSecond, mapV_nV, mapV_BV, mapV_comp] at H
    rw [mapSource_v]
    simpa [a1, b1, a2, b2, v1, v2, f, j] using H
  let inner : EvenFactorData F.Carrier :=
    ⟨a1, b1, F.roots 0, ha1, hb1, hr1,
      rho_nonzero _ _ _ ha1 hb1 hr1⟩
  let outer : EvenFactorData F.Carrier :=
    ⟨a2, b2, F.roots 1, ha2, hb2, hr2,
      rho_nonzero _ _ _ ha2 hb2 hr2⟩
  let w : TwoEvenWord F.Carrier := ⟨inner, outer⟩
  refine ⟨F.Carrier, inferInstance, inferInstance, f, j E.root, w,
    f.injective, hs, hs0, ?_, ?_⟩
  · change evenV a2 b2 (evenV a1 b1 (mapSource f x).v) = _
    exact hv1F
  · change evenV a2 b2 (evenV a1 b1 (mapSource f y).v) = _
    exact hv2F

end AlbertLean.Generic.SourceVectorPairDephaseProvenance
