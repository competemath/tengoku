import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorCoefficientMap
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairDephaseAut
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FiniteQuadraticRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms evenSourceAut_diagonalUnit` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_common_field_sourceAut` (it only prints; the queue checks the axioms of every declaration). -/

/-! Actual simultaneous normalization of the V slots of two source encoders
in one common extension. One orientation root, then two lift roots. All S/C
slots remain acted on by the genuine source automorphism. -/
noncomputable section
namespace AlbertLean.Generic.SourceVectorPairFiniteDephase
open AlbertLean.Triality ExteriorSix CoordinateTensor StructuredCubic
open SourceEvenReflections SourceVectorPairDephase SourceEvenAutomorphism
open ResidualLedgerPower
open SourceCoefficientMap SourceVectorCoefficientMap FiniteQuadraticRoots
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Each lifted even pair fixes every labelled standard idempotent, including
its zero V/S/C slots.
@isnad1 id=eq.4h5v.s9.6ff514b09a4b from=translated src=- shape=229dd418 vocab=c5db4ade
-/
theorem evenSourceAut_diagonalUnit (A B : VCoord K) (rho : K)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hr : rho^2 = nV A*nV B) (hr0 : rho ≠ 0) (i : Fin 3) :
    (evenSourceAut A B rho hA hB hr hr0).linear (diagonalUnit i) =
      diagonalUnit i := by
  change evenJEquiv A B rho hA hB hr hr0 (diagonalUnit i) = diagonalUnit i
  rw [evenJEquiv_apply]
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · exact (evenVEquiv A B hA hB).map_zero
  · exact (evenSEquiv A B rho hr hr0).map_zero
  · exact (evenCEquiv A B rho hr hr0).map_zero

private theorem sourceAutComp_fix_diagonalUnit
    (g2 g1 : ResidualAction.SourceAut (K := K))
    (h1 : ∀ i, g1.linear (diagonalUnit i) = diagonalUnit i)
    (h2 : ∀ i, g2.linear (diagonalUnit i) = diagonalUnit i) :
    ∀ i, (sourceAutComp g2 g1).linear (diagonalUnit i) = diagonalUnit i := by
  intro i
  change g2.linear (g1.linear (diagonalUnit i)) = diagonalUnit i
  rw [h1 i, h2 i]

private theorem sourceAutComp_even_diagonal
    (A1 B1 A2 B2 : VCoord K) (rho1 rho2 : K)
    (hA1 : nV A1 ≠ 0) (hB1 : nV B1 ≠ 0)
    (hr1 : rho1 ^ 2 = nV A1 * nV B1) (hrho1 : rho1 ≠ 0)
    (hA2 : nV A2 ≠ 0) (hB2 : nV B2 ≠ 0)
    (hr2 : rho2 ^ 2 = nV A2 * nV B2) (hrho2 : rho2 ≠ 0)
    (z : JCoord K) :
    let g1 := evenSourceAut A1 B1 rho1 hA1 hB1 hr1 hrho1
    let g2 := evenSourceAut A2 B2 rho2 hA2 hB2 hr2 hrho2
    (((sourceAutComp g2 g1).linear z).d1,
      ((sourceAutComp g2 g1).linear z).d2,
      ((sourceAutComp g2 g1).linear z).d3) = (z.d1, z.d2, z.d3) := by
  dsimp only
  have h1 := evenSourceAut_apply_diagonal A1 B1 rho1 hA1 hB1 hr1 hrho1 z
  have h2 := evenSourceAut_apply_diagonal A2 B2 rho2 hA2 hB2 hr2 hrho2
    ((evenSourceAut A1 B1 rho1 hA1 hB1 hr1 hrho1).linear z)
  exact h2.trans h1

private theorem exists_two_even_sourceAut
    (x y : JCoord K) (t1 t2 : VCoord K)
    (A1 B1 A2 B2 : VCoord K) (rho1 rho2 : K)
    (hA1 : nV A1 ≠ 0) (hB1 : nV B1 ≠ 0)
    (hr1 : rho1 ^ 2 = nV A1 * nV B1) (hrho1 : rho1 ≠ 0)
    (hA2 : nV A2 ≠ 0) (hB2 : nV B2 ≠ 0)
    (hr2 : rho2 ^ 2 = nV A2 * nV B2) (hrho2 : rho2 ≠ 0)
    (hx : evenV A2 B2 (evenV A1 B1 x.v) = t1)
    (hy : evenV A2 B2 (evenV A1 B1 y.v) = t2) :
    ∃ g : ResidualAction.SourceAut (K := K),
      (∀ i, g.linear (diagonalUnit i) = diagonalUnit i) ∧
      (∀ z : JCoord K,
        ((g.linear z).d1, (g.linear z).d2, (g.linear z).d3) =
          (z.d1, z.d2, z.d3)) ∧
      (g.linear x).v = t1 ∧ (g.linear y).v = t2 := by
  let g1 := evenSourceAut A1 B1 rho1 hA1 hB1 hr1 hrho1
  let g2 := evenSourceAut A2 B2 rho2 hA2 hB2 hr2 hrho2
  let g := sourceAutComp g2 g1
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · exact sourceAutComp_fix_diagonalUnit g2 g1
      (evenSourceAut_diagonalUnit _ _ _ _ _ _ _)
      (evenSourceAut_diagonalUnit _ _ _ _ _ _ _)
  · intro z
    exact sourceAutComp_even_diagonal A1 B1 A2 B2 rho1 rho2
      hA1 hB1 hr1 hrho1 hA2 hB2 hr2 hrho2 z
  · change evenV A2 B2 (evenV A1 B1 x.v) = t1
    exact hx
  · change evenV A2 B2 (evenV A1 B1 y.v) = t2
    exact hy

/-- No algebraic closure or universal square-root hypothesis; no ambient
raw-domain, density, or rational invariant assertion.
@isnad1 id=ex.2h3v.s11.d2c2c8c133a5 from=translated src=- shape=1912c518 vocab=64652817
-/
theorem exists_common_field_sourceAut
    (x y : JCoord K) (ha : nV x.v ≠ 0)
    (hGram : 4*nV x.v*nV y.v - (BV x.v y.v)^2 ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : CharZero L)
      (f : K →+* L) (sigma : L) (g : ResidualAction.SourceAut (K := L)),
      Function.Injective f ∧
      sigma ^ 2 = f ((BV x.v y.v)^2 - 4*nV x.v*nV y.v) ∧
      sigma ≠ 0 ∧
      (∀ i, g.linear (diagonalUnit i) = diagonalUnit i) ∧
      (∀ z : JCoord L,
        ((g.linear z).d1,(g.linear z).d2,(g.linear z).d3) = (z.d1,z.d2,z.d3)) ∧
      (g.linear (mapSource f x)).v = targetFirst (f (nV x.v)) ∧
      (g.linear (mapSource f y)).v =
        targetSecond (f (nV x.v)) (f (BV x.v y.v)) sigma := by
  classical
  let d := (BV x.v y.v)^2 - 4*nV x.v*nV y.v
  have hd : d ≠ 0 := by
    intro hz
    apply hGram
    change (BV x.v y.v)^2 - 4*nV x.v*nV y.v = 0 at hz
    linear_combination -hz
  obtain ⟨E⟩ := oneRootField_nonempty K d
  letI : CharZero E.Carrier := charZero_of_embedding E.embedding
  let v1 := mapV E.embedding x.v
  let v2 := mapV E.embedding y.v
  have haE : nV v1 ≠ 0 := by
    rw [show nV v1 = E.embedding (nV x.v) from mapV_nV E.embedding x.v]
    exact fun hz => ha (E.embedding.injective (by simpa using hz))
  have hgE : 4*nV v1*nV v2 - (BV v1 v2)^2 ≠ 0 := by
    have he : 4*nV v1*nV v2 - (BV v1 v2)^2 =
        E.embedding (4*nV x.v*nV y.v - (BV x.v y.v)^2) := by
      simp only [v1, v2, mapV_nV, mapV_BV, map_sub, map_mul, map_pow,
        map_ofNat]
    rw [he]
    exact fun hz => hGram (E.embedding.injective (by simpa using hz))
  have hsE : E.root ^ 2 = (BV v1 v2)^2 - 4*nV v1*nV v2 := by
    simpa only [d, v1, v2, mapV_nV, mapV_BV, map_sub, map_mul, map_pow,
      map_ofNat] using E.root_sq
  obtain ⟨A1,B1,A2,B2,hA1,hB1,hA2,hB2,hv1,hv2⟩ :=
    exists_two_even_pairs_dephasing v1 v2 E.root haE hgE hsE
  let rad : Fin 2 → E.Carrier := ![nV A1*nV B1, nV A2*nV B2]
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
  have hr1 : (F.roots 0)^2 = nV a1*nV b1 := by
    simpa [a1,b1,j,rad] using F.roots_sq 0
  have hr2 : (F.roots 1)^2 = nV a2*nV b2 := by
    simpa [a2,b2,j,rad] using F.roots_sq 1
  have rho_nonzero (rho : F.Carrier) (A B : VCoord F.Carrier)
      (hA : nV A ≠ 0) (hB : nV B ≠ 0)
      (hr : rho^2 = nV A*nV B) : rho ≠ 0 := by
    intro hz
    have hzero : nV A*nV B = 0 := by rw [← hr,hz]; simp
    exact mul_ne_zero hA hB hzero
  have hs : (j E.root)^2 = f d := by
    simpa [j,f] using congrArg F.embedding E.root_sq
  have hs0 : j E.root ≠ 0 := by
    intro hz
    have he : f d = 0 := by rw [← hs,hz]; simp
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
  obtain ⟨g, hdiag, hdiagAll, hxF, hyF⟩ := exists_two_even_sourceAut
    (mapSource f x) (mapSource f y)
    (targetFirst (f (nV x.v)))
    (targetSecond (f (nV x.v)) (f (BV x.v y.v)) (j E.root))
    a1 b1 a2 b2 (F.roots 0) (F.roots 1)
    ha1 hb1 hr1 (rho_nonzero _ _ _ ha1 hb1 hr1)
    ha2 hb2 hr2 (rho_nonzero _ _ _ ha2 hb2 hr2) hv1F hv2F
  refine ⟨F.Carrier,inferInstance,inferInstance,f,j E.root,g,
    f.injective,hs,hs0,hdiag,hdiagAll,hxF,hyF⟩

end AlbertLean.Generic.SourceVectorPairFiniteDephase
