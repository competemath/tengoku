/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.MultivariatePoisson
import Tengoku.Seed.Topology.ContinuousMap.Periodic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace SRG266.Lattice

open scoped FourierTransform

def integerTranslate {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (z : Fin n → ℤ) :
    C(EuclideanSpace ℝ (Fin n), ℂ) :=
  f.comp (ContinuousMap.addRight (intVectorToReal z))

/--
@isnad1 id=eq.0h4v.s8.bc9f5e880760 from=translated src=- shape=ae66429b vocab=6d830557
-/
@[simp]
theorem integerTranslate_apply {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (z : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    integerTranslate f z x = f (x + intVectorToReal z) :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.70b74011129a from=translated src=- shape=b7fed339 vocab=21d962f7
-/
@[simp]
theorem intVectorToReal_add {n : ℕ} (a b : Fin n → ℤ) :
    intVectorToReal (a + b) = intVectorToReal a + intVectorToReal b := by
  ext i
  simp [intVectorToReal]

/--
@isnad1 id=eq.0h1v.s6.53ec677960d8 from=translated src=- shape=dd0fe7eb vocab=faba4b4c
-/
@[simp]
theorem intVectorToReal_zero {n : ℕ} :
    intVectorToReal (0 : Fin n → ℤ) = 0 := by
  ext i
  simp [intVectorToReal]

abbrev LocallyNormallySummableIntegerTranslates {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n)),
    Summable fun z : Fin n → ℤ => ‖(integerTranslate f z).restrict K‖

def integerTranslateSum {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) :
    C(EuclideanSpace ℝ (Fin n), ℂ) :=
  ∑' z : Fin n → ℤ, integerTranslate f z

/--
@isnad1 id=eq.1h3v.s8.73f6eaf350ae from=translated src=- shape=0b8892f6 vocab=3d8860ae
-/
theorem integerTranslateSum_apply {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (x : EuclideanSpace ℝ (Fin n)) :
    integerTranslateSum f x =
      ∑' z : Fin n → ℤ, f (x + intVectorToReal z) := by
  let hs : Summable fun z : Fin n → ℤ => integerTranslate f z :=
    ContinuousMap.summable_of_locally_summable_norm hf
  exact (ContinuousMap.tsum_apply hs x).symm

/--
@isnad1 id=eq.1h4v.s8.d96c552805df from=translated src=- shape=8b52d483 vocab=f2e95306
-/
theorem integerTranslateSum_add_int {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (x : EuclideanSpace ℝ (Fin n)) (a : Fin n → ℤ) :
    integerTranslateSum f (x + intVectorToReal a) =
      integerTranslateSum f x := by
  rw [integerTranslateSum_apply f hf, integerTranslateSum_apply f hf]
  rw [← (Equiv.addRight a).tsum_eq
    (fun z : Fin n → ℤ => f (x + intVectorToReal z))]
  congr 1
  funext z
  simp only [Equiv.coe_addRight, intVectorToReal_add]
  congr 1
  abel

def euclideanToUnitTorus {n : ℕ} :
    C(EuclideanSpace ℝ (Fin n), UnitAddTorus (Fin n)) where
  toFun x := fun i => (x i : UnitAddCircle)
  continuous_toFun := by fun_prop

/--
@isnad1 id=isopenqu.0h1v.s7.15432d61691b from=translated src=- shape=76610196 vocab=aa1ee5a7
-/
theorem euclideanToUnitTorus_isOpenQuotientMap {n : ℕ} :
    IsOpenQuotientMap (@euclideanToUnitTorus n) := by
  let hPi : IsOpenQuotientMap
      (Pi.map fun _ : Fin n => ((↑) : ℝ → UnitAddCircle)) :=
    IsOpenQuotientMap.piMap fun _ =>
      QuotientAddGroup.isOpenQuotientMap_mk
  let hLp := (PiLp.homeomorph 2 fun _ : Fin n => ℝ).isOpenQuotientMap
  exact hPi.comp hLp

/--
@isnad1 id=ex.1h3v.s8.b317e7979d7c from=translated src=- shape=62817a01 vocab=9ca3cdcc
-/
theorem exists_intVector_add_eq_of_euclideanToUnitTorus_eq {n : ℕ}
    {x y : EuclideanSpace ℝ (Fin n)}
    (hxy : euclideanToUnitTorus x = euclideanToUnitTorus y) :
    ∃ z : Fin n → ℤ, x + intVectorToReal z = y := by
  have hcoord : ∀ i : Fin n, ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
    intro i
    have hi := congrFun hxy i
    change (↑(x i) : UnitAddCircle) = (↑(y i) : UnitAddCircle) at hi
    change (↑(y i - x i) : UnitAddCircle) = 0
    rw [QuotientAddGroup.mk_sub, hi, sub_self]
  choose z hz using fun i => (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hcoord i)
  refine ⟨z, ?_⟩
  ext i
  have hzi : (z i : ℝ) = y i - x i := by
    simpa using hz i
  simp only [PiLp.add_apply, intVectorToReal]
  rw [hzi]
  abel

def torusPeriodization {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f) :
    C(UnitAddTorus (Fin n), ℂ) :=
  euclideanToUnitTorus_isOpenQuotientMap.isQuotientMap.lift
    (integerTranslateSum f) fun x y hxy => by
      obtain ⟨z, hz⟩ :=
        exists_intVector_add_eq_of_euclideanToUnitTorus_eq hxy
      rw [← hz, integerTranslateSum_add_int f hf]

/--
@isnad1 id=summable.1h2v.s7.51089d7c7577 from=translated src=- shape=298905ad vocab=3e7e6853
-/
theorem summable_integerValues_of_locallyNormal {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f) :
    Summable fun z : Fin n → ℤ => f (intVectorToReal z) := by
  apply Summable.of_norm
  have h := hf ({0} : TopologicalSpace.Compacts
    (EuclideanSpace ℝ (Fin n)))
  convert h using 1
  funext z
  rw [ContinuousMap.norm_eq_iSup_norm]
  simp [integerTranslate]

end SRG266.Lattice
