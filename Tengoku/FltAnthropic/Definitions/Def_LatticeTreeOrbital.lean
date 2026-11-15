import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.RingTheory.DiscreteValuationRing.Basic
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.NumberTheory.Padics.PadicIntegers
import Tengoku.Seed.LinearAlgebra.Projectivization.Cardinality
import Tengoku.Seed.RingTheory.Ideal.Quotient.Defs
import Tengoku.Seed.Data.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

section Helpers

variable {α : Type*} [CommRing α]

/--
@isnad1 id=eq.0h3v.s7.d8ff66bfc2b6 from=translated src=- shape=827df3b1 vocab=220b56d7
-/
theorem mulVec_single_one (M : Matrix (Fin 2) (Fin 2) α) (j : Fin 2) :
    M *ᵥ (Pi.single j 1) = fun i => M i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

/--
@isnad1 id=eq.0h3v.s6.8b917baff465 from=translated src=- shape=f7a564c4 vocab=9c305d89
-/
theorem diagonal_mulVec (d v : Fin 2 → α) :
    Matrix.diagonal d *ᵥ v = fun i => d i * v i := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq]

end Helpers

variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]

def stdLattice : Submodule R (Fin 2 → K) where
  carrier := {v | ∀ i, IsLocalization.IsInteger R (v i)}
  add_mem' := fun hv hw i => IsLocalization.isInteger_add (hv i) (hw i)
  zero_mem' := fun _ => IsLocalization.isInteger_zero
  smul_mem' := fun r v hv i => by
    rw [Pi.smul_apply]
    exact IsLocalization.isInteger_smul (hv i)

/--
@isnad1 id=iff.0h3v.s8.07ea52176b4a from=translated src=- shape=76a2d648 vocab=e5d87596
-/
theorem mem_stdLattice {v : Fin 2 → K} :
    v ∈ stdLattice R K ↔ ∀ i, IsLocalization.IsInteger R (v i) := Iff.rfl

attribute [local simp] mem_stdLattice
/--
@isnad1 id=mem.0h3v.s8.cd7dc93d6d2e from=translated src=- shape=633d5a3b vocab=0b18eeb8
-/
theorem single_one_mem_stdLattice (j : Fin 2) :
    (Pi.single j 1 : Fin 2 → K) ∈ stdLattice R K := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same]
    exact IsLocalization.isInteger_one
  · rw [Pi.single_eq_of_ne h]
    exact IsLocalization.isInteger_zero

/--
@isnad1 id=eq.0h2v.s8.5e6838ed9140 from=translated src=- shape=fbaa1990 vocab=5ce46df6
-/
theorem stdLattice_eq_span :
    stdLattice R K = Submodule.span R (Set.range fun j => (Pi.single j 1 : Fin 2 → K)) := by
  apply le_antisymm
  · intro v hv
    choose w hw using hv
    have hv' : v = w 0 • (Pi.single 0 1 : Fin 2 → K) + w 1 • (Pi.single 1 1 : Fin 2 → K) := by
      funext i
      have h0 : algebraMap R K (w 0) = v 0 := hw 0
      have h1 : algebraMap R K (w 1) = v 1 := hw 1
      fin_cases i <;>
        simp [Algebra.smul_def, ← h0, ← h1]
    rw [hv']
    exact add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact single_one_mem_stdLattice R K j

/--
@isnad1 id=fg.0h2v.s6.bf5f24ecbe53 from=translated src=- shape=a9b668c9 vocab=e797170e
-/
theorem stdLattice_fg : (stdLattice R K).FG := by
  rw [Submodule.fg_def]
  exact ⟨Set.range fun j => (Pi.single j 1 : Fin 2 → K), Set.finite_range _,
    (stdLattice_eq_span R K).symm⟩

/--
@isnad1 id=eq.0h2v.s9.024361b450e2 from=translated src=- shape=9f5901fb vocab=8439307e
-/
theorem stdLattice_span_top :
    Submodule.span K ((stdLattice R K : Set (Fin 2 → K))) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span (by
    simpa only [Pi.basisFun_apply, SetLike.mem_coe] using single_one_mem_stdLattice R K j)

variable {R K}

def mulVecLinR (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (Fin 2 → K) →ₗ[R] (Fin 2 → K) where
  toFun v := (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' r v := by
    rw [RingHom.id_apply]
    exact Matrix.mulVec_smul _ r v

/--
@isnad1 id=eq.0h4v.s9.5524a1213039 from=translated src=- shape=6dd62328 vocab=adf887a6
-/
@[simp] theorem mulVecLinR_apply (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    mulVecLinR (R := R) g v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v := rfl

def latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) :=
  L.map (mulVecLinR g)

/--
@isnad1 id=iff.0h5v.s9.5af06af21648 from=translated src=- shape=e9b05dd8 vocab=5dc4e5cf
-/
theorem mem_latticeMap {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latticeMap g L ↔ ∃ w ∈ L, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = v :=
  Submodule.mem_map

/--
@isnad1 id=mem.1h5v.s9.2aeb94d6442f from=translated src=- shape=cd932daa vocab=5dc4e5cf
-/
theorem mulVec_mem_latticeMap {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {w : Fin 2 → K} (hw : w ∈ L) :
    (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ latticeMap g L :=
  ⟨w, hw, rfl⟩

/--
@isnad1 id=eq.0h4v.s9.904c446586c5 from=translated src=- shape=abfb2bdc vocab=7b62cd82
-/
theorem mulVecLinR_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    mulVecLinR (R := R) (g * h) = (mulVecLinR g).comp (mulVecLinR h) :=
  LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, mulVecLinR_apply, mulVecLinR_apply, mulVecLinR_apply,
      Matrix.mulVec_mulVec, Units.val_mul]

/--
@isnad1 id=eq.0h3v.s8.94e4f82919d2 from=translated src=- shape=6b6375b4 vocab=2e3c4557
-/
theorem latticeMap_one (L : Submodule R (Fin 2 → K)) : latticeMap 1 L = L := by
  have h : ∀ v : Fin 2 → K, mulVecLinR (R := R) 1 v = v := fun v => by
    rw [mulVecLinR_apply, Units.val_one, Matrix.one_mulVec]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [show mulVecLinR (R := R) 1 w = w from h w]
    exact hw
  · intro hv
    exact ⟨v, hv, h v⟩

attribute [local simp] latticeMap_one
/--
@isnad1 id=eq.0h5v.s8.83c4f43b4925 from=translated src=- shape=4255e859 vocab=a24ab0a4
-/
theorem latticeMap_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (g * h) L = latticeMap g (latticeMap h L) := by
  unfold latticeMap
  rw [mulVecLinR_mul, Submodule.map_comp]

/--
@isnad1 id=eq.0h4v.s8.b2feede5ea70 from=translated src=- shape=dbaa172b vocab=9f1274d6
-/
theorem latticeMap_inv_latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap g⁻¹ (latticeMap g L) = L := by
  rw [← latticeMap_mul, inv_mul_cancel, latticeMap_one]

/--
@isnad1 id=eq.0h4v.s8.196ccfbf3ab4 from=translated src=- shape=19ead20e vocab=9f1274d6
-/
theorem latticeMap_latticeMap_inv (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap g (latticeMap g⁻¹ L) = L := by
  rw [← latticeMap_mul, mul_inv_cancel, latticeMap_one]

/--
@isnad1 id=injectiv.0h3v.s7.1e045772b98a from=translated src=- shape=879ad0e8 vocab=a4758dd8
-/
theorem latticeMap_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (latticeMap (R := R) g) :=
  Function.LeftInverse.injective (latticeMap_inv_latticeMap g)

/--
@isnad1 id=le.1h5v.s9.0c46145d785d from=translated src=- shape=4069802e vocab=582c6db8
-/
theorem latticeMap_mono (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} (h : L ≤ L') : latticeMap g L ≤ latticeMap g L' :=
  Submodule.map_mono h

/--
@isnad1 id=le.1h5v.s9.57b6bf400bcb from=translated src=- shape=32f3ef4f vocab=582c6db8
-/
theorem le_of_latticeMap_le (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} (h : latticeMap g L ≤ latticeMap g L') : L ≤ L' := by
  have := latticeMap_mono g⁻¹ h
  rwa [latticeMap_inv_latticeMap, latticeMap_inv_latticeMap] at this

/--
@isnad1 id=iff.0h5v.s9.3d7ff0c6a6ac from=translated src=- shape=91fd300c vocab=b405a27e
-/
theorem latticeMap_lt_latticeMap_iff (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} : latticeMap g L < latticeMap g L' ↔ L < L' := by
  constructor
  · intro h
    exact lt_of_le_of_ne (le_of_latticeMap_le g h.1) (fun hEq => h.ne (by rw [hEq]))
  · intro h
    exact lt_of_le_of_ne (latticeMap_mono g h.1)
      (fun hEq => h.ne (latticeMap_injective g hEq))

def IsFullLattice (L : Submodule R (Fin 2 → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin 2 → K)) = ⊤

/--
@isnad1 id=isfullla.0h2v.s5.9773e685189d from=translated src=- shape=15afcf28 vocab=78bc3f84
-/
theorem isFullLattice_stdLattice : IsFullLattice (stdLattice R K) :=
  ⟨stdLattice_fg R K, stdLattice_span_top R K⟩

/--
@isnad1 id=isfullla.1h4v.s7.c4622af1123f from=translated src=- shape=477e6279 vocab=9753f395
-/
theorem IsFullLattice.map {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) : IsFullLattice (latticeMap g L) := by
  refine ⟨hL.1.map _, ?_⟩
  rw [eq_top_iff]
  intro v _

  have hv : v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [hv]
  have hw : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈
      Submodule.span K (L : Set (Fin 2 → K)) := hL.2 ▸ Submodule.mem_top
  refine Submodule.span_induction
    (p := fun w _ => (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈
      Submodule.span K ((latticeMap g L : Set (Fin 2 → K)))) ?_ ?_ ?_ ?_ hw
  · intro x hx
    exact Submodule.subset_span (mulVec_mem_latticeMap hx)
  · simp only [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    simp only [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    simp only [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hx

/--
@isnad1 id=isintege.1h5v.s9.c5bdd84c9d56 from=translated src=- shape=d2482a8a vocab=e726a5fa
-/
theorem isInteger_apply_of_mem_range {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (i j : Fin 2) : IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j) := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, (Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j h).symm⟩

/--
@isnad1 id=le.1h3v.s8.97c7360e9ce0 from=translated src=- shape=a97f9588 vocab=9efc0e2e
-/
theorem latticeMap_le_stdLattice_of_isInteger {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j)) :
    latticeMap g (stdLattice R K) ≤ stdLattice R K := by
  rintro _ ⟨w, hw, rfl⟩
  intro i
  show IsLocalization.IsInteger R (((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i)
  have hcoord : ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i =
      (g : Matrix (Fin 2) (Fin 2) K) i 0 * w 0 +
        (g : Matrix (Fin 2) (Fin 2) K) i 1 * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hcoord]
  exact IsLocalization.isInteger_add
    (IsLocalization.isInteger_mul (hg i 0) (hw 0))
    (IsLocalization.isInteger_mul (hg i 1) (hw 1))

def scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨(c : K) • 1, ((c⁻¹ : Kˣ) : K) • 1, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.mul_inv,
        one_smul], by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.inv_mul,
        one_smul]⟩

/--
@isnad1 id=eq.0h2v.s7.5678e79cdaf3 from=translated src=- shape=c5190f9b vocab=9420d356
-/
@[simp] theorem scalarGL_coe (c : Kˣ) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • 1 := rfl

/--
@isnad1 id=eq.0h3v.s7.ef93de66a88d from=translated src=- shape=73c23333 vocab=24ef880a
-/
theorem scalarGL_mulVec (c : Kˣ) (v : Fin 2 → K) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      (c : K) • v := by
  rw [scalarGL_coe, Matrix.smul_mulVec, Matrix.one_mulVec]

/--
@isnad1 id=eq.0h3v.s8.dbf2590bc836 from=translated src=- shape=9244596d vocab=eaca6648
-/
theorem scalarGL_mul (c c' : Kˣ) :
    (scalarGL (c * c') : Matrix.GeneralLinearGroup (Fin 2) K) = scalarGL c * scalarGL c' := by
  ext1
  rw [Units.val_mul, scalarGL_coe, scalarGL_coe, scalarGL_coe, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, Units.val_mul]

/--
@isnad1 id=eq.0h1v.s7.073431adeaa5 from=translated src=- shape=11d4ec53 vocab=d8d877e9
-/
theorem scalarGL_one : (scalarGL (1 : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K) = 1 := by
  ext1
  rw [scalarGL_coe, Units.val_one, one_smul, Units.val_one]

/--
@isnad1 id=eq.0h3v.s8.0d342a9ce621 from=translated src=- shape=df0058a6 vocab=eaca6648
-/
theorem scalarGL_mul_comm (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    scalarGL c * g = g * scalarGL c := by
  ext1
  rw [Units.val_mul, Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

/--
@isnad1 id=iff.0h5v.s9.6b626a38757f from=translated src=- shape=cb41128a vocab=06ceb4be
-/
theorem mem_latticeMap_scalarGL {c : Kˣ} {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latticeMap (scalarGL c) L ↔ ∃ w ∈ L, (c : K) • w = v := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (scalarGL_mulVec c w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, scalarGL_mulVec c w⟩

def diagSnd (x : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![1, (x : K)], Matrix.diagonal ![1, ((x⁻¹ : Kˣ) : K)], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

/--
@isnad1 id=eq.0h2v.s7.e7697516a475 from=translated src=- shape=ae0f0200 vocab=85ce2d02
-/
@[simp] theorem diagSnd_coe (x : Kˣ) :
    ((diagSnd x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![1, (x : K)] := rfl

/--
@isnad1 id=eq.0h3v.s7.fefdd7860d1b from=translated src=- shape=3cbfa5e2 vocab=620a78d2
-/
theorem diagSnd_mulVec (x : Kˣ) (v : Fin 2 → K) :
    ((diagSnd x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      ![v 0, (x : K) * v 1] := by
  rw [diagSnd_coe, diagonal_mulVec]
  funext i
  fin_cases i <;> simp

/--
@isnad1 id=iff.0h4v.s8.1f6d41237b40 from=translated src=- shape=bfc9bcb5 vocab=65457c6e
-/
theorem mem_latticeMap_diagSnd_stdLattice {x : Kˣ} {v : Fin 2 → K} :
    v ∈ latticeMap (diagSnd x) (stdLattice R K) ↔
      IsLocalization.IsInteger R (v 0) ∧
        ∃ w : K, IsLocalization.IsInteger R w ∧ (x : K) * w = v 1 := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [diagSnd_mulVec]
    exact ⟨by simpa using hw 0, w 1, hw 1, by simp⟩
  · rintro ⟨h0, w1, hw1, hw1'⟩
    refine ⟨![v 0, w1], ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using h0
      · simpa using hw1
    · rw [diagSnd_mulVec]
      funext i
      fin_cases i <;> simp [hw1']

/--
@isnad1 id=mem.0h3v.s8.8ad20ce64341 from=translated src=- shape=a979e714 vocab=42a63d0f
-/
theorem single_zero_one_mem_latticeMap_diagSnd (x : Kˣ) :
    (Pi.single 0 1 : Fin 2 → K) ∈ latticeMap (diagSnd x) (stdLattice R K) := by
  rw [mem_latticeMap_diagSnd_stdLattice]
  refine ⟨by rw [Pi.single_eq_same]; exact IsLocalization.isInteger_one,
    0, IsLocalization.isInteger_zero, ?_⟩
  rw [mul_zero, Pi.single_eq_of_ne]
  decide

def Homothetic (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ c : Kˣ, latticeMap (scalarGL c) L = L'

/--
@isnad1 id=homothet.0h3v.s6.cf0362b87723 from=translated src=- shape=af134649 vocab=73f1d965
-/
theorem Homothetic.refl (L : Submodule R (Fin 2 → K)) : Homothetic L L :=
  ⟨1, by rw [scalarGL_one, latticeMap_one]⟩

/--
@isnad1 id=homothet.1h4v.s7.4979318204a7 from=translated src=- shape=e77cf1b9 vocab=73f1d965
-/
theorem Homothetic.symm {L L' : Submodule R (Fin 2 → K)} (h : Homothetic L L') :
    Homothetic L' L := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c⁻¹, by
    rw [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]⟩

/--
@isnad1 id=homothet.2h5v.s8.8bae38d41df3 from=translated src=- shape=43b56523 vocab=73f1d965
-/
theorem Homothetic.trans {L L' L'' : Submodule R (Fin 2 → K)}
    (h : Homothetic L L') (h' : Homothetic L' L'') : Homothetic L L'' := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c' * c, by rw [scalarGL_mul, latticeMap_mul]⟩

/--
@isnad1 id=isfullla.2h4v.s7.fb10f76ef56b from=translated src=- shape=fe0ad3f4 vocab=d28baaa8
-/
theorem IsFullLattice.of_homothetic {L L' : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (h : Homothetic L L') : IsFullLattice L' := by
  obtain ⟨c, rfl⟩ := h
  exact hL.map _

variable (R K) in

def FullLattice : Type _ := {L : Submodule R (Fin 2 → K) // IsFullLattice L}

variable (R K) in

def homothetySetoid : Setoid (FullLattice R K) where
  r L L' := Homothetic L.1 L'.1
  iseqv := ⟨fun L => Homothetic.refl L.1, Homothetic.symm, Homothetic.trans⟩

variable (R K) in

def Vertex : Type _ := Quotient (homothetySetoid R K)

variable (R K) in

def Vertex.mk (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) : Vertex R K :=
  Quotient.mk (homothetySetoid R K) ⟨L, hL⟩

variable (R K) in

def stdVertex : Vertex R K := Vertex.mk R K (stdLattice R K) isFullLattice_stdLattice

/--
@isnad1 id=iff.2h4v.s7.f809881c8b30 from=translated src=- shape=e39ecd06 vocab=5054647d
-/
theorem Vertex.mk_eq_mk_iff {L L' : Submodule R (Fin 2 → K)} {hL : IsFullLattice L}
    {hL' : IsFullLattice L'} :
    Vertex.mk R K L hL = Vertex.mk R K L' hL' ↔ Homothetic L L' :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

def Vertex.act (g : Matrix.GeneralLinearGroup (Fin 2) K) : Vertex R K → Vertex R K :=
  Quotient.map (fun L => ⟨latticeMap g L.1, L.2.map g⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      exact ⟨c, by
        show latticeMap (scalarGL c) (latticeMap g L) = latticeMap g L'
        rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul, hc]⟩)

/--
@isnad1 id=eq.1h4v.s7.b77914945771 from=translated src=- shape=38d01321 vocab=5886a9e7
-/
@[simp] theorem Vertex.act_mk (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    Vertex.act g (Vertex.mk R K L hL) = Vertex.mk R K (latticeMap g L) (hL.map g) :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.f7dce0d6dbdd from=translated src=- shape=0f265979 vocab=951b8dec
-/
theorem Vertex.act_one (v : Vertex R K) : Vertex.act 1 v = v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeMap_one L.1))

/--
@isnad1 id=eq.0h5v.s8.0d29df9a9531 from=translated src=- shape=0fe7fe93 vocab=959f51cb
-/
theorem Vertex.act_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act (g * h) v = Vertex.act g (Vertex.act h v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeMap_mul g h L.1))

theorem eq_stdLattice_of_homothetic_of_le {L : Submodule R (Fin 2 → K)}
    (hhom : Homothetic (stdLattice R K) L) (hle : L ≤ stdLattice R K)
    {v : Fin 2 → K} (hv : v ∈ L) (hv0 : v 0 = 1) : L = stdLattice R K := by
  obtain ⟨c, rfl⟩ := hhom

  have hc : IsLocalization.IsInteger R ((c : K)) := by
    have h1 : (c : K) • (Pi.single 0 1 : Fin 2 → K) ∈
        latticeMap (scalarGL c) (stdLattice R K) :=
      mem_latticeMap_scalarGL.mpr ⟨Pi.single 0 1, single_one_mem_stdLattice R K 0, rfl⟩
    have h2 := hle h1 0
    rwa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2

  obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
  have hcw : (c : K) * w 0 = 1 := by
    have h3 := congrFun hwv 0
    rw [Pi.smul_apply, smul_eq_mul] at h3
    rw [h3, hv0]
  have hcinv : IsLocalization.IsInteger R (((c⁻¹ : Kˣ) : K)) := by
    have h4 : ((c⁻¹ : Kˣ) : K) = w 0 := by
      calc ((c⁻¹ : Kˣ) : K) = ((c⁻¹ : Kˣ) : K) * ((c : K) * w 0) := by rw [hcw, mul_one]
        _ = (((c⁻¹ : Kˣ) : K) * (c : K)) * w 0 := by rw [mul_assoc]
        _ = w 0 := by rw [Units.inv_mul, one_mul]
    rw [h4]
    exact hw 0

  apply le_antisymm hle
  intro u hu
  rw [mem_latticeMap_scalarGL]
  refine ⟨((c⁻¹ : Kˣ) : K) • u, fun i => ?_, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul]
    exact IsLocalization.isInteger_mul hcinv (hu i)
  · rw [smul_smul, Units.mul_inv, one_smul]

variable [IsFractionRing R K]

/--
@isnad1 id=iff.0h3v.s9.10382b117caa from=translated src=- shape=0a4fdd94 vocab=e9c2425e
-/
theorem latticeMap_stdLattice_eq_iff_mem_range (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    latticeMap g (stdLattice R K) = stdLattice R K ↔
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hinjM : Function.Injective
      ((algebraMap R K).mapMatrix : Matrix (Fin 2) (Fin 2) R →+* Matrix (Fin 2) (Fin 2) K) :=
    fun M N h => by
      ext i j
      apply hinj
      have := congrArg (fun X => X i j) h
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
  constructor
  · intro hfix

    have hcol : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j) := by
      intro i j
      have hj : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (Pi.single j 1) ∈ stdLattice R K :=
        hfix ▸ mulVec_mem_latticeMap (single_one_mem_stdLattice R K j)
      have := hj i
      rwa [mulVec_single_one] at this

    have hfix' : latticeMap g⁻¹ (stdLattice R K) = stdLattice R K := by
      conv_lhs => rw [← hfix, latticeMap_inv_latticeMap]
    have hcol' : ∀ i j,
        IsLocalization.IsInteger R (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) i j) := by
      intro i j
      have hj : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (Pi.single j 1) ∈ stdLattice R K :=
        hfix' ▸ mulVec_mem_latticeMap (single_one_mem_stdLattice R K j)
      have := hj i
      rwa [mulVec_single_one] at this

    choose a ha using fun p : Fin 2 × Fin 2 => hcol p.1 p.2
    choose b hb using fun p : Fin 2 × Fin 2 => hcol' p.1 p.2
    set A : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => a (i, j) with hA
    set B : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => b (i, j) with hB
    have hmapA : (algebraMap R K).mapMatrix A = (g : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact ha (i, j)
    have hmapB : (algebraMap R K).mapMatrix B =
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hb (i, j)
    have hAB : A * B = 1 := by
      apply hinjM
      rw [map_mul, map_one, hmapA, hmapB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hBA : B * A = 1 := by
      apply hinjM
      rw [map_mul, map_one, hmapA, hmapB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    exact ha (i, j)
  · intro hg
    apply le_antisymm (latticeMap_le_stdLattice_of_isInteger
      (isInteger_apply_of_mem_range hg))

    have hg' : g⁻¹ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range :=
      Subgroup.inv_mem _ hg
    have h1 : latticeMap g⁻¹ (stdLattice R K) ≤ stdLattice R K :=
      latticeMap_le_stdLattice_of_isInteger (isInteger_apply_of_mem_range hg')
    intro v hv
    have hv' : v ∈ latticeMap g (latticeMap g⁻¹ (stdLattice R K)) := by
      rw [latticeMap_latticeMap_inv]
      exact hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv'
    exact mulVec_mem_latticeMap (h1 hw)

/--
@isnad1 id=iff.0h3v.s9.fa2e9dcd017b from=translated src=- shape=a082d45d vocab=c6c9d89b
-/
theorem Vertex.act_stdVertex_eq_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Vertex.act g (stdVertex R K) = stdVertex R K ↔
      ∃ c : Kˣ, scalarGL c * g ∈
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (latticeMap_stdLattice_eq_iff_mem_range _).mp (by
      rw [latticeMap_mul]
      exact hc)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by
      rw [← latticeMap_mul]
      exact (latticeMap_stdLattice_eq_iff_mem_range _).mpr hc⟩

def unitOfNeZero {ϖ : R} (hϖ : ϖ ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap R K ϖ)
    (fun h => hϖ (IsFractionRing.injective R K (by rw [h, map_zero])))

/--
@isnad1 id=eq.1h3v.s7.ca8068e24a8e from=translated src=- shape=32181db1 vocab=fbddd6c2
-/
@[simp] theorem unitOfNeZero_coe {ϖ : R} (hϖ : ϖ ≠ 0) :
    ((unitOfNeZero (K := K) hϖ : Kˣ) : K) = algebraMap R K ϖ := rfl

/--
@isnad1 id=isunit.2h4v.s7.4160e77e30d1 from=translated src=- shape=89e447b4 vocab=250bcc0e
-/
theorem isUnit_of_algebraMap_mul_eq_one {ϖ : R} {w : K}
    (hw : IsLocalization.IsInteger R w) (h : algebraMap R K ϖ * w = 1) : IsUnit ϖ := by
  obtain ⟨r, rfl⟩ := hw
  rw [← map_mul] at h
  have h1 : ϖ * r = 1 := IsFractionRing.injective R K (by rw [h, map_one])
  exact ⟨⟨ϖ, r, h1, (mul_comm r ϖ).trans h1⟩, rfl⟩

/--
@isnad1 id=not.1h3v.s8.83c371f5186d from=translated src=- shape=98088c0c vocab=51d57fc9
-/
theorem single_one_one_notMem_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    (Pi.single 1 1 : Fin 2 → K) ∉
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  rw [mem_latticeMap_diagSnd_stdLattice]
  rintro ⟨-, w, hw, hweq⟩
  rw [unitOfNeZero_coe, Pi.single_eq_same] at hweq
  exact hϖ.not_isUnit (isUnit_of_algebraMap_mul_eq_one hw hweq)

/--
@isnad1 id=ne.1h3v.s7.bdabf5f518f3 from=translated src=- shape=d5994243 vocab=a01a5e90
-/
theorem latticeMap_diagSnd_ne_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≠
      stdLattice R K := fun h =>
  single_one_one_notMem_latticeMap_diagSnd hϖ (h ▸ single_one_mem_stdLattice R K 1)

/--
@isnad1 id=le.1h3v.s8.63934cddbd48 from=translated src=- shape=ec979bae vocab=30f3bdb9
-/
theorem latticeMap_diagSnd_le_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ stdLattice R K := by
  intro v hv
  rw [mem_latticeMap_diagSnd_stdLattice] at hv
  obtain ⟨h0, w, hw, hw'⟩ := hv
  intro i
  fin_cases i
  · exact h0
  · show IsLocalization.IsInteger R (v 1)
    rw [← hw', unitOfNeZero_coe]
    exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw

/--
@isnad1 id=lt.1h3v.s8.919d99333203 from=translated src=- shape=d5994243 vocab=02e374e5
-/
theorem latticeMap_diagSnd_lt_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      stdLattice R K :=
  lt_of_le_of_ne (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)
    (latticeMap_diagSnd_ne_stdLattice hϖ)

/--
@isnad1 id=not.1h3v.s6.089c63cf0440 from=translated src=- shape=0823e4f1 vocab=003fcc11
-/
theorem not_homothetic_stdLattice_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ Homothetic (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
  intro hhom
  exact latticeMap_diagSnd_ne_stdLattice hϖ
    (eq_stdLattice_of_homothetic_of_le hhom (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)
      (single_zero_one_mem_latticeMap_diagSnd _) (Pi.single_eq_same 0 1))

/--
@isnad1 id=ne.1h3v.s6.d95f513ad36b from=translated src=- shape=df53d1bd vocab=ae4debb7
-/
theorem stdVertex_ne_act_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdVertex R K) ≠
      stdVertex R K := by
  rw [stdVertex, Vertex.act_mk, Ne, Vertex.mk_eq_mk_iff]
  exact fun h => not_homothetic_stdLattice_diagSnd hϖ h.symm

def AdjacentLattice (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ (ϖ : R) (hϖ : Irreducible ϖ),
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) L < L' ∧ L' < L

/--
@isnad1 id=iff.1h4v.s8.caa6ad1fffe0 from=translated src=- shape=370e0a71 vocab=ec555a27
-/
theorem mem_latticeMap_scalarGL_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) {v : Fin 2 → K} :
    v ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ↔
      ∀ i, ∃ w : K, IsLocalization.IsInteger R w ∧ algebraMap R K ϖ * w = v i := by
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro i
    exact ⟨w i, hw i, by rw [Pi.smul_apply, smul_eq_mul, unitOfNeZero_coe]⟩
  · intro h
    choose w hw hw' using h
    refine ⟨w, hw, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, unitOfNeZero_coe]
    exact hw' i

/--
@isnad1 id=le.1h3v.s8.2397763dd732 from=translated src=- shape=9b694701 vocab=9101cd19
-/
theorem latticeMap_scalarGL_le_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≤
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  intro v hv
  rw [mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero] at hv
  rw [mem_latticeMap_diagSnd_stdLattice]
  obtain ⟨w0, hw0, hw0'⟩ := hv 0
  obtain ⟨w1, hw1, hw1'⟩ := hv 1
  refine ⟨?_, w1, hw1, by rw [unitOfNeZero_coe]; exact hw1'⟩
  rw [← hw0']
  exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw0

/--
@isnad1 id=ne.1h3v.s7.ee5653c5d469 from=translated src=- shape=9b694701 vocab=4964b83c
-/
theorem latticeMap_scalarGL_ne_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≠
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  intro h
  have he0 := single_zero_one_mem_latticeMap_diagSnd
    (R := R) (unitOfNeZero (K := K) hϖ.ne_zero)
  rw [← h, mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero] at he0
  obtain ⟨w, hw, hweq⟩ := he0 0
  rw [Pi.single_eq_same] at hweq
  exact hϖ.not_isUnit (isUnit_of_algebraMap_mul_eq_one hw hweq)

/--
@isnad1 id=adjacent.1h3v.s6.5470120733c3 from=translated src=- shape=734c6d05 vocab=a9f69989
-/
theorem adjacentLattice_stdLattice_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    AdjacentLattice (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) :=
  ⟨ϖ, hϖ,
    lt_of_le_of_ne (latticeMap_scalarGL_le_latticeMap_diagSnd hϖ)
      (latticeMap_scalarGL_ne_latticeMap_diagSnd hϖ),
    latticeMap_diagSnd_lt_stdLattice hϖ⟩

/--
@isnad1 id=adjacent.1h3v.s6.c44aa5f99a33 from=translated src=- shape=e3be064a vocab=a9f69989
-/
theorem adjacentLattice_diagSnd_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    AdjacentLattice
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))) := by
  have h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) :=
    lt_of_le_of_ne (latticeMap_scalarGL_le_latticeMap_diagSnd hϖ)
      (latticeMap_scalarGL_ne_latticeMap_diagSnd hϖ)
  have h₂ : latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      stdLattice R K := latticeMap_diagSnd_lt_stdLattice hϖ
  refine ⟨ϖ, hϖ, ?_, (latticeMap_lt_latticeMap_iff _).mpr h₂⟩
  have h₃ := (latticeMap_lt_latticeMap_iff
    (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))).mpr h₁
  rwa [← latticeMap_mul, ← scalarGL_mul_comm, latticeMap_mul] at h₃

/--
@isnad1 id=le.1h3v.s8.f6bf4f08ebc8 from=translated src=- shape=2224b1aa vocab=757e7db5
-/
theorem latticeMap_diagSnd_sq_le_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) ≤
      stdLattice R K :=
  le_trans (latticeMap_mono _ (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero))
    (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)

/--
@isnad1 id=not.1h3v.s6.01ba7cbb7ee9 from=translated src=- shape=b2373111 vocab=003fcc11
-/
theorem not_homothetic_stdLattice_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ Homothetic (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))) := by
  intro hhom

  have he0 : (Pi.single 0 1 : Fin 2 → K) ∈
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
    have h5 := mulVec_mem_latticeMap (g := diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
      (single_zero_one_mem_latticeMap_diagSnd (R := R)
        (unitOfNeZero (K := K) hϖ.ne_zero))
    have h6 : ((diagSnd (unitOfNeZero (K := K) hϖ.ne_zero) :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (Pi.single 0 1 : Fin 2 → K) = (Pi.single 0 1 : Fin 2 → K) := by
      rw [diagSnd_mulVec]
      funext i
      fin_cases i <;> simp
    rwa [h6] at h5

  have heq := eq_stdLattice_of_homothetic_of_le hhom
    (latticeMap_diagSnd_sq_le_stdLattice hϖ) he0 (Pi.single_eq_same 0 1)
  have he1 : (Pi.single 1 1 : Fin 2 → K) ∈
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
    rw [heq]
    exact single_one_mem_stdLattice R K 1
  exact single_one_one_notMem_latticeMap_diagSnd hϖ
    (latticeMap_mono _ (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero) he1)

/--
@isnad1 id=ne.1h3v.s6.52ccb5d212d9 from=translated src=- shape=4d4c7887 vocab=ae4debb7
-/
theorem stdVertex_ne_act_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdVertex R K)) ≠
      stdVertex R K := by
  rw [stdVertex, Vertex.act_mk, Vertex.act_mk, Ne, Vertex.mk_eq_mk_iff]
  exact fun h => not_homothetic_stdLattice_diagSnd_sq hϖ h.symm

end LT.LatticeTree

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

open Module
open scoped LinearAlgebra.Projectivization

section ResiduePlane

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/--
@isnad1 id=iff.1h3v.s8.f7991677e80c from=translated src=- shape=b39a66ac vocab=e10479c8
-/
theorem ne_bot_and_ne_top_iff_finrank_eq_one [FiniteDimensional k V]
    (hV : finrank k V = 2) (W : Submodule k V) :
    (W ≠ ⊥ ∧ W ≠ ⊤) ↔ finrank k W = 1 := by
  have hle : finrank k W ≤ 2 := hV ▸ W.finrank_le
  constructor
  · rintro ⟨hbot, htop⟩
    have h0 : finrank k W ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.mp h)
    have h2 : finrank k W ≠ 2 := fun h => htop (Submodule.eq_top_of_finrank_eq (h.trans hV.symm))
    omega
  · intro h1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, finrank_bot] at h1; exact absurd h1 (by norm_num)
    · rw [h, finrank_top, hV] at h1; exact absurd h1 (by norm_num)

set_option maxHeartbeats 800000 in

noncomputable def submoduleNeBotNeTopEquivProjectivization [FiniteDimensional k V]
    (hV : finrank k V = 2) :
    {W : Submodule k V // W ≠ ⊥ ∧ W ≠ ⊤} ≃ ℙ k V :=
  (Equiv.subtypeEquivRight (ne_bot_and_ne_top_iff_finrank_eq_one hV)).trans
    (Projectivization.equivSubmodule k V).symm

set_option maxHeartbeats 800000 in

/--
@isnad1 id=eq.1h2v.s7.516790d01d0c from=translated src=- shape=fe8e0b6e vocab=3965ea4a
-/
theorem card_submodule_ne_bot_ne_top_of_finrank_two [Finite k] [FiniteDimensional k V]
    (hV : finrank k V = 2) :
    Nat.card {W : Submodule k V // W ≠ ⊥ ∧ W ≠ ⊤} = Nat.card k + 1 :=
  (Nat.card_congr (submoduleNeBotNeTopEquivProjectivization hV)).trans
    (Projectivization.card_of_finrank_two k V hV)

end ResiduePlane

section NeighbourFamily

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

/--
@isnad1 id=isintege.1h3v.s6.23b9a434d708 from=translated src=- shape=47904575 vocab=06bf90d3
-/
theorem isInteger_neg {a : K} (ha : IsLocalization.IsInteger R a) :
    IsLocalization.IsInteger R (-a) := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨-a', map_neg _ _⟩

/--
@isnad1 id=isintege.2h4v.s6.79bcf751cdf0 from=translated src=- shape=e62869c2 vocab=0ff820d8
-/
theorem isInteger_sub {a b : K} (ha : IsLocalization.IsInteger R a)
    (hb : IsLocalization.IsInteger R b) : IsLocalization.IsInteger R (a - b) := by
  rw [sub_eq_add_neg]
  exact IsLocalization.isInteger_add ha (isInteger_neg hb)

variable (R K) in

def interLattice (ϖ c d : R) : Submodule R (Fin 2 → K) where
  carrier := {v | (∀ i, IsLocalization.IsInteger R (v i)) ∧
    ∃ w : K, IsLocalization.IsInteger R w ∧
      algebraMap R K d * v 0 - algebraMap R K c * v 1 = algebraMap R K ϖ * w}
  add_mem' := by
    rintro v u ⟨hv, wv, hwv, hv'⟩ ⟨hu, wu, hwu, hu'⟩
    refine ⟨fun i => IsLocalization.isInteger_add (hv i) (hu i),
      wv + wu, IsLocalization.isInteger_add hwv hwu, ?_⟩
    simp only [Pi.add_apply]
    linear_combination hv' + hu'
  zero_mem' := by
    refine ⟨fun _ => IsLocalization.isInteger_zero, 0, IsLocalization.isInteger_zero, ?_⟩
    simp
  smul_mem' := by
    rintro r v ⟨hv, w, hw, hv'⟩
    refine ⟨fun i => by rw [Pi.smul_apply]; exact IsLocalization.isInteger_smul (hv i),
      r • w, IsLocalization.isInteger_smul hw, ?_⟩
    simp only [Pi.smul_apply, Algebra.smul_def]
    linear_combination algebraMap R K r * hv'

/--
@isnad1 id=iff.0h6v.s9.f2ca33cb3887 from=translated src=- shape=72cc88b5 vocab=10f652ea
-/
theorem mem_interLattice {ϖ c d : R} {v : Fin 2 → K} :
    v ∈ interLattice R K ϖ c d ↔
      (∀ i, IsLocalization.IsInteger R (v i)) ∧
        ∃ w : K, IsLocalization.IsInteger R w ∧
          algebraMap R K d * v 0 - algebraMap R K c * v 1 = algebraMap R K ϖ * w :=
  Iff.rfl

/--
@isnad1 id=le.0h5v.s8.23881e5a0e63 from=translated src=- shape=d699f82e vocab=19090825
-/
theorem interLattice_le_stdLattice (ϖ c d : R) :
    interLattice R K ϖ c d ≤ stdLattice R K :=
  fun _ hv => hv.1

variable (R K) in

def vecPair (c d : R) : Fin 2 → K := ![algebraMap R K c, algebraMap R K d]

/--
@isnad1 id=eq.0h4v.s6.140042e5a5f3 from=translated src=- shape=4056fdb8 vocab=045bbb6b
-/
@[simp] theorem vecPair_zero (c d : R) : vecPair R K c d 0 = algebraMap R K c := rfl

/--
@isnad1 id=eq.0h4v.s6.fac56995d643 from=translated src=- shape=756119ba vocab=045bbb6b
-/
@[simp] theorem vecPair_one (c d : R) : vecPair R K c d 1 = algebraMap R K d := rfl

/--
@isnad1 id=mem.0h4v.s8.1b4c2b979cb6 from=translated src=- shape=c761094e vocab=7d118f17
-/
theorem vecPair_mem_stdLattice (c d : R) : vecPair R K c d ∈ stdLattice R K := by
  intro i
  fin_cases i
  · exact ⟨c, rfl⟩
  · exact ⟨d, rfl⟩

/--
@isnad1 id=mem.0h5v.s8.1d7f757935a9 from=translated src=- shape=7517ac4a vocab=405f9159
-/
theorem vecPair_mem_interLattice (ϖ c d : R) :
    vecPair R K c d ∈ interLattice R K ϖ c d := by
  refine ⟨vecPair_mem_stdLattice c d, 0, IsLocalization.isInteger_zero, ?_⟩
  simp [mul_comm]

variable [IsFractionRing R K]

/--
@isnad1 id=iff.0h4v.s7.a09f76b1e381 from=translated src=- shape=88a87192 vocab=f30f938c
-/
theorem exists_isInteger_eq_algebraMap_mul_iff_dvd {ϖ x : R} :
    (∃ w : K, IsLocalization.IsInteger R w ∧ algebraMap R K x = algebraMap R K ϖ * w) ↔
      ϖ ∣ x := by
  constructor
  · rintro ⟨w, ⟨w', rfl⟩, hw⟩
    rw [← map_mul] at hw
    exact ⟨w', IsFractionRing.injective R K hw⟩
  · rintro ⟨y, rfl⟩
    exact ⟨algebraMap R K y, ⟨y, rfl⟩, by rw [map_mul]⟩

/--
@isnad1 id=iff.0h7v.s8.7182b2fd1f1e from=translated src=- shape=98025a1e vocab=23f18c24
-/
theorem vecPair_mem_interLattice_iff_dvd {ϖ c d x y : R} :
    vecPair R K x y ∈ interLattice R K ϖ c d ↔ ϖ ∣ d * x - c * y := by
  rw [mem_interLattice]
  constructor
  · rintro ⟨-, w, hw, hweq⟩
    refine exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w, hw, ?_⟩
    rw [map_sub, map_mul, map_mul, ← vecPair_zero (K := K) x y, ← vecPair_one (K := K) x y]
    exact hweq
  · intro hdvd
    obtain ⟨w, hw, hweq⟩ := exists_isInteger_eq_algebraMap_mul_iff_dvd (K := K).mpr hdvd
    refine ⟨vecPair_mem_stdLattice x y, w, hw, ?_⟩
    rw [vecPair_zero, vecPair_one, ← hweq, map_sub, map_mul, map_mul]

/--
@isnad1 id=dvd.1h7v.s7.bc7fc92be7be from=translated src=- shape=33301650 vocab=b2c50b5a
-/
theorem dvd_of_interLattice_eq {ϖ c d c' d' : R}
    (h : interLattice R K ϖ c d = interLattice R K ϖ c' d') :
    ϖ ∣ d' * c - c' * d := by
  have hmem := vecPair_mem_interLattice (R := R) (K := K) ϖ c d
  rw [h, vecPair_mem_interLattice_iff_dvd] at hmem
  exact hmem

omit [IsFractionRing R K] in

/--
@isnad1 id=eq.1h5v.s7.d9fc4e0871fe from=translated src=- shape=73f19487 vocab=0a3b6db9
-/
theorem interLattice_one_eq_of_dvd_sub {ϖ a a' : R} (h : ϖ ∣ a - a') :
    interLattice R K ϖ 1 a = interLattice R K ϖ 1 a' := by
  have key : ∀ {b b' : R}, ϖ ∣ b - b' →
      interLattice R K ϖ 1 b ≤ interLattice R K ϖ 1 b' := by
    rintro b b' ⟨y, hy⟩ v ⟨hv, w, hw, hweq⟩
    obtain ⟨r, hr⟩ := hv 0
    refine ⟨hv, w - algebraMap R K (y * r), isInteger_sub hw ⟨y * r, rfl⟩, ?_⟩
    have hb : algebraMap R K b' =
        algebraMap R K b - algebraMap R K ϖ * algebraMap R K y := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hy)
    rw [hb]
    simp only [map_mul, map_one, one_mul] at hweq ⊢
    linear_combination hweq + algebraMap R K ϖ * algebraMap R K y * hr
  exact le_antisymm (key h) (key (dvd_sub_comm.mp h))

/--
@isnad1 id=le.1h5v.s8.ab2b45e039d0 from=translated src=- shape=bf550443 vocab=12fbebd9
-/
theorem latticeMap_scalarGL_le_interLattice {ϖ : R} (hϖ : ϖ ≠ 0) (c d : R) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤
      interLattice R K ϖ c d := by
  intro v hv
  rw [mem_latticeMap_scalarGL_stdLattice hϖ] at hv
  choose w hw hw' using hv
  refine ⟨fun i => by rw [← hw' i]; exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ (hw i),
    algebraMap R K d * w 0 - algebraMap R K c * w 1,
    isInteger_sub (IsLocalization.isInteger_mul ⟨d, rfl⟩ (hw 0))
      (IsLocalization.isInteger_mul ⟨c, rfl⟩ (hw 1)),
    by rw [← hw' 0, ← hw' 1]; ring⟩

/--
@isnad1 id=and.2h5v.s8.b86499ef7c35 from=translated src=- shape=22b152ff vocab=9166c2eb
-/
theorem dvd_of_vecPair_mem_latticeMap_scalarGL {ϖ : R} (hϖ : ϖ ≠ 0) {x y : R}
    (h : vecPair R K x y ∈
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K)) :
    ϖ ∣ x ∧ ϖ ∣ y := by
  rw [mem_latticeMap_scalarGL_stdLattice hϖ] at h
  obtain ⟨w0, hw0, hw0'⟩ := h 0
  obtain ⟨w1, hw1, hw1'⟩ := h 1
  rw [vecPair_zero] at hw0'
  rw [vecPair_one] at hw1'
  exact ⟨exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w0, hw0, hw0'.symm⟩,
    exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w1, hw1, hw1'.symm⟩⟩

/--
@isnad1 id=lt.2h5v.s8.a45a11e07fea from=translated src=- shape=e401a31c vocab=89dc4897
-/
theorem latticeMap_scalarGL_lt_interLattice {ϖ : R} (hϖ : ϖ ≠ 0) {c d : R}
    (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) <
      interLattice R K ϖ c d := by
  refine lt_of_le_of_ne (latticeMap_scalarGL_le_interLattice hϖ c d) (fun h => hcd ?_)
  exact dvd_of_vecPair_mem_latticeMap_scalarGL hϖ
    (h ▸ vecPair_mem_interLattice (R := R) (K := K) ϖ c d)

/--
@isnad1 id=lt.1h5v.s8.1dd950b080b9 from=translated src=- shape=3dea7809 vocab=925befca
-/
theorem interLattice_lt_stdLattice {ϖ : R} {c d : R} (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d)) :
    interLattice R K ϖ c d < stdLattice R K := by
  rw [lt_iff_le_and_ne]
  refine ⟨interLattice_le_stdLattice ϖ c d, fun h => ?_⟩
  rcases not_and_or.mp hcd with hc | hd
  ·
    have he : vecPair R K 0 1 ∈ stdLattice R K := vecPair_mem_stdLattice 0 1
    rw [← h, vecPair_mem_interLattice_iff_dvd] at he
    rw [mul_zero, mul_one, zero_sub] at he
    exact hc (dvd_neg.mp he)
  ·
    have he : vecPair R K 1 0 ∈ stdLattice R K := vecPair_mem_stdLattice 1 0
    rw [← h, vecPair_mem_interLattice_iff_dvd] at he
    rw [mul_zero, mul_one, sub_zero] at he
    exact hd he

variable (R K) in

noncomputable def neighborOfOption (ϖ : R) (x : Option (R ⧸ Ideal.span {ϖ})) :
    Submodule R (Fin 2 → K) :=
  x.elim (interLattice R K ϖ 0 1) (fun y => interLattice R K ϖ 1 y.out)

/--
@isnad1 id=and.1h4v.s9.9e15d484eb8f from=translated src=- shape=2c52e210 vocab=f0e12594
-/
theorem neighborOfOption_mem_interval {ϖ : R} (hϖ : Irreducible ϖ)
    (x : Option (R ⧸ Ideal.span {ϖ})) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
        neighborOfOption R K ϖ x ∧
      neighborOfOption R K ϖ x < stdLattice R K := by
  have hcd : ∀ y : R, ¬(ϖ ∣ (1 : R) ∧ ϖ ∣ y) := fun y h =>
    hϖ.not_isUnit (isUnit_of_dvd_one h.1)
  have hcd' : ¬(ϖ ∣ (0 : R) ∧ ϖ ∣ (1 : R)) := fun h =>
    hϖ.not_isUnit (isUnit_of_dvd_one h.2)
  cases x with
  | none => exact ⟨latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd',
      interLattice_lt_stdLattice hcd'⟩
  | some y => exact ⟨latticeMap_scalarGL_lt_interLattice hϖ.ne_zero (hcd _),
      interLattice_lt_stdLattice (hcd _)⟩

/--
@isnad1 id=injectiv.1h3v.s7.d4e7a343b38b from=translated src=- shape=ac648d11 vocab=23a61c07
-/
theorem neighborOfOption_injective {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Injective (neighborOfOption R K ϖ) := by
  have haff : ∀ (a : R), interLattice R K ϖ 0 1 ≠ interLattice R K ϖ 1 a := by
    intro a h
    have := dvd_of_interLattice_eq h
    rw [mul_zero, one_mul, zero_sub] at this
    exact hϖ.not_isUnit (isUnit_of_dvd_one (dvd_neg.mp this))
  rintro (_ | a) (_ | b) h
  · rfl
  · exact absurd h (haff _)
  · exact absurd h.symm (haff _)
  · have hd := dvd_of_interLattice_eq h
    rw [mul_one, one_mul] at hd
    rw [Option.some.injEq, ← Ideal.Quotient.mk_out a, ← Ideal.Quotient.mk_out b,
      Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr (dvd_sub_comm.mp hd)

/--
@isnad1 id=injectiv.1h3v.s10.14526f0c9f8b from=translated src=- shape=bd26d649 vocab=1755df33
-/
theorem neighborOfOption_injective_into_interval {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Injective (fun x : Option (R ⧸ Ideal.span {ϖ}) =>
      (⟨neighborOfOption R K ϖ x, neighborOfOption_mem_interval hϖ x⟩ :
        {L : Submodule R (Fin 2 → K) //
          latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < L ∧
            L < stdLattice R K})) :=
  fun _ _ h => neighborOfOption_injective hϖ (congrArg Subtype.val h)

/--
@isnad1 id=eq.0h2v.s6.eba19f586f6a from=translated src=- shape=84dd44f7 vocab=04c0231f
-/
theorem card_option_quotient (ϖ : R) [Finite (R ⧸ Ideal.span {ϖ})] :
    Nat.card (Option (R ⧸ Ideal.span {ϖ})) = Nat.card (R ⧸ Ideal.span {ϖ}) + 1 :=
  Finite.card_option

end NeighbourFamily

section Gates

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

/--
@isnad1 id=eq.0h3v.s7.34f6944479cc from=translated src=- shape=310424db vocab=38f191aa
-/
theorem interLattice_zero_zero (ϖ : R) : interLattice R K ϖ 0 0 = stdLattice R K := by
  refine le_antisymm (interLattice_le_stdLattice ϖ 0 0) (fun v hv => ?_)
  exact ⟨hv, 0, IsLocalization.isInteger_zero, by simp⟩

variable [IsFractionRing R K]

/--
@isnad1 id=eq.1h3v.s7.b91b9cc12498 from=translated src=- shape=1ac3c73f vocab=f110c6f9
-/
theorem interLattice_one_zero {ϖ : R} (hϖ : ϖ ≠ 0) :
    interLattice R K ϖ 1 0 =
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
  ext v
  rw [mem_interLattice, mem_latticeMap_diagSnd_stdLattice]
  constructor
  · rintro ⟨hv, w, hw, hweq⟩
    rw [map_zero, zero_mul, map_one, one_mul, zero_sub] at hweq
    refine ⟨hv 0, -w, isInteger_neg hw, ?_⟩
    rw [unitOfNeZero_coe, mul_neg, ← hweq, neg_neg]
  · rintro ⟨h0, w, hw, hweq⟩
    rw [unitOfNeZero_coe] at hweq
    refine ⟨fun i => ?_, -w, isInteger_neg hw, ?_⟩
    · fin_cases i
      · exact h0
      · exact hweq ▸ IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw
    · rw [map_zero, zero_mul, map_one, one_mul, zero_sub, ← hweq, mul_neg]

end Gates

section PadicGates

end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]

structure IntegralAut (R K : Type*) [CommRing R] [Field K] [Algebra R K] where

  toField : K ≃+* K

  toBase : R ≃+* R

  commutes : ∀ r : R, toField (algebraMap R K r) = algebraMap R K (toBase r)

namespace IntegralAut

variable (R K) in

def refl : IntegralAut R K where
  toField := RingEquiv.refl K
  toBase := RingEquiv.refl R
  commutes _ := rfl

/--
@isnad1 id=eq.0h2v.s6.f824f956d159 from=translated src=- shape=ff63d218 vocab=9296c6b4
-/
@[simp] theorem refl_toField : (refl R K).toField = RingEquiv.refl K := rfl

/--
@isnad1 id=eq.0h2v.s6.aa5e26e99efc from=translated src=- shape=581a77ed vocab=36cceff4
-/
@[simp] theorem refl_toBase : (refl R K).toBase = RingEquiv.refl R := rfl

def comp (σ τ : IntegralAut R K) : IntegralAut R K where
  toField := τ.toField.trans σ.toField
  toBase := τ.toBase.trans σ.toBase
  commutes r := by
    show σ.toField (τ.toField (algebraMap R K r)) = algebraMap R K (σ.toBase (τ.toBase r))
    rw [τ.commutes, σ.commutes]

/--
@isnad1 id=eq.0h5v.s9.afc10065ac40 from=translated src=- shape=9d913f28 vocab=d09b09fa
-/
@[simp] theorem comp_toField_apply (σ τ : IntegralAut R K) (x : K) :
    (σ.comp τ).toField x = σ.toField (τ.toField x) := rfl

/--
@isnad1 id=eq.0h5v.s8.5fc71c2d8129 from=translated src=- shape=811227da vocab=ac251c07
-/
@[simp] theorem comp_toBase_apply (σ τ : IntegralAut R K) (r : R) :
    (σ.comp τ).toBase r = σ.toBase (τ.toBase r) := rfl

/--
@isnad1 id=eq.0h4v.s9.454cf1fd7089 from=translated src=- shape=4d6d821a vocab=b512df9e
-/
theorem symm_commutes (σ : IntegralAut R K) (r : R) :
    σ.toField.symm (algebraMap R K r) = algebraMap R K (σ.toBase.symm r) := by
  apply σ.toField.injective
  rw [RingEquiv.apply_symm_apply, σ.commutes, RingEquiv.apply_symm_apply]

def symm (σ : IntegralAut R K) : IntegralAut R K where
  toField := σ.toField.symm
  toBase := σ.toBase.symm
  commutes := σ.symm_commutes

/--
@isnad1 id=eq.0h3v.s7.69621ded8d77 from=translated src=- shape=9776a766 vocab=97048fb6
-/
theorem symm_toField (σ : IntegralAut R K) : σ.symm.toField = σ.toField.symm := rfl

attribute [local simp] symm_toField
/--
@isnad1 id=eq.0h3v.s7.87f62ca6b02a from=translated src=- shape=18b0379e vocab=15245c74
-/
theorem symm_toBase (σ : IntegralAut R K) : σ.symm.toBase = σ.toBase.symm := rfl

attribute [local simp] symm_toBase
/--
@isnad1 id=isintege.1h4v.s7.d6ec1ec950a7 from=translated src=- shape=9caad31d vocab=f200a006
-/
theorem isInteger_map (σ : IntegralAut R K) {x : K}
    (hx : IsLocalization.IsInteger R x) : IsLocalization.IsInteger R (σ.toField x) := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨σ.toBase r, (σ.commutes r).symm⟩

def mapGL (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (σ.toField : K →+* K)

/--
@isnad1 id=eq.0h6v.s9.dfe005bc4a8d from=translated src=- shape=4a5a0139 vocab=c633e318
-/
theorem mapGL_apply (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (i j : Fin 2) :
    ((σ.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      σ.toField ((g : Matrix (Fin 2) (Fin 2) K) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j g

/--
@isnad1 id=eq.0h4v.s9.0a9933c767fc from=translated src=- shape=a174b1e7 vocab=3e6ec2c1
-/
theorem mapGL_coe (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ((σ.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((g : Matrix (Fin 2) (Fin 2) K)).map (σ.toField : K →+* K) := by
  ext i j
  rw [mapGL_apply, Matrix.map_apply]
  rfl

/--
@isnad1 id=eq.0h5v.s10.75302e7430d6 from=translated src=- shape=4eebbe81 vocab=4de99d83
-/
theorem mapGL_comp (σ τ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (σ.comp τ).mapGL g = σ.mapGL (τ.mapGL g) := by
  ext i j
  rw [mapGL_apply, mapGL_apply, mapGL_apply, comp_toField_apply]

/--
@isnad1 id=eq.0h3v.s9.a0d648bac3a0 from=translated src=- shape=e1f451e4 vocab=1fa4348a
-/
theorem mapGL_refl (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (refl R K).mapGL g = g := by
  ext i j
  rw [mapGL_apply]
  rfl

def unitMap (σ : IntegralAut R K) (c : Kˣ) : Kˣ where
  val := σ.toField c
  inv := σ.toField ↑c⁻¹
  val_inv := by rw [← map_mul, Units.mul_inv, map_one]
  inv_val := by rw [← map_mul, Units.inv_mul, map_one]

/--
@isnad1 id=eq.0h4v.s7.68f0bbd79fe3 from=translated src=- shape=996aae4a vocab=24c514f3
-/
@[simp] theorem unitMap_coe (σ : IntegralAut R K) (c : Kˣ) :
    ((σ.unitMap c : Kˣ) : K) = σ.toField c := rfl

end IntegralAut

attribute [local simp] IntegralAut.symm_toField IntegralAut.symm_toBase

def galVec (σ : IntegralAut R K) (v : Fin 2 → K) : Fin 2 → K :=
  fun i => σ.toField (v i)

/--
@isnad1 id=eq.0h5v.s7.500f0cc40441 from=translated src=- shape=8aa24c19 vocab=d18ac109
-/
@[simp] theorem galVec_apply (σ : IntegralAut R K) (v : Fin 2 → K) (i : Fin 2) :
    galVec σ v i = σ.toField (v i) := rfl

/--
@isnad1 id=eq.0h5v.s7.39c65bcd09e4 from=translated src=- shape=a2e1cc36 vocab=c0dc14e3
-/
theorem galVec_add (σ : IntegralAut R K) (v w : Fin 2 → K) :
    galVec σ (v + w) = galVec σ v + galVec σ w := by
  funext i
  simp [galVec, map_add]

/--
@isnad1 id=eq.0h3v.s7.f61199aa5dfb from=translated src=- shape=53bd8588 vocab=f01c8331
-/
theorem galVec_zero (σ : IntegralAut R K) : galVec σ (0 : Fin 2 → K) = 0 := by
  funext i
  simp [galVec]

/--
@isnad1 id=eq.0h5v.s8.1a6a8beb5a31 from=translated src=- shape=094a5e6c vocab=a53882b4
-/
theorem galVec_smul (σ : IntegralAut R K) (r : R) (v : Fin 2 → K) :
    galVec σ (r • v) = σ.toBase r • galVec σ v := by
  funext i
  rw [galVec_apply, Pi.smul_apply, Pi.smul_apply, galVec_apply, Algebra.smul_def,
    Algebra.smul_def, map_mul, σ.commutes]

/--
@isnad1 id=eq.0h5v.s8.7fb2e43d80bf from=translated src=- shape=9bdb81be vocab=135bd605
-/
theorem galVec_smul_field (σ : IntegralAut R K) (c : K) (v : Fin 2 → K) :
    galVec σ (c • v) = σ.toField c • galVec σ v := by
  funext i
  rw [galVec_apply, Pi.smul_apply, Pi.smul_apply, galVec_apply, smul_eq_mul, smul_eq_mul,
    map_mul]

/--
@isnad1 id=eq.0h5v.s6.18bfec21874b from=translated src=- shape=f75fd394 vocab=dc64e1d6
-/
theorem galVec_galVec (σ τ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ (galVec τ v) = galVec (σ.comp τ) v := rfl

/--
@isnad1 id=eq.0h3v.s5.4c76f0a1d6e1 from=translated src=- shape=c51fe512 vocab=535c4f1d
-/
@[simp] theorem galVec_refl (v : Fin 2 → K) : galVec (IntegralAut.refl R K) v = v := rfl

/--
@isnad1 id=eq.0h4v.s6.f75101e23bd2 from=translated src=- shape=85a65c45 vocab=41c41e8a
-/
theorem galVec_symm_galVec (σ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ.symm (galVec σ v) = v := by
  funext i
  simp [galVec]

attribute [local simp] galVec_symm_galVec
/--
@isnad1 id=eq.0h4v.s6.f1be7529fcfe from=translated src=- shape=75186faf vocab=41c41e8a
-/
theorem galVec_galVec_symm (σ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ (galVec σ.symm v) = v := by
  funext i
  simp [galVec]

attribute [local simp] galVec_galVec_symm
/--
@isnad1 id=eq.0h5v.s8.0fa50fd02839 from=translated src=- shape=03459843 vocab=9bffffd7
-/
theorem galVec_mulVec (σ : IntegralAut R K) (M : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 → K) :
    galVec σ (M *ᵥ v) = (M.map (σ.toField : K →+* K)) *ᵥ galVec σ v := by
  funext i
  rw [galVec_apply]
  exact RingHom.map_mulVec (σ.toField : K →+* K) M v i

def latticeGal (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) where
  carrier := galVec σ '' L
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, L.add_mem hv hw, galVec_add σ v w⟩
  zero_mem' := ⟨0, L.zero_mem, galVec_zero σ⟩
  smul_mem' := by
    rintro r _ ⟨w, hw, rfl⟩
    refine ⟨σ.toBase.symm r • w, L.smul_mem _ hw, ?_⟩
    rw [galVec_smul, RingEquiv.apply_symm_apply]

/--
@isnad1 id=iff.0h5v.s9.2be9679b19e2 from=translated src=- shape=b50d1c3e vocab=07b8986d
-/
theorem mem_latticeGal {σ : IntegralAut R K} {L : Submodule R (Fin 2 → K)}
    {v : Fin 2 → K} : v ∈ latticeGal σ L ↔ ∃ w ∈ L, galVec σ w = v := Iff.rfl

/--
@isnad1 id=mem.1h5v.s9.a533f4aec537 from=translated src=- shape=dc932f5e vocab=07b8986d
-/
theorem galVec_mem_latticeGal {σ : IntegralAut R K} {L : Submodule R (Fin 2 → K)}
    {w : Fin 2 → K} (hw : w ∈ L) : galVec σ w ∈ latticeGal σ L :=
  ⟨w, hw, rfl⟩

/--
@isnad1 id=eq.0h3v.s7.e4c37a447b94 from=translated src=- shape=547cd951 vocab=69846edf
-/
@[simp] theorem latticeGal_refl (L : Submodule R (Fin 2 → K)) :
    latticeGal (IntegralAut.refl R K) L = L := by
  ext v
  exact ⟨fun ⟨w, hw, h⟩ => h ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩

/--
@isnad1 id=eq.0h5v.s7.19aa5ed9c650 from=translated src=- shape=06c177e2 vocab=2603b0f7
-/
theorem latticeGal_comp (σ τ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    latticeGal (σ.comp τ) L = latticeGal σ (latticeGal τ L) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨galVec τ w, galVec_mem_latticeGal hw, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩

/--
@isnad1 id=eq.0h4v.s7.b23b7d8a86ed from=translated src=- shape=6d4e4d16 vocab=496b2476
-/
theorem latticeGal_symm_latticeGal (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : latticeGal σ.symm (latticeGal σ L) = L := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [galVec_symm_galVec]
  · intro hv
    exact ⟨galVec σ v, galVec_mem_latticeGal hv, galVec_symm_galVec σ v⟩

attribute [local simp] latticeGal_symm_latticeGal
/--
@isnad1 id=eq.0h4v.s7.23f690985c2f from=translated src=- shape=e42431f4 vocab=496b2476
-/
theorem latticeGal_latticeGal_symm (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : latticeGal σ (latticeGal σ.symm L) = L := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [galVec_galVec_symm]
  · intro hv
    exact ⟨galVec σ.symm v, galVec_mem_latticeGal hv, galVec_galVec_symm σ v⟩

attribute [local simp] latticeGal_latticeGal_symm
/--
@isnad1 id=injectiv.0h3v.s7.83c061b2b1f6 from=translated src=- shape=2a04cf2d vocab=6412aab2
-/
theorem latticeGal_injective (σ : IntegralAut R K) :
    Function.Injective (latticeGal (R := R) (K := K) σ) :=
  Function.LeftInverse.injective (latticeGal_symm_latticeGal σ)

/--
@isnad1 id=eq.0h4v.s8.79798a775ba0 from=translated src=- shape=9ca327d6 vocab=f31eb7b8
-/
theorem latticeGal_span (σ : IntegralAut R K) (s : Set (Fin 2 → K)) :
    latticeGal σ (Submodule.span R s) = Submodule.span R (galVec σ '' s) := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [galVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [galVec_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [galVec_smul]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact galVec_mem_latticeGal (Submodule.subset_span hx)

/--
@isnad1 id=eq.0h3v.s7.8bc15fdeddda from=translated src=- shape=aa802097 vocab=700ea05e
-/
theorem latticeGal_stdLattice (σ : IntegralAut R K) :
    latticeGal σ (stdLattice R K) = stdLattice R K := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    intro i
    exact σ.isInteger_map (hw i)
  · intro v hv
    refine ⟨galVec σ.symm v, fun i => ?_, galVec_galVec_symm σ v⟩
    exact σ.symm.isInteger_map (hv i)

/--
@isnad1 id=eq.0h5v.s9.dc2800bb0413 from=translated src=- shape=1a8ac4a8 vocab=444c2036
-/
theorem latticeGal_latticeMap (σ : IntegralAut R K)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    latticeGal σ (latticeMap g L) = latticeMap (σ.mapGL g) (latticeGal σ L) := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨galVec σ w, galVec_mem_latticeGal hw, ?_⟩
    simp only [mulVecLinR_apply]
    rw [galVec_mulVec, σ.mapGL_coe]
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ w, mulVec_mem_latticeMap hw, ?_⟩
    simp only [mulVecLinR_apply]
    rw [galVec_mulVec, σ.mapGL_coe]

/--
@isnad1 id=eq.0h4v.s9.40db99661d62 from=translated src=- shape=b06570b0 vocab=f5eeff18
-/
theorem latticeGal_latticeMap_stdLattice (σ : IntegralAut R K)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    latticeGal σ (latticeMap g (stdLattice R K)) =
      latticeMap (σ.mapGL g) (stdLattice R K) := by
  rw [latticeGal_latticeMap, latticeGal_stdLattice]

/--
@isnad1 id=eq.0h4v.s9.62e0ee750583 from=translated src=- shape=ad54c86c vocab=0d7da7c2
-/
theorem mapGL_scalarGL (σ : IntegralAut R K) (c : Kˣ) :
    σ.mapGL (scalarGL c) = scalarGL (σ.unitMap c) := by
  ext i j
  rw [σ.mapGL_apply, scalarGL_coe, scalarGL_coe, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, IntegralAut.unitMap_coe]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, map_zero]

/--
@isnad1 id=eq.0h5v.s7.3c9695a22966 from=translated src=- shape=1b4c727b vocab=8650740c
-/
theorem latticeGal_scalarGL (σ : IntegralAut R K) (c : Kˣ) (L : Submodule R (Fin 2 → K)) :
    latticeGal σ (latticeMap (scalarGL c) L) =
      latticeMap (scalarGL (σ.unitMap c)) (latticeGal σ L) := by
  rw [latticeGal_latticeMap, mapGL_scalarGL]

/--
@isnad1 id=isfullla.1h4v.s7.1115af1734bd from=translated src=- shape=16d5454d vocab=cb7b7031
-/
theorem IsFullLattice.gal {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (σ : IntegralAut R K) : IsFullLattice (latticeGal σ L) := by
  obtain ⟨hfg, hspan⟩ := hL
  constructor
  · obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp hfg
    exact Submodule.fg_def.mpr
      ⟨galVec σ '' S, hSfin.image _, by rw [← latticeGal_span, hS]⟩
  · rw [eq_top_iff]
    intro v _
    have hv : galVec σ.symm v ∈ Submodule.span K (L : Set (Fin 2 → K)) :=
      hspan ▸ Submodule.mem_top
    have hkey : ∀ w ∈ Submodule.span K (L : Set (Fin 2 → K)),
        galVec σ w ∈ Submodule.span K ((latticeGal σ L : Set (Fin 2 → K))) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (galVec_mem_latticeGal hx)
      | zero => rw [galVec_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [galVec_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [galVec_smul_field]; exact Submodule.smul_mem _ _ hx
    have := hkey _ hv
    rwa [galVec_galVec_symm] at this

def Vertex.galAct (σ : IntegralAut R K) : Vertex R K → Vertex R K :=
  Quotient.map (fun L => ⟨latticeGal σ L.1, L.2.gal σ⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      refine ⟨σ.unitMap c, ?_⟩
      show latticeMap _ (latticeGal σ L) = latticeGal σ L'
      rw [← latticeGal_scalarGL, hc])

/--
@isnad1 id=eq.1h4v.s7.e06d12f1286d from=translated src=- shape=6272d2dd vocab=7bef9889
-/
@[simp] theorem Vertex.galAct_mk (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K))
    (hL : IsFullLattice L) :
    Vertex.galAct σ (Vertex.mk R K L hL) = Vertex.mk R K (latticeGal σ L) (hL.gal σ) :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.816da4adcdc6 from=translated src=- shape=fee49212 vocab=29b0dffd
-/
theorem Vertex.galAct_stdVertex (σ : IntegralAut R K) :
    Vertex.galAct σ (stdVertex R K) = stdVertex R K := by
  rw [stdVertex, Vertex.galAct_mk, Vertex.mk_eq_mk_iff, latticeGal_stdLattice]
  exact Homothetic.refl _

def twistedLatticeMap (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : Submodule R (Fin 2 → K) :=
  latticeMap δ (latticeGal σ L)

/--
@isnad1 id=eq.0h7v.s9.68e211be6ed1 from=translated src=- shape=71d10e55 vocab=4bdeb937
-/
theorem twistedLatticeMap_twistedLatticeMap (δ δ' : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ τ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ' τ L) =
      twistedLatticeMap (δ * σ.mapGL δ') (σ.comp τ) L := by
  unfold twistedLatticeMap
  rw [latticeGal_latticeMap, ← latticeMap_mul, latticeGal_comp]

def normTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  δ * σ.mapGL δ

def normThree (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  δ * σ.mapGL δ * (σ.comp σ).mapGL δ

/--
@isnad1 id=eq.1h5v.s8.7ed4d39fef0f from=translated src=- shape=8808d429 vocab=f6b25167
-/
theorem twistedLatticeMap_two_of_orderTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : σ.comp σ = IntegralAut.refl R K)
    (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ σ L) = latticeMap (normTwo δ σ) L := by
  rw [twistedLatticeMap_twistedLatticeMap, hσ]
  unfold twistedLatticeMap normTwo
  rw [latticeGal_refl]

/--
@isnad1 id=eq.1h5v.s8.c2e05a222559 from=translated src=- shape=a0b84709 vocab=533c28fd
-/
theorem twistedLatticeMap_three_of_orderThree (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ σ (twistedLatticeMap δ σ L)) =
      latticeMap (normThree δ σ) L := by
  rw [twistedLatticeMap_twistedLatticeMap, twistedLatticeMap_twistedLatticeMap, hσ]
  unfold twistedLatticeMap normThree
  rw [latticeGal_refl]

/--
@isnad1 id=eq.2h5v.s8.d21c20600240 from=translated src=- shape=1ee8512d vocab=533c28fd
-/
theorem latticeMap_norm_eq_self_of_twisted_fixed (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    {L : Submodule R (Fin 2 → K)} (hL : twistedLatticeMap δ σ L = L) :
    latticeMap (normThree δ σ) L = L := by
  rw [← twistedLatticeMap_three_of_orderThree δ hσ, hL, hL, hL]

/--
@isnad1 id=ne.0h0v.s2.61a4074e6d33 from=translated src=- shape=2a2f4805 vocab=ee284f82
-/
theorem complex_I_ne_neg_I : Complex.I ≠ -Complex.I := by
  intro h
  have h2 : Complex.I.im = (-Complex.I).im := congrArg Complex.im h
  rw [Complex.neg_im, Complex.I_im] at h2
  norm_num at h2

def conjAut : IntegralAut ℂ ℂ where
  toField := starRingAut
  toBase := starRingAut
  commutes r := by
    simp [Algebra.algebraMap_self]

/--
@isnad1 id=ne.0h0v.s5.fe04dba300f1 from=translated src=- shape=9d9e24ef vocab=c91c04e7
-/
theorem conjAut_toField_ne_refl : conjAut.toField ≠ RingEquiv.refl ℂ := by
  intro h
  have hI : conjAut.toField Complex.I = Complex.I := by rw [h]; rfl
  have hI' : conjAut.toField Complex.I = -Complex.I := Complex.conj_I
  rw [hI'] at hI
  exact complex_I_ne_neg_I hI.symm

/--
@isnad1 id=ne.0h0v.s6.4a7b6ace3115 from=translated src=- shape=8ca357ba vocab=5c4c11f7
-/
theorem galVec_conjAut_ne : galVec conjAut ![1, Complex.I] ≠ ![1, Complex.I] := by
  intro h
  have h1 : conjAut.toField (![1, Complex.I] 1) = ![1, Complex.I] 1 := congrFun h 1
  have h2 : (![1, Complex.I] 1 : ℂ) = Complex.I := by simp
  rw [h2] at h1
  rw [show conjAut.toField Complex.I = -Complex.I from Complex.conj_I] at h1
  exact complex_I_ne_neg_I h1.symm

/--
@isnad1 id=ne.0h0v.s8.d84766c81ef0 from=translated src=- shape=7b15d31c vocab=2ce3b5dc
-/
theorem latticeGal_conj_line_ne :
    latticeGal conjAut (Submodule.span ℂ {![1, Complex.I]}) ≠
      Submodule.span ℂ {![1, Complex.I]} := by
  intro h

  have hmem : galVec conjAut ![1, Complex.I] ∈
      Submodule.span ℂ {![(1 : ℂ), Complex.I]} := by
    rw [← h]
    exact galVec_mem_latticeGal (Submodule.mem_span_singleton_self _)
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem

  have h0 : c * 1 = 1 := by
    have := congrFun hc 0
    simpa [galVec, conjAut, Pi.smul_apply, smul_eq_mul] using this

  have h1 : c * Complex.I = -Complex.I := by
    have := congrFun hc 1
    simpa [galVec, conjAut, Pi.smul_apply, smul_eq_mul, Complex.conj_I] using this
  rw [mul_one] at h0
  rw [h0, one_mul] at h1
  exact complex_I_ne_neg_I h1

/--
@isnad1 id=eq.0h0v.s5.fab030ee3afb from=translated src=- shape=5ed5d805 vocab=cdc67afe
-/
theorem conjAut_comp_conjAut : conjAut.comp conjAut = IntegralAut.refl ℂ ℂ := by
  unfold conjAut IntegralAut.comp IntegralAut.refl
  congr 1 <;>
  · ext x
    exact star_star x

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one IntegralAut.symm_toField IntegralAut.symm_toBase galVec_symm_galVec galVec_galVec_symm latticeGal_symm_latticeGal latticeGal_latticeGal_symm

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def IsFixedVertex (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) : Prop :=
  Vertex.act g v = v

def fixedVertexSet (g : Matrix.GeneralLinearGroup (Fin 2) K) : Set (Vertex R K) :=
  {v | IsFixedVertex g v}

/--
@isnad1 id=iff.0h4v.s6.4761ddbde0fb from=translated src=- shape=d3f3d15c vocab=6088723c
-/
theorem mem_fixedVertexSet {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {v : Vertex R K} : v ∈ fixedVertexSet (R := R) g ↔ Vertex.act g v = v :=
  Iff.rfl

attribute [local simp] mem_fixedVertexSet
variable (R) in

noncomputable def unitOrbitalCount (g : Matrix.GeneralLinearGroup (Fin 2) K) : ℕ :=
  Nat.card (fixedVertexSet (R := R) g)

/--
@isnad1 id=iff.1h4v.s7.3bf05fd4a97a from=translated src=- shape=10f712fd vocab=f16f60b3
-/
theorem isFixedVertex_mk_iff {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {hL : IsFullLattice L} :
    IsFixedVertex g (Vertex.mk R K L hL) ↔ Homothetic (latticeMap g L) L := by
  rw [IsFixedVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff]

/--
@isnad1 id=isfixedv.2h4v.s7.8898fe5abf3f from=translated src=- shape=14a314e3 vocab=094347e7
-/
theorem isFixedVertex_mk_of_latticeMap_eq {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {hL : IsFullLattice L}
    (h : latticeMap g L = L) : IsFixedVertex g (Vertex.mk R K L hL) :=
  isFixedVertex_mk_iff.mpr (by rw [h]; exact Homothetic.refl L)

/--
@isnad1 id=iff.0h5v.s9.5de31d90bec8 from=translated src=- shape=94e6b666 vocab=04972118
-/
theorem isFixedVertex_conj_iff (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (v : Vertex R K) :
    IsFixedVertex (h * g * h⁻¹) v ↔ IsFixedVertex g (Vertex.act h⁻¹ v) := by
  unfold IsFixedVertex
  rw [Vertex.act_mul, Vertex.act_mul]
  constructor
  · intro hfix
    have h2 := congrArg (Vertex.act h⁻¹) hfix
    rwa [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one] at h2
  · intro hfix
    rw [hfix, ← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

/--
@isnad1 id=eq.0h4v.s9.a4616adf1f18 from=translated src=- shape=c9fa171c vocab=13393f58
-/
theorem fixedVertexSet_conj (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    fixedVertexSet (R := R) (h * g * h⁻¹) = Vertex.act h '' fixedVertexSet (R := R) g := by
  ext v
  constructor
  · intro hv
    exact ⟨Vertex.act h⁻¹ v, (isFixedVertex_conj_iff g h v).mp hv, by
      rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]⟩
  · rintro ⟨w, hw, rfl⟩
    refine (isFixedVertex_conj_iff g h _).mpr ?_
    show IsFixedVertex g (Vertex.act h⁻¹ (Vertex.act h w))
    rwa [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

/--
@isnad1 id=eq.0h4v.s9.1879850b0fe0 from=translated src=- shape=6797908c vocab=1e36c019
-/
theorem unitOrbitalCount_conj (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    unitOrbitalCount R (h * g * h⁻¹) = unitOrbitalCount R g := by
  rw [unitOrbitalCount, unitOrbitalCount, fixedVertexSet_conj]
  have hinj : Function.Injective (Vertex.act (R := R) h) := fun v w hvw => by
    have h2 := congrArg (Vertex.act h⁻¹) hvw
    rwa [← Vertex.act_mul, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one,
      Vertex.act_one] at h2
  exact Nat.card_congr (Equiv.Set.image _ _ hinj).symm

/--
@isnad1 id=isfixedv.0h4v.s5.ca8ae650566e from=translated src=- shape=b59ebf2a vocab=fc22be99
-/
theorem isFixedVertex_scalarGL (c : Kˣ) (v : Vertex R K) :
    IsFixedVertex (scalarGL c) v := by
  induction v using Quotient.inductionOn with
  | h L =>
    show Vertex.act (scalarGL c) (Vertex.mk R K L.1 L.2) = Vertex.mk R K L.1 L.2
    rw [Vertex.act_mk, Vertex.mk_eq_mk_iff]
    exact Homothetic.symm ⟨c, rfl⟩

/--
@isnad1 id=eq.0h3v.s5.f8a335200891 from=translated src=- shape=93476e27 vocab=81fbe89d
-/
theorem fixedVertexSet_scalarGL (c : Kˣ) :
    fixedVertexSet (R := R) (scalarGL c) = Set.univ :=
  Set.eq_univ_of_forall (isFixedVertex_scalarGL c)

/--
@isnad1 id=not.1h4v.s6.3ede2b65d22b from=translated src=- shape=f6ce32d0 vocab=d3d31c5d
-/
theorem not_subsingleton_fixedVertexSet_scalarGL [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) (c : Kˣ) :
    ¬ (fixedVertexSet (R := R) (scalarGL c)).Subsingleton := by
  intro hsub
  exact stdVertex_ne_act_diagSnd (K := K) hϖ
    (hsub (isFixedVertex_scalarGL c _) (isFixedVertex_scalarGL c _)).symm

/--
@isnad1 id=isfixedv.1h3v.s9.6cc43a71c6f7 from=translated src=- shape=a62846f0 vocab=09cd212a
-/
theorem isFixedVertex_stdVertex_of_mem_range [IsFractionRing R K]
    {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    IsFixedVertex g (stdVertex R K) :=
  (Vertex.act_stdVertex_eq_iff g).mpr ⟨1, by rwa [scalarGL_one, one_mul]⟩

/--
@isnad1 id=nonempty.1h3v.s9.f31cf598a6bd from=translated src=- shape=e677a925 vocab=4adc6024
-/
theorem nonempty_fixedVertexSet_of_mem_range [IsFractionRing R K]
    {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    (fixedVertexSet (R := R) g).Nonempty :=
  ⟨stdVertex R K, isFixedVertex_stdVertex_of_mem_range hg⟩

section Engine

variable [IsFractionRing R K]

def mulVecPair (M : Matrix (Fin 2) (Fin 2) R) (c d : R) : Fin 2 → R :=
  M *ᵥ ![c, d]

/--
@isnad1 id=eq.0h4v.s7.eae623833a09 from=translated src=- shape=1a61ffc7 vocab=d9543853
-/
@[simp] theorem mulVecPair_zero (M : Matrix (Fin 2) (Fin 2) R) (c d : R) :
    mulVecPair M c d 0 = M 0 0 * c + M 0 1 * d := by
  simp [mulVecPair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h4v.s7.9ec1c16849de from=translated src=- shape=1a61ffc7 vocab=d9543853
-/
@[simp] theorem mulVecPair_one (M : Matrix (Fin 2) (Fin 2) R) (c d : R) :
    mulVecPair M c d 1 = M 1 0 * c + M 1 1 * d := by
  simp [mulVecPair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h6v.s7.e273d7737f5a from=translated src=- shape=c8454076 vocab=5d006397
-/
theorem mulVecPair_mul (M N : Matrix (Fin 2) (Fin 2) R) (c d : R) (i : Fin 2) :
    mulVecPair (M * N) c d i =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) i := by
  have h0 : mulVecPair (M * N) c d 0 =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) 0 := by
    simp only [mulVecPair_zero, mulVecPair_one, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h1 : mulVecPair (M * N) c d 1 =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) 1 := by
    simp only [mulVecPair_zero, mulVecPair_one, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  fin_cases i
  · exact h0
  · exact h1

omit [IsFractionRing R K] in

/--
@isnad1 id=eq.0h5v.s9.51dc476ea036 from=translated src=- shape=20083f49 vocab=888b5abd
-/
theorem map_coe_apply (M : Matrix.GeneralLinearGroup (Fin 2) R) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map (algebraMap R K) M :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) i j) :=
  Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j M

omit [IsFractionRing R K] in

/--
@isnad1 id=le.0h6v.s10.13522e8e5dbe from=translated src=- shape=5293d3d7 vocab=fd69bf24
-/
theorem latticeMap_map_interLattice_le (M : Matrix.GeneralLinearGroup (Fin 2) R)
    (ϖ c d : R) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) ≤
      interLattice R K ϖ (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
        (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) := by
  rintro _ ⟨w, hwmem, rfl⟩
  obtain ⟨hwint, t, ht, hweq⟩ := hwmem

  have hcoord : ∀ i : Fin 2,
      (mulVecLinR (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) M) w) i =
        algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) i 0) * w 0 +
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) i 1) * w 1 := by
    intro i
    rw [mulVecLinR_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [map_coe_apply, map_coe_apply]
  refine ⟨fun i => ?_, algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R).det) * t,
    IsLocalization.isInteger_mul ⟨_, rfl⟩ ht, ?_⟩
  · rw [hcoord i]
    exact IsLocalization.isInteger_add
      (IsLocalization.isInteger_mul ⟨_, rfl⟩ (hwint 0))
      (IsLocalization.isInteger_mul ⟨_, rfl⟩ (hwint 1))
  · rw [hcoord 0, hcoord 1, mulVecPair_zero, mulVecPair_one,
      Matrix.det_fin_two, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_sub,
      map_mul, map_mul]

    linear_combination
      (algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 0 0) *
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 1 1) -
        algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 0 1) *
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 1 0)) * hweq

omit [IsFractionRing R K] in

/--
@isnad1 id=eq.0h6v.s9.8338a5669e2f from=translated src=- shape=5293d3d7 vocab=779b32a3
-/
theorem latticeMap_map_interLattice (M : Matrix.GeneralLinearGroup (Fin 2) R)
    (ϖ c d : R) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) =
      interLattice R K ϖ (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
        (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) := by
  refine le_antisymm (latticeMap_map_interLattice_le M ϖ c d) ?_

  have hinv := latticeMap_map_interLattice_le (K := K) M⁻¹ ϖ
    (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
    (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1)

  have hcomp : ∀ i : Fin 2, mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) i = ![c, d] i := by
    intro i
    rw [← mulVecPair_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    show ((1 : Matrix (Fin 2) (Fin 2) R) *ᵥ ![c, d]) i = ![c, d] i
    rw [Matrix.one_mulVec]
  rw [show mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) 0 = c from hcomp 0,
    show mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) 1 = d from hcomp 1] at hinv

  have hmono := latticeMap_mono (R := R)
    (Matrix.GeneralLinearGroup.map (algebraMap R K) M) hinv
  rwa [← latticeMap_mul, ← map_mul, mul_inv_cancel, map_one, latticeMap_one] at hmono

end Engine

section Dichotomy

variable [IsFractionRing R K]

omit [IsFractionRing R K] in

/--
@isnad1 id=eq.2h7v.s7.ce15aa68256a from=translated src=- shape=84f108e8 vocab=0a3b6db9
-/
theorem interLattice_congr {ϖ c d c' d' : R} (hc : ϖ ∣ c - c') (hd : ϖ ∣ d - d') :
    interLattice R K ϖ c d = interLattice R K ϖ c' d' := by
  have key : ∀ {a b a' b' : R}, ϖ ∣ a - a' → ϖ ∣ b - b' →
      interLattice R K ϖ a b ≤ interLattice R K ϖ a' b' := by
    rintro a b a' b' ⟨x, hx⟩ ⟨y, hy⟩ v ⟨hv, w, hw, hweq⟩
    obtain ⟨r0, hr0⟩ := hv 0
    obtain ⟨r1, hr1⟩ := hv 1
    refine ⟨hv, w - algebraMap R K y * algebraMap R K r0 +
        algebraMap R K x * algebraMap R K r1,
      IsLocalization.isInteger_add
        (isInteger_sub hw (IsLocalization.isInteger_mul ⟨y, rfl⟩ ⟨r0, rfl⟩))
        (IsLocalization.isInteger_mul ⟨x, rfl⟩ ⟨r1, rfl⟩), ?_⟩
    have ha' : algebraMap R K a' =
        algebraMap R K a - algebraMap R K ϖ * algebraMap R K x := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hx)
    have hb' : algebraMap R K b' =
        algebraMap R K b - algebraMap R K ϖ * algebraMap R K y := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hy)
    rw [ha', hb']
    linear_combination hweq + algebraMap R K ϖ * algebraMap R K y * hr0 -
      algebraMap R K ϖ * algebraMap R K x * hr1
  exact le_antisymm (key hc hd) (key (dvd_sub_comm.mp hc) (dvd_sub_comm.mp hd))

omit [IsFractionRing R K] in

/--
@isnad1 id=eq.0h6v.s7.51ae2745c3df from=translated src=- shape=ba58b77f vocab=08994e6a
-/
theorem interLattice_unit_mul (ϖ : R) (u : Rˣ) (c d : R) :
    interLattice R K ϖ ((u : R) * c) ((u : R) * d) = interLattice R K ϖ c d := by
  have hu : algebraMap R K ((u⁻¹ : Rˣ) : R) * algebraMap R K (u : R) = 1 := by
    rw [← map_mul, ← map_one (algebraMap R K)]
    exact congrArg _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  ext v
  rw [mem_interLattice, mem_interLattice]
  constructor
  · rintro ⟨hv, w, hw, hweq⟩
    refine ⟨hv, algebraMap R K ((u⁻¹ : Rˣ) : R) * w,
      IsLocalization.isInteger_mul ⟨_, rfl⟩ hw, ?_⟩
    rw [map_mul, map_mul] at hweq
    calc algebraMap R K d * v 0 - algebraMap R K c * v 1
        = algebraMap R K ((u⁻¹ : Rˣ) : R) *
            (algebraMap R K (u : R) * algebraMap R K d * v 0 -
              algebraMap R K (u : R) * algebraMap R K c * v 1) := by
          rw [mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, hu, one_mul,
            one_mul]
      _ = algebraMap R K ϖ * (algebraMap R K ((u⁻¹ : Rˣ) : R) * w) := by
          rw [hweq]; ring
  · rintro ⟨hv, w, hw, hweq⟩
    refine ⟨hv, algebraMap R K (u : R) * w, IsLocalization.isInteger_mul ⟨_, rfl⟩ hw, ?_⟩
    rw [map_mul, map_mul]
    calc algebraMap R K (u : R) * algebraMap R K d * v 0 -
          algebraMap R K (u : R) * algebraMap R K c * v 1
        = algebraMap R K (u : R) * (algebraMap R K d * v 0 - algebraMap R K c * v 1) := by
          ring
      _ = algebraMap R K ϖ * (algebraMap R K (u : R) * w) := by rw [hweq]; ring

omit [IsFractionRing R K] in

/--
@isnad1 id=eq.2h7v.s9.bb31c9041d55 from=translated src=- shape=f435ec01 vocab=d4f7c142
-/
theorem latticeMap_map_interLattice_eq_self (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (lam : Rˣ)
    (h0 : ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 - (lam : R) * c)
    (h1 : ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 - (lam : R) * d) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) =
      interLattice R K ϖ c d := by
  rw [latticeMap_map_interLattice, interLattice_congr h0 h1, interLattice_unit_mul]

/--
@isnad1 id=dvd.1h6v.s9.1e7f4e00cfe9 from=translated src=- shape=b8f4b042 vocab=d87faf77
-/
theorem dvd_of_latticeMap_map_interLattice_eq_self
    (M : Matrix.GeneralLinearGroup (Fin 2) R) {ϖ c d : R}
    (h : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) = interLattice R K ϖ c d) :
    ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 := by
  rw [latticeMap_map_interLattice] at h
  exact dvd_of_interLattice_eq h

end Dichotomy

section Rigidity

variable [IsFractionRing R K]

omit [Algebra R K] [IsFractionRing R K] in

/--
@isnad1 id=or.2h4v.s6.f3c6d7e07427 from=translated src=- shape=3e640ba6 vocab=f4b6e72e
-/
theorem isUnit_or_isUnit_or_associated_of_mul_eq_sq [IsDomain R] {ϖ a b : R}
    (hϖ : Prime ϖ) (h : a * b = ϖ * ϖ) :
    IsUnit a ∨ IsUnit b ∨ ∃ u : R, IsUnit u ∧ a = ϖ * u := by
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  rcases hϖ.2.2 a b ⟨ϖ, by rw [← h]⟩ with ha | hb
  ·
    obtain ⟨a', rfl⟩ := ha
    have hcancel : a' * b = ϖ := by
      have h2 : ϖ * (a' * b) = ϖ * ϖ := by linear_combination h
      exact mul_left_cancel₀ hne h2
    rcases hϖ.2.2 a' b ⟨1, by rw [mul_one]; exact hcancel⟩ with ha' | hb'
    ·
      obtain ⟨a'', rfl⟩ := ha'
      have h3 : a'' * b = 1 := by
        have h2 : ϖ * (a'' * b) = ϖ * 1 := by rw [mul_one]; linear_combination hcancel
        exact mul_left_cancel₀ hne h2
      exact Or.inr (Or.inl (IsUnit.of_mul_eq_one_right a'' h3))
    ·
      obtain ⟨b', rfl⟩ := hb'
      have h3 : a' * b' = 1 := by
        have h2 : ϖ * (a' * b') = ϖ * 1 := by rw [mul_one]; linear_combination hcancel
        exact mul_left_cancel₀ hne h2
      exact Or.inr (Or.inr ⟨a', IsUnit.of_mul_eq_one b' h3, rfl⟩)
  ·
    obtain ⟨b', rfl⟩ := hb
    have hcancel : a * b' = ϖ := by
      have h2 : ϖ * (a * b') = ϖ * ϖ := by linear_combination h
      exact mul_left_cancel₀ hne h2
    rcases hϖ.2.2 a b' ⟨1, by rw [mul_one]; exact hcancel⟩ with ha' | hb''
    ·
      obtain ⟨a', rfl⟩ := ha'
      have h3 : a' * b' = 1 := by
        have h2 : ϖ * (a' * b') = ϖ * 1 := by rw [mul_one]; linear_combination hcancel
        exact mul_left_cancel₀ hne h2
      exact Or.inr (Or.inr ⟨a', IsUnit.of_mul_eq_one b' h3, rfl⟩)
    ·
      obtain ⟨b'', rfl⟩ := hb''
      have h3 : a * b'' = 1 := by
        have h2 : ϖ * (a * b'') = ϖ * 1 := by rw [mul_one]; linear_combination hcancel
        exact mul_left_cancel₀ hne h2
      exact Or.inl (IsUnit.of_mul_eq_one b'' h3)

omit [IsFractionRing R K] in

/--
@isnad1 id=eq.2h5v.s8.0f651faf8170 from=translated src=- shape=bf71db1f vocab=b21e1f33
-/
theorem latticeMap_scalarGL_eq_self_of_isUnit {e : Kˣ} {u : R} (hu : IsUnit u)
    (heu : (e : K) = algebraMap R K u) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL e) L = L := by
  obtain ⟨v, rfl⟩ := hu
  ext x
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [heu, algebraMap_smul]
    exact L.smul_mem _ hw
  · intro hx
    refine ⟨((v⁻¹ : Rˣ) : R) • x, L.smul_mem _ hx, ?_⟩
    rw [heu, algebraMap_smul, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul]

/--
@isnad1 id=isintege.3h5v.s9.3f1c9241f6cf from=translated src=- shape=f59da802 vocab=3f41af41
-/
theorem isInteger_mul_algebraMap_of_latticeMap_le {e : Kˣ} {ϖ : R} (hϖ : ϖ ≠ 0)
    {N : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ N)
    (hup : latticeMap (scalarGL e) N ≤ stdLattice R K) :
    IsLocalization.IsInteger R ((e : K) * algebraMap R K ϖ) := by
  have h1 : (algebraMap R K ϖ) • (Pi.single 0 1 : Fin 2 → K) ∈
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
    rw [mem_latticeMap_scalarGL]
    exact ⟨Pi.single 0 1, single_one_mem_stdLattice R K 0, by rw [unitOfNeZero_coe]⟩
  have h2 : (e : K) • ((algebraMap R K ϖ) • (Pi.single 0 1 : Fin 2 → K)) ∈
      latticeMap (scalarGL e) N := by
    rw [mem_latticeMap_scalarGL]
    exact ⟨_, hlow h1, rfl⟩
  have h3 := hup h2 0
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
  exact h3

/--
@isnad1 id=le.4h6v.s10.05fef1278e90 from=translated src=- shape=930e6723 vocab=518a1719
-/
theorem latticeMap_scalarGL_inv_le_of_mul_eq_unit {e : Kˣ} {ϖ : R} (hϖ : ϖ ≠ 0) {u : R}
    (hu : IsUnit u) (heu : (e : K) * algebraMap R K ϖ = algebraMap R K u)
    {N : Submodule R (Fin 2 → K)} (hN : N ≤ stdLattice R K) :
    latticeMap (scalarGL e⁻¹) N ≤
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
  obtain ⟨v, rfl⟩ := hu

  have hprod : (e : K) *
      (algebraMap R K ϖ * algebraMap R K ((v⁻¹ : Rˣ) : R)) = 1 := by
    rw [← mul_assoc, heu, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      map_one]
  have hinv : ((e⁻¹ : Kˣ) : K) =
      algebraMap R K ϖ * algebraMap R K ((v⁻¹ : Rˣ) : R) := by
    have h1 := congrArg (fun z => ((e⁻¹ : Kˣ) : K) * z) hprod
    simp only [mul_one] at h1
    rw [← mul_assoc, Units.inv_mul, one_mul] at h1
    exact h1.symm
  intro x hx
  rw [mem_latticeMap_scalarGL] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  rw [mem_latticeMap_scalarGL_stdLattice hϖ]
  intro i
  obtain ⟨wi, hwi⟩ := hN hw i
  refine ⟨algebraMap R K ((v⁻¹ : Rˣ) : R) * algebraMap R K wi,
    IsLocalization.isInteger_mul ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hinv, ← hwi]
  ring

theorem eq_of_homothetic_of_mem_interval [IsDomain R] {ϖ : R} (hϖ : Prime ϖ)
    {N N' : Submodule R (Fin 2 → K)}
    (hNlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < N)
    (hNup : N ≤ stdLattice R K)
    (hN'low : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < N')
    (hN'up : N' ≤ stdLattice R K)
    (h : Homothetic N N') : N = N' := by
  obtain ⟨e, he⟩ := h
  have hNinv : latticeMap (scalarGL e⁻¹) N' = N := by
    rw [← he, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one,
      latticeMap_one]

  obtain ⟨a, ha⟩ := isInteger_mul_algebraMap_of_latticeMap_le hϖ.ne_zero hNlow.le
    (he ▸ hN'up)
  obtain ⟨b, hb⟩ := isInteger_mul_algebraMap_of_latticeMap_le hϖ.ne_zero hN'low.le
    (hNinv ▸ hNup)
  have hϖK : algebraMap R K ϖ ≠ 0 := fun h0 =>
    hϖ.ne_zero (IsFractionRing.injective R K (h0.trans (map_zero _).symm))

  have hab : a * b = ϖ * ϖ := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ha, hb]
    calc (e : K) * algebraMap R K ϖ * (((e⁻¹ : Kˣ) : K) * algebraMap R K ϖ)
        = ((e : K) * ((e⁻¹ : Kˣ) : K)) * (algebraMap R K ϖ * algebraMap R K ϖ) := by
          ring
      _ = algebraMap R K ϖ * algebraMap R K ϖ := by rw [Units.mul_inv, one_mul]
  rcases isUnit_or_isUnit_or_associated_of_mul_eq_sq hϖ hab with hua | hub | ⟨u, hu, hau⟩
  ·
    exfalso
    have hkey := latticeMap_scalarGL_inv_le_of_mul_eq_unit (e := e) hϖ.ne_zero hua
      ha.symm hN'up
    rw [hNinv] at hkey
    exact absurd (le_antisymm hkey hNlow.le) hNlow.ne'
  ·
    exfalso
    have hkey := latticeMap_scalarGL_inv_le_of_mul_eq_unit (e := e⁻¹) hϖ.ne_zero hub
      hb.symm hNup
    rw [inv_inv, he] at hkey
    exact absurd (le_antisymm hkey hN'low.le) hN'low.ne'
  ·
    have heu : (e : K) = algebraMap R K u := by
      have h2 : (e : K) * algebraMap R K ϖ = algebraMap R K u * algebraMap R K ϖ := by
        rw [← ha, hau, map_mul]; ring
      exact mul_right_cancel₀ hϖK h2
    rw [← he, latticeMap_scalarGL_eq_self_of_isUnit hu heu]

/--
@isnad1 id=dvd.5h6v.s10.ec873bcab28c from=translated src=- shape=89c82fe8 vocab=c7a28c46
-/
theorem dvd_of_isFixedVertex_interLattice [IsDomain R]
    (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (hϖ : Prime ϖ) (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d))
    (hcd' : ¬(ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 ∧
      ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1))
    {hL : IsFullLattice (interLattice R K ϖ c d)}
    (h : IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
      (Vertex.mk R K (interLattice R K ϖ c d) hL)) :
    ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 := by
  rw [isFixedVertex_mk_iff, latticeMap_map_interLattice] at h
  have heq := eq_of_homothetic_of_mem_interval hϖ
    (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd')
    (interLattice_le_stdLattice _ _ _)
    (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd)
    (interLattice_le_stdLattice _ _ _) h
  exact dvd_of_interLattice_eq heq

/--
@isnad1 id=not.5h6v.s10.35283b9346c3 from=translated src=- shape=6f08f2be vocab=c7a28c46
-/
theorem not_isFixedVertex_interLattice_of_not_dvd [IsDomain R]
    (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (hϖ : Prime ϖ) (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d))
    (hcd' : ¬(ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 ∧
      ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1))
    (hnofix : ¬ ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1)
    {hL : IsFullLattice (interLattice R K ϖ c d)} :
    ¬ IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
      (Vertex.mk R K (interLattice R K ϖ c d) hL) :=
  fun h => hnofix (dvd_of_isFixedVertex_interLattice M hϖ hcd hcd' h)

end Rigidity

section FullLattice

variable [IsFractionRing R K]

/--
@isnad1 id=isfullla.3h4v.s9.3dce50e3d9b3 from=translated src=- shape=6d1d9ea5 vocab=dddbac56
-/
theorem isFullLattice_of_le_of_le [IsNoetherianRing R] {ϖ : R} (hϖ : ϖ ≠ 0)
    {N : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ N)
    (hup : N ≤ stdLattice R K) : IsFullLattice N := by
  constructor
  ·
    haveI : IsNoetherian R (stdLattice R K) :=
      isNoetherian_of_fg_of_noetherian _ (stdLattice_fg R K)
    have h1 : (Submodule.comap (stdLattice R K).subtype N).FG :=
      IsNoetherian.noetherian _
    have h2 := Submodule.FG.map (f := (stdLattice R K).subtype) h1
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hup] at h2
  ·
    have hfull : IsFullLattice
        (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K)) :=
      (isFullLattice_stdLattice).map _
    rw [eq_top_iff, ← hfull.2]
    exact Submodule.span_mono hlow

/--
@isnad1 id=isfullla.1h5v.s6.08dc44d0a3ee from=translated src=- shape=507a0e14 vocab=46a157ce
-/
theorem isFullLattice_interLattice [IsNoetherianRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    (c d : R) : IsFullLattice (interLattice R K ϖ c d) :=
  isFullLattice_of_le_of_le hϖ.ne_zero
    (latticeMap_scalarGL_le_interLattice hϖ.ne_zero c d)
    (interLattice_le_stdLattice ϖ c d)

end FullLattice

section PadicGates

noncomputable def gammaZero : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  ((Matrix.isUnit_iff_isUnit_det
      (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ_[2])).mpr
    (by rw [Matrix.det_fin_two_of]; norm_num)).unit

/--
@isnad1 id=eq.0h0v.s9.95f698ad14e0 from=translated src=- shape=72f6de37 vocab=e9be0934
-/
@[simp] theorem gammaZero_coe :
    (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) = !![0, -1; 1, -1] :=
  IsUnit.unit_spec _

noncomputable def transvectionGate : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  ((Matrix.isUnit_iff_isUnit_det
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ_[2])).mpr
    (by rw [Matrix.det_fin_two_of]; norm_num)).unit

/--
@isnad1 id=eq.0h0v.s9.eac74e26e28d from=translated src=- shape=13669dfb vocab=f0a4f89c
-/
@[simp] theorem transvectionGate_coe :
    (transvectionGate : Matrix (Fin 2) (Fin 2) ℤ_[2]) = !![1, 1; 0, 1] :=
  IsUnit.unit_spec _

/--
@isnad1 id=not.0h0v.s7.93fc554d133a from=translated src=- shape=6cf5eb34 vocab=8296ca59
-/
theorem not_two_dvd_one_padic : ¬ ((2 : ℤ_[2]) ∣ 1) := fun h =>
  (PadicInt.irreducible_p (p := 2)).not_isUnit (isUnit_of_dvd_one h)

end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one IntegralAut.symm_toField IntegralAut.symm_toBase galVec_symm_galVec galVec_galVec_symm latticeGal_symm_latticeGal latticeGal_latticeGal_symm mem_fixedVertexSet

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def Vertex.twistedAct (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (v : Vertex R K) : Vertex R K :=
  Vertex.act δ (Vertex.galAct σ v)

/--
@isnad1 id=eq.1h5v.s7.765e4c105993 from=translated src=- shape=8913bfe4 vocab=81581178
-/
theorem Vertex.twistedAct_mk (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    Vertex.twistedAct δ σ (Vertex.mk R K L hL) =
      Vertex.mk R K (twistedLatticeMap δ σ L) ((hL.gal σ).map δ) :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.88dbcb8f0e8c from=translated src=- shape=69670d68 vocab=22ed50cb
-/
theorem Vertex.galAct_refl (v : Vertex R K) :
    Vertex.galAct (IntegralAut.refl R K) v = v := by
  induction v using Quotient.inductionOn with
  | h L =>
    show Vertex.galAct (IntegralAut.refl R K) (Vertex.mk R K L.1 L.2) =
      Vertex.mk R K L.1 L.2
    rw [Vertex.galAct_mk, Vertex.mk_eq_mk_iff, latticeGal_refl]
    exact Homothetic.refl _

/--
@isnad1 id=eq.0h4v.s6.f05954bcc031 from=translated src=- shape=82818bad vocab=a5e2ab97
-/
theorem Vertex.twistedAct_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (v : Vertex R K) :
    Vertex.twistedAct δ (IntegralAut.refl R K) v = Vertex.act δ v := by
  rw [Vertex.twistedAct, Vertex.galAct_refl]

def IsTwistedFixedVertex (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (v : Vertex R K) : Prop :=
  Vertex.twistedAct δ σ v = v

def twistedFixedVertexSet (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : Set (Vertex R K) :=
  {v | IsTwistedFixedVertex δ σ v}

/--
@isnad1 id=iff.0h5v.s6.dd6048b9291c from=translated src=- shape=71b25e39 vocab=05482908
-/
theorem mem_twistedFixedVertexSet {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    {σ : IntegralAut R K} {v : Vertex R K} :
    v ∈ twistedFixedVertexSet δ σ ↔ Vertex.twistedAct δ σ v = v :=
  Iff.rfl

attribute [local simp] mem_twistedFixedVertexSet
noncomputable def twistedUnitOrbitalCount (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : ℕ :=
  Nat.card (twistedFixedVertexSet δ σ)

/--
@isnad1 id=eq.0h3v.s6.b2dad213ccdc from=translated src=- shape=c7bc86ac vocab=d05ceed1
-/
theorem twistedFixedVertexSet_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedFixedVertexSet δ (IntegralAut.refl R K) = fixedVertexSet (R := R) δ := by
  ext v
  rw [mem_twistedFixedVertexSet, mem_fixedVertexSet, Vertex.twistedAct_refl]

/--
@isnad1 id=eq.0h3v.s6.6da108796755 from=translated src=- shape=4c1a6426 vocab=101ddc64
-/
theorem twistedUnitOrbitalCount_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedUnitOrbitalCount δ (IntegralAut.refl R K) = unitOrbitalCount R δ := by
  rw [twistedUnitOrbitalCount, unitOrbitalCount, twistedFixedVertexSet_refl]

/--
@isnad1 id=istwiste.1h4v.s9.e921f020bc7e from=translated src=- shape=30626af2 vocab=11153517
-/
theorem isTwistedFixedVertex_stdVertex_of_mem_range [IsFractionRing R K]
    {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hδ : δ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (σ : IntegralAut R K) :
    IsTwistedFixedVertex δ σ (stdVertex R K) := by
  show Vertex.twistedAct δ σ (stdVertex R K) = stdVertex R K
  rw [Vertex.twistedAct, Vertex.galAct_stdVertex]
  exact isFixedVertex_stdVertex_of_mem_range hδ

/--
@isnad1 id=nonempty.1h4v.s9.f39f9d86ec64 from=translated src=- shape=1ff9b66a vocab=8f4b52f0
-/
theorem nonempty_twistedFixedVertexSet_of_mem_range [IsFractionRing R K]
    {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hδ : δ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (σ : IntegralAut R K) :
    (twistedFixedVertexSet δ σ).Nonempty :=
  ⟨stdVertex R K, isTwistedFixedVertex_stdVertex_of_mem_range hδ σ⟩

/--
@isnad1 id=eq.3h6v.s7.34476e20c38b from=translated src=- shape=40db504f vocab=4276314e
-/
theorem twistedFixedVertexSet_eq_singleton_of_subset_subsingleton
    {δ : Matrix.GeneralLinearGroup (Fin 2) K} {σ : IntegralAut R K}
    {s : Set (Vertex R K)} (hincl : twistedFixedVertexSet δ σ ⊆ s)
    (hsub : s.Subsingleton) {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedFixedVertexSet δ σ = {v₀} :=
  Set.eq_singleton_iff_unique_mem.mpr
    ⟨hv₀, fun _ hw => hsub (hincl hw) (hincl hv₀)⟩

/--
@isnad1 id=eq.3h6v.s7.cf792c11d652 from=translated src=- shape=3da4c4bb vocab=e6c987f3
-/
theorem twistedUnitOrbitalCount_eq_one_of_subset_subsingleton
    {δ : Matrix.GeneralLinearGroup (Fin 2) K} {σ : IntegralAut R K}
    {s : Set (Vertex R K)} (hincl : twistedFixedVertexSet δ σ ⊆ s)
    (hsub : s.Subsingleton) {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedUnitOrbitalCount δ σ = 1 := by
  rw [twistedUnitOrbitalCount,
    twistedFixedVertexSet_eq_singleton_of_subset_subsingleton hincl hsub hv₀,
    Nat.card_coe_set_eq, Set.ncard_singleton]

/--
@isnad1 id=eq.2h4v.s6.d1960a32cd85 from=translated src=- shape=a8906d44 vocab=b834b7b4
-/
theorem unitOrbitalCount_eq_one_of_subsingleton
    {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hsub : (fixedVertexSet (R := R) γ).Subsingleton) {w₀ : Vertex R K}
    (hw₀ : IsFixedVertex γ w₀) : unitOrbitalCount R γ = 1 := by
  have heq : fixedVertexSet (R := R) γ = {w₀} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hw₀, fun _ hx => hsub hx hw₀⟩
  rw [unitOrbitalCount, heq, Nat.card_coe_set_eq, Set.ncard_singleton]

section FundamentalLemma

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']

end FundamentalLemma

/--
@isnad1 id=le.0h6v.s9.8a0823ed8c4b from=translated src=- shape=6bde2819 vocab=536ae463
-/
theorem latticeGal_interLattice_le (σ : IntegralAut R K) (ϖ c d : R) :
    latticeGal σ (interLattice R K ϖ c d) ≤
      interLattice R K (σ.toBase ϖ) (σ.toBase c) (σ.toBase d) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwint, t, ht, hweq⟩ := hw
  refine ⟨fun i => σ.isInteger_map (hwint i), σ.toField t, σ.isInteger_map ht, ?_⟩
  have key : algebraMap R K (σ.toBase d) * σ.toField (w 0) -
      algebraMap R K (σ.toBase c) * σ.toField (w 1) =
        algebraMap R K (σ.toBase ϖ) * σ.toField t := by
    rw [← σ.commutes d, ← σ.commutes c, ← σ.commutes ϖ]
    calc σ.toField (algebraMap R K d) * σ.toField (w 0) -
          σ.toField (algebraMap R K c) * σ.toField (w 1)
        = σ.toField (algebraMap R K d * w 0 - algebraMap R K c * w 1) := by
          rw [map_sub, map_mul, map_mul]
      _ = σ.toField (algebraMap R K ϖ * t) := by rw [hweq]
      _ = σ.toField (algebraMap R K ϖ) * σ.toField t := by rw [map_mul]
  rw [galVec_apply, galVec_apply]
  exact key

/--
@isnad1 id=eq.0h6v.s9.b61481b882f6 from=translated src=- shape=6bde2819 vocab=ba6e9bf0
-/
theorem latticeGal_interLattice (σ : IntegralAut R K) (ϖ c d : R) :
    latticeGal σ (interLattice R K ϖ c d) =
      interLattice R K (σ.toBase ϖ) (σ.toBase c) (σ.toBase d) := by
  refine le_antisymm (latticeGal_interLattice_le σ ϖ c d) ?_
  have h := latticeGal_interLattice_le σ.symm (σ.toBase ϖ) (σ.toBase c) (σ.toBase d)
  rw [IntegralAut.symm_toBase, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply] at h
  intro v hv
  exact ⟨galVec σ.symm v, h (galVec_mem_latticeGal hv), galVec_galVec_symm σ v⟩

/--
@isnad1 id=eq.1h7v.s10.a4a622e83a76 from=translated src=- shape=44195f90 vocab=9f9efa8b
-/
theorem twistedLatticeMap_map_interLattice (δ : Matrix.GeneralLinearGroup (Fin 2) R)
    (σ : IntegralAut R K) {ϖ : R} (hϖ : σ.toBase ϖ = ϖ) (c d : R) :
    twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ
        (interLattice R K ϖ c d) =
      interLattice R K ϖ
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 0)
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 1) := by
  rw [twistedLatticeMap, latticeGal_interLattice, hϖ, latticeMap_map_interLattice]

/--
@isnad1 id=dvd.2h7v.s10.a5de48203a4e from=translated src=- shape=fa0e9122 vocab=f7eb8d39
-/
theorem dvd_of_twistedLatticeMap_map_interLattice_eq_self [IsFractionRing R K]
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (σ : IntegralAut R K) {ϖ : R}
    (hϖ : σ.toBase ϖ = ϖ) {c d : R}
    (h : twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ
        (interLattice R K ϖ c d) = interLattice R K ϖ c d) :
    ϖ ∣ d * mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 0 -
        c * mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 1 := by
  rw [twistedLatticeMap_map_interLattice δ σ hϖ c d] at h
  exact dvd_of_interLattice_eq h

end LT.LatticeTree
