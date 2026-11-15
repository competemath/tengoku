import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicLsXi
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Carrier

variable (n : ℕ) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev AdelicGL : Type _ := Matrix.GeneralLinearGroup (Fin n) (AdeleRing R K)

def globalPointsGL : Matrix.GeneralLinearGroup (Fin n) K →* AdelicGL n R K :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))

def centralScalarGL : (AdeleRing R K)ˣ →* AdelicGL n R K :=
  Matrix.GeneralLinearGroup.scalar (Fin n)

end Carrier

section Unipotent

variable {A : Type*} [CommRing A]

def upperUnipotent3 (x y z : A) : GL (Fin 3) A where
  val := !![1, x, z; 0, 1, y; 0, 0, 1]
  inv := !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals ring

/--
@isnad1 id=eq.0h4v.s8.c2c5b52403bb from=translated src=- shape=4549f7e4 vocab=975fc876
-/
@[simp] theorem upperUnipotent3_coe (x y z : A) :
    (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) A) = !![1, x, z; 0, 1, y; 0, 0, 1] := rfl

/--
@isnad1 id=eq.0h1v.s7.0168030c4258 from=translated src=- shape=b11d75da vocab=9a768d6f
-/
@[simp] theorem upperUnipotent3_zero : upperUnipotent3 (0 : A) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]

def radicalP21 (v : Fin 2 → A) : GL (Fin 3) A :=
  upperUnipotent3 0 (v 1) (v 0)

def radicalP12 (v : Fin 2 → A) : GL (Fin 3) A :=
  upperUnipotent3 (v 0) 0 (v 1)

/--
@isnad1 id=eq.0h1v.s7.ba4667c075fb from=translated src=- shape=0d218bd9 vocab=93beef77
-/
@[simp] theorem radicalP21_zero : radicalP21 (0 : Fin 2 → A) = 1 := by
  simp [radicalP21]

/--
@isnad1 id=eq.0h1v.s7.9372900cc189 from=translated src=- shape=0d218bd9 vocab=e77bf1a4
-/
@[simp] theorem radicalP12_zero : radicalP12 (0 : Fin 2 → A) = 1 := by
  simp [radicalP12]

/--
@isnad1 id=eq.0h2v.s9.89ff74b17899 from=translated src=- shape=857169cc vocab=2bc6c71d
-/
@[simp] theorem radicalP21_coe (v : Fin 2 → A) :
    (radicalP21 v : Matrix (Fin 3) (Fin 3) A) = !![1, 0, v 0; 0, 1, v 1; 0, 0, 1] := rfl

/--
@isnad1 id=eq.0h2v.s9.aabe2c58fe53 from=translated src=- shape=3fec6502 vocab=3a65d80b
-/
@[simp] theorem radicalP12_coe (v : Fin 2 → A) :
    (radicalP12 v : Matrix (Fin 3) (Fin 3) A) = !![1, v 0, v 1; 0, 1, 0; 0, 0, 1] := rfl

/--
@isnad1 id=eq.0h3v.s8.2cffe6c1bd38 from=translated src=- shape=13d2062e vocab=1f33d164
-/
theorem radicalP21_add (v w : Fin 2 → A) : radicalP21 (v + w) = radicalP21 v * radicalP21 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP21, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

/--
@isnad1 id=eq.0h3v.s8.ca42986ecd97 from=translated src=- shape=13d2062e vocab=fa7dc566
-/
theorem radicalP12_add (v w : Fin 2 → A) : radicalP12 (v + w) = radicalP12 v * radicalP12 w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP12, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

end Unipotent

section Iota

variable {A : Type*} [CommRing A]

def embedMat2 (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 3) (Fin 3) A :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

/--
@isnad1 id=eq.0h1v.s7.e00d4632df98 from=translated src=- shape=f3285880 vocab=3155d999
-/
theorem embedMat2_one : embedMat2 (1 : Matrix (Fin 2) (Fin 2) A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

/--
@isnad1 id=eq.0h3v.s7.5625e7dd80b7 from=translated src=- shape=7fa3b8c8 vocab=60b67aa6
-/
theorem embedMat2_mul (M N : Matrix (Fin 2) (Fin 2) A) :
    embedMat2 (M * N) = embedMat2 M * embedMat2 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def iotaGL : GL (Fin 2) A →* GL (Fin 3) A where
  toFun h :=
    { val := embedMat2 h
      inv := embedMat2 ((h⁻¹ : GL (Fin 2) A) : Matrix _ _ _)
      val_inv := by rw [← embedMat2_mul, Units.mul_inv, embedMat2_one]
      inv_val := by rw [← embedMat2_mul, Units.inv_mul, embedMat2_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact embedMat2_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact embedMat2_mul _ _)

/--
@isnad1 id=eq.0h2v.s9.f899f27359b7 from=translated src=- shape=9b0caa2e vocab=c305ab6d
-/
@[simp] theorem coe_iotaGL (h : GL (Fin 2) A) :
    ((iotaGL h : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = embedMat2 h := rfl

/--
@isnad1 id=eq.0h2v.s9.5aec6ccc4acb from=translated src=- shape=93d597e3 vocab=82ea1a89
-/
theorem iotaGL_unipotentGL2 (x : A) :
    iotaGL (AutomorphicForm.unipotentGL2 x) = upperUnipotent3 x 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, upperUnipotent3]

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def iota : AutomorphicForm.AdelicGL2 R K →* AdelicGL 3 R K :=
  iotaGL (A := AdeleRing R K)

abbrev MirabolicIndex : Type _ :=
  Quotient (QuotientGroup.rightRel (AutomorphicForm.unipotentGL2Hom (R := K)).range)

def mirabolicRep (c : MirabolicIndex K) : GL (Fin 2) K :=
  c.out

/--
@isnad1 id=eq.0h2v.s8.0b58cf083c37 from=translated src=- shape=f615f26f vocab=a35c2f00
-/
theorem mirabolicRep_spec (c : MirabolicIndex K) :
    Quotient.mk _ (mirabolicRep K c) = c :=
  c.out_eq

/--
@isnad1 id=eq.0h3v.s9.d117631ffc55 from=translated src=- shape=7718340c vocab=d840176a
-/
theorem mirabolic_mk_unipotent_mul (x : K) (g : GL (Fin 2) K) :
    (Quotient.mk _ (AutomorphicForm.unipotentGL2 x * g) : MirabolicIndex K) = Quotient.mk _ g := by
  have h : g * (AutomorphicForm.unipotentGL2 x * g)⁻¹ ∈
      (AutomorphicForm.unipotentGL2Hom (R := K)).range := by
    rw [_root_.mul_inv_rev, mul_inv_cancel_left]
    exact inv_mem ⟨Multiplicative.ofAdd x, rfl⟩
  exact Quotient.sound (QuotientGroup.rightRel_apply.mpr h)

end Iota

section LocalCompact

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/--
@isnad1 id=le.0h5v.s8.4451184f98ac from=translated src=- shape=6ffc4a1c vocab=90c7a914
-/
theorem valued_one_entry_le3 (i j : Fin 3) :
    Valued.v ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le

/--
@isnad1 id=le.2h8v.s9.49852aef699c from=translated src=- shape=75f99a3e vocab=8aa1a2ab
-/
theorem valued_mul_apply_le3 {C : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ C) (hb : ∀ l, Valued.v (b l j) ≤ 1) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ Valued.v (a i l) * 1 :=
          mul_le_mul_right (hb l) _
      _ = Valued.v (a i l) := mul_one _
      _ ≤ C := ha l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

def localMaximalCompact3 : Subgroup (GL (Fin 3) (v.adicCompletion K)) where
  carrier := {k | (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1) ∧
    (∀ i j, Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1)}
  one_mem' := by
    constructor
    · intro i j
      rw [Units.val_one]
      exact valued_one_entry_le3 R K v i j
    · intro i j
      rw [inv_one, Units.val_one]
      exact valued_one_entry_le3 R K v i j
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    constructor
    · intro i j
      rw [Units.val_mul]
      exact valued_mul_apply_le3 R K v (fun l => ha i l) (fun l => hb l j)
    · intro i j
      rw [_root_.mul_inv_rev, Units.val_mul]
      exact valued_mul_apply_le3 R K v (fun l => hb' i l) (fun l => ha' l j)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨ha', ?_⟩
    intro i j
    rw [inv_inv]
    exact ha i j

/--
@isnad1 id=iff.0h4v.s10.ed17c9abd4a8 from=translated src=- shape=cafa9f4d vocab=916bba7a
-/
theorem mem_localMaximalCompact3_iff {k : GL (Fin 3) (v.adicCompletion K)} :
    k ∈ localMaximalCompact3 R K v ↔
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1) ∧
      (∀ i j, Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ 1) :=
  Iff.rfl

/--
@isnad1 id=not.1h6v.s10.8c2832c94e82 from=translated src=- shape=9b9ecc34 vocab=67c73479
-/
theorem not_mem_localMaximalCompact3_of_entry {k : GL (Fin 3) (v.adicCompletion K)} {i j : Fin 3}
    (h : 1 < Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)) :
    k ∉ localMaximalCompact3 R K v :=
  fun hk => not_le_of_gt h (hk.1 i j)

/--
@isnad1 id=not.1h6v.s10.a5b48b53d6d7 from=translated src=- shape=80456d2d vocab=54097468
-/
theorem not_mem_localMaximalCompact3_of_inv_entry {k : GL (Fin 3) (v.adicCompletion K)} {i j : Fin 3}
    (h : 1 < Valued.v (((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)) :
    k ∉ localMaximalCompact3 R K v :=
  fun hk => not_le_of_gt h (hk.2 i j)

end LocalCompact

section Components

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (v : HeightOneSpectrum R)

def componentAtN : GL ι (AdeleRing R K) →* GL ι (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map ((AdelicLevel.finAdeleEval R K v).comp (AdelicLevel.adeleFin R K))

def archComponentN : GL ι (AdeleRing R K) →* GL ι (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch R K)

end Components

section Three

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

abbrev componentAt3 : AdelicGL 3 R K →* GL (Fin 3) (v.adicCompletion K) :=
  componentAtN (Fin 3) R K v

abbrev archComponent3 : AdelicGL 3 R K →* GL (Fin 3) (InfiniteAdeleRing K) :=
  archComponentN (Fin 3) R K

end Three

end LanglandsTunnell.CubicInduction
