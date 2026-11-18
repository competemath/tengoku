import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.lean`: wrote out 17 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 16 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul

set_option autoImplicit false

noncomputable section

section CarryC8b

namespace CasimirCentral

open Matrix Finset

variable {A : Type*} [Ring A]

def admRel (e : Fin 3 → Fin 3 → A) : Prop :=
  ∀ i j k l : Fin 3, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0)

def admgen (e : Fin 3 → Fin 3 → A) : Matrix (Fin 3) (Fin 3) A := Matrix.of fun i j => e i j

def cas (e : Fin 3 → Fin 3 → A) (n : ℕ) : A := (admgen e ^ n).trace

private def _root_.CasimirCentral.admder (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (x : A) : A := x * e a b - e a b * x

export _root_.CasimirCentral (admder)

def derM (e : Fin 3 → Fin 3 → A) (a b : Fin 3) (X : Matrix (Fin 3) (Fin 3) A) : Matrix (Fin 3) (Fin 3) A :=
  Matrix.of fun i j => admder e a b (X i j)

def admunit (a b : Fin 3) : Matrix (Fin 3) (Fin 3) A := Matrix.single b a (1 : A)

end CasimirCentral

open MvPolynomial Matrix

namespace SymRestriction

abbrev admIdx : Type := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}

abbrev admP : Type := MvPolynomial admIdx ℂ

def admY : Matrix (Fin 3) (Fin 3) admP :=
  Matrix.of fun a b => if h : a ≤ b then X ⟨(a, b), h⟩ else X ⟨(b, a), le_of_not_ge h⟩

/--
@isnad1 id=eq.0h2v.s4.1e455e441269 from=translated src=- shape=376c686a vocab=2c409a33
-/
theorem Y_symm (a b : Fin 3) : admY a b = admY b a := by
  unfold admY
  simp only [Matrix.of_apply]
  by_cases hab : a ≤ b <;> by_cases hba : b ≤ a
  · have : a = b := le_antisymm hab hba
    subst this
    rfl
  · simp [hab, hba]
  · simp [hab, hba]
  · exact absurd (le_of_not_ge hab) hba

/--
@isnad1 id=eq.0h0v.s4.7e5b11436570 from=translated src=- shape=28fd4024 vocab=ded69957
-/
theorem Y_transpose : admY.transpose = admY :=
  Matrix.ext fun a b => Y_symm b a

def admK (i j : Fin 3) : Matrix (Fin 3) (Fin 3) admP := Matrix.single i j 1 - Matrix.single j i 1

/--
@isnad1 id=eq.0h2v.s6.e1697dbf4207 from=translated src=- shape=2b2d7422 vocab=69053d7f
-/
theorem K_transpose (i j : Fin 3) : (admK i j).transpose = -admK i j := by
  unfold admK
  rw [transpose_sub, transpose_single, transpose_single, neg_sub]

/--
@isnad1 id=eq.0h4v.s9.205be077d7f4 from=translated src=- shape=6bd0aec9 vocab=c218f2c3
-/
theorem comm_symm (i j : Fin 3) (a b : Fin 3) :
    (admK i j * admY - admY * admK i j) a b = (admK i j * admY - admY * admK i j) b a := by
  have h : (admK i j * admY - admY * admK i j).transpose = admK i j * admY - admY * admK i j := by
    rw [transpose_sub, transpose_mul, transpose_mul, Y_transpose, K_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, sub_neg_eq_add, neg_add_eq_sub]
  conv_rhs => rw [← h]
  rfl

def admD (i j : Fin 3) : Derivation ℂ admP admP :=
  mkDerivation ℂ fun v : admIdx => (admK i j * admY - admY * admK i j) v.1.1 v.1.2

/--
@isnad1 id=eq.0h4v.s8.8ea75e5379fd from=translated src=- shape=e2ae1e68 vocab=dc619189
-/
theorem D_Y (i j a b : Fin 3) : admD i j (admY a b) = (admK i j * admY - admY * admK i j) a b := by
  unfold admD
  by_cases hab : a ≤ b
  · have hY : admY a b = X (⟨(a, b), hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, mkDerivation_X]
  · have hY : admY a b = X (⟨(b, a), le_of_not_ge hab⟩ : admIdx) := by simp [admY, hab]
    rw [hY, mkDerivation_X, comm_symm]

def DM (i j : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) : Matrix (Fin 3) (Fin 3) admP := M.map (admD i j)

/--
@isnad1 id=eq.0h5v.s8.22091cc5d573 from=translated src=- shape=26dc6d26 vocab=4ae3e494
-/
theorem single_mul_entry (i j a b : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) :
    (Matrix.single i j (1 : admP) * M) a b = if a = i then M j b else 0 := by
  by_cases h : a = i
  · subst h
    simp
  · simp [h]

/--
@isnad1 id=eq.0h5v.s8.020532a4f075 from=translated src=- shape=6e5fa064 vocab=4ae3e494
-/
theorem mul_single_entry (i j a b : Fin 3) (M : Matrix (Fin 3) (Fin 3) admP) :
    (M * Matrix.single i j (1 : admP)) a b = if b = j then M a i else 0 := by
  by_cases h : b = j
  · subst h
    simp
  · simp [h]

/--
@isnad1 id=eq.0h4v.s8.d6d4b3ae8d80 from=translated src=- shape=01289d77 vocab=78cd5d3b
-/
theorem D_Y_eq (i j a b : Fin 3) :
    admD i j (admY a b) =
      ((if a = i then admY j b else 0) - (if a = j then admY i b else 0)) -
        ((if b = j then admY a i else 0) - (if b = i then admY a j else 0)) := by
  rw [D_Y]
  simp only [admK, Matrix.sub_apply, Matrix.sub_mul, Matrix.mul_sub, single_mul_entry, mul_single_entry]

section Distinct

variable (i j k : Fin 3)

def eig : Fin 6 → admP :=
  ![admY i i + admY j j, (admY i i - admY j j) + C (2 * Complex.I) * admY i j, (admY i i - admY j j) - C (2 *
      Complex.I) * admY i j, admY k k,
    admY i k + C Complex.I * admY j k, admY i k - C Complex.I * admY j k]

def wtv : Fin 6 → ℂ := ![0, -(2 * Complex.I), 2 * Complex.I, 0, -Complex.I, Complex.I]

abbrev admQ : Type := MvPolynomial (Fin 6) ℂ

def admE : Derivation ℂ admQ admQ := mkDerivation ℂ fun n : Fin 6 => wtv n • X n

def Φ : admQ →ₐ[ℂ] admP := aeval (eig i j k)

def ψval (a b : Fin 3) : admQ :=
  if a = b then
    (if a = i then C (1 / 2) * (X 0 + C (1 / 2) * (X 1 + X 2))
      else if a = j then C (1 / 2) * (X 0 - C (1 / 2) * (X 1 + X 2)) else X 3)
  else if a = k ∨ b = k then
    (if a = i ∨ b = i then C (1 / 2) * (X 4 + X 5) else C (-Complex.I / 2) * (X 4 - X 5))
  else C (-Complex.I / 4) * (X 1 - X 2)

def Ψ : admP →ₐ[ℂ] admQ := aeval fun w : admIdx => ψval i j k w.1.1 w.1.2

end Distinct

def wsum (m : Fin 6 →₀ ℕ) : ℂ := ∑ n : Fin 6, (m n : ℂ) * wtv n

def restrictDiag : admP →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval fun w : admIdx => if w.1.1 = w.1.2 then X w.1.1 else 0

section Distinct₂

variable (i j k : Fin 3)

def ρ : admQ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval ![X i + X j, X i - X j, X i - X j, X k, 0, 0]

end Distinct₂

def wt : admIdx → ℕ := fun v => if v.1.1 = v.1.2 then 0 else 1

abbrev IsWH (q : admP) (n : ℕ) : Prop := IsWeightedHomogeneous wt q n

abbrev wcomp (n : ℕ) : admP →ₗ[ℂ] admP := weightedHomogeneousComponent wt n

def zidx (i j : Fin 3) : admIdx := if h : i ≤ j then ⟨(i, j), h⟩ else ⟨(j, i), le_of_not_ge h⟩

section Distinct

variable (i j k : Fin 3)

end Distinct

def killOff : admP →ₐ[ℂ] admP := aeval fun v : admIdx => if v.1.1 = v.1.2 then X v else 0

def admemb : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] admP := rename fun a : Fin 3 => (⟨(a, a), le_rfl⟩ : admIdx)

def traces (n : Fin 3) : admP := (admY ^ ((n : ℕ) + 1)).trace

def psums (n : Fin 3) : MvPolynomial (Fin 3) ℂ := psum (Fin 3) ℂ ((n : ℕ) + 1)

abbrev R3 : Subalgebra ℂ (MvPolynomial (Fin 3) ℂ) := (aeval (R := ℂ) psums).range

end SymRestriction

namespace SymbolLemma

variable {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V]

def wordOp (g : ι → Module.End ℂ V) (l : List ι) : Module.End ℂ V := (l.map g).prod

def lengthSpan (g : ι → Module.End ℂ V) (n : ℕ) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ l : List ι, l.length ≤ n ∧ wordOp g l = T}

def wordSym (l : List ι) : MvPolynomial ι ℂ := (l.map MvPolynomial.X).prod

variable [DecidableEq ι]

def reprWord (μ : ι →₀ ℕ) : List ι := (Multiset.toFinsupp.symm μ).toList

def fword (l : List ι) : FreeAlgebra ℂ ι := (l.map (FreeAlgebra.ι ℂ)).prod

def filt (n : ℕ) : Submodule ℂ (FreeAlgebra ℂ ι) :=
  Submodule.span ℂ {a | ∃ l : List ι, l.length ≤ n ∧ fword l = a}

def admop (g : ι → Module.End ℂ V) : FreeAlgebra ℂ ι →ₐ[ℂ] Module.End ℂ V := FreeAlgebra.lift ℂ g

def sym : FreeAlgebra ℂ ι →ₐ[ℂ] MvPolynomial ι ℂ := FreeAlgebra.lift ℂ MvPolynomial.X

def admL : MvPolynomial ι ℂ →ₗ[ℂ] FreeAlgebra ℂ ι :=
  (MvPolynomial.basisMonomials ι ℂ).constr ℂ fun μ => fword (reprWord μ)

section Bracket

variable (g : ι → Module.End ℂ V) (δ : Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ)) (κ : Module.End ℂ V)

end Bracket

end SymbolLemma

namespace Adm0

open SymbolLemma CasimirCentral SymRestriction MvPolynomial Matrix

abbrev Letter : Type := admIdx ⊕ (Fin 3 × Fin 3)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def letters (e : Fin 3 → Fin 3 → Module.End ℂ V) : Letter → Module.End ℂ V
  | Sum.inl v => (2⁻¹ : ℂ) • (e v.1.1 v.1.2 + e v.1.2 v.1.1)
  | Sum.inr ij => e ij.1 ij.2 - e ij.2 ij.1

def pIdx (a b : Fin 3) : admIdx := if h : a ≤ b then ⟨(a, b), h⟩ else ⟨(b, a), le_of_not_ge h⟩

/--
@isnad1 id=eq.0h2v.s4.635afdf6ee57 from=translated src=- shape=98cbbbbb vocab=8c232272
-/
theorem Y_eq_X_pIdx (a b : Fin 3) : admY a b = X (pIdx a b) := by
  unfold admY pIdx
  simp only [Matrix.of_apply]
  split_ifs <;> rfl

def admfe (i j : Fin 3) : FreeAlgebra ℂ Letter :=
  FreeAlgebra.ι ℂ (Sum.inl (pIdx i j) : Letter) + (2⁻¹ : ℂ) • FreeAlgebra.ι ℂ (Sum.inr (i, j) : Letter)

def admproj : MvPolynomial Letter ℂ →ₐ[ℂ] admP :=
  aeval (Sum.elim (fun v : admIdx => (X v : admP)) fun _ : Fin 3 × Fin 3 => (0 : admP))

def admemb : admP →ₐ[ℂ] MvPolynomial Letter ℂ := rename Sum.inl

def psym : FreeAlgebra ℂ Letter →ₐ[ℂ] admP := admproj.comp sym

def tw (k : Fin 3) : ℕ := (k : ℕ) + 1

section OnF

variable (e : Fin 3 → Fin 3 → Module.End ℂ V) (F : Submodule ℂ V)

def QF (n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ w : List Letter, w.length ≤ n ∧ ∃ f ∈ F, wordOp (letters e) w f = v}

variable {e F}
variable (hg : ∀ x y : Letter, letters e x * letters e y - letters e y * letters e x ∈
    Submodule.span ℂ (Set.range (letters e)))
variable (hF : ∀ ij : Fin 3 × Fin 3, ∀ f ∈ F, letters e (Sum.inr ij) f = 0)
include hg hF

def casMon (α : Fin 3 →₀ ℕ) : FreeAlgebra ℂ Letter := cas admfe 1 ^ α 0 * cas admfe 2 ^ α 1 * cas admfe 3 ^ α 2

end OnF

end Adm0

namespace Adm0

open SymbolLemma CasimirCentral SymRestriction MvPolynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def admcm (a b : Module.End ℂ V) : Module.End ℂ V := a * b - b * a

def LS (e : Fin 3 → Fin 3 → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ (Set.range (letters e))

section Table

variable {e : Fin 3 → Fin 3 → Module.End ℂ V} (he : admRel e)
include he

end Table

def ktab (i j : Fin 3) (kl : Fin 3 × Fin 3) : MvPolynomial Letter ℂ :=
  ((if j = kl.1 then X (Sum.inr (i, kl.2) : Letter) else 0) +
      (if i = kl.2 then X (Sum.inr (j, kl.1) : Letter) else 0)) -
    ((if j = kl.2 then X (Sum.inr (i, kl.1) : Letter) else 0) +
      (if i = kl.1 then X (Sum.inr (j, kl.2) : Letter) else 0))

def rot (i j : Fin 3) : Derivation ℂ (MvPolynomial Letter ℂ) (MvPolynomial Letter ℂ) :=
  mkDerivation ℂ (Sum.elim (fun v : admIdx => admemb (-(admD i j (X v : admP)))) (ktab i j))

/--
@isnad1 id=eq.0h1v.s7.32b2f997e08d from=translated src=- shape=286661b0 vocab=f0d270db
-/
theorem pIdx_idx (v : admIdx) : pIdx v.1.1 v.1.2 = v := by
  unfold pIdx
  rw [dite_eq_left v.2]

/--
@isnad1 id=eq.0h1v.s7.99ea71873712 from=translated src=- shape=8a4aff28 vocab=0383ecef
-/
theorem X_idx_eq_Y (v : admIdx) : (X v : admP) = admY v.1.1 v.1.2 := by
  rw [Y_eq_X_pIdx, pIdx_idx]

section Brackets

variable {e : Fin 3 → Fin 3 → Module.End ℂ V} (he : admRel e)
include he

end Brackets

end Adm0

end CarryC8b

namespace FischerForm

open MvPolynomial Finset

variable {σ : Type*}

def wt (α : σ →₀ ℕ) : ℕ := α.prod fun _ n => n.factorial

/--
@isnad1 id=lt.0h2v.s4.2e639fd3e2d7 from=translated src=- shape=d1cbbded vocab=d28ecda1
-/
theorem wt_pos (α : σ →₀ ℕ) : 0 < wt α := by
  unfold wt Finsupp.prod
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

section Form

variable [DecidableEq σ]

def admform (p q : MvPolynomial σ ℂ) : ℂ :=
  ∑ α ∈ p.support ∪ q.support, (wt α : ℂ) * p.coeff α * star (q.coeff α)

/--
@isnad1 id=eq.1h4v.s7.ba77d4728ba0 from=translated src=- shape=756993a3 vocab=e064a0c3
-/
theorem form_eq_sum {p q : MvPolynomial σ ℂ} {S : Finset (σ →₀ ℕ)} (hS : p.support ∪ q.support ⊆ S) :
    admform p q = ∑ α ∈ S, (wt α : ℂ) * p.coeff α * star (q.coeff α) := by
  unfold admform
  refine Finset.sum_subset hS fun α _ hα => ?_
  rw [Finset.mem_union, not_or] at hα
  rw [notMem_support_iff.1 hα.1]
  simp

/--
@isnad1 id=eq.0h5v.s7.1ecd4f52544d from=translated src=- shape=cc877811 vocab=ab189885
-/
theorem form_lin (z : ℂ) (p₁ p₂ q : MvPolynomial σ ℂ) :
    admform (z • p₁ + p₂) q = z * admform p₁ q + admform p₂ q := by
  set S : Finset (σ →₀ ℕ) := (z • p₁ + p₂).support ∪ p₁.support ∪ p₂.support ∪ q.support with hSdef
  have h₀ : (z • p₁ + p₂).support ∪ q.support ⊆ S := by
    intro α hα; simp only [hSdef, Finset.mem_union] at hα ⊢; tauto
  have h₁ : p₁.support ∪ q.support ⊆ S := by
    intro α hα; simp only [hSdef, Finset.mem_union] at hα ⊢; tauto
  have h₂ : p₂.support ∪ q.support ⊆ S := by
    intro α hα; simp only [hSdef, Finset.mem_union] at hα ⊢; tauto
  rw [form_eq_sum h₀, form_eq_sum h₁, form_eq_sum h₂, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add, coeff_smul, smul_eq_mul]
  ring

/--
@isnad1 id=eq.0h3v.s5.41d876d3af3c from=translated src=- shape=c3f9bcf0 vocab=b05a563c
-/
theorem form_symm (p q : MvPolynomial σ ℂ) : admform q p = star (admform p q) := by
  unfold admform
  rw [star_sum, Finset.union_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [star_mul, star_mul, star_star, star_natCast]
  ring

/--
@isnad1 id=lt.1h2v.s6.705a70707b3b from=translated src=- shape=f713541c vocab=eb3f7c43
-/
theorem form_pos {p : MvPolynomial σ ℂ} (hp : p ≠ 0) : 0 < (admform p p).re := by
  unfold admform
  rw [Finset.union_self, Complex.re_sum]
  have hterm : ∀ α : σ →₀ ℕ,
      ((wt α : ℂ) * p.coeff α * star (p.coeff α)).re = (wt α : ℝ) * Complex.normSq (p.coeff α) := by
    intro α
    rw [mul_assoc, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  simp only [hterm]
  obtain ⟨α, hα⟩ : p.support.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h => hp (support_eq_empty.1 h)
  refine Finset.sum_pos' (fun β _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)) ⟨α, hα, ?_⟩
  exact mul_pos (Nat.cast_pos.2 (wt_pos α)) (Complex.normSq_pos.2 (mem_support_iff.1 hα))

/--
@isnad1 id=eq.0h2v.s5.e52afec8a5d1 from=translated src=- shape=94b1b2e1 vocab=bd7c46ba
-/
theorem form_zero_left (q : MvPolynomial σ ℂ) : admform (0 : MvPolynomial σ ℂ) q = 0 := by
  unfold admform
  simp

/--
@isnad1 id=eq.0h4v.s6.aa8e7b969d69 from=translated src=- shape=7e4f3547 vocab=b6628329
-/
theorem form_add_left (p₁ p₂ q : MvPolynomial σ ℂ) : admform (p₁ + p₂) q = admform p₁ q + admform p₂ q := by
  simpa using form_lin 1 p₁ p₂ q

/--
@isnad1 id=eq.0h4v.s6.697535556ee7 from=translated src=- shape=a0a6fa00 vocab=1e55b402
-/
theorem form_smul_left (z : ℂ) (p q : MvPolynomial σ ℂ) : admform (z • p) q = z * admform p q := by
  simpa [form_zero_left] using form_lin z p 0 q

/--
@isnad1 id=eq.0h5v.s6.ed5189840602 from=translated src=- shape=9f78ad4d vocab=2a4828fc
-/
theorem form_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (q : MvPolynomial σ ℂ) :
    admform (∑ i ∈ s, f i) q = ∑ i ∈ s, admform (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_left, ih]

/--
@isnad1 id=eq.0h5v.s6.c1a9020d107f from=translated src=- shape=f9496410 vocab=2a4828fc
-/
theorem form_sum_right {ι : Type*} (s : Finset ι) (p : MvPolynomial σ ℂ) (g : ι → MvPolynomial σ ℂ) :
    admform p (∑ i ∈ s, g i) = ∑ i ∈ s, admform p (g i) := by
  rw [form_symm, form_sum_left, star_sum]
  exact Finset.sum_congr rfl fun i _ => (form_symm (g i) p).symm

/--
@isnad1 id=eq.0h4v.s6.f2ff275a5a31 from=translated src=- shape=d0b4c5da vocab=fbec9373
-/
theorem form_smul_right (z : ℂ) (p q : MvPolynomial σ ℂ) : admform p (z • q) = star z * admform p q := by
  rw [form_symm, form_smul_left, star_mul', ← form_symm]

/--
@isnad1 id=eq.0h5v.s8.fc58e3de8441 from=translated src=- shape=099c72e9 vocab=6e74a1fc
-/
theorem form_monomial (γ β : σ →₀ ℕ) (c d : ℂ) :
    admform (monomial γ c) (monomial β d) = if γ = β then (wt β : ℂ) * c * star d else 0 := by
  have hS : (monomial γ c).support ∪ (monomial β d).support ⊆ {γ, β} := by
    refine Finset.union_subset ?_ ?_
    · exact support_monomial_subset.trans (by simp)
    · exact support_monomial_subset.trans (by simp)
  rw [form_eq_sum hS]
  by_cases hγβ : γ = β
  · subst hγβ
    simp [coeff_monomial]
  · rw [Finset.sum_pair hγβ, ite_eq_right hγβ]
    simp [coeff_monomial, hγβ, Ne.symm hγβ]

end Form

/--
@isnad1 id=le.0h2v.s7.cd9b3bb915f1 from=translated src=- shape=570aff30 vocab=de67304c
-/
theorem homogeneousSubmodule_le_restrictTotalDegree (n : ℕ) :
    homogeneousSubmodule σ ℂ n ≤ restrictTotalDegree σ ℂ n := by
  intro p hp
  rw [mem_restrictTotalDegree]
  by_cases h0 : p = 0
  · simp [h0]
  · exact ((mem_homogeneousSubmodule n p).1 hp).totalDegree h0 |>.le

section Der

variable [Fintype σ]

def admder (A : σ → σ → ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  ∑ i : σ, ∑ j : σ, A i j • (LinearMap.mulLeft ℂ (X j : MvPolynomial σ ℂ)).comp (pderiv i).toLinearMap

/--
@isnad1 id=eq.0h3v.s9.b94fe20d13f1 from=translated src=- shape=325fcd00 vocab=d15a46bb
-/
theorem der_apply (A : σ → σ → ℂ) (p : MvPolynomial σ ℂ) :
    admder A p = ∑ i : σ, ∑ j : σ, A i j • (X j * pderiv i p) := by
  simp [admder]

/--
@isnad1 id=finitedi.0h2v.s7.80e8b2499c20 from=translated src=- shape=f2142703 vocab=68dbc65a
-/
scoped instance finiteDimensional_homogeneousSubmodule (n : ℕ) :
    FiniteDimensional ℂ (homogeneousSubmodule σ ℂ n) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

/--
@isnad1 id=eq.0h4v.s9.d9cb9aa71e1d from=translated src=- shape=d570d235 vocab=f72e0a21
-/
theorem der_monomial (A : σ → σ → ℂ) (α : σ →₀ ℕ) (c : ℂ) :
    admder A (monomial α c) =
      ∑ i : σ, ∑ j : σ, A i j • monomial (Finsupp.single j 1 + (α - Finsupp.single i 1)) (c * (α i : ℂ)) := by
  rw [der_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_monomial, X, monomial_mul_monomial, one_mul]

end Der

section Skew

variable [Fintype σ] [DecidableEq σ]

/--
@isnad1 id=eq.0h3v.s6.009a8039fc44 from=translated src=- shape=29e0e4c0 vocab=aacd3488
-/
theorem wt_add_single (γ : σ →₀ ℕ) (i : σ) : wt (γ + Finsupp.single i 1) = (γ i + 1) * wt γ := by
  unfold wt
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
  have h : ∀ k : σ,
      ((γ + Finsupp.single i 1 : σ →₀ ℕ) k).factorial = (if k = i then γ i + 1 else 1) * (γ k).factorial := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp [Nat.factorial_succ]
    · simp [hk]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

/--
@isnad1 id=eq.0h5v.s9.57ed1d3ae6e5 from=translated src=- shape=535b1e6f vocab=15a798f4
-/
theorem ite_weight_swap (α β : σ →₀ ℕ) (i j : σ) :
    (if Finsupp.single j 1 + (α - Finsupp.single i 1) = β then (wt β : ℂ) * (α i : ℂ) else 0) =
      if α = Finsupp.single i 1 + (β - Finsupp.single j 1) then (wt α : ℂ) * (β j : ℂ) else 0 := by
  by_cases hαi : α i = 0
  · have hR : α ≠ Finsupp.single i 1 + (β - Finsupp.single j 1) := by
      intro h
      have := congrArg (fun f : σ →₀ ℕ => f i) h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      omega
    rw [ite_eq_right hR, hαi]
    split_ifs <;> simp
  by_cases hβj : β j = 0
  · have hL : Finsupp.single j 1 + (α - Finsupp.single i 1) ≠ β := by
      intro h
      have := congrArg (fun f : σ →₀ ℕ => f j) h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      omega
    rw [ite_eq_right hL, hβj]
    split_ifs <;> simp

  obtain ⟨α', rfl⟩ : ∃ α', α = α' + Finsupp.single i 1 :=
    ⟨α - Finsupp.single i 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hαi))).symm⟩
  obtain ⟨β', rfl⟩ : ∃ β', β = β' + Finsupp.single j 1 :=
    ⟨β - Finsupp.single j 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hβj))).symm⟩
  simp only [add_tsub_cancel_right]
  have hc₁ : (Finsupp.single j 1 + α' = β' + Finsupp.single j 1) ↔ α' = β' := by
    rw [add_comm]
    exact add_left_inj _
  have hc₂ : (α' + Finsupp.single i 1 = Finsupp.single i 1 + β') ↔ α' = β' := by
    rw [add_comm (Finsupp.single i 1) β']
    exact add_left_inj _
  simp only [hc₁, hc₂]
  by_cases h : α' = β'
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, wt_add_single, wt_add_single]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right h]

/--
@isnad1 id=eq.1h6v.s9.72151ebae796 from=translated src=- shape=b73721e1 vocab=275a6332
-/
theorem form_der_monomial {A : σ → σ → ℂ} (hA : ∀ i j, star (A i j) = -A j i) (α β : σ →₀ ℕ) (c d : ℂ) :
    admform (admder A (monomial α c)) (monomial β d) = -admform (monomial α c) (admder A (monomial β d)) := by
  rw [der_monomial, der_monomial, form_sum_left, form_sum_right]
  simp only [form_sum_left, form_sum_right, form_smul_left, form_smul_right, form_monomial, hA]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hk := ite_weight_swap α β j i
  simp only [star_mul', star_natCast, neg_mul, neg_neg]
  split_ifs at hk ⊢ with h₁ h₂ h₃
  · rw [← h₂]
    linear_combination (A j i * c * star d) * hk
  · linear_combination (A j i * c * star d) * hk
  · rw [← h₃]
    linear_combination (A j i * c * star d) * hk
  · simp

/--
@isnad1 id=eq.1h4v.s8.b2194b197397 from=translated src=- shape=3ab3bea6 vocab=97f179a7
-/
theorem form_der_skew {A : σ → σ → ℂ} (hA : ∀ i j, star (A i j) = -A j i) (p q : MvPolynomial σ ℂ) :
    admform (admder A p) q = -admform p (admder A q) := by
  conv_lhs => rw [p.as_sum, q.as_sum]
  conv_rhs => rw [p.as_sum, q.as_sum]
  rw [map_sum, form_sum_left, map_sum, form_sum_left]
  simp only [form_sum_right]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  exact form_der_monomial hA α β _ _

end Skew

end FischerForm
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm

section Piece

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/--
@isnad1 id=eq.2h4v.s8.468344a5bcc3 from=translated src=- shape=1a422c5b vocab=3ef83c02
-/
theorem form_zero_left (M₀ : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    {n : W} (hn : n ∈ M₀) : B 0 n = 0 := by
  have h := hlin (-1) 0 M₀.zero_mem 0 M₀.zero_mem n hn
  rw [smul_zero, add_zero] at h
  linear_combination h

def orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) : Submodule ℂ W where
  carrier := {w | w ∈ M₀ ∧ ∀ n ∈ N, B w n = 0}
  add_mem' {a b} ha hb := ⟨M₀.add_mem ha.1 hb.1, fun n hn => by
    have h := hlin 1 a ha.1 b hb.1 n (hNM hn)
    rw [one_smul, one_mul, ha.2 n hn, hb.2 n hn, add_zero] at h
    exact h⟩
  zero_mem' := ⟨M₀.zero_mem, fun n hn => form_zero_left M₀ B hlin (hNM hn)⟩
  smul_mem' z a ha := ⟨M₀.smul_mem z ha.1, fun n hn => by
    have h := hlin z a ha.1 0 M₀.zero_mem n (hNM hn)
    rw [add_zero, ha.2 n hn, mul_zero, zero_add, form_zero_left M₀ B hlin (hNM hn)] at h
    exact h⟩

end Piece
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm

namespace S5Split

open Adm0 SymRestriction FischerForm MvPolynomial

abbrev R9 : Type := MvPolynomial (Fin 3 × Fin 3) ℂ

def a9 (i j : Fin 3) (x y : Fin 3 × Fin 3) : ℤ :=
  (if x.1 = i ∧ y = (j, x.2) then 1 else 0) - (if x.1 = j ∧ y = (i, x.2) then 1 else 0) -
    (if x.2 = j ∧ y = (x.1, i) then 1 else 0) + (if x.2 = i ∧ y = (x.1, j) then 1 else 0)

/--
@isnad1 id=eq.0h4v.s5.8ab6e8d7233e from=translated src=- shape=43220fbb vocab=a6890aae
-/
theorem a9_antisymm (i j : Fin 3) : ∀ x y : Fin 3 × Fin 3, a9 i j x y = -a9 i j y x := by
  fin_cases i <;> fin_cases j <;> decide

def A9 (i j : Fin 3) (x y : Fin 3 × Fin 3) : ℂ := (a9 i j x y : ℂ)

/--
@isnad1 id=eq.0h4v.s6.b6918fa792de from=translated src=- shape=813bfce8 vocab=f8ebbe1a
-/
theorem A9_skew (i j : Fin 3) : ∀ x y : Fin 3 × Fin 3, star (A9 i j x y) = -A9 i j y x := by
  intro x y
  rw [A9, A9, a9_antisymm i j x y]
  push_cast
  rw [star_neg, Complex.star_def, map_intCast]

def D9 (i j : Fin 3) : R9 →ₗ[ℂ] R9 := FischerForm.admder (A9 i j)

/--
@isnad1 id=eq.0h3v.s9.6e12c71e30c1 from=translated src=- shape=a03534c3 vocab=12196e85
-/
theorem D9_X (i j : Fin 3) (x : Fin 3 × Fin 3) :
    D9 i j (X x) = ∑ y : Fin 3 × Fin 3, A9 i j x y • (X y : R9) := by
  rw [D9, der_apply]
  rw [Finset.sum_eq_single x]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [pderiv_X_self, mul_one]
  · intro a _ hax
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [pderiv_X_of_ne (Ne.symm hax), mul_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

/--
@isnad1 id=eq.0h4v.s9.77c0bf366e4d from=translated src=- shape=5cc0a950 vocab=15dd1f31
-/
theorem admder_mul {τ : Type*} [Fintype τ] (A : τ → τ → ℂ) (p q : MvPolynomial τ ℂ) :
    FischerForm.admder A (p * q) = p * FischerForm.admder A q + q * FischerForm.admder A p := by
  simp only [der_apply, Derivation.leibniz, smul_eq_mul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

section Nine

variable (n : ℕ)

abbrev M9 : Submodule ℂ R9 := homogeneousSubmodule (Fin 3 × Fin 3) ℂ n

scoped instance : FiniteDimensional ℂ (M9 n) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

def T9 : (Fin 3 × Fin 3 → M9 n) →ₗ[ℂ] R9 :=
  ∑ ij : Fin 3 × Fin 3, (D9 ij.1 ij.2).comp ((M9 n).subtype.comp (LinearMap.proj ij))

abbrev N9 : Submodule ℂ R9 := LinearMap.range (T9 n)

end Nine
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm

section Six

def toP : R9 →ₐ[ℂ] admP := rename fun ab : Fin 3 × Fin 3 => pIdx ab.1 ab.2

def ofP : admP →ₐ[ℂ] R9 := rename fun v : admIdx => v.1

/--
@isnad1 id=eq.0h1v.s8.17e1cb92034d from=translated src=- shape=e91fae65 vocab=fa028906
-/
theorem toP_ofP (p : admP) : toP (ofP p) = p := by
  rw [toP, ofP, rename_rename]
  have h : ((fun ab : Fin 3 × Fin 3 => pIdx ab.1 ab.2) ∘ fun v : admIdx => v.1) = id := funext fun v => pIdx_idx v
  rw [h, rename_id]
  rfl

/--
@isnad1 id=eq.0h1v.s8.38b9be415bcc from=translated src=- shape=9ebf48c5 vocab=e945dfbc
-/
theorem toP_X (ab : Fin 3 × Fin 3) : toP (X ab) = admY ab.1 ab.2 := by
  rw [toP, rename_X, Y_eq_X_pIdx]

/--
@isnad1 id=eq.0h3v.s9.2995e20cb71a from=translated src=- shape=e6419616 vocab=aca28e6c
-/
theorem toP_D9_X (i j : Fin 3) (ab : Fin 3 × Fin 3) : toP (D9 i j (X ab)) = admD i j (toP (X ab)) := by
  rw [D9_X, map_sum, toP_X, D_Y_eq]
  simp only [map_smul, toP_X]
  obtain ⟨a, b⟩ := ab
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [A9, a9, Fintype.sum_prod_type, Fin.sum_univ_three] <;> module

/--
@isnad1 id=eq.0h3v.s9.b5a2ed5d7fbb from=translated src=- shape=dc4c6805 vocab=cd78c305
-/
theorem toP_D9 (i j : Fin 3) (r : R9) : toP (D9 i j r) = admD i j (toP r) := by
  induction r using MvPolynomial.induction_on with
  | C c =>
    have h9 : D9 i j (C c : R9) = 0 := by
      rw [D9, der_apply]
      simp
    rw [h9, map_zero, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Derivation.map_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    have hX := toP_D9_X i j x
    simp only [D9] at hp hX ⊢
    rw [admder_mul, map_add, map_mul, map_mul, hp, hX, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm]

end Six
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm

end S5Split
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split

end
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split

set_option autoImplicit false

noncomputable section

namespace WsB
namespace TF

open Adm0 SymRestriction FischerForm S5Split MvPolynomial

def symE : admP →ₐ[ℂ] R9 :=
  aeval fun v : admIdx => C (1 / 2 : ℂ) * ((X v.1 : R9) + X (v.1.2, v.1.1))

/--
@isnad1 id=eq.0h1v.s9.c6476f71bd4b from=translated src=- shape=3dc41c8e vocab=6d6b5c0c
-/
theorem symE_X (v : admIdx) : symE (X v) = C (1 / 2 : ℂ) * ((X v.1 : R9) + X (v.1.2, v.1.1)) := by
  rw [symE, aeval_X]

/--
@isnad1 id=eq.0h2v.s9.46d9b9e353e7 from=translated src=- shape=e0614bc5 vocab=5a0ebff3
-/
theorem symE_Y (a b : Fin 3) : symE (admY a b) = C (1 / 2 : ℂ) * ((X (a, b) : R9) + X (b, a)) := by
  rw [Y_eq_X_pIdx, symE_X]
  unfold pIdx
  split_ifs with h
  · rfl
  · simp only
    rw [add_comm]

/--
@isnad1 id=eq.0h1v.s9.ea46e51feb5b from=translated src=- shape=1d8e4b17 vocab=cd4df464
-/
theorem toP_symE_X (v : admIdx) : toP (symE (X v)) = X v := by
  obtain ⟨⟨a, b⟩, hab⟩ := v
  rw [symE_X, ← smul_eq_C_mul, map_smul, map_add]
  simp only
  rw [toP_X, toP_X]
  simp only
  rw [Y_symm b a, ← two_smul ℂ (admY a b), smul_smul, X_idx_eq_Y]
  norm_num

/--
@isnad1 id=eq.0h1v.s8.38a9ec414585 from=translated src=- shape=e91fae65 vocab=0b46670d
-/
theorem toP_symE (p : admP) : toP (symE p) = p := by
  have h : toP.comp symE = AlgHom.id ℂ admP := MvPolynomial.algHom_ext fun v => by
    rw [AlgHom.comp_apply, AlgHom.id_apply, toP_symE_X]
  exact congrArg (fun φ : admP →ₐ[ℂ] admP => φ p) h

/--
@isnad1 id=injectiv.0h0v.s7.fe64a1f05ea2 from=translated src=- shape=91c1b9c9 vocab=63241d18
-/
theorem symE_injective : Function.Injective symE := fun p q h => by
  rw [← toP_symE p, ← toP_symE q, h]

def symP : R9 →ₐ[ℂ] R9 := symE.comp toP

/--
@isnad1 id=eq.0h1v.s9.464a7d2ea747 from=translated src=- shape=0b99efa2 vocab=4b378610
-/
theorem symP_X (x : Fin 3 × Fin 3) : symP (X x) = C (1 / 2 : ℂ) * ((X x : R9) + X (x.2, x.1)) := by
  rw [symP, AlgHom.comp_apply, toP_X, symE_Y]

/--
@isnad1 id=eq.0h4v.s7.e8aeae582d35 from=translated src=- shape=07364012 vocab=f1ee7687
-/
theorem a9_swap (i j : Fin 3) : ∀ x y : Fin 3 × Fin 3, a9 i j (x.2, x.1) y = a9 i j x (y.2, y.1) := by
  fin_cases i <;> fin_cases j <;> decide

/--
@isnad1 id=eq.0h4v.s7.e53c65c18db4 from=translated src=- shape=07364012 vocab=7aff59c7
-/
theorem A9_swap (i j : Fin 3) (x y : Fin 3 × Fin 3) : A9 i j (x.2, x.1) y = A9 i j x (y.2, y.1) := by
  rw [A9, A9, a9_swap]

/--
@isnad1 id=eq.0h3v.s10.b7985a2c8135 from=translated src=- shape=76e26682 vocab=14416352
-/
theorem D9_symP_X (i j : Fin 3) (x : Fin 3 × Fin 3) : D9 i j (symP (X x)) = symP (D9 i j (X x)) := by

  have hsw : (∑ y : Fin 3 × Fin 3, A9 i j (x.2, x.1) y • (X y : R9)) =
      ∑ y : Fin 3 × Fin 3, A9 i j x y • (X (y.2, y.1) : R9) := by
    rw [← Fintype.sum_equiv (Equiv.prodComm (Fin 3) (Fin 3)) (fun y => A9 i j x (y.2, y.1) • (X y : R9))
      (fun y => A9 i j x y • (X (y.2, y.1) : R9)) (fun y => rfl)]
    exact Finset.sum_congr rfl (fun y _ => by rw [A9_swap])
  calc D9 i j (symP (X x)) = D9 i j ((1 / 2 : ℂ) • ((X x : R9) + X (x.2, x.1))) := by rw [symP_X, smul_eq_C_mul]
    _ = (1 / 2 : ℂ) • (∑ y : Fin 3 × Fin 3, A9 i j x y • (X y : R9) +
          ∑ y : Fin 3 × Fin 3, A9 i j (x.2, x.1) y • (X y : R9)) := by rw [map_smul, map_add, D9_X, D9_X]
    _ = (1 / 2 : ℂ) • (∑ y : Fin 3 × Fin 3, A9 i j x y • (X y : R9) +
          ∑ y : Fin 3 × Fin 3, A9 i j x y • (X (y.2, y.1) : R9)) := by rw [hsw]
    _ = ∑ y : Fin 3 × Fin 3, A9 i j x y • ((1 / 2 : ℂ) • ((X y : R9) + X (y.2, y.1))) := by
          rw [← Finset.sum_add_distrib, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [← smul_add, smul_comm]
    _ = symP (D9 i j (X x)) := by
          rw [D9_X, map_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [map_smul, symP_X, ← smul_eq_C_mul]

/--
@isnad1 id=eq.0h3v.s10.459cebfe7dc4 from=translated src=- shape=df60bdfa vocab=a6edf0e4
-/
theorem D9_symP (i j : Fin 3) (r : R9) : D9 i j (symP r) = symP (D9 i j r) := by
  induction r using MvPolynomial.induction_on with
  | C c =>
    have h9 : ∀ c : ℂ, D9 i j (C c : R9) = 0 := by
      intro c; rw [D9, der_apply]; simp
    have hs : symP (C c) = C c := by rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rw [hs, h9, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    simp only [D9] at hp ⊢
    rw [map_mul, admder_mul, admder_mul, map_add, map_mul, map_mul, hp]
    have hX := D9_symP_X i j x
    simp only [D9] at hX
    rw [hX]

/--
@isnad1 id=eq.0h3v.s9.c0707129875b from=translated src=- shape=064fd50b vocab=a01403fa
-/
theorem symE_admD (i j : Fin 3) (p : admP) : symE (admD i j p) = D9 i j (symE p) := by
  have h1 : symE p = symP (ofP p) := by rw [symP, AlgHom.comp_apply, toP_ofP]
  rw [h1, D9_symP, symP, AlgHom.comp_apply, toP_D9, toP_ofP]

def FP (p q : admP) : ℂ := FischerForm.admform (symE p) (symE q)

/--
@isnad1 id=eq.0h4v.s6.a4e48ac9fb87 from=translated src=- shape=6779fc7e vocab=bf68d997
-/
theorem FP_lin (z : ℂ) (p₁ p₂ q : admP) : FP (z • p₁ + p₂) q = z * FP p₁ q + FP p₂ q := by
  simp only [FP, map_add, map_smul, form_lin]

/--
@isnad1 id=eq.0h2v.s5.7d62ccc42604 from=translated src=- shape=f868f03a vocab=181abaa9
-/
theorem FP_symm (p q : admP) : FP q p = (starRingEnd ℂ) (FP p q) := by
  rw [FP, FP, form_symm, starRingEnd_apply]

/--
@isnad1 id=lt.1h1v.s5.8b056854a8ba from=translated src=- shape=414f063b vocab=e644e4a2
-/
theorem FP_pos (p : admP) (hp : p ≠ 0) : 0 < (FP p p).re :=
  form_pos fun h => hp (symE_injective (by rw [h, map_zero]))

/--
@isnad1 id=eq.0h4v.s8.0221acb9eb6d from=translated src=- shape=cacdc906 vocab=22baaa39
-/
theorem FP_D_skew (i j : Fin 3) (p q : admP) : FP (admD i j p) q = -FP p (admD i j q) := by
  simp only [FP, symE_admD, D9]
  exact form_der_skew (A9_skew i j) _ _

end WsB.TF
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace WsB
namespace TFT

variable {P : Type*} [AddCommGroup P] [Module ℂ P]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {r : ℕ}

def coord (e : Module.Basis (Fin r) ℂ W) : P ⊗[ℂ] W ≃ₗ[ℂ] (Fin r → P) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ P) e.equivFun).trans (TensorProduct.piScalarRight ℂ ℂ P (Fin r))

/--
@isnad1 id=eq.0h7v.s9.b26ccc454222 from=translated src=- shape=f3503f2d vocab=60cc0cfb
-/
theorem coord_tmul (e : Module.Basis (Fin r) ℂ W) (p : P) (w : W) (k : Fin r) :
    coord e (p ⊗ₜ[ℂ] w) k = e.repr w k • p := by
  simp [coord, TensorProduct.congr_tmul, TensorProduct.piScalarRightHom_tmul, Module.Basis.equivFun_apply]

/--
@isnad1 id=eq.0h7v.s9.18c4ce1cc86f from=translated src=- shape=edc49831 vocab=2fcc1959
-/
theorem coord_map_left (e : Module.Basis (Fin r) ℂ W) (f : P →ₗ[ℂ] P) (x : P ⊗[ℂ] W) (k : Fin r) :
    coord e (TensorProduct.map f LinearMap.id x) k = f (coord e x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w => rw [TensorProduct.map_tmul, LinearMap.id_apply, coord_tmul, coord_tmul, map_smul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/--
@isnad1 id=eq.0h7v.s10.b3cb7c7695be from=translated src=- shape=c78fcf19 vocab=590aa4ba
-/
theorem coord_map_right (e : Module.Basis (Fin r) ℂ W) (g : W →ₗ[ℂ] W) (x : P ⊗[ℂ] W) (k : Fin r) :
    coord e (TensorProduct.map LinearMap.id g x) k = ∑ l : Fin r, e.repr (g (e l)) k • coord e x l := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p w =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, coord_tmul]
    simp only [coord_tmul, smul_smul, ← Finset.sum_smul]
    congr 1

    have hgw : g w = ∑ x : Fin r, e.repr w x • g (e x) := by
      conv_lhs => rw [← e.sum_repr w]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun x _ => map_smul _ _ _)
    rw [hgw, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]

section Form

variable (FP : P → P → ℂ)
  (hFlin : ∀ (z : ℂ) (p₁ p₂ q : P), FP (z • p₁ + p₂) q = z * FP p₁ q + FP p₂ q)
  (hFsymm : ∀ p q : P, FP q p = (starRingEnd ℂ) (FP p q))
  (hFpos : ∀ p : P, p ≠ 0 → 0 < (FP p p).re)

include hFlin in
/--
@isnad1 id=eq.1h3v.s7.bc23510f9021 from=translated src=- shape=012ea146 vocab=a662edd1
-/
theorem F_zero_left (q : P) : FP 0 q = 0 := by
  have h := hFlin (-1) 0 0 q; rw [smul_zero, add_zero] at h; linear_combination h

include hFlin in
/--
@isnad1 id=eq.1h5v.s7.300d0dcdac22 from=translated src=- shape=9f94152c vocab=a662edd1
-/
theorem F_add_left (p₁ p₂ q : P) : FP (p₁ + p₂) q = FP p₁ q + FP p₂ q := by
  have h := hFlin 1 p₁ p₂ q; rw [one_smul, one_mul] at h; exact h

include hFlin in
/--
@isnad1 id=eq.1h5v.s7.0e28305107db from=translated src=- shape=44aeb8ac vocab=a662edd1
-/
theorem F_smul_left (z : ℂ) (p q : P) : FP (z • p) q = z * FP p q := by
  have h := hFlin z p 0 q; rw [add_zero, F_zero_left FP hFlin, add_zero] at h; exact h

include hFlin hFsymm in
/--
@isnad1 id=eq.2h5v.s7.1ccde86e479b from=translated src=- shape=6db9218c vocab=b9be011b
-/
theorem F_add_right (p q₁ q₂ : P) : FP p (q₁ + q₂) = FP p q₁ + FP p q₂ := by
  rw [hFsymm (q₁ + q₂) p, hFsymm q₁ p, hFsymm q₂ p, F_add_left FP hFlin, map_add]

include hFlin hFsymm in
/--
@isnad1 id=eq.2h5v.s8.cb108ba1638c from=translated src=- shape=d3bdd370 vocab=b9be011b
-/
theorem F_smul_right (z : ℂ) (p q : P) : FP p (z • q) = (starRingEnd ℂ) z * FP p q := by
  rw [hFsymm (z • q) p, F_smul_left FP hFlin, map_mul, ← hFsymm q p]

include hFlin in
/--
@isnad1 id=eq.1h6v.s7.6cc7620984e7 from=translated src=- shape=00e64fba vocab=cce427fe
-/
theorem F_sum_left {ι : Type*} (s : Finset ι) (f : ι → P) (q : P) : FP (∑ i ∈ s, f i) q = ∑ i ∈ s, FP (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [F_zero_left FP hFlin]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, F_add_left FP hFlin, ih]

include hFlin hFsymm in
/--
@isnad1 id=eq.2h6v.s7.401ccfe3ba78 from=translated src=- shape=c70a908d vocab=58fa093b
-/
theorem F_sum_right {ι : Type*} (s : Finset ι) (p : P) (f : ι → P) : FP p (∑ i ∈ s, f i) = ∑ i ∈ s, FP p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rw [hFsymm 0 p, F_zero_left FP hFlin, map_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, F_add_right FP hFlin hFsymm, ih]

include hFlin hFpos in
/--
@isnad1 id=le.2h3v.s7.a9db557a5c0f from=translated src=- shape=2050e443 vocab=5d688eed
-/
theorem F_re_nonneg (p : P) : 0 ≤ (FP p p).re := by
  by_cases hp : p = 0
  · rw [hp, F_zero_left FP hFlin]; simp
  · exact (hFpos p hp).le

def BT (e : Module.Basis (Fin r) ℂ W) (x y : P ⊗[ℂ] W) : ℂ := ∑ k : Fin r, FP (coord e x k) (coord e y k)

include hFlin in
/--
@isnad1 id=eq.1h9v.s8.85a1c1f34d48 from=translated src=- shape=75da5e77 vocab=4b0d7373
-/
theorem BT_lin (e : Module.Basis (Fin r) ℂ W) (z : ℂ) (x₁ x₂ y : P ⊗[ℂ] W) :
    BT FP e (z • x₁ + x₂) y = z * BT FP e x₁ y + BT FP e x₂ y := by
  simp only [BT, map_add, map_smul, Pi.add_apply, Pi.smul_apply, hFlin, Finset.sum_add_distrib, Finset.mul_sum]

include hFsymm in
/--
@isnad1 id=eq.1h7v.s7.44b0993014e5 from=translated src=- shape=e74a6e40 vocab=44243bb6
-/
theorem BT_symm (e : Module.Basis (Fin r) ℂ W) (x y : P ⊗[ℂ] W) : BT FP e y x = (starRingEnd ℂ) (BT FP e x y) := by
  simp only [BT, map_sum]
  exact Finset.sum_congr rfl (fun k _ => hFsymm _ _)

include hFlin hFpos in
/--
@isnad1 id=lt.3h6v.s8.67fcaaffee0d from=translated src=- shape=02381b39 vocab=f67fa194
-/
theorem BT_pos (e : Module.Basis (Fin r) ℂ W) (x : P ⊗[ℂ] W) (hx : x ≠ 0) : 0 < (BT FP e x x).re := by
  have hne : coord e x ≠ 0 := fun h => hx ((coord e).map_eq_zero_iff.mp h)
  obtain ⟨k, hk⟩ : ∃ k, coord e x k ≠ 0 := by
    by_contra h; push_neg at h; exact hne (funext h)
  simp only [BT, Complex.re_sum]
  refine lt_of_lt_of_le (hFpos _ hk) ?_
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  have : 0 ≤ ∑ i ∈ Finset.univ.erase k, (FP (coord e x i) (coord e x i)).re :=
    Finset.sum_nonneg (fun i _ => F_re_nonneg FP hFlin hFpos _)
  linarith

include hFlin hFsymm in

/--
@isnad1 id=eq.3h8v.s9.91a75372aa43 from=translated src=- shape=f1d83b3c vocab=ce50482f
-/
theorem BT_skew_left (e : Module.Basis (Fin r) ℂ W) (f : P →ₗ[ℂ] P) (hf : ∀ p q : P, FP (f p) q = -FP p (f q))
    (x y : P ⊗[ℂ] W) :
    BT FP e (TensorProduct.map f LinearMap.id x) y = -BT FP e x (TensorProduct.map f LinearMap.id y) := by
  simp only [BT, coord_map_left, hf, Finset.sum_neg_distrib]

include hFlin hFsymm in

/--
@isnad1 id=eq.6h9v.s10.3f51a362e972 from=translated src=- shape=00da896e vocab=7a37f9f6
-/
theorem BT_skew_right (e : Module.Basis (Fin r) ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (horth : ∀ i j : Fin r, B (e i) (e j) = if i = j then 1 else 0)
    (g : W →ₗ[ℂ] W) (hg : ∀ x y : W, B (g x) y = -B x (g y)) (x y : P ⊗[ℂ] W) :
    BT FP e (TensorProduct.map LinearMap.id g x) y = -BT FP e x (TensorProduct.map LinearMap.id g y) := by

  have hB0 : ∀ w' : W, B 0 w' = 0 := by
    intro w'; have h := hlin (-1) 0 0 w'; rw [smul_zero, add_zero] at h; linear_combination h
  have hBadd : ∀ x y w' : W, B (x + y) w' = B x w' + B y w' := by
    intro x y w'; have h := hlin 1 x y w'; rw [one_smul, one_mul] at h; exact h
  have hBsmul : ∀ (z : ℂ) (x w' : W), B (z • x) w' = z * B x w' := by
    intro z x w'; have h := hlin z x 0 w'; rw [add_zero, hB0, add_zero] at h; exact h
  have hrepr : ∀ (w : W) (j : Fin r), e.repr w j = B w (e j) := by
    intro w j
    conv_rhs => rw [← e.sum_repr w]
    have : ∀ s : Finset (Fin r), B (∑ i ∈ s, e.repr w i • e i) (e j) = ∑ i ∈ s, e.repr w i * B (e i) (e j) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [hB0]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hBadd, hBsmul, ih]
    rw [this]
    simp [horth, Finset.sum_ite_eq']
  have hc : ∀ k l : Fin r, (starRingEnd ℂ) (e.repr (g (e k)) l) = -e.repr (g (e l)) k := by
    intro k l
    rw [hrepr, hrepr, ← hsymm, hg, neg_neg]
  simp only [BT, coord_map_right, F_sum_left FP hFlin, F_sum_right FP hFlin hFsymm, F_smul_left FP hFlin,
    F_smul_right FP hFlin hFsymm, hc, neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_comm, neg_neg]

end Form
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split

end WsB.TFT
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split

set_option autoImplicit false

open scoped TensorProduct

namespace WsB
namespace TFC

open MvPolynomial

noncomputable section

abbrev admIdx : Type := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}
abbrev P : Type := MvPolynomial admIdx ℂ

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def S (N : ℕ) : Submodule ℂ (P ⊗[ℂ] W) :=
  Submodule.span ℂ {x : P ⊗[ℂ] W | ∃ (q : P) (w : W), q.IsHomogeneous N ∧ x = q ⊗ₜ[ℂ] w}

/--
@isnad1 id=mem.1h4v.s8.77051c201c63 from=translated src=- shape=50433d3b vocab=34b6587b
-/
theorem tmul_mem_S {N : ℕ} {q : P} (hq : q.IsHomogeneous N) (w : W) : q ⊗ₜ[ℂ] w ∈ S (W := W) N :=
  Submodule.subset_span ⟨q, w, hq, rfl⟩

/--
@isnad1 id=le.0h1v.s7.069926864c4e from=translated src=- shape=4f77b44a vocab=6c0c33ae
-/
theorem homogeneousSubmodule_le_restrictTotalDegree (n : ℕ) :
    homogeneousSubmodule admIdx ℂ n ≤ restrictTotalDegree admIdx ℂ n := by
  intro p hp
  rw [mem_restrictTotalDegree]
  by_cases h0 : p = 0
  · simp [h0]
  · exact ((mem_homogeneousSubmodule n p).1 hp).totalDegree h0 |>.le

/--
@isnad1 id=finite.0h1v.s7.1d02122565df from=translated src=- shape=7901a591 vocab=75a3f35c
-/
scoped instance finite_homogeneousSubmodule (n : ℕ) : Module.Finite ℂ (homogeneousSubmodule admIdx ℂ n) :=
  Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

/--
@isnad1 id=le.0h2v.s10.d38724030a8f from=translated src=- shape=b5943ca7 vocab=58ec9383
-/
theorem S_le_range (N : ℕ) :
    S (W := W) N ≤ LinearMap.range (TensorProduct.map (homogeneousSubmodule admIdx ℂ N).subtype
      (LinearMap.id : W →ₗ[ℂ] W)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨q, w, hq, rfl⟩
  exact ⟨(⟨q, (mem_homogeneousSubmodule N q).2 hq⟩ : homogeneousSubmodule admIdx ℂ N) ⊗ₜ[ℂ] w,
    by rw [TensorProduct.map_tmul]; rfl⟩

/--
@isnad1 id=finite.0h2v.s9.c8d309ffd074 from=translated src=- shape=952e4f9b vocab=39e62da4
-/
theorem finite_S [Module.Finite ℂ W] (N : ℕ) : Module.Finite ℂ (S (W := W) N) := by
  haveI : Module.Finite ℂ (LinearMap.range (TensorProduct.map (homogeneousSubmodule admIdx ℂ N).subtype
      (LinearMap.id : W →ₗ[ℂ] W))) := inferInstance
  exact Submodule.finiteDimensional_of_le (S_le_range N)

variable (D : Fin 3 → Fin 3 → Derivation ℂ P P) (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))

def θ (i j : Fin 3) : P ⊗[ℂ] W →ₗ[ℂ] P ⊗[ℂ] W :=
  TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (D i j).toLinearMap LinearMap.id

/--
@isnad1 id=eq.0h7v.s10.15f9a7656efd from=translated src=- shape=dbf61f8d vocab=6215d8f3
-/
theorem θ_tmul (i j : Fin 3) (q : P) (w : W) :
    θ D ρ i j (q ⊗ₜ[ℂ] w) = q ⊗ₜ[ℂ] (ρ i j w) - (D i j q) ⊗ₜ[ℂ] w := by
  simp only [θ, LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

/--
@isnad1 id=mem.2h7v.s10.66e83f2159c3 from=translated src=- shape=e593ba5b vocab=bd7e58be
-/
theorem theta_mapsTo (hD : ∀ (i j : Fin 3) (N : ℕ) (q : P), q.IsHomogeneous N → (D i j q).IsHomogeneous N)
    (i j : Fin 3) (N : ℕ) : ∀ x ∈ S (W := W) N, θ D ρ i j x ∈ S (W := W) N := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, w, hq, rfl⟩ := hy
    rw [θ_tmul]
    exact sub_mem (tmul_mem_S hq _) (tmul_mem_S (hD i j N q hq) _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul z a _ ha => rw [map_smul]; exact Submodule.smul_mem _ z ha

def Y : Matrix (Fin 3) (Fin 3) P :=
  Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
def K (i j : Fin 3) : Matrix (Fin 3) (Fin 3) P := Matrix.single i j 1 - Matrix.single j i 1
def Dc (i j : Fin 3) : Derivation ℂ P P := MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2

/--
@isnad1 id=ishomoge.1h3v.s9.3a280308a0c3 from=translated src=- shape=b4a2b991 vocab=3d7b4270
-/
theorem isHomogeneous_derivation_monomial {σ : Type*}
    (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hδ : ∀ x : σ, (δ (X x)).IsHomogeneous 1) (μ : σ →₀ ℕ) :
    (δ (monomial μ (1 : ℂ))).IsHomogeneous (μ.degree) := by
  classical
  induction μ using Finsupp.induction with
  | zero =>
    rw [monomial_zero', C_1, Derivation.map_one_eq_zero]
    exact isHomogeneous_zero σ ℂ _
  | single_add a b f ha hb ih =>
    rw [monomial_single_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul,
      (map_add Finsupp.degree), Finsupp.degree_single]
    refine IsHomogeneous.add ?_ ?_
    · exact (isHomogeneous_X_pow a b).mul ih
    · rw [add_comm b (Finsupp.degree f)]
      refine (isHomogeneous_monomial _ rfl).mul ?_
      rw [nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
      have h2 : ((b : MvPolynomial σ ℂ) * X a ^ (b - 1)).IsHomogeneous (b - 1) := by
        have := (isHomogeneous_X_pow (R := ℂ) a (b - 1)).C_mul (b : ℂ)
        simpa using this
      have h3 := h2.mul (hδ a)
      rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hb)] at h3

/--
@isnad1 id=ishomoge.2h4v.s9.fa4c61acee87 from=translated src=- shape=841417dd vocab=9fd27fcf
-/
theorem isHomogeneous_derivation {σ : Type*} (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hδ : ∀ x : σ, (δ (X x)).IsHomogeneous 1) {n : ℕ} {p : MvPolynomial σ ℂ} (hp : p.IsHomogeneous n) :
    (δ p).IsHomogeneous n := by
  classical
  rw [p.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun μ hμ => ?_
  have hdeg : μ.degree = n := by
    rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 hμ)
  have hc : (monomial μ) (coeff μ p) = C (coeff μ p) * (monomial μ (1 : ℂ) : MvPolynomial σ ℂ) := by
    rw [C_mul_monomial, mul_one]
  rw [hc, C_mul', δ.map_smul, smul_eq_C_mul, ← hdeg]
  exact (isHomogeneous_derivation_monomial δ hδ μ).C_mul _

/--
@isnad1 id=ishomoge.0h2v.s4.6ea5d1ecd720 from=translated src=- shape=6da1cd60 vocab=da3c436e
-/
theorem isHomogeneous_Y (a b : Fin 3) : (Y a b).IsHomogeneous 1 := by
  unfold Y
  simp only [Matrix.of_apply]
  split_ifs <;> exact isHomogeneous_X ℂ _

/--
@isnad1 id=ishomoge.0h4v.s8.7d2204834bee from=translated src=- shape=f7e45517 vocab=862131ac
-/
theorem isHomogeneous_KY_sub_YK (i j a b : Fin 3) : ((K i j * Y - Y * K i j) a b).IsHomogeneous 1 := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, K, Matrix.sub_apply, Fin.sum_univ_three, Matrix.single_apply]

  refine IsHomogeneous.sub ?_ ?_ <;>
    refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_ <;>
    first
      | (refine (zero_add 1) ▸ IsHomogeneous.mul ?_ (isHomogeneous_Y _ _); split_ifs <;> simp <;>
          first | exact isHomogeneous_one admIdx ℂ | exact isHomogeneous_zero admIdx ℂ 0
                | exact (isHomogeneous_one admIdx ℂ).neg | exact ((isHomogeneous_one admIdx ℂ).sub (isHomogeneous_one admIdx ℂ)) )
      | (refine (add_zero 1) ▸ IsHomogeneous.mul (isHomogeneous_Y _ _) ?_; split_ifs <;> simp <;>
          first | exact isHomogeneous_one admIdx ℂ | exact isHomogeneous_zero admIdx ℂ 0
                | exact (isHomogeneous_one admIdx ℂ).neg | exact ((isHomogeneous_one admIdx ℂ).sub (isHomogeneous_one admIdx ℂ)) )

/--
@isnad1 id=ishomoge.1h4v.s7.9530b930c0cd from=translated src=- shape=ea95723e vocab=bab9686c
-/
theorem Dc_isHomogeneous (i j : Fin 3) (N : ℕ) (q : P) (hq : q.IsHomogeneous N) : (Dc i j q).IsHomogeneous N := by
  refine isHomogeneous_derivation (Dc i j) (fun v => ?_) hq
  rw [Dc, mkDerivation_X]
  exact isHomogeneous_KY_sub_YK i j _ _

/--
@isnad1 id=eq.0h7v.s11.aaef0f063544 from=translated src=- shape=a456ebda vocab=5dbfac2f
-/
theorem θθ_tmul (i j : Fin 3) (q : P) (w : W) :
    θ D ρ i j (θ D ρ i j (q ⊗ₜ[ℂ] w)) =
      q ⊗ₜ[ℂ] (ρ i j (ρ i j w)) - ((D i j q) ⊗ₜ[ℂ] (ρ i j w) + (D i j q) ⊗ₜ[ℂ] (ρ i j w)) +
        (D i j (D i j q)) ⊗ₜ[ℂ] w := by
  rw [θ_tmul, map_sub, θ_tmul, θ_tmul]
  abel

/--
@isnad1 id=eq.1h5v.s12.e35d5099967e from=translated src=- shape=790033c0 vocab=e331141c
-/
theorem Omega_add_two_tmul
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x)) (q : P) (w : W) :
    (θ D ρ 0 1 ∘ₗ θ D ρ 0 1 + θ D ρ 0 2 ∘ₗ θ D ρ 0 2 + θ D ρ 1 2 ∘ₗ θ D ρ 1 2) (q ⊗ₜ[ℂ] w) + (2 : ℂ) • (q ⊗ₜ[ℂ] w) =
      ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
      ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
      ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w))) := by
  have hsum : q ⊗ₜ[ℂ] (ρ 0 1 (ρ 0 1 w)) + q ⊗ₜ[ℂ] (ρ 0 2 (ρ 0 2 w)) + q ⊗ₜ[ℂ] (ρ 1 2 (ρ 1 2 w)) +
      (2 : ℂ) • (q ⊗ₜ[ℂ] w) = 0 := by
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add,
      hcas, neg_add_cancel, TensorProduct.tmul_zero]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, θθ_tmul]
  rw [← sub_eq_zero, ← hsum]
  abel

end
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split

end WsB.TFC
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace WsB
namespace TFmain

open SymRestriction FischerForm S5Split WsB.TF WsB.TFT

/--
@isnad1 id=ex.3h2v.s8.29f4acb596f4 from=translated src=- shape=8ffd56e1 vocab=2c355d83
-/
theorem exists_orthonormal_basis (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ W), ∀ i j : Fin n, B (b i) (b j) = if i = j then 1 else 0 := by
  classical
  have hB0 : ∀ w' : W, B 0 w' = 0 := by
    intro w'; have h := hlin (-1) 0 0 w'; rw [smul_zero, add_zero] at h; linear_combination h
  have hadd : ∀ x y w' : W, B (x + y) w' = B x w' + B y w' := by
    intro x y w'; have h := hlin 1 x y w'; rw [one_smul, one_mul] at h; exact h
  have hsmul : ∀ (z : ℂ) (x w' : W), B (z • x) w' = z * B x w' := by
    intro z x w'; have h := hlin z x 0 w'; rw [add_zero, hB0, add_zero] at h; exact h
  let core : InnerProductSpace.Core ℂ W :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (B x y) = B y x
        rw [hsymm x y]
      re_inner_nonneg := fun x => by
        show 0 ≤ (B x x).re
        by_cases hx : x = 0
        · rw [hx, hB0]; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show B z (x + y) = B z x + B z y
        rw [hsymm (x + y) z, hsymm x z, hsymm y z, hadd, map_add]
      smul_left := fun x y r => by
        show B y (r • x) = (starRingEnd ℂ) r * B y x
        rw [hsymm (r • x) y, hsmul, map_mul, ← hsymm x y]
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        have hx' : B x x = 0 := hx
        rw [hx', Complex.zero_re] at this
        exact lt_irrefl _ this }
  letI ipc : InnerProductSpace.Core ℂ W := core
  letI : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := W)
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore (𝕜 := ℂ) (F := W) ipc.toCore
  let ob := stdOrthonormalBasis ℂ W
  refine ⟨Module.finrank ℂ W, ob.toBasis, fun i j => ?_⟩
  have h := ob.orthonormal
  rw [orthonormal_iff_ite] at h
  have hij := h i j
  change B (ob j) (ob i) = _ at hij
  rw [OrthonormalBasis.coe_toBasis]
  rw [hsymm (ob j) (ob i), hij]
  split_ifs <;> simp

/--
@isnad1 id=ex.4h3v.s12.71be0bea11e9 from=translated src=- shape=c0b106a0 vocab=a5a1846d
-/
theorem form_part (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y)) :
    ∃ B' : admP ⊗[ℂ] W → admP ⊗[ℂ] W → ℂ,
      (∀ (z : ℂ) (w₁ w₂ w' : admP ⊗[ℂ] W), B' (z • w₁ + w₂) w' = z * B' w₁ w' + B' w₂ w') ∧
      (∀ w w' : admP ⊗[ℂ] W, B' w' w = (starRingEnd ℂ) (B' w w')) ∧
      (∀ w : admP ⊗[ℂ] W, w ≠ 0 → 0 < (B' w w).re) ∧
      (∀ (i j : Fin 3) (w w' : admP ⊗[ℂ] W),
        B' ((TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (admD i j).toLinearMap LinearMap.id :
            admP ⊗[ℂ] W →ₗ[ℂ] admP ⊗[ℂ] W) w) w' =
          -B' w ((TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (admD i j).toLinearMap LinearMap.id :
            admP ⊗[ℂ] W →ₗ[ℂ] admP ⊗[ℂ] W) w')) := by
  obtain ⟨r, e, horth⟩ := exists_orthonormal_basis W B hlin hsymm hpos
  refine ⟨BT FP e, BT_lin FP FP_lin e, BT_symm FP FP_symm e, BT_pos FP FP_lin FP_pos e, ?_⟩
  intro i j w w'
  have hsubL : ∀ x₁ x₂ y : admP ⊗[ℂ] W, BT FP e (x₁ - x₂) y = BT FP e x₁ y - BT FP e x₂ y := by
    intro x₁ x₂ y
    rw [sub_eq_add_neg, add_comm, ← neg_one_smul ℂ x₂, BT_lin FP FP_lin e]; ring
  have hsubR : ∀ x y₁ y₂ : admP ⊗[ℂ] W, BT FP e x (y₁ - y₂) = BT FP e x y₁ - BT FP e x y₂ := by
    intro x y₁ y₂
    rw [BT_symm FP FP_symm e (y₁ - y₂) x, hsubL, map_sub, ← BT_symm FP FP_symm e y₁ x, ← BT_symm FP FP_symm e y₂ x]
  rw [LinearMap.sub_apply, LinearMap.sub_apply, hsubL, hsubR,
    BT_skew_right FP FP_lin FP_symm e B hlin hsymm horth (ρ i j) (hskew i j),
    BT_skew_left FP FP_lin FP_symm e (admD i j).toLinearMap (fun p q => FP_D_skew i j p q)]
  ring

end WsB.TFmain
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB
open scoped _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.FischerForm _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.S5Split _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul.WsB

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=other.6h4v.s17.b4b54aeb58f4 from=translated src=- shape=aeef7815 vocab=f07ebd58
-/
theorem solution
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (hanti : ∀ (i j : Fin 3) (x : W), ρ j i x = -ρ i j x)
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y))
    (N : ℕ) :
    let Y : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
    let K : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => Matrix.single i j 1 - Matrix.single j i 1
    let D : Fin 3 → Fin 3 →
        Derivation ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)
          (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2
    let θ : Fin 3 → Fin 3 → (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W →ₗ[ℂ] MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :=
      fun i j => TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (D i j).toLinearMap LinearMap.id
    let S : Submodule ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W) :=
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W | ∃ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W), q.IsHomogeneous N ∧ x = q ⊗ₜ[ℂ] w}
    Module.Finite ℂ S ∧
    (∀ i j : Fin 3, ∀ x ∈ S, θ i j x ∈ S) ∧
    (∃ B' : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W → MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W → ℂ,
      (∀ (z : ℂ), ∀ w₁ ∈ S, ∀ w₂ ∈ S, ∀ w' ∈ S, B' (z • w₁ + w₂) w' = z * B' w₁ w' + B' w₂ w') ∧
      (∀ w ∈ S, ∀ w' ∈ S, B' w' w = (starRingEnd ℂ) (B' w w')) ∧
      (∀ w ∈ S, w ≠ 0 → 0 < (B' w w).re) ∧
      (∀ i j : Fin 3, ∀ w ∈ S, ∀ w' ∈ S, B' (θ i j w) w' = -B' w (θ i j w'))) ∧
    (∀ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W),
      (θ 0 1 ∘ₗ θ 0 1 + θ 0 2 ∘ₗ θ 0 2 + θ 1 2 ∘ₗ θ 1 2) (q ⊗ₜ[ℂ] w) + (2 : ℂ) • (q ⊗ₜ[ℂ] w) =
        ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
        ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
        ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w)))) := by
  intro Y K D θ S
  obtain ⟨B', h1, h2, h3, h4⟩ := WsB.TFmain.form_part W ρ B hlin hsymm hpos hskew
  refine ⟨?_, ?_, ⟨B', fun z w₁ _ w₂ _ w' _ => h1 z w₁ w₂ w', fun w _ w' _ => h2 w w', fun w _ hw => h3 w hw,
    fun i j w _ w' _ => h4 i j w w'⟩, ?_⟩
  · exact WsB.TFC.finite_S N
  · intro i j x hx
    exact WsB.TFC.theta_mapsTo D ρ (fun i j N q hq => WsB.TFC.Dc_isHomogeneous i j N q hq) i j N x hx
  · intro q w
    exact WsB.TFC.Omega_add_two_tmul D ρ hcas q w
