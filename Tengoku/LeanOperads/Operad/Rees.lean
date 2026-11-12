/-
# Weighted set operads: the associated graded and the Rees family

A **weight** on a set operad `S` (`SetOperadWeight`) is invariant under relabelling, zero on the
unit and subadditive under composition; it filters the linearization (`weightFiltration`). The
**defect** of a composite is the weight it drops, `w s + w t - w (s ∘ᵢ t)`, and it is additive
along both kinds of iterated composite (`defect_assoc_seq`, `defect_assoc_par`).

For every `h : R` this gives the **twisted linearization** `TwLin R W h`: the free modules
`S A →₀ R`, with composition

  `s ∘ᵢ t = h ^ (w s + w t - w (s ∘ᵢ t)) • (s ∘ᵢ t)`.

It is filtered by the same weight (`TwLin.filtration`), and its three instances are

* `h = 1`: the linearization (`TwLin.isoLin : TwLin R W 1 ≅ Lin R S`);
* `h = 0`: **the associated graded** `Gr R W` of the weight filtration, in which the composites that
  drop weight vanish and the others are the composites of `S` (`Gr.comp_single`);
* `h = X` over `R[X]`: **the Rees family**. In the basis `s ↦ Xʷ⁽ˢ⁾ s` of the classical Rees
  module `⊕ₚ Fₚ Xᵖ` the composition is exactly this one. Its specialization at `X = c`
  (`TwLin.specialize`) is a morphism of the underlying set operads onto `TwLin R W c`,
  semilinear along `Polynomial.eval c`, whose kernel is `(X - c)` times the family
  (`TwLin.specializeL_eq_zero_iff`): the fiber at `c = 1` is the linearization and the fiber at
  `c = 0` is the associated graded.

Morphisms out of a twisted linearization are built from their values on the basis
(`TwLin.liftHom`). On the associated graded, `s ↦ (-1)^{w s} s` is an involutive automorphism
(`Gr.sign`), and the weight-zero coefficient is a morphism to `Com` (`Gr.evZero`).
-/
import Tengoku.LeanOperads.Operad.Filtration
import Tengoku.LeanOperads.Operad.SymIso
import Tengoku.LeanOperads.Operad.SetBinary
import Tengoku.Seed.Algebra.Polynomial.Div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace Operad

open Sym

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

variable (S) in
/-- **A weight on a set operad**: invariant under relabelling, zero on the unit, subadditive under
composition.-/
structure SetOperadWeight where
  /-- The weight of an operation.-/
  w : ∀ (A : Type) [Fintype A] [DecidableEq A], S A → ℕ
  w_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (s : S A) : w B (SetOperad.map e s) = w A s
  w_one : w Unit SetOperad.one = 0
  w_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) (s : S A)
    (t : S B) : w _ (SetOperad.comp i s t) ≤ w A s + w B t

namespace SetOperadWeight

variable (W : SetOperadWeight S)
  {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

/-- **The filtration by the weight** of the linearization.-/
noncomputable def filtration (R : Type u) [CommRing R] : SymOperadFiltration R (Lin R S) :=
  weightFiltration R W.w W.w_map W.w_one W.w_comp

/-- **The defect of a composite**: the weight it drops.-/
def defect (i : A) (s : S A) (t : S B) : ℕ := W.w A s + W.w B t - W.w _ (SetOperad.comp i s t)

lemma w_comp_add_defect (i : A) (s : S A) (t : S B) :
    W.w _ (SetOperad.comp i s t) + W.defect i s t = W.w A s + W.w B t := by
  have := W.w_comp i s t
  unfold defect
  omega

lemma defect_eq_zero_iff (i : A) (s : S A) (t : S B) :
    W.defect i s t = 0 ↔ W.w _ (SetOperad.comp i s t) = W.w A s + W.w B t := by
  have := W.w_comp i s t
  unfold defect
  omega

omit [Fintype D] [DecidableEq D] in
lemma defect_map (σ : A ≃ A') (τ : B ≃ B') (i : A) (s : S A) (t : S B) :
    W.defect (σ i) (SetOperad.map σ s) (SetOperad.map τ t) = W.defect i s t := by
  unfold defect
  rw [← SetOperad.map_comp, W.w_map, W.w_map, W.w_map]

omit [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D] in
lemma defect_one_right (i : A) (s : S A) : W.defect i s SetOperad.one = 0 := by
  have h := congrArg (W.w A) (SetOperad.comp_one (S := S) i s)
  rw [W.w_map] at h
  unfold defect
  rw [h, W.w_one]
  omega

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
lemma defect_one_left (t : S B) : W.defect () SetOperad.one t = 0 := by
  have h := congrArg (W.w B) (SetOperad.one_comp (S := S) t)
  rw [W.w_map] at h
  unfold defect
  rw [h, W.w_one]
  omega

/-- **The defect is additive along sequential composites.**-/
lemma defect_assoc_seq (i : A) (j : B) (s : S A) (t : S B) (u : S D) :
    W.defect i s t + W.defect (Sum.inr j) (SetOperad.comp i s t) u
      = W.defect j t u + W.defect i s (SetOperad.comp j t u) := by
  have h := congrArg (W.w _) (SetOperad.comp_assoc_seq (S := S) i j s t u)
  rw [W.w_map] at h
  have h1 := W.w_comp i s t
  have h2 := W.w_comp (Sum.inr j) (SetOperad.comp i s t) u
  have h3 := W.w_comp j t u
  have h4 := W.w_comp i s (SetOperad.comp j t u)
  unfold defect
  omega

/-- **The defect is additive along parallel composites.**-/
lemma defect_assoc_par {i k : A} (hik : i ≠ k) (s : S A) (t : S B) (u : S D) :
    W.defect i s t + W.defect (Sum.inl ⟨k, Ne.symm hik⟩) (SetOperad.comp i s t) u
      = W.defect k s u + W.defect (Sum.inl ⟨i, hik⟩) (SetOperad.comp k s u) t := by
  have h := congrArg (W.w _) (SetOperad.comp_assoc_par (S := S) hik s t u)
  rw [W.w_map] at h
  have h1 := W.w_comp i s t
  have h2 := W.w_comp (Sum.inl ⟨k, Ne.symm hik⟩) (SetOperad.comp i s t) u
  have h3 := W.w_comp k s u
  have h4 := W.w_comp (Sum.inl ⟨i, hik⟩) (SetOperad.comp k s u) t
  unfold defect
  omega

end SetOperadWeight

/-! ## The twisted linearization -/

variable (R : Type u) [CommRing R]

/-- **The twisted linearization** of a weighted set operad: the free modules `S A →₀ R`, with the
composite of two operations scaled by `h` to the power of the weight it drops.-/
@[nolint unusedArguments]
def TwLin (_W : SetOperadWeight S) (_h : R) :
    (A : Type) → [Fintype A] → [DecidableEq A] → Type (max u v) :=
  fun A _ _ => S A →₀ R

namespace TwLin

variable {R} (W : SetOperadWeight S) (h : R)
  {A A' B B' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D]

noncomputable instance instAddCommGroup : AddCommGroup (TwLin R W h A) :=
  inferInstanceAs (AddCommGroup (S A →₀ R))

noncomputable instance instModule : Module R (TwLin R W h A) :=
  inferInstanceAs (Module R (S A →₀ R))

/-- The basis element of an operation, with a coefficient.-/
noncomputable def single (s : S A) (r : R) : TwLin R W h A := Finsupp.single s r

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
@[simp] lemma single_zero (s : S A) : single W h s 0 = 0 := Finsupp.single_zero s

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
@[simp] lemma smul_single (a : R) (s : S A) (r : R) :
    a • single W h s r = single W h s (a * r) := Finsupp.smul_single a s r

/-- Relabelling, extended linearly.-/
noncomputable def mapL (e : A ≃ B) : TwLin R W h A →ₗ[R] TwLin R W h B := Lin.mapL R e

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D] in
@[simp] lemma mapL_single (e : A ≃ B) (s : S A) (r : R) :
    mapL W h e (single W h s r) = single W h (SetOperad.map e s) r :=
  Lin.mapL_single e s r

/-- Composition on the free modules, twisted by the defect.-/
noncomputable def compF (i : A) :
    (S A →₀ R) →ₗ[R] (S B →₀ R) →ₗ[R] (S (Without A i ⊕ B) →₀ R) :=
  Finsupp.lift ((S B →₀ R) →ₗ[R] (S (Without A i ⊕ B) →₀ R)) R (S A) fun s =>
    Finsupp.lift (S (Without A i ⊕ B) →₀ R) R (S B) fun t =>
      Finsupp.single (SetOperad.comp i s t) (h ^ W.defect i s t)

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D] in
lemma compF_single (i : A) (s : S A) (t : S B) (r r' : R) :
    compF W h i (Finsupp.single s r) (Finsupp.single t r')
      = Finsupp.single (SetOperad.comp i s t) (h ^ W.defect i s t * (r * r')) := by
  simp only [compF, Finsupp.lift_apply, Finsupp.sum_single_index, zero_smul,
    LinearMap.smul_apply, Finsupp.smul_single, smul_eq_mul, zero_mul, Finsupp.single_zero]
  congr 1
  ring

/-- Composition, extended bilinearly and twisted by the defect.-/
noncomputable def compL (i : A) :
    TwLin R W h A →ₗ[R] TwLin R W h B →ₗ[R] TwLin R W h (Without A i ⊕ B) :=
  compF W h i

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype D] [DecidableEq D] in
@[simp] lemma compL_single (i : A) (s : S A) (t : S B) (r r' : R) :
    compL W h i (single W h s r) (single W h t r')
      = single W h (SetOperad.comp i s t) (h ^ W.defect i s t * (r * r')) :=
  compF_single W h i s t r r'

/-- The linear map out of a twisted linearization with given values on the basis.-/
noncomputable def lift {M : Type*} [AddCommGroup M] [Module R M] (f : S A → M) :
    TwLin R W h A →ₗ[R] M :=
  Finsupp.lift M R (S A) f

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype D] [DecidableEq D] in
@[simp] lemma lift_single {M : Type*} [AddCommGroup M] [Module R M] (f : S A → M) (s : S A)
    (r : R) : lift W h f (single W h s r) = r • f s := by
  show Finsupp.lift M R (S A) f (Finsupp.single s r) = r • f s
  simp

end TwLin

namespace TwLin

variable {R} (W : SetOperadWeight S) (h : R)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ### The filtration -/

/-! ### Morphisms out of a twisted linearization -/

variable {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-! ### The fiber at `h = 1`: the linearization -/

end TwLin

/-! ## The associated graded -/

/-- **The associated graded of the weight filtration**: the twisted linearization at `h = 0`, in
which the composites that drop weight vanish.-/
abbrev Gr (W : SetOperadWeight S) : (A : Type) → [Fintype A] → [DecidableEq A] → Type (max u v) :=
  TwLin R W (0 : R)

namespace Gr

variable {R} (W : SetOperadWeight S)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end Gr

/-! ## The Rees family -/

namespace TwLin

open Polynomial

variable {R} (W : SetOperadWeight S) (c : R)
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **Specialization of the Rees family at `X = c`**, on each component.-/
noncomputable def specializeL (A : Type) [Fintype A] [DecidableEq A] :
    TwLin R[X] W X A →+ TwLin R W c A :=
  Finsupp.mapRange.addMonoidHom (Polynomial.evalRingHom c).toAddMonoidHom

omit [Fintype B] [DecidableEq B] in
@[simp] lemma specializeL_single (s : S A) (p : R[X]) :
    specializeL W c A (single W X s p) = single W c s (p.eval c) :=
  Finsupp.mapRange_single (hf := (Polynomial.evalRingHom c).toAddMonoidHom.map_zero)

end TwLin

/-! ## Binary composites in a twisted linearization -/

section TwLinBin

open SetOperad

variable {R : Type u} [CommRing R] (W : SetOperadWeight S) {A B : Type} [Fintype A]
  [DecidableEq A] [Fintype B] [DecidableEq B]

end TwLinBin

end Operad
