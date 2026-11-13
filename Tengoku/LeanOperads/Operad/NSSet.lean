/-
# Non-symmetric set operads, and linearization

The planar counterpart of `Operad.SetOperad`: a non-symmetric operad in sets, in the positional
arity convention of `Operad.Basic` (`comp a b : S (a+1+b) → S n → S (a+n+b)`), with reindexing
along equalities of arities (`reindexS`) in place of `reindex`. Its linearization `LinNS R S`,
`n ↦ S n →₀ R`, is a non-symmetric operad in `R`-modules (`instNSOperadLinNS`).

A symmetric set operad has an underlying non-symmetric one on the standard finite types
(`SetOperad.toNSSet`); its axioms are those of `SymOperad.toNS` on the linearization, transported
back along the injectivity of `Finsupp.single`.
-/
import Tengoku.LeanOperads.Operad.SetOperad
import Tengoku.LeanOperads.Operad.SymNS

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace Operad

/-! ## Reindexing -/

section ReindexS

variable (S : ℕ → Type v)

/-- Transport along an equality of arities.-/
def reindexS {m n : ℕ} (h : m = n) : S m → S n := fun x => h ▸ x

variable {S}

/--
@isnad1 id=eq.1h3v.s4.47e9eed47568 from=translated src=- shape=c3d438c9 vocab=b85719cc
-/
@[simp] lemma reindexS_self {n : ℕ} (h : n = n) (x : S n) : reindexS S h x = x := rfl

/--
@isnad1 id=eq.2h5v.s5.d3d508da11c8 from=translated src=- shape=c139886a vocab=06035878
-/
@[simp] lemma reindexS_reindexS {l m n : ℕ} (h₁ : l = m) (h₂ : m = n) (x : S l) :
    reindexS S h₂ (reindexS S h₁ x) = reindexS S (h₁.trans h₂) x := by
  subst h₁; subst h₂; rfl

/--
@isnad1 id=injectiv.1h3v.s4.5d06de1dbe70 from=translated src=- shape=00720d9d vocab=dd6c95fb
-/
lemma reindexS_injective {m n : ℕ} (h : m = n) : Function.Injective (reindexS S h) := by
  subst h; exact fun _ _ h => h

/--
@isnad1 id=iff.1h5v.s5.6a4a8d238e92 from=translated src=- shape=bcb90e10 vocab=f03e4d1e
-/
lemma reindexS_symm_eq {m n : ℕ} (h : m = n) (x : S m) (y : S n) :
    reindexS S h x = y ↔ x = reindexS S h.symm y := by
  subst h; exact Iff.rfl

end ReindexS

/-- **A non-symmetric set operad**, in the positional arity convention. The axioms are those of
`NSOperad`, for functions.-/
class NSSetOperad (S : ℕ → Type v) where
  /-- The identity operation.-/
  one : S 1
  /-- Insert an arity-`n` operation into the slot with `a` inputs before it and `b` after.-/
  comp (a b : ℕ) {n : ℕ} : S (a + 1 + b) → S n → S (a + n + b)
  comp_one_right (a b : ℕ) (α : S (a + 1 + b)) : comp a b α one = α
  comp_one_left {n : ℕ} (α : S n) : reindexS S (by omega) (comp 0 0 one α) = α
  comp_assoc_seq (a b c d : ℕ) {p : ℕ} (α : S (a + 1 + b)) (β : S (c + 1 + d)) (γ : S p) :
    reindexS S (by omega)
        (comp (a + c) (d + b) (reindexS S (by omega) (comp a b α β)) γ)
      = comp a b α (comp c d β γ)
  comp_assoc_par (a b c : ℕ) {n p : ℕ} (α : S (a + 1 + b + 1 + c)) (β : S n) (γ : S p) :
    reindexS S (by omega)
        (comp (a + n + b) c
          (reindexS S (by omega) (comp a (b + 1 + c) (reindexS S (by omega) α) β)) γ)
      = comp a (b + p + c) (reindexS S (by omega) (comp (a + 1 + b) c α γ)) β

/-- **A morphism of non-symmetric set operads.**-/
structure NSSetOperadHom (S : ℕ → Type v) (T : ℕ → Type w) [NSSetOperad S] [NSSetOperad T] where
  /-- The component at an arity.-/
  app (n : ℕ) : S n → T n
  app_one : app 1 NSSetOperad.one = NSSetOperad.one
  app_comp (a b : ℕ) {n : ℕ} (α : S (a + 1 + b)) (β : S n) :
    app (a + n + b) (NSSetOperad.comp a b α β) = NSSetOperad.comp a b (app _ α) (app n β)

namespace NSSetOperadHom

variable {S : ℕ → Type v} {T : ℕ → Type w} [NSSetOperad S] [NSSetOperad T]

/--
@isnad1 id=eq.1h4v.s5.3896ffd171d8 from=translated src=- shape=9fdc65aa vocab=f2654ae4
-/
@[ext] lemma ext {φ ψ : NSSetOperadHom S T} (h : ∀ n (x : S n), φ.app n x = ψ.app n x) :
    φ = ψ := by
  obtain ⟨φa, _, _⟩ := φ
  obtain ⟨ψa, _, _⟩ := ψ
  have : φa = ψa := funext fun n => funext (h n)
  subst this
  rfl

/-- Components commute with reindexing.
@isnad1 id=eq.1h6v.s5.80007c6be644 from=translated src=- shape=d7bf859b vocab=7cfb43c1
-/
lemma app_reindexS (φ : NSSetOperadHom S T) {m n : ℕ} (h : m = n) (x : S m) :
    φ.app n (reindexS S h x) = reindexS T h (φ.app m x) := by
  subst h; rfl

/-- The identity morphism.-/
def id : NSSetOperadHom S S where
  app _ x := x
  app_one := rfl
  app_comp := by intros; rfl

variable {U : ℕ → Type*} [NSSetOperad U]

/-- The composite of two morphisms.-/
def comp (ψ : NSSetOperadHom T U) (φ : NSSetOperadHom S T) : NSSetOperadHom S U where
  app n x := ψ.app n (φ.app n x)
  app_one := by rw [φ.app_one, ψ.app_one]
  app_comp := by
    intro a b n α β
    show ψ.app _ (φ.app _ _) = _
    rw [φ.app_comp, ψ.app_comp]

end NSSetOperadHom

/-- **An isomorphism of non-symmetric set operads.**-/
structure NSSetOperadIso (S : ℕ → Type v) (T : ℕ → Type w) [NSSetOperad S] [NSSetOperad T] where
  /-- The forward morphism.-/
  hom : NSSetOperadHom S T
  /-- The inverse morphism.-/
  inv : NSSetOperadHom T S
  hom_inv_id : inv.comp hom = NSSetOperadHom.id
  inv_hom_id : hom.comp inv = NSSetOperadHom.id

namespace NSSetOperadHom

variable {S : ℕ → Type v} {T : ℕ → Type w} [NSSetOperad S] [NSSetOperad T]

/-- **The inverse of a bijective morphism** is a morphism.-/
noncomputable def invOfBijective (φ : NSSetOperadHom S T) (h : ∀ n, Function.Bijective (φ.app n)) :
    NSSetOperadHom T S where
  app n := (Equiv.ofBijective _ (h n)).symm
  app_one := by
    apply (h 1).1
    rw [Equiv.ofBijective_apply_symm_apply (φ.app 1) (h 1), φ.app_one]
  app_comp a b n x y := by
    apply (h _).1
    rw [Equiv.ofBijective_apply_symm_apply (φ.app _) (h _), φ.app_comp,
      Equiv.ofBijective_apply_symm_apply (φ.app _) (h _),
      Equiv.ofBijective_apply_symm_apply (φ.app _) (h _)]

end NSSetOperadHom

/-- **A bijective morphism is an isomorphism.**-/
noncomputable def NSSetOperadIso.ofBijective {S : ℕ → Type v} {T : ℕ → Type w} [NSSetOperad S]
    [NSSetOperad T] (φ : NSSetOperadHom S T) (h : ∀ n, Function.Bijective (φ.app n)) :
    NSSetOperadIso S T where
  hom := φ
  inv := φ.invOfBijective h
  hom_inv_id := by
    ext n x
    exact Equiv.ofBijective_symm_apply_apply _ (h n) x
  inv_hom_id := by
    ext n x
    exact Equiv.ofBijective_apply_symm_apply _ (h n) x

/-! ## Linearization -/

/-- **The linearization of a non-symmetric set operad.**-/
abbrev LinNS (R : Type u) [CommRing R] (S : ℕ → Type v) : ℕ → Type (max u v) :=
  fun n => S n →₀ R

namespace LinNS

variable (R : Type u) [CommRing R] {S : ℕ → Type v} [NSSetOperad S]

/-- Composition, extended bilinearly.-/
noncomputable def compL (a b : ℕ) {n : ℕ} :
    (S (a + 1 + b) →₀ R) →ₗ[R] (S n →₀ R) →ₗ[R] (S (a + n + b) →₀ R) :=
  Finsupp.lift ((S n →₀ R) →ₗ[R] (S (a + n + b) →₀ R)) R (S (a + 1 + b))
    (fun s => Finsupp.lmapDomain R R (NSSetOperad.comp a b s))

variable {R}

/--
@isnad1 id=eq.0h9v.s11.57656a2ad91d from=translated src=- shape=bfa91a04 vocab=a79cc2d5
-/
@[simp] lemma compL_single (a b : ℕ) {n : ℕ} (s : S (a + 1 + b)) (t : S n) (r r' : R) :
    compL R a b (Finsupp.single s r) (Finsupp.single t r')
      = Finsupp.single (NSSetOperad.comp a b s t) (r * r') := by
  simp [compL, Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul]

omit [NSSetOperad S] in
/--
@isnad1 id=eq.1h6v.s9.b802193590a1 from=translated src=- shape=04456b51 vocab=1a6c4060
-/
@[simp] lemma reindex_single {m n : ℕ} (h : m = n) (s : S m) (r : R) :
    reindex R (LinNS R S) h (Finsupp.single s r) = Finsupp.single (reindexS S h s) r := by
  subst h; rfl

end LinNS

/-- **The linearization of a non-symmetric set operad is a non-symmetric operad in `R`-modules.**-/
noncomputable instance instNSOperadLinNS (R : Type u) [CommRing R] (S : ℕ → Type v)
    [NSSetOperad S] : NSOperad R (LinNS R S) where
  one := Finsupp.single NSSetOperad.one 1
  comp a b := LinNS.compL R a b
  comp_one_right a b x := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r => rw [LinNS.compL_single, NSSetOperad.comp_one_right, mul_one]
  comp_one_left x := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | single s r =>
      rw [LinNS.compL_single, LinNS.reindex_single, NSSetOperad.comp_one_left, one_mul]
  comp_assoc_seq a b c d p x y z := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | single t r' =>
        induction z using Finsupp.induction_linear with
        | zero => simp
        | add z z' hz hz' => simp only [map_add, hz, hz']
        | single w r'' =>
          simp only [LinNS.compL_single, LinNS.reindex_single, NSSetOperad.comp_assoc_seq,
            mul_assoc]
  comp_assoc_par a b c n p x y z := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single s r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | single t r' =>
        induction z using Finsupp.induction_linear with
        | zero => simp
        | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
        | single w r'' =>
          simp only [LinNS.compL_single, LinNS.reindex_single, NSSetOperad.comp_assoc_par]
          congr 1
          ring

/-! ## The underlying non-symmetric set operad of a symmetric one -/

namespace SetOperad

open Sym

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

/-- **The underlying non-symmetric collection**: the components on the standard finite types.-/
def toNSSet (S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) : ℕ → Type v :=
  fun n => S (Fin n)

/-- Positional composition: compose at the input `a`, then list the inputs in order.-/
def nsCompSet (a b : ℕ) {n : ℕ} (x : S (Fin (a + 1 + b))) (y : S (Fin n)) :
    S (Fin (a + n + b)) :=
  map (insertEquiv a b n) (comp (⟨a, by omega⟩ : Fin (a + 1 + b)) x y)

/-- The unit, on the one-element `Fin`.-/
def nsOneSet : S (Fin 1) := map unitFinOne one

/-! The axioms are transported from the linearization over `ℤ`, where `Operad.SymNS` proves
them, along the injectivity of `Finsupp.single`. -/

/--
@isnad1 id=eq.0h1v.s7.20ee3cc4cd1d from=translated src=- shape=88dbd059 vocab=de4166ea
-/
lemma single_nsOneSet :
    (Finsupp.single (α := S (Fin 1)) (nsOneSet (S := S)) (1 : ℤ))
      = SymOperad.nsOne (R := ℤ) (P := Lin ℤ S) := by
  show _ = Lin.mapL ℤ _ (Finsupp.single one 1)
  rw [Lin.mapL_single]
  rfl

end SetOperad

end Operad
