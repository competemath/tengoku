import Tengoku

namespace OAI

noncomputable section
namespace DeligneDrinfeld

/--
@isnad1 id=var.0h9v.s7.ab4028e5a8fe from=translated src=- shape=3cb73a4e vocab=5fafbe88
-/
theorem freeLie_induction {R α : Type*} [CommRing R]
    {P : FreeLieAlgebra R α → Prop} (h0 : P 0)
    (hg : ∀ a, P (FreeLieAlgebra.of R a))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hs : ∀ (r : R) a, P a → P (r • a))
    (hl : ∀ a b, P a → P b → P ⁅a,b⁆) (q : FreeLieAlgebra R α) : P q := by
  let K : LieSubalgebra R (FreeLieAlgebra R α) :=
    { carrier := {a | P a}
      zero_mem' := h0
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      smul_mem' := fun r a h => hs r a h
      lie_mem' := fun ha' hb' => hl _ _ ha' hb' }
  let f : FreeLieAlgebra R α →ₗ⁅R⁆ K :=
    FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, hg a⟩)
  have hf : K.incl.comp f = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [f]
  have h := (f q).property
  change P ((K.incl.comp f) q) at h
  simpa only [hf, LieHom.id_apply] using h

abbrev L := FreeLieAlgebra ℚ Bool
def x : L := FreeLieAlgebra.of ℚ false
def y : L := FreeLieAlgebra.of ℚ true

def eval {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) : L →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun i => if i then b else a)

abbrev Edge := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev BraidFree := FreeLieAlgebra ℚ Edge

def chord (i j : Fin 4) : BraidFree :=
  if h : i < j then FreeLieAlgebra.of ℚ ⟨(i, j), h⟩
  else if h : j < i then FreeLieAlgebra.of ℚ ⟨(j, i), h⟩ else 0

def braidRelations : Set BraidFree :=
  {z | (∃ i j k l : Fin 4,
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      z = ⁅chord i j, chord k l⁆) ∨
    (∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      z = ⁅chord i j, chord i k + chord j k⁆)}

def braidIdeal : LieIdeal ℚ BraidFree :=
  LieSubmodule.lieSpan ℚ BraidFree braidRelations

abbrev T4 := BraidFree ⧸ braidIdeal
def t (i j : Fin 4) : T4 := LieSubmodule.Quotient.mk (chord i j)

def IsSolution (p : L) : Prop :=
  p + eval y x p = 0 ∧
  p + eval y (-x-y) p + eval (-x-y) x p = 0 ∧
  eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p =
    eval (t 1 2) (t 2 3) p + eval (t 0 1 + t 0 2) (t 1 3 + t 2 3) p +
      eval (t 0 1) (t 1 2) p

def W : Submodule ℚ L where
  carrier := {p | IsSolution p}
  zero_mem' := by simp [IsSolution]
  add_mem' := by
    intro p q hp hq
    rcases hp with ⟨hp1, hp2, hp3⟩
    rcases hq with ⟨hq1, hq2, hq3⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_add]
      calc
        _ = (p + eval y x p) + (q + eval y x q) := by abel
        _ = 0 := by rw [hp1, hq1, add_zero]
    · simp only [map_add]
      calc
        _ = (p + eval y (-x-y) p + eval (-x-y) x p) +
            (q + eval y (-x-y) q + eval (-x-y) x q) := by abel
        _ = 0 := by rw [hp2, hq2, add_zero]
    · simp only [map_add]
      calc
        _ = (eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p) +
            (eval (t 0 1) (t 1 2 + t 1 3) q + eval (t 0 2 + t 1 2) (t 2 3) q) := by abel
        _ = _ := by rw [hp3, hq3]; abel
  smul_mem' := by
    intro a p hp
    rcases hp with ⟨hp1, hp2, hp3⟩
    change IsSolution (a • p)
    simp only [IsSolution, map_smul]
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp1
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp2
    · simpa only [smul_add] using congrArg (a • ·) hp3

structure Tangent where
  base : L
  velocity : L

def Tangent.equiv : Tangent ≃ L × L where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup Tangent := Tangent.equiv.addCommGroup
instance : Module ℚ Tangent := Tangent.equiv.addEquiv.module ℚ
instance : Bracket Tangent Tangent :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

/--
@isnad1 id=eq.2h2v.s4.6a1ce6c96216 from=translated src=- shape=04c0b690 vocab=19e9c8f2
-/
@[ext] theorem Tangent.ext {a b : Tangent} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

/--
@isnad1 id=eq.0h0v.s4.b0abd62231ce from=translated src=- shape=1ac31801 vocab=6327730e
-/
@[simp] theorem Tangent.base_zero : (0 : Tangent).base = 0 := rfl
/--
@isnad1 id=eq.0h0v.s4.c0849e6fcb4b from=translated src=- shape=1ac31801 vocab=46cf0af2
-/
@[simp] theorem Tangent.velocity_zero : (0 : Tangent).velocity = 0 := rfl
/--
@isnad1 id=eq.0h2v.s5.27091b9fb54b from=translated src=- shape=0438c7a3 vocab=cca1e00e
-/
@[simp] theorem Tangent.base_add (a b : Tangent) : (a+b).base = a.base+b.base := rfl
/--
@isnad1 id=eq.0h2v.s5.cb7220debfa1 from=translated src=- shape=0438c7a3 vocab=f4ea6d2b
-/
@[simp] theorem Tangent.velocity_add (a b : Tangent) :
    (a+b).velocity = a.velocity+b.velocity := rfl
/--
@isnad1 id=eq.0h2v.s6.3cb6c12b66d1 from=translated src=- shape=3b6301b8 vocab=a8b295c3
-/
@[simp] theorem Tangent.base_smul (q : ℚ) (a : Tangent) : (q • a).base = q • a.base := rfl
/--
@isnad1 id=eq.0h2v.s6.ad7d3fd1cf5a from=translated src=- shape=3b6301b8 vocab=5870b24b
-/
@[simp] theorem Tangent.velocity_smul (q : ℚ) (a : Tangent) :
    (q • a).velocity = q • a.velocity := rfl
/--
@isnad1 id=eq.0h2v.s5.2bf41714440b from=translated src=- shape=2fc54c2c vocab=c7d9d3ee
-/
@[simp] theorem Tangent.base_lie (a b : Tangent) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
/--
@isnad1 id=eq.0h2v.s6.44f5edf5cc23 from=translated src=- shape=3e259c5d vocab=1daea0dd
-/
@[simp] theorem Tangent.velocity_lie (a b : Tangent) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing Tangent where
  add_lie a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact add_lie a.base b.base c.base
    · change ⁅a.velocity + b.velocity, c.base⁆ + ⁅a.base + b.base, c.velocity⁆ =
        (⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆) +
          (⁅b.velocity, c.base⁆ + ⁅b.base, c.velocity⁆)
      simp only [add_lie]
      abel
  lie_add a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_add a.base b.base c.base
    · change ⁅a.velocity, b.base + c.base⁆ + ⁅a.base, b.velocity + c.velocity⁆ =
        (⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆) +
          (⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆)
      simp only [lie_add]
      abel
  lie_self a := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_self a.base
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact leibniz_lie a.base b.base c.base
    · change ⁅a.velocity, ⁅b.base, c.base⁆⁆ +
          ⁅a.base, ⁅b.velocity, c.base⁆ + ⁅b.base, c.velocity⁆⁆ =
        (⁅⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆, c.base⁆ +
          ⁅⁅a.base, b.base⁆, c.velocity⁆) +
        (⁅b.velocity, ⁅a.base, c.base⁆⁆ +
          ⁅b.base, ⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆⁆)
      simp only [lie_add, add_lie, lie_lie]
      abel

instance : LieAlgebra ℚ Tangent where
  lie_smul scalar left right := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_smul scalar left.base right.base
    · change ⁅left.velocity, scalar • right.base⁆ + ⁅left.base, scalar • right.velocity⁆ =
        scalar • (⁅left.velocity, right.base⁆ + ⁅left.base, right.velocity⁆)
      simp only [lie_smul, smul_add]

def tangentLift (p : L) : L →ₗ⁅ℚ⁆ Tangent :=
  FreeLieAlgebra.lift ℚ (fun i => if i then ⟨y, ⁅y,p⁆⟩ else ⟨x, 0⟩)

def D (p q : L) : L := (tangentLift p q).velocity

def ihara (p q : L) : L := D p q - D q p + ⁅p,q⁆

/--
@isnad1 id=eq.0h3v.s5.a1439ac084fe from=translated src=- shape=e2f00491 vocab=f256b8e9
-/
@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b x = a := by simp [eval, x]
/--
@isnad1 id=eq.0h3v.s5.fa03365f68ee from=translated src=- shape=d7b29f72 vocab=271577d6
-/
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b y = b := by simp [eval, y]

def Tangent.baseHom : Tangent →ₗ⁅ℚ⁆ L where
  toFun := Tangent.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

/--
@isnad1 id=eq.0h2v.s5.4dc2ce5c9881 from=translated src=- shape=77e9399a vocab=91146d31
-/
@[simp] theorem tangentLift_base (p q : L) : (tangentLift p q).base = q := by
  have h : Tangent.baseHom.comp (tangentLift p) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [tangentLift, Tangent.baseHom, x, y] <;> rfl
  exact LieHom.congr_fun h q

/--
@isnad1 id=eq.0h1v.s4.2d4a13fc1d68 from=translated src=- shape=4be16840 vocab=4edf4de8
-/
@[simp] theorem D_x (p : L) : D p x = 0 := by simp [D, tangentLift, x]
/--
@isnad1 id=eq.0h1v.s4.cb1bf5e96de4 from=translated src=- shape=71b798ed vocab=c31689c0
-/
@[simp] theorem D_y (p : L) : D p y = ⁅y,p⁆ := by simp [D, tangentLift, y]
/--
@isnad1 id=eq.0h1v.s4.e8953076b1bd from=translated src=- shape=1d838610 vocab=8e4ff61a
-/
@[simp] theorem D_zero (p : L) : D p 0 = 0 := by simp [D]
/--
@isnad1 id=eq.0h3v.s5.c0a39022890e from=translated src=- shape=4a33f3d9 vocab=e267ca6e
-/
@[simp] theorem D_add (p q r : L) : D p (q+r) = D p q + D p r := by simp [D]
/--
@isnad1 id=eq.0h3v.s5.ea6823f6c0a1 from=translated src=- shape=2f4fc0ab vocab=f32c7bb4
-/
@[simp] theorem D_smul (p q : L) (a : ℚ) : D p (a • q) = a • D p q := by simp [D]
/--
@isnad1 id=eq.0h3v.s6.08ca8cf77ff2 from=translated src=- shape=94836126 vocab=d6b7d6e5
-/
theorem D_lie (p q r : L) : D p ⁅q,r⁆ = ⁅D p q,r⁆ + ⁅q,D p r⁆ := by
  simp [D, LieHom.map_lie]

def derivation (p : L) : LieDerivation ℚ L L where
  toFun := D p
  map_add' := D_add p
  map_smul' a q := D_smul p q a
  leibniz' a b := by
    change D p ⁅a,b⁆ = ⁅a,D p b⁆ - ⁅b,D p a⁆
    rw [D_lie, sub_eq_add_neg, lie_skew, add_comm]

/--
@isnad1 id=eq.0h2v.s6.5c0fdf6cfd46 from=translated src=- shape=af186608 vocab=a87b9159
-/
@[simp] theorem derivation_apply (p q : L) : derivation p q = D p q := rfl

/--
@isnad1 id=eq.2h2v.s8.294f4dfafd0d from=translated src=- shape=966b90f5 vocab=37008285
-/
theorem derivation_ext {d₁ d₂ : LieDerivation ℚ L L}
    (hx : d₁ x = d₂ x) (hy : d₁ y = d₂ y) : d₁ = d₂ := by
  ext q
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i; exact hx; exact hy
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

/--
@isnad1 id=eq.0h1v.s4.6151ba5359e7 from=translated src=- shape=fe2c2146 vocab=8e4ff61a
-/
@[simp] theorem D_zero_left (q : L) : D 0 q = 0 := by
  have h : derivation 0 = 0 := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

/--
@isnad1 id=eq.0h3v.s5.e0c4ae9f216e from=translated src=- shape=2f6dc6a8 vocab=e267ca6e
-/
@[simp] theorem D_add_left (p q r : L) : D (p+q) r = D p r + D q r := by
  have h : derivation (p+q) = derivation p + derivation q := by
    apply derivation_ext <;> simp [lie_add]
  exact LieDerivation.congr_fun h r

/--
@isnad1 id=eq.0h3v.s5.2613e743f6c2 from=translated src=- shape=1e8b4ccd vocab=f32c7bb4
-/
@[simp] theorem D_smul_left (p q : L) (a : ℚ) : D (a • p) q = a • D p q := by
  have h : derivation (a • p) = a • derivation p := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

inductive WeightedWord {α : Type*} (wt : α → ℕ) : ℕ → FreeLieAlgebra ℚ α → Prop
  | generator (a : α) : WeightedWord wt (wt a) (FreeLieAlgebra.of ℚ a)
  | bracket {n m a b} : WeightedWord wt n a → WeightedWord wt m b →
      WeightedWord wt (n+m) ⁅a,b⁆

def weightPiece {α : Type*} (wt : α → ℕ) (n : ℕ) : Submodule ℚ (FreeLieAlgebra ℚ α) :=
  Submodule.span ℚ {p | WeightedWord wt n p}

abbrev OddFree := FreeLieAlgebra ℚ ℕ
def oddWeight (k : ℕ) : ℕ := 2*k+3
abbrev Fn (n : ℕ) := weightPiece oddWeight n
abbrev Ln (n : ℕ) := weightPiece (fun _ : Bool => 1) n
abbrev Wn (n : ℕ) : Submodule ℚ L := W ⊓ Ln n

def Graded (e : OddFree ≃ₗ[ℚ] W) : Prop :=
  ∀ n a, (e a : L) ∈ Ln n ↔ a ∈ Fn n

abbrev OddCompletion := (n : ℕ) → Fn n
abbrev WCompletion := (n : ℕ) → Wn n

instance : TopologicalSpace L := ⊥
instance : TopologicalSpace OddFree := ⊥

def completed (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) : OddCompletion → WCompletion :=
  fun a n => ⟨e (a n), (e (a n)).property, (h n (a n)).2 (a n).property⟩

def completedInv (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) : WCompletion → OddCompletion :=
  fun a n => ⟨e.symm ⟨a n, (a n).property.1⟩,
    (h n (e.symm ⟨a n, (a n).property.1⟩)).1 (by
      rw [LinearEquiv.apply_symm_apply]
      exact (a n).property.2)⟩

def MainStatement : Prop :=
  ∃ (e : OddFree ≃ₗ[ℚ] W) (h : Graded e),
    (∀ a b, (e ⁅a,b⁆ : L) = ihara (e a) (e b)) ∧
    Function.LeftInverse (completedInv e h) (completed e h) ∧
    Function.RightInverse (completedInv e h) (completed e h) ∧
    Continuous (completed e h) ∧ Continuous (completedInv e h) ∧
    (∀ (a b : OddCompletion) n,
      (e (∑ i ∈ Finset.range (n+1), ⁅(a i : OddFree), (b (n-i) : OddFree)⁆) : L) =
      ∑ i ∈ Finset.range (n+1),
        ihara (completed e h a i) (completed e h b (n-i)))

namespace AssociativeModel

variable {α : Type*}
abbrev FL (α : Type*) := FreeLieAlgebra ℚ α
abbrev A (α : Type*) := MonoidAlgebra ℚ (FreeMonoid α)
attribute [local instance] LieRing.ofAssociativeRing

def atom (a : α) : A α := MonoidAlgebra.single (FreeMonoid.of a) 1

def embed : FL α →ₗ⁅ℚ⁆ A α := FreeLieAlgebra.lift ℚ atom

/--
@isnad1 id=eq.0h2v.s7.30c230f0a46c from=translated src=- shape=367f82f3 vocab=d4f05c90
-/
@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of ℚ a) = atom a := by
  simp [embed]

def dynkinWord : List α → FL α
  | [] => 0
  | [a] => FreeLieAlgebra.of ℚ a
  | a :: b :: w => ⁅FreeLieAlgebra.of ℚ a, dynkinWord (b :: w)⁆

/--
@isnad1 id=eq.1h3v.s6.72723fe0961e from=translated src=- shape=eca510af vocab=0b0c1400
-/
theorem dynkinWord_cons (a : α) (w : List α) (hw : w ≠ []) :
    dynkinWord (a::w) = ⁅FreeLieAlgebra.of ℚ a, dynkinWord w⁆ := by
  cases w with
  | nil => contradiction
  | cons b w => rfl

def wordLinear {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : FreeMonoid α → M) : A α →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ f).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/--
@isnad1 id=eq.0h5v.s7.e0d0de310c99 from=translated src=- shape=bcc8ba35 vocab=96cbc78f
-/
@[simp] theorem wordLinear_single {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : FreeMonoid α → M) (w : FreeMonoid α) (c : ℚ) :
    wordLinear f (MonoidAlgebra.single w c) = c • f w := by
  change Finsupp.linearCombination ℚ f (Finsupp.single w c) = _; simp

def dynkin : A α →ₗ[ℚ] FL α := wordLinear (fun w => dynkinWord w.toList)

def wordAct : FreeMonoid α →* Module.End ℚ (FL α) :=
  FreeMonoid.lift (fun a => LieAlgebra.ad ℚ (FL α) (FreeLieAlgebra.of ℚ a))

def act : A α →ₐ[ℚ] Module.End ℚ (FL α) :=
  MonoidAlgebra.lift ℚ (Module.End ℚ (FL α)) (FreeMonoid α) wordAct

/--
@isnad1 id=eq.0h3v.s9.a5dfc8c4603e from=translated src=- shape=0b861dc4 vocab=465aa1eb
-/
@[simp] theorem act_single (w : FreeMonoid α) (c : ℚ) :
    act (MonoidAlgebra.single w c) = c • wordAct w := by simp [act]

/--
@isnad1 id=eq.0h3v.s8.825152072e60 from=translated src=- shape=660b430d vocab=8038e835
-/
@[simp] theorem wordAct_of_apply (a : α) (q : FL α) :
    wordAct (FreeMonoid.of a) q = ⁅FreeLieAlgebra.of ℚ a,q⁆ := by
  simp [wordAct, LieAlgebra.ad_apply]

/--
@isnad1 id=eq.0h3v.s9.b3df38a5332d from=translated src=- shape=8f133bdc vocab=842d621e
-/
@[simp] theorem act_embed (p q : FL α) : act (embed p) q = ⁅p,q⁆ := by
  have h : act.toLieHom.comp embed = LieAlgebra.ad ℚ (FL α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [atom, wordAct]
  exact LinearMap.congr_fun (LieHom.congr_fun h p) q

/--
@isnad1 id=eq.1h3v.s8.bf1d1f5b0958 from=translated src=- shape=21a16f50 vocab=1816c351
-/
theorem dynkinWord_append (u v : List α) (hv : v ≠ []) :
    dynkinWord (u++v) = wordAct (FreeMonoid.ofList u) (dynkinWord v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [List.cons_append, dynkinWord_cons _ _ (List.append_ne_nil_of_right_ne_nil u hv),
      ih, FreeMonoid.ofList_cons, map_mul, Module.End.mul_apply, wordAct_of_apply]

def homogeneous (n : ℕ) : Submodule ℚ (A α) :=
  Submodule.span ℚ {p | ∃ w : FreeMonoid α,
    w.toList.length = n ∧ p = MonoidAlgebra.single w 1}

/--
@isnad1 id=mem.1h3v.s6.1da77e2fb197 from=translated src=- shape=4cea2a65 vocab=e2c3a36f
-/
theorem single_mem_homogeneous (w : FreeMonoid α) (n : ℕ)
    (hn : w.toList.length = n) : MonoidAlgebra.single w 1 ∈ homogeneous (α := α) n :=
  Submodule.subset_span ⟨w, hn, rfl⟩

/--
@isnad1 id=mem.2h5v.s8.bc478610fe42 from=translated src=- shape=13e8ea44 vocab=c479b521
-/
theorem mul_homogeneous {n m : ℕ} {a b : A α}
    (ha : a ∈ homogeneous n) (hb : b ∈ homogeneous m) : a*b ∈ homogeneous (n+m) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨v,hv,rfl⟩
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨w,hw,rfl⟩
      simpa only [MonoidAlgebra.single_mul_single, one_mul] using
        single_mem_homogeneous (v*w) (n+m) (by simp [hv,hw])
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (homogeneous (n+m)).add_mem hb hc
    | smul r b _ hb => simpa only [mul_smul_comm] using (homogeneous (n+m)).smul_mem r hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (homogeneous (n+m)).add_mem ha hc
  | smul r a _ ha => simpa only [smul_mul_assoc] using (homogeneous (n+m)).smul_mem r ha

/--
@isnad1 id=eq.2h4v.s9.59094b741fe4 from=translated src=- shape=5bfecaa1 vocab=5a3ee837
-/
theorem dynkin_mul {n : ℕ} (hn : n > 0) (a : A α) {b : A α}
    (hb : b ∈ homogeneous n) : dynkin (a*b) = act a (dynkin b) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => simp [add_mul, ha, hc]
  | single v r =>
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨w,hw,rfl⟩
      have hw' : w.toList ≠ [] := by intro h; simp [h] at hw; omega
      simp [dynkin, dynkinWord_append _ _ hw']
    | zero => simp
    | add b c _ _ hb hc => simp [mul_add, hb, hc]
    | smul r b _ hb => simp [hb]

/--
@isnad1 id=and.1h3v.s9.a8c91d617d4d from=translated src=- shape=0e419bc2 vocab=3408440a
-/
theorem dynkin_embed_word {n : ℕ} {p : FL α}
    (hp : WeightedWord (fun _ : α => 1) n p) :
    0 < n ∧ embed p ∈ homogeneous n ∧ dynkin (embed p) = (n : ℚ) • p := by
  induction hp with
  | generator a =>
    refine ⟨by omega, ?_, ?_⟩
    · simpa [atom] using single_mem_homogeneous (FreeMonoid.of a) 1 rfl
    · simp [dynkin, atom, dynkinWord]
  | @bracket n m p q hp hq ihp ihq =>
    rcases ihp with ⟨hn,hn',hpn⟩
    rcases ihq with ⟨hm,hm',hqm⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [LieHom.map_lie]
      change embed p * embed q - embed q * embed p ∈ homogeneous (n+m)
      exact (homogeneous (n+m)).sub_mem (mul_homogeneous hn' hm')
        (by simpa [Nat.add_comm] using mul_homogeneous hm' hn')
    · rw [LieHom.map_lie]
      change dynkin (embed p * embed q - embed q * embed p) = _
      rw [map_sub, dynkin_mul hm _ hm', dynkin_mul hn _ hn', hqm, hpn]
      simp only [map_smul, act_embed]
      rw [← lie_skew q p]
      simp only [smul_neg, sub_neg_eq_add, Nat.cast_add, add_smul]
      exact add_comm _ _

def normalizedDynkin : A α →ₗ[ℚ] FL α :=
  wordLinear (fun w => (w.toList.length : ℚ)⁻¹ • dynkinWord w.toList)

/--
@isnad1 id=eq.1h3v.s8.d11798e1d568 from=translated src=- shape=3961c225 vocab=d65d2feb
-/
theorem normalizedDynkin_homogeneous {n : ℕ} {a : A α}
    (ha : a ∈ homogeneous n) : normalizedDynkin a = (n : ℚ)⁻¹ • dynkin a := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨w,hw,rfl⟩
    simp [normalizedDynkin, dynkin, hw]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb, smul_add]
  | smul r a _ ha =>
    rw [map_smul, map_smul, ha, smul_comm]

/--
@isnad1 id=eq.1h3v.s8.bc7ef7282d5d from=translated src=- shape=3b20ec37 vocab=9208508f
-/
theorem normalizedDynkin_embed_word {n : ℕ} {p : FL α}
    (hp : WeightedWord (fun _ : α => 1) n p) : normalizedDynkin (embed p) = p := by
  obtain ⟨hn,hn',hp'⟩ := dynkin_embed_word hp
  rw [normalizedDynkin_homogeneous hn', hp', smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.ne_of_gt hn)

/--
@isnad1 id=mem.0h3v.s7.2634bf5f40a1 from=translated src=- shape=db3c408e vocab=dbc4b3a4
-/
theorem mem_word_span (wt : α → ℕ) (p : FL α) :
    p ∈ Submodule.span ℚ {q | ∃ n, WeightedWord wt n q} := by
  let S : Submodule ℚ (FL α) := Submodule.span ℚ {q | ∃ n, WeightedWord wt n q}
  change p ∈ S
  induction p using freeLie_induction with
  | h0 => exact S.zero_mem
  | hg a => exact Submodule.subset_span ⟨wt a, WeightedWord.generator a⟩
  | ha a b ha hb => exact S.add_mem ha hb
  | hs r a ha => exact S.smul_mem r ha
  | hl a b ha hb =>
    induction ha using Submodule.span_induction with
    | mem a ha =>
      rcases ha with ⟨n, hn⟩
      induction hb using Submodule.span_induction with
      | mem b hb =>
        rcases hb with ⟨m, hm⟩
        exact Submodule.subset_span ⟨n+m, WeightedWord.bracket hn hm⟩
      | zero => simp
      | add b c _ _ hb hc => simpa only [lie_add] using S.add_mem hb hc
      | smul r b _ hb => simpa only [lie_smul] using S.smul_mem r hb
    | zero => simp
    | add a c _ _ ha hc => simpa only [add_lie] using S.add_mem ha hc
    | smul r a _ ha => simpa only [smul_lie] using S.smul_mem r ha

/--
@isnad1 id=eq.0h2v.s8.7079c50ce81d from=translated src=- shape=5f0a0df9 vocab=73d9253a
-/
theorem normalizedDynkin_embed (p : FL α) : normalizedDynkin (embed p) = p := by
  have hp := mem_word_span (fun _ : α => 1) p
  induction hp using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n,hn⟩ := ha
    exact normalizedDynkin_embed_word hn
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul r a _ ha => simp [ha]

/--
@isnad1 id=injectiv.0h1v.s7.bc7ee70e60e1 from=translated src=- shape=c216bdf5 vocab=d3ce458f
-/
theorem embed_injective : Function.Injective (embed (α := α)) :=
  Function.LeftInverse.injective normalizedDynkin_embed

end AssociativeModel

namespace FreeDerivations

variable {R : Type*} [CommRing R]
variable {M : Type*} [LieRing M] [LieAlgebra R M]

structure Jet (R M : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  base : M
  velocity : M

def Jet.equiv : Jet R M ≃ M × M where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Jet R M) := Jet.equiv.addCommGroup
instance : Module R (Jet R M) := Jet.equiv.addEquiv.module R
instance : Bracket (Jet R M) (Jet R M) :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

/--
@isnad1 id=eq.2h4v.s6.b10702d0f4c5 from=translated src=- shape=2930bb47 vocab=c4c8b496
-/
@[ext] theorem Jet.ext {a b : Jet R M} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

/--
@isnad1 id=eq.0h2v.s6.ff909a98b214 from=translated src=- shape=036a0911 vocab=72b4ec40
-/
@[simp] theorem Jet.base_zero : (0 : Jet R M).base = 0 := rfl
/--
@isnad1 id=eq.0h2v.s6.d3d39a7d4341 from=translated src=- shape=036a0911 vocab=0c8c10ec
-/
@[simp] theorem Jet.velocity_zero : (0 : Jet R M).velocity = 0 := rfl
/--
@isnad1 id=eq.0h4v.s7.337b04cfc7c2 from=translated src=- shape=8e7aec71 vocab=dd97797a
-/
@[simp] theorem Jet.base_add (a b : Jet R M) : (a+b).base = a.base+b.base := rfl
/--
@isnad1 id=eq.0h4v.s7.6cdfa0fdf13f from=translated src=- shape=8e7aec71 vocab=8cb84421
-/
@[simp] theorem Jet.velocity_add (a b : Jet R M) :
    (a+b).velocity = a.velocity+b.velocity := rfl
/--
@isnad1 id=eq.0h4v.s8.311687e2bd24 from=translated src=- shape=86265f6a vocab=cc53aeb4
-/
@[simp] theorem Jet.base_smul (q : R) (a : Jet R M) : (q • a).base = q • a.base := rfl
/--
@isnad1 id=eq.0h4v.s8.ec1052507db5 from=translated src=- shape=86265f6a vocab=e64361bd
-/
@[simp] theorem Jet.velocity_smul (q : R) (a : Jet R M) :
    (q • a).velocity = q • a.velocity := rfl
/--
@isnad1 id=eq.0h4v.s6.069297f64ef1 from=translated src=- shape=41aea695 vocab=afd28642
-/
@[simp] theorem Jet.base_lie (a b : Jet R M) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
/--
@isnad1 id=eq.0h4v.s7.73187b041647 from=translated src=- shape=79c73cd7 vocab=e5c639f9
-/
@[simp] theorem Jet.velocity_lie (a b : Jet R M) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing (Jet R M) where
  add_lie a b c := by (ext <;> simp [add_lie]); abel
  lie_add a b c := by (ext <;> simp [lie_add]); abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by (ext <;> simp [lie_add, add_lie, lie_lie]); abel
instance : LieAlgebra R (Jet R M) where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]

def Jet.baseHom : Jet R M →ₗ⁅R⁆ M where
  toFun := Jet.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

variable {α : Type*}
local notation "F" => FreeLieAlgebra R α

def jetLift (f : α → F) : F →ₗ⁅R⁆ Jet R F :=
  FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, f a⟩)

/--
@isnad1 id=eq.0h4v.s7.e9c622d88514 from=translated src=- shape=8fd31a50 vocab=023fd3f4
-/
@[simp] theorem jetLift_base (f : α → F) (p : F) :
    (jetLift f p).base = p := by
  have h : Jet.baseHom.comp (jetLift f) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [jetLift, Jet.baseHom]
    rfl
  exact LieHom.congr_fun h p

def extend (f : α → F) : LieDerivation R F F where
  toFun q := (jetLift f q).velocity
  map_add' a b := by
    change (jetLift f (a+b)).velocity = _
    rw [map_add]
    rfl
  map_smul' r a := by
    change (jetLift f (r • a)).velocity = _
    rw [map_smul]
    rfl
  leibniz' a b := by
    change (jetLift f ⁅a,b⁆).velocity = ⁅a,(jetLift f b).velocity⁆ - ⁅b,(jetLift f a).velocity⁆
    rw [LieHom.map_lie, Jet.velocity_lie, jetLift_base, jetLift_base]
    rw [sub_eq_add_neg, lie_skew, add_comm]

/--
@isnad1 id=eq.0h4v.s7.0ab8f11125e1 from=translated src=- shape=b4de477a vocab=b59760ba
-/
@[simp] theorem extend_of (f : α → F) (a : α) :
    extend f (FreeLieAlgebra.of R a) = f a := by
  change (jetLift f (FreeLieAlgebra.of R a)).velocity = _
  simp [jetLift]

/--
@isnad1 id=eq.1h4v.s8.4646457723eb from=translated src=- shape=ee525182 vocab=a1387508
-/
@[ext] theorem ext {d₁ d₂ : LieDerivation R F F}
    (h : ∀ a, d₁ (FreeLieAlgebra.of R a) = d₂ (FreeLieAlgebra.of R a)) : d₁ = d₂ := by
  ext q
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => exact h a
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

/--
@isnad1 id=eq.1h4v.s8.23956a664498 from=translated src=- shape=49bcac22 vocab=b59760ba
-/
theorem extend_unique (f : α → F) (d : LieDerivation R F F)
    (h : ∀ a, d (FreeLieAlgebra.of R a) = f a) : d = extend f := by
  apply ext
  intro a
  simpa using h a

variable [DecidableEq α]
def pair (i j : α) : LieDerivation R F F :=
  extend (fun k => if k = i then ⁅FreeLieAlgebra.of R i, FreeLieAlgebra.of R j⁆
    else if k = j then ⁅FreeLieAlgebra.of R j, FreeLieAlgebra.of R i⁆ else 0)

/--
@isnad1 id=eq.0h4v.s7.03b7a930dfda from=translated src=- shape=0a19c87d vocab=384d034f
-/
@[simp] theorem pair_of_left (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R i) = ⁅FreeLieAlgebra.of R i,FreeLieAlgebra.of R j⁆ := by
  simp [pair]

/--
@isnad1 id=eq.0h4v.s7.7b4ce7302d5a from=translated src=- shape=b4442cc7 vocab=384d034f
-/
@[simp] theorem pair_of_right (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R j) = ⁅FreeLieAlgebra.of R j,FreeLieAlgebra.of R i⁆ := by
  by_cases h : j = i
  · subst j; simp
  · simp [pair, h]

/--
@isnad1 id=eq.2h5v.s7.8b326eb6d306 from=translated src=- shape=6241cab8 vocab=595d2f0f
-/
@[simp] theorem pair_of_other (i j k : α) (hi : k ≠ i) (hj : k ≠ j) :
    pair (R := R) i j (FreeLieAlgebra.of R k) = 0 := by
  simp [pair, hi, hj]

/--
@isnad1 id=eq.0h4v.s6.4fc8c98378bc from=translated src=- shape=6261a559 vocab=594f3457
-/
theorem pair_comm (i j : α) : pair (R := R) i j = pair j i := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  by_cases hj : a=j
  · subst a; simp
  simp [hi,hj]

/--
@isnad1 id=eq.0h3v.s7.8c0cd9cc6ed1 from=translated src=- shape=6086eaec vocab=594f3457
-/
theorem pair_self (i : α) : pair (R := R) i i = 0 := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  simp [hi]

/--
@isnad1 id=eq.4h6v.s8.2f8697ed95cc from=translated src=- shape=2e882551 vocab=c29af250
-/
theorem pair_disjoint (i j k l : α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅pair (R := R) i j,pair (R := R) k l⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases haj : a=j
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases hak : a=k
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  by_cases hal : a=l
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  simp [hai,haj,hak,hal]

/--
@isnad1 id=eq.3h5v.s9.acb4d38d62c1 from=translated src=- shape=8807eed4 vocab=2e387f30
-/
theorem pair_three (i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅pair (R := R) i j, pair (R := R) i k + pair (R := R) j k⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases haj : a=j
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases hak : a=k
  · subst a
    simp [hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  simp [hai,haj,hak]

end FreeDerivations

namespace BraidRepresentation
open FreeDerivations LieAlgebra
variable {R α : Type*} [CommRing R] [DecidableEq α]
local notation "F" => FreeLieAlgebra R α
local notation "Der" => LieDerivation R F F
local notation "SD" => SemiDirectSum F Der (LieHom.id : Der →ₗ⁅R⁆ Der)

def fiber (i : α) : SD := SemiDirectSum.inl LieHom.id (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr LieHom.id (pair i j)

def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j

/--
@isnad1 id=eq.0h2v.s10.834acc3e9002 from=translated src=- shape=679afa57 vocab=06033139
-/
@[simp] theorem chord_none_none : chord (R := R) (α := α) none none = 0 := rfl
/--
@isnad1 id=eq.0h3v.s7.798f86528d8e from=translated src=- shape=2a0999a6 vocab=01d9ec22
-/
@[simp] theorem chord_none_some (j : α) : chord (R := R) none (some j) = fiber j := rfl
/--
@isnad1 id=eq.0h3v.s7.6a800991a423 from=translated src=- shape=33b7bb63 vocab=01d9ec22
-/
@[simp] theorem chord_some_none (i : α) : chord (R := R) (some i) none = fiber i := rfl
/--
@isnad1 id=eq.0h4v.s7.c8a97314f4db from=translated src=- shape=4651161b vocab=1a818a02
-/
@[simp] theorem chord_some_some (i j : α) : chord (R := R) (some i) (some j) = base i j := rfl

/--
@isnad1 id=eq.0h4v.s7.39001ed723fe from=translated src=- shape=8d0f0acd vocab=31b005b1
-/
theorem chord_comm (i j : Option α) : chord (R := R) i j = chord j i := by
  cases i <;> cases j <;> simp [base, pair_comm]

/--
@isnad1 id=eq.0h3v.s10.33eebc515069 from=translated src=- shape=6fed92ba vocab=31b005b1
-/
@[simp] theorem chord_self (i : Option α) : chord (R := R) i i = 0 := by
  cases i <;> simp [base, pair_self]

/--
@isnad1 id=eq.0h5v.s11.01e62b65ef2a from=translated src=- shape=9fa9e006 vocab=5a4a98f2
-/
theorem base_fiber (i j k : α) :
    ⁅base (R := R) i j, fiber k⁆ = SemiDirectSum.inl LieHom.id
      (pair (R := R) i j (FreeLieAlgebra.of R k)) := by
  simp [base, fiber]

/--
@isnad1 id=eq.0h5v.s11.d421661dfada from=translated src=- shape=0863e336 vocab=8d87ffb3
-/
theorem fiber_base (i j k : α) :
    ⁅fiber (R := R) k, base i j⁆ = - SemiDirectSum.inl LieHom.id
      (pair (R := R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew, base_fiber]

/--
@isnad1 id=eq.4h6v.s11.18e0701de1a6 from=translated src=- shape=73db23f4 vocab=ed06ff3b
-/
theorem chord_disjoint (i j k l : Option α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅chord (R := R) i j, chord (R := R) k l⁆ = 0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base, fiber, pair_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction

/--
@isnad1 id=eq.3h5v.s11.d764ccdc2573 from=translated src=- shape=7c620799 vocab=321d3fcb
-/
theorem chord_three (i j k : Option α)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord (R := R) i j, chord (R := R) i k + chord (R := R) j k⁆ = 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_none_some, chord_none_some, chord_some_some, lie_add, fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_some_none, chord_some_some, chord_none_some, lie_add, fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_some_some, chord_some_none, chord_some_none, lie_add,
          base_fiber, base_fiber]
        simp only [pair_of_left, pair_of_right, ← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_some_some, base, ← map_add, ← LieHom.map_lie]
        rw [pair_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)), map_zero]

end BraidRepresentation

namespace BraidModel
open LieAlgebra
abbrev Fiber := FreeLieAlgebra ℚ (Fin 3)
abbrev Der := LieDerivation ℚ Fiber Fiber
abbrev Model := SemiDirectSum Fiber Der (LieHom.id : Der →ₗ⁅ℚ⁆ Der)
def chord (i j : Fin 4) : Model :=
  BraidRepresentation.chord (finSuccEquiv' (1 : Fin 4) i) (finSuccEquiv' (1 : Fin 4) j)

/--
@isnad1 id=eq.0h2v.s4.7b9a57007d92 from=translated src=- shape=376c686a vocab=38883f3c
-/
theorem chord_comm (i j : Fin 4) : chord i j = chord j i :=
  BraidRepresentation.chord_comm _ _

/--
@isnad1 id=eq.0h1v.s7.055447db2982 from=translated src=- shape=6e4c2516 vocab=9abd9a08
-/
@[simp] theorem chord_self (i : Fin 4) : chord i i = 0 :=
  BraidRepresentation.chord_self _

def preMap : BraidFree →ₗ⁅ℚ⁆ Model := FreeLieAlgebra.lift ℚ (fun e => chord e.val.1 e.val.2)

/--
@isnad1 id=eq.0h2v.s9.27371b9af6ef from=translated src=- shape=2dedaa33 vocab=64350aae
-/
@[simp] theorem preMap_chord (i j : Fin 4) : preMap (DeligneDrinfeld.chord i j) = chord i j := by
  unfold DeligneDrinfeld.chord
  split_ifs with hij hji
  · simp [preMap]
  · simp [preMap, chord_comm j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp

/--
@isnad1 id=le.0h0v.s8.0d491acffd52 from=translated src=- shape=1f424ad4 vocab=4d625224
-/
theorem ideal_le_ker : braidIdeal ≤ preMap.ker := by
  rw [braidIdeal, LieSubmodule.lieSpan_le]
  intro z hz
  change preMap z = 0
  rcases hz with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
  · rw [LieHom.map_lie, preMap_chord, preMap_chord]
    exact BraidRepresentation.chord_disjoint _ _ _ _
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hik) ((finSuccEquiv' (1 : Fin 4)).injective.ne hil)
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hjk) ((finSuccEquiv' (1 : Fin 4)).injective.ne hjl)
  · rw [LieHom.map_lie, map_add, preMap_chord, preMap_chord, preMap_chord]
    exact BraidRepresentation.chord_three _ _ _
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hij) ((finSuccEquiv' (1 : Fin 4)).injective.ne hik)
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hjk)

def map : T4 →ₗ⁅ℚ⁆ Model :=
  { braidIdeal.toSubmodule.liftQ preMap.toLinearMap ideal_le_ker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact preMap.map_lie a b }

/--
@isnad1 id=eq.0h2v.s9.9534561b028e from=translated src=- shape=2dedaa33 vocab=7b825472
-/
@[simp] theorem map_t (i j : Fin 4) : map (t i j) = chord i j := preMap_chord i j

end BraidModel

namespace AssociativeModel
attribute [local instance] LieRing.ofAssociativeRing
variable {α : Type*}

/--
@isnad1 id=eq.1h4v.s7.0e573a75075f from=translated src=- shape=02d75ddf vocab=b832d916
-/
theorem coeff_rotate {P : A α} {b : α} (h : atom b * P = P * atom b) (w : List α) :
    P.coeff (FreeMonoid.ofList (b :: w)) = P.coeff (FreeMonoid.ofList (w ++ [b])) := by
  calc
    P.coeff (FreeMonoid.ofList (b :: w)) =
        (P * atom b).coeff ((FreeMonoid.of b * FreeMonoid.ofList w) * FreeMonoid.of b) := by
      simp [atom, FreeMonoid.ofList_cons]
    _ = (atom b * P).coeff (FreeMonoid.of b * (FreeMonoid.ofList w * FreeMonoid.of b)) := by
      rw [h, mul_assoc]
    _ = P.coeff (FreeMonoid.ofList (w ++ [b])) := by
      simp [atom, FreeMonoid.ofList_append]

/--
@isnad1 id=eq.2h5v.s7.383c5f198a1f from=translated src=- shape=06f5753c vocab=b3221cb3
-/
theorem coeff_starts_ne {P : A α} {b a : α} (h : atom b * P = P * atom b)
    (hab : a ≠ b) (v : List α) : P.coeff (FreeMonoid.ofList (a :: v)) = 0 := by
  have hz : (atom b * P).coeff (FreeMonoid.ofList (a::v) * FreeMonoid.of b) = 0 := by
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro d hd
    have hh := congrArg (fun w : FreeMonoid α => w.toList.head?) hd
    exact hab (by simpa using hh.symm)
  rw [h] at hz
  simpa [atom] using hz

/--
@isnad1 id=eq.2h6v.s7.4180d136357b from=translated src=- shape=ffc637dc vocab=4da84300
-/
theorem coeff_contains_ne {P : A α} {b a : α} (h : atom b * P = P * atom b)
    (hab : a ≠ b) (u v : List α) : P.coeff (FreeMonoid.ofList (u ++ a :: v)) = 0 := by
  induction u generalizing v with
  | nil => exact coeff_starts_ne h hab v
  | cons c u ih =>
    by_cases hc : c = b
    · subst c
      rw [List.cons_append, coeff_rotate h]
      simpa [List.append_assoc] using ih (v ++ [b])
    · exact coeff_starts_ne h hc (u ++ a :: v)

/--
@isnad1 id=eq.3h5v.s7.d770e57d4922 from=translated src=- shape=deb39d3c vocab=20f1c958
-/
theorem coeff_eq_zero_of_letter_ne {P : A α} {b a : α}
    (h : atom b * P = P * atom b) {w : List α} (ha : a ∈ w) (hab : a ≠ b) :
    P.coeff (FreeMonoid.ofList w) = 0 := by
  obtain ⟨u,v,rfl⟩ := List.append_of_mem ha
  exact coeff_contains_ne h hab u v

/--
@isnad1 id=mem.1h3v.s7.baa1c43ab3b8 from=translated src=- shape=70eb44cb vocab=76da1b81
-/
theorem dynkinWord_all_eq (b : α) (w : List α) (hw : ∀ a ∈ w, a = b) :
    dynkinWord w ∈ Submodule.span ℚ {FreeLieAlgebra.of ℚ b} := by
  induction w with
  | nil => simp [dynkinWord]
  | cons a w ih =>
    have ha : a = b := hw a (by simp)
    subst a
    cases w with
    | nil => exact Submodule.subset_span (by simp [dynkinWord])
    | cons c w =>
      rw [dynkinWord]
      have hmem := ih (fun a ha => hw a (by simp [ha]))
      obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hmem
      rw [← hr, lie_smul, lie_self, smul_zero]
      exact Submodule.zero_mem _

/--
@isnad1 id=mem.1h3v.s7.7f32797c2719 from=translated src=- shape=c3b47c8b vocab=c0439c41
-/
theorem centralizer_generator {p : FL α} (b : α) (h : ⁅FreeLieAlgebra.of ℚ b,p⁆ = 0) :
    p ∈ Submodule.span ℚ {FreeLieAlgebra.of ℚ b} := by
  classical
  have hc : atom b * embed p = embed p * atom b := by
    have ht := congrArg embed h
    rw [LieHom.map_lie, embed_of, map_zero] at ht
    exact sub_eq_zero.mp ht
  rw [← normalizedDynkin_embed p, ← MonoidAlgebra.sum_coeff_single (embed p)]
  unfold Finsupp.sum
  rw [map_sum]
  apply Submodule.sum_mem
  intro w hw
  rw [normalizedDynkin, wordLinear_single]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  apply dynkinWord_all_eq
  intro a ha
  by_contra hab
  have hz := coeff_eq_zero_of_letter_ne hc ha hab
  have hn := Finsupp.mem_support_iff.mp hw
  exact hn (by simpa using hz)

end AssociativeModel

/--
@isnad1 id=eq.0h6v.s7.4c4440889979 from=translated src=- shape=e2461232 vocab=35b716f8
-/
theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra ℚ M]
    [LieRing N] [LieAlgebra ℚ N] (f : M →ₗ⁅ℚ⁆ N) (a b : M) (p : L) :
    f (eval a b p) = eval (f a) (f b) p := by
  have h : f.comp (eval a b) = eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun h p

/--
@isnad1 id=eq.0h0v.s5.13a899d8deac from=translated src=- shape=d99dab9f vocab=6f2ab1de
-/
theorem eval_self : eval x y = LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i <;> simp [eval, x, y]

/--
@isnad1 id=eq.2h5v.s7.21cb6f385856 from=translated src=- shape=01033e52 vocab=d5b589a8
-/
theorem eval_commutes {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b z : M) (ha : ⁅z,a⁆ = 0) (hb : ⁅z,b⁆ = 0) (p : L) :
    ⁅z,eval a b p⁆ = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval, ha, hb]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [LieHom.map_lie, leibniz_lie, hp, hq]

/--
@isnad1 id=eq.0h2v.s4.dfa738174439 from=translated src=- shape=376c686a vocab=28615248
-/
@[simp] theorem chord_comm (i j : Fin 4) : chord i j = chord j i := by
  unfold chord
  split_ifs <;> first | rfl | omega

/--
@isnad1 id=eq.0h2v.s4.9b3f054777cf from=translated src=- shape=376c686a vocab=d9c57a79
-/
@[simp] theorem t_comm (i j : Fin 4) : t i j = t j i := by
  unfold t
  rw [chord_comm]

/--
@isnad1 id=eq.6h4v.s7.24cbc44c2378 from=translated src=- shape=8bae162d vocab=4b05802b
-/
theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

/--
@isnad1 id=eq.3h3v.s7.8f28b2ec823d from=translated src=- shape=a76d3652 vocab=c6a698f3
-/
theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

namespace BraidModel

def inclusion : Fiber →ₗ⁅ℚ⁆ T4 := FreeLieAlgebra.lift ℚ
  (fun i => t 1 ((finSuccEquiv' (1 : Fin 4)).symm (some i)))

/--
@isnad1 id=eq.0h0v.s9.e8d9a630f8f5 from=translated src=- shape=4ddb57d9 vocab=431f70f1
-/
theorem map_inclusion : map.comp inclusion = LieAlgebra.SemiDirectSum.inl LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  simp [inclusion, chord, BraidRepresentation.fiber]

/--
@isnad1 id=injectiv.0h0v.s6.7bfdd924c927 from=translated src=- shape=91c1b9c9 vocab=f8cc4569
-/
theorem inclusion_injective : Function.Injective inclusion := by
  intro a b hab
  have h := congrArg map hab
  have hm (c : Fiber) : map (inclusion c) = LieAlgebra.SemiDirectSum.inl LieHom.id c :=
    LieHom.congr_fun map_inclusion c
  rw [hm,hm] at h
  exact LieAlgebra.SemiDirectSum.inl_injective _ h

end BraidModel

/--
@isnad1 id=eq.1h3v.s6.47164f924437 from=translated src=- shape=f7e33493 vocab=cedfc192
-/
theorem commute_symm {M : Type*} [LieRing M] {a b : M} (h : ⁅a,b⁆ = 0) : ⁅b,a⁆ = 0 := by
  rw [← lie_skew, h, neg_zero]

/--
@isnad1 id=eq.4h7v.s8.338ff6f471bb from=translated src=- shape=23d57fec vocab=d5b589a8
-/
theorem evals_commute {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p q : L) :
    ⁅eval a b p,eval c d q⁆ = 0 := by
  apply eval_commutes
  · exact commute_symm (eval_commutes a b c (commute_symm hac) (commute_symm hbc) p)
  · exact commute_symm (eval_commutes a b d (commute_symm had) (commute_symm hbd) p)

/--
@isnad1 id=eq.4h6v.s8.61c4e9b0019b from=translated src=- shape=432d4308 vocab=913a90d3
-/
theorem eval_add_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p : L) :
    eval (a+c) (b+d) p = eval a b p + eval c d p := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq =>
    simp only [LieHom.map_lie, hp, hq, add_lie, lie_add]
    rw [evals_commute a b c d hac had hbc hbd p q,
      commute_symm (evals_commute a b c d hac had hbc hbd q p)]
    simp

/--
@isnad1 id=eq.3h5v.s7.82fd4850a7cc from=translated src=- shape=dd235e6a vocab=b3636fae
-/
theorem eval_vanish_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b : M) (hab : ⁅a,b⁆ = 0) {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a b p = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    cases hp with
    | generator i => omega
    | @bracket n m p q hp hq =>
      rw [LieHom.map_lie]
      exact evals_commute a b a b (lie_self a) hab (commute_symm hab) (lie_self b) p q
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

/--
@isnad1 id=eq.4h6v.s8.8a9caac4d253 from=translated src=- shape=2d85d77f vocab=e60ad35d
-/
theorem eval_central_shift {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c : M) (hac : ⁅a,c⁆ = 0) (hbc : ⁅b,c⁆ = 0)
    {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a (b+c) p = eval a b p := by
  have h := eval_add_of_commuting a b 0 c (lie_zero a) hac (lie_zero b) hbc p
  simpa [eval_vanish_of_commuting 0 c (zero_lie c) hp hn] using h

namespace T4Universal
variable {M : Type*} [LieRing M] [LieAlgebra ℚ M]

def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun e => f e.val.1 e.val.2)

/--
@isnad1 id=eq.2h4v.s7.c04e8ca73ef5 from=translated src=- shape=59847924 vocab=85d560cd
-/
theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]

def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℚ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }

/--
@isnad1 id=eq.4h4v.s8.fe37f2c5c51b from=translated src=- shape=42165217 vocab=de833ed6
-/
@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j

end T4Universal

/--
@isnad1 id=eq.0h1v.s5.87645eb3c402 from=translated src=- shape=6e4c2516 vocab=e5761800
-/
@[simp] theorem t_self (i : Fin 4) : t i i = 0 := by simp [t, chord]

def t4Rename (e : Equiv.Perm (Fin 4)) : T4 →ₗ⁅ℚ⁆ T4 :=
  T4Universal.lift (fun i j => t (e i) (e j))
    (fun _ _ => t_comm _ _) (fun _ => t_self _)
    (fun _ _ _ _ hij hik hil hjk hjl hkl => t_disjoint _ _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hil)
      (e.injective.ne hjk) (e.injective.ne hjl) (e.injective.ne hkl))
    (fun _ _ _ hij hik hjk => t_three _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))

/--
@isnad1 id=eq.0h3v.s8.fb4ee8fdc03d from=translated src=- shape=700623a8 vocab=5fdf79f4
-/
@[simp] theorem t4Rename_t (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    t4Rename e (t i j) = t (e i) (e j) := T4Universal.lift_t _ _ _ _ _ _ _

/--
@isnad1 id=eq.1h4v.s7.2c940442b896 from=translated src=- shape=3775634f vocab=ae3a1b64
-/
theorem solution_swap {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b p = - eval b a p := by
  have h := congrArg (eval a b) hp.1
  simp only [map_add, map_zero, map_eval, eval_x, eval_y] at h
  exact eq_neg_of_add_eq_zero_left h

/--
@isnad1 id=eq.1h4v.s8.2bcb8be92849 from=translated src=- shape=b14f1006 vocab=c55b568d
-/
theorem solution_three {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b p + eval b (-a-b) p + eval (-a-b) a p = 0 := by
  have h := congrArg (eval a b) hp.2.1
  simpa only [map_add, map_zero, map_eval, map_sub, map_neg, eval_x, eval_y] using h

/--
@isnad1 id=eq.1h9v.s10.24e655c7131c from=translated src=- shape=d25274be vocab=b26d063f
-/
theorem free_action_inner {R α β Z : Type*} [CommRing R]
    [LieRing Z] [LieAlgebra R Z]
    (f : FreeLieAlgebra R α →ₗ⁅R⁆ Z) (g : FreeLieAlgebra R β →ₗ⁅R⁆ Z)
    (h : FreeLieAlgebra R β →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
    (hg : ∀ b a, f (h (FreeLieAlgebra.of R b) (FreeLieAlgebra.of R a)) =
      ⁅g (FreeLieAlgebra.of R b),f (FreeLieAlgebra.of R a)⁆)
    (q : FreeLieAlgebra R β) (p : FreeLieAlgebra R α) :
    f (h q p) = ⁅g q,f p⁆ := by
  have H : ∀ q : FreeLieAlgebra R β, ∀ p : FreeLieAlgebra R α,
      f (h q p) = ⁅g q,f p⁆ := by
    intro q
    induction q using freeLie_induction with
    | h0 => intro p; simp
    | hg b =>
      intro p
      induction p using freeLie_induction with
      | h0 => simp
      | hg a => exact hg b a
      | ha p r hp hr => simp [hp,hr]
      | hs c p hp => simp [hp]
      | hl p r hp hr =>
        simp [hp,hr,LieHom.map_lie]
        grind [lie_lie,lie_skew]
    | ha q r hq hr => intro p; simp [hq,hr]
    | hs c q hq => intro p; simp [hq]
    | hl q r hq hr => intro p; simp [LieHom.map_lie,hq,hr,lie_lie]
  exact H q p

namespace InnerSemiDirect
open LieAlgebra
variable {R K B Z : Type*} [CommRing R]
  [LieRing K] [LieAlgebra R K] [LieRing B] [LieAlgebra R B]
  [LieRing Z] [LieAlgebra R Z]
variable (action : B →ₗ⁅R⁆ LieDerivation R K K)
  (f : K →ₗ⁅R⁆ Z) (g : B →ₗ⁅R⁆ Z)
  (h : ∀ q p, f (action q p) = ⁅g q,f p⁆)

def lift : SemiDirectSum K B action →ₗ⁅R⁆ Z where
  toFun z := f z.left + g z.right
  map_add' z t := by simp; abel
  map_smul' c z := by simp [smul_add]
  map_lie' {z t} := by
    simp only [SemiDirectSum.lie_eq_mk, map_sub, map_add, LieHom.map_lie, h,
      add_lie, lie_add]
    rw [sub_eq_add_neg, lie_skew]
    abel

/--
@isnad1 id=eq.1h8v.s9.c4132f6c3892 from=translated src=- shape=e821690a vocab=b5a798fa
-/
@[simp] theorem lift_inl (p : K) : lift action f g h (SemiDirectSum.inl action p) = f p := by
  simp [lift]
/--
@isnad1 id=eq.1h8v.s9.8eff73e7c662 from=translated src=- shape=df9d16f1 vocab=a9cb1a96
-/
@[simp] theorem lift_inr (p : B) : lift action f g h (SemiDirectSum.inr action p) = g p := by
  simp [lift]
end InnerSemiDirect

namespace SpecialFiber
open LieAlgebra FreeDerivations
abbrev F := FreeLieAlgebra ℚ (Fin 3)
def fa : F := FreeLieAlgebra.of ℚ 0
def fb : F := FreeLieAlgebra.of ℚ 1
def fc : F := FreeLieAlgebra.of ℚ 2

def action : L →ₗ⁅ℚ⁆ LieDerivation ℚ F F := eval (pair 0 1) (pair 1 2)
abbrev M := SemiDirectSum F L action

def a : M := SemiDirectSum.inl action fa
def b : M := SemiDirectSum.inl action fb
def c : M := SemiDirectSum.inl action fc
def u : M := SemiDirectSum.inr action x
def v : M := SemiDirectSum.inr action y
def w : M := -a-b-c-u-v

/--
@isnad1 id=eq.0h0v.s6.a4119bf6bc7f from=translated src=- shape=88492276 vocab=4a2a8b4c
-/
theorem au : ⁅a,u⁆ = -⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fa,fb]
/--
@isnad1 id=eq.0h0v.s6.795d30441107 from=translated src=- shape=16f0caf0 vocab=722d469d
-/
theorem bu : ⁅b,u⁆ = ⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa,fb]
/--
@isnad1 id=eq.0h0v.s6.94f2c031f527 from=translated src=- shape=616ad71d vocab=7ff3bbe1
-/
theorem cu : ⁅c,u⁆ = 0 := by
  simp only [c,u, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fc]
/--
@isnad1 id=eq.0h0v.s6.10b0102e98d2 from=translated src=- shape=616ad71d vocab=6dddd0d3
-/
theorem av : ⁅a,v⁆ = 0 := by
  simp only [a,v, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa]
/--
@isnad1 id=eq.0h0v.s6.d347e2e1f433 from=translated src=- shape=88492276 vocab=590c8e91
-/
theorem bv : ⁅b,v⁆ = -⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fb,fc]
/--
@isnad1 id=eq.0h0v.s6.6f8f4e6df052 from=translated src=- shape=16f0caf0 vocab=31500fe1
-/
theorem cv : ⁅c,v⁆ = ⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fb,fc]

def chord (i j : Fin 4) : M :=
  match i.val, j.val with
  | 0,1 | 1,0 => a
  | 0,2 | 2,0 => u
  | 0,3 | 3,0 => w
  | 1,2 | 2,1 => b
  | 1,3 | 3,1 => c
  | 2,3 | 3,2 => v
  | _,_ => 0

private theorem chord_symm (i j : Fin 4) : chord i j = chord j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem chord_zero (i : Fin 4) : chord i i = 0 := by fin_cases i <;> rfl

private theorem chord_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : ⁅chord i j,chord k l⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals fin_cases l <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie,
    bu,cu,av,bv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]

private theorem chord_three (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord i j,chord i k+chord j k⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie, lie_add,
    au,bu,cu,av,bv,cv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]

def representation : T4 →ₗ⁅ℚ⁆ M :=
  T4Universal.lift chord chord_symm chord_zero chord_disjoint chord_three

/--
@isnad1 id=eq.0h2v.s7.d70046444fad from=translated src=- shape=2dedaa33 vocab=6ef4f99e
-/
@[simp] theorem representation_t (i j : Fin 4) : representation (t i j) = chord i j :=
  T4Universal.lift_t _ _ _ _ _ _ _

def fiberSpec : F →ₗ⁅ℚ⁆ L := FreeLieAlgebra.lift ℚ
  (fun i => if i = 0 then x else if i = 1 then y else -x-y)
def baseSpec : L →ₗ⁅ℚ⁆ L := eval (-x-y) x

/--
@isnad1 id=eq.0h0v.s6.a762a7724cd9 from=translated src=- shape=5f004dda vocab=49f4f2b9
-/
@[simp] theorem fiberSpec_fa : fiberSpec fa = x := by simp [fiberSpec,fa]
/--
@isnad1 id=eq.0h0v.s6.ad15cfc89e9a from=translated src=- shape=5f004dda vocab=b2c21792
-/
@[simp] theorem fiberSpec_fb : fiberSpec fb = y := by simp [fiberSpec,fb]
/--
@isnad1 id=eq.0h0v.s6.fa9c9ab481c6 from=translated src=- shape=3201ba7a vocab=6c9d9fe2
-/
@[simp] theorem fiberSpec_fc : fiberSpec fc = -x-y := by simp [fiberSpec,fc]
/--
@isnad1 id=eq.0h0v.s6.2bcc03ce35cf from=translated src=- shape=6f5849f3 vocab=91a8b1a7
-/
@[simp] theorem baseSpec_x : baseSpec x = -x-y := eval_x _ _
/--
@isnad1 id=eq.0h0v.s5.dc8595ba8329 from=translated src=- shape=00497b90 vocab=a1fbeb4c
-/
@[simp] theorem baseSpec_y : baseSpec y = x := eval_y _ _

/--
@isnad1 id=eq.0h2v.s9.07028eb74163 from=translated src=- shape=21114cbf vocab=051edaaa
-/
theorem spec_equivariant (q : L) (p : F) :
    fiberSpec (action q p) = ⁅baseSpec q,fiberSpec p⁆ := by
  apply free_action_inner
  intro i j
  cases i <;> fin_cases j <;>
    simp [action, eval, baseSpec, fiberSpec, FreeDerivations.pair,
      x,y,sub_lie,neg_lie,lie_sub,lie_neg]

def specialize : M →ₗ⁅ℚ⁆ L := InnerSemiDirect.lift action fiberSpec baseSpec spec_equivariant

/--
@isnad1 id=eq.0h0v.s7.5b11dae2a157 from=translated src=- shape=5f004dda vocab=26191b14
-/
@[simp] theorem specialize_a : specialize a = x := by simp [specialize,a, InnerSemiDirect.lift]
/--
@isnad1 id=eq.0h0v.s7.0ba9c1eeb620 from=translated src=- shape=5f004dda vocab=2cbf1f75
-/
@[simp] theorem specialize_b : specialize b = y := by simp [specialize,b, InnerSemiDirect.lift]
/--
@isnad1 id=eq.0h0v.s7.b7f2b1ec905d from=translated src=- shape=3201ba7a vocab=53e1c791
-/
@[simp] theorem specialize_c : specialize c = -x-y := by simp [specialize,c, InnerSemiDirect.lift]
/--
@isnad1 id=eq.0h0v.s7.25b640d0f8d0 from=translated src=- shape=3201ba7a vocab=8519d7b3
-/
@[simp] theorem specialize_u : specialize u = -x-y := by simp [specialize,u, InnerSemiDirect.lift]
/--
@isnad1 id=eq.0h0v.s7.bbf7f4f81962 from=translated src=- shape=5f004dda vocab=45edb807
-/
@[simp] theorem specialize_v : specialize v = x := by simp [specialize,v, InnerSemiDirect.lift]

/--
@isnad1 id=eq.0h3v.s8.f0c43b166e89 from=translated src=- shape=991ac3b7 vocab=9e4b11fd
-/
@[simp] theorem eval_right (d e : M) (p : L) :
    (eval d e p).right = eval d.right e.right p :=
  map_eval (SemiDirectSum.projr action) d e p

def Fa (p : L) : F := (eval (u+b) v p - eval u v p).left
def Fb (p : L) : F := (eval (u+a) (v+c) p - eval u v p).left
def Fc (p : L) : F := (eval u (v+b) p - eval u v p).left

 /--
 @isnad1 id=eq.0h1v.s9.33eca9c7f70c from=translated src=- shape=b48ef45c vocab=865af3b9
 -/
 theorem Fa_inl (p : L) : SemiDirectSum.inl action (Fa p) = eval (u+b) v p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,b,v]
 /--
 @isnad1 id=eq.0h1v.s9.df125691e60e from=translated src=- shape=9dcc2710 vocab=d0f95019
 -/
 theorem Fb_inl (p : L) : SemiDirectSum.inl action (Fb p) = eval (u+a) (v+c) p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,a,v,c]
 /--
 @isnad1 id=eq.0h1v.s9.bccbe456541f from=translated src=- shape=6e4ba533 vocab=2383e0c3
 -/
 theorem Fc_inl (p : L) : SemiDirectSum.inl action (Fc p) = eval u (v+b) p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,b,v]

/--
@isnad1 id=eq.0h1v.s8.14f122762e49 from=translated src=- shape=49a64e1b vocab=9ea8bad6
-/
theorem eval_comm_a (p : L) : ⁅a,eval (u+b) v p⁆ = 0 := by
  apply eval_commutes
  · rw [lie_add,au]; exact neg_add_cancel _
  · exact av
/--
@isnad1 id=eq.0h1v.s8.65897e9756c7 from=translated src=- shape=79f809fa vocab=04218c20
-/
theorem eval_comm_b (p : L) : ⁅b,eval (u+a) (v+c) p⁆ = 0 := by
  apply eval_commutes
  · rw [lie_add,bu]; grind [lie_skew]
  · rw [lie_add,bv]; exact neg_add_cancel _
/--
@isnad1 id=eq.0h1v.s8.cfbb180a775c from=translated src=- shape=2421f257 vocab=a3166efb
-/
theorem eval_comm_c (p : L) : ⁅c,eval u (v+b) p⁆ = 0 := by
  apply eval_commutes
  · exact cu
  · rw [lie_add,cv]; grind [lie_skew]
/--
@isnad1 id=eq.0h1v.s8.f8dcd9b557a3 from=translated src=- shape=968e3714 vocab=04218c20
-/
theorem eval_comm_sum (p : L) : ⁅a+b+c,eval u v p⁆ = 0 := by
  apply eval_commutes
  · rw [add_lie,add_lie,au,bu,cu]; abel
  · rw [add_lie,add_lie,av,bv,cv]; abel

/--
@isnad1 id=eq.0h1v.s7.170f9c06fe2c from=translated src=- shape=67332673 vocab=0e0d12db
-/
theorem fiber_identity (p : L) :
    ⁅fa+fb+fc,Fb p⁆ = ⁅fa,Fb p-Fa p⁆ + ⁅fc,Fb p-Fc p⁆ := by
  apply SemiDirectSum.inl_injective action
  simp only [LieHom.map_lie, map_add, map_sub, Fa_inl,Fb_inl,Fc_inl]
  change ⁅a+b+c,eval (u+a) (v+c) p - eval u v p⁆ =
    ⁅a,(eval (u+a) (v+c) p - eval u v p) - (eval (u+b) v p - eval u v p)⁆ +
    ⁅c,(eval (u+a) (v+c) p - eval u v p) - (eval u (v+b) p - eval u v p)⁆
  rw [lie_sub,eval_comm_sum]
  simp only [lie_sub,add_lie,eval_comm_a,eval_comm_b,eval_comm_c]
  abel

/--
@isnad1 id=eq.2h2v.s8.a5345fbee87b from=translated src=- shape=87762c14 vocab=6c187fa6
-/
theorem Fb_specialize {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    fiberSpec (Fb p) = -eval (-x-y) x p := by
  have H := congrArg specialize (Fb_inl p)
  rw [show specialize (SemiDirectSum.inl action (Fb p)) = fiberSpec (Fb p) from
    InnerSemiDirect.lift_inl _ _ _ _ _] at H
  simp only [map_sub,map_eval,map_add,specialize_u,specialize_a,specialize_v,specialize_c] at H
  have ha : -x-y+x = -y := by abel
  have hb : x+(-x-y) = -y := by abel
  rw [ha,hb,eval_vanish_of_commuting (-y) (-y) (lie_self _) hp hn,zero_sub] at H
  exact H

/--
@isnad1 id=eq.1h1v.s10.831e2e224d00 from=translated src=- shape=8096973e vocab=ee4cba0b
-/
theorem pentagon {p : L} (hp : p ∈ W) :
    eval a (b+c) p + eval (u+b) v p =
    eval b v p + eval (a+u) (c+v) p + eval a b p := by
  have h := congrArg representation hp.2.2
  simpa [map_eval,chord] using h

/--
@isnad1 id=eq.1h1v.s10.e695daca611d from=translated src=- shape=8096973e vocab=ee4cba0b
-/
theorem pentagon_reverse {p : L} (hp : p ∈ W) :
    eval c (b+a) p + eval (v+b) u p =
    eval b u p + eval (c+v) (a+u) p + eval c b p := by
  have h := congrArg (representation.comp (t4Rename (Equiv.swap 0 3))) hp.2.2
  simp only [LieHom.comp_apply,map_add,map_eval,t4Rename_t,representation_t] at h
  exact h

/--
@isnad1 id=eq.2h2v.s9.f9a6f9a9a222 from=translated src=- shape=438f39f0 vocab=e67be1e1
-/
theorem eval_bv_shift {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    eval b v p = eval b (-b-c) p := by
  have H := eval_central_shift b (-b-c) (v+b+c) (p := p) (n := n) ?_ ?_ hp hn
  · have he : -b-c+(v+b+c) = v := by abel
    simpa only [he] using H
  · simp only [lie_add,lie_self,bv]
    abel
  · simp only [sub_lie,neg_lie,lie_add,lie_self,bv,cv]
    grind [lie_skew]

/--
@isnad1 id=eq.2h2v.s9.027719c16cec from=translated src=- shape=438f39f0 vocab=49be7181
-/
theorem eval_bu_shift {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    eval b u p = eval b (-b-a) p := by
  have H := eval_central_shift b (-b-a) (u+b+a) (p := p) (n := n) ?_ ?_ hp hn
  · have he : -b-a+(u+b+a) = u := by abel
    simpa only [he] using H
  · simp only [lie_add,lie_self,bu]
    grind [lie_skew]
  · simp only [sub_lie,neg_lie,lie_add,lie_self,bu,au]
    grind [lie_skew]

/--
@isnad1 id=eq.3h2v.s9.d47189e673f6 from=translated src=- shape=611b70d9 vocab=376049c8
-/
theorem delta_a {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n) (hn : 1<n) :
    Fb p-Fa p = eval fa (fb+fc) p - eval fa fb p - eval fb (-fb-fc) p := by
  apply SemiDirectSum.inl_injective action
  simp only [map_sub,map_eval,map_add,map_neg,Fb_inl,Fa_inl]
  change (eval (u+a) (v+c) p - eval u v p) - (eval (u+b) v p - eval u v p) =
    eval a (b+c) p - eval a b p - eval b (-b-c) p
  have H := pentagon hp
  rw [eval_bv_shift hpn hn,add_comm a u,add_comm c v] at H
  grind only

/--
@isnad1 id=eq.3h2v.s9.3c3aca026949 from=translated src=- shape=06003748 vocab=2c1b1f7a
-/
theorem delta_c {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n) (hn : 1<n) :
    Fb p-Fc p = -eval fc (fa+fb) p + eval fc fb p + eval fb (-fb-fa) p := by
  apply SemiDirectSum.inl_injective action
  simp only [map_sub,map_eval,map_add,map_neg,Fb_inl,Fc_inl]
  change (eval (u+a) (v+c) p - eval u v p) - (eval u (v+b) p - eval u v p) =
    -eval c (a+b) p + eval c b p + eval b (-b-a) p
  have H := pentagon_reverse hp
  rw [eval_bu_shift hpn hn,solution_swap hp (v+b) u,solution_swap hp (c+v) (a+u),
    add_comm b a,add_comm a u,add_comm c v] at H
  grind only

end SpecialFiber

namespace Differentiation
open FreeDerivations

variable {M N : Type} [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]

/--
@isnad1 id=eq.0h2v.s6.62a133b90299 from=translated src=- shape=5829f91c vocab=705159b6
-/
@[simp] theorem Jet.base_neg (p : Jet ℚ M) : (-p).base = -p.base := rfl
/--
@isnad1 id=eq.0h2v.s6.3283a52bc6ff from=translated src=- shape=5829f91c vocab=13b8640c
-/
@[simp] theorem Jet.velocity_neg (p : Jet ℚ M) : (-p).velocity = -p.velocity := rfl
/--
@isnad1 id=eq.0h3v.s6.380f28a08c6c from=translated src=- shape=c0928747 vocab=38bf9d87
-/
@[simp] theorem Jet.base_sub (p q : Jet ℚ M) : (p-q).base = p.base-q.base := rfl
/--
@isnad1 id=eq.0h3v.s6.628298133e27 from=translated src=- shape=c0928747 vocab=e2742eee
-/
@[simp] theorem Jet.velocity_sub (p q : Jet ℚ M) : (p-q).velocity = p.velocity-q.velocity := rfl

/--
@isnad1 id=eq.0h5v.s7.464431e7cc5f from=translated src=- shape=4e565b25 vocab=a29de0c1
-/
@[simp] theorem Jet.mk_add (a b da db : M) :
    (Jet.mk a da : Jet ℚ M) + Jet.mk b db = Jet.mk (a+b) (da+db) := rfl
/--
@isnad1 id=eq.0h3v.s6.d248b487df8d from=translated src=- shape=22fc7874 vocab=7bdb463a
-/
@[simp] theorem Jet.mk_neg (a da : M) :
    -(Jet.mk a da : Jet ℚ M) = Jet.mk (-a) (-da) := rfl
/--
@isnad1 id=eq.0h5v.s7.4adc0cacd1aa from=translated src=- shape=4e565b25 vocab=31eb60ab
-/
@[simp] theorem Jet.mk_sub (a b da db : M) :
    (Jet.mk a da : Jet ℚ M) - Jet.mk b db = Jet.mk (a-b) (da-db) := rfl

/--
@isnad1 id=eq.0h4v.s7.3cb5d4b515fb from=translated src=- shape=28b7e987 vocab=2c61358a
-/
@[simp] theorem eval_base (a b : Jet ℚ M) (p : L) :
    (eval a b p).base = eval a.base b.base p := map_eval Jet.baseHom a b p

def adPower (a : M) : ℕ → M → M
  | 0, t => t
  | n+1, t => ⁅a,adPower a n t⁆

omit [LieAlgebra ℚ M] in
/--
@isnad1 id=eq.0h3v.s4.1d502500d92d from=translated src=- shape=3833cb09 vocab=88d2241f
-/
@[simp] theorem adPower_zero (a t : M) : adPower a 0 t = t := rfl
omit [LieAlgebra ℚ M] in
/--
@isnad1 id=eq.0h4v.s5.b1b33c3a347c from=translated src=- shape=995e4dfe vocab=734cfe7e
-/
@[simp] theorem adPower_succ (a t : M) (n : ℕ) : adPower a (n+1) t = ⁅a,adPower a n t⁆ := rfl
/--
@isnad1 id=eq.0h5v.s7.37d8f1e69952 from=translated src=- shape=b79e812d vocab=d768f064
-/
@[simp] theorem adPower_smul (a t : M) (n : ℕ) (r : ℚ) :
    adPower a n (r • t) = r • adPower a n t := by
  induction n <;> simp_all
omit [LieAlgebra ℚ M] in
/--
@isnad1 id=eq.0h3v.s5.ad362d248ab0 from=translated src=- shape=07a1cab9 vocab=88d2241f
-/
@[simp] theorem adPower_zero_right (a : M) (n : ℕ) : adPower a n 0 = 0 := by
  induction n <;> simp_all
omit [LieAlgebra ℚ M] in
/--
@isnad1 id=eq.1h3v.s5.935588214c95 from=translated src=- shape=1ffaccf9 vocab=a2e968eb
-/
@[simp] theorem adPower_self (a : M) {n : ℕ} (hn : 0<n) : adPower a n a = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih => simp_all
omit [LieAlgebra ℚ M] in
/--
@isnad1 id=eq.1h3v.s5.f1dbae90dfd0 from=translated src=- shape=e6c3b3bc vocab=a2e968eb
-/
@[simp] theorem adPower_zero_left (t : M) {n : ℕ} (hn : 0<n) : adPower (0:M) n t = 0 := by
  cases n <;> simp_all

def slope (p : L) (a b da db : M) : M :=
  (eval (Jet.mk a da : Jet ℚ M) (Jet.mk b db) p).velocity

/--
@isnad1 id=eq.0h5v.s4.e4ce95ed6507 from=translated src=- shape=fedfdf0c vocab=897f3f10
-/
@[simp] theorem slope_x (a b da db : M) : slope x a b da db = da := by simp [slope]
/--
@isnad1 id=eq.0h5v.s4.3b8781006317 from=translated src=- shape=54048240 vocab=0a5ef597
-/
@[simp] theorem slope_y (a b da db : M) : slope y a b da db = db := by simp [slope]
/--
@isnad1 id=eq.0h5v.s5.a330e493b12c from=translated src=- shape=41821439 vocab=7eedad7b
-/
@[simp] theorem slope_zero (a b da db : M) : slope 0 a b da db = 0 := by simp [slope]
/--
@isnad1 id=eq.0h7v.s6.87b0a85b5f6b from=translated src=- shape=581dbdf0 vocab=5de6c3cb
-/
@[simp] theorem slope_add (p q : L) (a b da db : M) :
    slope (p+q) a b da db = slope p a b da db + slope q a b da db := by simp [slope]
/--
@isnad1 id=eq.0h7v.s7.6ac91245b2cf from=translated src=- shape=4ff8a03c vocab=1d6a8394
-/
@[simp] theorem slope_smul (r : ℚ) (p : L) (a b da db : M) :
    slope (r • p) a b da db = r • slope p a b da db := by simp [slope]
/--
@isnad1 id=eq.0h7v.s7.c24e0451ae1b from=translated src=- shape=749d4ecd vocab=24705edc
-/
@[simp] theorem slope_lie (p q : L) (a b da db : M) :
    slope ⁅p,q⁆ a b da db = ⁅slope p a b da db,eval a b q⁆ +
      ⁅eval a b p,slope q a b da db⁆ := by simp [slope,LieHom.map_lie]

/--
@isnad1 id=eq.0h4v.s6.fd37229727c5 from=translated src=- shape=8d4461b4 vocab=0eafe61d
-/
@[simp] theorem slope_zero_direction (p : L) (a b : M) : slope p a b 0 0 = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq]

/--
@isnad1 id=eq.0h8v.s6.f40e6a0af5e8 from=translated src=- shape=e5ee0aa1 vocab=e3aa2c25
-/
theorem slope_add_direction (p : L) (a b da db ea eb : M) :
    slope p a b (da+ea) (db+eb) = slope p a b da db + slope p a b ea eb := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq => simp [hp,hq,add_lie,lie_add]; abel

/--
@isnad1 id=eq.0h7v.s7.e62b40fa560a from=translated src=- shape=ca6c0c8e vocab=845b153c
-/
theorem slope_smul_direction (p : L) (a b da db : M) (r : ℚ) :
    slope p a b (r • da) (r • db) = r • slope p a b da db := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq,smul_add]
  | hs s p hp => simp [hp,smul_comm s r]
  | hl p q hp hq => simp [hp,hq,smul_add]

/--
@isnad1 id=lt.1h2v.s4.8d70c1bbf8e9 from=translated src=- shape=19048bc8 vocab=efc8366a
-/
theorem word_pos {n : ℕ} {p : L} (hp : WeightedWord (fun _:Bool => 1) n p) : 0<n := by
  induction hp with
  | generator => omega
  | bracket hp hq ihp ihq => omega

def DiagonalData (n : ℕ) (p : L) (s k : ℚ) : Prop :=
  (n ≠ 1 → s = 0) ∧ ∀ (M : Type) [LieRing M] [LieAlgebra ℚ M] (a t : M),
    eval (Jet.mk a 0 : Jet ℚ M) (Jet.mk (-a) t) p =
      Jet.mk (s • a) (k • adPower a (n-1) t)

/--
@isnad1 id=ex.4h8v.s6.6f499b343e43 from=translated src=- shape=6ad70e67 vocab=a118bb01
-/
theorem diagonal_bracket {n m : ℕ} {p q : L} {s k t l : ℚ}
    (hn : 0 < n) (hm : 0 < m) (hp : DiagonalData n p s k) (hq : DiagonalData m q t l) :
    ∃ r : ℚ, DiagonalData (n+m) ⁅p,q⁆ 0 r := by
  rcases hp with ⟨hs,hp⟩
  rcases hq with ⟨ht,hq⟩
  by_cases hn1 : n=1 <;> by_cases hm1 : m=1
  · subst n; subst m
    refine ⟨s*l-t*k, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · change ⁅k • b,t • a⁆ + ⁅s • a,l • b⁆ = (s*l-t*k) • ⁅a,b⁆
      rw [smul_lie,lie_smul,←lie_skew b a,smul_neg,smul_lie,lie_smul]
      simp only [sub_smul,mul_smul]
      module
  · subst n
    have ht0 := ht hm1
    subst t
    refine ⟨s*l, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · have he : 1+m-1 = (m-1)+1 := by omega
      simp [he,mul_smul,smul_comm l s]
  · subst m
    have hs0 := hs hn1
    subst s
    refine ⟨-(t*k), fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · have he : n+1-1 = (n-1)+1 := by omega
      simp only [Jet.velocity_lie,zero_smul,zero_lie,he,adPower_succ,
        smul_lie,lie_smul,neg_smul,mul_smul]
      rw [←lie_skew (adPower a (n-1) b) a,smul_neg,smul_neg]
      rw [smul_comm]
      simp
  · have hs0 := hs hn1
    have ht0 := ht hm1
    subst s; subst t
    refine ⟨0, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext <;> simp

/--
@isnad1 id=ex.1h2v.s4.d9f3d65d79ba from=translated src=- shape=28b08565 vocab=f4f9c226
-/
theorem diagonal_word {n : ℕ} {p : L} (hp : WeightedWord (fun _:Bool => 1) n p) :
    ∃ s k : ℚ, DiagonalData n p s k := by
  induction hp with
  | generator i =>
    cases i
    · refine ⟨1,0, ?_⟩
      constructor
      · simp
      · intro M _ _ a b; simp [eval]
    · refine ⟨-1,1, ?_⟩
      constructor
      · simp
      · intro M _ _ a b; simp [eval]
  | bracket hp hq ihp ihq =>
    rcases ihp with ⟨s,k,hp'⟩
    rcases ihq with ⟨t,l,hq'⟩
    obtain ⟨r,hr⟩ := diagonal_bracket (word_pos hp) (word_pos hq) hp' hq'
    exact ⟨0,r,hr⟩

/--
@isnad1 id=ex.1h2v.s6.639ec479ea76 from=translated src=- shape=98f2d3b8 vocab=aa7538c0
-/
theorem diagonal_homogeneous {n : ℕ} {p : L} (hp : p ∈ Ln n) :
    ∃ s k : ℚ, DiagonalData n p s k := by
  induction hp using Submodule.span_induction with
  | mem p hp => exact diagonal_word hp
  | zero =>
    refine ⟨0,0,fun _ => rfl,?_⟩
    intro M _ _ a b
    ext <;> simp
  | add p q _ _ hp hq =>
    rcases hp with ⟨s,k,hs,hp⟩
    rcases hq with ⟨t,l,ht,hq⟩
    refine ⟨s+t,k+l,fun hn => by simp [hs hn,ht hn],?_⟩
    intro M _ _ a b
    rw [map_add,hp,hq]
    ext <;> simp [add_smul]
  | smul r p _ hp =>
    rcases hp with ⟨s,k,hs,hp⟩
    refine ⟨r*s,r*k,fun hn => by simp [hs hn],?_⟩
    intro M _ _ a b
    rw [map_smul,hp]
    ext <;> simp [mul_smul]

 /--
 @isnad1 id=eq.0h6v.s6.adbf0c54dcb1 from=translated src=- shape=a2e4f88c vocab=b912c88a
 -/
 theorem slope_neg_direction (p : L) (a b da db : M) :
    slope p a b (-da) (-db) = -slope p a b da db := by
  simpa using slope_smul_direction p a b da db (-1)

 /--
 @isnad1 id=eq.0h5v.s6.6f63d174b189 from=translated src=- shape=a1f58642 vocab=47b5b5bf
 -/
 theorem slope_inner (p : L) (a b t : M) :
    slope p a b ⁅t,a⁆ ⁅t,b⁆ = ⁅t,eval a b p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq,LieHom.map_lie,lie_lie]

 /--
 @isnad1 id=eq.1h6v.s6.9c0a71310821 from=translated src=- shape=8d83bca2 vocab=fe6ddf91
 -/
 theorem slope_swap {p : L} (hp : p ∈ W) (a b da db : M) :
    slope p a b da db = -slope p b a db da := by
  exact congrArg Jet.velocity (solution_swap hp (Jet.mk a da : Jet ℚ M) (Jet.mk b db))

 /--
 @isnad1 id=eq.1h7v.s7.b2b642e5ce81 from=translated src=- shape=01038a65 vocab=0e97571d
 -/
 theorem diagonal_slope {n : ℕ} {p : L} {s k : ℚ}
    (hp : DiagonalData n p s k) (a t : M) :
    slope p a (-a) 0 t = k • adPower a (n-1) t :=
  congrArg Jet.velocity (hp.2 M a t)

 /--
 @isnad1 id=eq.2h5v.s7.e9caeb5ad731 from=translated src=- shape=4d145ec1 vocab=c2cb067f
 -/
 theorem diagonal_first {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) (a t : M) :
    slope p a (-a) t 0 = slope p a (-a) 0 t := by
  have H := congrArg Jet.velocity (eval_vanish_of_commuting
    (Jet.mk a t : Jet ℚ M) (-Jet.mk a t) (by rw [lie_neg,lie_self,neg_zero]) hp hn)
  change slope p a (-a) t (-t) = 0 at H
  have hs := slope_add_direction p a (-a) t 0 0 (-t)
  have hneg := slope_neg_direction p a (-a) 0 t
  simp only [neg_zero] at hneg
  simp only [add_zero,zero_add,hneg,H] at hs
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hs.symm)

 def G (p : L) : L := ⁅x,eval y x p⁆ + ⁅-x-y,eval y (-x-y) p⁆

 /--
 @isnad1 id=eq.0h4v.s7.2ea253bc42fb from=translated src=- shape=0047a77f vocab=41474cd3
 -/
 theorem eval_G (p : L) (a b : M) :
    eval a b (G p) = ⁅a,eval b a p⁆ + ⁅-a-b,eval b (-a-b) p⁆ := by
  simp only [G,map_add,LieHom.map_lie,map_eval,eval_x,eval_y,map_sub,map_neg]

 /--
 @isnad1 id=eq.0h5v.s8.78223c087c3c from=translated src=- shape=9931b6df vocab=63073fd4
 -/
 theorem slope_G (p : L) (a b t : M) :
    slope (G p) a b t 0 =
      ⁅t,eval b a p-eval b (-a-b) p⁆ +
      ⁅a,slope p b a 0 t⁆ - ⁅-a-b,slope p b (-a-b) 0 t⁆ := by
  have hh := congrArg Jet.velocity (eval_G p (Jet.mk a t : Jet ℚ M) (Jet.mk b 0))
  change slope (G p) a b t 0 = _ at hh
  simp only [Jet.mk_neg,Jet.mk_sub,sub_zero] at hh
  simp only [Jet.velocity_add,Jet.velocity_lie,eval_base] at hh
  have he : slope p b (-a-b) 0 (-t) = -slope p b (-a-b) 0 t := by
    simpa only [neg_zero] using slope_neg_direction p b (-a-b) 0 t
  change slope (G p) a b t 0 = ⁅t,eval b a p⁆ + ⁅a,slope p b a 0 t⁆ +
    (⁅-t,eval b (-a-b) p⁆ + ⁅-a-b,slope p b (-a-b) 0 (-t)⁆) at hh
  rw [he,neg_lie,lie_neg] at hh
  rw [lie_sub]
  grind only

 def fiberEval (a b c : M) : SpecialFiber.F →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun i => if i=0 then a else if i=1 then b else c)
/--
@isnad1 id=eq.0h4v.s6.d1f787c69b63 from=translated src=- shape=bb96d991 vocab=d26f8a6d
-/
@[simp] theorem fiberEval_fa (a b c : M) : fiberEval a b c SpecialFiber.fa = a := by
  simp [fiberEval,SpecialFiber.fa]
/--
@isnad1 id=eq.0h4v.s6.17d5b1df564e from=translated src=- shape=03e3b827 vocab=6af9aa86
-/
@[simp] theorem fiberEval_fb (a b c : M) : fiberEval a b c SpecialFiber.fb = b := by
  simp [fiberEval,SpecialFiber.fb]
/--
@isnad1 id=eq.0h4v.s6.a8c8ff796555 from=translated src=- shape=d54d7370 vocab=3d49bb72
-/
@[simp] theorem fiberEval_fc (a b c : M) : fiberEval a b c SpecialFiber.fc = c := by
  simp [fiberEval,SpecialFiber.fc]

 /--
 @isnad1 id=eq.0h4v.s7.0b51dfd2cea6 from=translated src=- shape=44fbae9c vocab=457ba110
 -/
 theorem fiberEval_spec (a b : M) (z : SpecialFiber.F) :
    fiberEval a b (-a-b) z = eval a b (SpecialFiber.fiberSpec z) := by
  have h : fiberEval a b (-a-b) = (eval a b).comp SpecialFiber.fiberSpec := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,SpecialFiber.fiberSpec]
  exact LieHom.congr_fun h z

/--
@isnad1 id=eq.0h5v.s7.844ad3efb38a from=translated src=- shape=29fa8261 vocab=26266294
-/
@[simp] theorem fiberEval_base (a b c : Jet ℚ M) (z : SpecialFiber.F) :
    (fiberEval a b c z).base = fiberEval a.base b.base c.base z := by
  have h : Jet.baseHom.comp (fiberEval a b c) = fiberEval a.base b.base c.base := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,Jet.baseHom] <;> rfl
  exact LieHom.congr_fun h z

 /--
 @isnad1 id=eq.2h5v.s8.bec73bf5280d from=translated src=- shape=260a3574 vocab=7137be60
 -/
 theorem fiberEval_Fb {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) (a b : M) :
    fiberEval a b (-a-b) (SpecialFiber.Fb p) = - eval (-a-b) a p := by
  rw [fiberEval_spec,SpecialFiber.Fb_specialize hp hn]
  simp [map_eval]

 /--
 @isnad1 id=eq.4h7v.s9.c04487219279 from=translated src=- shape=bc2d6d92 vocab=51bec226
 -/
 theorem transverse {n : ℕ} {p : L} {k : ℚ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 1<n) (hdiag : DiagonalData n p 0 k) (a b t : M) :
    -⁅t,eval (-a-b) a p⁆ = k • (adPower a n t-adPower (-a-b) n t) +
       ⁅a,slope p b a 0 t⁆ - ⁅-a-b,slope p b (-a-b) 0 t⁆ := by
  have H := congrArg (fiberEval (Jet.mk a 0 : Jet ℚ M) (Jet.mk b 0)
    (Jet.mk (-a-b) t)) (SpecialFiber.fiber_identity p)
  rw [SpecialFiber.delta_a hp hpn hn,SpecialFiber.delta_c hp hpn hn] at H
  simp only [LieHom.map_lie,map_add,map_sub,map_neg,map_eval,
    fiberEval_fa,fiberEval_fb,fiberEval_fc] at H
  have hc : (Jet.mk a 0 : Jet ℚ M) + Jet.mk b 0 + Jet.mk (-a-b) t = Jet.mk 0 t := by
    ext <;> simp
  rw [hc] at H
  simp only [Jet.mk_add,Jet.mk_neg,Jet.mk_sub,zero_add,add_zero,neg_zero,sub_zero,zero_sub] at H
  have Hv := congrArg Jet.velocity H
  simp only [Jet.velocity_lie,Jet.velocity_sub,Jet.velocity_add,Jet.velocity_neg,
    Jet.base_add,Jet.base_sub,Jet.base_neg,eval_base,fiberEval_base] at Hv
  have hdiagNeg : -(-a-b) = a+b := by abel
  have hba : b+(-a-b) = -a := by abel
  have hab : -b-(-a-b) = a := by abel
  have hc0 : eval (-a-b) (a+b) p = 0 := by
    have h := eval_vanish_of_commuting (-a-b) (-(-a-b)) (by simp only [lie_neg,lie_self,neg_zero]) hpn hn
    simpa only [hdiagNeg] using h
  have hdelc : -eval (-a-b) (a+b) p + eval (-a-b) b p + eval b (-b-a) p = 0 := by
    rw [hc0,neg_zero,zero_add,solution_swap hp (-a-b) b]
    have he : -b-a = -a-b := by abel
    rw [he,neg_add_cancel]
  have hdp : slope p (-a-b) (a+b) t 0 = k • adPower (-a-b) (n-1) t := by
    rw [← hdiagNeg,diagonal_first hpn hn,diagonal_slope hdiag]
  have hdm : slope p b a 0 (-t) = -slope p b a 0 t := by
    simpa only [neg_zero] using slope_neg_direction p b a 0 t
  have hswap := slope_swap hp (-a-b) b t 0
  have hnp : n=(n-1)+1 := by omega
  change ⁅t,fiberEval a b (-a-b) (SpecialFiber.Fb p)⁆ + ⁅(0:M),_⁆ =
    (⁅(0:M),_⁆ + ⁅a,slope p a (b+(-a-b)) 0 t - slope p a b 0 0 -
      slope p b (-b-(-a-b)) 0 (-t)⁆) +
    (⁅t,-eval (-a-b) (a+b) p + eval (-a-b) b p + eval b (-b-a) p⁆ +
      ⁅-a-b,-slope p (-a-b) (a+b) t 0 + slope p (-a-b) b t 0 +
        slope p b (-b-a) 0 0⁆) at Hv
  rw [fiberEval_Fb hpn hn,hdelc,hba,hab,slope_zero_direction,slope_zero_direction,
    diagonal_slope hdiag,hdp,hdm,hswap] at Hv
  simp only [zero_lie,lie_zero,add_zero,zero_add,sub_zero,lie_neg,lie_sub,lie_add,lie_smul] at Hv
  rw [show ⁅a,adPower a (n-1) t⁆ = adPower a n t by rw [hnp]; rfl,
    show ⁅-a-b,adPower (-a-b) (n-1) t⁆ = adPower (-a-b) n t by rw [hnp]; rfl] at Hv
  rw [smul_sub]
  grind only

 /--
 @isnad1 id=eq.4h7v.s8.0e9a7601e471 from=translated src=- shape=b01c8708 vocab=42611236
 -/
 theorem slope_G_formula {n : ℕ} {p : L} {k : ℚ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 1<n) (hdiag : DiagonalData n p 0 k) (a b t : M) :
    slope (G p) a b t 0 = - k • (adPower a n t-adPower (-a-b) n t) := by
  have H := transverse hp hpn hn hdiag a b t
  have h3 := solution_three hp a b
  rw [solution_swap hp a b] at h3
  have he : eval b a p - eval b (-a-b) p = eval (-a-b) a p := by grind only
  rw [slope_G,he,neg_smul]
  grind only

def swapJet : Jet ℚ (Jet ℚ M) →ₗ⁅ℚ⁆ Jet ℚ (Jet ℚ M) where
  toFun z := ⟨⟨z.base.base,z.velocity.base⟩,⟨z.base.velocity,z.velocity.velocity⟩⟩
  map_add' a b := by apply Jet.ext <;> apply Jet.ext <;> rfl
  map_smul' r a := by apply Jet.ext <;> apply Jet.ext <;> rfl
  map_lie' {a b} := by
    apply Jet.ext <;> apply Jet.ext
    all_goals simp only [Jet.base_lie,Jet.velocity_lie,Jet.base_add,Jet.velocity_add]
    all_goals first | rfl | abel

/--
@isnad1 id=eq.0h6v.s8.87fb9d92adc9 from=translated src=- shape=cea080ca vocab=198512c5
-/
theorem mixed_slope (p : L) (a b u v : M) :
    (slope p (Jet.mk a u : Jet ℚ M) (Jet.mk b 0) (Jet.mk v 0) 0).velocity =
    (slope p (Jet.mk a v : Jet ℚ M) (Jet.mk b 0) (Jet.mk u 0) 0).velocity := by
  have h := map_eval (swapJet : Jet ℚ (Jet ℚ M) →ₗ⁅ℚ⁆ Jet ℚ (Jet ℚ M))
    (Jet.mk (Jet.mk a u) (Jet.mk v 0)) (Jet.mk (Jet.mk b 0) 0) p
  exact congrArg (fun z => z.velocity.velocity) h

/--
@isnad1 id=eq.0h4v.s6.8daf750d3db4 from=translated src=- shape=ed2b3360 vocab=3e5de9a0
-/
@[simp] theorem adPower_base (a t : Jet ℚ M) (n : ℕ) :
    (adPower a n t).base = adPower a.base n t.base := by
  induction n <;> simp_all

/--
@isnad1 id=eq.0h4v.s7.985e71574d0f from=translated src=- shape=2632b10d vocab=cac1b06e
-/
theorem adPower_radial (a t : M) (n : ℕ) :
    (adPower (Jet.mk a a : Jet ℚ M) n (Jet.mk t 0)).velocity =
      (n : ℚ) • adPower a n t := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [adPower_succ,Jet.velocity_lie,adPower_base,ih,lie_smul,
      Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    abel

/--
@isnad1 id=eq.1h4v.s6.60791ce3accc from=translated src=- shape=1f8db301 vocab=3cc7ca54
-/
theorem adPower_transverse_self (a t : M) {n : ℕ} (hn : 0<n) :
    (adPower (Jet.mk a t : Jet ℚ M) n (Jet.mk a 0)).velocity = -adPower a n t := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp [lie_skew]
    | succ n ih =>
      rw [adPower_succ,Jet.velocity_lie,adPower_base]
      change ⁅t,adPower a (n+1) a⁆ +
        ⁅a,(adPower (Jet.mk a t : Jet ℚ M) (n+1) (Jet.mk a 0)).velocity⁆ = _
      rw [adPower_self a (n := n+1) (by omega),lie_zero,zero_add,ih (by omega),lie_neg]
      rfl

/--
@isnad1 id=eq.1h4v.s6.80f1d6da19dd from=translated src=- shape=93735d58 vocab=e1eb9497
-/
theorem adPower_zero_base (a t : M) {n : ℕ} (hn : 1<n) :
    (adPower (Jet.mk 0 a : Jet ℚ M) n (Jet.mk t 0)).velocity = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [adPower_succ,Jet.velocity_lie,adPower_base,zero_lie,add_zero]
    rw [adPower_zero_left t (by omega),lie_zero]

 /--
 @isnad1 id=eq.4h6v.s8.fe59c77daea4 from=translated src=- shape=30c05176 vocab=dc2ab4ab
 -/
 theorem mixed_scalar {n : ℕ} {p : L} {k : ℚ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (hdiag : DiagonalData n p 0 k) (a t : M) :
    (((n : ℚ)+1)*k) • adPower a n t = 0 := by
  have H1 := congrArg Jet.velocity (slope_G_formula hp hpn (by omega) hdiag
    (Jet.mk a a : Jet ℚ M) (Jet.mk (-a) 0) (Jet.mk t 0))
  have H2 := congrArg Jet.velocity (slope_G_formula hp hpn (by omega) hdiag
    (Jet.mk a t : Jet ℚ M) (Jet.mk (-a) 0) (Jet.mk a 0))
  have hc1 : -(Jet.mk a a : Jet ℚ M) - Jet.mk (-a) 0 = Jet.mk 0 (-a) := by
    ext <;> simp
  have hc2 : -(Jet.mk a t : Jet ℚ M) - Jet.mk (-a) 0 = Jet.mk 0 (-t) := by
    ext <;> simp
  rw [hc1] at H1
  rw [hc2] at H2
  simp only [Jet.velocity_smul,Jet.velocity_sub,adPower_radial,
    adPower_zero_base (-a) t (n := n) (by omega),sub_zero] at H1
  simp only [Jet.velocity_smul,Jet.velocity_sub,
    adPower_transverse_self a t (n := n) (by omega),adPower_zero_base (-t) a (n := n) (by omega),sub_zero] at H2
  have hm := mixed_slope (G p) a (-a) a t
  rw [H1,H2] at hm
  have hz : (-k) • ((n:ℚ) • adPower a n t) - (-k) • (-adPower a n t) = 0 := sub_eq_zero.mpr hm
  calc
    (((n : ℚ)+1)*k) • adPower a n t =
        -((-k) • ((n:ℚ) • adPower a n t) - (-k) • (-adPower a n t)) := by module
    _ = 0 := by rw [hz,neg_zero]

 /--
 @isnad1 id=eq.4h3v.s7.5a4567a97863 from=translated src=- shape=f20608a8 vocab=1ad3a760
 -/
 theorem diagonal_scalar_zero {n : ℕ} {p : L} {k : ℚ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (hdiag : DiagonalData n p 0 k) : k=0 := by
  let := LieRing.ofAssociativeRing (A := Matrix (Fin 2) (Fin 2) ℚ)
  let a : Matrix (Fin 2) (Fin 2) ℚ := !![1,0;0,0]
  let t : Matrix (Fin 2) (Fin 2) ℚ := !![0,1;0,0]
  have hbr : ⁅a,t⁆ = t := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a,t,Ring.lie_def,Matrix.mul_apply,Fin.sum_univ_two]
  have had (m : ℕ) : adPower a m t = t := by
    induction m with
    | zero => rfl
    | succ m ih => rw [adPower_succ,ih,hbr]
  have H := mixed_scalar hp hpn hn hdiag a t
  rw [had] at H
  have hc := congrArg (fun z => z 0 1) H
  change (((n : ℚ)+1)*k) * 1 = 0 at hc
  rw [mul_one] at hc
  exact (mul_eq_zero.mp hc).resolve_left (by positivity)

 /--
 @isnad1 id=eq.3h5v.s7.0a60f679bf23 from=translated src=- shape=402a0dcd vocab=759a6a6d
 -/
 theorem special_linearization {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (a t : M) : slope p a (-a) 0 t = 0 := by
  obtain ⟨s,k,hd⟩ := diagonal_homogeneous hpn
  have hs := hd.1 (by omega)
  subst s
  have hk := diagonal_scalar_zero hp hpn hn hd
  rw [diagonal_slope hd,hk,zero_smul]

 /--
 @isnad1 id=eq.3h2v.s7.0592046579ff from=translated src=- shape=103dbbce vocab=a22087ee
 -/
 theorem special_G_zero {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) : G p = 0 := by
  obtain ⟨s,k,hd⟩ := diagonal_homogeneous hpn
  have hs := hd.1 (by omega)
  subst s
  have hk := diagonal_scalar_zero hp hpn hn hd
  subst k
  have hder (t : L) : slope (G p) x y t 0 = 0 := by
    rw [slope_G_formula hp hpn (by omega) hd]
    simp
  have hcomm : ⁅y,G p⁆ = 0 := by
    have h := slope_inner (G p) x y y
    rw [lie_self,eval_self,LieHom.id_apply] at h
    rw [← h,hder]
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
    (AssociativeModel.centralizer_generator true hcomm)
  change r • y = G p at hr
  have he : eval (0 : L) y (G p) = 0 := by
    rw [eval_G]
    simp only [zero_lie,neg_zero,zero_sub,zero_add]
    rw [eval_vanish_of_commuting y (-y) (by simp) hpn (by omega),lie_zero]
  rw [← hr,map_smul,eval_y] at he
  exact hr.symm.trans he

 /--
 @isnad1 id=eq.3h5v.s8.19c7baa5907d from=translated src=- shape=37c05d2f vocab=87daf6fe
 -/
 theorem special_identity {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (a b : M) : ⁅a,eval b a p⁆ + ⁅-a-b,eval b (-a-b) p⁆ = 0 := by
  rw [← eval_G,special_G_zero hp hpn hn,map_zero]

end Differentiation

namespace Elimination
open LieAlgebra
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing
abbrev F (R α : Type*) [CommRing R] := FreeLieAlgebra R (ℕ × α)
abbrev G (R α : Type*) [CommRing R] := FreeLieAlgebra R (Option α)
def X : G R α := FreeLieAlgebra.of R none
def Y (a : α) : G R α := FreeLieAlgebra.of R (some a)
def E (n : ℕ) (a : α) : F R α := FreeLieAlgebra.of R (n,a)
def shift : LieDerivation R (F R α) (F R α) :=
  FreeDerivations.extend (fun (i,a) => E (i+1) a)
/--
@isnad1 id=eq.0h4v.s7.08788fe2cb4b from=translated src=- shape=ffa6bf2d vocab=938cbfe4
-/
@[simp] theorem shift_E (n : ℕ) (a : α) : shift (E n a : F R α) = E (n+1) a := by
  simp [shift,E]
def action : R →ₗ⁅R⁆ LieDerivation R (F R α) (F R α) where
  toFun r := r • shift
  map_add' r s := add_smul r s shift
  map_smul' r s := mul_smul r s shift
  map_lie' {r s} := by simp [Ring.lie_def,mul_comm,smul_lie,lie_smul]
abbrev M (R α : Type*) [CommRing R] := SemiDirectSum (F R α) R action

def expand : G R α →ₗ⁅R⁆ M R α :=
  FreeLieAlgebra.lift R (fun a => match a with
    | none => SemiDirectSum.inr action 1
    | some a => SemiDirectSum.inl action (E 0 a))
/--
@isnad1 id=eq.0h2v.s9.c5e31ff522ef from=translated src=- shape=ecb4713b vocab=45cd61de
-/
@[simp] theorem expand_X : expand (X : G R α) = SemiDirectSum.inr action 1 := by
  simp [expand,X]
/--
@isnad1 id=eq.0h3v.s9.c088ca849f08 from=translated src=- shape=3bf764b3 vocab=e5894bf6
-/
@[simp] theorem expand_Y (a : α) : expand (Y a : G R α) = SemiDirectSum.inl action (E 0 a) := by
  simp [expand,Y]

def adWord (n : ℕ) (a : α) : G R α :=
  (LieAlgebra.ad R (G R α) X)^[n] (Y a)
/--
@isnad1 id=eq.0h3v.s4.34586271c7a6 from=translated src=- shape=6f8305ae vocab=78c96e00
-/
@[simp] theorem adWord_zero (a : α) : adWord 0 a = (Y a : G R α) := rfl
/--
@isnad1 id=eq.0h4v.s6.62ed5866b82d from=translated src=- shape=f492db91 vocab=10d350dd
-/
@[simp] theorem adWord_succ (n : ℕ) (a : α) :
    (adWord (n+1) a : G R α) = ⁅(X : G R α),adWord n a⁆ := by
  exact Function.iterate_succ_apply' _ n _
def collapseFiber : F R α →ₗ⁅R⁆ G R α := FreeLieAlgebra.lift R (fun (n,a) => adWord n a)
/--
@isnad1 id=eq.0h4v.s6.9eccb084b00f from=translated src=- shape=ea027a32 vocab=5a2dd6bc
-/
@[simp] theorem collapseFiber_E (n : ℕ) (a : α) :
    collapseFiber (E n a : F R α) = adWord n a := by simp [collapseFiber,E]

/--
@isnad1 id=eq.0h3v.s8.0311d30b1b91 from=translated src=- shape=69781037 vocab=1a79249a
-/
theorem collapse_shift (p : F R α) : collapseFiber (shift p) = ⁅(X : G R α),collapseFiber p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => cases a; simp [shift,collapseFiber,E,adWord_succ]
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [add_comm] using (leibniz_lie (X : G R α) (collapseFiber p) (collapseFiber q)).symm

def scalarX : R →ₗ⁅R⁆ G R α where
  toFun r := r • X
  map_add' r s := add_smul r s X
  map_smul' r s := mul_smul r s X
  map_lie' {r s} := by simp [Ring.lie_def,mul_comm,smul_lie,lie_smul]

def collapse : M R α →ₗ⁅R⁆ G R α :=
  InnerSemiDirect.lift action collapseFiber scalarX (by
    intro r p
    change collapseFiber (r • shift p) = ⁅r • X,collapseFiber p⁆
    rw [map_smul,collapse_shift,smul_lie])

/--
@isnad1 id=eq.0h3v.s9.691a6f49614e from=translated src=- shape=a4020029 vocab=4b9f03ef
-/
@[simp] theorem collapse_inl (p : F R α) :
    collapse (SemiDirectSum.inl action p) = collapseFiber p := by simp [collapse,InnerSemiDirect.lift]
/--
@isnad1 id=eq.0h3v.s9.22109769c7f0 from=translated src=- shape=6e78261b vocab=cc0aa56c
-/
@[simp] theorem collapse_inr (r : R) :
    collapse (SemiDirectSum.inr action r : M R α) = r • X := by simp [collapse,InnerSemiDirect.lift,scalarX]

/--
@isnad1 id=eq.0h3v.s8.ff574280eadf from=translated src=- shape=ab7a2e40 vocab=97cb4c76
-/
theorem collapse_expand (p : G R α) : collapse (expand p) = p := by
  have h : collapse.comp (expand : G R α →ₗ⁅R⁆ M R α) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [expand,collapse,InnerSemiDirect.lift,scalarX,collapseFiber,E,X,Y]
  exact LieHom.congr_fun h p

/--
@isnad1 id=eq.0h4v.s9.8c94259b07f3 from=translated src=- shape=d5412e84 vocab=41bba7e3
-/
theorem expand_adWord (n : ℕ) (a : α) :
    expand (adWord n a : G R α) = SemiDirectSum.inl action (E n a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [adWord_succ,LieHom.map_lie,expand_X,ih]
    simp only [SemiDirectSum.lie_eq_mk,SemiDirectSum.inl_eq_mk,SemiDirectSum.inr_eq_mk]
    ext <;> simp [action]

/--
@isnad1 id=eq.0h3v.s9.cb905219db25 from=translated src=- shape=24220b7a vocab=b484201b
-/
theorem expand_collapseFiber (p : F R α) :
    expand (collapseFiber p) = SemiDirectSum.inl action p := by
  have h : (expand : G R α →ₗ⁅R⁆ M R α).comp collapseFiber = SemiDirectSum.inl action := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a
    simp [collapseFiber,expand_adWord,E]
  exact LieHom.congr_fun h p

/--
@isnad1 id=eq.0h3v.s8.caff3e427669 from=translated src=- shape=ab7a2e40 vocab=97cb4c76
-/
theorem expand_collapse (p : M R α) : expand (collapse p) = p := by
  change expand (collapseFiber p.left + scalarX p.right) = p
  rw [map_add,expand_collapseFiber]
  change _ + expand (p.right • X) = p
  rw [map_smul,expand_X]
  ext <;> simp

def equivalence : G R α ≃ₗ⁅R⁆ M R α :=
  { expand with
    invFun := collapse
    left_inv := collapse_expand
    right_inv := expand_collapse }

/--
@isnad1 id=injectiv.0h2v.s6.fb785c690009 from=translated src=- shape=b199047c vocab=3135764d
-/
theorem collapseFiber_injective : Function.Injective (collapseFiber : F R α → G R α) := by
  intro p q h
  apply_fun expand at h
  rw [expand_collapseFiber,expand_collapseFiber] at h
  exact congrArg SemiDirectSum.left h

end Elimination

namespace AssociativeElimination
open LieAlgebra
variable {R α β : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing
abbrev A (R α : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid α)
def atom (a : α) : A R α := MonoidAlgebra.single (FreeMonoid.of a) 1

def lift {B : Type*} [Ring B] [Algebra R B] (f : α → B) : A R α →ₐ[R] B :=
  MonoidAlgebra.lift R B (FreeMonoid α) (FreeMonoid.lift f)
/--
@isnad1 id=eq.0h5v.s7.4cc5087154b0 from=translated src=- shape=9c1d0c0a vocab=8d804e9f
-/
@[simp] theorem lift_atom {B : Type*} [Ring B] [Algebra R B] (f : α → B) (a : α) :
    lift (R := R) f (atom a) = f a := by simp [lift,atom]

/--
@isnad1 id=eq.1h5v.s8.7225ea05a373 from=translated src=- shape=57bc8602 vocab=98ca4c2e
-/
@[ext] theorem hom_ext {B : Type*} [Semiring B] [Algebra R B] {f g : A R α →ₐ[R] B}
    (h : ∀ a, f (atom a) = g (atom a)) : f=g := by
  apply (MonoidAlgebra.lift R B (FreeMonoid α)).symm.injective
  apply FreeMonoid.hom_eq
  intro a
  exact h a

def embed : FreeLieAlgebra R α →ₗ⁅R⁆ A R α := FreeLieAlgebra.lift R atom
/--
@isnad1 id=eq.0h3v.s7.126932961f64 from=translated src=- shape=ee6b5636 vocab=3c630370
-/
@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of R a) = atom a := by simp [embed]

def dualLift (f : α → A R α) : A R α →ₐ[R] DualNumber (A R α) :=
  lift (fun a => TrivSqZeroExt.inl (atom a) + TrivSqZeroExt.inr (f a))
/--
@isnad1 id=eq.0h4v.s9.a17f30fb9d10 from=translated src=- shape=6121f63d vocab=5bc4c69c
-/
@[simp] theorem dualLift_base (f : α → A R α) (p : A R α) :
    (dualLift f p).fst = p := by
  have h : (TrivSqZeroExt.fstHom R (A R α) (A R α)).comp (dualLift f) = AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp [dualLift]
  exact AlgHom.congr_fun h p

def deriv (f : α → A R α) : A R α →ₗ[R] A R α :=
  ((TrivSqZeroExt.sndHom (A R α) (A R α)).restrictScalars R).comp (dualLift f).toLinearMap
/--
@isnad1 id=eq.0h4v.s7.af86e1a43191 from=translated src=- shape=4c0b9c43 vocab=e1797a52
-/
@[simp] theorem deriv_atom (f : α → A R α) (a : α) : deriv f (atom a) = f a := by
  simp [deriv,dualLift]
/--
@isnad1 id=eq.0h3v.s8.c06381fdc54c from=translated src=- shape=f5396686 vocab=4c0d3c86
-/
@[simp] theorem deriv_one (f : α → A R α) : deriv f 1 = 0 := by simp [deriv]
/--
@isnad1 id=eq.0h5v.s9.86a77546cfd6 from=translated src=- shape=d3c1f010 vocab=a1437718
-/
theorem deriv_mul (f : α → A R α) (p q : A R α) :
    deriv f (p*q) = deriv f p*q + p*deriv f q := by
  change (dualLift f (p*q)).snd = _
  rw [map_mul,DualNumber.snd_mul,dualLift_base,dualLift_base]
  exact add_comm _ _
/--
@isnad1 id=eq.0h5v.s9.2aff23128ccb from=translated src=- shape=04690b48 vocab=b09824ce
-/
theorem deriv_lie (f : α → A R α) (p q : A R α) :
    deriv f ⁅p,q⁆ = ⁅deriv f p,q⁆ + ⁅p,deriv f q⁆ := by
  simp only [Ring.lie_def,map_sub,deriv_mul]
  abel

def shift : A R (ℕ×α) →ₗ[R] A R (ℕ×α) := deriv (fun (i,a) => atom (i+1,a))
/--
@isnad1 id=eq.0h4v.s8.44c66101a5a6 from=translated src=- shape=a4a7409b vocab=1682d9a6
-/
@[simp] theorem shift_atom (i : ℕ) (a : α) : shift (atom (i,a) : A R (ℕ×α)) = atom (i+1,a) := by
  simp [shift]
/--
@isnad1 id=eq.0h2v.s8.6328448bd02f from=translated src=- shape=f1f0d892 vocab=08bbe5f9
-/
@[simp] theorem shift_one : shift (1 : A R (ℕ×α)) = 0 := deriv_one _
/--
@isnad1 id=eq.0h4v.s9.7f7af837bc96 from=translated src=- shape=a99d41d9 vocab=6a030353
-/
theorem shift_mul (p q : A R (ℕ×α)) : shift (p*q) = shift p*q + p*shift q := deriv_mul _ _ _

/--
@isnad1 id=eq.0h3v.s9.e57c12a71fae from=translated src=- shape=fd8e21b3 vocab=cd8866e7
-/
theorem embed_shift (p : Elimination.F R α) : embed (Elimination.shift p) = shift (embed p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => cases a; simp [Elimination.shift,Elimination.E]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [shift,add_comm] using (deriv_lie (fun (i,a) => (atom (i+1,a) : A R (ℕ×α))) (embed p) (embed q)).symm

def leftMul : A R α →ₐ[R] Module.End R (A R α) := Algebra.lsmul R R (A R α)
/--
@isnad1 id=eq.0h4v.s9.50e82652af93 from=translated src=- shape=15740251 vocab=3785533f
-/
@[simp] theorem leftMul_apply (p q : A R α) : leftMul p q = p*q := rfl
/--
@isnad1 id=eq.0h3v.s11.31526b81a722 from=translated src=- shape=4500ba7e vocab=5dc55c17
-/
@[simp] theorem comm_shift_left (p : A R (ℕ×α)) :
    ⁅(shift : Module.End R (A R (ℕ×α))),leftMul p⁆ = leftMul (shift p) := by
  apply LinearMap.ext
  intro q
  change shift (p*q)-p*shift q = shift p*q
  rw [shift_mul,add_sub_cancel_right]

def scalarShift : R →ₗ⁅R⁆ Module.End R (A R (ℕ×α)) where
  toFun r := r • shift
  map_add' r s := add_smul r s shift
  map_smul' r s := mul_smul r s shift
  map_lie' {r s} := by simp [Ring.lie_def,smul_smul,mul_comm]

def representation : Elimination.M R α →ₗ⁅R⁆ Module.End R (A R (ℕ×α)) :=
  InnerSemiDirect.lift Elimination.action (leftMul.toLieHom.comp embed) scalarShift (by
    intro r p
    change leftMul (embed (r • Elimination.shift p)) = ⁅r • (shift : Module.End R (A R (ℕ×α))),leftMul (embed p)⁆
    rw [map_smul,map_smul,embed_shift]
    apply LinearMap.ext
    intro q
    change r • (shift (embed p)*q) = r • shift (embed p*q) - embed p*(r • shift q)
    rw [shift_mul,smul_add,mul_smul_comm,add_sub_cancel_right])

def operator : A R (Option α) →ₐ[R] Module.End R (A R (ℕ×α)) :=
  lift (fun | none => shift | some a => leftMul (atom (0,a)))

/--
@isnad1 id=eq.0h3v.s11.419148da828b from=translated src=- shape=0fe38a44 vocab=6f69687a
-/
@[simp] theorem representation_inl (p : Elimination.F R α) :
    representation (SemiDirectSum.inl Elimination.action p) = leftMul (embed p) := by simp [representation,InnerSemiDirect.lift]
/--
@isnad1 id=eq.0h3v.s10.fece57b7fa2d from=translated src=- shape=33050325 vocab=70dee28c
-/
@[simp] theorem representation_inr (r : R) :
    representation (SemiDirectSum.inr Elimination.action r : Elimination.M R α) = r • shift := by
  simp [representation,InnerSemiDirect.lift,scalarShift]

/--
@isnad1 id=eq.0h3v.s10.a270bc14e2bf from=translated src=- shape=a928461d vocab=09a92936
-/
theorem operator_embed (p : Elimination.G R α) :
    operator (embed p) = representation (Elimination.expand p) := by
  have h : operator.toLieHom.comp embed = representation.comp (Elimination.expand : Elimination.G R α →ₗ⁅R⁆ Elimination.M R α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [operator,Elimination.expand,Elimination.E,representation,InnerSemiDirect.lift,scalarShift]
  exact LieHom.congr_fun h p

def extract : A R (Option α) →ₗ[R] A R (ℕ×α) :=
  (LinearMap.applyₗ 1).comp operator.toLinearMap

/--
@isnad1 id=eq.0h3v.s9.8255ddf98c1d from=translated src=- shape=a63a4c29 vocab=019c521a
-/
theorem extract_embed (p : Elimination.G R α) :
    extract (embed p) = embed (Elimination.expand p).left := by
  change operator (embed p) 1 = _
  rw [operator_embed]
  change (leftMul (embed (Elimination.expand p).left) + (Elimination.expand p).right • (shift : Module.End R (A R (ℕ×α)))) 1 = _
  simp

end AssociativeElimination

namespace IntegralWords
open Classical
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {α β : Type*}
abbrev AQ (α : Type*) := A ℚ α

def word (w : List α) : AQ α := MonoidAlgebra.single (FreeMonoid.ofList w) 1
/--
@isnad1 id=eq.0h1v.s5.826daef1cfc0 from=translated src=- shape=f9dcc584 vocab=75ab2245
-/
@[simp] theorem word_nil : word ([] : List α) = 1 := rfl
/--
@isnad1 id=eq.0h2v.s4.5006320e1b5e from=translated src=- shape=5376824f vocab=8da225b0
-/
@[simp] theorem word_singleton (a : α) : word [a] = atom a := rfl
/--
@isnad1 id=eq.0h3v.s6.187ebc3c4ef4 from=translated src=- shape=4d45420e vocab=fd6f2bc8
-/
theorem word_append (u v : List α) : word (u++v) = word u * word v := by
  simp [word,MonoidAlgebra.single_mul_single,FreeMonoid.ofList_append]
/--
@isnad1 id=eq.0h3v.s6.52be47fb5c83 from=translated src=- shape=78f5e24c vocab=97ff4824
-/
theorem word_cons (a : α) (w : List α) : word (a::w) = atom a * word w := by
  exact word_append [a] w

def lattice : Submodule ℤ (AQ α) := Submodule.span ℤ (Set.range word)
def lieLattice : LieSubalgebra ℤ (AQ α) := LieSubalgebra.lieSpan ℤ (AQ α) (Set.range atom)
def rationalLie : LieSubalgebra ℚ (AQ α) := LieSubalgebra.lieSpan ℚ (AQ α) (Set.range atom)

/--
@isnad1 id=mem.0h2v.s6.1ffec2fc635b from=translated src=- shape=32b939aa vocab=26c0f0ea
-/
theorem word_integral (w : List α) : word w ∈ lattice := Submodule.subset_span ⟨w,rfl⟩
/--
@isnad1 id=mem.0h2v.s6.53711760d2a8 from=translated src=- shape=fb07ffb3 vocab=0c2ba192
-/
theorem atom_integral (a : α) : (atom a : AQ α) ∈ lattice := word_integral [a]
/--
@isnad1 id=mem.0h1v.s6.07f2ae6b8376 from=translated src=- shape=6e482b44 vocab=98165a1d
-/
theorem one_integral : (1 : AQ α) ∈ lattice := word_integral []

/--
@isnad1 id=mem.2h3v.s8.803474992f0b from=translated src=- shape=12c5be86 vocab=4849f270
-/
theorem integral_mul {p q : AQ α} (hp : p ∈ lattice) (hq : q ∈ lattice) : p*q ∈ lattice := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨u,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨v,rfl⟩
      rw [← word_append]
      exact word_integral _
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (lattice.add_mem hp hq)
    | smul r p _ hp => simpa only [mul_smul_comm] using lattice.smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [smul_mul_assoc] using lattice.smul_mem r hp

/--
@isnad1 id=mem.2h3v.s8.8128a6595b89 from=translated src=- shape=9e3450bd vocab=e61a8633
-/
theorem integral_lie {p q : AQ α} (hp : p ∈ lattice) (hq : q ∈ lattice) : ⁅p,q⁆ ∈ lattice :=
  lattice.sub_mem (integral_mul hp hq) (integral_mul hq hp)

/--
@isnad1 id=ex.1h3v.s7.18006d64956d from=translated src=- shape=b08ad4f9 vocab=4c8f3229
-/
theorem integral_coeff {p : AQ α} (hp : p ∈ lattice) (w : FreeMonoid α) :
    ∃ z : ℤ, p.coeff w = (z : ℚ) := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨u,rfl⟩
    by_cases h : FreeMonoid.ofList u = w
    · exact ⟨1,by simp [word,h]⟩
    · exact ⟨0,by simp [word,h]⟩
  | zero => exact ⟨0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    exact ⟨a+b,by simp [ha,hb]⟩
  | smul r p _ hp =>
    obtain ⟨a,ha⟩ := hp
    refine ⟨r*a,?_⟩
    calc
      (r • p).coeff w = r • p.coeff w := MonoidAlgebra.coeff_smul_apply _ _ _
      _ = ((r*a : ℤ) : ℚ) := by rw [ha]; simp [zsmul_eq_mul]

/--
@isnad1 id=mem.1h2v.s7.493ad7da63e0 from=translated src=- shape=95f36e51 vocab=4c8f3229
-/
theorem integral_of_coeff {p : AQ α} (hp : ∀ w, ∃ z : ℤ, p.coeff w = (z : ℚ)) : p ∈ lattice := by
  classical
  rw [← MonoidAlgebra.sum_coeff_single p]
  apply Submodule.sum_mem
  intro w hw
  obtain ⟨z,hz⟩ := hp w
  rw [hz]
  convert lattice.smul_mem z (word_integral w.toList) using 1
  simp [word]

def words (P : List α → Prop) : Submodule ℚ (AQ α) :=
  Submodule.span ℚ {p | ∃ w, P w ∧ p=word w}

/--
@isnad1 id=mem.0h4v.s6.53da53a5cc17 from=translated src=- shape=96e26b88 vocab=e4127a11
-/
theorem word_mem {P : List α → Prop} {w : List α} (hw : P w) : word w ∈ words P :=
  Submodule.subset_span ⟨w,hw,rfl⟩

/--
@isnad1 id=iff.0h3v.s7.bdabb1fbd0ef from=translated src=- shape=fe7ae132 vocab=9e20888a
-/
theorem mem_words {P : List α → Prop} {p : AQ α} :
    p ∈ words P ↔ ∀ w, p.coeff w ≠ 0 → P w.toList := by
  classical
  constructor
  · intro hp w hw
    induction hp using Submodule.span_induction with
    | mem p hp =>
      rcases hp with ⟨u,hu,rfl⟩
      have h : FreeMonoid.ofList u = w := by
        by_contra h
        exact hw (by simp [word,h])
      simpa [← h] using hu
    | zero => exact (hw (by simp)).elim
    | add p q _ _ hp hq =>
      by_cases h : p.coeff w = 0
      · exact hq (by simpa [h] using hw)
      · exact hp h
    | smul r p _ hp =>
      exact hp (by intro h; apply hw; simp [h])
  · intro hp
    rw [← MonoidAlgebra.sum_coeff_single p]
    apply Submodule.sum_mem
    intro w hw
    have h : P w.toList := hp w (Finsupp.mem_support_iff.mp hw)
    convert (words P).smul_mem (p.coeff w) (word_mem h) using 1
    simp [word]

/--
@isnad1 id=le.0h4v.s7.5d013683f591 from=translated src=- shape=462cf971 vocab=05e4e4c9
-/
theorem words_mono {P Q : List α → Prop} (h : ∀ w, P w → Q w) : words P ≤ words Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,hw,rfl⟩
  exact word_mem (h w hw)

/--
@isnad1 id=mem.2h7v.s8.5696d3096f29 from=translated src=- shape=f375ba00 vocab=522c2801
-/
theorem mul_words {P Q T : List α → Prop} {p q : AQ α}
    (h : ∀ u v, P u → Q v → T (u++v)) (hp : p ∈ words P) (hq : q ∈ words Q) : p*q ∈ words T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨u,hu,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨v,hv,rfl⟩
      rw [← word_append]
      exact word_mem (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (words T).add_mem hp hq
    | smul r p _ hp => simpa only [mul_smul_comm] using (words T).smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using (words T).add_mem hp hq
  | smul r p _ hp => simpa only [smul_mul_assoc] using (words T).smul_mem r hp

/--
@isnad1 id=ex.1h2v.s8.8470287348f0 from=translated src=- shape=e5706ffb vocab=fef2e657
-/
theorem lie_has_preimage {p : AQ α} (hp : p ∈ rationalLie) : ∃ q : FreeLieAlgebra ℚ α, embed q = p := by
  have h : rationalLie (α := α) ≤ (embed : FreeLieAlgebra ℚ α →ₗ⁅ℚ⁆ AQ α).range := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨a,rfl⟩
    exact ⟨FreeLieAlgebra.of ℚ a,embed_of a⟩
  exact h hp

/--
@isnad1 id=mem.0h2v.s8.2d7a54db53e1 from=translated src=- shape=0ac7c907 vocab=fef2e657
-/
theorem embed_mem_lie (p : FreeLieAlgebra ℚ α) : embed p ∈ rationalLie := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => rw [embed_of]; exact LieSubalgebra.subset_lieSpan ⟨a,rfl⟩
  | ha p q hp hq => simpa using rationalLie.add_mem hp hq
  | hs r p hp => simpa using rationalLie.smul_mem r hp
  | hl p q hp hq => simpa only [LieHom.map_lie] using rationalLie.lie_mem hp hq

/--
@isnad1 id=mem.1h2v.s8.d8a52f203198 from=translated src=- shape=1bc4784a vocab=9053a307
-/
theorem shift_integral {p : AQ (ℕ×α)} (hp : p ∈ lattice) : shift p ∈ lattice := by
  have hword : ∀ w : List (ℕ×α), shift (word w) ∈ lattice := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      rcases a with ⟨i,a⟩
      rw [word_cons,shift_mul,shift_atom]
      exact lattice.add_mem (integral_mul (atom_integral _) (word_integral _))
        (integral_mul (atom_integral _) ih)
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hword w
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

/--
@isnad1 id=mem.1h2v.s8.010aa0dfa0c7 from=translated src=- shape=b0f697ef vocab=97453f0e
-/
theorem extract_integral {p : AQ (Option α)} (hp : p ∈ lattice) : extract p ∈ lattice := by
  have hword : ∀ w : List (Option α), ∀ q : AQ (ℕ×α), q ∈ lattice → operator (word w) q ∈ lattice := by
    intro w
    induction w with
    | nil => intro q hq; simpa using hq
    | cons a w ih =>
      intro q hq
      rw [word_cons,map_mul,Module.End.mul_apply]
      cases a with
      | none => simpa [operator] using shift_integral (ih q hq)
      | some a => simpa [operator] using integral_mul (atom_integral (0,a)) (ih q hq)
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hword w 1 one_integral
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

/--
@isnad1 id=mem.1h2v.s9.aeb0f337f4ef from=translated src=- shape=c6da009f vocab=e4419c0d
-/
theorem extract_lie {p : AQ (Option α)} (hp : p ∈ rationalLie) : extract p ∈ rationalLie := by
  obtain ⟨q,rfl⟩ := lie_has_preimage hp
  rw [extract_embed]
  exact embed_mem_lie _

def countSome : List (Option α) → ℕ
  | [] => 0
  | none::w => countSome w
  | some _::w => countSome w + 1

/--
@isnad1 id=le.0h2v.s4.e28c6d320503 from=translated src=- shape=0c010da9 vocab=de9b8ce7
-/
theorem countSome_le (w : List (Option α)) : countSome w ≤ w.length := by
  induction w with
  | nil => simp [countSome]
  | cons a w ih => cases a <;> simp [countSome] <;> omega

/--
@isnad1 id=lt.1h2v.s4.a036dcd58e2c from=translated src=- shape=6c05218a vocab=6c836028
-/
theorem countSome_lt {w : List (Option α)} (hw : none ∈ w) : countSome w < w.length := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    cases a with
    | none => simpa [countSome] using Nat.lt_succ_of_le (countSome_le w)
    | some a =>
      have h := ih (by simpa using hw)
      simp [countSome]
      omega

/--
@isnad1 id=mem.1h3v.s8.181925041a0e from=translated src=- shape=886b54fe vocab=7aec439a
-/
theorem shift_length {p : AQ (ℕ×α)} {n : ℕ} (hp : p ∈ words (fun w => w.length=n)) :
    shift p ∈ words (fun w => w.length=n) := by
  have hword : ∀ w : List (ℕ×α), shift (word w) ∈ words (fun v => v.length=w.length) := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      rcases a with ⟨i,a⟩
      rw [word_cons,shift_mul,shift_atom]
      apply (words _).add_mem
      · exact mul_words (fun u v hu hv => by simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(i+1,a)]) rfl) (word_mem (P := fun v => v.length=w.length) (w := w) rfl)
      · exact mul_words (fun u v hu hv => by simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(i,a)]) rfl) ih
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,hw,rfl⟩ := hp; simpa [hw] using hword w
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

/--
@isnad1 id=mem.1h4v.s9.ddb190a7c5d1 from=translated src=- shape=ce661565 vocab=e01b6eb0
-/
theorem operator_length (w : List (Option α)) {q : AQ (ℕ×α)} {n : ℕ}
    (hq : q ∈ words (fun v => v.length=n)) :
    operator (word w) q ∈ words (fun v => v.length=n+countSome w) := by
  induction w with
  | nil => simpa [countSome] using hq
  | cons a w ih =>
    rw [word_cons,map_mul,Module.End.mul_apply]
    cases a with
    | none => simpa [operator,countSome] using shift_length ih
    | some a =>
      have h : atom (0,a) * operator (word w) q ∈ words (fun v => v.length=n+countSome w+1) :=
        mul_words (fun u v (hu : u.length=1) (hv : v.length=n+countSome w) => by
          simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(0,a)]) rfl) ih
      simpa [operator,countSome, Nat.add_assoc] using h

/--
@isnad1 id=mem.0h2v.s8.ebfc84c8851c from=translated src=- shape=7ed65d7c vocab=f0abbd7b
-/
theorem extract_word_length (w : List (Option α)) :
    extract (word w) ∈ words (fun v => v.length=countSome w) := by
  simpa [extract] using operator_length w (word_mem (w := []) rfl)

def rename (f : α → β) : AQ α →ₐ[ℚ] AQ β := lift (fun a => atom (f a))
/--
@isnad1 id=eq.0h4v.s7.6ea89a8de575 from=translated src=- shape=f782f945 vocab=55c2b29a
-/
@[simp] theorem rename_atom (f : α → β) (a : α) : rename f (atom a) = atom (f a) := by
  simp [rename]

/--
@isnad1 id=eq.0h4v.s7.b1f645e47262 from=translated src=- shape=6c0b97ec vocab=d52fa74e
-/
theorem rename_word (f : α → β) (w : List α) : rename f (word w) = word (w.map f) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [word_cons,ih]

/--
@isnad1 id=mem.1h4v.s8.13ad2e88e15a from=translated src=- shape=6d0ef984 vocab=cb2603ba
-/
theorem rename_integral (f : α → β) {p : AQ α} (hp : p ∈ lattice) : rename f p ∈ lattice := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; rw [rename_word]; exact word_integral _
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

/--
@isnad1 id=mem.1h4v.s9.0766b1d50de6 from=translated src=- shape=14fef8ca vocab=7c6e386d
-/
theorem rename_lie (f : α → β) {p : AQ α} (hp : p ∈ rationalLie) : rename f p ∈ rationalLie := by
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; rw [rename_atom]; exact LieSubalgebra.subset_lieSpan ⟨f a,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using rationalLie.add_mem hp hq
  | smul r p _ hp => simpa using rationalLie.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using rationalLie.lie_mem hp hq

/--
@isnad1 id=mem.1h4v.s8.f79696fd6cc6 from=translated src=- shape=6d0ef984 vocab=ed704fcc
-/
theorem rename_lieIntegral (f : α → β) {p : AQ α} (hp : p ∈ lieLattice) : rename f p ∈ lieLattice := by
  induction hp using LieSubalgebra.lieSpan_induction ℤ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; rw [rename_atom]; exact LieSubalgebra.subset_lieSpan ⟨f a,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using lieLattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lieLattice.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using lieLattice.lie_mem hp hq

noncomputable def kill (a : α) : AQ α →ₐ[ℚ] AQ α := by
  classical
  exact lift fun b => if a=b then 0 else atom b

/--
@isnad1 id=eq.0h3v.s7.c3327e147da8 from=translated src=- shape=a78827d9 vocab=a6483a0c
-/
theorem kill_atom (a b : α) : kill a (atom b) = if a=b then 0 else atom b := by
  classical
  simp [kill]

/--
@isnad1 id=eq.0h3v.s7.50b8e94a3226 from=translated src=- shape=b23bfdd4 vocab=95a4f9b0
-/
theorem kill_word (a : α) (w : List α) : kill a (word w) = if a ∈ w then 0 else word w := by
  classical
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [word_cons,map_mul,kill_atom,ih]
    by_cases h : a=b <;> by_cases h' : a ∈ w <;> simp [h,h']

/--
@isnad1 id=mem.1h3v.s8.30e7a2227aea from=translated src=- shape=f7794f9e vocab=180b9c05
-/
theorem kill_integral (a : α) {p : AQ α} (hp : p ∈ lattice) : kill a p ∈ lattice := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,rfl⟩ := hp
    rw [kill_word]
    split_ifs <;> simp [word_integral]
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

/--
@isnad1 id=mem.1h3v.s9.79f32b89a0c8 from=translated src=- shape=885fa614 vocab=d695b57d
-/
theorem kill_lie (a : α) {p : AQ α} (hp : p ∈ rationalLie) : kill a p ∈ rationalLie := by
  classical
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp =>
    obtain ⟨b,rfl⟩ := hp
    rw [kill_atom]
    split_ifs
    · exact rationalLie.zero_mem
    · exact LieSubalgebra.subset_lieSpan ⟨b,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using rationalLie.add_mem hp hq
  | smul r p _ hp => simpa using rationalLie.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using rationalLie.lie_mem hp hq

def tag (a b : α) : Option α := if a=b then none else some b

def untag (a : α) : Option α → α
  | none => a
  | some b => b

/--
@isnad1 id=eq.0h3v.s8.257bc49ecbb3 from=translated src=- shape=3133eed9 vocab=226b032f
-/
theorem rename_untag_tag (a : α) (p : AQ α) : rename (untag a) (rename (tag a) p) = p := by
  have h : (rename (untag a)).comp (rename (tag a)) = AlgHom.id ℚ (AQ α) := by
    apply hom_ext
    intro b
    simp only [AlgHom.comp_apply,rename_atom,AlgHom.id_apply]
    congr 1
    dsimp [tag]
    split_ifs with h
    · exact h
    · rfl
  exact AlgHom.congr_fun h p

/--
@isnad1 id=mem.1h4v.s9.11f629f6deed from=translated src=- shape=e0867b32 vocab=fec8701c
-/
theorem rename_extract_lower (a : α) {p : AQ α} {n : ℕ}
    (hp : p ∈ words (fun w => w.length≤n+1 ∧ a ∈ w)) :
    extract (rename (tag a) p) ∈ words (fun w => w.length≤n) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [rename_word]
    have hm : none ∈ w.map (tag a) := List.mem_map.mpr ⟨a,hw.2,by simp [tag]⟩
    have hc := countSome_lt hm
    apply words_mono (P := fun v => v.length=countSome (w.map (tag a))) ?_ (extract_word_length _)
    intro v hv
    simp only [List.length_map] at hc
    omega
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

/--
@isnad1 id=mem.1h5v.s8.7052d08e0c3f from=translated src=- shape=e7fd290b vocab=9394ca18
-/
theorem kill_bound (a : α) (S : Finset α) (n : ℕ) {p : AQ α}
    (hp : p ∈ words (fun w => w.length≤n ∧ ∀ b ∈ w, b ∈ insert a S)) :
    kill a p ∈ words (fun w => w.length≤n ∧ ∀ b ∈ w, b ∈ S) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [kill_word]
    split_ifs with h
    · exact (words _).zero_mem
    · apply word_mem
      refine ⟨hw.1,?_⟩
      intro b hb
      rcases Finset.mem_insert.mp (hw.2 b hb) with h'|h'
      · exact (h (h' ▸ hb)).elim
      · exact h'
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

/--
@isnad1 id=mem.1h4v.s8.719752046087 from=translated src=- shape=81e646b0 vocab=fc7b487d
-/
theorem remainder_bound (a : α) {p : AQ α} {n : ℕ}
    (hp : p ∈ words (fun w => w.length≤n)) :
    p-kill a p ∈ words (fun w => w.length≤n ∧ a ∈ w) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [kill_word]
    split_ifs with h
    · simpa using word_mem (P := fun v => v.length≤n ∧ a ∈ v) ⟨hw,h⟩
    · simp
  | zero => simp
  | add p q _ _ hp hq =>
    rw [map_add]
    convert (words _).add_mem hp hq using 1
    abel
  | smul r p _ hp => simpa only [map_smul,smul_sub] using (words _).smul_mem r hp

/--
@isnad1 id=mem.1h2v.s8.0b9782b2af22 from=translated src=- shape=5d7b436d vocab=10b6ae86
-/
theorem lie_positive {p : AQ α} (hp : p ∈ rationalLie) : p ∈ words (fun w => 0<w.length) := by
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; exact word_mem (w := [a]) (by simp)
  | zero => simp
  | add p q _ _ hp hq => exact (words _).add_mem hp hq
  | smul r p _ hp => exact (words _).smul_mem r hp
  | lie p q _ _ hp hq =>
    apply (words _).sub_mem
    · exact mul_words (fun u v hu hv => by simp only [List.length_append]; omega) hp hq
    · exact mul_words (fun u v hu hv => by simp only [List.length_append]; omega) hq hp

def traceX : AQ (Option α) →ₐ[ℚ] ℚ := lift (fun | none => 1 | some _ => 0)

/--
@isnad1 id=eq.0h2v.s9.7b3bfd2019db from=translated src=- shape=19bdfb9d vocab=4890c1c0
-/
theorem trace_embed (q : Elimination.G ℚ α) : traceX (embed q) = (Elimination.expand q).right := by
  have h : traceX.toLieHom.comp embed =
      (LieAlgebra.SemiDirectSum.projr Elimination.action).comp (Elimination.expand : Elimination.G ℚ α →ₗ⁅ℚ⁆ Elimination.M ℚ α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [traceX,Elimination.expand]
  exact LieHom.congr_fun h q

def collapseAssoc : AQ (ℕ×α) →ₐ[ℚ] AQ (Option α) :=
  lift (fun (i,a) => embed (Elimination.adWord i a))

/--
@isnad1 id=eq.0h2v.s9.bfdc3597c3eb from=translated src=- shape=18acd1d5 vocab=52ad9e1a
-/
theorem collapse_embed (q : Elimination.F ℚ α) :
    collapseAssoc (embed q) = embed (Elimination.collapseFiber q) := by
  have h : collapseAssoc.toLieHom.comp embed =
      (embed : Elimination.G ℚ α →ₗ⁅ℚ⁆ AQ (Option α)).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    intro a
    rcases a with ⟨i,a⟩
    simp [collapseAssoc,Elimination.collapseFiber]
  exact LieHom.congr_fun h q

/--
@isnad1 id=eq.1h2v.s9.558bf7c547a9 from=translated src=- shape=f04556f3 vocab=1180e328
-/
theorem decompose_lie {p : AQ (Option α)} (hp : p ∈ rationalLie) :
    p = collapseAssoc (extract p) + traceX p • atom none := by
  obtain ⟨q,rfl⟩ := lie_has_preimage hp
  rw [extract_embed,collapse_embed,trace_embed]
  conv_lhs => rw [← Elimination.collapse_expand q]
  change embed (Elimination.collapseFiber (Elimination.expand q).left +
    (Elimination.expand q).right • Elimination.X) = _
  simp [Elimination.X]

/--
@isnad1 id=ex.1h2v.s7.f3b8f960c571 from=translated src=- shape=e5176de0 vocab=091542d9
-/
theorem trace_integral {p : AQ (Option α)} (hp : p ∈ lattice) : ∃ z : ℤ, traceX p = (z : ℚ) := by
  have hw : ∀ w : List (Option α), ∃ z : ℤ, traceX (word w) = (z : ℚ) := by
    intro w
    induction w with
    | nil => exact ⟨1,by simp⟩
    | cons a w ih =>
      obtain ⟨z,hz⟩ := ih
      rw [word_cons,map_mul,hz]
      cases a with
      | none => exact ⟨z,by simp [traceX]⟩
      | some a => exact ⟨0,by simp [traceX]⟩
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hw w
  | zero => exact ⟨0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    exact ⟨a+b,by simp [ha,hb]⟩
  | smul r p _ hp =>
    obtain ⟨a,ha⟩ := hp
    refine ⟨r*a,?_⟩
    rw [map_zsmul,ha]
    simp [zsmul_eq_mul]

/--
@isnad1 id=mem.0h3v.s8.f70ab2df2ce1 from=translated src=- shape=76811f47 vocab=2f000f92
-/
theorem adWord_integralLie (i : ℕ) (a : α) :
    embed (Elimination.adWord i a) ∈ lieLattice := by
  induction i with
  | zero =>
    simp only [Elimination.adWord,Function.iterate_zero_apply,Elimination.Y,embed_of]
    exact LieSubalgebra.subset_lieSpan ⟨some a,rfl⟩
  | succ i ih =>
    rw [Elimination.adWord_succ,LieHom.map_lie]
    apply lieLattice.lie_mem ?_ ih
    simp only [Elimination.X,embed_of]
    exact LieSubalgebra.subset_lieSpan ⟨none,rfl⟩

/--
@isnad1 id=mem.1h2v.s9.dd80fba432a7 from=translated src=- shape=72bb2c72 vocab=0442f861
-/
theorem collapse_integralLie {p : AQ (ℕ×α)} (hp : p ∈ lieLattice) : collapseAssoc p ∈ lieLattice := by
  induction hp using LieSubalgebra.lieSpan_induction ℤ with
  | mem p hp =>
    obtain ⟨⟨i,a⟩,rfl⟩ := hp
    simpa [collapseAssoc] using adWord_integralLie i a
  | zero => simp
  | add p q _ _ hp hq => simpa using lieLattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lieLattice.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using lieLattice.lie_mem hp hq

/--
@isnad1 id=mem.2h4v.s8.dd6a3cb1b3b5 from=translated src=- shape=bc1cef3d vocab=8d0a9331
-/
theorem words_and {P Q : List α → Prop} {p : AQ α} (hp : p ∈ words P) (hq : p ∈ words Q) :
    p ∈ words (fun w => P w ∧ Q w) := by
  apply mem_words.mpr
  intro w hw
  exact ⟨mem_words.mp hp w hw,mem_words.mp hq w hw⟩

/--
@isnad1 id=ex.0h2v.s7.8eff24b44e38 from=translated src=- shape=062add41 vocab=c6198e47
-/
theorem exists_support (p : AQ α) : ∃ S : Finset α, p ∈ words (fun w => ∀ b ∈ w, b ∈ S) := by
  let S := p.coeff.support.biUnion (fun w => w.toList.toFinset)
  refine ⟨S,mem_words.mpr ?_⟩
  intro w hw b hb
  exact Finset.mem_biUnion.mpr ⟨w,Finsupp.mem_support_iff.mpr hw,by simpa using hb⟩

/--
@isnad1 id=ex.0h2v.s6.3600a4c37bde from=translated src=- shape=aa79a553 vocab=2cf55c05
-/
theorem exists_bound (p : AQ α) : ∃ n : ℕ, p ∈ words (fun w => w.length≤n) := by
  refine ⟨p.coeff.support.sup (fun w => w.toList.length),mem_words.mpr ?_⟩
  intro w hw
  exact Finset.le_sup (f := fun w => w.toList.length) (Finsupp.mem_support_iff.mpr hw)

/--
@isnad1 id=eq.2h2v.s8.a74314ba9cdb from=translated src=- shape=d83617e9 vocab=63342ca0
-/
theorem bound_zero_of_lie {p : AQ α} (hl : p ∈ rationalLie)
    (hp : p ∈ words (fun w => w.length≤0)) : p=0 := by
  ext w
  change p.coeff w = 0
  by_contra h
  have h₁ := mem_words.mp (lie_positive hl) w h
  have h₂ := mem_words.mp hp w h
  omega

/--
@isnad1 id=eq.2h2v.s8.12ac1d77e877 from=translated src=- shape=b427125b vocab=0f23c933
-/
theorem support_empty_of_lie {p : AQ α} (hl : p ∈ rationalLie)
    (hp : p ∈ words (fun w => ∀ b ∈ w, b ∈ (∅ : Finset α))) : p=0 := by
  ext w
  change p.coeff w = 0
  by_contra h
  have h₁ := mem_words.mp (lie_positive hl) w h
  have h₂ := mem_words.mp hp w h
  cases ht : w.toList with
  | nil => simp [ht] at h₁
  | cons b v =>
    have hb := h₂ b (by simp [ht])
    simp at hb

universe u

/--
@isnad1 id=mem.3h3v.s9.18069e3ca413 from=translated src=- shape=87a5c7f6 vocab=eb5da37a
-/
theorem saturation_bounded (n : ℕ) : ∀ (α : Type u) (p : AQ α),
    p ∈ rationalLie → p ∈ lattice → p ∈ words (fun w => w.length≤n) → p ∈ lieLattice := by
  induction n with
  | zero =>
    intro α p hl _ hw
    rw [bound_zero_of_lie hl hw]
    exact lieLattice.zero_mem
  | succ n ih =>
    intro α p hl hi hw
    have hs : ∀ S : Finset α, ∀ p : AQ α,
        p ∈ rationalLie → p ∈ lattice →
        p ∈ words (fun w => w.length≤n+1 ∧ ∀ b ∈ w, b ∈ S) → p ∈ lieLattice := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro p hl _ hw
        have hz : p=0 := support_empty_of_lie hl (words_mono (fun _ h => h.2) hw)
        rw [hz]
        exact lieLattice.zero_mem
      | @insert a S ha ihS =>
        intro p hl hi hw
        have hl0 := kill_lie a hl
        have hi0 := kill_integral a hi
        have hp0 := ihS (kill a p) hl0 hi0 (kill_bound a S (n+1) hw)
        have hrl : p-kill a p ∈ rationalLie := rationalLie.sub_mem hl hl0
        have hri : p-kill a p ∈ lattice := lattice.sub_mem hi hi0
        have hrw := remainder_bound a (words_mono (fun _ h => h.1) hw)
        have htl := rename_lie (tag a) hrl
        have hti := rename_integral (tag a) hri
        have he := ih (ℕ×α) (extract (rename (tag a) (p-kill a p)))
          (extract_lie htl) (extract_integral hti) (rename_extract_lower a hrw)
        have ht : rename (tag a) (p-kill a p) ∈ lieLattice := by
          rw [decompose_lie htl]
          apply lieLattice.add_mem (collapse_integralLie he)
          obtain ⟨z,hz⟩ := trace_integral hti
          rw [hz,Int.cast_smul_eq_zsmul]
          exact lieLattice.smul_mem z (LieSubalgebra.subset_lieSpan ⟨none,rfl⟩)
        have hr := rename_lieIntegral (untag a) ht
        rw [rename_untag_tag] at hr
        convert lieLattice.add_mem hr hp0 using 1
        abel
    obtain ⟨S,hS⟩ := exists_support p
    exact hs S p hl hi (words_and hw hS)

/--
@isnad1 id=mem.2h2v.s8.c0f20ca36f6b from=translated src=- shape=02b631ae vocab=10a3f685
-/
theorem saturation {p : AQ α} (hl : p ∈ rationalLie) (hi : p ∈ lattice) : p ∈ lieLattice := by
  obtain ⟨n,hn⟩ := exists_bound p
  exact saturation_bounded n α p hl hi hn

end IntegralWords

namespace UniversalEmbedding
open Classical LieAlgebra AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
abbrev FL (R α : Type*) [CommRing R] := FreeLieAlgebra R α

inductive Tree (α : Type*)
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def Tree.leaves : Tree α → List α
  | .leaf a => [a]
  | .node t u => t.leaves ++ u.leaves

def Tree.eval : Tree α → FL R α
  | .leaf a => FreeLieAlgebra.of R a
  | .node t u => ⁅t.eval,u.eval⁆

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node t u => .node (t.map f) (u.map f)

/--
@isnad1 id=eq.0h4v.s4.56e02505239e from=translated src=- shape=82b556c0 vocab=764cd698
-/
@[simp] theorem Tree.leaves_map (f : α → β) (t : Tree α) :
    (t.map f).leaves = t.leaves.map f := by
  induction t <;> simp_all [Tree.map,Tree.leaves]

/--
@isnad1 id=lt.0h2v.s4.84f8cde131fe from=translated src=- shape=ed46282e vocab=c1dc75b2
-/
theorem Tree.positive (t : Tree α) : 0<t.leaves.length := by
  induction t <;> simp_all [Tree.leaves]

def bounded (n : ℕ) (S : Finset α) : Submodule R (FL R α) :=
  Submodule.span R {p | ∃ t : Tree α, t.leaves.length≤n ∧ (∀ a ∈ t.leaves, a∈S) ∧ t.eval=p}
def small (n : ℕ) : Submodule R (FL R α) :=
  Submodule.span R {p | ∃ t : Tree α, t.leaves.length≤n ∧ t.eval=p}

/--
@isnad1 id=mem.2h5v.s7.6ad51487b1f7 from=translated src=- shape=40829e3f vocab=9d482c07
-/
theorem eval_bounded (t : Tree α) {n : ℕ} {S : Finset α}
    (hn : t.leaves.length≤n) (hS : ∀ a ∈ t.leaves, a∈S) :
    (t.eval : FL R α) ∈ bounded n S := Submodule.subset_span ⟨t,hn,hS,rfl⟩
/--
@isnad1 id=mem.1h4v.s7.d0ebe75957ed from=translated src=- shape=39dde090 vocab=e30ba1c8
-/
theorem eval_small (t : Tree α) {n : ℕ} (hn : t.leaves.length≤n) :
    (t.eval : FL R α) ∈ small n := Submodule.subset_span ⟨t,hn,rfl⟩

/--
@isnad1 id=le.2h6v.s7.74165024e2a9 from=translated src=- shape=d9dd95f1 vocab=bda5aea2
-/
theorem bounded_mono {n m : ℕ} {S T : Finset α} (hn : n ≤ m) (hS : S ⊆ T) :
    (bounded n S : Submodule R (FL R α)) ≤ bounded m T := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,hs,rfl⟩
  exact eval_bounded t (ht.trans hn) (fun a ha => hS (hs a ha))
/--
@isnad1 id=le.0h4v.s7.da1902a2f5b1 from=translated src=- shape=76a0c813 vocab=e65d3ff9
-/
theorem bounded_small (n : ℕ) (S : Finset α) :
    (bounded n S : Submodule R (FL R α)) ≤ small n := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,_,rfl⟩
  exact eval_small t ht

/--
@isnad1 id=le.1h4v.s7.0053ae0315da from=translated src=- shape=0b48218e vocab=d31e2d20
-/
theorem small_mono {n m : ℕ} (h : n ≤ m) :
    (small n : Submodule R (FL R α)) ≤ small m := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  exact eval_small t (ht.trans h)

/--
@isnad1 id=mem.2h6v.s8.9f19ecc4753f from=translated src=- shape=caf45661 vocab=9acfcbc2
-/
theorem bracket_small {n m : ℕ} {p q : FL R α} (hp : p∈small n) (hq : q∈small m) :
    ⁅p,q⁆ ∈ small (n+m) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨u,hu,rfl⟩
      exact eval_small (.node t u) (by simpa [Tree.leaves] using Nat.add_le_add ht hu)
    | zero => simp
    | add p q _ _ hp hq => simpa only [lie_add] using (small _).add_mem hp hq
    | smul r p _ hp => simpa only [lie_smul] using (small _).smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_lie] using (small _).add_mem hp hq
  | smul r p _ hp => simpa only [smul_lie] using (small _).smul_mem r hp

/--
@isnad1 id=ex.1h4v.s8.cc2adbb4c504 from=translated src=- shape=ed8d6ac4 vocab=fd129ba6
-/
theorem small_exists_support {p : FL R α} {n : ℕ} (hp : p∈small n) :
    ∃ S : Finset α, p∈bounded n S := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,rfl⟩
    exact ⟨t.leaves.toFinset,eval_bounded t ht (by simp)⟩
  | zero => exact ⟨∅,Submodule.zero_mem _⟩
  | add p q _ _ hp hq =>
    rcases hp with ⟨S,hS⟩
    rcases hq with ⟨T,hT⟩
    exact ⟨S∪T,(bounded _ _).add_mem
      (bounded_mono le_rfl Finset.subset_union_left hS)
      (bounded_mono le_rfl Finset.subset_union_right hT)⟩
  | smul r p _ hp =>
    obtain ⟨S,hS⟩ := hp
    exact ⟨S,(bounded _ _).smul_mem r hS⟩

/--
@isnad1 id=ex.0h3v.s7.e752d6fb6ea2 from=translated src=- shape=4b412828 vocab=1314a3cc
-/
theorem small_exists (p : FL R α) : ∃ n, p∈small n := by
  induction p using freeLie_induction with
  | h0 => exact ⟨0,Submodule.zero_mem _⟩
  | hg a => exact ⟨1,eval_small (.leaf a) le_rfl⟩
  | ha p q hp hq =>
    obtain ⟨n,hn⟩ := hp
    obtain ⟨m,hm⟩ := hq
    exact ⟨n+m,(small _).add_mem (small_mono (Nat.le_add_right _ _) hn)
      (small_mono (Nat.le_add_left _ _) hm)⟩
  | hs r p hp => obtain ⟨n,hn⟩ := hp; exact ⟨n,(small _).smul_mem r hn⟩
  | hl p q hp hq =>
    obtain ⟨n,hn⟩ := hp
    obtain ⟨m,hm⟩ := hq
    exact ⟨n+m,bracket_small hn hm⟩

/--
@isnad1 id=eq.1h3v.s7.183a3a41a0be from=translated src=- shape=5c6e91b7 vocab=1314a3cc
-/
theorem small_zero {p : FL R α} (hp : p∈small 0) : p=0 := by
  have h : (small 0 : Submodule R (FL R α)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro p ⟨t,ht,_⟩
    have := t.positive
    omega
  exact h hp

/--
@isnad1 id=eq.1h4v.s7.8c9fb5dd3b43 from=translated src=- shape=fbb4b4b3 vocab=0017ffe3
-/
theorem bounded_empty {p : FL R α} {n : ℕ} (hp : p∈bounded n ∅) : p=0 := by
  have h : (bounded n ∅ : Submodule R (FL R α)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro p ⟨t,_,ht,_⟩
    obtain ⟨a,ha⟩ := List.exists_mem_of_length_pos t.positive
    exact (Finset.notMem_empty a (ht a ha)).elim
  exact h hp

def rename (f : α → β) : FL R α →ₗ⁅R⁆ FL R β :=
  FreeLieAlgebra.lift R (fun a => FreeLieAlgebra.of R (f a))
def renameAssoc (f : α → β) : A R α →ₐ[R] A R β := lift (fun a => atom (f a))
/--
@isnad1 id=eq.0h5v.s6.bdf31befba55 from=translated src=- shape=53a5b820 vocab=cb639516
-/
@[simp] theorem rename_of (f : α → β) (a : α) :
    rename f (FreeLieAlgebra.of R a) = FreeLieAlgebra.of R (f a) := by simp [rename]
/--
@isnad1 id=eq.0h5v.s6.c2979397b03b from=translated src=- shape=5204a101 vocab=b98c9efa
-/
@[simp] theorem rename_eval (f : α → β) (t : Tree α) :
    rename f (t.eval : FL R α) = (t.map f).eval := by
  induction t <;> simp_all [Tree.eval,Tree.map,LieHom.map_lie]

/--
@isnad1 id=eq.0h5v.s9.39bb3e5853d5 from=translated src=- shape=e20014c8 vocab=804fe451
-/
theorem rename_embed (f : α → β) (p : FL R α) :
    embed (rename f p) = renameAssoc f (embed p) := by
  have h : (embed : FL R β →ₗ⁅R⁆ A R β).comp (rename f) =
      (renameAssoc f).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [renameAssoc]
  exact LieHom.congr_fun h p

def kill (a : α) : FL R α →ₗ⁅R⁆ FL R α :=
  FreeLieAlgebra.lift R (fun b => if b=a then 0 else FreeLieAlgebra.of R b)
def killAssoc (a : α) : A R α →ₐ[R] A R α :=
  lift (fun b => if b=a then 0 else atom b)
/--
@isnad1 id=eq.0h4v.s7.4e91df476533 from=translated src=- shape=4aba9880 vocab=42d9e291
-/
@[simp] theorem kill_of (a b : α) : kill a (FreeLieAlgebra.of R b) =
    if b=a then 0 else FreeLieAlgebra.of R b := by simp [kill]

/--
@isnad1 id=eq.0h4v.s9.82b86453304c from=translated src=- shape=a2b48901 vocab=628810b9
-/
theorem kill_embed (a : α) (p : FL R α) : embed (kill a p) = killAssoc a (embed p) := by
  have h : (embed : FL R α →ₗ⁅R⁆ A R α).comp (kill a) = (killAssoc a).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro b
    simp only [LieHom.comp_apply,kill_of,embed_of,killAssoc,lift_atom,AlgHom.toLieHom_apply]
    split_ifs <;> simp
  exact LieHom.congr_fun h p

/--
@isnad1 id=eq.0h4v.s7.433a62060e04 from=translated src=- shape=0e434767 vocab=38b441b7
-/
theorem kill_eval (a : α) (t : Tree α) :
    kill a (t.eval : FL R α) = if a∈t.leaves then 0 else t.eval := by
  induction t with
  | leaf b => simp [Tree.eval,Tree.leaves,eq_comm]
  | node t u ht hu =>
    simp only [Tree.eval,LieHom.map_lie,ht,hu,Tree.leaves,List.mem_append]
    split_ifs <;> simp_all

/--
@isnad1 id=mem.1h6v.s8.995c276556f4 from=translated src=- shape=b8e0d8fe vocab=fa1bb3ef
-/
theorem kill_bounded (a : α) (S : Finset α) {n : ℕ} {p : FL R α}
    (hp : p∈bounded n (insert a S)) : kill a p∈bounded n S := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨t,ht,hs,rfl⟩
    rw [kill_eval]
    split_ifs with ha
    · exact (bounded _ _).zero_mem
    · exact eval_bounded t ht (fun b hb => (Finset.mem_insert.mp (hs b hb)).resolve_left
        (fun h => ha (h ▸ hb)))
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (bounded _ _).add_mem hp hq
  | smul r p _ hp => simpa only [map_smul] using (bounded _ _).smul_mem r hp

def fiber : Elimination.G R α →ₗ[R] Elimination.F R α :=
  { toFun := fun p => (Elimination.expand p).left
    map_add' := by intro p q; simp
    map_smul' := by intro r p; simp }

/--
@isnad1 id=eq.0h2v.s7.06f3ed5516b2 from=translated src=- shape=4b7678d5 vocab=a53306a3
-/
@[simp] theorem fiber_X : fiber (Elimination.X : Elimination.G R α) = 0 := by
  simp [fiber]
/--
@isnad1 id=eq.0h3v.s7.0e01b9e6d5a1 from=translated src=- shape=ff1466de vocab=2190c6e6
-/
@[simp] theorem fiber_Y (a : α) : fiber (Elimination.Y a : Elimination.G R α) = Elimination.E 0 a := by
  simp [fiber]
/--
@isnad1 id=eq.0h4v.s11.86576a4648c2 from=translated src=- shape=fb8e482b vocab=15e4d281
-/
theorem fiber_lie (p q : Elimination.G R α) :
    fiber ⁅p,q⁆ = ⁅fiber p,fiber q⁆ + (Elimination.expand p).right • Elimination.shift (fiber q) -
      (Elimination.expand q).right • Elimination.shift (fiber p) := by
  simp [fiber,LieHom.map_lie,Elimination.action]

/--
@isnad1 id=mem.1h4v.s8.a9972aafc2d1 from=translated src=- shape=5c4d44f1 vocab=e689c5f9
-/
theorem shift_small {p : Elimination.F R α} {n : ℕ} (hp : p∈small n) :
    Elimination.shift p∈small n := by
  have ht : ∀ t : Tree (ℕ×α), Elimination.shift (t.eval : Elimination.F R α)∈small t.leaves.length := by
    intro t
    induction t with
    | leaf a =>
      rcases a with ⟨i,a⟩
      simpa [Tree.eval,Tree.leaves,Elimination.shift,Elimination.E] using
        eval_small (R := R) (.leaf (i+1,a)) le_rfl
    | node t u ht hu =>
      simp only [Tree.eval,Tree.leaves,List.length_append,LieDerivation.apply_lie_eq_add]
      exact (small _).add_mem (bracket_small (eval_small t le_rfl) hu)
        (bracket_small ht (eval_small u le_rfl))
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,hn,rfl⟩ := hp; exact small_mono hn (ht t)
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (small _).add_mem hp hq
  | smul r p _ hp => simpa only [map_smul] using (small _).smul_mem r hp

/--
@isnad1 id=eq.0h3v.s5.577054e52d7b from=translated src=- shape=3337fb9e vocab=898be2ec
-/
theorem countSome_append (u v : List (Option α)) :
    IntegralWords.countSome (u++v) = IntegralWords.countSome u+IntegralWords.countSome v := by
  induction u with
  | nil => simp [IntegralWords.countSome]
  | cons a u ih =>
    cases a <;> simp only [List.cons_append,IntegralWords.countSome,ih]
    omega

/--
@isnad1 id=mem.0h3v.s8.95fe6af01f0a from=translated src=- shape=812ec14c vocab=ee46f1c0
-/
theorem fiber_eval (t : Tree (Option α)) :
    fiber (t.eval : Elimination.G R α)∈small (IntegralWords.countSome t.leaves) := by
  induction t with
  | leaf a =>
    cases a with
    | none =>
      change fiber (Elimination.X : Elimination.G R α)∈small 0
      simp
    | some a =>
      change fiber (Elimination.Y a : Elimination.G R α)∈small 1
      rw [fiber_Y]
      exact eval_small (.leaf (0,a)) le_rfl
  | node t u ht hu =>
    rw [Tree.eval,fiber_lie,Tree.leaves,countSome_append]
    exact (small _).sub_mem
      ((small _).add_mem (bracket_small ht hu)
        ((small _).smul_mem _ (small_mono (Nat.le_add_left _ _) (shift_small hu))))
      ((small _).smul_mem _ (small_mono (Nat.le_add_right _ _) (shift_small ht)))

/--
@isnad1 id=mem.1h5v.s9.3b2d795a6a15 from=translated src=- shape=4c56cf78 vocab=b157324f
-/
theorem fiber_remainder (a : α) {p : FL R α} {n : ℕ} (hp : p∈small (n+1)) :
    fiber (rename (IntegralWords.tag a) (p-kill a p))∈small n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    rw [kill_eval]
    split_ifs with ha
    · rw [sub_zero,rename_eval]
      apply small_mono _ (fiber_eval (R := R) (t.map (IntegralWords.tag a)))
      have hnone : none∈(t.map (IntegralWords.tag a)).leaves := by
        rw [Tree.leaves_map]
        exact List.mem_map.mpr ⟨a,ha,by simp [IntegralWords.tag]⟩
      have hlt := IntegralWords.countSome_lt hnone
      simp only [Tree.leaves_map,List.length_map] at hlt ⊢
      omega
    · simp
  | zero => simp
  | add p q _ _ hp hq =>
    have h : p+q-kill a (p+q) = (p-kill a p)+(q-kill a q) := by rw [map_add]; abel
    rw [h,map_add,map_add]
    exact (small _).add_mem hp hq
  | smul r p _ hp =>
    simpa only [map_smul,← smul_sub] using (small _).smul_mem r hp

def traceAssoc : A R (Option α) →ₐ[R] R := lift (fun | none => 1 | some _ => 0)
/--
@isnad1 id=eq.0h3v.s9.827ccd8121f0 from=translated src=- shape=616de3c9 vocab=8ef35f7b
-/
theorem trace_embed (p : Elimination.G R α) :
    traceAssoc (embed p) = (Elimination.expand p).right := by
  have h : (traceAssoc : A R (Option α) →ₐ[R] R).toLieHom.comp embed =
      (SemiDirectSum.projr Elimination.action).comp Elimination.expand := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [traceAssoc,Elimination.expand]
  exact LieHom.congr_fun h p

/--
@isnad1 id=eq.0h4v.s7.88248144c49f from=translated src=- shape=cb29a83e vocab=b7f8a843
-/
theorem untag_tag (a : α) (p : FL R α) :
    rename (IntegralWords.untag a) (rename (IntegralWords.tag a) p) = p := by
  have h : (rename (IntegralWords.untag a) : FL R (Option α) →ₗ⁅R⁆ FL R α).comp
      (rename (IntegralWords.tag a)) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro b
    simp [IntegralWords.tag,IntegralWords.untag]
    split_ifs <;> simp_all
  exact LieHom.congr_fun h p

universe u v

/--
@isnad1 id=eq.2h4v.s8.e0285c67fc63 from=translated src=- shape=2d68284a vocab=cec84b11
-/
theorem kernel_bounded (R : Type v) [CommRing R] (n : ℕ) :
    ∀ (α : Type u) (p : FL R α), p∈small n → embed p=0 → p=0 := by
  induction n with
  | zero => intro α p hp _; exact small_zero hp
  | succ n ih =>
    intro α p hp hzero
    have hs : ∀ S : Finset α, ∀ p : FL R α, p∈bounded (n+1) S → embed p=0 → p=0 := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro p hp _; exact bounded_empty hp
      | @insert a S ha ihS =>
        intro p hp hz
        have hk : kill a p=0 := ihS (kill a p) (kill_bounded a S hp) (by rw [kill_embed,hz,map_zero])
        have ht : embed (rename (IntegralWords.tag a) p)=0 := by rw [rename_embed,hz,map_zero]
        have hf : fiber (rename (IntegralWords.tag a) p)=0 := by
          apply ih (ℕ×α) _
          · simpa only [hk,sub_zero] using fiber_remainder a (bounded_small _ _ hp)
          · change embed (Elimination.expand (rename (IntegralWords.tag a) p)).left=0
            rw [← extract_embed,ht,map_zero]
        have hr : (Elimination.expand (rename (IntegralWords.tag a) p)).right=0 := by
          rw [← trace_embed,ht,map_zero]
        have he : Elimination.expand (rename (IntegralWords.tag a) p)=0 := by
          apply SemiDirectSum.ext
          · exact hf
          · exact hr
        have hz' : rename (IntegralWords.tag a) p=0 := by
          rw [← Elimination.collapse_expand (rename (IntegralWords.tag a) p),he,map_zero]
        rw [← untag_tag a p,hz',map_zero]
    obtain ⟨S,hS⟩ := small_exists_support hp
    exact hs S p hS hzero

/--
@isnad1 id=injectiv.0h2v.s7.386bc0df6ca2 from=translated src=- shape=b199047c vocab=564f85ec
-/
theorem injective : Function.Injective (embed : FL R α →ₗ⁅R⁆ A R α) := by
  intro p q h
  obtain ⟨n,hn⟩ := small_exists (p-q)
  have h0 : embed (p-q)=0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp (kernel_bounded R n α (p-q) hn h0)

end UniversalEmbedding

namespace QuadraticAlphabet
open AssociativeElimination LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
inductive Letter | a | c | b deriving DecidableEq
instance (α : Type*) : CharP (A F α) 2 :=
  charP_of_injective_ringHom (algebraMap F (A F α)).injective 2
abbrev S := A F Letter
abbrev T := A F (Option Unit)
def a : S := atom Letter.a
def c : S := atom Letter.c
def b : S := atom Letter.b
def x : T := atom none
def y : T := atom (some ())

def delta : S →ₗ[F] S := deriv (fun | .a => 0 | .c => ⁅a,b⁆ | .b => c)
/--
@isnad1 id=eq.0h0v.s8.170b6d6fccae from=translated src=- shape=13d80617 vocab=b0d8f626
-/
@[simp] theorem delta_a : delta a=0 := by simp [delta,a]
/--
@isnad1 id=eq.0h0v.s8.46d0906ff2f7 from=translated src=- shape=79939243 vocab=76e0b4df
-/
@[simp] theorem delta_b : delta b=c := by simp [delta,b]
/--
@isnad1 id=eq.0h0v.s8.2d063faf4b81 from=translated src=- shape=de636c27 vocab=cbce24c7
-/
@[simp] theorem delta_c : delta c=⁅a,b⁆ := by simp [delta,c]
/--
@isnad1 id=eq.0h0v.s8.a3b64ae95dd5 from=translated src=- shape=b175b41c vocab=06e10b55
-/
@[simp] theorem delta_one : delta 1=0 := deriv_one _
/--
@isnad1 id=eq.0h2v.s10.148d15dafba4 from=translated src=- shape=cb924aab vocab=3650a878
-/
theorem delta_mul (p q : S) : delta (p*q)=delta p*q+p*delta q := deriv_mul _ _ _
/--
@isnad1 id=eq.0h2v.s10.84d9e903591d from=translated src=- shape=23d6ea67 vocab=bf5ab085
-/
theorem delta_lie (p q : S) : delta ⁅p,q⁆=⁅delta p,q⁆+⁅p,delta q⁆ := deriv_lie _ _ _

/--
@isnad1 id=var.0h9v.s8.2b4365d1f360 from=translated src=- shape=91e06f95 vocab=3a38316a
-/
theorem algebra_induction {R α : Type*} [CommRing R] {P : A R α → Prop}
    (p : A R α) (h1 : P 1) (ha : ∀ a, P (atom a))
    (hadd : ∀ p q, P p → P q → P (p+q))
    (hs : ∀ (r : R) p, P p → P (r • p))
    (hm : ∀ p q, P p → P q → P (p*q)) : P p := by
  apply MonoidAlgebra.induction_on p ?_ hadd hs
  intro w
  change P (MonoidAlgebra.single w 1)
  have hh : ∀ v : List α, P (MonoidAlgebra.single (FreeMonoid.ofList v) 1) := by
    intro v
    induction v with
    | nil => exact h1
    | cons a v ih =>
      convert hm (atom a) (MonoidAlgebra.single (FreeMonoid.ofList v) 1) (ha a) ih using 1
      simp only [atom,MonoidAlgebra.single_mul_single,one_mul,FreeMonoid.ofList_cons]
  simpa using hh w.toList

/--
@isnad1 id=eq.0h2v.s11.aac035203bb9 from=translated src=- shape=c6123e21 vocab=3650a878
-/
theorem delta_square_mul (p q : S) :
    delta (delta (p*q))=delta (delta p)*q+p*delta (delta q) := by
  rw [delta_mul,map_add,delta_mul,delta_mul]
  calc
    _ = delta (delta p)*q+p*delta (delta q)+(delta p*delta q+delta p*delta q) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

/--
@isnad1 id=eq.0h1v.s9.1f6ba4410421 from=translated src=- shape=90e4591d vocab=52bc1257
-/
theorem delta_square (p : S) : delta (delta p)=⁅a,p⁆ := by
  induction p using algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha l =>
    cases l with
    | a => change delta (delta a)=⁅a,a⁆; simp
    | c => change delta (delta c)=⁅a,c⁆; simp [delta_lie]
    | b => change delta (delta b)=⁅a,b⁆; simp
  | hadd p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [delta_square_mul,hp,hq]; simp [Ring.lie_def]; noncomm_ring

def left : S →ₐ[F] Module.End F (S×S) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]

/--
@isnad1 id=eq.0h2v.s11.f42ede0c410a from=translated src=- shape=a2deefe1 vocab=f8a7a100
-/
@[simp] theorem left_apply (p : S) (z : S×S) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S×S) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
/--
@isnad1 id=eq.0h1v.s10.0bcfd9557fbc from=translated src=- shape=c1d80b7c vocab=374acf71
-/
@[simp] theorem root_apply (z : S×S) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl

/--
@isnad1 id=eq.0h1v.s12.a61b085180d9 from=translated src=- shape=a355c0c7 vocab=5d7d1c05
-/
theorem root_comm (p : S) : ⁅root,left p⁆=left (delta p) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp [Ring.lie_def,delta_mul,Module.End.mul_apply,mul_add,mul_assoc]

/--
@isnad1 id=eq.0h0v.s11.3f0fa8c91ad6 from=translated src=- shape=ad3e5028 vocab=e59b6bfb
-/
theorem root_square : root*root=left a := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp only [Module.End.mul_apply,root_apply,left_apply,
    map_add,delta_mul,delta_square,delta_a,mul_zero,add_zero,Ring.lie_def,add_mul]
  · calc
      _ = a*z.1+(delta z.2*a+delta z.2*a) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
  · calc
      _ = a*z.2+(delta z.1+delta z.1) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

def substitution : S →ₐ[F] T := lift (fun | .a => x*x | .c => ⁅x,y⁆ | .b => y)
/--
@isnad1 id=eq.0h0v.s8.650e9bd22915 from=translated src=- shape=faccab05 vocab=cbb95f29
-/
@[simp] theorem substitution_a : substitution a=x*x := by simp [substitution,a]
/--
@isnad1 id=eq.0h0v.s8.90a18eee508e from=translated src=- shape=49282511 vocab=a456feeb
-/
@[simp] theorem substitution_c : substitution c=⁅x,y⁆ := by simp [substitution,c]
/--
@isnad1 id=eq.0h0v.s8.c35f5dc5a6ae from=translated src=- shape=5f004dda vocab=75b1276b
-/
@[simp] theorem substitution_b : substitution b=y := by simp [substitution,b]

def representation : T →ₐ[F] Module.End F (S×S) :=
  lift (fun | none => root | some _ => left b)
/--
@isnad1 id=eq.0h0v.s10.e57937ad84e7 from=translated src=- shape=7c185480 vocab=13cb554f
-/
@[simp] theorem representation_x : representation x=root := by simp [representation,x]
/--
@isnad1 id=eq.0h0v.s11.5add8bc82796 from=translated src=- shape=9818e495 vocab=a01a1f75
-/
@[simp] theorem representation_y : representation y=left b := by simp [representation,y]

/--
@isnad1 id=eq.0h0v.s10.3f1d25c3180e from=translated src=- shape=39287177 vocab=021bafb7
-/
theorem representation_substitution : representation.comp substitution=left := by
  apply hom_ext
  intro l
  cases l with
  | a => change representation (substitution a)=left a; simp [root_square]
  | c =>
    change representation (substitution c)=left c
    rw [substitution_c]
    change representation (x*y-y*x)=left c
    rw [map_sub,map_mul,map_mul,representation_x,representation_y]
    change ⁅root,left b⁆=left c
    rw [root_comm,delta_b]
  | b => change representation (substitution b)=left b; simp

/--
@isnad1 id=injectiv.0h0v.s10.761df1cae83e from=translated src=- shape=411e6356 vocab=687c55f8
-/
theorem left_injective : Function.Injective left := by
  intro p q h
  have hh := congrArg (fun f : Module.End F (S×S) => (f (1,0)).1) h
  simpa using hh

/--
@isnad1 id=injectiv.0h0v.s8.792be822a3cb from=translated src=- shape=91c1b9c9 vocab=4970b83e
-/
theorem substitution_injective : Function.Injective substitution := by
  intro p q h
  apply left_injective
  rw [← representation_substitution]
  exact congrArg representation h

/--
@isnad1 id=eq.0h2v.s8.0cff181c8bae from=translated src=- shape=a119687f vocab=ed5f7ddc
-/
theorem ad_square (u v : T) : ⁅u,⁅u,v⁆⁆=⁅u*u,v⁆ := by
  simp only [Ring.lie_def,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

abbrev LABC := FreeLieAlgebra F Letter
def la : LABC := FreeLieAlgebra.of F Letter.a
def lc : LABC := FreeLieAlgebra.of F Letter.c
def lb : LABC := FreeLieAlgebra.of F Letter.b
def under : LABC →ₗ⁅F⁆ T := substitution.toLieHom.comp embed
/--
@isnad1 id=eq.0h0v.s8.2341df4d60f0 from=translated src=- shape=faccab05 vocab=9a3c1696
-/
@[simp] theorem under_a : under la=x*x := by simp [under,la,substitution]
/--
@isnad1 id=eq.0h0v.s8.0bc3c49ddf77 from=translated src=- shape=49282511 vocab=97256c1e
-/
@[simp] theorem under_c : under lc=⁅x,y⁆ := by simp [under,lc,substitution]
/--
@isnad1 id=eq.0h0v.s8.f1461fcc6e67 from=translated src=- shape=5f004dda vocab=440c6d8a
-/
@[simp] theorem under_b : under lb=y := by simp [under,lb,substitution]

def lieDelta : LieDerivation F LABC LABC :=
  FreeDerivations.extend (fun | .a => 0 | .c => ⁅la,lb⁆ | .b => lc)
/--
@isnad1 id=eq.0h0v.s7.a823cb05fa81 from=translated src=- shape=44884960 vocab=7b9a1483
-/
@[simp] theorem lieDelta_a : lieDelta la=0 := by simp [lieDelta,la]
/--
@isnad1 id=eq.0h0v.s7.8abcea53f0c6 from=translated src=- shape=4a86fbb1 vocab=6c481276
-/
@[simp] theorem lieDelta_c : lieDelta lc=⁅la,lb⁆ := by simp [lieDelta,lc]
/--
@isnad1 id=eq.0h0v.s7.6a76dfb100ae from=translated src=- shape=00497b90 vocab=dfa156b4
-/
@[simp] theorem lieDelta_b : lieDelta lb=lc := by simp [lieDelta,lb]

/--
@isnad1 id=eq.0h1v.s9.27a6dbd73424 from=translated src=- shape=4313cb46 vocab=73c53d4c
-/
theorem under_delta (p : LABC) : under (lieDelta p)=⁅x,under p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg l =>
    cases l with
    | a => change under (lieDelta la)=⁅x,under la⁆; simp [Ring.lie_def,mul_assoc]
    | c => change under (lieDelta lc)=⁅x,under lc⁆; simp [LieHom.map_lie,ad_square]
    | b => change under (lieDelta lb)=⁅x,under lb⁆; simp
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [add_comm] using (leibniz_lie x (under p) (under q)).symm

def iter (i : ℕ) : LABC := lieDelta^[i] lb
/--
@isnad1 id=eq.0h0v.s3.35c565223ad7 from=translated src=- shape=d3a93718 vocab=287b0704
-/
@[simp] theorem iter_zero : iter 0=lb := rfl
/--
@isnad1 id=eq.0h1v.s7.d50e02761d46 from=translated src=- shape=6c24923c vocab=13243f94
-/
@[simp] theorem iter_succ (i : ℕ) : iter (i+1)=lieDelta (iter i) :=
  Function.iterate_succ_apply' _ _ _

/--
@isnad1 id=eq.0h1v.s9.396d526c90fc from=translated src=- shape=00eef4fb vocab=607bf037
-/
theorem under_iter (i : ℕ) : under (iter i)=embed (Elimination.adWord i () : Elimination.G F Unit) := by
  induction i with
  | zero => simp [Elimination.Y,y]
  | succ i ih =>
    rw [iter_succ,under_delta,ih,Elimination.adWord_succ,LieHom.map_lie]
    simp [Elimination.X,x]

def fiberLift : Elimination.F F Unit →ₗ⁅F⁆ LABC :=
  FreeLieAlgebra.lift F (fun (i,_) => iter i)
/--
@isnad1 id=eq.0h1v.s9.a8e160bf1132 from=translated src=- shape=cfde9fa5 vocab=cdb0b772
-/
theorem under_fiberLift (p : Elimination.F F Unit) :
    under (fiberLift p)=embed (Elimination.collapseFiber p) := by
  have h : under.comp fiberLift = (embed : Elimination.G F Unit →ₗ⁅F⁆ T).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨i,u⟩
    cases u
    simp [fiberLift,Elimination.collapseFiber,under_iter]
  exact LieHom.congr_fun h p

def polynomial (p : Elimination.G F Unit) : LABC := fiberLift (Elimination.expand p).left

/--
@isnad1 id=eq.0h1v.s10.7c72ee26dede from=translated src=- shape=9c520b6e vocab=e639a648
-/
theorem decompose (p : Elimination.G F Unit) :
    embed p=under (polynomial p)+(Elimination.expand p).right • x := by
  rw [polynomial,under_fiberLift]
  have hx : embed (Elimination.X : Elimination.G F Unit)=x := by simp [Elimination.X,x]
  rw [← hx,← map_smul,← map_add]
  conv_lhs => rw [← Elimination.collapse_expand p]
  rfl

/--
@isnad1 id=injectiv.0h0v.s8.90892d3dad42 from=translated src=- shape=91c1b9c9 vocab=8a8c409e
-/
theorem under_injective : Function.Injective under := by
  intro p q h
  exact UniversalEmbedding.injective (substitution_injective h)

/--
@isnad1 id=existsun.1h1v.s10.c88d145a3aa3 from=translated src=- shape=364cea92 vocab=7e029e77
-/
theorem represent_unique (p : Elimination.G F Unit)
    (hp : (Elimination.expand p).right=0) : ∃! q : LABC, under q=embed p := by
  refine ⟨polynomial p,?_,?_⟩
  · simpa only [hp,zero_smul,add_zero] using (decompose p).symm
  · intro q hq
    apply under_injective
    rw [hq,decompose,hp,zero_smul,add_zero]

def homogeneous (n : ℕ) : Submodule F (Elimination.G F Unit) :=
  Submodule.span F {p | ∃ t : UniversalEmbedding.Tree (Option Unit), t.leaves.length=n ∧ t.eval=p}

/--
@isnad1 id=eq.2h2v.s9.a46527b899ed from=translated src=- shape=259446e0 vocab=a165bcd3
-/
theorem homogeneous_trace_zero {p : Elimination.G F Unit} {n : ℕ}
    (hn : 1<n) (hp : p∈homogeneous n) : (Elimination.expand p).right=0 := by
  have hm : ∀ t : UniversalEmbedding.Tree (Option Unit), 1<t.leaves.length →
      (Elimination.expand (t.eval : Elimination.G F Unit)).right=0 := by
    intro t ht
    cases t with
    | leaf l => simp [UniversalEmbedding.Tree.leaves] at ht
    | node t u =>
      simp [UniversalEmbedding.Tree.eval,LieHom.map_lie,Ring.lie_def,mul_comm]
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,ht,rfl⟩ := hp; exact hm t (ht ▸ hn)
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

/--
@isnad1 id=existsun.2h2v.s9.9f440f12a5be from=translated src=- shape=a4a7c1c2 vocab=267dfc87
-/
theorem homogeneous_representation {p : Elimination.G F Unit} {n : ℕ}
    (hn : 1<n) (hp : p∈homogeneous n) : ∃! q : LABC, under q=embed p :=
  represent_unique p (homogeneous_trace_zero hn hp)

end QuadraticAlphabet

namespace AssociativeDerivations
open LieAlgebra AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
local notation "FL" => FreeLieAlgebra R α

def extend (d : LieDerivation R FL FL) : Module.End R (A R α) :=
  deriv (fun a => embed (d (FreeLieAlgebra.of R a)))
/--
@isnad1 id=eq.0h4v.s9.30241cd924ee from=translated src=- shape=55e2a319 vocab=855d070c
-/
@[simp] theorem extend_atom (d : LieDerivation R FL FL) (a : α) :
    extend d (atom a) = embed (d (FreeLieAlgebra.of R a)) := by simp [extend]
/--
@isnad1 id=eq.0h3v.s8.a9675d4f7a12 from=translated src=- shape=1ed4d141 vocab=81a29612
-/
@[simp] theorem extend_one (d : LieDerivation R FL FL) :
    extend d 1=0 := deriv_one _
/--
@isnad1 id=eq.0h5v.s9.6de0d64aa7b3 from=translated src=- shape=a81dbf6e vocab=b40f3e1c
-/
theorem extend_mul (d : LieDerivation R FL FL) (p q : A R α) :
    extend d (p*q)=extend d p*q+p*extend d q := deriv_mul _ p q

/--
@isnad1 id=eq.0h4v.s9.c8e0fa2e7f74 from=translated src=- shape=c45223e8 vocab=5146727c
-/
theorem extend_embed (d : LieDerivation R FL FL) (p : FL) :
    extend d (embed p)=embed (d p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieHom.map_lie,extend,deriv_lie] at *
    rw [hp,hq,LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,LieHom.map_lie]
    exact add_comm _ _

/--
@isnad1 id=eq.4h4v.s11.8c38e3c2c802 from=translated src=- shape=ece18a55 vocab=1ad02cd5
-/
theorem linear_ext {f g : Module.End R (A R α)}
    (h1 : f 1=g 1) (ha : ∀ a, f (atom a)=g (atom a))
    (hf : ∀ p q, f (p*q)=f p*q+p*f q)
    (hg : ∀ p q, g (p*q)=g p*q+p*g q) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => exact h1
  | ha a => exact ha a
  | hadd p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [hf,hg,hp,hq]

/--
@isnad1 id=eq.2h6v.s12.58192aefeca4 from=translated src=- shape=603a01c7 vocab=559ab4bf
-/
theorem comm_mul (f g : Module.End R (A R α))
    (hf : ∀ p q, f (p*q)=f p*q+p*f q)
    (hg : ∀ p q, g (p*q)=g p*q+p*g q) (p q : A R α) :
    ⁅f,g⁆ (p*q)=⁅f,g⁆ p*q+p*⁅f,g⁆ q := by
  change f (g (p*q))-g (f (p*q))=(f (g p)-g (f p))*q+p*(f (g q)-g (f q))
  rw [hf,hg,map_add,map_add,hf,hf,hg,hg]
  noncomm_ring

def hom : LieDerivation R FL FL →ₗ⁅R⁆ Module.End R (A R α) where
  toFun := extend
  map_add' d e := by
    apply linear_ext
    · simp
    · intro a; simp [LieDerivation.add_apply]
    · exact extend_mul _
    · intro p q; simp only [LinearMap.add_apply,extend_mul]; noncomm_ring
  map_smul' r d := by
    apply linear_ext
    · simp
    · intro a; simp
    · exact extend_mul _
    · intro p q; simp [extend_mul,smul_add]
  map_lie' {d e} := by
    apply linear_ext
    · change extend ⁅d,e⁆ 1=extend d (extend e 1)-extend e (extend d 1)
      simp
    · intro a
      change extend ⁅d,e⁆ (atom a)=extend d (extend e (atom a))-extend e (extend d (atom a))
      simp [extend_embed]
    · exact extend_mul _
    · exact comm_mul _ _ (extend_mul d) (extend_mul e)

/--
@isnad1 id=eq.0h4v.s10.6c32d0b4ea9f from=translated src=- shape=ae27c49e vocab=a5f66fa1
-/
@[simp] theorem hom_apply (d : LieDerivation R FL FL) (p : A R α) :
    hom d p=extend d p := rfl

/--
@isnad1 id=eq.0h4v.s11.404687e8b2ce from=translated src=- shape=968ccd4e vocab=c20753ac
-/
theorem comm_left (d : LieDerivation R FL FL) (p : A R α) :
    ⁅hom d,leftMul p⁆=leftMul (extend d p) := by
  apply LinearMap.ext
  intro q
  change extend d (p*q)-p*extend d q=extend d p*q
  rw [extend_mul,add_sub_cancel_right]
end AssociativeDerivations

namespace EnvelopingTools
open LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/--
@isnad1 id=var.0h8v.s8.f49eb4cfc89b from=translated src=- shape=a4c7b233 vocab=89744a27
-/
theorem induction (q : UniversalEnvelopingAlgebra R L)
    {P : UniversalEnvelopingAlgebra R L → Prop}
    (hs : ∀ r, P (algebraMap R _ r))
    (hi : ∀ l, P (UniversalEnvelopingAlgebra.ι R l))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hm : ∀ a b, P a → P b → P (a*b)) : P q := by
  let K : Subalgebra R (UniversalEnvelopingAlgebra R L) :=
    { carrier := {a | P a}
      algebraMap_mem' := hs
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      mul_mem' := fun ha' hb' => hm _ _ ha' hb' }
  let i : L →ₗ⁅R⁆ K :=
    { (UniversalEnvelopingAlgebra.ι R).toLinearMap.codRestrict K.toSubmodule hi with
      map_lie' := by intro a b; apply Subtype.ext; exact LieHom.map_lie _ a b }
  let f := UniversalEnvelopingAlgebra.lift R i
  have h : K.val.comp f=AlgHom.id R (UniversalEnvelopingAlgebra R L) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro l
    change (f (UniversalEnvelopingAlgebra.ι R l) : UniversalEnvelopingAlgebra R L)=
      UniversalEnvelopingAlgebra.ι R l
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  have hq := (f q).property
  change P ((K.val.comp f) q) at hq
  simpa only [h,AlgHom.id_apply] using hq
end EnvelopingTools

namespace FiberPBW
open AssociativeElimination LieAlgebra
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α G : Type*} [CommRing R] [LieRing G] [LieAlgebra R G]
local notation "F" => FreeLieAlgebra R α
local notation "B" => UniversalEnvelopingAlgebra R G
variable (act : G →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
abbrev M := SemiDirectSum (R:=R) F G act
local notation "V" => A R α ⊗[R] B

def onLeft (f : Module.End R (A R α)) : Module.End R V :=
  f.rTensor B

def onRight (f : Module.End R B) : Module.End R V :=
  f.lTensor (A R α)

/--
@isnad1 id=eq.0h6v.s10.42d81bd594ee from=translated src=- shape=88bc25cc vocab=a699db8f
-/
@[simp] theorem onLeft_tmul (f : Module.End R (A R α)) (p : A R α) (b : B) :
    onLeft f (p⊗ₜ b)=f p⊗ₜ b := rfl
/--
@isnad1 id=eq.0h6v.s10.9489ddadaa96 from=translated src=- shape=595166da vocab=7742a6b5
-/
@[simp] theorem onRight_tmul (f : Module.End R B) (p : A R α) (b : B) :
    onRight f (p⊗ₜ b)=p⊗ₜ f b := rfl

/--
@isnad1 id=eq.0h5v.s12.7e0079e15e14 from=translated src=- shape=91e69619 vocab=b4ea758b
-/
theorem commute_tensor (f : Module.End R (A R α)) (g : Module.End R B) :
    ⁅onLeft (G:=G) f,onRight (α:=α) g⁆=0 := by
  apply TensorProduct.ext'
  intro p b
  simp

def fiber : F →ₗ⁅R⁆ Module.End R V :=
  (Module.End.rTensorAlgHom R (A R α) B).toLieHom.comp (leftMul.toLieHom.comp embed)

def action : G →ₗ⁅R⁆ Module.End R V :=
  (Module.End.rTensorAlgHom R (A R α) B).toLieHom.comp (AssociativeDerivations.hom.comp act)

def baseLeft : B →ₐ[R] Module.End R B := Algebra.lsmul R R B

def constant : G →ₗ⁅R⁆ Module.End R V :=
  (Module.End.lTensorAlgHom R B (A R α)).toLieHom.comp
    (baseLeft.toLieHom.comp (UniversalEnvelopingAlgebra.ι R))

def base : G →ₗ⁅R⁆ Module.End R V where
  toFun g := action act g+constant g
  map_add' g h := by simp only [map_add]; abel
  map_smul' r g := by simp only [map_smul,smul_add,RingHom.id_apply]
  map_lie' {g h} := by
    have h1 : ⁅action act g,constant h⁆=0 := commute_tensor _ _
    have h2 : ⁅action act h,constant g⁆=0 := commute_tensor _ _
    change action act ⁅g,h⁆+constant ⁅g,h⁆= _
    rw [LieHom.map_lie,LieHom.map_lie]
    change (action act g*action act h-action act h*action act g)+
      (constant g*constant h-constant h*constant g)=
      (action act g+constant g)*(action act h+constant h)-
      (action act h+constant h)*(action act g+constant g)
    change action act g*constant h-constant h*action act g=0 at h1
    change action act h*constant g-constant g*action act h=0 at h2
    have h1' : action act g*constant h=constant h*action act g := by
      exact (sub_eq_zero (a:=action act g*constant h) (b:=constant h*action act g)).mp h1
    have h2' : action act h*constant g=constant g*action act h := by
      exact (sub_eq_zero (a:=action act h*constant g) (b:=constant g*action act h)).mp h2
    simp only [add_mul,mul_add]
    rw [h1',h2']
    abel

/--
@isnad1 id=eq.0h6v.s12.445cda8850c6 from=translated src=- shape=820ed00b vocab=c9f894b4
-/
@[simp] theorem fiber_tmul (p : F) (q : A R α) (b : B) :
    fiber p (q⊗ₜ b)=(embed p*q)⊗ₜ b := rfl
/--
@isnad1 id=eq.0h7v.s12.22ed9f9406c0 from=translated src=- shape=5a5e8098 vocab=bed5cee2
-/
@[simp] theorem base_tmul (g : G) (q : A R α) (b : B) :
    base act g (q⊗ₜ b)=AssociativeDerivations.extend (act g) q⊗ₜ b+
      q⊗ₜ (UniversalEnvelopingAlgebra.ι R g*b) := rfl

/--
@isnad1 id=eq.0h6v.s14.ce1d28221897 from=translated src=- shape=615c5606 vocab=e57ef42c
-/
theorem compatibility (g : G) (p : F) :
    fiber (G:=G) (act g p)=⁅base act g,fiber (G:=G) p⁆ := by
  apply TensorProduct.ext'
  intro q b
  change fiber (act g p) (q⊗ₜ b)=
    base act g (fiber p (q⊗ₜ b))-fiber p (base act g (q⊗ₜ b))
  simp only [base_tmul,fiber_tmul,map_add,AssociativeDerivations.extend_mul,
    AssociativeDerivations.extend_embed,TensorProduct.add_tmul]
  abel

def representation : M act →ₗ⁅R⁆ Module.End R V :=
  InnerSemiDirect.lift act fiber (base act) (compatibility act)

def operators : UniversalEnvelopingAlgebra R (M act) →ₐ[R] Module.End R V :=
  UniversalEnvelopingAlgebra.lift R (representation act)

def fiberIn : A R α →ₐ[R] UniversalEnvelopingAlgebra R (M act) :=
  lift (fun a => UniversalEnvelopingAlgebra.ι R (SemiDirectSum.inl act (FreeLieAlgebra.of R a)))
def baseIn : B →ₐ[R] UniversalEnvelopingAlgebra R (M act) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp (SemiDirectSum.inr act))

/--
@isnad1 id=eq.0h4v.s12.be2599c31531 from=translated src=- shape=6a76b2ba vocab=a6a64e52
-/
theorem operators_fiber : (operators act).comp (fiberIn act)=
    (Module.End.rTensorAlgHom R (A R α) B).comp leftMul := by
  apply AssociativeElimination.hom_ext (R:=R) (α:=α)
  intro a
  simp only [AlgHom.comp_apply,fiberIn,lift_atom,operators,UniversalEnvelopingAlgebra.lift_ι_apply,
    representation,InnerSemiDirect.lift_inl,fiber,LieHom.comp_apply,embed_of]
  rfl

/--
@isnad1 id=eq.0h6v.s12.766bdbd89c83 from=translated src=- shape=9b239925 vocab=1926c37c
-/
theorem operators_base_one (p : B) (b : B) :
    operators act (baseIn act p) ((1 : A R α)⊗ₜ b)=1⊗ₜ (p*b) := by
  induction p using EnvelopingTools.induction generalizing b with
  | hs r => simp [Algebra.algebraMap_eq_smul_one]
  | hi g =>
    simp only [baseIn,UniversalEnvelopingAlgebra.lift_ι_apply,LieHom.comp_apply,
      operators,representation,InnerSemiDirect.lift_inr,base_tmul,
      AssociativeDerivations.extend_one,TensorProduct.zero_tmul,zero_add]
  | ha p q hp hq => simp [hp,hq,add_mul,TensorProduct.tmul_add]
  | hm p q hp hq =>
    simp only [map_mul,Module.End.mul_apply]
    rw [hq,hp,mul_assoc]

def normal : V →ₗ[R] UniversalEnvelopingAlgebra R (M act) :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun b => fiberIn act p*baseIn act b
          map_add' := by intro b c; simp [mul_add]
          map_smul' := by intro r b; simp }
      map_add' := by intro p q; ext b; simp [add_mul]
      map_smul' := by intro r p; ext b; simp }
/--
@isnad1 id=eq.0h6v.s11.cea4638b1c39 from=translated src=- shape=9ff6f0f6 vocab=e77f7381
-/
@[simp] theorem normal_tmul (p : A R α) (b : B) :
    normal act (p⊗ₜ b)=fiberIn act p*baseIn act b := rfl

def extract : UniversalEnvelopingAlgebra R (M act) →ₗ[R] V :=
  (LinearMap.applyₗ ((1 : A R α)⊗ₜ (1 : B))).comp (operators act).toLinearMap

/--
@isnad1 id=eq.0h5v.s12.91d924491c15 from=translated src=- shape=051398ea vocab=15c8304f
-/
theorem extract_normal (z : V) : extract act (normal act z)=z := by
  have h : (extract act).comp (normal act)=LinearMap.id := by
    apply TensorProduct.ext'
    intro p b
    change operators act (fiberIn act p*baseIn act b) (1⊗ₜ (1 : B))=p⊗ₜ b
    rw [map_mul,Module.End.mul_apply,operators_base_one,mul_one]
    have hh := AlgHom.congr_fun (operators_fiber act) p
    change operators act (fiberIn act p) (1⊗ₜ b)=p⊗ₜ b
    simp only [AlgHom.comp_apply] at hh
    rw [hh]
    change (p*1)⊗ₜ b=p⊗ₜ b
    rw [mul_one]
  exact LinearMap.congr_fun h z

/--
@isnad1 id=injectiv.0h4v.s11.0ff3a5d08115 from=translated src=- shape=77443ab4 vocab=ab6f7b75
-/
theorem normal_injective : Function.Injective (normal act) :=
  Function.LeftInverse.injective (extract_normal act)

end FiberPBW

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]
abbrev Free (R α : Type*) [CommRing R] := FreeLieAlgebra R (α×α)
def gen (i j : α) : Free R α := FreeLieAlgebra.of R (i,j)
def relations : Set (Free R α) := {q |
  (∃ i, q=gen (R:=R) i i) ∨ (∃ i j, q=gen (R:=R) i j-gen (R:=R) j i) ∨
  (∃ i j k l, i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ q=⁅gen (R:=R) i j,gen (R:=R) k l⁆) ∨
  (∃ i j k, i≠j ∧ i≠k ∧ j≠k ∧ q=⁅gen (R:=R) i j,gen (R:=R) i k+gen (R:=R) j k⁆)}
def ideal : LieIdeal R (Free R α) := LieSubmodule.lieSpan R _ relations
abbrev T (R α : Type*) [CommRing R] := Free R α ⧸ (ideal (R:=R) (α:=α))
def t (i j : α) : T R α := (ideal (R:=R) (α:=α)).mkQ (gen i j)

/--
@isnad1 id=eq.1h3v.s10.b4b83bf1b87e from=translated src=- shape=9f5c089f vocab=bf7e248f
-/
theorem relation_zero {q : Free R α} (h : q∈relations) :
    (ideal (R:=R) (α:=α)).mkQ q=0 := by
  exact (LieSubmodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan h)
/--
@isnad1 id=eq.0h3v.s6.0fdae1db1563 from=translated src=- shape=ee0b2f6b vocab=9148050e
-/
@[simp] theorem t_self (i : α) : t (R:=R) i i=0 :=
  relation_zero (Or.inl ⟨i,rfl⟩)
/--
@isnad1 id=eq.0h4v.s4.5cf48c2dc2d8 from=translated src=- shape=fdfacf2f vocab=af70ddae
-/
theorem t_comm (i j : α) : t (R:=R) i j=t j i := by
  have h := relation_zero (R:=R) (Or.inr (Or.inl ⟨i,j,rfl⟩))
  simpa only [map_sub,sub_eq_zero,t] using h
/--
@isnad1 id=eq.4h6v.s7.f58fc6490e49 from=translated src=- shape=703b3298 vocab=d4763bac
-/
theorem t_disjoint (i j k l : α) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅t (R:=R) i j,t (R:=R) k l⁆=0 := by
  change (ideal (R:=R) (α:=α)).mkQ (⁅gen i j,gen k l⁆)=0
  exact relation_zero (Or.inr (Or.inr (Or.inl ⟨i,j,k,l,hik,hil,hjk,hjl,rfl⟩)))
/--
@isnad1 id=eq.3h5v.s8.3c45d1c18a35 from=translated src=- shape=b9d59067 vocab=74f4e495
-/
theorem t_three (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅t (R:=R) i j,t (R:=R) i k+t (R:=R) j k⁆=0 := by
  change (ideal (R:=R) (α:=α)).mkQ (⁅gen i j,gen i k+gen j k⁆)=0
  exact relation_zero (Or.inr (Or.inr (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)))

variable {E : Type*} [LieRing E] [LieAlgebra R E]
def lift (f : α → α → E) (hz : ∀ i, f i i=0) (hs : ∀ i j,f i j=f j i)
    (hd : ∀ i j k l,i≠k → i≠l → j≠k → j≠l → ⁅f i j,f k l⁆=0)
    (ht : ∀ i j k,i≠j → i≠k → j≠k → ⁅f i j,f i k+f j k⁆=0) : T R α →ₗ⁅R⁆ E := by
  let p := FreeLieAlgebra.lift R (fun ij : α×α => f ij.1 ij.2)
  have hker : ideal (R:=R) (α:=α) ≤ p.ker := by
    rw [ideal,LieSubmodule.lieSpan_le]
    intro q hq
    change p q=0
    rcases hq with ⟨i,rfl⟩ | ⟨i,j,rfl⟩ | ⟨i,j,k,l,hik,hil,hjk,hjl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [p,gen,FreeLieAlgebra.lift_of_apply] using hz i
    · simpa only [map_sub,p,gen,FreeLieAlgebra.lift_of_apply,sub_eq_zero] using hs i j
    · simpa only [LieHom.map_lie,p,gen,FreeLieAlgebra.lift_of_apply] using hd i j k l hik hil hjk hjl
    · simpa only [LieHom.map_lie,map_add,p,gen,FreeLieAlgebra.lift_of_apply] using ht i j k hij hik hjk
  exact { (ideal (R:=R) (α:=α)).toSubmodule.liftQ p.toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact p.map_lie a b }
/--
@isnad1 id=eq.4h6v.s8.f60885365775 from=translated src=- shape=c8157d36 vocab=5a7a61f7
-/
@[simp] theorem lift_t (f : α → α → E) (hz hs hd ht) (i j : α) :
    lift f hz hs hd ht (t (R:=R) i j)=f i j := by
  change FreeLieAlgebra.lift R (fun ij : α×α => f ij.1 ij.2) (FreeLieAlgebra.of R (i,j))=f i j
  simp only [FreeLieAlgebra.lift_of_apply]

variable [DecidableEq α]
def action : T R α →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α) :=
  lift pair pair_self pair_comm pair_disjoint pair_three
local notation "F" => FreeLieAlgebra R α
local notation "SD" => SemiDirectSum F (T R α) action
/--
@isnad1 id=eq.0h4v.s8.61e29cf33f71 from=translated src=- shape=f6cc2a93 vocab=93d80922
-/
@[simp] theorem action_t (i j : α) : action (t (R:=R) i j)=pair i j := by simp [action]
def fiber (i : α) : SD := SemiDirectSum.inl action (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr action (t i j)
def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j
/--
@isnad1 id=eq.0h2v.s9.2582a9c95550 from=translated src=- shape=82959642 vocab=0cf594e7
-/
@[simp] theorem chord_nn : chord (R:=R) (α:=α) none none=0 := rfl
/--
@isnad1 id=eq.0h3v.s6.a1e31087cbac from=translated src=- shape=4db00d4e vocab=86e439a1
-/
@[simp] theorem chord_ns (i : α) : chord (R:=R) none (some i)=fiber i := rfl
/--
@isnad1 id=eq.0h3v.s6.d58820175951 from=translated src=- shape=1dbbe6c7 vocab=86e439a1
-/
@[simp] theorem chord_sn (i : α) : chord (R:=R) (some i) none=fiber i := rfl
/--
@isnad1 id=eq.0h4v.s6.6e2ab90904a2 from=translated src=- shape=850a7bef vocab=1371805b
-/
@[simp] theorem chord_ss (i j : α) : chord (R:=R) (some i) (some j)=base i j := rfl
/--
@isnad1 id=eq.0h3v.s9.b1216e1e7d68 from=translated src=- shape=6c6d8811 vocab=516aa0c3
-/
@[simp] theorem chord_self (i : Option α) : chord (R:=R) i i=0 := by
  cases i <;> simp [base]
/--
@isnad1 id=eq.0h4v.s6.5a4ece548781 from=translated src=- shape=adfdfdd4 vocab=516aa0c3
-/
theorem chord_comm (i j : Option α) : chord (R:=R) i j=chord j i := by
  cases i <;> cases j <;> simp [base,t_comm]
/--
@isnad1 id=eq.0h5v.s10.b5138f4d49ca from=translated src=- shape=bcf6af18 vocab=3222dbbc
-/
theorem base_fiber (i j k : α) : ⁅base (R:=R) i j,fiber k⁆=
    SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  simp [base,fiber]
/--
@isnad1 id=eq.0h5v.s10.8d9603b66758 from=translated src=- shape=ad77e08b vocab=a8f11561
-/
theorem fiber_base (i j k : α) : ⁅fiber (R:=R) k,base i j⁆=
    -SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew,base_fiber]
/--
@isnad1 id=eq.4h6v.s9.ff62d59c2641 from=translated src=- shape=af25e49f vocab=f4875960
-/
theorem chord_disjoint (i j k l : Option α)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅chord (R:=R) i j,chord (R:=R) k l⁆=0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base,fiber,t_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction
/--
@isnad1 id=eq.3h5v.s10.818d544ce7df from=translated src=- shape=c02e3b6b vocab=f1bfb0cb
-/
theorem chord_three (i j k : Option α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅chord (R:=R) i j,chord (R:=R) i k+chord (R:=R) j k⁆=0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_ns,chord_ns,chord_ss,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_sn,chord_ss,chord_ns,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_ss,chord_sn,chord_sn,lie_add,base_fiber,base_fiber]
        simp only [pair_of_left,pair_of_right,← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_ss,base,← map_add,← LieHom.map_lie]
        rw [t_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)),map_zero]
def toSemidirect : T R (Option α) →ₗ⁅R⁆ SD :=
  lift chord chord_self chord_comm chord_disjoint chord_three
/--
@isnad1 id=eq.0h4v.s9.37451010ebcd from=translated src=- shape=41b3fd1a vocab=380a5c22
-/
@[simp] theorem toSemidirect_t (i j : Option α) : toSemidirect (t (R:=R) i j)=chord i j := by
  simp [toSemidirect]
end GenericBraid

namespace RestrictedAlphabet
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
inductive Letter (α : Type*) | a | c (i : α) | b (i : α)
variable {α : Type*}
abbrev S (α : Type*) := A F (Letter α)
abbrev T (α : Type*) := A F (Option α)
def a : S α := atom .a
def b (i : α) : S α := atom (.b i)
def c (i : α) : S α := atom (.c i)
def y (i : α) : T α := atom (some i)
def x : T α := atom none
def delta : Module.End F (S α) := deriv (fun (l : Letter α) => match l with | .a => 0 | .c i => ⁅(a : S α),b i⁆ | .b i => c i)
/--
@isnad1 id=eq.0h1v.s8.438467ce1a7a from=translated src=- shape=32bb7597 vocab=b5c3ccfe
-/
@[simp] theorem delta_a : delta (a : S α)=0 := by simp [delta,a]
/--
@isnad1 id=eq.0h2v.s8.0d0c47354fae from=translated src=- shape=5aa4e6d7 vocab=2e049af2
-/
@[simp] theorem delta_b (i : α) : delta (b i)=c i := by simp [delta,b]
/--
@isnad1 id=eq.0h2v.s8.a3eaa35057c8 from=translated src=- shape=87d4ddc1 vocab=98ccfcdc
-/
@[simp] theorem delta_c (i : α) : delta (c i)=⁅(a : S α),b i⁆ := by simp [delta,c]
/--
@isnad1 id=eq.0h1v.s8.e750c28b410d from=translated src=- shape=f9a04bba vocab=804ebba4
-/
@[simp] theorem delta_one : delta (1 : S α)=0 := deriv_one _
/--
@isnad1 id=eq.0h3v.s9.3382ae928a3c from=translated src=- shape=9756800d vocab=634be1b7
-/
theorem delta_mul (p q : S α) : delta (p*q)=delta p*q+p*delta q := deriv_mul _ _ _
/--
@isnad1 id=eq.0h3v.s10.77835c026991 from=translated src=- shape=6bfef5e5 vocab=1acf954b
-/
theorem delta_lie (p q : S α) : delta ⁅p,q⁆=⁅delta p,q⁆+⁅p,delta q⁆ := deriv_lie _ _ _
/--
@isnad1 id=eq.0h3v.s10.c70496b6ef47 from=translated src=- shape=9515e3e5 vocab=634be1b7
-/
theorem delta_square_mul (p q : S α) :
    delta (delta (p*q))=delta (delta p)*q+p*delta (delta q) := by
  rw [delta_mul,map_add,delta_mul,delta_mul]
  calc
    _ = delta (delta p)*q+p*delta (delta q)+(delta p*delta q+delta p*delta q) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
/--
@isnad1 id=eq.0h2v.s9.627e71922647 from=translated src=- shape=af60784a vocab=7531d861
-/
theorem delta_square (p : S α) : delta (delta p)=⁅(a : S α),p⁆ := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha l =>
    cases l with
    | a => change delta (delta a)=⁅a,a⁆; simp
    | c i => change delta (delta (c i))=⁅a,c i⁆; simp [delta_lie]
    | b i => change delta (delta (b i))=⁅(a : S α),b i⁆; simp
  | hadd p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [delta_square_mul,hp,hq]; simp [Ring.lie_def]; noncomm_ring

def left : S α →ₐ[F] Module.End F (S α×S α) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]
/--
@isnad1 id=eq.0h3v.s11.dfcd28886bbb from=translated src=- shape=18ac965a vocab=647387e2
-/
@[simp] theorem left_apply (p : S α) (z : S α×S α) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S α×S α) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
/--
@isnad1 id=eq.0h2v.s10.cc9986b01480 from=translated src=- shape=9fd27e14 vocab=955cf464
-/
@[simp] theorem root_apply (z : S α×S α) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl
/--
@isnad1 id=eq.0h2v.s12.e42387bcbc39 from=translated src=- shape=8fe374dd vocab=2081b60c
-/
theorem root_comm (p : S α) : ⁅(root : Module.End F (S α×S α)),left p⁆=left (delta p) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp [Ring.lie_def,delta_mul,Module.End.mul_apply,mul_add,mul_assoc]
/--
@isnad1 id=eq.0h1v.s11.d0e18d834be0 from=translated src=- shape=b8553d0b vocab=3b433bad
-/
theorem root_square : root*root=left (a : S α) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp only [Module.End.mul_apply,root_apply,left_apply,
    map_add,delta_mul,delta_square,delta_a,mul_zero,add_zero,Ring.lie_def,add_mul]
  · calc
      _ = a*z.1+(delta z.2*a+delta z.2*a) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
  · calc
      _ = a*z.2+(delta z.1+delta z.1) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

def substitution : S α →ₐ[F] T α := lift (fun | .a => x*x | .c i => ⁅(x : T α),y i⁆ | .b i => y i)
/--
@isnad1 id=eq.0h1v.s8.00adfc1642a8 from=translated src=- shape=8cf0b594 vocab=eb019544
-/
@[simp] theorem substitution_a : substitution (a : S α)=x*x := by simp [substitution,a]
/--
@isnad1 id=eq.0h2v.s8.2a8ba991efd2 from=translated src=- shape=92bc9367 vocab=2cf86978
-/
@[simp] theorem substitution_c (i : α) : substitution (c i)=⁅(x : T α),y i⁆ := by simp [substitution,c]
/--
@isnad1 id=eq.0h2v.s8.c0b338bfd930 from=translated src=- shape=76f1febf vocab=d7d78eed
-/
@[simp] theorem substitution_b (i : α) : substitution (b i)=y i := by simp [substitution,b]
def representation : T α →ₐ[F] Module.End F (S α×S α) :=
  lift (fun | none => root | some i => left (b i))
/--
@isnad1 id=eq.0h1v.s11.303a28cacd21 from=translated src=- shape=c2870b37 vocab=ebd02188
-/
@[simp] theorem representation_x : representation (x : T α)=root := by simp [representation,x]
/--
@isnad1 id=eq.0h2v.s11.b3e9ecf05c92 from=translated src=- shape=cf0a26a0 vocab=072ebe2e
-/
@[simp] theorem representation_y (i : α) : representation (y i)=left (b i) := by simp [representation,y]
/--
@isnad1 id=eq.0h1v.s10.2eb6a35ac269 from=translated src=- shape=beb56744 vocab=b79bbe2d
-/
theorem representation_substitution : representation.comp substitution=left (α:=α) := by
  apply hom_ext
  intro l
  cases l with
  | a => change representation (substitution a)=left a; simp [root_square]
  | c i =>
    change representation (substitution (c i))=left (c i)
    rw [substitution_c]
    change representation (x*y i-y i*x)=left (c i)
    rw [map_sub,map_mul,map_mul,representation_x,representation_y]
    exact (root_comm (b i)).trans (congrArg left (delta_b i))
  | b i => change representation (substitution (b i))=left (b i); simp

/--
@isnad1 id=injectiv.0h1v.s8.31481b3b6c1f from=translated src=- shape=c216bdf5 vocab=bef84c65
-/
theorem injective : Function.Injective (substitution (α:=α)) := by
  intro p q hpq
  have h := congrArg representation hpq
  have hh (v : S α) : representation (substitution v)=left v := AlgHom.congr_fun representation_substitution v
  rw [hh,hh] at h
  have he := congrArg (fun f : Module.End F (S α×S α) => (f (1,0)).1) h
  simpa only [left_apply,mul_one] using he
end RestrictedAlphabet

namespace GenericBraid
open LieAlgebra AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R] [DecidableEq α]
abbrev Env (R α : Type*) [CommRing R] := UniversalEnvelopingAlgebra R (T R α)

def baseLie : T R α →ₗ⁅R⁆ T R (Option α) :=
  lift (fun i j => t (some i) (some j)) (fun i => t_self (some i))
    (fun i j => t_comm (some i) (some j)) (fun i j k l hik hil hjk hjl =>
      t_disjoint (some i) (some j) (some k) (some l) (fun h => hik (Option.some.inj h))
        (fun h => hil (Option.some.inj h)) (fun h => hjk (Option.some.inj h))
        (fun h => hjl (Option.some.inj h)))
    (fun i j k hij hik hjk => t_three (some i) (some j) (some k) (fun h => hij (Option.some.inj h))
      (fun h => hik (Option.some.inj h)) (fun h => hjk (Option.some.inj h)))
omit [DecidableEq α] in
/--
@isnad1 id=eq.0h4v.s8.9d4e80ed5ace from=translated src=- shape=79405c68 vocab=e6211034
-/
@[simp] theorem baseLie_t (i j : α) : baseLie (t (R:=R) i j)=t (some i) (some j) := by
  simp [baseLie]

omit [DecidableEq α] in
/--
@isnad1 id=eq.1h5v.s8.fd43db1c90a6 from=translated src=- shape=3161ba32 vocab=67a18cad
-/
theorem hom_ext {E : Type*} [LieRing E] [LieAlgebra R E]
    {f g : T R α →ₗ⁅R⁆ E} (h : ∀ i j, f (t i j)=g (t i j)) : f=g := by
  let q : Free R α →ₗ⁅R⁆ T R α :=
    { (ideal (R:=R) (α:=α)).mkQ with map_lie' := by intros; rfl }
  have hh : f.comp q=g.comp q := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨i,j⟩
    exact h i j
  apply LieHom.ext
  intro a
  induction a using Submodule.Quotient.induction_on with | _ a =>
    exact LieHom.congr_fun hh a

def fiberIn : A R α →ₐ[R] Env R (Option α) :=
  AssociativeElimination.lift (fun i => UniversalEnvelopingAlgebra.ι R (t none (some i)))
def baseIn : Env R α →ₐ[R] Env R (Option α) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp baseLie)
def toSemi : Env R (Option α) →ₐ[R] UniversalEnvelopingAlgebra R
    (SemiDirectSum (FreeLieAlgebra R α) (T R α) action) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp toSemidirect)

/--
@isnad1 id=eq.0h2v.s10.f64868d82e69 from=translated src=- shape=91e1e9c4 vocab=b2088a08
-/
theorem toSemi_fiber : toSemi.comp fiberIn=FiberPBW.fiberIn (action (R:=R) (α:=α)) := by
  apply AssociativeElimination.hom_ext
  intro i
  simp [toSemi,fiberIn,FiberPBW.fiberIn,fiber]

/--
@isnad1 id=eq.0h2v.s11.077acc062037 from=translated src=- shape=7956a6c7 vocab=00336f9b
-/
theorem toSemi_base : toSemi.comp baseIn=FiberPBW.baseIn (action (R:=R) (α:=α)) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply hom_ext
  intro i j
  simp [toSemi,baseIn,FiberPBW.baseIn,base]

def normal : A R α ⊗[R] Env R α →ₗ[R] Env R (Option α) :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun b => fiberIn p*baseIn b
          map_add' := by intro b c; simp [mul_add]
          map_smul' := by intro r b; simp }
      map_add' := by intro p q; ext b; simp [add_mul]
      map_smul' := by intro r p; ext b; simp }
omit [DecidableEq α] in
/--
@isnad1 id=eq.0h4v.s12.6021b7f35e40 from=translated src=- shape=736e4193 vocab=d59315f4
-/
@[simp] theorem normal_tmul (p : A R α) (b : Env R α) :
    normal (p⊗ₜ b)=fiberIn p*baseIn b := rfl

/--
@isnad1 id=eq.0h2v.s12.fa08f9639b41 from=translated src=- shape=8b9ebf02 vocab=e56e7125
-/
theorem toSemi_normal : toSemi.toLinearMap.comp normal=
    FiberPBW.normal (action (R:=R) (α:=α)) := by
  apply TensorProduct.ext'
  intro p b
  change toSemi (fiberIn p*baseIn b)=_
  rw [map_mul]
  have hf := AlgHom.congr_fun (toSemi_fiber (R:=R) (α:=α)) p
  have hb := AlgHom.congr_fun (toSemi_base (R:=R) (α:=α)) b
  exact congrArg₂ (·*·) hf hb

/--
@isnad1 id=injectiv.0h2v.s11.e6d210139650 from=translated src=- shape=7084b297 vocab=3b7e5c53
-/
theorem normal_injective : Function.Injective (normal (R:=R) (α:=α)) := by
  intro a b h
  apply FiberPBW.normal_injective (action (R:=R) (α:=α))
  have he (z) := LinearMap.congr_fun (toSemi_normal (R:=R) (α:=α)) z
  rw [← he a,← he b]
  exact congrArg toSemi h
end GenericBraid

namespace RestrictedAlphabet
open LieAlgebra AssociativeElimination
open scoped TensorProduct
variable {α : Type*} [DecidableEq α]
local notation "U" => UniversalEnvelopingAlgebra F (GenericBraid.T F (Option α))

def normal : S α ⊗[F] U →ₗ[F]
    UniversalEnvelopingAlgebra F (GenericBraid.T F (Option (Option α))) :=
  GenericBraid.normal.comp (substitution.toLinearMap.rTensor U)

/--
@isnad1 id=injectiv.0h1v.s13.819c1a25390d from=translated src=- shape=fdeeee8e vocab=599a6b4f
-/
theorem normal_injective : Function.Injective (normal (α:=α)) :=
  GenericBraid.normal_injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap substitution.toLinearMap injective)
end RestrictedAlphabet

namespace Deletion

section
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
def word (w : List α) : A R α := MonoidAlgebra.single (FreeMonoid.ofList w) 1
/--
@isnad1 id=eq.0h2v.s5.a98ed46aded7 from=translated src=- shape=b393f0ee vocab=8638be8e
-/
@[simp] theorem word_nil : word ([] : List α)=(1 : A R α) := rfl
/--
@isnad1 id=eq.0h4v.s6.97838bcfa276 from=translated src=- shape=3236e9d3 vocab=6d0dd6c5
-/
theorem word_cons (a : α) (s : List α) : word (R:=R) (a::s)=atom a*word s := by
  simp only [word,atom,MonoidAlgebra.single_mul_single,one_mul,FreeMonoid.ofList_cons]

def raw (ν : α → α → R) (l r : α) : List α → A R α
  | [] => 0
  | a::s => (ν a (s.headD r)-ν l a) • word s+atom a*raw ν a r s

def op (ν : α → α → R) (l r : α) : Module.End R (A R α) :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => raw ν l r w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
/--
@isnad1 id=eq.0h6v.s7.23d53d75bfac from=translated src=- shape=6166bc87 vocab=f407a221
-/
@[simp] theorem op_word (ν : α → α → R) (l r : α) (s : List α) :
    op ν l r (word s)=raw ν l r s := by
  change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => raw ν l r monoidWord.toList) (Finsupp.single (FreeMonoid.ofList s) 1) = _; simp
/--
@isnad1 id=eq.0h5v.s7.28f38fdecb39 from=translated src=- shape=ca7dab93 vocab=d846b15f
-/
@[simp] theorem op_one (ν : α → α → R) (l r : α) : op ν l r 1=0 := by
  exact op_word ν l r []
/--
@isnad1 id=eq.0h7v.s9.d6e6afba6b34 from=translated src=- shape=3ada56db vocab=8acc84c3
-/
theorem op_cons (ν : α → α → R) (l r a : α) (s : List α) :
    op ν l r (word (a::s))=(ν a (s.headD r)-ν l a) • word s+atom a*op ν a r (word s) := by
  simp only [op_word,raw]
/--
@isnad1 id=eq.0h7v.s9.17c1e82f4dca from=translated src=- shape=5b4332fb vocab=d06ef788
-/
theorem op_mul_word (ν : α → α → R) (l r a : α) (s : List α) :
    op ν l r (atom a*word s)=(ν a (s.headD r)-ν l a) • word s+atom a*op ν a r (word s) := by
  rw [← word_cons,op_cons]

/--
@isnad1 id=eq.0h8v.s9.2aea1a502375 from=translated src=- shape=6c7b1a98 vocab=d59d0f18
-/
theorem op_two (ν : α → α → R) (l r a b : α) (p : A R α) :
    op ν l r (atom a*(atom b*p))=(ν a b-ν l a) • (atom b*p)+atom a*op ν a r (atom b*p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    have h := op_cons ν l r a (b::w.toList)
    simp only [word_cons,List.headD_cons] at h
    simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using h
  | add p q hp hq => simp only [mul_add,map_add,smul_add,hp,hq]; abel
  | smul c p hp => simp only [mul_smul_comm,map_smul,hp,smul_add,smul_smul]; rw [mul_comm c]

def curvature (ν μ : α → α → R) (l a b c : α) : R :=
  (ν a b-ν l a)*(μ b c-μ l b)+(ν b c-ν a b)*(μ a c-μ l a)-
  (μ a b-μ l a)*(ν b c-ν l b)-(μ b c-μ a b)*(ν a c-ν l a)

/--
@isnad1 id=eq.0h9v.s10.2d2cc57617e0 from=translated src=- shape=6fdcef08 vocab=7ddd2ba1
-/
theorem comm_cons (ν μ : α → α → R) (l r a b : α) (s : List α) :
    op μ l r (op ν l r (word (a::b::s)))-op ν l r (op μ l r (word (a::b::s)))=
      curvature ν μ l a b (s.headD r) • word s+
        atom a*(op μ a r (op ν a r (word (b::s)))-op ν a r (op μ a r (word (b::s)))) := by
  simp only [word_cons,op_two,op_mul_word,map_add,map_smul,mul_add,mul_smul_comm,
    mul_sub,smul_add,curvature]
  module

/--
@isnad1 id=eq.1h6v.s10.0c5efc3e1d6e from=translated src=- shape=3e0c45f3 vocab=72ca0488
-/
theorem commute_of_curvature (ν μ : α → α → R)
    (hc : ∀ l a b c,curvature ν μ l a b c=0) (l r : α) : ⁅op μ l r,op ν l r⁆=0 := by
  apply LinearMap.ext
  intro p
  have hs (s : List α) : op μ l r (op ν l r (word s))-op ν l r (op μ l r (word s))=0 := by
    induction s generalizing l with
    | nil => simp
    | cons a s ih =>
      cases s with
      | nil => simp [raw]
      | cons b s => rw [comm_cons,hc,ih]; simp
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change op μ l r (op ν l r (MonoidAlgebra.single w 1))-
      op ν l r (op μ l r (MonoidAlgebra.single w 1))=0
    simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using hs w.toList
  | add p q hp hq =>
    simp only [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.zero_apply] at hp hq ⊢
    simp only [map_add]
    rw [add_sub_add_comm, hp, hq, add_zero]
  | smul c p hp => simpa using congrArg (c • ·) hp
end

open AssociativeElimination
variable {R α : Type*} [CommRing R]
/--
@isnad1 id=eq.1h5v.s8.775b2286668e from=translated src=- shape=2c14c909 vocab=f465c59d
-/
theorem linear_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : A R α →ₗ[R] M} (h : ∀ s : List α,f (word s)=g (word s)) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using h w.toList
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

/--
@isnad1 id=eq.0h7v.s6.f27ed20604ef from=translated src=- shape=5cc34ec5 vocab=a441ddf1
-/
theorem raw_add (ν μ : α → α → R) (l r : α) (s : List α) :
    raw (fun a b => ν a b+μ a b) l r s=raw ν l r s+raw μ l r s := by
  induction s generalizing l with
  | nil => simp [raw]
  | cons a s ih => simp only [raw,ih,mul_add]; module
/--
@isnad1 id=eq.0h6v.s8.fbf58974a372 from=translated src=- shape=c2dd3aa4 vocab=b32d4cc5
-/
@[simp] theorem op_add (ν μ : α → α → R) (l r : α) :
    op (fun a b => ν a b+μ a b) l r=op ν l r+op μ l r := by
  apply linear_ext
  intro s
  simp only [LinearMap.add_apply,op_word,raw_add]
/--
@isnad1 id=eq.0h4v.s8.1c035409285d from=translated src=- shape=b9ca687a vocab=3fec73ce
-/
@[simp] theorem op_zero (l r : α) : op (fun _ _ => (0 : R)) l r=0 := by
  apply linear_ext
  intro s
  simp only [LinearMap.zero_apply,op_word]
  induction s generalizing l with
  | nil => rfl
  | cons a s ih => simp [raw,ih]

/--
@isnad1 id=eq.0h7v.s8.c5576f8548e9 from=translated src=- shape=86d0e955 vocab=aa981124
-/
theorem op_list_sum {ι : Type*} (ν : ι → α → α → R) (s : List ι) (l r : α) :
    op (fun a b => (s.map (fun i => ν i a b)).sum) l r=(s.map (fun i => op (ν i) l r)).sum := by
  induction s with
  | nil => simp
  | cons i s ih => simpa only [List.map_cons,List.sum_cons,op_add] using congrArg (op (ν i) l r+·) ih
end Deletion

namespace DeletionTable
open Deletion AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
inductive Letter | o | e | p | w deriving DecidableEq
instance : Fintype Letter := ⟨{.o,.e,.p,.w}, by intro x; cases x <;> simp⟩
inductive Hyperplane | a1 | a2 | a3 | p12 | m12 | p13 | m13 | p23 | m23 deriving DecidableEq
instance : Fintype Hyperplane := ⟨{.a1,.a2,.a3,.p12,.m12,.p13,.m13,.p23,.m23}, by intro x; cases x <;> simp⟩
open Letter Hyperplane

def weight : Hyperplane → Letter → Letter → ℤ
  | .p23, .o, .p | .p23, .p, .o => 1
  | .m23, .o, .p | .m23, .p, .o => -1
  | .p12, .o, .w | .p12, .w, .o => 1
  | .m12, .o, .w | .m12, .w, .o => -1
  | .a3, .e, .p | .a3, .p, .e => 1
  | .m23, .e, .p | .m23, .p, .e => -1
  | .a1, .e, .w | .a1, .w, .e => 1
  | .m12, .e, .w | .m12, .w, .e => -1
  | .a2, .p, .w | .a2, .w, .p => 1
  | .p13, .p, .w | .p13, .w, .p => 1
  | .m12, .p, .w | .m12, .w, .p => -1
  | .m23, .p, .w | .m23, .w, .p => -1
  | _, _, _ => 0

def flat : Fin 13 → List Hyperplane :=
  ![[.a1,.a2,.p12,.m12],
    [.a1,.a3,.p13,.m13],
    [.a2,.a3,.p23,.m23],
    [.p12,.p13,.p23],
    [.p12,.m13,.m23],
    [.m12,.p13,.m23],
    [.m12,.m13,.p23],
    [.a1,.p23],
    [.a1,.m23],
    [.a2,.p13],
    [.a2,.m13],
    [.a3,.p12],
    [.a3,.m12]]

def total (i : Fin 13) (a b : Letter) : ℤ := ((flat i).map (fun h => weight h a b)).sum

/--
@isnad1 id=eq.1h5v.s6.b7a972a9edf9 from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_0 : ∀ h : Hyperplane, h∈flat 0 →
    ∀ l a b c : Letter, curvature (weight h) (total 0) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.48d734433066 from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_1 : ∀ h : Hyperplane, h∈flat 1 →
    ∀ l a b c : Letter, curvature (weight h) (total 1) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.3baa9c334d83 from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_2 : ∀ h : Hyperplane, h∈flat 2 →
    ∀ l a b c : Letter, curvature (weight h) (total 2) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.7e8e72f12930 from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_3 : ∀ h : Hyperplane, h∈flat 3 →
    ∀ l a b c : Letter, curvature (weight h) (total 3) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.ce4c223c1a08 from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_4 : ∀ h : Hyperplane, h∈flat 4 →
    ∀ l a b c : Letter, curvature (weight h) (total 4) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.bd0b70fcbc69 from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_5 : ∀ h : Hyperplane, h∈flat 5 →
    ∀ l a b c : Letter, curvature (weight h) (total 5) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.418219a9cb9a from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_6 : ∀ h : Hyperplane, h∈flat 6 →
    ∀ l a b c : Letter, curvature (weight h) (total 6) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.8c32f6469001 from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_7 : ∀ h : Hyperplane, h∈flat 7 →
    ∀ l a b c : Letter, curvature (weight h) (total 7) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.a62723fba7cb from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_8 : ∀ h : Hyperplane, h∈flat 8 →
    ∀ l a b c : Letter, curvature (weight h) (total 8) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.ce6be8686dce from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_9 : ∀ h : Hyperplane, h∈flat 9 →
    ∀ l a b c : Letter, curvature (weight h) (total 9) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.5588a9861cdf from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_10 : ∀ h : Hyperplane, h∈flat 10 →
    ∀ l a b c : Letter, curvature (weight h) (total 10) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.c5df8098fb74 from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_11 : ∀ h : Hyperplane, h∈flat 11 →
    ∀ l a b c : Letter, curvature (weight h) (total 11) l a b c=0 := by decide

/--
@isnad1 id=eq.1h5v.s6.014ab08baaea from=translated src=- shape=452ee444 vocab=79cde004
-/
theorem curvature_12 : ∀ h : Hyperplane, h∈flat 12 →
    ∀ l a b c : Letter, curvature (weight h) (total 12) l a b c=0 := by decide

/--
@isnad1 id=eq.1h6v.s5.448d6895e159 from=translated src=- shape=2ec097f8 vocab=79cde004
-/
theorem flat_curvature (i : Fin 13) (h : Hyperplane) (hi : h∈flat i) (l a b c : Letter) :
    curvature (weight h) (total i) l a b c=0 := by
  fin_cases i
  · exact curvature_0 h hi l a b c
  · exact curvature_1 h hi l a b c
  · exact curvature_2 h hi l a b c
  · exact curvature_3 h hi l a b c
  · exact curvature_4 h hi l a b c
  · exact curvature_5 h hi l a b c
  · exact curvature_6 h hi l a b c
  · exact curvature_7 h hi l a b c
  · exact curvature_8 h hi l a b c
  · exact curvature_9 h hi l a b c
  · exact curvature_10 h hi l a b c
  · exact curvature_11 h hi l a b c
  · exact curvature_12 h hi l a b c

/--
@isnad1 id=eq.1h4v.s10.5a362e009098 from=translated src=- shape=ca136e88 vocab=cc661e3b
-/
theorem integral_flat (i : Fin 13) (h : Hyperplane) (hi : h∈flat i) (l r : Letter) :
    ⁅op (weight h) l r,((flat i).map (fun g => op (weight g) l r)).sum⁆=0 := by
  rw [← op_list_sum]
  change ⁅op (weight h) l r,op (total i) l r⁆=0
  have hc := commute_of_curvature (weight h) (total i) (flat_curvature i h hi) l r
  rw [← lie_skew,hc,neg_zero]
end DeletionTable

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]

/--
@isnad1 id=var.0h9v.s9.b7f5126e811d from=translated src=- shape=19d89e68 vocab=8594546d
-/
theorem induction {P : T R α → Prop} (h0 : P 0) (ht : ∀ i j,P (t i j))
    (ha : ∀ p q,P p → P q → P (p+q)) (hs : ∀ (r : R) p,P p → P (r • p))
    (hl : ∀ p q,P p → P q → P ⁅p,q⁆) (p : T R α) : P p := by
  induction p using Submodule.Quotient.induction_on with | _ p =>
    induction p using freeLie_induction with
    | h0 => exact h0
    | hg ij => exact ht ij.1 ij.2
    | ha p q hp hq => exact ha _ _ hp hq
    | hs r p hp => exact hs r _ hp
    | hl p q hp hq => exact hl _ _ hp hq

variable [DecidableEq α]
def fiberLie : FreeLieAlgebra R α →ₗ⁅R⁆ T R (Option α) :=
  FreeLieAlgebra.lift R (fun i => t none (some i))
omit [DecidableEq α] in
/--
@isnad1 id=eq.0h3v.s7.4def7c51b7ca from=translated src=- shape=a6cb20a1 vocab=44fe0504
-/
@[simp] theorem fiberLie_of (i : α) : fiberLie (FreeLieAlgebra.of R i)=t none (some i) := by
  simp [fiberLie]

/--
@isnad1 id=eq.0h4v.s7.872bd5c92772 from=translated src=- shape=d27013ac vocab=114d2da1
-/
theorem t_base_fiber_left (i j : α) :
    ⁅t (R:=R) (some i) (some j),t (R:=R) none (some i)⁆=⁅t (R:=R) none (some i),t (R:=R) none (some j)⁆ := by
  by_cases hij : i=j
  · subst j; simp
  have h := t_three (R:=R) (none : Option α) (some i) (some j) (by simp) (by simp)
    (fun h => hij (Option.some.inj h))
  rw [lie_add] at h
  grind [lie_skew]

/--
@isnad1 id=eq.0h4v.s10.ac052c1376e1 from=translated src=- shape=4118f4bb vocab=67054b3c
-/
theorem compatibility (g : T R α) (p : FreeLieAlgebra R α) :
    fiberLie (action g p)=⁅baseLie g,fiberLie p⁆ := by
  induction g using induction generalizing p with
  | h0 => simp
  | ht i j =>
    rw [action_t,baseLie_t]
    induction p using freeLie_induction with
    | h0 => simp
    | hg k =>
      by_cases hki : k=i
      · subst k; simp only [pair_of_left,LieHom.map_lie,fiberLie_of]; exact (t_base_fiber_left i j).symm
      by_cases hkj : k=j
      · subst k
        simp only [pair_of_right,LieHom.map_lie,fiberLie_of]
        rw [t_comm (some i) (some j)]
        exact (t_base_fiber_left j i).symm
      simp only [pair_of_other i j k hki hkj,map_zero,fiberLie_of]
      exact (t_disjoint _ _ _ _ (by simp) (fun h => hki (Option.some.inj h).symm)
        (by simp) (fun h => hkj (Option.some.inj h).symm)).symm
    | ha p q hp hq => simp [hp,hq,lie_add]
    | hs r p hp => simp [hp]
    | hl p q hp hq =>
      simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
      simpa only [add_comm] using (leibniz_lie (t (R:=R) (some i) (some j)) (fiberLie p) (fiberLie q)).symm
  | ha g h hg hh => simp [hg,hh,add_lie]
  | hs r g hg => simp [hg]
  | hl g h hg hh =>
    simp only [LieHom.map_lie,LieDerivation.lie_apply,map_sub,hg,hh]
    exact (lie_lie _ _ _).symm

def fromSemidirect : SemiDirectSum (FreeLieAlgebra R α) (T R α) action →ₗ⁅R⁆ T R (Option α) :=
  InnerSemiDirect.lift action fiberLie baseLie compatibility

/--
@isnad1 id=eq.0h3v.s10.31b4b28efe76 from=translated src=- shape=a58dd02f vocab=f923ebb9
-/
theorem toSemidirect_fiberLie (p : FreeLieAlgebra R α) :
    toSemidirect (fiberLie p)=SemiDirectSum.inl action p := by
  have h : (toSemidirect (R:=R) (α:=α)).comp fiberLie=SemiDirectSum.inl action := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [fiber]
  exact LieHom.congr_fun h p

/--
@isnad1 id=eq.0h3v.s10.bd2f40b912ba from=translated src=- shape=7a641824 vocab=750c1c72
-/
theorem toSemidirect_baseLie (p : T R α) :
    toSemidirect (baseLie p)=SemiDirectSum.inr action p := by
  have h : (toSemidirect (R:=R) (α:=α)).comp baseLie=SemiDirectSum.inr action := by
    apply hom_ext
    intro i j
    simp [base]
  exact LieHom.congr_fun h p

/--
@isnad1 id=eq.0h3v.s10.2efe3289c1dc from=translated src=- shape=651d08df vocab=a5c048dd
-/
theorem to_from (p : SemiDirectSum (FreeLieAlgebra R α) (T R α) action) :
    toSemidirect (fromSemidirect p)=p := by
  change toSemidirect (fiberLie p.left+baseLie p.right)=p
  rw [map_add,toSemidirect_fiberLie,toSemidirect_baseLie]
  ext <;> simp

/--
@isnad1 id=eq.0h3v.s10.7d3f148ede5d from=translated src=- shape=154d3aa8 vocab=a5c048dd
-/
theorem from_to (p : T R (Option α)) : fromSemidirect (toSemidirect p)=p := by
  have h : (fromSemidirect (R:=R) (α:=α)).comp toSemidirect=LieHom.id := by
    apply hom_ext
    intro i j
    cases i <;> cases j <;> simp [fromSemidirect,InnerSemiDirect.lift,fiber,base,t_comm]
  exact LieHom.congr_fun h p

def equivalence : T R (Option α) ≃ₗ⁅R⁆ SemiDirectSum (FreeLieAlgebra R α) (T R α) action :=
  { toSemidirect with
    invFun := fromSemidirect
    left_inv := from_to
    right_inv := to_from }
end GenericBraid

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace IntegralBaseChange
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {S α : Type*} [CommRing S]
def words : A ℤ α →+* A S α := MonoidAlgebra.mapRingHom _ (Int.castRingHom S)
/--
@isnad1 id=eq.0h3v.s7.7ce859b3c305 from=translated src=- shape=cae61cfc vocab=73ee49d3
-/
@[simp] theorem words_atom (a : α) : words (atom a : A ℤ α)=(atom a : A S α) := by
  simp [words,atom]
/--
@isnad1 id=eq.0h4v.s7.5c5b8e2941c8 from=translated src=- shape=08f2750a vocab=e6958487
-/
@[simp] theorem words_coeff (p : A ℤ α) (w : FreeMonoid α) :
    (words p : A S α).coeff w=(p.coeff w : S) := by simp [words]
def lie : FreeLieAlgebra ℤ α →ₗ⁅ℤ⁆ FreeLieAlgebra S α :=
  FreeLieAlgebra.lift ℤ (FreeLieAlgebra.of S)
/--
@isnad1 id=eq.0h3v.s6.1bfaa7ab481e from=translated src=- shape=4b8c1aa8 vocab=68220948
-/
@[simp] theorem lie_of (a : α) : lie (FreeLieAlgebra.of ℤ a)=FreeLieAlgebra.of S a := by exact FreeLieAlgebra.lift_of_apply (FreeLieAlgebra.of S) a
/--
@isnad1 id=eq.0h3v.s9.c7dc4b30e27a from=translated src=- shape=5c1e8189 vocab=54d767f8
-/
theorem embed_lie (p : FreeLieAlgebra ℤ α) :
    embed (lie p : FreeLieAlgebra S α)=words (embed p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq,Ring.lie_def,map_sub,map_mul]
/--
@isnad1 id=injectiv.0h1v.s6.689411828958 from=translated src=- shape=7f4e9927 vocab=1e0e2b27
-/
theorem words_rational_injective : Function.Injective (words (S:=ℚ) (α:=α)) := by
  intro p q h
  ext w
  have hc := congrArg (fun z : A ℚ α => z.coeff w) h
  simpa using hc

/--
@isnad1 id=injectiv.0h1v.s6.c45c4525b4d7 from=translated src=- shape=f5aa3f84 vocab=fdbc62f8
-/
theorem lie_rational_injective : Function.Injective (lie (S:=ℚ) (α:=α)) := by
  intro p q h
  apply UniversalEmbedding.injective
  apply words_rational_injective
  rw [← embed_lie,← embed_lie,h]

/--
@isnad1 id=ex.1h2v.s8.0f4af1014ae8 from=translated src=- shape=358e21f0 vocab=d9d6ca0e
-/
theorem lift_integral {p : FreeLieAlgebra ℚ α} (hp : embed p∈IntegralWords.lattice) :
    ∃ q : FreeLieAlgebra ℤ α,lie q=p := by
  have hr : embed p∈IntegralWords.rationalLie := by
    clear hp
    induction p using freeLie_induction with
    | h0 => simp
    | hg a => exact LieSubalgebra.subset_lieSpan ⟨a,by simp⟩
    | ha p q hp hq => simpa using IntegralWords.rationalLie.add_mem hp hq
    | hs r p hp => simpa using IntegralWords.rationalLie.smul_mem r hp
    | hl p q hp hq => simpa only [LieHom.map_lie] using IntegralWords.rationalLie.lie_mem hp hq
  have hi := IntegralWords.saturation hr hp
  let f : FreeLieAlgebra ℤ α →ₗ⁅ℤ⁆ A ℚ α := FreeLieAlgebra.lift ℤ atom
  have he (q : FreeLieAlgebra ℤ α) : f q=embed (lie q : FreeLieAlgebra ℚ α) := by
    induction q using freeLie_induction with
    | h0 => simp
    | hg a => rw [lie_of,embed_of]; exact FreeLieAlgebra.lift_of_apply atom a
    | ha p q hp hq => simp [hp,hq]
    | hs r p hp => simp [map_smul,hp]
    | hl p q hp hq => simp [hp,hq]
  have hspan : IntegralWords.lieLattice ≤ f.range := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro a ⟨a,rfl⟩
    exact ⟨FreeLieAlgebra.of ℤ a,FreeLieAlgebra.lift_of_apply atom a⟩
  obtain ⟨q,hq⟩ := hspan hi
  refine ⟨q, UniversalEmbedding.injective ?_⟩
  rw [← he]
  exact hq
end IntegralBaseChange

namespace GenericBraid

section
variable {S α β : Type*} [CommRing S]
def cast : T ℤ α →ₗ⁅ℤ⁆ T S α :=
  lift (t (R:=S)) t_self t_comm t_disjoint t_three
/--
@isnad1 id=eq.0h4v.s8.d2cfb126ed79 from=translated src=- shape=d267daf7 vocab=357fb797
-/
@[simp] theorem cast_t (i j : α) : cast (t (R:=ℤ) i j)=t (R:=S) i j := by simp [cast]
def rename {R : Type*} [CommRing R] (e : α ≃ β) : T R α →ₗ⁅R⁆ T R β :=
  lift (fun i j => t (e i) (e j)) (fun i => t_self (e i)) (fun i j => t_comm (e i) (e j))
    (fun i j k l hik hil hjk hjl => t_disjoint (e i) (e j) (e k) (e l)
      (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl))
    (fun i j k hij hik hjk => t_three (e i) (e j) (e k) (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))
/--
@isnad1 id=eq.0h6v.s8.0610b64203cc from=translated src=- shape=129bfb01 vocab=d615dcaf
-/
@[simp] theorem rename_t {R : Type*} [CommRing R] (e : α ≃ β) (i j : α) :
    rename e (t (R:=R) i j)=t (e i) (e j) := by simp [rename]
/--
@isnad1 id=eq.0h5v.s8.3b903ad08322 from=translated src=- shape=9544343e vocab=cd76edfd
-/
theorem rename_symm {R : Type*} [CommRing R] (e : α ≃ β) (p : T R α) :
    rename e.symm (rename e p)=p := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
/--
@isnad1 id=injectiv.0h4v.s7.26cd007e1b25 from=translated src=- shape=19d127bf vocab=80f40b53
-/
theorem rename_injective {R : Type*} [CommRing R] (e : α ≃ β) :
    Function.Injective (rename (R:=R) e) := Function.LeftInverse.injective (rename_symm e)
/--
@isnad1 id=eq.0h5v.s9.d6b770a91a9e from=translated src=- shape=3e383c76 vocab=a659798a
-/
theorem cast_rename (e : α ≃ β) (p : T ℤ α) :
    cast (S:=S) (rename e p)=rename e (cast p) := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
variable [DecidableEq α]
omit [DecidableEq α] in
/--
@isnad1 id=eq.0h3v.s9.faa079a23e8f from=translated src=- shape=9d089dd1 vocab=5f737fad
-/
theorem cast_fiber (p : FreeLieAlgebra ℤ α) :
    cast (S:=S) (fiberLie p)=fiberLie (IntegralBaseChange.lie p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
omit [DecidableEq α] in
/--
@isnad1 id=eq.0h3v.s10.75316ca641b2 from=translated src=- shape=69e6a1b0 vocab=50008a4b
-/
theorem cast_base (p : T ℤ α) : cast (S:=S) (baseLie p)=baseLie (cast p) := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
/--
@isnad1 id=injectiv.1h1v.s9.167981317c95 from=translated src=- shape=4ba9f306 vocab=1ed5a8d2
-/
theorem cast_option_injective (h : Function.Injective (cast (S:=ℚ) (α:=α))) :
    Function.Injective (cast (S:=ℚ) (α:=Option α)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  have hd : p=fiberLie (toSemidirect p).left+baseLie (toSemidirect p).right := (from_to p).symm
  rw [hd,map_add,cast_fiber,cast_base] at hp
  have he := congrArg (toSemidirect (R:=ℚ) (α:=α)) hp
  rw [map_add,toSemidirect_fiberLie,toSemidirect_baseLie,map_zero] at he
  have hl := congrArg LieAlgebra.SemiDirectSum.left he
  have hr := congrArg LieAlgebra.SemiDirectSum.right he
  simp only [LieAlgebra.SemiDirectSum.add_eq_mk,LieAlgebra.SemiDirectSum.inl_eq_mk,
    LieAlgebra.SemiDirectSum.inr_eq_mk,add_zero,zero_add,LieAlgebra.SemiDirectSum.zero_eq_mk] at hl hr
  have hl0 : (toSemidirect p).left=0 := IntegralBaseChange.lie_rational_injective (hl.trans (map_zero _).symm)
  have hr0 : (toSemidirect p).right=0 := h (hr.trans (map_zero _).symm)
  rw [hd,hl0,hr0,map_zero,map_zero,add_zero]
end

variable {α : Type*}
/--
@isnad1 id=injectiv.0h1v.s8.b504a012acb9 from=translated src=- shape=b6464893 vocab=40b70d1f
-/
theorem cast_fin_injective (n : ℕ) : Function.Injective (cast (S:=ℚ) (α:=Fin n)) := by
  induction n with
  | zero =>
    have hz (p : T ℤ (Fin 0)) : p=0 := by
      induction p using induction with
      | h0 => rfl
      | ht i j => exact Fin.elim0 i
      | ha p q hp hq => simp [hp,hq]
      | hs r p hp => simp [hp]
      | hl p q hp hq => simp [hp,hq]
    intro p q _
    rw [hz p,hz q]
  | succ n ih =>
    intro p q h
    apply rename_injective (finSuccEquiv' (0 : Fin (n+1)))
    apply cast_option_injective ih
    rw [cast_rename,cast_rename,h]
/--
@isnad1 id=injectiv.0h1v.s8.c31be40f2eef from=translated src=- shape=ecbd1f1a vocab=446495b8
-/
theorem cast_finite_injective [Fintype α] : Function.Injective (cast (S:=ℚ) (α:=α)) := by
  intro p q h
  apply rename_injective (Fintype.equivFin α)
  apply cast_fin_injective
  rw [cast_rename,cast_rename,h]

def fromT4 : T4 →ₗ⁅ℚ⁆ T ℚ (Fin 4) :=
  T4Universal.lift (t (R:=ℚ)) t_comm t_self
    (fun i j k l _ hik hil hjk hjl _ => t_disjoint i j k l hik hil hjk hjl) t_three
/--
@isnad1 id=eq.0h2v.s8.f199700d5dbc from=translated src=- shape=03a38636 vocab=54623382
-/
@[simp] theorem fromT4_t (i j : Fin 4) : fromT4 (DeligneDrinfeld.t i j)=t i j := by
  simp [fromT4]
end GenericBraid

namespace BaseChangeEquations
variable {R : Type*} [CommRing R]
def x : FreeLieAlgebra R Bool := FreeLieAlgebra.of R false
def y : FreeLieAlgebra R Bool := FreeLieAlgebra.of R true
def eval {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : FreeLieAlgebra R Bool →ₗ⁅R⁆ M :=
  FreeLieAlgebra.lift R (fun i => if i then b else a)
/--
@isnad1 id=eq.0h4v.s6.35f2216349ee from=translated src=- shape=6e813175 vocab=ecb8a6b7
-/
@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : eval (R:=R) a b x=a := by simp [eval,x]
/--
@isnad1 id=eq.0h4v.s6.969788feb7a2 from=translated src=- shape=2297cb99 vocab=fa6dafb4
-/
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : eval (R:=R) a b y=b := by simp [eval,y]
def antisymmetry (q : FreeLieAlgebra R Bool) := q+eval y x q
def threeTerm (q : FreeLieAlgebra R Bool) := q+eval y (-x-y) q+eval (-x-y) x q
def pentagon (q : FreeLieAlgebra R Bool) : GenericBraid.T R (Fin 4) :=
  let t := GenericBraid.t (R:=R)
  eval (t 0 1) (t 1 2+t 1 3) q+eval (t 0 2+t 1 2) (t 2 3) q-
    eval (t 1 2) (t 2 3) q-eval (t 0 1+t 0 2) (t 1 3+t 2 3) q-eval (t 0 1) (t 1 2) q

def Equations (q : FreeLieAlgebra R Bool) : Prop :=
  antisymmetry q=0 ∧ threeTerm q=0 ∧ pentagon q=0

/--
@isnad1 id=eq.1h1v.s8.7b4c4f08994a from=translated src=- shape=a8e6d4a5 vocab=c64e7bed
-/
theorem pentagon_rational {q : L} (hq : q∈W) : pentagon q=0 := by
  have h := congrArg GenericBraid.fromT4 hq.2.2
  have he (a b : T4) : GenericBraid.fromT4 (DeligneDrinfeld.eval a b q)=
      eval (GenericBraid.fromT4 a) (GenericBraid.fromT4 b) q := by
    have hm : GenericBraid.fromT4.comp (DeligneDrinfeld.eval a b)=
        eval (GenericBraid.fromT4 a) (GenericBraid.fromT4 b) := by
      apply FreeLieAlgebra.hom_ext
      intro i
      cases i <;> simp [eval,DeligneDrinfeld.eval]
    exact LieHom.congr_fun hm q
  simp only [map_add,he,GenericBraid.fromT4_t] at h
  change _ - _ - _ - _ = 0
  rw [h]
  abel

/--
@isnad1 id=equation.1h1v.s6.f4402bf7d686 from=translated src=- shape=9da361cc vocab=5aa45073
-/
theorem rational {q : L} (hq : q∈W) : Equations q :=
  ⟨hq.1,hq.2.1,pentagon_rational hq⟩

variable {S : Type*} [CommRing S]
/--
@isnad1 id=eq.0h4v.s9.a5661a1d93ef from=translated src=- shape=aae7803b vocab=6d91ee47
-/
theorem cast_eval_lie (a b q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (eval a b q)=
      eval (R:=S) (IntegralBaseChange.lie a) (IntegralBaseChange.lie b) (IntegralBaseChange.lie q) := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp =>
    rw [map_smul,map_smul]
    simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
/--
@isnad1 id=eq.0h4v.s11.914d666ea86d from=translated src=- shape=29dd683b vocab=56338c7d
-/
theorem cast_eval_braid (a b : GenericBraid.T ℤ (Fin 4)) (q : FreeLieAlgebra ℤ Bool) :
    GenericBraid.cast (S:=S) (eval a b q)=
      eval (R:=S) (GenericBraid.cast a) (GenericBraid.cast b) (IntegralBaseChange.lie q) := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
/--
@isnad1 id=eq.0h1v.s6.bb0868a9a54c from=translated src=- shape=bd1dc8ea vocab=6500ad9b
-/
@[simp] theorem cast_x : IntegralBaseChange.lie (x : FreeLieAlgebra ℤ Bool)=(x : FreeLieAlgebra S Bool) := by simp [x]
/--
@isnad1 id=eq.0h1v.s6.fb68bba1e969 from=translated src=- shape=bd1dc8ea vocab=5ff4926a
-/
@[simp] theorem cast_y : IntegralBaseChange.lie (y : FreeLieAlgebra ℤ Bool)=(y : FreeLieAlgebra S Bool) := by simp [y]
/--
@isnad1 id=eq.0h2v.s7.136771be5004 from=translated src=- shape=b5f79bf1 vocab=5e483232
-/
theorem cast_antisymmetry (q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (antisymmetry q)=antisymmetry (IntegralBaseChange.lie q) := by
  simp [antisymmetry,cast_eval_lie]
/--
@isnad1 id=eq.0h2v.s7.76428cfda742 from=translated src=- shape=b5f79bf1 vocab=3fab7df0
-/
theorem cast_threeTerm (q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (threeTerm q)=threeTerm (IntegralBaseChange.lie q) := by
  simp [threeTerm,cast_eval_lie]
/--
@isnad1 id=eq.0h2v.s9.3b9f8e7bceeb from=translated src=- shape=40c17b38 vocab=a2daf0e4
-/
theorem cast_pentagon (q : FreeLieAlgebra ℤ Bool) :
    GenericBraid.cast (S:=S) (pentagon q)=pentagon (IntegralBaseChange.lie q) := by
  simp only [pentagon,map_sub,map_add,cast_eval_braid,GenericBraid.cast_t]

/--
@isnad1 id=equation.1h1v.s7.01e12def7b7f from=translated src=- shape=d62b095f vocab=7373a1ee
-/
theorem integral_of_rational (q : FreeLieAlgebra ℤ Bool)
    (hq : (IntegralBaseChange.lie q : L)∈W) : Equations q := by
  have h := rational hq
  refine ⟨IntegralBaseChange.lie_rational_injective ?_,IntegralBaseChange.lie_rational_injective ?_,
    GenericBraid.cast_fin_injective 4 ?_⟩
  · rw [cast_antisymmetry,h.1,map_zero]
  · rw [cast_threeTerm,h.2.1,map_zero]
  · rw [cast_pentagon,h.2.2,map_zero]

/--
@isnad1 id=equation.1h2v.s7.f04df9ccf1b2 from=translated src=- shape=7e6decc0 vocab=087ade8e
-/
theorem reduce (q : FreeLieAlgebra ℤ Bool)
    (hq : (IntegralBaseChange.lie q : L)∈W) : Equations (IntegralBaseChange.lie (S:=S) q) := by
  have h := integral_of_rational q hq
  refine ⟨?_,?_,?_⟩
  · rw [← cast_antisymmetry,h.1,map_zero]
  · rw [← cast_threeTerm,h.2.1,map_zero]
  · rw [← cast_pentagon,h.2.2,map_zero]
end BaseChangeEquations

namespace PolynomialOrdering
open AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
variable (δ : β → α → A R α)
def fiberOp (a : α) : Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  TensorProduct.map (leftMul (atom a)) LinearMap.id
def baseOp (b : β) : Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  TensorProduct.map (deriv (δ b)) LinearMap.id+
    TensorProduct.map LinearMap.id (leftMul (atom b))
def op : Sum α β → Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  Sum.elim fiberOp (baseOp δ)
/--
@isnad1 id=eq.0h6v.s9.25f32f544edc from=translated src=- shape=5d323bf7 vocab=983a6408
-/
@[simp] theorem fiberOp_tmul (a : α) (p : A R α) (q : A R β) :
    fiberOp a (p⊗ₜ q)=(atom a*p)⊗ₜ q := rfl
/--
@isnad1 id=eq.0h7v.s10.e11f794eaaf0 from=translated src=- shape=eaab3e67 vocab=9162fcc2
-/
@[simp] theorem baseOp_tmul (b : β) (p : A R α) (q : A R β) :
    baseOp δ b (p⊗ₜ q)=deriv (δ b) p⊗ₜ q+p⊗ₜ (atom b*q) := rfl

def operators : A R (Sum α β) →ₐ[R] Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  lift (op δ)
def normalize : A R (Sum α β) →ₗ[R] V (R:=R) (α:=α) (β:=β) :=
  (LinearMap.applyₗ ((1 : A R α)⊗ₜ (1 : A R β))).comp (operators δ).toLinearMap
/--
@isnad1 id=eq.0h4v.s9.91c86fa92d62 from=translated src=- shape=45709385 vocab=7cdd0bb2
-/
@[simp] theorem normalize_one : normalize δ 1=1⊗ₜ 1 := by
  change operators δ 1 (1⊗ₜ 1)=_; simp
/--
@isnad1 id=eq.0h6v.s10.7715e67f2439 from=translated src=- shape=285e26bc vocab=083b05a2
-/
@[simp] theorem normalize_atom_mul (s : Sum α β) (p : A R (Sum α β)) :
    normalize δ (atom s*p)=op δ s (normalize δ p) := by
  change operators δ (atom s*p) (1⊗ₜ 1)=_
  rw [map_mul,Module.End.mul_apply]
  simp only [operators,lift_atom]
  rfl

variable {U : Type*} [Ring U] [Algebra R U]
def interpret (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U) : V (R:=R) (α:=α) (β:=β) →ₗ[R] U :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun q => f p*g q
          map_add' := by intro q r; simp [mul_add]
          map_smul' := by intro c q; simp }
      map_add' := by intro p r; ext q; simp [add_mul]
      map_smul' := by intro c p; ext q; simp }
/--
@isnad1 id=eq.0h8v.s9.7baafb9c1544 from=translated src=- shape=248cffd8 vocab=8bf7bae1
-/
@[simp] theorem interpret_tmul (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
    (p : A R α) (q : A R β) : interpret f g (p⊗ₜ q)=f p*g q := rfl

def evaluate (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U) : A R (Sum α β) →ₐ[R] U :=
  lift (Sum.elim (fun a => f (atom a)) (fun b => g (atom b)))

variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
variable (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
include hδ
/--
@isnad1 id=eq.1h9v.s10.6fda8e39acdf from=translated src=- shape=8c1edf2b vocab=b053dba4
-/
theorem commutator (b : β) (p : A R α) :
    g (atom b)*f p-f p*g (atom b)=f (deriv (δ b) p) := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp
  | ha a => simpa using hδ b a
  | hadd p q hp hq => simp only [map_add,mul_add,add_mul]; rw [← hp,← hq]; abel
  | hs r p hp => simp only [map_smul,mul_smul_comm,smul_mul_assoc,← smul_sub,hp]
  | hm p q hp hq =>
    rw [AssociativeElimination.deriv_mul,map_add,map_mul,map_mul,map_mul,← hp,← hq]
    noncomm_ring

/--
@isnad1 id=eq.1h9v.s11.1f33f974e8b5 from=translated src=- shape=c53d15b4 vocab=c4e3c9e3
-/
theorem interpret_op (s : Sum α β) (z : V (R:=R) (α:=α) (β:=β)) :
    interpret f g (op δ s z)=evaluate f g (atom s)*interpret f g z := by
  have h : (interpret f g).comp (op δ s)=
      (Algebra.lmul R U (evaluate f g (atom s))).comp (interpret f g) := by
    apply TensorProduct.ext'
    intro p q
    cases s with
    | inl a => simp [op,evaluate,mul_assoc]
    | inr b =>
      simp only [LinearMap.comp_apply,op,Sum.elim_inr,baseOp_tmul,map_add,interpret_tmul,
        evaluate,lift_atom,map_mul]
      change f (deriv (δ b) p)*g q+f p*(g (atom b)*g q)=g (atom b)*(f p*g q)
      rw [← commutator δ f g hδ b p]
      noncomm_ring
  exact LinearMap.congr_fun h z

/--
@isnad1 id=eq.1h9v.s11.656fb2af961d from=translated src=- shape=9699b900 vocab=47f4ba2c
-/
theorem interpret_operators (p : A R (Sum α β)) (z : V (R:=R) (α:=α) (β:=β)) :
    interpret f g (operators δ p z)=evaluate f g p*interpret f g z := by
  induction p using QuadraticAlphabet.algebra_induction generalizing z with
  | h1 => simp
  | ha s => simpa [operators] using interpret_op δ f g hδ s z
  | hadd p q hp hq => simp [hp,hq,add_mul]
  | hs r p hp => simp [hp]
  | hm p q hp hq => simp only [map_mul,Module.End.mul_apply,hp,hq,mul_assoc]

/--
@isnad1 id=eq.1h8v.s10.dcf62991bff7 from=translated src=- shape=b24960c9 vocab=ff6ce16e
-/
theorem interpret_normalize (p : A R (Sum α β)) :
    interpret f g (normalize δ p)=evaluate f g p := by
  change interpret f g (operators δ p (1⊗ₜ 1))=_
  rw [interpret_operators δ f g hδ,interpret_tmul,map_one,map_one,mul_one,mul_one]

omit hδ
def fiberIn : A R α →ₐ[R] A R (Sum α β) := lift (fun a => atom (.inl a))
def baseIn : A R β →ₐ[R] A R (Sum α β) := lift (fun b => atom (.inr b))
/--
@isnad1 id=eq.0h4v.s11.329ac26a024e from=translated src=- shape=e9cbbc95 vocab=506721b1
-/
theorem operators_fiber : (operators δ).comp fiberIn=
    (Module.End.rTensorAlgHom R (A R α) (A R β)).comp leftMul := by
  apply hom_ext
  intro a
  simp only [AlgHom.comp_apply,fiberIn,lift_atom,operators]
  rfl

/--
@isnad1 id=eq.0h6v.s11.055c90da101a from=translated src=- shape=478c4a8d vocab=1564f6da
-/
theorem operators_base_one (q b : A R β) :
    operators δ (baseIn q) ((1 : A R α)⊗ₜ b)=1⊗ₜ (q*b) := by
  induction q using QuadraticAlphabet.algebra_induction generalizing b with
  | h1 => simp
  | ha a =>
    simp only [baseIn,lift_atom,operators,op,Sum.elim_inr,baseOp_tmul,AssociativeElimination.deriv_one,
      TensorProduct.zero_tmul,zero_add]
  | hadd p q hp hq => simp [hp,hq,add_mul,TensorProduct.tmul_add]
  | hs r p hp => simp [hp,TensorProduct.tmul_smul]
  | hm p q hp hq => simp only [map_mul,Module.End.mul_apply,hq,hp,mul_assoc]

/--
@isnad1 id=eq.0h6v.s10.ed16dcbce4e4 from=translated src=- shape=cc229f30 vocab=6e293c55
-/
theorem normalize_product (p : A R α) (q : A R β) :
    normalize δ (fiberIn p*baseIn q)=p⊗ₜ q := by
  change operators δ (fiberIn p*baseIn q) (1⊗ₜ (1 : A R β))=_
  rw [map_mul,Module.End.mul_apply,operators_base_one,mul_one]
  have h := AlgHom.congr_fun (operators_fiber δ) p
  simp only [AlgHom.comp_apply] at h
  rw [h]
  change (p*1)⊗ₜ q=p⊗ₜ q
  rw [mul_one]
end PolynomialOrdering

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
def word (w : FreeMonoid α) : A R α := MonoidAlgebra.single w 1
/--
@isnad1 id=eq.0h2v.s6.63de3f318963 from=translated src=- shape=8084807c vocab=74e501ef
-/
@[simp] theorem word_one : word (1 : FreeMonoid α)=(1 : A R α) := rfl
/--
@isnad1 id=eq.0h3v.s4.49114fd9cd63 from=translated src=- shape=ac71f63b vocab=28bafbfc
-/
@[simp] theorem word_of (a : α) : word (FreeMonoid.of a)=(atom a : A R α) := rfl
/--
@isnad1 id=eq.0h4v.s6.08365a1becea from=translated src=- shape=f60ddac9 vocab=61747cba
-/
@[simp] theorem word_mul (u v : FreeMonoid α) : word (R:=R) (u*v)=word u*word v := by
  simp [word,MonoidAlgebra.single_mul_single]
def space (P : FreeMonoid α → Prop) : Submodule R (A R α) :=
  Submodule.span R {p | ∃ w,P w ∧ p=word w}
/--
@isnad1 id=mem.0h5v.s7.7a60e98044c0 from=translated src=- shape=437d1cbf vocab=f6ebbf8d
-/
theorem word_mem {P : FreeMonoid α → Prop} (w : FreeMonoid α) (hw : P w) : word (R:=R) w∈space P :=
  Submodule.subset_span ⟨w,hw,rfl⟩
/--
@isnad1 id=le.0h5v.s7.12d6801f5e77 from=translated src=- shape=3fa5d7c1 vocab=2a3af67b
-/
theorem space_mono {P Q : FreeMonoid α → Prop} (h : ∀ w,P w → Q w) :
    space (R:=R) P ≤ space Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,hw,rfl⟩
  exact word_mem w (h w hw)
/--
@isnad1 id=eq.2h5v.s7.6904325112d8 from=translated src=- shape=efcab9d5 vocab=8a2e535a
-/
theorem coeff_support {P : FreeMonoid α → Prop} {p : A R α} (hp : p∈space P)
    (w : FreeMonoid α) (hw : ¬P w) : p.coeff w=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨v,hv,rfl⟩ := hp
    have hne : v≠w := fun h => hw (h ▸ hv)
    simp [word,hne]
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul c p _ hp => simp [hp]
/--
@isnad1 id=mem.0h5v.s7.bcbf3c7c3cb5 from=translated src=- shape=a007145d vocab=8a2e535a
-/
theorem mem_space {P : FreeMonoid α → Prop} {p : A R α}
    (h : ∀ w,p.coeff w≠0 → P w) : p∈space P := by
  classical
  rw [← MonoidAlgebra.sum_coeff_single p]
  apply Submodule.sum_mem
  intro w hw
  have hp := h w (Finsupp.mem_support_iff.mp hw)
  have he : MonoidAlgebra.single w (p.coeff w)=p.coeff w • word (R:=R) w := by simp [word]
  rw [he]
  exact (space P).smul_mem _ (word_mem w hp)
/--
@isnad1 id=iff.0h4v.s7.635ea65ef549 from=translated src=- shape=090c3a95 vocab=8a2e535a
-/
theorem mem_space_iff {P : FreeMonoid α → Prop} {p : A R α} :
    p∈space P ↔ ∀ w,p.coeff w≠0 → P w := by
  constructor
  · intro hp w hw
    by_contra h
    exact hw (coeff_support hp w h)
  · exact mem_space

/--
@isnad1 id=mem.2h8v.s9.556b0e1b1278 from=translated src=- shape=5904a808 vocab=ef784e65
-/
theorem mul_mem {P Q T : FreeMonoid α → Prop} (h : ∀ u v,P u → Q v → T (u*v))
    {p q : A R α} (hp : p∈space P) (hq : q∈space Q) : p*q∈space T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq => obtain ⟨v,hv,rfl⟩ := hq; rw [← word_mul]; exact word_mem _ (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (space T).add_mem hp hq
    | smul c p _ hp => simpa only [mul_smul_comm] using (space T).smul_mem c hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using (space T).add_mem hp hq
  | smul c p _ hp => simpa only [smul_mul_assoc] using (space T).smul_mem c hp

def project (P : FreeMonoid α → Prop) [DecidablePred P] : A R α →ₗ[R] A R α :=
  (Finsupp.linearCombination R (fun w => if P w then word w else 0)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
/--
@isnad1 id=eq.0h4v.s8.4811e16ceadb from=translated src=- shape=6eeec79d vocab=ee15cabd
-/
@[simp] theorem project_word (P : FreeMonoid α → Prop) [DecidablePred P] (w : FreeMonoid α) :
    project (R:=R) P (word w)=if P w then word w else 0 := by
  change Finsupp.linearCombination R (fun monoidWord => if P monoidWord then word monoidWord else 0) (Finsupp.single w 1) = _; simp
/--
@isnad1 id=eq.0h5v.s8.51d62ab666b4 from=translated src=- shape=6d2d7d18 vocab=3df46221
-/
theorem project_coeff (P : FreeMonoid α → Prop) [DecidablePred P] (p : A R α) (w : FreeMonoid α) :
    (project P p).coeff w=if P w then p.coeff w else 0 := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change (project P (word v)).coeff w=_
    rw [project_word]
    by_cases hv : P v <;> by_cases hw : P w <;> simp [hv,hw,word]
    · apply Finsupp.single_eq_of_ne
      intro h
      exact hw (h ▸ hv)
    · symm
      apply Finsupp.single_eq_of_ne
      intro h
      exact hv (h ▸ hw)
  | add p q hp hq => simp only [map_add,MonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]; split_ifs <;> simp
  | smul c p hp => simp only [map_smul,MonoidAlgebra.coeff_smul,Finsupp.smul_apply,hp]; split_ifs <;> simp

/--
@isnad1 id=mem.0h4v.s8.6db1f331e4e7 from=translated src=- shape=04192c71 vocab=c51c77d4
-/
theorem project_mem (P : FreeMonoid α → Prop) [DecidablePred P] (p : A R α) : project P p∈space P := by
  apply mem_space
  intro w hw
  by_contra hn
  exact hw (by rw [project_coeff,ite_eq_right hn])
/--
@isnad1 id=eq.1h4v.s8.cc5d393c4fd1 from=translated src=- shape=30e5bce2 vocab=c51c77d4
-/
theorem project_eq_self {P : FreeMonoid α → Prop} [DecidablePred P] {p : A R α}
    (hp : p∈space P) : project P p=p := by
  ext w
  rw [project_coeff]
  split_ifs with h
  · rfl
  · exact (coeff_support hp w h).symm
/--
@isnad1 id=eq.2h5v.s8.fcc87700294d from=translated src=- shape=8ac73162 vocab=c51c77d4
-/
theorem project_eq_zero {P Q : FreeMonoid α → Prop} [DecidablePred Q] {p : A R α}
    (hp : p∈space P) (h : ∀ w,P w → ¬Q w) : project Q p=0 := by
  ext w
  rw [project_coeff]
  split_ifs with hw
  · exact coeff_support hp w (fun hp => h w hp hw)
  · rfl

def degree (wt : α → ℕ) (w : FreeMonoid α) : ℕ := (w.toList.map wt).sum
/--
@isnad1 id=eq.0h2v.s5.fee566712787 from=translated src=- shape=66d28c8b vocab=cbb3bb71
-/
@[simp] theorem degree_one (wt : α → ℕ) : degree wt 1=0 := rfl
/--
@isnad1 id=eq.0h3v.s4.239ab55e6d2a from=translated src=- shape=36259ed9 vocab=ec7b43e7
-/
@[simp] theorem degree_of (wt : α → ℕ) (a : α) : degree wt (FreeMonoid.of a)=wt a := by simp [degree]
/--
@isnad1 id=eq.0h4v.s5.a755c8e06713 from=translated src=- shape=5ca19ca0 vocab=8f071530
-/
@[simp] theorem degree_mul (wt : α → ℕ) (u v : FreeMonoid α) : degree wt (u*v)=degree wt u+degree wt v := by
  simp [degree]
def homogeneous (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w=n)
def above (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => n≤degree wt w)
def below (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w≤n)
def piece (wt : α → ℕ) (n : ℕ) : A R α →ₗ[R] A R α := project (fun w => degree wt w=n)
/--
@isnad1 id=mem.2h7v.s8.a07ad7a9bbb0 from=translated src=- shape=012b7072 vocab=18dd9aef
-/
theorem homogeneous_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt n) (hq : q∈homogeneous wt m) : p*q∈homogeneous wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq
/--
@isnad1 id=mem.2h7v.s8.647230ce18c0 from=translated src=- shape=012b7072 vocab=ab82ead8
-/
theorem above_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈above wt n) (hq : q∈above wt m) : p*q∈above wt (n+m) :=
  mul_mem (by intros; simp_all; omega) hp hq
/--
@isnad1 id=mem.2h7v.s8.a0e27aa65b35 from=translated src=- shape=012b7072 vocab=f4041436
-/
theorem below_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈below wt n) (hq : q∈below wt m) : p*q∈below wt (n+m) :=
  mul_mem (by intros; simp_all; omega) hp hq
/--
@isnad1 id=mem.2h7v.s9.4ddc5f8f9770 from=translated src=- shape=b21e0636 vocab=f27e3c48
-/
theorem map_space {M : Type*} [AddCommGroup M] [Module R M]
    {P : FreeMonoid α → Prop} (f : A R α →ₗ[R] M) (T : Submodule R M)
    (h : ∀ w,P w → f (word w)∈T) {p : A R α} (hp : p∈space P) : f p∈T := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,hw,rfl⟩ := hp; exact h w hw
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using T.add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using T.smul_mem c hp

/--
@isnad1 id=mem.2h7v.s9.eb431a702e6b from=translated src=- shape=d37c9520 vocab=99a45117
-/
theorem deriv_homogeneous {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈homogeneous wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈homogeneous wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈homogeneous wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := homogeneous_mul (hf a) (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w))
      have h2 := homogeneous_mul (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a)) ih
      simp only [degree_mul,degree_of]
      apply (homogeneous wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  exact map_space (deriv f) _ (by intro w hw'; simpa only [hw'] using hw w) hp

/--
@isnad1 id=mem.1h5v.s8.776529eb1676 from=translated src=- shape=0e2d8533 vocab=b57af6fc
-/
theorem homogeneous_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈above wt n := space_mono (by intros; omega) hp
/--
@isnad1 id=mem.1h5v.s8.f58b84f23513 from=translated src=- shape=0e2d8533 vocab=afa41293
-/
theorem homogeneous_below {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈below wt n := space_mono (by intros; omega) hp

/--
@isnad1 id=mem.2h7v.s9.83c37568ae11 from=translated src=- shape=d37c9520 vocab=6d056b37
-/
theorem deriv_above {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈above wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : deriv f p∈above wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈above wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := above_mul (hf a) (homogeneous_above (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w)))
      have h2 := above_mul (homogeneous_above (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a))) ih
      simp only [degree_mul,degree_of]
      apply (above wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  apply map_space (deriv f) _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; omega) (hw w)

/--
@isnad1 id=mem.2h7v.s9.da400ef92db8 from=translated src=- shape=d37c9520 vocab=0f48417a
-/
theorem deriv_below {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈below wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈below wt n) : deriv f p∈below wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈below wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := below_mul (hf a) (homogeneous_below (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w)))
      have h2 := below_mul (homogeneous_below (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a))) ih
      simp only [degree_mul,degree_of]
      apply (below wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  apply map_space (deriv f) _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; omega) (hw w)

/--
@isnad1 id=eq.0h5v.s9.5d4a73c22c49 from=translated src=- shape=1561dff1 vocab=7f6ab34e
-/
theorem deriv_sub (f g : α → A R α) (p : A R α) : deriv (fun a => f a-g a) p=deriv f p-deriv g p := by
  have hw (w : FreeMonoid α) : deriv (fun a => f a-g a) (word w)=deriv f (word w)-deriv g (word w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      simp only [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom,ih,mul_sub,sub_mul]
      abel
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simp only [map_add,hp,hq]; abel
  | smul c p hp => simp only [map_smul,hp,smul_sub]
end WordGrading

namespace TriangularWords
open AssociativeElimination WordGrading
variable {R α V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
def action (f : α → Module.End R V) : A R α →ₐ[R] Module.End R V := lift f
/--
@isnad1 id=eq.0h5v.s8.7b62d4b62a35 from=translated src=- shape=876b6277 vocab=6b86492d
-/
@[simp] theorem action_atom (f : α → Module.End R V) (a : α) : action f (atom a)=f a := lift_atom f a

def apply (f : α → Module.End R V) (v : V) : A R α →ₗ[R] V :=
  (LinearMap.applyₗ v).comp (action f).toLinearMap
/--
@isnad1 id=eq.0h5v.s7.e1af324e7032 from=translated src=- shape=0d25b432 vocab=a3dc9394
-/
@[simp] theorem apply_word_one (f : α → Module.End R V) (v : V) : apply f v (word 1)=v := by simp [apply]
/--
@isnad1 id=eq.0h7v.s8.f445b40471f4 from=translated src=- shape=2b2a21b6 vocab=b805d516
-/
@[simp] theorem apply_word_cons (f : α → Module.End R V) (v : V) (a : α) (w : FreeMonoid α) :
    apply f v (word (FreeMonoid.of a*w))=f a (apply f v (word w)) := by
  simp [apply,Module.End.mul_apply]

/--
@isnad1 id=and.5h11v.s10.0910b7906c6a from=translated src=- shape=4c41f425 vocab=20d93f0e
-/
theorem comparison (wt : α → ℕ) (H E : ℕ → Submodule R V)
    (f g : α → Module.End R V) (v : V) (hv : v∈H 0)
    (hg : ∀ a n z,z∈H n → g a z∈H (wt a+n))
    (hf : ∀ a n z,z∈E n → f a z∈E (wt a+n))
    (hfg : ∀ a n z,z∈H n → f a z-g a z∈E (wt a+n))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wt n) :
    apply g v p∈H n ∧ apply f v p-apply g v p∈E n := by
  have hw (w : FreeMonoid α) : apply g v (word w)∈H (degree wt w) ∧
      apply f v (word w)-apply g v (word w)∈E (degree wt w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simpa [apply] using And.intro hv ((E 0).zero_mem)
    | of_mul a w ih =>
      simp only [degree_mul,degree_of,apply_word_cons]
      refine ⟨hg a _ _ ih.1,?_⟩
      have h1 := hf a _ _ ih.2
      have h2 := hfg a _ _ ih.1
      have he : f a (apply f v (word w))-g a (apply g v (word w))=
          f a (apply f v (word w)-apply g v (word w))+
          (f a (apply g v (word w))-g a (apply g v (word w))) := by rw [map_sub]; abel
      rw [he]
      exact (E _).add_mem h1 h2
  constructor
  · exact map_space (apply g v) _ (by intro w hw'; simpa only [hw'] using (hw w).1) hp
  · exact map_space (apply f v-apply g v) _ (by intro w hw'; simpa only [hw',LinearMap.sub_apply] using (hw w).2) hp
end TriangularWords
namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
def strictlyBelow (wt : α → ℕ) (n : ℕ) := space (R:=R) (fun w => degree wt w<n)
/--
@isnad1 id=mem.2h7v.s8.d9819cec7a48 from=translated src=- shape=810064f4 vocab=379e2238
-/
theorem homogeneous_mul_strictlyBelow {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt n) (hq : q∈strictlyBelow wt m) : p*q∈strictlyBelow wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq
/--
@isnad1 id=mem.2h7v.s8.df05f90785fb from=translated src=- shape=3e58bd63 vocab=379e2238
-/
theorem strictlyBelow_mul_homogeneous {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈strictlyBelow wt n) (hq : q∈homogeneous wt m) : p*q∈strictlyBelow wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq

/--
@isnad1 id=mem.2h7v.s9.0f42e7e394f4 from=translated src=- shape=1c84e489 vocab=3cd32326
-/
theorem deriv_strictlyBelow {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈strictlyBelow wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈strictlyBelow wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈strictlyBelow wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := strictlyBelow_mul_homogeneous (hf a) (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w))
      have h2 := homogeneous_mul_strictlyBelow (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a)) ih
      simp only [degree_mul,degree_of]
      apply (strictlyBelow wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  exact map_space (deriv f) _ (by intro w hw'; simpa only [hw'] using hw w) hp
end WordGrading
namespace TensorGrading
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
def space (P : FreeMonoid α → FreeMonoid β → Prop) : Submodule R (V (R:=R) (α:=α) (β:=β)) :=
  Submodule.span R {z | ∃ u v,P u v ∧ z=word u⊗ₜ word v}
/--
@isnad1 id=mem.0h7v.s9.f217943e8637 from=translated src=- shape=34c09146 vocab=e28820ef
-/
theorem tmul_word_mem {P : FreeMonoid α → FreeMonoid β → Prop} (u : FreeMonoid α) (v : FreeMonoid β)
    (h : P u v) : word (R:=R) u⊗ₜ word (R:=R) v∈space P :=
  Submodule.subset_span ⟨u,v,h,rfl⟩
/--
@isnad1 id=le.0h6v.s9.2c64df565ac4 from=translated src=- shape=f31ad1f3 vocab=374966a2
-/
theorem space_mono {P Q : FreeMonoid α → FreeMonoid β → Prop} (h : ∀ u v,P u v → Q u v) :
    space (R:=R) P ≤ space Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u,v,huv,rfl⟩
  exact tmul_word_mem u v (h u v huv)
/--
@isnad1 id=mem.2h9v.s9.f27f0d9dc9c7 from=translated src=- shape=aacebe9d vocab=6a784268
-/
theorem tmul_mem {P : FreeMonoid α → Prop} {Q : FreeMonoid β → Prop}
    {T : FreeMonoid α → FreeMonoid β → Prop} (h : ∀ u v,P u → Q v → T u v)
    {p : A R α} {q : A R β} (hp : p∈WordGrading.space P) (hq : q∈WordGrading.space Q) :
    p⊗ₜ q∈space T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq => obtain ⟨v,hv,rfl⟩ := hq; exact tmul_word_mem _ _ (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [TensorProduct.tmul_add] using (space T).add_mem hp hq
    | smul c p _ hp => simpa only [TensorProduct.tmul_smul] using (space T).smul_mem c hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [TensorProduct.add_tmul] using (space T).add_mem hp hq
  | smul c p _ hp => simpa only [TensorProduct.smul_tmul'] using (space T).smul_mem c hp

def homogeneous (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v=n)
def above (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => n≤degree wa u+degree wb v)
def below (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v≤n)
def strictlyBelow (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v<n)

/--
@isnad1 id=mem.2h8v.s10.8a3a7da324ee from=translated src=- shape=625f008e vocab=7fa1ec43
-/
theorem map_space {M : Type*} [AddCommGroup M] [Module R M] (f : V (R:=R) (α:=α) (β:=β) →ₗ[R] M)
    {P : FreeMonoid α → FreeMonoid β → Prop} (Q : Submodule R M)
    (hf : ∀ u v,P u v → f (word u⊗ₜ word v)∈Q) {p : V (R:=R) (α:=α) (β:=β)} (hp : p∈space P) : f p∈Q := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨u,v,h,rfl⟩ := hp; exact hf u v h
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using Q.add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using Q.smul_mem c hp

/--
@isnad1 id=mem.2h9v.s9.ea46412e6ff0 from=translated src=- shape=67dde532 vocab=df52b772
-/
theorem homo_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.homogeneous wa n) (hq : q∈WordGrading.homogeneous wb m) :
    p⊗ₜ q∈homogeneous wa wb (n+m) := tmul_mem (by intros; simp_all) hp hq
/--
@isnad1 id=mem.2h9v.s9.91efa8cdcbe9 from=translated src=- shape=67dde532 vocab=41806abb
-/
theorem above_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.above wa n) (hq : q∈WordGrading.above wb m) :
    p⊗ₜ q∈above wa wb (n+m) := tmul_mem (by intros; omega) hp hq
/--
@isnad1 id=mem.2h9v.s9.18b3a3536bc8 from=translated src=- shape=67dde532 vocab=24d1b4b0
-/
theorem below_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.below wa n) (hq : q∈WordGrading.below wb m) :
    p⊗ₜ q∈below wa wb (n+m) := tmul_mem (by intros; omega) hp hq
/--
@isnad1 id=mem.2h9v.s9.13302ae5ad28 from=translated src=- shape=737349cd vocab=0e9f737e
-/
theorem strict_homo_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.strictlyBelow wa n) (hq : q∈WordGrading.homogeneous wb m) :
    p⊗ₜ q∈strictlyBelow wa wb (n+m) := tmul_mem (by intros; omega) hp hq

variable {wa : α → ℕ} {wb : β → ℕ} {δ : β → α → A R α}
/--
@isnad1 id=mem.2h9v.s10.80d5808a5ceb from=translated src=- shape=e1cb61f8 vocab=0abb4719
-/
theorem op_homogeneous (hδ : ∀ b a,δ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z∈homogeneous wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.homogeneous wa (degree wa u) := word_mem u rfl
  have hv : word (R:=R) v∈WordGrading.homogeneous wb (degree wb v) := word_mem v rfl
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.homogeneous wa (wa a) := word_mem (FreeMonoid.of a) (degree_of wa a)
    have h := homo_tmul (WordGrading.homogeneous_mul ha hu) hv
    simpa only [PolynomialOrdering.op,Sum.elim_inl,PolynomialOrdering.fiberOp_tmul,← huv,Nat.add_assoc] using h
  | inr b =>
    have hd := WordGrading.deriv_homogeneous (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.homogeneous wb (wb b) := word_mem (FreeMonoid.of b) (degree_of wb b)
    have h1 := homo_tmul hd hv
    have h2 := homo_tmul hu (WordGrading.homogeneous_mul hb hv)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈homogeneous wa wb (wb b+n)
    apply (homogeneous wa wb (wb b+n)).add_mem
    · simpa only [← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · simpa only [← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

/--
@isnad1 id=mem.2h9v.s10.4ee89f1e2dc7 from=translated src=- shape=e1cb61f8 vocab=a99c5946
-/
theorem op_above (hδ : ∀ b a,δ b a∈WordGrading.above wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈above wa wb n) :
    PolynomialOrdering.op δ s z∈above wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.above wa (degree wa u) := word_mem u (by rfl)
  have hv : word (R:=R) v∈WordGrading.above wb (degree wb v) := word_mem v (by rfl)
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.above wa (wa a) := word_mem (FreeMonoid.of a) (by simp)
    have h := above_tmul (WordGrading.above_mul ha hu) hv
    have hm : above (R:=R) wa wb (wa a+degree wa u+degree wb v) ≤ above wa wb (wa a+n) :=
      space_mono (by intro u' v' hh; change n ≤ degree wa u+degree wb v at huv; omega)
    exact hm h
  | inr b =>
    have hd := WordGrading.deriv_above (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.above wb (wb b) := word_mem (FreeMonoid.of b) (by simp)
    have h1 := above_tmul hd hv
    have h2 := above_tmul hu (WordGrading.above_mul hb hv)
    have hm : above (R:=R) wa wb (degree wa u+degree wb v+wb b) ≤ above wa wb (wb b+n) :=
      space_mono (by intro u' v' hh; change n ≤ degree wa u+degree wb v at huv; omega)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈above wa wb (wb b+n)
    apply ( above wa wb (wb b+n)).add_mem
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

/--
@isnad1 id=mem.2h9v.s10.02ac212919c5 from=translated src=- shape=e1cb61f8 vocab=5c0e662d
-/
theorem op_below (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈below wa wb n) :
    PolynomialOrdering.op δ s z∈below wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.below wa (degree wa u) := word_mem u (by rfl)
  have hv : word (R:=R) v∈WordGrading.below wb (degree wb v) := word_mem v (by rfl)
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.below wa (wa a) := word_mem (FreeMonoid.of a) (by simp)
    have h := below_tmul (WordGrading.below_mul ha hu) hv
    have hm : below (R:=R) wa wb (wa a+degree wa u+degree wb v) ≤ below wa wb (wa a+n) :=
      space_mono (by intro u' v' hh; change degree wa u+degree wb v ≤ n at huv; omega)
    exact hm h
  | inr b =>
    have hd := WordGrading.deriv_below (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.below wb (wb b) := word_mem (FreeMonoid.of b) (by simp)
    have h1 := below_tmul hd hv
    have h2 := below_tmul hu (WordGrading.below_mul hb hv)
    have hm : below (R:=R) wa wb (degree wa u+degree wb v+wb b) ≤ below wa wb (wb b+n) :=
      space_mono (by intro u' v' hh; change degree wa u+degree wb v ≤ n at huv; omega)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈below wa wb (wb b+n)
    apply ( below wa wb (wb b+n)).add_mem
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

/--
@isnad1 id=mem.2h9v.s10.6877b52e6a91 from=translated src=- shape=e1cb61f8 vocab=755bab93
-/
theorem op_strictlyBelow (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈strictlyBelow wa wb n) :
    PolynomialOrdering.op δ s z∈strictlyBelow wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hh : word (R:=R) u⊗ₜ word (R:=R) v∈below wa wb (degree wa u+degree wb v) := tmul_word_mem u v (by rfl)
  have h := op_below hδ s hh
  have hm : below (R:=R) wa wb (Sum.elim wa wb s+(degree wa u+degree wb v)) ≤
      strictlyBelow wa wb (Sum.elim wa wb s+n) :=
    space_mono (by intro u' v' hh; change degree wa u+degree wb v<n at huv; omega)
  exact hm h

variable {δ₀ : β → α → A R α}
/--
@isnad1 id=eq.0h8v.s11.50aab40a7ee4 from=translated src=- shape=af6adcd2 vocab=8b9f6a7d
-/
theorem op_difference (s : Sum α β) (u : FreeMonoid α) (v : FreeMonoid β) :
    (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) (word u⊗ₜ word v)=
    Sum.elim (fun _ => 0) (fun b => deriv (fun a => δ b a-δ₀ b a) (word u)⊗ₜ word v) s := by
  cases s with
  | inl a => simp [PolynomialOrdering.op]
  | inr b =>
    simp only [PolynomialOrdering.op,Sum.elim_inr,LinearMap.sub_apply,PolynomialOrdering.baseOp_tmul,
      WordGrading.deriv_sub,TensorProduct.sub_tmul]
    abel

/--
@isnad1 id=mem.2h10v.s11.456826199871 from=translated src=- shape=096050ea vocab=4ff0c734
-/
theorem op_difference_above (hδ : ∀ b a,δ b a-δ₀ b a∈WordGrading.above wa (wb b+wa a+1))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z-PolynomialOrdering.op δ₀ s z∈above wa wb (Sum.elim wa wb s+n+1) := by
  apply map_space (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) _ ?_ hz
  intro u v huv
  rw [op_difference]
  cases s with
  | inl a => exact (above wa wb _).zero_mem
  | inr b =>
    have hu : word (R:=R) u∈WordGrading.above wa (degree wa u) := word_mem u (by rfl)
    have hv : word (R:=R) v∈WordGrading.above wb (degree wb v) := word_mem v (by rfl)
    have hd := WordGrading.deriv_above (c:=wb b+1) (f:=fun a => δ b a-δ₀ b a)
      (by intro a; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hδ b a) hu
    have hh := above_tmul hd hv
    simpa only [Sum.elim_inr,← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/--
@isnad1 id=mem.2h10v.s11.2d4ca2f4ce08 from=translated src=- shape=b31e1cd6 vocab=a3b5a5ac
-/
theorem op_difference_below (hδ : ∀ b a,δ b a-δ₀ b a∈WordGrading.strictlyBelow wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z-PolynomialOrdering.op δ₀ s z∈strictlyBelow wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) _ ?_ hz
  intro u v huv
  rw [op_difference]
  cases s with
  | inl a => exact (strictlyBelow wa wb _).zero_mem
  | inr b =>
    have hu : word (R:=R) u∈WordGrading.homogeneous wa (degree wa u) := word_mem u rfl
    have hv : word (R:=R) v∈WordGrading.homogeneous wb (degree wb v) := word_mem v rfl
    have hd := WordGrading.deriv_strictlyBelow (c:=wb b) (f:=fun a => δ b a-δ₀ b a)
      (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hh := strict_homo_tmul hd hv
    simpa only [Sum.elim_inr,← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/--
@isnad1 id=and.4h9v.s11.79b50e31651c from=translated src=- shape=28b331de vocab=44941749
-/
theorem comparison_above (h0 : ∀ b a,δ₀ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈WordGrading.above wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈WordGrading.above wa (wb b+wa a+1))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈WordGrading.homogeneous (Sum.elim wa wb) n) :
    PolynomialOrdering.normalize δ₀ p∈homogeneous wa wb n ∧
    PolynomialOrdering.normalize δ p-PolynomialOrdering.normalize δ₀ p∈above wa wb (n+1) := by
  apply TriangularWords.comparison (Sum.elim wa wb) (homogeneous wa wb) (fun n => above wa wb (n+1))
    (PolynomialOrdering.op δ) (PolynomialOrdering.op δ₀) (1⊗ₜ 1) ?_ ?_ ?_ ?_ hp
  · exact tmul_word_mem 1 1 (by simp)
  · intro a n z hz; exact op_homogeneous h0 a hz
  · intro a n z hz; simpa only [Nat.add_assoc] using op_above hδ a hz
  · intro a n z hz; exact op_difference_above hd a hz

/--
@isnad1 id=and.4h9v.s11.165ac4e7e23a from=translated src=- shape=98b05c6f vocab=10b5a86c
-/
theorem comparison_below (h0 : ∀ b a,δ₀ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈WordGrading.strictlyBelow wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈WordGrading.homogeneous (Sum.elim wa wb) n) :
    PolynomialOrdering.normalize δ₀ p∈homogeneous wa wb n ∧
    PolynomialOrdering.normalize δ p-PolynomialOrdering.normalize δ₀ p∈strictlyBelow wa wb n := by
  apply TriangularWords.comparison (Sum.elim wa wb) (homogeneous wa wb) (strictlyBelow wa wb)
    (PolynomialOrdering.op δ) (PolynomialOrdering.op δ₀) (1⊗ₜ 1) ?_ ?_ ?_ ?_ hp
  · exact tmul_word_mem 1 1 (by simp)
  · intro a n z hz; exact op_homogeneous h0 a hz
  · intro a n z hz; exact op_strictlyBelow hδ a hz
  · intro a n z hz; exact op_difference_below hd a hz
end TensorGrading
namespace CountTables

section
open AssociativeElimination
abbrev K := ZMod 2
abbrev F := Fin 5
abbrev B := Fin 4

def H : A K F := atom 0
def U (i : Fin 2) : A K F := atom ⟨i.val+1,by omega⟩
def V (i : Fin 2) : A K F := atom ⟨i.val+3,by omega⟩
def bracket {R α : Type*} [CommRing R] (p q : A R α) := p*q-q*p
def R' (i : Fin 2) := bracket H (U i)
def Q (i : Fin 2) := bracket (H+V i) (U i)
def W := bracket (V 0) (U 1)+bracket (U 0) (V 1)
def common : B → F → A K F
  | 0,0 => bracket H (V 0)
  | 0,1 => Q 0
  | 0,3 => bracket H (V 0)
  | 1,0 => bracket H (V 1)
  | 1,2 => Q 1
  | 1,4 => bracket H (V 1)
  | 2,1 | 2,2 => bracket (U 0) (U 1)
  | 2,3 | 2,4 => W
  | 3,1 => bracket (U 0) (V 1)
  | 3,2 => bracket (U 1) (V 0)
  | 3,3 | 3,4 => bracket (V 0) (V 1)
  | _,_ => 0
def higher : B → F → A K F
  | 0,0 => bracket (R' 0) (U 0)
  | 0,3 => bracket (bracket (V 0) (U 0)) (U 0)
  | 0,4 => bracket (Q 0) (U 1)
  | 1,0 => bracket (R' 1) (U 1)
  | 1,4 => bracket (bracket (V 1) (U 1)) (U 1)
  | 1,3 => bracket (Q 1) (U 0)
  | 3,0 => bracket H (bracket (U 0) (U 1))
  | 3,3 => bracket W (U 0)+bracket (U 0) (R' 1)
  | 3,4 => bracket W (U 1)+bracket (U 1) (R' 0)
  | _,_ => 0
def lower : B → F → A K F
  | 2,3 | 2,4 => bracket (V 0) (V 1)
  | _,_ => 0
def source (b : B) (a : F) := common b a+higher b a
def target (b : B) (a : F) := common b a+lower b a

def fiberCount : F → ℕ | 1 | 2 => 1 | _ => 0
def baseCount : B → ℕ | 2 => 1 | _ => 0

open WordGrading

/--
@isnad1 id=mem.2h4v.s9.4954d634d20d from=translated src=- shape=d4bec97f vocab=a2674909
-/
theorem bracket_homo {n m : ℕ} {p q : A K F}
    (hp : p∈homogeneous fiberCount n) (hq : q∈homogeneous fiberCount m) :
    bracket p q∈homogeneous fiberCount (n+m) := by
  apply (homogeneous fiberCount (n+m)).sub_mem (homogeneous_mul hp hq)
  simpa only [Nat.add_comm] using homogeneous_mul hq hp

/--
@isnad1 id=mem.0h0v.s7.6b32f5062e57 from=translated src=- shape=d8bcab5c vocab=755708ba
-/
theorem H_homo : H∈homogeneous fiberCount 0 := word_mem (FreeMonoid.of 0) rfl
/--
@isnad1 id=mem.0h1v.s8.3f1d3e57cfa0 from=translated src=- shape=a0530344 vocab=2715af6e
-/
theorem U_homo (i : Fin 2) : U i∈homogeneous fiberCount 1 := by
  apply word_mem
  fin_cases i <;> rfl
/--
@isnad1 id=mem.0h1v.s8.d2f02eff3e5b from=translated src=- shape=a0530344 vocab=4d40f3b7
-/
theorem V_homo (i : Fin 2) : V i∈homogeneous fiberCount 0 := by
  apply word_mem
  fin_cases i <;> rfl
/--
@isnad1 id=mem.0h1v.s8.217f2648e0f7 from=translated src=- shape=a0530344 vocab=7736e9ba
-/
theorem R_homo (i : Fin 2) : R' i∈homogeneous fiberCount 1 := by
  have h := bracket_homo H_homo (U_homo i)
  exact h
/--
@isnad1 id=mem.0h1v.s8.83e687933475 from=translated src=- shape=a0530344 vocab=836a99da
-/
theorem Q_homo (i : Fin 2) : Q i∈homogeneous fiberCount 1 :=
  by
    have h := bracket_homo ((homogeneous fiberCount 0).add_mem H_homo (V_homo i)) (U_homo i)
    exact h
/--
@isnad1 id=mem.0h0v.s7.9a1a6ecaa694 from=translated src=- shape=d8bcab5c vocab=197dd224
-/
theorem W_homo : W∈homogeneous fiberCount 1 :=
  by
    have h1 := bracket_homo (V_homo 0) (U_homo 1)
    have h2 := bracket_homo (U_homo 0) (V_homo 1)
    exact (homogeneous fiberCount 1).add_mem h1 h2

/--
@isnad1 id=mem.0h1v.s8.cec641d2c1d3 from=translated src=- shape=96a02aaa vocab=3411ef0a
-/
theorem common_homo_0 (a : F) : common 0 a∈homogeneous fiberCount (baseCount 0+fiberCount a) := by
  fin_cases a
  · have h := bracket_homo H_homo (V_homo 0)
    exact h
  · have h := Q_homo 0
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo H_homo (V_homo 0)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
/--
@isnad1 id=mem.0h1v.s8.94aa7de2a98b from=translated src=- shape=96a02aaa vocab=3411ef0a
-/
theorem common_homo_1 (a : F) : common 1 a∈homogeneous fiberCount (baseCount 1+fiberCount a) := by
  fin_cases a
  · have h := bracket_homo H_homo (V_homo 1)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := Q_homo 1
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo H_homo (V_homo 1)
    exact h
/--
@isnad1 id=mem.0h1v.s8.43b15d61a627 from=translated src=- shape=96a02aaa vocab=3411ef0a
-/
theorem common_homo_2 (a : F) : common 2 a∈homogeneous fiberCount (baseCount 2+fiberCount a) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (U_homo 0) (U_homo 1)
    exact h
  · have h := bracket_homo (U_homo 0) (U_homo 1)
    exact h
  · have h := W_homo
    exact h
  · have h := W_homo
    exact h
/--
@isnad1 id=mem.0h1v.s8.f53c664beb50 from=translated src=- shape=96a02aaa vocab=3411ef0a
-/
theorem common_homo_3 (a : F) : common 3 a∈homogeneous fiberCount (baseCount 3+fiberCount a) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (U_homo 0) (V_homo 1)
    exact h
  · have h := bracket_homo (U_homo 1) (V_homo 0)
    exact h
  · have h := bracket_homo (V_homo 0) (V_homo 1)
    exact h
  · have h := bracket_homo (V_homo 0) (V_homo 1)
    exact h
/--
@isnad1 id=mem.0h2v.s8.bad77befd1d7 from=translated src=- shape=ac841708 vocab=3411ef0a
-/
theorem common_homo (b : B) (a : F) : common b a∈homogeneous fiberCount (baseCount b+fiberCount a) := by
  fin_cases b
  · exact common_homo_0 a
  · exact common_homo_1 a
  · exact common_homo_2 a
  · exact common_homo_3 a
/--
@isnad1 id=mem.0h1v.s8.539ae14c9c1f from=translated src=- shape=6dda29e1 vocab=8f30fa0b
-/
theorem higher_homo_0 (a : F) : higher 0 a∈homogeneous fiberCount (baseCount 0+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo (R_homo 0) (U_homo 0)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (bracket_homo (V_homo 0) (U_homo 0)) (U_homo 0)
    exact h
  · have h := bracket_homo (Q_homo 0) (U_homo 1)
    exact h
/--
@isnad1 id=mem.0h1v.s8.3de7fb36ad6c from=translated src=- shape=6dda29e1 vocab=8f30fa0b
-/
theorem higher_homo_1 (a : F) : higher 1 a∈homogeneous fiberCount (baseCount 1+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo (R_homo 1) (U_homo 1)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (Q_homo 1) (U_homo 0)
    exact h
  · have h := bracket_homo (bracket_homo (V_homo 1) (U_homo 1)) (U_homo 1)
    exact h
/--
@isnad1 id=mem.0h1v.s8.feb299ebc48e from=translated src=- shape=6dda29e1 vocab=8f30fa0b
-/
theorem higher_homo_2 (a : F) : higher 2 a∈homogeneous fiberCount (baseCount 2+fiberCount a+2) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
/--
@isnad1 id=mem.0h1v.s8.65d6666536d7 from=translated src=- shape=6dda29e1 vocab=8f30fa0b
-/
theorem higher_homo_3 (a : F) : higher 3 a∈homogeneous fiberCount (baseCount 3+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo H_homo (bracket_homo (U_homo 0) (U_homo 1))
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h1 := bracket_homo W_homo (U_homo 0)
    have h2 := bracket_homo (U_homo 0) (R_homo 1)
    exact (homogeneous fiberCount 2).add_mem h1 h2
  · have h1 := bracket_homo W_homo (U_homo 1)
    have h2 := bracket_homo (U_homo 1) (R_homo 0)
    exact (homogeneous fiberCount 2).add_mem h1 h2
/--
@isnad1 id=mem.0h2v.s8.fac8f66033c1 from=translated src=- shape=da1b7501 vocab=8f30fa0b
-/
theorem higher_homo (b : B) (a : F) : higher b a∈homogeneous fiberCount (baseCount b+fiberCount a+2) := by
  fin_cases b
  · exact higher_homo_0 a
  · exact higher_homo_1 a
  · exact higher_homo_2 a
  · exact higher_homo_3 a

/--
@isnad1 id=mem.0h2v.s8.ad268a5ad761 from=translated src=- shape=ac841708 vocab=c8ff3ce8
-/
theorem lower_strict (b : B) (a : F) : lower b a∈strictlyBelow fiberCount (baseCount b+fiberCount a) := by
  fin_cases b <;> fin_cases a <;> simp only [lower,baseCount,fiberCount,Nat.reduceAdd]
  all_goals first
    | exact (strictlyBelow fiberCount _).zero_mem
    | exact (space_mono (P:=fun w => degree fiberCount w=0) (Q:=fun w => degree fiberCount w<1)
        (by intros; omega)) (bracket_homo (n:=0) (m:=0) (V_homo 0) (V_homo 1))

/--
@isnad1 id=mem.0h2v.s8.d6bc6c5dd6a9 from=translated src=- shape=ac841708 vocab=254a9c90
-/
theorem source_above (b : B) (a : F) : source b a∈above fiberCount (baseCount b+fiberCount a) := by
  apply (above fiberCount _).add_mem
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a) (by intros; omega)
    exact common_homo b a
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a+2) (by intros; omega)
    exact higher_homo b a

/--
@isnad1 id=mem.0h2v.s8.da4d28a9adc9 from=translated src=- shape=7b13c01f vocab=9d46e7b8
-/
theorem source_difference (b : B) (a : F) :
    source b a-common b a∈above fiberCount (baseCount b+fiberCount a+1) := by
  rw [source,add_sub_cancel_left]
  apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a+2) (by intros; omega)
  exact higher_homo b a

/--
@isnad1 id=mem.0h2v.s8.9cef5e0040ea from=translated src=- shape=ac841708 vocab=309d8663
-/
theorem target_below (b : B) (a : F) : target b a∈below fiberCount (baseCount b+fiberCount a) := by
  apply (below fiberCount _).add_mem
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a) (by intros; omega)
    exact common_homo b a
  · apply space_mono (P:=fun w => degree fiberCount w<baseCount b+fiberCount a) (by intros; omega)
    exact lower_strict b a

/--
@isnad1 id=mem.0h2v.s8.65585fbf69a6 from=translated src=- shape=8da72055 vocab=e34a7003
-/
theorem target_difference (b : B) (a : F) :
    target b a-common b a∈strictlyBelow fiberCount (baseCount b+fiberCount a) := by
  rw [target,add_sub_cancel_left]
  exact lower_strict b a

/--
@isnad1 id=and.1h2v.s12.2c88a10ae6fc from=translated src=- shape=46e6f958 vocab=e109ac62
-/
theorem source_comparison {n : ℕ} {p : A K (Sum F B)}
    (hp : p∈homogeneous (Sum.elim fiberCount baseCount) n) :
    PolynomialOrdering.normalize common p∈TensorGrading.homogeneous fiberCount baseCount n ∧
    PolynomialOrdering.normalize source p-PolynomialOrdering.normalize common p∈TensorGrading.above fiberCount baseCount (n+1) :=
  TensorGrading.comparison_above common_homo source_above source_difference hp

/--
@isnad1 id=and.1h2v.s12.a9a61c42cdca from=translated src=- shape=b4d358fe vocab=6cfcff37
-/
theorem target_comparison {n : ℕ} {p : A K (Sum F B)}
    (hp : p∈homogeneous (Sum.elim fiberCount baseCount) n) :
    PolynomialOrdering.normalize common p∈TensorGrading.homogeneous fiberCount baseCount n ∧
    PolynomialOrdering.normalize target p-PolynomialOrdering.normalize common p∈TensorGrading.strictlyBelow fiberCount baseCount n :=
  TensorGrading.comparison_below common_homo target_below target_difference hp
end

open AssociativeElimination
abbrev G := Fin 3
def X : A K G := atom 0
def Y (i : Fin 2) : A K G := atom ⟨i.val+1,by omega⟩
def C (i : Fin 2) := bracket X (Y i)
def realize : A K F →ₐ[K] A K G := lift (fun a => match a with
  | 0 => X*X | 1 => Y 0 | 2 => Y 1 | 3 => C 0 | _ => C 1)
def δ (i : Fin 2) : A K G →ₗ[K] A K G := deriv (fun a => if a=0 ∨ a.val=i.val+1 then C i else 0)
def ε : A K G →ₗ[K] A K G := deriv (fun a => if a=0 then 0 else bracket (Y 0) (Y 1))
def baseDeriv : B → A K G →ₗ[K] A K G
  | 0 => (δ 0).comp (δ 0)
  | 1 => (δ 1).comp (δ 1)
  | 2 => ε
  | _ => (δ 0).comp ε-ε.comp (δ 0)

/--
@isnad1 id=eq.0h0v.s8.3159f7d1dc4f from=translated src=- shape=f2784ca4 vocab=ee35523e
-/
@[simp] theorem realize_H : realize H=X*X := by simp [realize,H]
/--
@isnad1 id=eq.0h1v.s8.df46aa79c187 from=translated src=- shape=a8223446 vocab=c17d57f6
-/
@[simp] theorem realize_U (i : Fin 2) : realize (U i)=Y i := by fin_cases i <;> simp [realize,U]
/--
@isnad1 id=eq.0h1v.s8.5a1f07385fd1 from=translated src=- shape=a8223446 vocab=b29aadb8
-/
@[simp] theorem realize_V (i : Fin 2) : realize (V i)=C i := by fin_cases i <;> simp [realize,V]
/--
@isnad1 id=eq.0h2v.s10.ad74fe4bc34b from=translated src=- shape=036faaae vocab=33058f69
-/
@[simp] theorem realize_bracket (p q : A K F) : realize (bracket p q)=bracket (realize p) (realize q) := by simp [bracket]
/--
@isnad1 id=eq.0h5v.s9.3b34c373d5ae from=translated src=- shape=77bdc34c vocab=68eac1a1
-/
@[simp] theorem deriv_bracket {R α : Type*} [CommRing R] (f : α → A R α) (p q : A R α) :
    deriv f (bracket p q)=bracket (deriv f p) q+bracket p (deriv f q) := by
  simp only [bracket,map_sub,AssociativeElimination.deriv_mul]; abel

/--
@isnad1 id=eq.0h3v.s7.5e0257c8fdff from=translated src=- shape=605ad947 vocab=d555e7d5
-/
@[simp] theorem bracket_add_left (p q r : A K G) : bracket (p+q) r=bracket p r+bracket q r := by simp [bracket,add_mul,mul_add]; abel
/--
@isnad1 id=eq.0h3v.s7.3b975d0c544e from=translated src=- shape=afdde928 vocab=d555e7d5
-/
@[simp] theorem bracket_add_right (p q r : A K G) : bracket p (q+r)=bracket p q+bracket p r := by simp [bracket,add_mul,mul_add]; abel
/--
@isnad1 id=eq.0h3v.s8.9cae4a8431db from=translated src=- shape=605ad947 vocab=48b390af
-/
@[simp] theorem bracket_sub_left (p q r : A K G) : bracket (p-q) r=bracket p r-bracket q r := by simp [bracket,sub_mul,mul_sub]; abel
/--
@isnad1 id=eq.0h3v.s8.1dd12f87c406 from=translated src=- shape=afdde928 vocab=48b390af
-/
@[simp] theorem bracket_sub_right (p q r : A K G) : bracket p (q-r)=bracket p q-bracket p r := by simp [bracket,sub_mul,mul_sub]; abel
/--
@isnad1 id=eq.0h1v.s7.fc629cff3493 from=translated src=- shape=daf20f54 vocab=2b0e6126
-/
@[simp] theorem bracket_zero_left (r : A K G) : bracket 0 r=0 := by simp [bracket]
/--
@isnad1 id=eq.0h1v.s7.8dede94645a9 from=translated src=- shape=0e7669ec vocab=2b0e6126
-/
@[simp] theorem bracket_zero_right (r : A K G) : bracket r 0=0 := by simp [bracket]
/--
@isnad1 id=eq.0h1v.s6.e0b34a429da1 from=translated src=- shape=bbfcd9a0 vocab=2b0e6126
-/
@[simp] theorem bracket_self (r : A K G) : bracket r r=0 := by simp [bracket]
/--
@isnad1 id=eq.0h2v.s5.eb4fbac3ee03 from=translated src=- shape=0ecdd215 vocab=1e740a9d
-/
theorem bracket_swap (p q : A K G) : bracket p q=bracket q p := by simp [bracket,CharTwo.sub_eq_add,add_comm]
/--
@isnad1 id=eq.0h2v.s7.964e9684b6f3 from=translated src=- shape=a1b5ce6d vocab=2a1aadd4
-/
theorem bracket_ad_square (u v : A K G) : bracket u (bracket u v)=bracket (u*u) v := by
  simp only [bracket,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
/--
@isnad1 id=eq.0h3v.s7.7e8df1934dbb from=translated src=- shape=abc4fb0f vocab=d555e7d5
-/
theorem bracket_leibniz (p q r : A K G) : bracket p (bracket q r)=bracket (bracket p q) r+bracket q (bracket p r) := by
  simp only [bracket]; noncomm_ring
/--
@isnad1 id=eq.0h1v.s8.a0b80194881e from=translated src=- shape=44cdf31b vocab=6efc24ec
-/
@[simp] theorem δ_X (i : Fin 2) : δ i X=C i := by simp [δ,X]
/--
@isnad1 id=eq.0h1v.s8.1995353f578e from=translated src=- shape=375f6c5c vocab=8b9599ee
-/
@[simp] theorem δ_Y_self (i : Fin 2) : δ i (Y i)=C i := by simp [δ,Y]
/--
@isnad1 id=eq.1h2v.s8.5402f95d82ed from=translated src=- shape=c369f36e vocab=a4ab00e0
-/
@[simp] theorem δ_Y_other (i j : Fin 2) (h : j≠i) : δ i (Y j)=0 := by
  have hv : j.val≠i.val := fun he => h (Fin.ext he)
  simp [δ,Y,hv]
/--
@isnad1 id=eq.0h3v.s10.51b50a2fed61 from=translated src=- shape=eb6d47b2 vocab=f19c040b
-/
theorem δ_mul (i : Fin 2) (p q : A K G) : δ i (p*q)=δ i p*q+p*δ i q := deriv_mul _ _ _
/--
@isnad1 id=eq.0h3v.s10.aa42ce6bca68 from=translated src=- shape=9ffc0a66 vocab=1d1509ed
-/
@[simp] theorem δ_bracket (i : Fin 2) (p q : A K G) : δ i (bracket p q)=bracket (δ i p) q+bracket p (δ i q) := deriv_bracket _ _ _
/--
@isnad1 id=eq.0h1v.s9.03976a32ca85 from=translated src=- shape=735dddf2 vocab=64cdb85e
-/
@[simp] theorem δ_H (i : Fin 2) : δ i (X*X)=bracket (X*X) (Y i) := by
  rw [δ_mul,δ_X,← bracket_ad_square]
  change C i*X+X*C i=bracket X (C i)
  simp [bracket,CharTwo.sub_eq_add,add_comm]
/--
@isnad1 id=eq.0h1v.s4.9c2238bf7b4b from=translated src=- shape=4af9c4a3 vocab=3920b6b1
-/
theorem bracket_X_Y (i : Fin 2) : bracket X (Y i)=C i := rfl
/--
@isnad1 id=eq.0h1v.s6.4d76c490a7e4 from=translated src=- shape=cc631ffb vocab=3f45bb02
-/
theorem bracket_X_C (i : Fin 2) : bracket X (C i)=bracket (X*X) (Y i) := bracket_ad_square _ _
/--
@isnad1 id=eq.0h1v.s9.fb2a4a3856f9 from=translated src=- shape=9479968c vocab=62df8e02
-/
@[simp] theorem δ_C_self (i : Fin 2) : δ i (C i)=bracket (X*X+C i) (Y i) := by
  change δ i (bracket X (Y i))=_
  rw [δ_bracket,δ_X,δ_Y_self,bracket_X_C,bracket_add_left]
  exact add_comm _ _
/--
@isnad1 id=eq.1h2v.s8.fab4267d4103 from=translated src=- shape=f3f7ffe7 vocab=7954dd3a
-/
@[simp] theorem δ_C_other (i j : Fin 2) (h : j≠i) : δ i (C j)=bracket (C i) (Y j) := by
  rw [C,δ_bracket,δ_X,δ_Y_other i j h,bracket_zero_right,add_zero]
/--
@isnad1 id=eq.0h0v.s8.ca43f3206294 from=translated src=- shape=d1be504e vocab=0adfb62d
-/
@[simp] theorem ε_X : ε X=0 := by simp [ε,X]
/--
@isnad1 id=eq.0h1v.s8.df15bb9da47f from=translated src=- shape=3e6a8e6e vocab=ba9c3519
-/
@[simp] theorem ε_Y (i : Fin 2) : ε (Y i)=bracket (Y 0) (Y 1) := by simp [ε,Y]
/--
@isnad1 id=eq.0h2v.s10.e02c0b9aea48 from=translated src=- shape=631be01e vocab=c03de50b
-/
@[simp] theorem ε_bracket (p q : A K G) : ε (bracket p q)=bracket (ε p) q+bracket p (ε q) := deriv_bracket _ _ _
/--
@isnad1 id=eq.0h0v.s9.14df295afaa7 from=translated src=- shape=03af2234 vocab=cef22e07
-/
@[simp] theorem ε_H : ε (X*X)=0 := by simp [ε,AssociativeElimination.deriv_mul,X]
/--
@isnad1 id=eq.0h1v.s9.76218740c33c from=translated src=- shape=8ee79ab3 vocab=da94e9d2
-/
theorem ε_C (i : Fin 2) : ε (C i)=bracket (C 0) (Y 1)+bracket (Y 0) (C 1) := by
  rw [C,ε_bracket,ε_X,ε_Y,bracket_zero_left,zero_add,bracket_leibniz]
  rfl

def J := baseDeriv 3
/--
@isnad1 id=eq.0h0v.s9.21bbd123067a from=translated src=- shape=730ae19e vocab=4ff0debf
-/
@[simp] theorem J_X : J X=bracket (C 0) (Y 1)+bracket (Y 0) (C 1) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_X,map_zero,δ_X,ε_C]
  simp only [zero_sub,CharTwo.neg_eq]
/--
@isnad1 id=eq.0h0v.s8.449817fc8c8c from=translated src=- shape=93a1af81 vocab=ccf71132
-/
@[simp] theorem J_Y_zero : J (Y 0)=bracket (Y 0) (C 1) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_Y,δ_bracket,δ_Y_self,
    δ_Y_other 0 1 (by decide),bracket_zero_right,add_zero,ε_C]
  simp only [sub_add_eq_sub_sub,sub_self,zero_sub,CharTwo.neg_eq]
/--
@isnad1 id=eq.0h0v.s8.148d17ae780e from=translated src=- shape=93a1af81 vocab=ccf71132
-/
@[simp] theorem J_Y_one : J (Y 1)=bracket (Y 1) (C 0) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_Y,δ_bracket,δ_Y_self,
    δ_Y_other 0 1 (by decide),bracket_zero_right,add_zero,map_zero,sub_zero]
  exact bracket_swap _ _
/--
@isnad1 id=eq.0h2v.s10.b07d7a24463c from=translated src=- shape=631be01e vocab=f44f0ccc
-/
@[simp] theorem J_bracket (p q : A K G) : J (bracket p q)=bracket (J p) q+bracket p (J q) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_bracket,δ_bracket,map_add,
    bracket_sub_left,bracket_sub_right]
  abel
/--
@isnad1 id=eq.0h2v.s10.ea135aeb9c03 from=translated src=- shape=daa7046b vocab=a60f5801
-/
@[simp] theorem J_mul (p q : A K G) : J (p*q)=J p*q+p*J q := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε,δ,AssociativeElimination.deriv_mul,
    map_add,sub_mul,mul_sub]
  abel
/--
@isnad1 id=eq.0h0v.s9.c6ae1b8e573d from=translated src=- shape=c4ddcb33 vocab=6c532949
-/
@[simp] theorem J_H : J (X*X)=bracket (X*X) (bracket (Y 0) (Y 1)) := by
  rw [J_mul,J_X]
  have h : bracket (C 0) (Y 1)+bracket (Y 0) (C 1)=bracket X (bracket (Y 0) (Y 1)) :=
    (bracket_leibniz X (Y 0) (Y 1)).symm
  rw [h,← bracket_ad_square]
  simp only [bracket,CharTwo.sub_eq_add]
  exact add_comm _ _
/--
@isnad1 id=eq.0h0v.s9.d5f43071de85 from=translated src=- shape=bbd61650 vocab=aad636d3
-/
@[simp] theorem J_C_zero : J (C 0)=bracket (C 0) (C 1)+
    bracket (bracket (C 0) (Y 1)+bracket (Y 0) (C 1)) (Y 0)+bracket (Y 0) (bracket (X*X) (Y 1)) := by
  change J (bracket X (Y 0))=_
  rw [J_bracket,J_X,J_Y_zero,bracket_leibniz,bracket_X_C]
  rw [bracket_X_Y 0,add_left_comm,← add_assoc]
/--
@isnad1 id=eq.0h0v.s9.e29397cc3fae from=translated src=- shape=bbd61650 vocab=aad636d3
-/
@[simp] theorem J_C_one : J (C 1)=bracket (C 0) (C 1)+
    bracket (bracket (C 0) (Y 1)+bracket (Y 0) (C 1)) (Y 1)+bracket (Y 1) (bracket (X*X) (Y 0)) := by
  change J (bracket X (Y 1))=_
  rw [J_bracket,J_X,J_Y_one,bracket_leibniz,bracket_X_C]
  rw [bracket_X_Y 1,bracket_swap (C 1) (C 0),add_left_comm,← add_assoc]

/--
@isnad1 id=eq.0h1v.s10.c4b31fa97a0a from=translated src=- shape=a45da043 vocab=62df8e02
-/
@[simp] theorem δ_square_H (i : Fin 2) : δ i (δ i (X*X))=
    bracket (X*X) (C i)+bracket (bracket (X*X) (Y i)) (Y i) := by
  rw [δ_H,δ_bracket,δ_H,δ_Y_self]
  exact add_comm _ _
/--
@isnad1 id=eq.0h1v.s9.1f573460a353 from=translated src=- shape=96958103 vocab=62df8e02
-/
@[simp] theorem δ_H_add_C (i : Fin 2) : δ i (X*X+C i)=bracket (C i) (Y i) := by
  rw [map_add,δ_H,δ_C_self,bracket_add_left,CharTwo.add_cancel_left]
/--
@isnad1 id=eq.0h1v.s9.34b7671adf7d from=translated src=- shape=700ea2ca vocab=62df8e02
-/
@[simp] theorem δ_square_C_self (i : Fin 2) : δ i (δ i (C i))=
    bracket (X*X) (C i)+bracket (bracket (C i) (Y i)) (Y i) := by
  rw [δ_C_self,δ_bracket,δ_H_add_C,δ_Y_self,bracket_add_left,bracket_self,add_zero]
  exact add_comm _ _
/--
@isnad1 id=eq.1h2v.s9.30d144b42468 from=translated src=- shape=78e1a934 vocab=62df8e02
-/
@[simp] theorem δ_square_C_other (i j : Fin 2) (h : j≠i) : δ i (δ i (C j))=
    bracket (bracket (X*X+C i) (Y i)) (Y j) := by
  rw [δ_C_other i j h,δ_bracket,δ_C_self,δ_Y_other i j h,bracket_zero_right,add_zero]

/--
@isnad1 id=eq.0h0v.s8.0bd4c2b92b02 from=translated src=- shape=d4a7e952 vocab=319d224a
-/
@[simp] theorem realize_atom_zero : realize (atom (0 : F))=X*X := realize_H
/--
@isnad1 id=eq.0h0v.s8.8005d3721c63 from=translated src=- shape=bd49ba60 vocab=a857d0b5
-/
@[simp] theorem realize_atom_one : realize (atom (1 : F))=Y 0 := realize_U 0
/--
@isnad1 id=eq.0h0v.s8.588657dc2d85 from=translated src=- shape=bd49ba60 vocab=a857d0b5
-/
@[simp] theorem realize_atom_two : realize (atom (2 : F))=Y 1 := realize_U 1
/--
@isnad1 id=eq.0h0v.s8.f075b0ba2a5c from=translated src=- shape=bd49ba60 vocab=edd28e4d
-/
@[simp] theorem realize_atom_three : realize (atom (3 : F))=C 0 := realize_V 0
/--
@isnad1 id=eq.0h0v.s8.b8e18eba86eb from=translated src=- shape=bd49ba60 vocab=edd28e4d
-/
@[simp] theorem realize_atom_four : realize (atom (4 : F))=C 1 := realize_V 1

attribute [local irreducible] X Y C H U V
 /--
 @isnad1 id=eq.0h1v.s10.95273375a20e from=translated src=- shape=473570c3 vocab=57d41138
 -/
 theorem source_realization_a0 (a : F) : baseDeriv 0 (realize (atom a))=realize (source 0 a) := by
  fin_cases a <;> simp [source,common,higher,R',Q,baseDeriv,δ_Y_other 0 1 (by decide)]
  · exact add_comm _ _
  · rw [add_add_add_comm,CharTwo.add_self_eq_zero,zero_add]
 /--
 @isnad1 id=eq.0h1v.s10.c389517a2d64 from=translated src=- shape=473570c3 vocab=57d41138
 -/
 theorem source_realization_a1 (a : F) : baseDeriv 1 (realize (atom a))=realize (source 1 a) := by
  fin_cases a <;> simp [source,common,higher,R',Q,baseDeriv,δ_Y_other 1 0 (by decide)]
  · exact add_comm _ _
  · rw [add_add_add_comm,CharTwo.add_self_eq_zero,zero_add]
 /--
 @isnad1 id=eq.0h1v.s10.cf17063fcfd4 from=translated src=- shape=473570c3 vocab=57d41138
 -/
 theorem source_realization_u (a : F) : baseDeriv 2 (realize (atom a))=realize (source 2 a) := by
  fin_cases a <;> simp [source,common,higher,W,baseDeriv,ε_C]
 /--
 @isnad1 id=eq.0h1v.s10.98e448f52ca1 from=translated src=- shape=473570c3 vocab=57d41138
 -/
 theorem source_realization_v (a : F) : baseDeriv 3 (realize (atom a))=realize (source 3 a) := by
  change J (realize (atom a))=_
  fin_cases a <;> simp [source,common,higher,R',W,add_assoc]
  have h := J_H
  rw [J_mul,J_X] at h
  exact h
/--
@isnad1 id=eq.0h2v.s10.24e8f8c10708 from=translated src=- shape=ba2cfa8d vocab=57d41138
-/
theorem source_realization (b : B) (a : F) : baseDeriv b (realize (atom a))=realize (source b a) := by
  fin_cases b
  · exact source_realization_a0 a
  · exact source_realization_a1 a
  · exact source_realization_u a
  · exact source_realization_v a
end CountTables
namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
def raw (κ : α → α → α → R) (l r : α) : List α → A R α
  | [] => 0
  | a::s => κ l a (s.headD r) • word (FreeMonoid.ofList s)+atom a*raw κ a r s

def op (κ : α → α → α → R) (l r : α) : Module.End R (A R α) :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => raw κ l r w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
/--
@isnad1 id=eq.0h6v.s7.2a5981798db0 from=translated src=- shape=15be2974 vocab=9ea02c1c
-/
@[simp] theorem op_word (κ : α → α → α → R) (l r : α) (s : List α) :
    op κ l r (word (FreeMonoid.ofList s))=raw κ l r s := by change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => raw κ l r monoidWord.toList) (Finsupp.single (FreeMonoid.ofList s) 1) = _; simp

inductive Step (κ : α → α → α → R) (r : α) : α → List α → List α → Prop
  | head (l a : α) (s : List α) (h : κ l a (s.headD r)≠0) : Step κ r l (a::s) s
  | tail (l a : α) (s t : List α) (h : Step κ r a s t) : Step κ r l (a::s) (a::t)

/--
@isnad1 id=mem.0h8v.s7.6bf64a4f53ab from=translated src=- shape=4883185e vocab=e23e4bd9
-/
theorem raw_mem_space (κ : α → α → α → R) (l r : α) (s : List α)
    (P : FreeMonoid α → Prop) (h : ∀ t,Step κ r l s t → P (FreeMonoid.ofList t)) :
    raw κ l r s∈space P := by
  classical
  induction s generalizing l P with
  | nil => exact (space P).zero_mem
  | cons a s ih =>
    apply (space P).add_mem
    · by_cases hc : κ l a (s.headD r)=0
      · simp only [hc,zero_smul]; exact (space P).zero_mem
      · exact (space P).smul_mem _ (word_mem _ (h s (.head l a s hc)))
    · have ht := ih a (fun w => P (FreeMonoid.of a*w)) (by
        intro t ht
        simpa only [FreeMonoid.ofList_cons] using h (a::t) (.tail l a s t ht))
      exact map_space (Algebra.lmul R (A R α) (atom a)) (space P) (by
        intro w hw
        change atom a*word w∈space P
        rw [← word_of a,← word_mul]
        exact word_mem _ hw) ht

/--
@isnad1 id=eq.1h7v.s5.4406a43bd389 from=translated src=- shape=3f910a7a vocab=667e282b
-/
theorem Step.length {κ : α → α → α → R} {r l : α} {s t : List α}
    (h : Step κ r l s t) : t.length+1=s.length := by
  induction h with
  | head => simp
  | tail _ _ _ _ _ ih => simp only [List.length_cons]; omega

/--
@isnad1 id=mem.0h6v.s7.34b3815b2c34 from=translated src=- shape=e7831758 vocab=7ad4e89b
-/
theorem raw_length (κ : α → α → α → R) (l r : α) (s : List α) :
    raw κ l r s∈space (fun w => w.toList.length+1=s.length) :=
  raw_mem_space κ l r s _ (by intro t ht; simpa only [FreeMonoid.toList_ofList] using ht.length)

def count (wt : α → ℕ) (s : List α) : ℕ := (s.map wt).sum
/--
@isnad1 id=eq.0h2v.s4.d98dfd099e3d from=translated src=- shape=71350fa2 vocab=d64b8f9d
-/
@[simp] theorem count_nil (wt : α → ℕ) : count wt []=0 := rfl
/--
@isnad1 id=eq.0h4v.s5.37f2ad43ebdc from=translated src=- shape=4d9cb06a vocab=7435d647
-/
@[simp] theorem count_cons (wt : α → ℕ) (a : α) (s : List α) : count wt (a::s)=wt a+count wt s := rfl

/--
@isnad1 id=le.2h9v.s6.3ffbb2d3afe2 from=translated src=- shape=3c210a82 vocab=271bab42
-/
theorem Step.count_bound {κ : α → α → α → R} {r l : α} {s t : List α}
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a≤c)
    (h : Step κ r l s t) : count wt s≤c+count wt t := by
  induction h with
  | head l a s h => simpa only [count_cons] using Nat.add_le_add_right (hc l a _ h) (count wt s)
  | tail l a s t h ih => simp only [count_cons]; omega

/--
@isnad1 id=mem.1h8v.s7.a17acd81ebb8 from=translated src=- shape=3dda7828 vocab=73e8f1be
-/
theorem raw_count_bound (κ : α → α → α → R) (l r : α) (s : List α)
    (wt : α → ℕ) (c : ℕ) (hc : ∀ l a b,κ l a b≠0 → wt a≤c) :
    raw κ l r s∈space (fun w => count wt s≤c+degree wt w) :=
  raw_mem_space κ l r s _ (by
    intro t ht
    simpa only [degree,FreeMonoid.toList_ofList,count] using ht.count_bound wt c hc)
end WeightedDeletion

end DeligneDrinfeld

end

end OAI
