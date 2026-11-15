import Tengoku.FltAnthropic.Definitions.Def_IharaIota
import Tengoku.Seed.GroupTheory.PushoutI

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups

def iharaEdge (N q : ℕ) : Fin 2 → (Gamma0 (N * q) →* Gamma0 N) :=
  ![ι₀ N q, ι₁ N q]

/--
@isnad1 id=eq.0h2v.s11.61efa8085b9d from=translated src=- shape=fade1d0d vocab=066470ce
-/
@[simp] theorem iharaEdge_zero (N q : ℕ) : iharaEdge N q 0 = ι₀ N q := rfl

/--
@isnad1 id=eq.0h2v.s11.715a410413eb from=translated src=- shape=fade1d0d vocab=91c4fc36
-/
@[simp] theorem iharaEdge_one (N q : ℕ) : iharaEdge N q 1 = ι₁ N q := rfl

def iharaAmalgam (N q : ℕ) : Type :=
  Monoid.PushoutI (iharaEdge N q)

instance (N q : ℕ) : Group (iharaAmalgam N q) :=
  inferInstanceAs (Group (Monoid.PushoutI (iharaEdge N q)))

def iharaVertex (N q : ℕ) (i : Fin 2) : Gamma0 N →* iharaAmalgam N q :=
  Monoid.PushoutI.of (φ := iharaEdge N q) i

def iharaBase (N q : ℕ) : Gamma0 (N * q) →* iharaAmalgam N q :=
  Monoid.PushoutI.base (iharaEdge N q)

/--
@isnad1 id=eq.0h3v.s13.0ed945f8f7dd from=translated src=- shape=d4a8c48f vocab=788af032
-/
theorem iharaVertex_zero_iota0 (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 0 (ι₀ N q γ) = iharaBase N q γ :=
  Monoid.PushoutI.of_apply_eq_base (iharaEdge N q) 0 γ

/--
@isnad1 id=eq.0h3v.s13.af2cd3bd99cb from=translated src=- shape=d4a8c48f vocab=dd769ff4
-/
theorem iharaVertex_one_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 1 (ι₁ N q γ) = iharaBase N q γ :=
  Monoid.PushoutI.of_apply_eq_base (iharaEdge N q) 1 γ

/--
@isnad1 id=eq.0h3v.s14.2d7b0a1e07ae from=translated src=- shape=315d629a vocab=0a3ccd60
-/
theorem iharaVertex_edge (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 0 (ι₀ N q γ) = iharaVertex N q 1 (ι₁ N q γ) := by
  rw [iharaVertex_zero_iota0, iharaVertex_one_iota1]

section Lift

variable {N q : ℕ} {K : Type*} [Monoid K]

def pairFamily (f₀ f₁ : Gamma0 N →* K) : (i : Fin 2) → (Gamma0 N →* K) :=
  ![f₀, f₁]

/--
@isnad1 id=eq.0h4v.s11.d9caf64c9254 from=translated src=- shape=bc92601a vocab=5225e57c
-/
@[simp] theorem pairFamily_zero (f₀ f₁ : Gamma0 N →* K) : pairFamily f₀ f₁ 0 = f₀ := rfl

/--
@isnad1 id=eq.0h4v.s11.d48bcd8ae7bd from=translated src=- shape=099db61d vocab=5225e57c
-/
@[simp] theorem pairFamily_one (f₀ f₁ : Gamma0 N →* K) : pairFamily f₀ f₁ 1 = f₁ := rfl

/--
@isnad1 id=eq.1h6v.s13.93aabaea5c30 from=translated src=- shape=75d210ca vocab=987db275
-/
theorem pairFamily_compat (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q)) :
    ∀ i : Fin 2, (pairFamily f₀ f₁ i).comp (iharaEdge N q i) = f₀.comp (ι₀ N q) := by
  intro i
  fin_cases i
  · rfl
  · exact h.symm

def iharaLift (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q)) :
    iharaAmalgam N q →* K :=
  Monoid.PushoutI.lift (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h)

/--
@isnad1 id=eq.1h7v.s13.41184815bfb9 from=translated src=- shape=8116f64c vocab=d1578f23
-/
theorem iharaLift_vertex (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (i : Fin 2) (g : Gamma0 N) :
    iharaLift f₀ f₁ h (iharaVertex N q i g) = pairFamily f₀ f₁ i g :=
  Monoid.PushoutI.lift_of (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h) g

/--
@isnad1 id=eq.1h6v.s13.e12775010f88 from=translated src=- shape=5e1e34e4 vocab=f1eb3ebf
-/
theorem iharaLift_vertex_zero (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (g : Gamma0 N) : iharaLift f₀ f₁ h (iharaVertex N q 0 g) = f₀ g :=
  iharaLift_vertex f₀ f₁ h 0 g

/--
@isnad1 id=eq.1h6v.s13.c099f20884aa from=translated src=- shape=4a9dda3f vocab=f1eb3ebf
-/
theorem iharaLift_vertex_one (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (g : Gamma0 N) : iharaLift f₀ f₁ h (iharaVertex N q 1 g) = f₁ g :=
  iharaLift_vertex f₀ f₁ h 1 g

/--
@isnad1 id=eq.1h6v.s14.91b9fc0db2b4 from=translated src=- shape=eab92885 vocab=e9c0a6e3
-/
theorem iharaLift_base (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (γ : Gamma0 (N * q)) : iharaLift f₀ f₁ h (iharaBase N q γ) = f₀ (ι₀ N q γ) :=
  Monoid.PushoutI.lift_base (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h) γ

/--
@isnad1 id=eq.1h5v.s11.fbe2c9cd933f from=translated src=- shape=39f85c96 vocab=f0237ebc
-/
theorem iharaAmalgam_hom_ext {f g : iharaAmalgam N q →* K}
    (h : ∀ i : Fin 2, f.comp (iharaVertex N q i) = g.comp (iharaVertex N q i)) : f = g :=
  Monoid.PushoutI.hom_ext_nonempty h

end Lift

/--
@isnad1 id=eq.0h2v.s9.2bd161b4ee76 from=translated src=- shape=ed167992 vocab=a1454315
-/
theorem iharaVertex_range_sup (N q : ℕ) :
    (iharaVertex N q 0).range ⊔ (iharaVertex N q 1).range = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using Monoid.PushoutI.induction_on with
  | of i g =>
    fin_cases i
    · exact Subgroup.mem_sup_left ⟨g, rfl⟩
    · exact Subgroup.mem_sup_right ⟨g, rfl⟩
  | base γ => exact Subgroup.mem_sup_left ⟨ι₀ N q γ, iharaVertex_zero_iota0 N q γ⟩
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy

end Ihara
