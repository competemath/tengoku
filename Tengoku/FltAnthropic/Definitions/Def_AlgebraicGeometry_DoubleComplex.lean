import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

namespace DoubleComplex

structure Bounded (R : Type u) [CommRing R] where

  C : ℕ → ℕ → Type u
  [abGrp : ∀ p q, AddCommGroup (C p q)]
  [modR : ∀ p q, Module R (C p q)]

  dH : ∀ p q, C p q →ₗ[R] C (p + 1) q

  dV : ∀ p q, C p q →ₗ[R] C p (q + 1)
  dH_sq : ∀ p q, dH (p + 1) q ∘ₗ dH p q = 0
  dV_sq : ∀ p q, dV p (q + 1) ∘ₗ dV p q = 0

  dHV_comm : ∀ p q, dV (p + 1) q ∘ₗ dH p q = dH p (q + 1) ∘ₗ dV p q

  N : ℕ
  hBound : ∀ p q, N ≤ p ∨ N ≤ q → Subsingleton (C p q)

attribute [instance] Bounded.abGrp Bounded.modR

section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)

abbrev Diag (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

abbrev Tot (n : ℕ) : Type u :=
  ∀ i : Diag n, D.C i.1.1 i.1.2

def dTotH {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(0, _), _⟩ => 0
  | ⟨(p' + 1, q), h⟩ => (D.dH p' q).comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p', q), by omega⟩)

def dTotV {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(_, 0), _⟩ => 0
  | ⟨(p, q' + 1), h⟩ => (D.dV p q').comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p, q'), by omega⟩)

def dTot (n : ℕ) :
    Tot D n →ₗ[R] Tot D (n + 1) :=
  LinearMap.pi fun i =>
    dTotH D i + ((-1 : ℤ) ^ i.1.1) • dTotV D i

def HTotB : (n : ℕ) → Submodule R (LinearMap.ker (dTot D n))
  | 0 => ⊥
  | n' + 1 => (LinearMap.range (dTot D n')).comap
      (LinearMap.ker (dTot D (n' + 1))).subtype

abbrev HTot (n : ℕ) : Type u :=
  LinearMap.ker (dTot D n) ⧸ HTotB D n

end Tot

section DTotGeneric

variable {R : Type u} [CommRing R] {D : Bounded R}

end DTotGeneric

section E2

variable {R : Type u} [CommRing R] (D : Bounded R)

def colB (p : ℕ) : (q : ℕ) → Submodule R (LinearMap.ker (D.dV p q))
  | 0 => ⊥
  | q' + 1 => (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype

abbrev colH (p q : ℕ) : Type u :=
  LinearMap.ker (D.dV p q) ⧸ colB D p q

def colHdH (p q : ℕ) :
    colH D p q →ₗ[R] colH D (p + 1) q :=
  Submodule.mapQ _ _
    ((D.dH p q).restrict fun x hx => LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply,
        LinearMap.mem_ker.mp hx, map_zero])
    (by
      rcases q with _ | q'
      · simp only [colB]; exact bot_le
      · rintro x ⟨y, hy⟩
        exact ⟨D.dH p q' y, by
          show D.dV (p + 1) q' (D.dH p q' y) = D.dH p (q' + 1) x.1
          rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply, hy]; rfl⟩)

def E₂IB :
    (p q : ℕ) → Submodule R (LinearMap.ker (colHdH D p q))
  | 0, _ => ⊥
  | p' + 1, q => (LinearMap.range (colHdH D p' q)).comap
      (LinearMap.ker (colHdH D (p' + 1) q)).subtype

abbrev E₂I (p q : ℕ) : Type u :=
  LinearMap.ker (colHdH D p q) ⧸ E₂IB D p q

def transpose : Bounded R where
  C a b := D.C b a
  dH a b := D.dV b a
  dV a b := D.dH b a
  dH_sq a b := D.dV_sq b a
  dV_sq a b := D.dH_sq b a
  dHV_comm a b := (D.dHV_comm b a).symm
  N := D.N
  hBound a b h := D.hBound b a h.symm

abbrev E₂II (p q : ℕ) : Type u :=
  E₂I (transpose D) q p

instance (p q : ℕ) : AddCommGroup (E₂I D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂I D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))
instance (p q : ℕ) : AddCommGroup (E₂II D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂II D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))

end E2

structure SubQuot (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] where
  Z : Submodule R M
  B : Submodule R M
  hBZ : B ≤ Z

abbrev SubQuot.carrier {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (s : SubQuot R M) : Type u := s.Z ⧸ s.B.comap s.Z.subtype

structure Convergence (R : Type u) [CommRing R]
    (E₂ : ℕ → ℕ → Type u) [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    (H : ℕ → Type u) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] (N : ℕ) where

  Einf : ∀ p q, SubQuot R (E₂ p q)

  hZ0 : ∀ p, (Einf p 0).Z = ⊤

  Bfilt : ∀ p, Fin (N + 1) → Submodule R (E₂ p 0)
  Bfilt_mono : ∀ p, Monotone (Bfilt p)
  Bfilt_bot : ∀ p, Bfilt p 0 = ⊥
  Bfilt_top : ∀ p, Bfilt p (Fin.last N) = (Einf p 0).B

  Bfilt_gr : ∀ p (i : Fin N), ∃ p' q', 1 ≤ q' ∧ ∃ (s : SubQuot R (E₂ p' q')),
    Nonempty (((Bfilt p i.succ) ⧸ (Bfilt p i.castSucc).comap (Bfilt p i.succ).subtype)
      ≃ₗ[R] s.carrier)

  Hfilt : ∀ n, Fin (N + 2) → Submodule R (H n)
  Hfilt_mono : ∀ n, Monotone (Hfilt n)
  Hfilt_bot : ∀ n, Hfilt n 0 = ⊥
  Hfilt_top : ∀ n, Hfilt n (Fin.last (N + 1)) = ⊤

  Hfilt_gr : ∀ (p : Fin (N + 1)),
    Nonempty (((Hfilt (↑p) p.succ) ⧸ (Hfilt (↑p) p.castSucc).comap (Hfilt (↑p) p.succ).subtype)
      ≃ₗ[R] (Einf p 0).carrier)

def BoundedSpectralSequence : Prop :=
  ∀ (R : Type u) [CommRing R] (D : Bounded R),
    Nonempty (Convergence R (E₂I D) (HTot D) D.N)

end DoubleComplex

end
