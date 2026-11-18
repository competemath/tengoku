import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime

open scoped MatrixGroups

namespace SL2CRTLift

noncomputable section

variable {m M : ℕ}

abbrev crt (h : m.Coprime M) : ZMod (m * M) ≃+* ZMod m × ZMod M := ZMod.chineseRemainder h

def π₁ (h : m.Coprime M) : ZMod (m * M) →+* ZMod m := (RingHom.fst _ _).comp (crt h).toRingHom

def π₂ (h : m.Coprime M) : ZMod (m * M) →+* ZMod M := (RingHom.snd _ _).comp (crt h).toRingHom

/--
@isnad1 id=eq.1h3v.s9.8f0429ce48fa from=translated src=- shape=cdd9a39b vocab=489881c0
-/
theorem π₁_apply (h : m.Coprime M) (x : ZMod (m * M)) : π₁ h x = (crt h x).1 := rfl

/--
@isnad1 id=eq.1h3v.s9.693c08aef7ad from=translated src=- shape=294ff9eb vocab=9b7de566
-/
theorem π₂_apply (h : m.Coprime M) (x : ZMod (m * M)) : π₂ h x = (crt h x).2 := rfl

/--
@isnad1 id=eq.1h3v.s9.e03cefb7c2ce from=translated src=- shape=3f12b122 vocab=9dcc93ab
-/
theorem crt_apply_eq (h : m.Coprime M) (x : ZMod (m * M)) : crt h x = (π₁ h x, π₂ h x) := rfl

def crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    Matrix (Fin 2) (Fin 2) (ZMod (m * M)) :=
  Matrix.of fun i j => (crt h).symm (A i j, B i j)

/--
@isnad1 id=eq.1h6v.s8.e7718708cd9b from=translated src=- shape=1cabe223 vocab=b79f1c35
-/
theorem π₁_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) (i j : Fin 2) :
    π₁ h (crtMat h A B i j) = A i j := by
  simp [π₁_apply, crtMat]

/--
@isnad1 id=eq.1h6v.s8.d7326f68b728 from=translated src=- shape=9392c961 vocab=f2c515c3
-/
theorem π₂_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) (i j : Fin 2) :
    π₂ h (crtMat h A B i j) = B i j := by
  simp [π₂_apply, crtMat]

/--
@isnad1 id=eq.1h4v.s9.e7262234e33f from=translated src=- shape=213d8ecf vocab=b71cbd03
-/
theorem mapMatrix_π₁_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    (π₁ h).mapMatrix (crtMat h A B) = (A : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact π₁_crtMat h A B i j

/--
@isnad1 id=eq.1h4v.s9.f4e45724f5d6 from=translated src=- shape=f254f6a9 vocab=5235925e
-/
theorem mapMatrix_π₂_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    (π₂ h).mapMatrix (crtMat h A B) = (B : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact π₂_crtMat h A B i j

/--
@isnad1 id=eq.1h4v.s7.d5b62fbcd642 from=translated src=- shape=916fed40 vocab=621ea23c
-/
theorem det_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    (crtMat h A B).det = 1 := by
  apply (crt h).injective
  rw [map_one, crt_apply_eq, RingHom.map_det, RingHom.map_det, mapMatrix_π₁_crtMat,
    mapMatrix_π₂_crtMat, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe]
  rfl

def crtSL (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) : SL(2, ZMod (m * M)) :=
  ⟨crtMat h A B, det_crtMat h A B⟩

/--
@isnad1 id=eq.1h3v.s7.e27c14bb4cd8 from=translated src=- shape=c12f58c4 vocab=29c205b6
-/
theorem π₁_intCast (h : m.Coprime M) (k : ℤ) : π₁ h (k : ZMod (m * M)) = (k : ZMod m) :=
  map_intCast (π₁ h) k

/--
@isnad1 id=eq.1h3v.s7.5eb446124fea from=translated src=- shape=5615bb4e vocab=ba303365
-/
theorem π₂_intCast (h : m.Coprime M) (k : ℤ) : π₂ h (k : ZMod (m * M)) = (k : ZMod M) :=
  map_intCast (π₂ h) k

/--
@isnad1 id=ex.1h4v.s10.f8162e2a83f7 from=translated src=- shape=60f25f14 vocab=9d75b62d
-/
theorem main (m M : ℕ) [NeZero m] [NeZero M] (hmM : Nat.Coprime m M)
    (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ = A ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = B := by
  haveI : NeZero (m * M) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne M)⟩
  obtain ⟨γ, hγ⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod (m * M) (crtSL hmM A B)

  have hent : ∀ i j : Fin 2, ((γ i j : ℤ) : ZMod (m * M)) = crtMat hmM A B i j := by
    intro i j
    have := congrArg (fun Y : SL(2, ZMod (m * M)) => Y i j) hγ
    simp at this
    exact this
  refine ⟨γ, ?_, ?_⟩
  · ext i j
    have h1 : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ) i j = ((γ i j : ℤ) : ZMod m) := by
      simp
    rw [h1, ← π₁_intCast hmM, hent, π₁_crtMat]
  · ext i j
    have h1 : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ) i j = ((γ i j : ℤ) : ZMod M) := by
      simp
    rw [h1, ← π₂_intCast hmM, hent, π₂_crtMat]

end

end SL2CRTLift

/--
@isnad1 id=ex.1h4v.s10.f8162e2a83f7 from=translated src=- shape=60f25f14 vocab=9d75b62d
-/
theorem solution
    (m M : ℕ) [NeZero m] [NeZero M] (hmM : Nat.Coprime m M)
    (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ = A ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = B :=
  SL2CRTLift.main m M hmM A B
