import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Lifting
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Plane
import Tengoku

namespace OAI

/-!
# Elimination of auxiliary variables

Explicit mutually inverse complex algebra maps identify the lifting presentation
with the quotient of the original polynomial ring by `(F)`.
-/

noncomputable section
namespace AbhyankarSathaye.Presentation
open MvPolynomial

abbrev B := Plane.Q ℂ
abbrev hB : B := Plane.qvar ℂ 0
abbrev xB : B := Plane.qvar ℂ 1
abbrev yB : B := Plane.qvar ℂ 2
abbrev sB : B := Plane.qvar ℂ 3
abbrev L := Lifting.Q hB xB yB sB
abbrev D := R ⧸ Ideal.span {F}

def dmap : R →ₐ[ℂ] D := Ideal.Quotient.mkₐ ℂ (Ideal.span {F})
def lcoef : B →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ B L
def lvar (i : Fin 3) : L := Lifting.qvar hB xB yB sB i

/--
@isnad1 id=eq.0h0v.s9.0f6e79a87dea from=translated src=- shape=8cc970ed vocab=5496dc9b
-/
theorem dmap_F : dmap F = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

def auxValues : Fin 4 → D := ![dmap h, dmap x, dmap y, dmap s]
def auxEval : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] D := aeval auxValues

/--
@isnad1 id=eq.0h0v.s9.3a36551a4861 from=translated src=- shape=4448f017 vocab=7daa4e73
-/
theorem auxEval_h : auxEval (Plane.relH ℂ) = 0 := by
  calc
    _ = dmap (h-1-p) := by simp [Plane.relH, auxEval, auxValues, p]
    _ = dmap F := by congr 1; unfold F; ring
    _ = 0 := dmap_F

/--
@isnad1 id=eq.0h0v.s9.f969acbb9854 from=translated src=- shape=4448f017 vocab=ffa67deb
-/
theorem auxEval_cusp : auxEval (Plane.relCusp ℂ) = 0 := by
  calc
    _ = dmap (x^2+y^3-s*h) := by simp [Plane.relCusp, auxEval, auxValues]
    _ = 0 := by rw [cusp]; simp [mul_comm]

def auxToD : B →ₐ[ℂ] D :=
  lift_pair (Plane.relH ℂ) (Plane.relCusp ℂ) auxEval auxEval_h auxEval_cusp

/--
@isnad1 id=eq.0h1v.s9.ccba5dcdf5ce from=translated src=- shape=2b17ee42 vocab=06f50608
-/
@[simp] theorem auxToD_qvar (i : Fin 4) : auxToD (Plane.qvar ℂ i) = auxValues i := by
  change aeval auxValues (X i) = auxValues i
  exact aeval_X _ _

def liftValues : Fin 3 → D := ![dmap u, dmap v, dmap w]
def liftEval : MvPolynomial (Fin 3) B →ₐ[ℂ] D := aevalTower auxToD liftValues

/--
@isnad1 id=eq.0h0v.s10.212c11c370af from=translated src=- shape=bb9906b6 vocab=e0607af5
-/
theorem liftEval_x : liftEval (Lifting.relX hB xB) = 0 := by
  simp [liftEval, Lifting.relX, liftValues, auxValues, x]

/--
@isnad1 id=eq.0h0v.s10.b50fd718a38f from=translated src=- shape=bb9906b6 vocab=4a2e097e
-/
theorem liftEval_y : liftEval (Lifting.relY hB yB) = 0 := by
  simp [liftEval, Lifting.relY, liftValues, auxValues, y]

/--
@isnad1 id=eq.0h0v.s10.80ebb0de678a from=translated src=- shape=bb9906b6 vocab=a98a6008
-/
theorem liftEval_s : liftEval (Lifting.relS hB sB) = 0 := by
  simp [liftEval, Lifting.relS, liftValues, auxValues, s]

def toOriginal : L →ₐ[ℂ] D :=
  lift_triple (Lifting.relX hB xB) (Lifting.relY hB yB) (Lifting.relS hB sB)
    liftEval liftEval_x liftEval_y liftEval_s

/--
@isnad1 id=eq.0h1v.s10.3ed28a98571a from=translated src=- shape=d6783b79 vocab=2773a6ec
-/
@[simp] theorem toOriginal_lvar (i : Fin 3) : toOriginal (lvar i) = liftValues i := by
  change aevalTower auxToD liftValues (X i) = liftValues i
  exact aevalTower_X _ _ _

/--
@isnad1 id=eq.0h1v.s11.0933e5e5018e from=translated src=- shape=fd2727ee vocab=e0f0ea35
-/
@[simp] theorem toOriginal_lcoef (b : B) : toOriginal (lcoef b) = auxToD b := by
  change aevalTower auxToD liftValues (C b) = auxToD b
  simp

def originalValues : Fin 4 → L := ![lcoef hB, lvar 0, lvar 1, lvar 2]
def originalEval : R →ₐ[ℂ] L := aeval originalValues

/--
@isnad1 id=eq.0h0v.s11.14e99a1cb93b from=translated src=- shape=eb8c235c vocab=0d9b234a
-/
@[simp] theorem originalEval_h : originalEval h = lcoef hB := by
  simp [originalEval, originalValues, h]
/--
@isnad1 id=eq.0h0v.s10.04514cd21894 from=translated src=- shape=0afde4ee vocab=2c21d45a
-/
@[simp] theorem originalEval_u : originalEval u = lvar 0 := by
  simp [originalEval, originalValues, u]
/--
@isnad1 id=eq.0h0v.s10.be059829d34e from=translated src=- shape=0afde4ee vocab=cee2391f
-/
@[simp] theorem originalEval_v : originalEval v = lvar 1 := by
  simp [originalEval, originalValues, v]
/--
@isnad1 id=eq.0h0v.s10.ca0d2294ebb3 from=translated src=- shape=0afde4ee vocab=87b565d2
-/
@[simp] theorem originalEval_w : originalEval w = lvar 2 := by
  simp [originalEval, originalValues, w]

/--
@isnad1 id=eq.0h0v.s11.78223cb11c47 from=translated src=- shape=eb8c235c vocab=53cc42cd
-/
@[simp] theorem originalEval_x : originalEval x = lcoef xB := by
  simpa [x, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).1
/--
@isnad1 id=eq.0h0v.s11.8ea51966403c from=translated src=- shape=eb8c235c vocab=3f823083
-/
@[simp] theorem originalEval_y : originalEval y = lcoef yB := by
  simpa [y, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).2.1
/--
@isnad1 id=eq.0h0v.s11.6441a1858695 from=translated src=- shape=eb8c235c vocab=d0dd5528
-/
@[simp] theorem originalEval_s : originalEval s = lcoef sB := by
  simpa [s, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).2.2

/--
@isnad1 id=eq.0h0v.s10.adbe261744ed from=translated src=- shape=8cc970ed vocab=ac4abd83
-/
theorem originalEval_F : originalEval F = 0 := by
  have hh : hB = 1+P xB yB sB := Plane.relation_h ℂ
  have he : hB-P xB yB sB-1 = 0 := by rw [hh]; ring
  simpa [F, p] using congrArg lcoef he

def fromOriginal : D →ₐ[ℂ] L := by
  have hi : Ideal.span {F} ≤ RingHom.ker originalEval := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact originalEval_F
  exact Ideal.Quotient.liftₐ _ originalEval (fun z hz => hi hz)

/--
@isnad1 id=eq.0h1v.s11.ffda8bdafb67 from=translated src=- shape=fd2727ee vocab=24ea712d
-/
@[simp] theorem fromOriginal_dmap (f : R) : fromOriginal (dmap f) = originalEval f := rfl

/--
@isnad1 id=eq.0h0v.s10.371879fb1868 from=translated src=- shape=beae8cac vocab=68e709ea
-/
theorem to_from : toOriginal.comp fromOriginal = AlgHom.id ℂ D := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change toOriginal (fromOriginal (dmap (X i))) = dmap (X i)
  rw [fromOriginal_dmap]
  fin_cases i <;> simp [originalEval, originalValues, auxValues, liftValues, h, u, v, w]

/--
@isnad1 id=eq.0h0v.s10.70159b48b594 from=translated src=- shape=9eaf15bf vocab=b48117c5
-/
theorem from_auxToD : fromOriginal.comp auxToD = lcoef := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fromOriginal (auxToD (Plane.qvar ℂ i)) = lcoef (Plane.qvar ℂ i)
  rw [auxToD_qvar]
  fin_cases i <;> simp [auxValues]

/--
@isnad1 id=eq.0h0v.s11.d2ee3d210bf4 from=translated src=- shape=beae8cac vocab=68e709ea
-/
theorem from_to : fromOriginal.comp toOriginal = AlgHom.id ℂ L := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro b
    change fromOriginal (toOriginal (lcoef b)) = lcoef b
    rw [toOriginal_lcoef]
    exact AlgHom.congr_fun from_auxToD b
  · intro i
    change fromOriginal (toOriginal (lvar i)) = lvar i
    rw [toOriginal_lvar]
    fin_cases i <;> simp [liftValues]

def eliminationEquiv : L ≃ₐ[ℂ] D :=
  AlgEquiv.ofAlgHom toOriginal fromOriginal to_from from_to

end AbhyankarSathaye.Presentation

end

end OAI
