import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open MvPolynomial

namespace IncidenceSystem

inductive Var (g e m' : ℕ) : Type
  | u : Fin g → Var g e m'
  | w : Fin g → Fin e → Fin (m' + 1) → Var g e m'
  | σ : Option (Fin (g * m')) → Fin g → Fin (m' + 1) → Var g e m'
  | c : Fin (g * m') → Var g e m'
  deriving DecidableEq, Fintype

variable (g e m' : ℕ) (A : Type*) [CommRing A]

structure Data where

  G : Fin g → Fin e → MvPolynomial (Option (Fin e)) A

  p : Option (Fin (g * m')) → Fin g → MvPolynomial (Option (Fin e)) A

  s : Option (Fin (g * m')) → Fin g → MvPolynomial (Option (Fin e)) A

  u₀ : Fin g → A

  w₀ : Fin g → Fin e → Fin (m' + 1) → A

  σ₀ : Option (Fin (g * m')) → Fin g → Fin (m' + 1) → A

variable {g e m' A}

abbrev R (g e m' : ℕ) (A : Type*) [CommRing A] := MvPolynomial (Var g e m') A

noncomputable def xser (i : Fin g) : Polynomial (R g e m' A) :=
  Polynomial.C (X (Var.u i)) + Polynomial.X

noncomputable def wser (i : Fin g) (j : Fin e) : Polynomial (R g e m' A) :=
  ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (X (Var.w i j r))

noncomputable def sser (k : Option (Fin (g * m'))) (i : Fin g) : Polynomial (R g e m' A) :=
  ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (X (Var.σ k i r))

noncomputable def coord (i : Fin g) : Option (Fin e) → Polynomial (R g e m' A) :=
  fun o => Option.elim o (xser i) (wser i)

noncomputable def subst (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) : Polynomial (R g e m' A) :=
  MvPolynomial.aeval (coord (m' := m') i) H

noncomputable def cc : Option (Fin (g * m')) → R g e m' A
  | none => 1
  | some k => X (Var.c k)

namespace Data

variable (D : Data g e m' A)

noncomputable def branch (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) : R g e m' A :=
  (subst i (D.G i j)).coeff r

noncomputable def inv (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) : R g e m' A :=
  (sser k i * subst i (D.s k i) - 1).coeff r

noncomputable def tc (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) : R g e m' A :=
  (subst i (D.p k i) * sser k i).coeff r

noncomputable def inc (i : Fin g) (r : Fin (m' + 1)) : R g e m' A :=
  ∑ k : Option (Fin (g * m')), cc k * D.tc k i r

noncomputable def system : Var g e m' → R g e m' A
  | Var.w i j r => D.branch i j r
  | Var.σ k i r => D.inv k i r
  | Var.u i => D.inc i (Fin.last m')
  | Var.c k => D.inc (finProdFinEquiv.symm k).1 (Fin.castSucc (finProdFinEquiv.symm k).2)

def centre : Var g e m' → A
  | Var.u i => D.u₀ i
  | Var.w i j r => D.w₀ i j r
  | Var.σ k i r => D.σ₀ k i r
  | Var.c _ => 0

noncomputable def jacobian (pt : Var g e m' → A) : Matrix (Var g e m') (Var g e m') A :=
  Matrix.of fun v v' => MvPolynomial.eval pt (MvPolynomial.pderiv v' (D.system v))

noncomputable def tcMatrix (pt : Var g e m' → A) : Matrix (Fin (g * m')) (Fin (g * m')) A :=
  Matrix.of fun k k' => MvPolynomial.eval pt
    (D.tc (some k') (finProdFinEquiv.symm k).1 (Fin.castSucc (finProdFinEquiv.symm k).2))

def ptCoord (pt : Var g e m' → A) (i : Fin g) : Option (Fin e) → A :=
  fun o => Option.elim o (pt (Var.u i)) (fun j => pt (Var.w i j 0))

noncomputable def dG (pt : Var g e m' → A) (i : Fin g) (j : Fin e) : A :=
  MvPolynomial.eval (ptCoord pt i) (MvPolynomial.pderiv (some j) (D.G i j))

noncomputable def sVal (pt : Var g e m' → A) (k : Option (Fin (g * m'))) (i : Fin g) : A :=
  MvPolynomial.eval (ptCoord pt i) (D.s k i)

end Data

section Eval

variable (pt : Var g e m' → A)

noncomputable def wpoly (i : Fin g) (j : Fin e) : Polynomial A :=
  ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (pt (Var.w i j r))

noncomputable def spoly (k : Option (Fin (g * m'))) (i : Fin g) : Polynomial A :=
  ∑ r : Fin (m' + 1), Polynomial.monomial (r : ℕ) (pt (Var.σ k i r))

noncomputable def coordAt (i : Fin g) : Option (Fin e) → Polynomial A :=
  fun o => Option.elim o (Polynomial.C (pt (Var.u i)) + Polynomial.X) (wpoly pt i)

noncomputable def substAt (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) : Polynomial A :=
  MvPolynomial.aeval (coordAt pt i) H

/--
@isnad1 id=eq.0h6v.s7.f587fecf8e90 from=translated src=- shape=19887826 vocab=ac8c125e
-/
theorem map_eval_xser (i : Fin g) :
    (xser (e := e) (m' := m') i).map (MvPolynomial.eval pt) = Polynomial.C (pt (Var.u i)) + Polynomial.X := by
  simp [xser]

/--
@isnad1 id=eq.0h7v.s6.153ede3d3f39 from=translated src=- shape=a6dc5092 vocab=ca1507f4
-/
theorem map_eval_wser (i : Fin g) (j : Fin e) :
    (wser (m' := m') i j).map (MvPolynomial.eval pt) = wpoly pt i j := by
  simp [wser, wpoly, Polynomial.map_sum]

/--
@isnad1 id=eq.0h7v.s6.3b945891ab50 from=translated src=- shape=57d447b8 vocab=c66311e4
-/
theorem map_eval_sser (k : Option (Fin (g * m'))) (i : Fin g) :
    (sser (e := e) k i).map (MvPolynomial.eval pt) = spoly pt k i := by
  simp [sser, spoly, Polynomial.map_sum]

/--
@isnad1 id=eq.0h7v.s6.55c742f08092 from=translated src=- shape=d4d2292a vocab=f87888c7
-/
theorem map_eval_subst (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) :
    (subst (m' := m') i H).map (MvPolynomial.eval pt) = substAt pt i H := by
  change (Polynomial.mapAlgHom (MvPolynomial.aeval pt)) (MvPolynomial.aeval (coord i) H) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  unfold substAt
  congr 2
  funext o
  cases o with
  | none => simp [coord, coordAt, xser]
  | some j => simp [coord, coordAt, wser, wpoly]

variable (D : Data g e m' A)

/--
@isnad1 id=eq.0h9v.s7.f1433ddce1f0 from=translated src=- shape=3be786dd vocab=b6473a02
-/
theorem eval_branch (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.branch i j r) = (substAt pt i (D.G i j)).coeff r := by
  rw [Data.branch, ← Polynomial.coeff_map, map_eval_subst]

/--
@isnad1 id=eq.0h9v.s8.d4caeaec2d0c from=translated src=- shape=a2fbc375 vocab=00ee270b
-/
theorem eval_inv (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.inv k i r) = (spoly pt k i * substAt pt i (D.s k i) - 1).coeff r := by
  rw [Data.inv, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, map_eval_subst,
    map_eval_sser, Polynomial.map_one]

/--
@isnad1 id=eq.0h9v.s8.f7723fa6280c from=translated src=- shape=6c4d0f7d vocab=0e414e79
-/
theorem eval_tc (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.tc k i r) = (substAt pt i (D.p k i) * spoly pt k i).coeff r := by
  rw [Data.tc, ← Polynomial.coeff_map, Polynomial.map_mul, map_eval_subst, map_eval_sser]

/--
@isnad1 id=eq.0h8v.s8.26d5c006c8e4 from=translated src=- shape=942f8570 vocab=f55189b5
-/
theorem eval_inc (i : Fin g) (r : Fin (m' + 1)) :
    MvPolynomial.eval pt (D.inc i r) =
      (substAt pt i (D.p none i) * spoly pt none i).coeff r +
        ∑ k : Fin (g * m'), pt (Var.c k) * (substAt pt i (D.p (some k) i) * spoly pt (some k) i).coeff r := by
  rw [Data.inc, map_sum, Fintype.sum_option]
  simp [cc, eval_tc]

end Eval

namespace Data

variable (D : Data g e m' A) {B : Type*} [CommRing B] (f : A →+* B)

noncomputable def map : Data g e m' B where
  G i j := MvPolynomial.map f (D.G i j)
  p k i := MvPolynomial.map f (D.p k i)
  s k i := MvPolynomial.map f (D.s k i)
  u₀ i := f (D.u₀ i)
  w₀ i j r := f (D.w₀ i j r)
  σ₀ k i r := f (D.σ₀ k i r)

/--
@isnad1 id=eq.0h7v.s6.d353d19988ab from=translated src=- shape=9281184c vocab=3007d19e
-/
theorem map_centre : (D.map f).centre = f ∘ D.centre := by
  funext v; cases v <;> simp [centre, map]

/--
@isnad1 id=eq.0h7v.s7.53fcfc5b20a9 from=translated src=- shape=4151f963 vocab=619bcb69
-/
theorem map_xser (i : Fin g) :
    (xser (e := e) (m' := m') (A := A) i).map (MvPolynomial.map f) = xser i := by
  simp [xser]

/--
@isnad1 id=eq.0h8v.s7.9246b6a09b79 from=translated src=- shape=9880b2f3 vocab=81e532cb
-/
theorem map_wser (i : Fin g) (j : Fin e) :
    (wser (m' := m') (A := A) i j).map (MvPolynomial.map f) = wser i j := by
  simp [wser, Polynomial.map_sum]

/--
@isnad1 id=eq.0h8v.s7.d9a2075a43d6 from=translated src=- shape=a791b290 vocab=41755463
-/
theorem map_sser (k : Option (Fin (g * m'))) (i : Fin g) :
    (sser (e := e) (A := A) k i).map (MvPolynomial.map f) = sser k i := by
  simp [sser, Polynomial.map_sum]

/--
@isnad1 id=eq.0h8v.s8.62ce2e3d730b from=translated src=- shape=77da862c vocab=239fdd27
-/
theorem map_subst (i : Fin g) (H : MvPolynomial (Option (Fin e)) A) :
    (subst (m' := m') i H).map (MvPolynomial.map f) = subst i (MvPolynomial.map f H) := by
  unfold subst
  rw [← Polynomial.coe_mapRingHom, ← AlgHom.coe_toRingHom, ← RingHom.comp_apply,
    ← AlgHom.coe_toRingHom, ← RingHom.comp_apply]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro o
    cases o with
    | none => simp [coord, map_xser]
    | some j => simp [coord, map_wser]

/--
@isnad1 id=eq.0h10v.s8.1573cb5c7479 from=translated src=- shape=34620b0e vocab=6dce4bd0
-/
theorem map_branch (i : Fin g) (j : Fin e) (r : Fin (m' + 1)) :
    (D.map f).branch i j r = MvPolynomial.map f (D.branch i j r) := by
  rw [branch, branch, ← Polynomial.coeff_map, map_subst]; rfl

/--
@isnad1 id=eq.0h10v.s8.a4af49646723 from=translated src=- shape=4b76d976 vocab=a0c07b32
-/
theorem map_inv (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).inv k i r = MvPolynomial.map f (D.inv k i r) := by
  rw [inv, inv, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, map_subst, map_sser,
    Polynomial.map_one]; rfl

/--
@isnad1 id=eq.0h10v.s8.9047fe83cf0d from=translated src=- shape=4b76d976 vocab=e143d687
-/
theorem map_tc (k : Option (Fin (g * m'))) (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).tc k i r = MvPolynomial.map f (D.tc k i r) := by
  rw [tc, tc, ← Polynomial.coeff_map, Polynomial.map_mul, map_subst, map_sser]; rfl

/--
@isnad1 id=eq.0h9v.s8.235563262a16 from=translated src=- shape=3060f2f1 vocab=c018bf24
-/
theorem map_inc (i : Fin g) (r : Fin (m' + 1)) :
    (D.map f).inc i r = MvPolynomial.map f (D.inc i r) := by
  rw [inc, inc, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_tc]
  cases k <;> simp [cc]

/--
@isnad1 id=eq.0h8v.s8.e7b0377aa822 from=translated src=- shape=41060f8c vocab=ca0256f1
-/
theorem map_system (v : Var g e m') :
    (D.map f).system v = MvPolynomial.map f (D.system v) := by
  cases v <;> simp [system, map_branch, map_inv, map_inc]

/--
@isnad1 id=eq.0h6v.s8.977735aee3bf from=translated src=- shape=655d5db5 vocab=7203adf1
-/
theorem _root_.IncidenceSystem.eval_comp_map {ι : Type*} (pt : ι → A) (P : MvPolynomial ι A) :
    MvPolynomial.eval (f ∘ pt) (MvPolynomial.map f P) = f (MvPolynomial.eval pt P) := by
  rw [MvPolynomial.eval_map, show MvPolynomial.eval pt P = MvPolynomial.eval₂ (RingHom.id A) pt P from rfl,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]

/--
@isnad1 id=eq.0h8v.s7.09becf1ac425 from=translated src=- shape=0405ec0b vocab=df7b397a
-/
theorem map_jacobian (pt : Var g e m' → A) :
    (D.map f).jacobian (f ∘ pt) = (D.jacobian pt).map f := by
  ext v v'
  simp only [jacobian, Matrix.of_apply, Matrix.map_apply, map_system, MvPolynomial.pderiv_map,
    eval_comp_map]

/--
@isnad1 id=eq.0h8v.s7.911de25e8221 from=translated src=- shape=45123cd3 vocab=34540b4a
-/
theorem map_tcMatrix (pt : Var g e m' → A) :
    (D.map f).tcMatrix (f ∘ pt) = (D.tcMatrix pt).map f := by
  ext k k'
  simp only [tcMatrix, Matrix.of_apply, Matrix.map_apply, map_tc, eval_comp_map]

omit f in
/--
@isnad1 id=eq.0h8v.s7.4f6471dd3c6b from=translated src=- shape=539421cf vocab=3fcb583f
-/
theorem map_ptCoord (pt : Var g e m' → A) (i : Fin g) (f : A →+* B) :
    ptCoord (f ∘ pt) i = f ∘ ptCoord pt i := by
  funext o; cases o <;> rfl

/--
@isnad1 id=eq.0h10v.s7.e6cea8732fd9 from=translated src=- shape=f65dbaf6 vocab=d40d0099
-/
theorem map_dG (pt : Var g e m' → A) (i : Fin g) (j : Fin e) :
    (D.map f).dG (f ∘ pt) i j = f (D.dG pt i j) := by
  rw [dG, dG, map_ptCoord, ← eval_comp_map f, ← MvPolynomial.pderiv_map]; rfl

/--
@isnad1 id=eq.0h10v.s7.24bef0b1db00 from=translated src=- shape=d1a080d3 vocab=34615e1a
-/
theorem map_sVal (pt : Var g e m' → A) (k : Option (Fin (g * m'))) (i : Fin g) :
    (D.map f).sVal (f ∘ pt) k i = f (D.sVal pt k i) := by
  rw [sVal, sVal, map_ptCoord, ← eval_comp_map f]; rfl

end Data

end IncidenceSystem
