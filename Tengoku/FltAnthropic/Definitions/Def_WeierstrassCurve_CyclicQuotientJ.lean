import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_Velu
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VeluPointMap2
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_OddOrderSummingSet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

section XData

variable {R : Type*} [CommRing R] (V : WeierstrassCurve R)

def xVeluT (x : R) : R := 6 * x ^ 2 + V.b₂ * x + V.b₄

def xVeluU (x : R) : R := 4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆

def xVeluW (x : R) : R := V.xVeluU x + x * V.xVeluT x

/--
@isnad1 id=eq.0h4v.s4.f00da58e239e from=translated src=- shape=ce2bbaa5 vocab=cd462176
-/
theorem xVeluT_eq_veluT (x y : R) : V.xVeluT x = V.veluT x y := by
  rw [xVeluT, veluT_eq]

/--
@isnad1 id=eq.1h4v.s5.06855ab75425 from=translated src=- shape=8e895e90 vocab=07eff99f
-/
theorem xVeluU_eq_veluU {x y : R} (h : V.toAffine.Equation x y) : V.xVeluU x = V.veluU x y := by
  rw [V.veluU_eq_Ψ₂Sq_eval h, xVeluU, Ψ₂Sq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]

/--
@isnad1 id=eq.1h4v.s5.33ea7faf3bca from=translated src=- shape=8e895e90 vocab=4dc6ac06
-/
theorem xVeluW_eq_veluW {x y : R} (h : V.toAffine.Equation x y) : V.xVeluW x = V.veluW x y := by
  rw [xVeluW, veluW, V.xVeluU_eq_veluU h, V.xVeluT_eq_veluT x y]

end XData

section Field

variable {L : Type*} [Field L]

def absSum (X : Set L) (g : L → L) : L :=
  haveI := Classical.dec X.Finite
  if X.Finite then ∑ᶠ x ∈ X, g x else 0

/--
@isnad1 id=eq.1h3v.s5.dafee9b87299 from=translated src=- shape=25e82959 vocab=01fee4e6
-/
theorem absSum_of_finite {X : Set L} (hX : X.Finite) (g : L → L) :
    absSum X g = ∑ x ∈ hX.toFinset, g x := by
  rw [absSum, ite_eq_left hX, finsum_mem_eq_finite_toFinset_sum g hX]

/--
@isnad1 id=eq.1h3v.s5.1d10bc291fb0 from=translated src=- shape=84b921f4 vocab=6e666de1
-/
theorem absSum_of_infinite {X : Set L} (hX : X.Infinite) (g : L → L) : absSum X g = 0 := by
  rw [absSum, ite_eq_right hX]

def xVeluCurve (V : WeierstrassCurve L) (X : Set L) : WeierstrassCurve L where
  a₁ := V.a₁
  a₂ := V.a₂
  a₃ := V.a₃
  a₄ := V.a₄ - 5 * absSum X V.xVeluT
  a₆ := V.a₆ - V.b₂ * absSum X V.xVeluT - 7 * absSum X V.xVeluW

def xVeluX (V : WeierstrassCurve L) (X : Set L) (x : L) : L :=
  x + absSum X fun x₀ => V.xVeluT x₀ / (x - x₀) + V.xVeluU x₀ / (x - x₀) ^ 2

/--
@isnad1 id=eq.0h3v.s4.f9b015b94d58 from=translated src=- shape=cc5db9fa vocab=632ad26f
-/
@[simp] theorem xVeluCurve_a₁ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₁ = V.a₁ := rfl
/--
@isnad1 id=eq.0h3v.s4.8972199ff41a from=translated src=- shape=cc5db9fa vocab=e1c46902
-/
@[simp] theorem xVeluCurve_a₂ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₂ = V.a₂ := rfl
/--
@isnad1 id=eq.0h3v.s4.f694d87f6ce7 from=translated src=- shape=cc5db9fa vocab=9d5f41b2
-/
@[simp] theorem xVeluCurve_a₃ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₃ = V.a₃ := rfl
/--
@isnad1 id=eq.0h3v.s6.7a8c7d691224 from=translated src=- shape=5262e4d5 vocab=268c84bb
-/
theorem xVeluCurve_a₄ (V : WeierstrassCurve L) (X : Set L) :
    (V.xVeluCurve X).a₄ = V.a₄ - 5 * absSum X V.xVeluT := rfl
/--
@isnad1 id=eq.0h3v.s7.d5262d786f0a from=translated src=- shape=5e67cac6 vocab=367ce4e2
-/
theorem xVeluCurve_a₆ (V : WeierstrassCurve L) (X : Set L) :
    (V.xVeluCurve X).a₆ = V.a₆ - V.b₂ * absSum X V.xVeluT - 7 * absSum X V.xVeluW := rfl

def twoTorsionY (V : WeierstrassCurve L) (x₀ : L) : L := -(V.a₁ * x₀ + V.a₃) / 2

def xVeluG (V : WeierstrassCurve L) (x₀ : L) : L := V.veluGx x₀ (V.twoTorsionY x₀)

def twoVeluCurve (V : WeierstrassCurve L) (X : Set L) : WeierstrassCurve L where
  a₁ := V.a₁
  a₂ := V.a₂
  a₃ := V.a₃
  a₄ := V.a₄ - 5 * absSum X V.xVeluG
  a₆ := V.a₆ - V.b₂ * absSum X V.xVeluG - 7 * absSum X fun x => x * V.xVeluG x

def twoVeluX (V : WeierstrassCurve L) (X : Set L) (x : L) : L :=
  x + absSum X fun x₀ => V.xVeluG x₀ / (x - x₀)

/--
@isnad1 id=eq.0h3v.s4.c3ff6d685bf7 from=translated src=- shape=cc5db9fa vocab=73960b4d
-/
@[simp] theorem twoVeluCurve_a₁ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₁ = V.a₁ := rfl
/--
@isnad1 id=eq.0h3v.s4.5de323fe90e3 from=translated src=- shape=cc5db9fa vocab=81f174b0
-/
@[simp] theorem twoVeluCurve_a₂ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₂ = V.a₂ := rfl
/--
@isnad1 id=eq.0h3v.s4.857c499b199c from=translated src=- shape=cc5db9fa vocab=d3ba033d
-/
@[simp] theorem twoVeluCurve_a₃ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₃ = V.a₃ := rfl
/--
@isnad1 id=eq.0h3v.s6.9aeaeb35eb1e from=translated src=- shape=5262e4d5 vocab=7670784e
-/
theorem twoVeluCurve_a₄ (V : WeierstrassCurve L) (X : Set L) :
    (V.twoVeluCurve X).a₄ = V.a₄ - 5 * absSum X V.xVeluG := rfl
/--
@isnad1 id=eq.0h3v.s7.7ef2f1973ec7 from=translated src=- shape=c08379c8 vocab=4224b9f4
-/
theorem twoVeluCurve_a₆ (V : WeierstrassCurve L) (X : Set L) :
    (V.twoVeluCurve X).a₆ = V.a₆ - V.b₂ * absSum X V.xVeluG - 7 * absSum X fun x => x * V.xVeluG x :=
  rfl

variable [DecidableEq L]

def kernelXSet (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) : Set L :=
  (fun P => P.coordsOrZero.1) '' {P | P ∈ H ∧ P ≠ 0 ∧ ℓ • P = 0}

def coKernelXSet (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) : Set L :=
  (fun P => P.coordsOrZero.1) '' {P | P ∈ H ∧ ℓ • P ≠ 0}

def stepCurve (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    WeierstrassCurve L :=
  if ℓ = 2 then V.twoVeluCurve (V.kernelXSet H 2) else V.xVeluCurve (V.kernelXSet H ℓ)

def stepX (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) (x : L) : L :=
  if ℓ = 2 then V.twoVeluX (V.kernelXSet H 2) x else V.xVeluX (V.kernelXSet H ℓ) x

/--
@isnad1 id=eq.0h3v.s6.df710e6352f4 from=translated src=- shape=30f07e7d vocab=dac311c3
-/
theorem stepCurve_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.stepCurve H 2 = V.twoVeluCurve (V.kernelXSet H 2) :=
  ite_eq_left rfl

/--
@isnad1 id=eq.1h4v.s6.01e59dab222a from=translated src=- shape=f1ac4f44 vocab=6cc904a0
-/
theorem stepCurve_of_ne_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) {ℓ : ℕ}
    (hℓ : ℓ ≠ 2) : V.stepCurve H ℓ = V.xVeluCurve (V.kernelXSet H ℓ) :=
  ite_eq_right hℓ

/--
@isnad1 id=eq.0h4v.s6.3c8c98e2ed2f from=translated src=- shape=e556b7ec vocab=fdaf13fd
-/
theorem stepX_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (x : L) :
    V.stepX H 2 x = V.twoVeluX (V.kernelXSet H 2) x :=
  ite_eq_left rfl

/--
@isnad1 id=eq.1h5v.s6.f2260c53f6d6 from=translated src=- shape=6d668dd9 vocab=5e6dcc40
-/
theorem stepX_of_ne_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) {ℓ : ℕ}
    (hℓ : ℓ ≠ 2) (x : L) : V.stepX H ℓ x = V.xVeluX (V.kernelXSet H ℓ) x :=
  ite_eq_right hℓ

def subgroupOfX (V' : WeierstrassCurve L) (Y : Set L) : AddSubgroup V'.toAffine.Point :=
  AddSubgroup.closure {P | P ≠ 0 ∧ P.coordsOrZero.1 ∈ Y}

def stepSubgroup (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    AddSubgroup (V.stepCurve H ℓ).toAffine.Point :=
  subgroupOfX (V.stepCurve H ℓ) (V.stepX H ℓ '' V.coKernelXSet H ℓ)

variable (L) in

abbrev CQJState : Type _ := (Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) × ℕ

def cqjStep (s : CQJState L) : CQJState L :=
  ⟨⟨s.1.1.stepCurve s.1.2 s.2.minFac, s.1.1.stepSubgroup s.1.2 s.2.minFac⟩, s.2 / s.2.minFac⟩

def cqjIterate (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) : CQJState L :=
  cqjStep^[N.primeFactorsList.length] ⟨⟨V, H⟩, N⟩

def cyclicQuotientCurve (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    WeierstrassCurve L :=
  (V.cqjIterate H N).1.1

def cyclicQuotientJ (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) : L :=
  (V.cyclicQuotientCurve H N).c₄ ^ 3 / (V.cyclicQuotientCurve H N).Δ

/--
@isnad1 id=eq.0h4v.s7.ccff5be934bf from=translated src=- shape=e6eab78c vocab=724a6707
-/
theorem cqjIterate_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    V.cqjIterate H N = cqjStep^[N.primeFactorsList.length] ⟨⟨V, H⟩, N⟩ := rfl

/--
@isnad1 id=eq.0h4v.s6.e43f3b555133 from=translated src=- shape=63c0d738 vocab=499e1d30
-/
theorem cyclicQuotientCurve_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point)
    (N : ℕ) : V.cyclicQuotientCurve H N = (V.cqjIterate H N).1.1 := rfl

/--
@isnad1 id=eq.0h4v.s6.f80d2e122323 from=translated src=- shape=d63c461d vocab=6d8a8776
-/
theorem cyclicQuotientJ_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    V.cyclicQuotientJ H N =
      (V.cyclicQuotientCurve H N).c₄ ^ 3 / (V.cyclicQuotientCurve H N).Δ := rfl

/--
@isnad1 id=eq.0h4v.s7.6aef90adee25 from=translated src=- shape=274b2c6e vocab=62efc2f2
-/
theorem cqjStep_apply (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (n : ℕ) :
    cqjStep ⟨⟨V, H⟩, n⟩ =
      ⟨⟨V.stepCurve H n.minFac, V.stepSubgroup H n.minFac⟩, n / n.minFac⟩ := rfl

/--
@isnad1 id=eq.0h3v.s6.dee479bf1024 from=translated src=- shape=b6031420 vocab=5b2d0401
-/
theorem cqjIterate_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cqjIterate H 1 = ⟨⟨V, H⟩, 1⟩ := by
  simp [cqjIterate, Nat.primeFactorsList_one]

/--
@isnad1 id=eq.0h3v.s5.e27670b49f0a from=translated src=- shape=a02d8e28 vocab=fc8cf427
-/
theorem cyclicQuotientCurve_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cyclicQuotientCurve H 1 = V := by
  rw [cyclicQuotientCurve_def, cqjIterate_one]

/--
@isnad1 id=eq.0h3v.s6.89f3eac2e8b2 from=translated src=- shape=d2d71a3d vocab=e2ec2f78
-/
theorem cyclicQuotientJ_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cyclicQuotientJ H 1 = V.c₄ ^ 3 / V.Δ := by
  rw [cyclicQuotientJ_def, cyclicQuotientCurve_one]

/--
@isnad1 id=eq.1h1v.s5.b9eae422936b from=translated src=- shape=b8fe98b3 vocab=68291889
-/
theorem length_primeFactorsList_eq_succ {N : ℕ} (hN : 2 ≤ N) :
    N.primeFactorsList.length = (N / N.minFac).primeFactorsList.length + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  rw [Nat.primeFactorsList, List.length_cons]

/--
@isnad1 id=eq.1h4v.s6.96e5e39e2a7f from=translated src=- shape=8b6117a4 vocab=2191b7ff
-/
theorem cqjIterate_eq_of_two_le (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point)
    {N : ℕ} (hN : 2 ≤ N) :
    V.cqjIterate H N =
      (V.stepCurve H N.minFac).cqjIterate (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cqjIterate, length_primeFactorsList_eq_succ hN, Function.iterate_succ_apply]
  rfl

/--
@isnad1 id=eq.1h4v.s6.7d7fdf915dad from=translated src=- shape=1479d4a1 vocab=9cab690e
-/
theorem cyclicQuotientCurve_eq_of_two_le (V : WeierstrassCurve L)
    (H : AddSubgroup V.toAffine.Point) {N : ℕ} (hN : 2 ≤ N) :
    V.cyclicQuotientCurve H N =
      (V.stepCurve H N.minFac).cyclicQuotientCurve (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cyclicQuotientCurve_def, cqjIterate_eq_of_two_le V H hN, cyclicQuotientCurve_def]

/--
@isnad1 id=eq.1h4v.s6.617885c6994b from=translated src=- shape=c5edf0ae vocab=6bd19d9b
-/
theorem cyclicQuotientJ_eq_of_two_le (V : WeierstrassCurve L)
    (H : AddSubgroup V.toAffine.Point) {N : ℕ} (hN : 2 ≤ N) :
    V.cyclicQuotientJ H N =
      (V.stepCurve H N.minFac).cyclicQuotientJ (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cyclicQuotientJ_def, cyclicQuotientCurve_eq_of_two_le V H hN, cyclicQuotientJ_def]

/--
@isnad1 id=eq.0h4v.s6.c7b05a0eaae0 from=translated src=- shape=169310cf vocab=e3182530
-/
theorem cyclicQuotientJ_eq_j (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ)
    [(V.cyclicQuotientCurve H N).IsElliptic] :
    V.cyclicQuotientJ H N = (V.cyclicQuotientCurve H N).j := by
  rw [cyclicQuotientJ_def, WeierstrassCurve.j, div_eq_mul_inv, mul_comm, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ']

end Field

end WeierstrassCurve

end
