module

public import Tengoku.PshdLean.PshLines.FirstPass.HermitianGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric equality of chartwise differential forms

Only coefficients on the open chart targets represent a differential form.
`GeometricallyEq` forgets arbitrary extensions outside those targets. Its
quotient is optional: the representative API and all the properties below
already respect this relation. No coordinate naturality of exterior
differentiation is needed to prove locality under this equality.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PshLines.FirstPass

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace SmoothRealForm

/-- Equality of geometric forms, independent of off-target extensions.-/
def GeometricallyEq (a b : SmoothRealForm n M k) : Prop :=
  ∀ e, EqOn (a.coeff e) (b.coeff e) e.val.target

/--
@isnad1 id=geometri.0h4v.s6.fb50278366f1 from=translated src=- shape=8b370a6c vocab=81e67bb5
-/
theorem GeometricallyEq.refl (a : SmoothRealForm n M k) : a.GeometricallyEq a :=
  fun _ _ _ => rfl

/--
@isnad1 id=geometri.1h5v.s6.2846c4622283 from=translated src=- shape=25c9d66e vocab=81e67bb5
-/
theorem GeometricallyEq.symm {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) : b.GeometricallyEq a :=
  fun e => (h e).symm

/--
@isnad1 id=geometri.2h6v.s6.b9ea850b2fcf from=translated src=- shape=da79565a vocab=81e67bb5
-/
theorem GeometricallyEq.trans {a b c : SmoothRealForm n M k}
    (hab : a.GeometricallyEq b) (hbc : b.GeometricallyEq c) : a.GeometricallyEq c :=
  fun e => (hab e).trans (hbc e)

/--
@isnad1 id=equivale.0h3v.s6.736bdacdabe9 from=translated src=- shape=9a5e940a vocab=aaf7ec9f
-/
theorem geometricallyEq_equivalence :
    Equivalence (GeometricallyEq (n := n) (M := M) (k := k)) :=
  ⟨GeometricallyEq.refl, GeometricallyEq.symm, GeometricallyEq.trans⟩

/-- Targetwise equality is exactly equality of all geometric evaluations.
@isnad1 id=iff.0h5v.s10.80b2e7594039 from=translated src=- shape=34068b04 vocab=afc3ddaa
-/
theorem geometricallyEq_iff {a b : SmoothRealForm n M k} :
    a.GeometricallyEq b ↔
      ∀ e z, z ∈ e.val.target → ∀ v, a.coeff e z v = b.coeff e z v := by
  constructor
  · intro h e z hz v
    rw [h e hz]
  · intro h e z hz
    ext v
    exact h e z hz v

/-- Open targets make equal coefficients equal as germs at every target point.
@isnad1 id=eventual.2h7v.s9.d02ddaadb090 from=translated src=- shape=b36b3008 vocab=4a2b7a63
-/
theorem GeometricallyEq.coeff_eventuallyEq {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) : a.coeff e =ᶠ[𝓝 z] b.coeff e :=
  eventually_of_mem (e.val.open_target.mem_nhds hz) (fun _ hw => h e hw)

/-- Exterior differentiation is local, even though coefficients are total functions.
@isnad1 id=eqon.1h6v.s9.b86c85fb5065 from=translated src=- shape=55a60d48 vocab=ed356bb4
-/
theorem GeometricallyEq.extDeriv_eqOn {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) (e : ComplexChart n M) :
    EqOn (extDeriv (a.coeff e)) (extDeriv (b.coeff e)) e.val.target :=
  fun _ hz => (h.coeff_eventuallyEq e hz).extDeriv_eq

/--
@isnad1 id=iff.1h5v.s6.6618369c018e from=translated src=- shape=43e6a366 vocab=0c58eb9b
-/
theorem GeometricallyEq.isClosed_iff {a b : SmoothRealForm n M k}
    (h : a.GeometricallyEq b) : a.IsClosed ↔ b.IsClosed := by
  constructor
  · intro ha e z hz
    rw [← h.extDeriv_eqOn e hz]
    exact ha e z hz
  · intro hb e z hz
    rw [h.extDeriv_eqOn e hz]
    exact hb e z hz

/-- Type `(1,1)` for a given global real two-form.-/
def IsTypeOneOne (a : SmoothRealForm n M 2) : Prop :=
  ∀ e z, z ∈ e.val.target → IsOneOne (a.coeff e z)

/-- The usual semipositivity cone, evaluated on actual complex tangent lines.-/
def IsSemipositive (a : SmoothRealForm n M 2) : Prop :=
  ∀ e z, z ∈ e.val.target → ∀ v, 0 ≤ a.coeff e z ![v, Complex.I • v]

/--
@isnad1 id=iff.1h4v.s6.43424aeabbcb from=translated src=- shape=d9f674b9 vocab=dde7e03e
-/
theorem GeometricallyEq.isTypeOneOne_iff {a b : SmoothRealForm n M 2}
    (h : a.GeometricallyEq b) : a.IsTypeOneOne ↔ b.IsTypeOneOne := by
  unfold IsTypeOneOne
  exact forall_congr' fun e => forall_congr' fun z =>
    forall_congr' fun hz => by rw [h e hz]

/--
@isnad1 id=iff.1h4v.s6.d58fe655ae67 from=translated src=- shape=d9f674b9 vocab=fd26128f
-/
theorem GeometricallyEq.isSemipositive_iff {a b : SmoothRealForm n M 2}
    (h : a.GeometricallyEq b) : a.IsSemipositive ↔ b.IsSemipositive := by
  unfold IsSemipositive
  exact forall_congr' fun e => forall_congr' fun z =>
    forall_congr' fun hz => by rw [h e hz]

/--
@isnad1 id=iff.1h4v.s6.746e23848ad8 from=translated src=- shape=d9f674b9 vocab=641aea7e
-/
theorem GeometricallyEq.isHermitian_iff {a b : SmoothRealForm n M 2}
    (h : a.GeometricallyEq b) : a.IsHermitian ↔ b.IsHermitian := by
  unfold IsHermitian
  exact forall_congr' fun e => forall_congr' fun z =>
    forall_congr' fun hz => by rw [h e hz]

/--
@isnad1 id=iff.1h4v.s6.81628174df96 from=translated src=- shape=d9f674b9 vocab=99d01cf0
-/
theorem GeometricallyEq.isKahler_iff {a b : SmoothRealForm n M 2}
    (h : a.GeometricallyEq b) : a.IsKahler ↔ b.IsKahler :=
  and_congr h.isHermitian_iff h.isClosed_iff

/-- An explicit setoid, without changing Lean's equality of representatives.-/
def geometricSetoid : Setoid (SmoothRealForm n M k) where
  r := GeometricallyEq
  iseqv := geometricallyEq_equivalence

end SmoothRealForm

/-- Geometric forms with off-target coefficient extensions identified.-/
def GeometricRealForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (k : ℕ) :=
  Quotient (SmoothRealForm.geometricSetoid (n := n) (M := M) (k := k))

namespace GeometricRealForm

def ofRepresentative (a : SmoothRealForm n M k) : GeometricRealForm n M k :=
  Quotient.mk _ a

/--
@isnad1 id=iff.0h5v.s6.2d52acb8ef9d from=translated src=- shape=62907baf vocab=16fcf8f0
-/
theorem ofRepresentative_eq_iff (a b : SmoothRealForm n M k) :
    ofRepresentative a = ofRepresentative b ↔ a.GeometricallyEq b :=
  Quotient.eq

/-- Closedness descends to geometric forms.-/
def IsClosed (a : GeometricRealForm n M k) : Prop :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid) SmoothRealForm.IsClosed
    (fun _ _ h => propext h.isClosed_iff) a

/-- Hermitian positivity descends to geometric forms.-/
def IsHermitian (a : GeometricRealForm n M 2) : Prop :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid) SmoothRealForm.IsHermitian
    (fun _ _ h => propext h.isHermitian_iff) a

/-- Kählerness descends without asserting the existence of any Kähler form.-/
def IsKahler (a : GeometricRealForm n M 2) : Prop :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid) SmoothRealForm.IsKahler
    (fun _ _ h => propext h.isKahler_iff) a

/--
@isnad1 id=iff.0h4v.s6.73313c03cfe6 from=translated src=- shape=35bd8682 vocab=7476dc73
-/
@[simp] theorem isClosed_ofRepresentative (a : SmoothRealForm n M k) :
    (ofRepresentative a).IsClosed ↔ a.IsClosed := Iff.rfl

/--
@isnad1 id=iff.0h3v.s6.d655dedefb3d from=translated src=- shape=b3a2cce1 vocab=bd28ee55
-/
@[simp] theorem isHermitian_ofRepresentative (a : SmoothRealForm n M 2) :
    (ofRepresentative a).IsHermitian ↔ a.IsHermitian := Iff.rfl

/--
@isnad1 id=iff.0h3v.s6.c272c764953e from=translated src=- shape=b3a2cce1 vocab=225d1365
-/
@[simp] theorem isKahler_ofRepresentative (a : SmoothRealForm n M 2) :
    (ofRepresentative a).IsKahler ↔ a.IsKahler := Iff.rfl

end GeometricRealForm

end

end PshLines.FirstPass
