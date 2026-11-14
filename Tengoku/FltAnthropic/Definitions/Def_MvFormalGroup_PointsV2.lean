import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2
import Tengoku.Seed.RingTheory.AdicCompletion.Topology
import Tengoku.Seed.RingTheory.Finiteness.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace Tengoku.FltAnthropic.MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section AdicEval

variable {S : Type*} [CommRing S] [Algebra R S] {S' : Type*} [CommRing S'] [Algebra R S']
  {σ : Type*}

def adicEval (J : Ideal S) (x : σ → S) (f : MvPowerSeries σ R) : S :=
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  MvPowerSeries.eval₂ (algebraMap R S) x f

private theorem isTopologicallyNilpotent_of_mem_radical (J : Ideal S) {a : S}
    (ha : a ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    IsTopologicallyNilpotent a := by
  letI : TopologicalSpace S := J.adicTopology
  obtain ⟨k, hk⟩ := ha
  show Filter.Tendsto (a ^ ·) Filter.atTop (nhds 0)
  rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
  intro n _
  filter_upwards [Filter.eventually_ge_atTop (k * n)] with m hm
  obtain ⟨r, rfl⟩ : ∃ r, m = k * n + r := ⟨m - k * n, by omega⟩
  rw [pow_add, pow_mul]
  exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk n))

private theorem hasEval_of_mem_radical [Finite σ] (J : Ideal S) {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    MvPowerSeries.HasEval x := by
  letI : TopologicalSpace S := J.adicTopology
  refine ⟨fun s => isTopologicallyNilpotent_of_mem_radical J (hx s), ?_⟩
  rw [Filter.cofinite_eq_bot]
  exact Filter.tendsto_bot

/--
@isnad1 id=eq.0h6v.s5.bcbb68f1a948 from=translated src=- shape=201ecd2a vocab=6bf9215b
-/
theorem adicEval_X (J : Ideal S) (x : σ → S) (s : σ) :
    adicEval J x (X s : MvPowerSeries σ R) = x s := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  exact MvPowerSeries.eval₂_X (algebraMap R S) x s

def adicEvalAlgHom [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) : MvPowerSeries σ R →ₐ[R] S :=
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  MvPowerSeries.aeval (hasEval_of_mem_radical J hx)

/--
@isnad1 id=eq.1h5v.s7.5a0f7dfb63d8 from=translated src=- shape=b6ed37fa vocab=78ae5fce
-/
theorem coe_adicEvalAlgHom [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) : ⇑(adicEvalAlgHom (R := R) J hx) = adicEval J x := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  funext f
  exact congrFun (MvPowerSeries.coe_aeval (hasEval_of_mem_radical J hx)) f

open MvPowerSeries.WithPiTopology in

/--
@isnad1 id=mem.2h6v.s7.bb8d9097e108 from=translated src=- shape=f9275a40 vocab=0e90fc9e
-/
theorem adicEval_mem_radical [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    adicEval J x f ∈ J.radical := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  show MvPowerSeries.eval₂ (algebraMap R S) x f ∈ J.radical
  have hφ : Continuous (algebraMap R S) := continuous_of_discreteTopology
  have ha := hasEval_of_mem_radical J hx
  have hf' : IsTopologicallyNilpotent f :=
    MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero hf
  have hc : Continuous (MvPowerSeries.eval₂Hom hφ ha) := by
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.continuous_eval₂ hφ ha
  obtain ⟨n, hn⟩ := (hf'.map hc).exists_pow_mem_of_mem_nhds
    ((J.hasBasis_nhds_zero_adic).mem_of_mem (i := 1) trivial)
  rw [MvPowerSeries.coe_eval₂Hom, pow_one] at hn
  exact ⟨n, hn⟩

/--
@isnad1 id=eq.2h8v.s7.d7f94baac0f4 from=translated src=- shape=720859fb vocab=263ce081
-/
theorem adicEval_subst [Finite σ] {τ : Type*} (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) {a : τ → MvPowerSeries σ R} (ha : HasSubst a)
    (f : MvPowerSeries τ R) :
    adicEval J x (subst a f) = adicEval J (fun t => adicEval J x (a t)) f := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  exact MvPowerSeries.eval₂_subst ha (hasEval_of_mem_radical J hx) f

/--
@isnad1 id=eq.3h10v.s8.729c23d3b778 from=translated src=- shape=c40f9d02 vocab=2abfffcf
-/
theorem adicEval_subst_elim (F : MvFormalGroup g R) {τ : Type*} [Finite τ] (J : Ideal S)
    [IsAdicComplete J S] {w : τ → S} (hw : ∀ t, w t ∈ J.radical)
    {u v : Fin g → MvPowerSeries τ R} (hu : ∀ j, (u j).constantCoeff = 0)
    (hv : ∀ j, (v j).constantCoeff = 0) (i : Fin g) :
    adicEval J w (subst (Sum.elim u v) (F.toPowerSeries i)) =
      adicEval J (Sum.elim (fun j => adicEval J w (u j)) fun j => adicEval J w (v j))
        (F.toPowerSeries i) := by
  have hfam : (fun s => adicEval J w (Sum.elim u v s)) =
      Sum.elim (fun j => adicEval J w (u j)) fun j => adicEval J w (v j) := by
    funext s
    rcases s with j | j <;> rfl
  rw [adicEval_subst J hw (hasSubst_elim hu hv), hfam]

end AdicEval

private theorem forall_sumElim {α β M : Type*} {p : M → Prop} {x : α → M} {y : β → M}
    (hx : ∀ a, p (x a)) (hy : ∀ b, p (y b)) : ∀ c, p (Sum.elim x y c) := by
  rintro (a | b)
  exacts [hx a, hy b]

@[ext]
structure Points (F : MvFormalGroup g R) (S : Type*) [CommRing S] (J : Ideal S) : Type _ where

  val : Fin g → S

  mem_radical : ∀ i, val i ∈ J.radical

namespace Points

variable {F : MvFormalGroup g R} {S : Type*} [CommRing S] {J : Ideal S}

instance instZero : Zero (Points F S J) := ⟨⟨fun _ => 0, fun _ => Submodule.zero_mem _⟩⟩

variable [Algebra R S]

private theorem adicEval_X_eq (x : Points F S J) :
    (fun j => adicEval J x.val (X j : MvPowerSeries (Fin g) R)) = x.val :=
  funext fun j => adicEval_X J x.val j

variable [IsAdicComplete J S]

protected def add (x y : Points F S J) : Points F S J where
  val i := adicEval J (Sum.elim x.val y.val) (F.toPowerSeries i)
  mem_radical i := adicEval_mem_radical J (forall_sumElim x.mem_radical y.mem_radical)
    (F.constantCoeff_eq_zero i)

instance instAdd : Add (Points F S J) := ⟨Points.add⟩

protected def neg (x : Points F S J) : Points F S J where
  val i := adicEval J x.val (invSeries F i)
  mem_radical i := adicEval_mem_radical J x.mem_radical (constantCoeff_invSeries F i)

instance instNeg : Neg (Points F S J) := ⟨Points.neg⟩

/--
@isnad1 id=eq.0h8v.s8.a2517963d2b6 from=translated src=- shape=683fca7e vocab=de549971
-/
protected theorem add_assoc (x y z : Points F S J) : x + y + z = x + (y + z) := by
  ext i
  show adicEval J (Sum.elim (fun j => adicEval J (Sum.elim x.val y.val) (F.toPowerSeries j))
        z.val) (F.toPowerSeries i)
      = adicEval J (Sum.elim x.val fun j => adicEval J (Sum.elim y.val z.val)
        (F.toPowerSeries j)) (F.toPowerSeries i)
  have hw : ∀ t, Sum.elim x.val (Sum.elim y.val z.val) t ∈ J.radical :=
    forall_sumElim x.mem_radical (forall_sumElim y.mem_radical z.mem_radical)
  have ha : ∀ j, (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R).constantCoeff
      = 0 := fun j => constantCoeff_X _
  have hb : ∀ j, (X (Sum.inr (Sum.inl j)) :
      MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R).constantCoeff = 0 := fun j => constantCoeff_X _
  have hc : ∀ j, (X (Sum.inr (Sum.inr j)) :
      MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R).constantCoeff = 0 := fun j => constantCoeff_X _
  have hxa : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)) = x.val :=
    funext fun j => adicEval_X _ _ _
  have hyb : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (X (Sum.inr (Sum.inl j)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)) = y.val :=
    funext fun j => adicEval_X _ _ _
  have hzc : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)) = z.val :=
    funext fun j => adicEval_X _ _ _
  have hin1 : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j)))
      = fun j => adicEval J (Sum.elim x.val y.val) (F.toPowerSeries j) := by
    funext j
    rw [adicEval_subst_elim F J hw ha hb, hxa, hyb]
  have hin2 : (fun j => adicEval J (Sum.elim x.val (Sum.elim y.val z.val))
      (subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) :
          MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)))
      = fun j => adicEval J (Sum.elim y.val z.val) (F.toPowerSeries j) := by
    funext j
    rw [adicEval_subst_elim F J hw hb hc, hyb, hzc]
  have key := congrArg (adicEval J (Sum.elim x.val (Sum.elim y.val z.val)))
    (subst_elim_assoc F ha hb hc i)
  rw [adicEval_subst_elim F J hw (constantCoeff_subst_elim F ha hb) hc,
    adicEval_subst_elim F J hw ha (constantCoeff_subst_elim F hb hc),
    hin1, hzc, hxa, hin2] at key
  exact key

/--
@isnad1 id=eq.0h6v.s7.ee76dd3632fe from=translated src=- shape=ab330f74 vocab=de549971
-/
protected theorem zero_add (x : Points F S J) : 0 + x = x := by
  ext i
  show adicEval J (Sum.elim (fun _ => 0) x.val) (F.toPowerSeries i) = x.val i
  have h0 : ∀ j : Fin g, (0 : MvPowerSeries (Fin g) R).constantCoeff = 0 := fun _ => map_zero _
  have hX : ∀ j : Fin g, (X j : MvPowerSeries (Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hz : (fun _ : Fin g => adicEval J x.val (0 : MvPowerSeries (Fin g) R)) = fun _ => 0 := by
    funext j
    rw [← coe_adicEvalAlgHom J x.mem_radical, map_zero]
  have key := congrArg (adicEval J x.val) (subst_elim_zero_left F hX i)
  rw [adicEval_subst_elim F J x.mem_radical h0 hX, hz, adicEval_X_eq, adicEval_X] at key
  exact key

/--
@isnad1 id=eq.0h6v.s7.a1074c19edfa from=translated src=- shape=3fc00911 vocab=de549971
-/
protected theorem add_zero (x : Points F S J) : x + 0 = x := by
  ext i
  show adicEval J (Sum.elim x.val fun _ => 0) (F.toPowerSeries i) = x.val i
  have h0 : ∀ j : Fin g, (0 : MvPowerSeries (Fin g) R).constantCoeff = 0 := fun _ => map_zero _
  have hX : ∀ j : Fin g, (X j : MvPowerSeries (Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hz : (fun _ : Fin g => adicEval J x.val (0 : MvPowerSeries (Fin g) R)) = fun _ => 0 := by
    funext j
    rw [← coe_adicEvalAlgHom J x.mem_radical, map_zero]
  have key := congrArg (adicEval J x.val) (subst_elim_zero_right F hX i)
  rw [adicEval_subst_elim F J x.mem_radical hX h0, hz, adicEval_X_eq, adicEval_X] at key
  exact key

/--
@isnad1 id=eq.0h6v.s7.7e1a57cf9754 from=translated src=- shape=0757344e vocab=f2cb3953
-/
protected theorem neg_add_cancel (x : Points F S J) : -x + x = 0 := by
  ext i
  show adicEval J (Sum.elim (fun j => adicEval J x.val (invSeries F j)) x.val)
      (F.toPowerSeries i) = 0
  have hX : ∀ j : Fin g, (X j : MvPowerSeries (Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hz : adicEval J x.val (0 : MvPowerSeries (Fin g) R) = 0 := by
    rw [← coe_adicEvalAlgHom J x.mem_radical, map_zero]
  have key := congrArg (adicEval J x.val) (subst_elim_invSeries_X F i)
  rw [adicEval_subst_elim F J x.mem_radical (constantCoeff_invSeries F) hX, adicEval_X_eq,
    hz] at key
  exact key

instance instAddGroup : AddGroup (Points F S J) where
  add := (· + ·)
  zero := 0
  neg := fun x => -x
  add_assoc := Points.add_assoc
  zero_add := Points.zero_add
  add_zero := Points.add_zero
  neg_add_cancel := Points.neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

/--
@isnad1 id=eq.0h7v.s7.9a9c92b19571 from=translated src=- shape=c591d23d vocab=e6c108f5
-/
protected theorem add_comm [IsComm F] (x y : Points F S J) : x + y = y + x := by
  ext i
  show adicEval J (Sum.elim x.val y.val) (F.toPowerSeries i)
      = adicEval J (Sum.elim y.val x.val) (F.toPowerSeries i)
  have hw : ∀ t, Sum.elim x.val y.val t ∈ J.radical :=
    forall_sumElim x.mem_radical y.mem_radical
  have ha : ∀ j, (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hb : ∀ j, (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R).constantCoeff = 0 :=
    fun j => constantCoeff_X _
  have hxa : (fun j => adicEval J (Sum.elim x.val y.val)
      (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ Fin g) R)) = x.val :=
    funext fun j => adicEval_X _ _ _
  have hyb : (fun j => adicEval J (Sum.elim x.val y.val)
      (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) = y.val :=
    funext fun j => adicEval_X _ _ _
  have key := congrArg (adicEval J (Sum.elim x.val y.val)) (subst_elim_comm F ha hb i)
  rw [adicEval_subst_elim F J hw ha hb, adicEval_subst_elim F J hw hb ha, hxa, hyb] at key
  exact key

end Points

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R} {H : MvFormalGroup k R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]

end Hom

namespace Points

variable {F : MvFormalGroup g R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {J' : Ideal S'} [IsAdicComplete J' S']

end Points

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}
  {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} [IsAdicComplete J S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {J' : Ideal S'} [IsAdicComplete J' S']

end Hom

end Tengoku.FltAnthropic.MvFormalGroup
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
