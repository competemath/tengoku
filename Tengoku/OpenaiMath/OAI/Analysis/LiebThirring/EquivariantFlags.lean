import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.GenericPosition

namespace OAI

universe u95 u96 u97 u98 u99 u100 u101 u102 u193 u194

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter

namespace SharpLiebThirring.PLParity
section EquivariantAssignment
variable {G : Type u95} {X : Type u96} [Group G] [MulAction G X] [IsCancelSMul G X]

abbrev Orbit := Quotient (MulAction.orbitRel G X)

omit [IsCancelSMul G X] in
lemma assignment_orbit_smul (g : G) (x : X) :
    (Quotient.mk'' (g • x) : Orbit (G := G) (X := X)) = Quotient.mk'' x :=
  Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩))

def assignmentEquiv : (Orbit (G := G) (X := X) × G) ≃ X :=
  Equiv.ofBijective (fun z ↦ z.2 • z.1.out) (by
    constructor
    · rintro ⟨q, g⟩ ⟨r, h⟩ he
      have hq : q = r := by
        have hh := congrArg (fun x : X ↦ (Quotient.mk'' x : Orbit (G := G) (X := X))) he
        simpa only [assignment_orbit_smul, Quotient.out_eq'] using hh
      subst r
      have hg : g = h := IsCancelSMul.right_cancel g h q.out he
      subst h
      rfl
    · intro x
      let q : Orbit (G := G) (X := X) := Quotient.mk'' x
      have hr : (MulAction.orbitRel G X) x q.out :=
        Quotient.exact' (by rw [Quotient.out_eq'])
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hr)
      exact ⟨(q, g), hg⟩)

def orbitLabel (x : X) : Orbit (G := G) (X := X) := assignmentEquiv.symm x |>.1
def orbitTransport (x : X) : G := assignmentEquiv.symm x |>.2

lemma assignment_reconstruct (x : X) : orbitTransport (G := G) x • (orbitLabel (G := G) x).out = x :=
  assignmentEquiv.apply_symm_apply x

lemma assignment_symm_smul (g : G) (x : X) :
    assignmentEquiv.symm (g • x) = (orbitLabel (G := G) x, g * orbitTransport x) := by
  apply assignmentEquiv.injective
  rw [Equiv.apply_symm_apply]
  change g • x = (g * orbitTransport x) • (orbitLabel (G := G) x).out
  rw [mul_smul, assignment_reconstruct]

lemma orbitLabel_smul (g : G) (x : X) : orbitLabel (G := G) (g • x) = orbitLabel x := by
  simpa only [orbitLabel] using congrArg Prod.fst (assignment_symm_smul g x)

lemma orbitTransport_smul (g : G) (x : X) : orbitTransport (g • x) = g * orbitTransport x :=
  congrArg Prod.snd (assignment_symm_smul g x)

lemma orbitLabel_eq_mk (x : X) : orbitLabel (G := G) x = Quotient.mk'' x := by
  have h := assignment_orbit_smul (orbitTransport (G := G) x) (orbitLabel (G := G) x).out
  rw [assignment_reconstruct, Quotient.out_eq'] at h
  exact h.symm

variable {V : Type u97} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : G →* (V ≃ₗ[ℝ] V))

def equivariantAssignment (a : Orbit (G := G) (X := X) → V) (x : X) : V :=
  ρ (orbitTransport x) (a (orbitLabel x))

omit [FiniteDimensional ℝ V] in
lemma equivariantAssignment_smul (a : Orbit (G := G) (X := X) → V) (g : G) (x : X) :
    equivariantAssignment ρ a (g • x) = ρ g (equivariantAssignment ρ a x) := by
  simp only [equivariantAssignment, orbitLabel_smul, orbitTransport_smul, map_mul,
    LinearEquiv.mul_apply]

omit [FiniteDimensional ℝ V] in
lemma equivariantAssignment_recovers (b : X → V)
    (hb : ∀ g : G, ∀ x, b (g • x) = ρ g (b x)) (x : X) :
    ρ (orbitTransport x) (b (orbitLabel (G := G) x).out) = b x := by
  rw [← hb, assignment_reconstruct]

/-- Free finite group actions admit arbitrarily close equivariant generic
vertex values, while retaining a prescribed invariant family exactly. -/
lemma exists_equivariant_generic [Fintype X]
    {T₁ : Type u98} {T₂ : Type u99} [Fintype T₁] [Fintype T₂]
    (J₁ : T₁ → Type u193) (J₂ : T₂ → Type u194) [∀ t, Fintype (J₁ t)] [∀ t, Fintype (J₂ t)]
    (P : X → Prop) (hP : ∀ g : G, ∀ x, P (g • x) ↔ P x)
    (b : X → V) (hb : ∀ g : G, ∀ x, b (g • x) = ρ g (b x))
    (v₁ : ∀ t, J₁ t → X) (v₂ : ∀ t, J₂ t → X)
    (he₁ : ∀ t, Function.Injective (orbitLabel (G := G) ∘ v₁ t))
    (he₂ : ∀ t, Function.Injective (orbitLabel (G := G) ∘ v₂ t))
    (hf₁ : ∀ t, LinearIndependent ℝ (fun i : {i // P (v₁ t i)} ↦ b (v₁ t i.val)))
    (hf₂ : ∀ t, LinearIndependent ℝ (fun i : {i // P (v₂ t i)} ↦ ((1 : ℝ), b (v₂ t i.val))))
    (hc₁ : ∀ t, Fintype.card (J₁ t) ≤ Module.finrank ℝ V)
    (hc₂ : ∀ t, Fintype.card (J₂ t) ≤ Module.finrank ℝ V + 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : X → V,
      (∀ g : G, ∀ x, a (g • x) = ρ g (a x)) ∧
      (∀ x, dist (a x) (b x) < ε) ∧
      (∀ x, P x → a x = b x) ∧
      (∀ t, LinearIndependent ℝ (fun i ↦ a (v₁ t i))) ∧
      (∀ t, LinearIndependent ℝ (fun i ↦ ((1 : ℝ), a (v₂ t i)))) := by
  classical
  let Q := Orbit (G := G) (X := X)
  let P' : Q → Prop := fun q ↦ P q.out
  let b' : Q → V := fun q ↦ b q.out
  let e : X → Q := orbitLabel (G := G)
  let A : X → V ≃ₗ[ℝ] V := fun x ↦ ρ (orbitTransport x)
  have hpe (x : X) : P' (e x) ↔ P x := by
    change P (orbitLabel (G := G) x).out ↔ P x
    have h := hP (orbitTransport (G := G) x) (orbitLabel (G := G) x).out
    rw [assignment_reconstruct] at h
    exact h.symm
  have hbe (x : X) : A x (b' (e x)) = b x := equivariantAssignment_recovers ρ b hb x
  have hfix₁ (t : T₁) : LinearIndependent ℝ
      (fun i : {i // P' (e (v₁ t i))} ↦ A (v₁ t i.val) (b' (e (v₁ t i.val)))) := by
    simp only [hbe]
    exact (hf₁ t).comp (fun i : {i // P' (e (v₁ t i))} ↦ ⟨i.val, (hpe _).mp i.prop⟩)
      (by
        intro i j h
        apply Subtype.ext
        exact congrArg (fun z : {i // P (v₁ t i)} ↦ z.val) h)
  have hfix₂ (t : T₂) : LinearIndependent ℝ
      (fun i : {i // P' (e (v₂ t i))} ↦ ((1 : ℝ), A (v₂ t i.val) (b' (e (v₂ t i.val))))) := by
    simp only [hbe]
    exact (hf₂ t).comp (fun i : {i // P' (e (v₂ t i))} ↦ ⟨i.val, (hpe _).mp i.prop⟩)
      (by
        intro i j h
        apply Subtype.ext
        exact congrArg (fun z : {i // P (v₂ t i)} ↦ z.val) h)
  obtain ⟨c, hc, h₁, h₂⟩ := exists_mixed_generic J₁ J₂ P' b' e A v₁ v₂
    he₁ he₂ hfix₁ hfix₂ hc₁ hc₂ ε hε
  let a' : Q → V := fun q ↦ if h : P' q then b' q else c ⟨q, h⟩
  let a : X → V := equivariantAssignment ρ a'
  have ha (x : X) : a x = mixedVertexEvaluation P' b' e A c x := rfl
  refine ⟨a, equivariantAssignment_smul ρ a', ?_, ?_, ?_, ?_⟩
  · intro x
    rw [ha, ← hbe]
    exact hc x
  · intro x hx
    rw [ha]
    simp only [mixedVertexEvaluation, dite_eq_left ((hpe x).mpr hx), hbe]
  · simpa only [← ha] using h₁
  · simpa only [← ha] using h₂

end EquivariantAssignment
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open SharpLiebThirring.PLParity
open Finset
attribute [local instance] Classical.propDecidable

lemma card_omit_one_le {n : ℕ} (i : Fin (n + 1)) : Fintype.card {k // k ≠ i} ≤ n := by
  have h := Fintype.card_subtype_lt (p := fun k : Fin (n + 1) ↦ k ≠ i) (x := i) (by simp)
  simp only [Fintype.card_fin] at h
  omega

lemma card_omit_two_le {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) :
    Fintype.card {k // k ≠ i ∧ k ≠ j} + 1 ≤ n := by
  let e : {k // k ≠ i ∧ k ≠ j} ≃ {k : {k : Fin (n + 1) // k ≠ i} // k.val ≠ j} :=
    ⟨fun k ↦ ⟨⟨k.val, k.prop.1⟩, k.prop.2⟩, fun k ↦ ⟨k.val.val, k.val.prop, k.prop⟩,
      by intro k; rfl, by intro k; rfl⟩
  have hc := Fintype.card_congr e
  have hl := Fintype.card_subtype_lt (p := fun k : {k : Fin (n + 1) // k ≠ i} ↦ k.val ≠ j)
    (x := ⟨j, hij.symm⟩) (by simp)
  have hu := card_omit_one_le i
  omega

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset

def spatial {d : ℕ} : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun := Fin.init
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def embedSpatial {d : ℕ} : (Fin d → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun x := Fin.snoc x 0
  map_add' x y := by ext i; refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' a x := by ext i; refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

@[simp] lemma spatial_embed {d : ℕ} (x : Fin d → ℝ) : spatial (embedSpatial x) = x := by
  ext i
  change (Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) x 0) i.castSucc = x i
  simp only [Fin.snoc_castSucc]

/-- A bottom flag with its cube chosen within one mesh of any given spatial point. -/
def bottomSeed {d : ℕ} (h : ℝ) (p : Fin d → ℝ) : Flag (d + 1) where
  base := Fin.snoc (fun i ↦ ⌊p i / h⌋) 0
  corner := fun _ ↦ false
  order := Equiv.refl _

end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
