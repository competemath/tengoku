import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.PoissonCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Counterexamples in every higher Poisson rank

Extend the original map by the identity on m additional canonical pairs, prove
all-polynomial bracket preservation and an explicit collision, then reindex to
exactly n=2+m pairs. Position/momentum is the second coordinate 0/1, so the
canonical convention is {pᵢ,xⱼ}=δᵢⱼ. The final theorem quantifies over every n≥2.
-/

set_option maxHeartbeats 0
namespace RankTwoPoisson
namespace HigherRank
open MvPolynomial
noncomputable section

abbrev Vars (m : ℕ) := Var ⊕ (Fin m × Fin 2)
abbrev Poly (m : ℕ) (K : Type*) [CommSemiring K] := MvPolynomial (Vars m) K
variable (m : ℕ) (K : Type*) [Field K]

def pairTerm (f g : Poly m K) (u v : Vars m) :=
  pderiv u f * pderiv v g - pderiv v f * pderiv u g

def bracket (f g : Poly m K) : Poly m K :=
  pairTerm m K f g (.inl 2) (.inl 0) + pairTerm m K f g (.inl 3) (.inl 1) +
  ∑ k : Fin m, pairTerm m K f g (.inr (k,1)) (.inr (k,0))

theorem pair_add_left (f g h : Poly m K) (u v) :
    pairTerm m K (f+g) h u v = pairTerm m K f h u v + pairTerm m K g h u v := by
  simp [pairTerm]; ring

theorem pair_add_right (f g h : Poly m K) (u v) :
    pairTerm m K f (g+h) u v = pairTerm m K f g u v + pairTerm m K f h u v := by
  simp [pairTerm]; ring

theorem pair_mul_left (f g h : Poly m K) (u v) :
    pairTerm m K (f*g) h u v = f*pairTerm m K g h u v + g*pairTerm m K f h u v := by
  simp [pairTerm]; ring

theorem pair_mul_right (f g h : Poly m K) (u v) :
    pairTerm m K f (g*h) u v = g*pairTerm m K f h u v + h*pairTerm m K f g u v := by
  simp [pairTerm]; ring

@[simp] theorem C_left (c : K) (f : Poly m K) : bracket m K (C c) f = 0 := by simp [bracket,pairTerm]
@[simp] theorem C_right (f : Poly m K) (c : K) : bracket m K f (C c) = 0 := by simp [bracket,pairTerm]

def lift : MvPolynomial Var K →ₐ[K] Poly m K := rename Sum.inl

@[simp] theorem lift_X (i : Var) : lift m K (X i) = X (.inl i) := rename_X _ _

@[simp] theorem deriv_lift_inl (i : Var) (f : MvPolynomial Var K) :
    pderiv (.inl i) (lift m K f) = lift m K (pderiv i f) :=
  pderiv_rename Sum.inl_injective i f

@[simp] theorem deriv_lift_inr (i : Fin m × Fin 2) (f : MvPolynomial Var K) :
    pderiv (.inr i) (lift m K f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [lift]
  | add f g hf hg => simp [hf,hg]
  | mul_X f j hf =>
    simp only [map_mul, lift_X, MvPolynomial.pderiv_mul, hf]
    simp

/-- Point map for a polynomial algebra endomorphism on any variable type.-/
def pointMap {σ : Type*} (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (v : σ → K) : σ → K :=
  fun i => aeval v (φ (X i))

theorem pointMap_of_surjective_injective {σ : Type*}
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (hs : Function.Surjective φ) :
    Function.Injective (pointMap K φ) := by
  intro v w h
  have hc : (aeval v).comp φ = (aeval w).comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    exact congrFun h i
  funext i
  obtain ⟨f,hf⟩ := hs (X i)
  have hi := congrArg (fun e : MvPolynomial σ K →ₐ[K] K => e f) hc
  simpa only [AlgHom.comp_apply,hf,aeval_X] using hi

variable [CharZero K]

def output : Vars m → Poly m K := Sum.elim (fun i => lift m K (outputK K i)) (fun i => X (.inr i))
def Phi : Poly m K →ₐ[K] Poly m K := aeval (output m K)

@[simp] theorem Phi_X_inl (i : Var) : Phi m K (X (.inl i)) = lift m K (outputK K i) := by simp [Phi,output]
@[simp] theorem Phi_X_inr (i : Fin m × Fin 2) : Phi m K (X (.inr i)) = X (.inr i) := by simp [Phi,output]

theorem Phi_lift (f : MvPolynomial Var K) : Phi m K (lift m K f) = lift m K (PhiK K f) := by
  have h : (Phi m K).comp (lift m K) = (lift m K).comp (PhiK K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [lift, PhiK_X]
  exact congrArg (fun e : MvPolynomial Var K →ₐ[K] Poly m K => e f) h

def extendPoint (v : Var → K) : Vars m → K := Sum.elim v (fun _ => 0)

theorem pointMap_extendPoint (v : Var → K) :
    pointMap K (Phi m K) (extendPoint m K v) = extendPoint m K (pointMapK K (PhiK K) v) := by
  funext i
  cases i <;>
    simp [pointMap,Phi,output,lift,extendPoint,pointMapK,PhiK,aeval_rename,Function.comp_def]

theorem extended_collision :
    pointMap K (Phi m K) (extendPoint m K (point0K K)) =
      pointMap K (Phi m K) (extendPoint m K (point1K K)) := by
  rw [pointMap_extendPoint,pointMap_extendPoint,point0K_image,point1K_image]

theorem extended_points_distinct : extendPoint m K (point0K K) ≠ extendPoint m K (point1K K) := by
  intro h
  apply point0K_ne_point1K K
  funext i
  exact congrFun h (.inl i)

theorem Phi_not_surjective : ¬ Function.Surjective (Phi m K) := by
  intro hs
  exact extended_points_distinct m K
    (pointMap_of_surjective_injective K (Phi m K) hs (extended_collision m K))

theorem Phi_not_automorphism :
    ¬ ∃ e : Poly m K ≃ₐ[K] Poly m K, e.toAlgHom = Phi m K := by
  rintro ⟨e,he⟩
  apply Phi_not_surjective m K
  rw [← he]
  exact e.surjective

/-- Non-surjectivity of the original polynomial substitution, strengthening nonautomorphism.-/
theorem base_not_surjective : ¬ Function.Surjective (PhiK K) := by
  intro hs
  exact point0K_ne_point1K K (pointMap_of_surjective_injective K (PhiK K) hs
    ((point0K_image K).trans (point1K_image K).symm))

/-- The original order (x,q,p,z) corresponds to pairs (x,p), (q,z).-/
def basePairEquiv : Var ≃ Fin 2 × Fin 2 :=
  (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2*2)).symm.trans (Equiv.prodComm _ _)

/-- Reindex the original two pairs and m added pairs as exactly 2+m canonical pairs.-/
def coordinateEquiv : Vars m ≃ Fin (2+m) × Fin 2 :=
  (Equiv.sumCongr basePairEquiv (Equiv.refl _)).trans
    ((Equiv.sumProdDistrib (Fin 2) (Fin m) (Fin 2)).symm.trans
      (Equiv.prodCongr finSumFinEquiv (Equiv.refl _)))

theorem coordinate_extra (i : Fin m × Fin 2) :
    coordinateEquiv m (.inr i) = (Fin.natAdd 2 i.1,i.2) := rfl

/-- The manuscript's bracket on n canonical pairs, indexed (pair,position/momentum).-/
def canonicalBracket (n : ℕ) (f g : MvPolynomial (Fin n × Fin 2) K) :=
  ∑ k : Fin n, (pderiv (k,1) f * pderiv (k,0) g - pderiv (k,0) f * pderiv (k,1) g)

def reindexEquiv : Poly m K ≃ₐ[K] MvPolynomial (Fin (2+m) × Fin 2) K :=
  MvPolynomial.renameEquiv K (coordinateEquiv m)

/-- The extended map on the standard polynomial algebra with exactly 2+m pairs.-/
def standardPhi : MvPolynomial (Fin (2+m) × Fin 2) K →ₐ[K] MvPolynomial (Fin (2+m) × Fin 2) K :=
  (reindexEquiv m K).toAlgHom.comp ((Phi m K).comp (reindexEquiv m K).symm.toAlgHom)

theorem standardPhi_reindex (f : Poly m K) :
    standardPhi m K (reindexEquiv m K f) = reindexEquiv m K (Phi m K f) := by
  simp [standardPhi]

theorem standardPhi_not_surjective : ¬ Function.Surjective (standardPhi m K) := by
  intro hs
  apply Phi_not_surjective m K
  intro f
  obtain ⟨g,hg⟩ := hs (reindexEquiv m K f)
  refine ⟨(reindexEquiv m K).symm g, (reindexEquiv m K).injective ?_⟩
  exact hg

theorem standardPhi_not_automorphism :
    ¬ ∃ e : MvPolynomial (Fin (2+m) × Fin 2) K ≃ₐ[K] MvPolynomial (Fin (2+m) × Fin 2) K,
      e.toAlgHom = standardPhi m K := by
  rintro ⟨e,he⟩
  apply standardPhi_not_surjective m K
  rw [← he]
  exact e.surjective

theorem standardPhi_X (i : Vars m) :
    standardPhi m K (X (coordinateEquiv m i)) = reindexEquiv m K (output m K i) := by
  have hi : reindexEquiv m K (X i) = X (coordinateEquiv m i) := by simp [reindexEquiv]
  rw [← hi,standardPhi_reindex]
  simp [Phi]

/-- The added canonical pairs are fixed generator by generator.-/
theorem standardPhi_X_extra (i : Fin m) (b : Fin 2) :
    standardPhi m K (X (Fin.natAdd 2 i,b)) = X (Fin.natAdd 2 i,b) := by
  rw [← coordinate_extra m (i,b),standardPhi_X]
  simp [output,reindexEquiv]

end
end HigherRank
end RankTwoPoisson
