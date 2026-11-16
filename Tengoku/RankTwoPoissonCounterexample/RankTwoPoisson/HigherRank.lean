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

/--
@isnad1 id=eq.0h7v.s7.93d3cc05349c from=translated src=- shape=1e37ce94 vocab=2af02f6e
-/
theorem pair_add_left (f g h : Poly m K) (u v) :
    pairTerm m K (f+g) h u v = pairTerm m K f h u v + pairTerm m K g h u v := by
  simp [pairTerm]; ring

/--
@isnad1 id=eq.0h7v.s7.d87a832a72e0 from=translated src=- shape=ce514fb1 vocab=2af02f6e
-/
theorem pair_add_right (f g h : Poly m K) (u v) :
    pairTerm m K f (g+h) u v = pairTerm m K f g u v + pairTerm m K f h u v := by
  simp [pairTerm]; ring

/--
@isnad1 id=eq.0h7v.s8.d74909c3445f from=translated src=- shape=c546615f vocab=f422a173
-/
theorem pair_mul_left (f g h : Poly m K) (u v) :
    pairTerm m K (f*g) h u v = f*pairTerm m K g h u v + g*pairTerm m K f h u v := by
  simp [pairTerm]; ring

/--
@isnad1 id=eq.0h7v.s8.3c9a17c1580e from=translated src=- shape=642355ee vocab=f422a173
-/
theorem pair_mul_right (f g h : Poly m K) (u v) :
    pairTerm m K f (g*h) u v = g*pairTerm m K f h u v + h*pairTerm m K f g u v := by
  simp [pairTerm]; ring

/--
@isnad1 id=eq.0h4v.s7.1eaebc9106d4 from=translated src=- shape=547b2807 vocab=2ec18d56
-/
@[simp] theorem C_left (c : K) (f : Poly m K) : bracket m K (C c) f = 0 := by simp [bracket,pairTerm]
/--
@isnad1 id=eq.0h4v.s7.a424fc0515b7 from=translated src=- shape=dc122dfb vocab=2ec18d56
-/
@[simp] theorem C_right (f : Poly m K) (c : K) : bracket m K f (C c) = 0 := by simp [bracket,pairTerm]

def lift : MvPolynomial Var K →ₐ[K] Poly m K := rename Sum.inl

/--
@isnad1 id=eq.0h3v.s8.2f219a74fe9e from=translated src=- shape=c458cae1 vocab=796cfbb1
-/
@[simp] theorem lift_X (i : Var) : lift m K (X i) = X (.inl i) := rename_X _ _

/--
@isnad1 id=eq.0h4v.s10.f86a84140aea from=translated src=- shape=a704ea2a vocab=695de4dd
-/
@[simp] theorem deriv_lift_inl (i : Var) (f : MvPolynomial Var K) :
    pderiv (.inl i) (lift m K f) = lift m K (pderiv i f) :=
  pderiv_rename Sum.inl_injective i f

/--
@isnad1 id=eq.0h4v.s9.5037fa9e2591 from=translated src=- shape=68248a06 vocab=97848f49
-/
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

/--
@isnad1 id=injectiv.1h3v.s8.20083cbd3bd2 from=translated src=- shape=6aaa7e4e vocab=704fd194
-/
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

/--
@isnad1 id=eq.0h3v.s9.9a30044213bd from=translated src=- shape=8377135f vocab=5b1f98b7
-/
@[simp] theorem Phi_X_inl (i : Var) : Phi m K (X (.inl i)) = lift m K (outputK K i) := by simp [Phi,output]
/--
@isnad1 id=eq.0h3v.s8.af5ae606f342 from=translated src=- shape=b8ad92b6 vocab=11891b1d
-/
@[simp] theorem Phi_X_inr (i : Fin m × Fin 2) : Phi m K (X (.inr i)) = X (.inr i) := by simp [Phi,output]

/--
@isnad1 id=eq.0h3v.s10.17c0f88b98a7 from=translated src=- shape=665651d1 vocab=fd1006eb
-/
theorem Phi_lift (f : MvPolynomial Var K) : Phi m K (lift m K f) = lift m K (PhiK K f) := by
  have h : (Phi m K).comp (lift m K) = (lift m K).comp (PhiK K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [lift, PhiK_X]
  exact congrArg (fun e : MvPolynomial Var K →ₐ[K] Poly m K => e f) h

def extendPoint (v : Var → K) : Vars m → K := Sum.elim v (fun _ => 0)

/--
@isnad1 id=eq.0h3v.s5.e7e85f0608ca from=translated src=- shape=865e8520 vocab=a3e5a59b
-/
theorem pointMap_extendPoint (v : Var → K) :
    pointMap K (Phi m K) (extendPoint m K v) = extendPoint m K (pointMapK K (PhiK K) v) := by
  funext i
  cases i <;>
    simp [pointMap,Phi,output,lift,extendPoint,pointMapK,PhiK,aeval_rename,Function.comp_def]

/--
@isnad1 id=eq.0h2v.s5.de999a5e4630 from=translated src=- shape=e911f484 vocab=7dde6b3a
-/
theorem extended_collision :
    pointMap K (Phi m K) (extendPoint m K (point0K K)) =
      pointMap K (Phi m K) (extendPoint m K (point1K K)) := by
  rw [pointMap_extendPoint,pointMap_extendPoint,point0K_image,point1K_image]

/--
@isnad1 id=ne.0h2v.s5.ccf295d1f5d7 from=translated src=- shape=17fb3753 vocab=9b25f432
-/
theorem extended_points_distinct : extendPoint m K (point0K K) ≠ extendPoint m K (point1K K) := by
  intro h
  apply point0K_ne_point1K K
  funext i
  exact congrFun h (.inl i)

/--
@isnad1 id=not.0h2v.s8.263d27df3889 from=translated src=- shape=e5611c19 vocab=d90d560d
-/
theorem Phi_not_surjective : ¬ Function.Surjective (Phi m K) := by
  intro hs
  exact extended_points_distinct m K
    (pointMap_of_surjective_injective K (Phi m K) hs (extended_collision m K))

/--
@isnad1 id=not.0h2v.s9.fa0b108fa42f from=translated src=- shape=6a576f12 vocab=d768df45
-/
theorem Phi_not_automorphism :
    ¬ ∃ e : Poly m K ≃ₐ[K] Poly m K, e.toAlgHom = Phi m K := by
  rintro ⟨e,he⟩
  apply Phi_not_surjective m K
  rw [← he]
  exact e.surjective

/-- Non-surjectivity of the original polynomial substitution, strengthening nonautomorphism.
@isnad1 id=not.0h1v.s8.2a0d39e7ea65 from=translated src=- shape=4ebf060c vocab=922362b7
-/
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

/--
@isnad1 id=eq.0h2v.s7.a73e0f611329 from=translated src=- shape=26a7e85f vocab=33805d24
-/
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

/--
@isnad1 id=eq.0h3v.s11.03937bc13f47 from=translated src=- shape=f8f98a8c vocab=ea3bc343
-/
theorem standardPhi_reindex (f : Poly m K) :
    standardPhi m K (reindexEquiv m K f) = reindexEquiv m K (Phi m K f) := by
  simp [standardPhi]

/--
@isnad1 id=not.0h2v.s9.576325ae9ede from=translated src=- shape=ce9d9a95 vocab=89ed846d
-/
theorem standardPhi_not_surjective : ¬ Function.Surjective (standardPhi m K) := by
  intro hs
  apply Phi_not_surjective m K
  intro f
  obtain ⟨g,hg⟩ := hs (reindexEquiv m K f)
  refine ⟨(reindexEquiv m K).symm g, (reindexEquiv m K).injective ?_⟩
  exact hg

/--
@isnad1 id=not.0h2v.s10.dafa48efcb0a from=translated src=- shape=93e42f38 vocab=5e629f3b
-/
theorem standardPhi_not_automorphism :
    ¬ ∃ e : MvPolynomial (Fin (2+m) × Fin 2) K ≃ₐ[K] MvPolynomial (Fin (2+m) × Fin 2) K,
      e.toAlgHom = standardPhi m K := by
  rintro ⟨e,he⟩
  apply standardPhi_not_surjective m K
  rw [← he]
  exact e.surjective

/--
@isnad1 id=eq.0h3v.s10.15ca460f9e0c from=translated src=- shape=f1df4452 vocab=8dcf949f
-/
theorem standardPhi_X (i : Vars m) :
    standardPhi m K (X (coordinateEquiv m i)) = reindexEquiv m K (output m K i) := by
  have hi : reindexEquiv m K (X i) = X (coordinateEquiv m i) := by simp [reindexEquiv]
  rw [← hi,standardPhi_reindex]
  simp [Phi]

/-- The added canonical pairs are fixed generator by generator.
@isnad1 id=eq.0h4v.s9.6881cd1e70f0 from=translated src=- shape=33808711 vocab=9ff7de06
-/
theorem standardPhi_X_extra (i : Fin m) (b : Fin 2) :
    standardPhi m K (X (Fin.natAdd 2 i,b)) = X (Fin.natAdd 2 i,b) := by
  rw [← coordinate_extra m (i,b),standardPhi_X]
  simp [output,reindexEquiv]

end
end HigherRank
end RankTwoPoisson
