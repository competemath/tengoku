import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Symplectic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Source-coordinate algebra equivalences

The polynomial maps Ψ₀=(x,y,β,D₀) and Ψ=(x,y,β,D) are represented
contravariantly by their substitution algebra equivalences. Their inverses,
core substitution, algebraic independence, and full Jacobian determinants are
proved over every characteristic-zero field.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RankTwoPoisson
namespace SourceCoordinates
open MvPolynomial
noncomputable section

def sourceTuple : Var → P := ![x,y,beta,D0]
def inverseTuple : Var → P := ![x,Qs,pInv,zInv]
def sourceHom : P →ₐ[ℚ] P := aeval sourceTuple
def inverseHom : P →ₐ[ℚ] P := aeval inverseTuple

/--
@isnad1 id=eq.0h0v.s7.ca7182772a0d from=translated src=- shape=727dc3fb vocab=1e6a0e61
-/
theorem inverse_source : inverseHom.comp sourceHom = AlgHom.id ℚ P := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, sourceHom, inverseHom, aeval_X, AlgHom.id_apply]
  fin_cases i
  · simp [sourceTuple, inverseTuple, x]
  · change aeval inverseTuple y = q
    convert yBack_eq using 1
    simp [yBack, betaBack, y, beta, B, a, rat, x, q, p, z, inverseTuple]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]
  · change aeval inverseTuple beta = p
    convert betaBack_eq using 1
    simp [betaBack, beta, B, a, rat, x, q, p, z, inverseTuple]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]
  · change aeval inverseTuple D0 = z
    convert D0Back_eq using 1
    simp [D0Back, D0, rat, x, q, p, z, inverseTuple]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]

/--
@isnad1 id=eq.0h0v.s7.392304c6e325 from=translated src=- shape=727dc3fb vocab=1e6a0e61
-/
theorem source_inverse : sourceHom.comp inverseHom = AlgHom.id ℚ P := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, sourceHom, inverseHom, aeval_X, AlgHom.id_apply]
  fin_cases i
  · simp [sourceTuple, inverseTuple, x]
  · change aeval sourceTuple Qs = q
    convert Qorig_eq using 1
    simp [Qorig, Qs, sourceTuple, rat, x, q, p]
  · change aeval sourceTuple pInv = p
    convert pRecovered_eq using 1
    simp [pInv, pRecovered, Morig, Qorig, Qs, As, Ms, sourceTuple, rat, x, q, p, z]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]
  · change aeval sourceTuple zInv = z
    convert zRecovered_eq using 1
    simp [zInv, zRecovered, Morig, Qorig, Qs, Cs, Ms, sourceTuple, rat, x, q, p, z]
    apply MvPolynomial.funext
    intro v
    simp only [map_ofNat]

def sourceEquiv : P ≃ₐ[ℚ] P :=
  AlgEquiv.ofAlgHom sourceHom inverseHom source_inverse inverse_source

/-- Embed independent core coordinates as the first three polynomial variables.-/
def coreLift : Core.CoreP →ₐ[ℚ] P := aeval ![x,q,p]
/-- Substitute the actual source coordinates into the independent core.-/
def coreSubst : Core.CoreP →ₐ[ℚ] P := aeval ![x,y,beta]

/--
@isnad1 id=and.0h0v.s9.9451d405bb8a from=translated src=- shape=18ce0454 vocab=4b21e455
-/
theorem core_substitution :
    coreSubst Core.r = R ∧ coreSubst Core.t = T ∧
    coreSubst Core.s = S ∧ coreSubst Core.h = H := by
  simp [coreSubst, Core.r, Core.t, Core.s, Core.h, Core.U, Core.crat,
    Core.Xc, Core.Yc, Core.Wc, R, T, S, H, u, rat]

/--
@isnad1 id=eq.0h1v.s8.c4a0c751fc00 from=translated src=- shape=c21e71fe vocab=c8dc7e0f
-/
theorem source_coreLift (f : Core.CoreP) : sourceHom (coreLift f) = coreSubst f := by
  rw [coreLift, MvPolynomial.comp_aeval_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [coreSubst, sourceHom, sourceTuple, x, q, p]

def shear (c : ℚ) : P →ₐ[ℚ] P := aeval ![x,q,p,z + rat c * coreLift Core.h]

/--
@isnad1 id=eq.0h2v.s8.36835e278784 from=translated src=- shape=d02bba34 vocab=9f5e632d
-/
theorem shear_coreLift (c : ℚ) (f : Core.CoreP) : shear c (coreLift f) = coreLift f := by
  rw [coreLift, MvPolynomial.comp_aeval_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [shear, x, q, p]

/--
@isnad1 id=eq.0h2v.s8.291416334f7c from=translated src=- shape=4284a8ac vocab=86694621
-/
theorem shear_X (c : ℚ) (i : Var) :
    shear c (X i) = ![x,q,p,z + rat c * coreLift Core.h] i := by simp [shear]

/--
@isnad1 id=eq.0h2v.s7.648a9baee42f from=translated src=- shape=6089a9b6 vocab=b02cdb1a
-/
theorem shear_comp (c d : ℚ) : (shear c).comp (shear d) = shear (c+d) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, shear_X]
  fin_cases i <;>
    simp [x, q, p, z, rat, map_add, map_mul, shear_X, shear_coreLift, add_mul]
  ring

/--
@isnad1 id=eq.0h0v.s6.cec50a468e5d from=translated src=- shape=cdc352ec vocab=5bfd1e63
-/
theorem shear_zero : shear 0 = AlgHom.id ℚ P := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [shear, x, q, p, z, rat]

def shearEquiv : P ≃ₐ[ℚ] P := AlgEquiv.ofAlgHom (shear 1) (shear (-1))
  (by rw [shear_comp]; norm_num; exact shear_zero)
  (by rw [shear_comp]; norm_num; exact shear_zero)

def correctedEquiv : P ≃ₐ[ℚ] P := shearEquiv.trans sourceEquiv

/--
@isnad1 id=eq.0h1v.s7.60c6f99aa51f from=translated src=- shape=23a588a8 vocab=a1eacbac
-/
theorem source_X (i : Var) : sourceHom (X i) = sourceTuple i := by simp [sourceHom]

variable (K : Type*) [Field K] [CharZero K]

/--
@isnad1 id=eq.0h3v.s9.51c9680f530d from=translated src=- shape=95884571 vocab=d34dbd58
-/
theorem substitution_map (F : Var → P) (f : P) :
    aeval (fun i => mapK K (F i)) (mapK K f) = mapK K (aeval F f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [mapK]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, hf]; simp [mapK]

def extendHom (f : P →ₐ[ℚ] P) : MvPolynomial Var K →ₐ[K] MvPolynomial Var K :=
  aeval (fun i => mapK K (f (X i)))

/--
@isnad1 id=eq.0h3v.s9.5908747d29cd from=translated src=- shape=9be280db vocab=af188812
-/
theorem extendHom_map (f : P →ₐ[ℚ] P) (g : P) :
    extendHom K f (mapK K g) = mapK K (f g) := by
  rw [extendHom, substitution_map]
  congr 1
  have h : aeval (fun i => f (X i)) = f := by ext i; simp
  rw [h]

/--
@isnad1 id=eq.0h3v.s9.ab5e7015d9f2 from=translated src=- shape=5e50f056 vocab=26d8070a
-/
theorem extendHom_comp (f g : P →ₐ[ℚ] P) :
    (extendHom K f).comp (extendHom K g) = extendHom K (f.comp g) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, extendHom, aeval_X]
  exact extendHom_map K f (g (X i))

/--
@isnad1 id=eq.0h1v.s7.2691aa2b1da5 from=translated src=- shape=dc73e7bc vocab=381aa603
-/
theorem extendHom_id : extendHom K (AlgHom.id ℚ P) = AlgHom.id K _ := by
  ext i
  simp [extendHom, mapK]

def extendEquiv (e : P ≃ₐ[ℚ] P) : MvPolynomial Var K ≃ₐ[K] MvPolynomial Var K :=
  AlgEquiv.ofAlgHom (extendHom K e.toAlgHom) (extendHom K e.symm.toAlgHom)
    (by rw [extendHom_comp, e.comp_symm]; exact extendHom_id K)
    (by rw [extendHom_comp, e.symm_comp]; exact extendHom_id K)

/-- Independent core substitution after coefficient extension.-/
def coreSubstK : MvPolynomial Core.CoreVar K →ₐ[K] MvPolynomial Var K :=
  aeval (fun i => mapK K (![x,y,beta] i))

/--
@isnad1 id=eq.0h2v.s9.5d457d777ae6 from=translated src=- shape=28fe94b2 vocab=6b463880
-/
theorem coreSubstK_map (f : Core.CoreP) :
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) f) = mapK K (coreSubst f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [coreSubstK, coreSubst, mapK]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, hf]; simp [coreSubstK, coreSubst]

/--
@isnad1 id=and.0h1v.s11.7cffac924688 from=translated src=- shape=7c75d99a vocab=446cbb41
-/
theorem core_substitution_charZero :
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) Core.r) = mapK K R ∧
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) Core.t) = mapK K T ∧
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) Core.s) = mapK K S ∧
    coreSubstK K (MvPolynomial.map (algebraMap ℚ K) Core.h) = mapK K H := by
  simp only [coreSubstK_map, core_substitution.1, core_substitution.2.1,
    core_substitution.2.2.1, core_substitution.2.2.2, and_self]

/-- Source-coordinate automorphism over every characteristic-zero field.-/
def sourceEquivK := extendEquiv K sourceEquiv
/-- Corrected source-coordinate automorphism over every characteristic-zero field.-/
def correctedEquivK := extendEquiv K correctedEquiv

/--
@isnad1 id=eq.0h2v.s8.b5ca5f5bba13 from=translated src=- shape=e906e19f vocab=3b80dd58
-/
theorem sourceEquivK_X (i : Var) : sourceEquivK K (X i) = mapK K (sourceTuple i) := by
  simp [sourceEquivK, extendEquiv, extendHom, sourceEquiv, source_X]

/--
@isnad1 id=eq.0h2v.s9.43a95b1e52a0 from=translated src=- shape=f5832421 vocab=1bc2f731
-/
theorem sourceEquivK_symm_X (i : Var) :
    (sourceEquivK K).symm (X i) = mapK K (inverseTuple i) := by
  simp [sourceEquivK, extendEquiv, extendHom, sourceEquiv, inverseHom]

end
end SourceCoordinates
end RankTwoPoisson
