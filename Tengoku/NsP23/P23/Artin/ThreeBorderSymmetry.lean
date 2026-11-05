import Tengoku.NsP23.P23.Presentation.MonomialQuotient
import Tengoku.NsP23.P23.OneTie.H5Cover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual algebra and ordinary canonical-trace transport for one-tie symmetry. -/
namespace P23.Artin
noncomputable section
set_option backward.isDefEq.respectTransparency false
open P23.OneTie P23.Presentation
variable {k : Type*} [Field k]
variable {a b c a' b' c' : ℕ} [NeZero a] [NeZero a']
variable {S : Finset (Normal a b c)} {T : Finset (Normal a' b' c')}

def transportDirectCanonicalHom (E : MonomialArtin k S ≃ₐ[k] MonomialArtin k T)
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S) :
    Omega k T →ₗ[MonomialArtin k T] MonomialArtin k T where
  toFun ψ := E (F (ψ.comp E.toLinearMap))
  map_add' ψ χ := by
    have he : (ψ+χ).comp E.toLinearMap = ψ.comp E.toLinearMap + χ.comp E.toLinearMap := by
      ext x; rfl
    rw [he,F.map_add]
    exact map_add E _ _
  map_smul' r ψ := by
    have he : (r • ψ).comp E.toLinearMap = E.symm r • ψ.comp E.toLinearMap := by
      ext v
      change ψ (r * E v) = ψ (E (E.symm r * v))
      rw [map_mul E,E.apply_symm_apply]
    rw [he,F.map_smul]
    simp [smul_eq_mul]

/--
@isnad1 id=mem.1h11v.s9.41113aa6af21 from=translated src=- shape=75155538 vocab=e8482fcf
-/
theorem directTrace_transport (E : MonomialArtin k S ≃ₐ[k] MonomialArtin k T)
    {v : MonomialArtin k S} (hv : v ∈ TraceSubmodule k S) : E v ∈ TraceSubmodule k T := by
  rw [trace_eq_span_traceValueSet] at hv
  refine Submodule.span_induction (p := fun v _ => E v ∈ TraceSubmodule k T) ?_ ?_ ?_ ?_ hv
  · rintro v ⟨F,φ,rfl⟩
    apply trace_range_le T (transportDirectCanonicalHom E F)
    refine ⟨φ.comp E.symm.toLinearMap,?_⟩
    change E (F ((φ.comp E.symm.toLinearMap).comp E.toLinearMap)) = E (F φ)
    congr 2
    ext x
    simp
  · simp
  · intro x y hx hy hx' hy'
    simpa only [map_add] using (TraceSubmodule k T).add_mem hx' hy'
  · intro r x hx hx'
    simpa [smul_eq_mul] using (TraceSubmodule k T).smul_mem (E r) hx'

/--
@isnad1 id=iff.0h11v.s9.64296fc23b4b from=translated src=- shape=04237fea vocab=e8482fcf
-/
theorem directTrace_mem_iff_algEquiv (E : MonomialArtin k S ≃ₐ[k] MonomialArtin k T)
    (v : MonomialArtin k S) : E v ∈ TraceSubmodule k T ↔ v ∈ TraceSubmodule k S := by
  constructor
  · intro h
    simpa using directTrace_transport E.symm h
  · exact directTrace_transport E

def normalModelCongr (e : Normal a b c ≃* Normal a' b' c')
    (he : ∀ p, e p ∈ standardSet T ↔ p ∈ standardSet S) :
    MonomialArtin k S ≃ₐ[k] MonomialArtin k T := by
  let E := MonoidAlgebra.domCongr k k e
  have hmap : killedMonomialIdeal (k := k) T = (killedMonomialIdeal (k := k) S).map E.toRingHom := by
    unfold killedMonomialIdeal
    rw [Ideal.map_span]
    congr 1
    ext f
    constructor
    · rintro ⟨p,hp,rfl⟩
      refine ⟨monomial (k := k) (e.symm p),?_,?_⟩
      · refine ⟨e.symm p,?_,rfl⟩
        intro hs
        exact hp (by simpa using (he (e.symm p)).mpr hs)
      · simp [E,monomial]
    · rintro ⟨f,⟨p,hp,rfl⟩,rfl⟩
      refine ⟨e p,mt (he p).mp hp,?_⟩
      simp [E,monomial]
  exact (normalMonomialQuotientEquiv (k := k) S).symm.trans
    ((Ideal.quotientEquivAlg _ _ E hmap).trans (normalMonomialQuotientEquiv (k := k) T))

/--
@isnad1 id=eq.2h11v.s9.71bc39b11bdd from=translated src=- shape=e46b645c vocab=6210a494
-/
theorem normalModelCongr_X (e : Normal a b c ≃* Normal a' b' c')
    (he : ∀ p, e p ∈ standardSet T ↔ p ∈ standardSet S)
    (p : Normal a b c) (hp : p ∈ standardFinset S) :
    normalModelCongr (k := k) e he (X (k := k) S p hp) =
      X (k := k) T (e p) ((mem_standardFinset_iff_standardSet T _).mpr
        ((he p).mpr ((mem_standardFinset_iff_standardSet S p).mp hp))) := by
  have hX := normalMonomialQuotientEquiv_monomial_of_mem (k := k) S p hp
  rw [← hX]
  dsimp only [normalModelCongr,AlgEquiv.trans_apply]
  rw [AlgEquiv.symm_apply_apply,Ideal.quotientEquivAlg_mk]
  simpa [monomial] using truncatedMonomial_of_mem (k := k) T (e p)
    ((mem_standardFinset_iff_standardSet T _).mpr
      ((he p).mpr ((mem_standardFinset_iff_standardSet S p).mp hp)))

def swapYZMulEquiv : Normal a b c ≃* Normal a c b where
  toFun := swapYZ
  invFun := swapYZ
  left_inv := swapYZ_swapYZ
  right_inv := swapYZ_swapYZ
  map_mul' p q := by
    apply Normal.ext <;> simp [swapYZ,Normal.mul,Normal.raw,Normal.normalize]

/--
@isnad1 id=eq.1h11v.s9.68e71ddcb15d from=translated src=- shape=8e0d3c8c vocab=828280b0
-/
theorem normalModelCongr_truncated (e : Normal a b c ≃* Normal a' b' c')
    (he : ∀ p, e p ∈ standardSet T ↔ p ∈ standardSet S) (p : Normal a b c) :
    normalModelCongr (k := k) e he (truncatedMonomial (k := k) S p) =
      truncatedMonomial (k := k) T (e p) := by
  by_cases hp : p ∈ standardFinset S
  · rw [truncatedMonomial_of_mem S p hp,normalModelCongr_X]
    symm
    exact truncatedMonomial_of_mem T (e p) _
  · have hpt : e p ∉ standardFinset T := by
      intro hh
      exact hp ((mem_standardFinset_iff_standardSet S _).mpr
        ((he p).mp ((mem_standardFinset_iff_standardSet T _).mp hh)))
    simp [hp,hpt]

def swapYZDirectEquiv (S : Finset (Normal a b c)) :
    MonomialArtin k S ≃ₐ[k] MonomialArtin k (swapYZFinset S) :=
  normalModelCongr swapYZMulEquiv (fun p => mem_standardSet_swapYZFinset_iff S p)

/--
@isnad1 id=variable.4h5v.s6.9e4de7f06f15 from=translated src=- shape=b9759178 vocab=bdb6f5c7
-/
theorem swapYZVariablesInTrace (S : Finset (Normal a b c))
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (hl' : IsLiveTie (swapYZFinset S)) (hv : VariablesInTrace k S hl) :
    VariablesInTrace k (swapYZFinset S) hl' := by
  have ha1 : a ≠ 1 := by have := hd.1; omega
  rcases hv with ⟨hx,hy,hz⟩
  have hx' := directTrace_transport (swapYZDirectEquiv (k := k) S) hx
  have hy' := directTrace_transport (swapYZDirectEquiv (k := k) S) hy
  have hz' := directTrace_transport (swapYZDirectEquiv (k := k) S) hz
  dsimp only [swapYZDirectEquiv] at hx' hy' hz'
  rw [normalModelCongr_X] at hx' hy' hz'
  refine ⟨?_,?_,?_⟩
  · simpa [swapYZMulEquiv,swapYZ,Normal.xGenerator,ha1] using hx'
  · simpa [swapYZMulEquiv,swapYZ,Normal.yGenerator,Normal.zGenerator] using hz'
  · simpa [swapYZMulEquiv,swapYZ,Normal.yGenerator,Normal.zGenerator] using hy'

/--
@isnad1 id=isrootan.1h4v.s5.0a7ff3534c73 from=translated src=- shape=81cd560f vocab=e8db1c26
-/
theorem swapYZIsRootAntichain (S : Finset (Normal a b c)) (ha : IsRootAntichain S) :
    IsRootAntichain (swapYZFinset S) := by
  intro p hp q hq hn hd
  obtain ⟨p',hp',rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := Finset.mem_map.mp hq
  exact ha p' hp' q' hq' (fun he => hn (he ▸ rfl)) ((swapYZ_divides_iff p' q').mp hd)

/--
@isnad1 id=isliveti.2h4v.s5.6f6a2866deb7 from=translated src=- shape=047926dd vocab=f66831cc
-/
theorem swapYZIsLiveTie (S : Finset (Normal a b c))
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S) : IsLiveTie (swapYZFinset S) := by
  have ha1 : a ≠ 1 := by have := hd.1; omega
  refine ⟨?_,?_,?_,?_⟩
  · simpa [Normal.xGenerator,swapYZ,ha1] using
      (mem_standardSet_swapYZFinset_iff S Normal.xGenerator).mpr hl.1
  · simpa [Normal.yGenerator,Normal.zGenerator,swapYZ] using
      (mem_standardSet_swapYZFinset_iff S Normal.zGenerator).mpr hl.2.2.1
  · simpa [Normal.yGenerator,Normal.zGenerator,swapYZ] using
      (mem_standardSet_swapYZFinset_iff S Normal.yGenerator).mpr hl.2.1
  · simpa [liveTiePoint,swapYZ] using
      (mem_standardSet_swapYZFinset_iff S liveTiePoint).mpr hl.2.2.2
end
end P23.Artin
