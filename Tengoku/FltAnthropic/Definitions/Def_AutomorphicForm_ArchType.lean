import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_RowIsometryInvariance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField AdelicLevel IsDedekindDomain Matrix

open scoped Classical

namespace AutomorphicForm

section MatrixFurniture

variable (F : Type) [Field F]

noncomputable section

abbrev archMatrixPiEquiv :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) ≃+* Π w : InfinitePlace F,
      Matrix (Fin 2) (Fin 2) w.Completion :=
  Matrix.piRingEquiv (β := fun w : InfinitePlace F => w.Completion)

/--
@isnad1 id=eq.0h5v.s10.37b673ea2660 from=translated src=- shape=0266f34d vocab=00ce9861
-/
theorem archMatrixPiEquiv_apply (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
    (w : InfinitePlace F) (i j : Fin 2) :
    archMatrixPiEquiv F m w i j = m i j w := rfl

def archMatrixUpdate (w : InfinitePlace F) (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  (archMatrixPiEquiv F).symm (Function.update 1 w m)

/--
@isnad1 id=eq.0h3v.s10.76059f0c49fd from=translated src=- shape=6bddaa41 vocab=21237dba
-/
theorem archMatrixPiEquiv_archMatrixUpdate (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    archMatrixPiEquiv F (archMatrixUpdate F w m)
      = Function.update (1 : Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w m :=
  (archMatrixPiEquiv F).apply_symm_apply _

/--
@isnad1 id=eq.0h5v.s5.a12171e107e6 from=translated src=- shape=c590fcd8 vocab=a6d5bf8d
-/
theorem archMatrixUpdate_apply_self (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2) :
    archMatrixUpdate F w m i j w = m i j := by
  have h := archMatrixPiEquiv_archMatrixUpdate F w m
  have hw := congrFun h w
  simp only [Function.update_self] at hw
  exact congrFun (congrFun hw i) j

/--
@isnad1 id=eq.1h6v.s7.457733e15f53 from=translated src=- shape=c46d630c vocab=a6d5bf8d
-/
theorem archMatrixUpdate_apply_of_ne (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2)
    {v : InfinitePlace F} (hvw : v ≠ w) :
    archMatrixUpdate F w m i j v = (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  have h := archMatrixPiEquiv_archMatrixUpdate F w m
  have hv := congrFun h v
  simp only [Function.update_of_ne hvw, Pi.one_apply] at hv
  exact congrFun (congrFun hv i) j

/--
@isnad1 id=eq.0h2v.s7.1e880368adc7 from=translated src=- shape=f3af7c07 vocab=3f6106e5
-/
theorem archMatrixUpdate_one (w : InfinitePlace F) :
    archMatrixUpdate F w (1 : Matrix (Fin 2) (Fin 2) w.Completion) = 1 := by
  apply (archMatrixPiEquiv F).injective
  rw [archMatrixPiEquiv_archMatrixUpdate, map_one]
  exact Function.update_eq_self_iff.mpr rfl

/--
@isnad1 id=eq.0h4v.s8.8c7ff1d52bd0 from=translated src=- shape=2cfadb72 vocab=e5d24acb
-/
theorem archMatrixUpdate_mul (w : InfinitePlace F)
    (a b : Matrix (Fin 2) (Fin 2) w.Completion) :
    archMatrixUpdate F w (a * b) = archMatrixUpdate F w a * archMatrixUpdate F w b := by
  apply (archMatrixPiEquiv F).injective
  rw [archMatrixPiEquiv_archMatrixUpdate, map_mul,
    archMatrixPiEquiv_archMatrixUpdate, archMatrixPiEquiv_archMatrixUpdate]
  funext v
  by_cases hv : v = w
  · subst hv
    simp
  · simp [Function.update_of_ne hv]

def archMatrixInclHom (w : InfinitePlace F) :
    Matrix (Fin 2) (Fin 2) w.Completion →* Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) where
  toFun := archMatrixUpdate F w
  map_one' := archMatrixUpdate_one F w
  map_mul' := archMatrixUpdate_mul F w

def archGLIncl (w : InfinitePlace F) :
    GL (Fin 2) w.Completion →* GL (Fin 2) (InfiniteAdeleRing F) :=
  Units.map (archMatrixInclHom F w)

end

end MatrixFurniture

section ComponentReceipts

variable (F : Type) [Field F]

/--
@isnad1 id=eq.0h3v.s10.59c47965a78f from=translated src=- shape=f19043dc vocab=6e9ae1f6
-/
theorem archComponent_archGLIncl_self (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    archComponent F w (archGLIncl F w k) = k := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show archEval F w (archMatrixUpdate F w (k : _) i j) = (k : _) i j
  rw [archEval_apply, archMatrixUpdate_apply_self]

/--
@isnad1 id=eq.1h4v.s10.2599b3bd4c56 from=translated src=- shape=5f497533 vocab=6e9ae1f6
-/
theorem archComponent_archGLIncl_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (k : GL (Fin 2) w.Completion) :
    archComponent F v (archGLIncl F w k) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show archEval F v (archMatrixUpdate F w (k : _) i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
  rw [archEval_apply, archMatrixUpdate_apply_of_ne _ _ _ _ _ hvw]

end ComponentReceipts

section AdelicInclusion

variable (F : Type) [Field F] [NumberField F]

noncomputable section

def adelicMatrixProdEquiv :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) ≃+*
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) ×
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) where
  toFun M := ((RingHom.fst _ _).mapMatrix M, (RingHom.snd _ _).mapMatrix M)
  invFun p := Matrix.of fun i j => (p.1 i j, p.2 i j)
  left_inv M := by ext i j; rfl
  right_inv p := by ext i j <;> rfl
  map_mul' M N := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]; exact map_mul _ M N
    · simp only [Prod.snd_mul]; exact map_mul _ M N
  map_add' M N := rfl

def adelicArchGLIncl : GL (Fin 2) (InfiniteAdeleRing F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (MonoidHom.id _) (1 : _ →* GL (Fin 2) _)

def adelicArchGLInclAt (w : InfinitePlace F) :
    GL (Fin 2) w.Completion →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (archGLIncl F w)

/--
@isnad1 id=eq.0h2v.s10.48d4e6093e8b from=translated src=- shape=dc9fd028 vocab=5779f4f4
-/
theorem glArch_adelicArchGLIncl (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    glArch (𝓞 F) F (adelicArchGLIncl F k) = k := by
  ext i j
  rfl

/--
@isnad1 id=eq.0h2v.s11.dac92d0d7e9f from=translated src=- shape=7138e39b vocab=a528689c
-/
theorem glFin_adelicArchGLIncl (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    glFin (𝓞 F) F (adelicArchGLIncl F k) = 1 := by
  ext i j
  rfl

end

end AdelicInclusion

section Predicate

variable (F : Type) [Field F] [NumberField F]

noncomputable def archRowIsometryAt (w : InfinitePlace F) : Subgroup (GL (Fin 2) (InfiniteAdeleRing F)) :=
  (rowIsometrySubgroup w.Completion).map (archGLIncl F w)

def HasArchCharacterAt (w : InfinitePlace F) (χ : rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ k : rowIsometrySubgroup w.Completion, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
      = (χ k : ℂ) * φ g

def HasArchType (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, HasArchCharacterAt F w (χ w) φ

/--
@isnad1 id=hasarcht.0h2v.s11.d5728b0847c3 from=translated src=- shape=74ecfef9 vocab=2064d2ab
-/
theorem hasArchType_zero (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ) :
    HasArchType F χ (fun _ => 0) := fun _ _ _ => by simp

/--
@isnad1 id=hasarcht.0h2v.s13.8a2de32ab928 from=translated src=- shape=691422ca vocab=2064d2ab
-/
theorem hasArchType_const_of_trivial (c : ℂ) :
    HasArchType F (fun _ => 1) (fun _ => c) := fun _ _ _ => (one_mul c).symm

/--
@isnad1 id=not.1h4v.s13.1484f1990f1d from=translated src=- shape=4714274a vocab=de53fe5a
-/
theorem not_hasArchCharacterAt_one_of_ne_one (w : InfinitePlace F)
    (χ : rowIsometrySubgroup w.Completion →* ℂˣ)
    (k : rowIsometrySubgroup w.Completion) (hχ : χ k ≠ 1) :
    ¬ HasArchCharacterAt F w χ (fun _ => (1 : ℂ)) := fun h => by
  have hk := h k 1
  simp only [mul_one] at hk
  exact hχ (Units.val_eq_one.mp hk.symm)

/--
@isnad1 id=not.2h5v.s13.2d746acf9859 from=translated src=- shape=f0898f29 vocab=2a22cfc9
-/
theorem not_hasArchType_const_of_exists_ne_one
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (w₀ : InfinitePlace F) (k : rowIsometrySubgroup w₀.Completion) (hχ : χ w₀ k ≠ 1)
    (c : ℂ) (hc : c ≠ 0) :
    ¬ HasArchType F χ (fun _ => c) := fun h => by
  have hk : c = (χ w₀ k : ℂ) * c := h w₀ k 1
  have : ((χ w₀ k : ℂ) - 1) * c = 0 := by linear_combination -hk
  rcases mul_eq_zero.mp this with h1 | h0
  · exact hχ (Units.val_eq_one.mp (sub_eq_zero.mp h1))
  · exact hc h0

end Predicate

end AutomorphicForm
