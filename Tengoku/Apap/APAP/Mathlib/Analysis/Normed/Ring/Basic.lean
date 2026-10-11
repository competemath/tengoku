module

public import Tengoku

public section

variable {R : Type*} [SeminormedRing R] {a b c : R}

/--
@isnad1 id=le.1h4v.s7.152c2e4096a8 from=translated src=- shape=5d21432c vocab=674f30b4
-/
lemma norm_one_sub_mul (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ := by
  calc ‖c - a * b‖ = ‖(c - a) + a * (1 - b)‖ := by noncomm_ring
    _ ≤ ‖c - a‖ + ‖1 - b‖ := by grw [norm_add_le, norm_mul_le, ha, one_mul]

/--
@isnad1 id=le.1h4v.s7.3e740fd67c63 from=translated src=- shape=97f116ac vocab=674f30b4
-/
lemma norm_one_sub_mul' (hb : ‖b‖ ≤ 1) : ‖c - a * b‖ ≤ ‖1 - a‖ + ‖c - b‖ :=
  (norm_one_sub_mul (R := Rᵐᵒᵖ) hb).trans_eq (add_comm _ _)

/--
@isnad1 id=le.1h4v.s7.f98d1afaa76a from=translated src=- shape=5d21432c vocab=2ad4b0dd
-/
lemma nnnorm_one_sub_mul (ha : ‖a‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖c - a‖₊ + ‖1 - b‖₊ :=
  norm_one_sub_mul ha

/--
@isnad1 id=le.1h4v.s7.14ab410a5f96 from=translated src=- shape=97f116ac vocab=2ad4b0dd
-/
lemma nnnorm_one_sub_mul' (hb : ‖b‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖1 - a‖₊ + ‖c - b‖₊ :=
  norm_one_sub_mul' hb
