/-
  VWC/MathlibToy.lean
  Companion to Appendix D of "Verification Without Correspondence".

  VERIFICATION STATUS: NOT COMPILED.  REQUIRES MATHLIB (version not
  determined; to be recorded at first compile).  Not imported by the other
  modules.  Several lemma names below (`Nat.sInf_empty`, `Nat.find`,
  `Nat.find_spec`, `Set.mem_setOf_eq`) are assumed from memory of Mathlib
  and may have been renamed.

  Purpose: illustrate, for the polynomial p_e(n, x1, x2) = x1 + x2 - n
  reported by Bastounis, Circelli and Hansen (Example 4.2 of their paper),
  (a) the silent default of `sInf` on an empty set of naturals and (b) a
  hypothesis-carrying definition that cannot be applied unless existence
  has been supplied.  This restates a toy case; it formalises nothing of
  Theorem A.3 or A.4.
-/
import Mathlib

namespace VWC

/-- [DEF] B n: for all natural x1 x2, x1 + x2 - n is nonzero (over Int). -/
def B (n : Nat) : Prop :=
  ∀ x1 x2 : Nat, ((x1 : Int) + (x2 : Int) - (n : Int)) ≠ 0

/-- [PROOF-UNCHECKED] No `n` satisfies `B`: take (x1, x2) = (n, 0). -/
theorem B_false (n : Nat) : ¬ B n := by
  intro h
  exact h n 0 (by simp)

/-- [PROOF-UNCHECKED] The witness set is empty. -/
theorem B_set_empty : {n : Nat | B n} = ∅ := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact B_false n

/-- [DEF] The silent-default definition: `sInf` of an empty set is 0. -/
noncomputable def nSilent : Nat := sInf {n : Nat | B n}

/-- [PROOF-UNCHECKED] The silent default assigns 0 although no witness
    exists.  Relies on the assumed name `Nat.sInf_empty`. -/
theorem nSilent_eq_zero : nSilent = 0 := by
  unfold nSilent
  rw [B_set_empty]
  exact Nat.sInf_empty

/-- [DEF] Hypothesis-carrying definition: applicable only given a proof of
    existence.  Uses classical decidability to apply `Nat.find`. -/
open Classical in
noncomputable def nChecked (h : ∃ n, B n) : Nat := Nat.find h

/-- [PROOF-UNCHECKED] The checked definition satisfies the defining
    property. -/
open Classical in
theorem nChecked_spec (h : ∃ n, B n) : B (nChecked h) :=
  Nat.find_spec h

/-- [PROOF-UNCHECKED] For this toy case existence fails, so `nChecked`
    can never be applied. -/
theorem no_witness : ¬ ∃ n, B n := by
  rintro ⟨n, hn⟩
  exact B_false n hn

end VWC
