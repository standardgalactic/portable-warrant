/-
  VWC/Ledger.lean
  Companion to Appendix D of "Verification Without Correspondence".

  VERIFICATION STATUS: NOT COMPILED.  No Lean toolchain was available when
  this file was written.  Every declaration below is unchecked.  The tags
  [DEF], [STMT], [PROOF-UNCHECKED] describe what the author INTENDS each
  declaration to be; none is a verified proved declaration until this file
  has been compiled and `#print axioms` has been inspected.

  Imports: none (core Lean 4 only).
  Axioms declared by this file: none.
  Placeholders: every `sorry` is listed in the Appendix D table.
-/

namespace VWC

/-- [DEF] Obligation statuses (Definition def:status of Appendix A). -/
inductive Status where
  | open_
  | supported
  | discharged
  | refuted
  | defeated
  deriving DecidableEq

/-- [DEF] Kinds of obligation (a subset of the kinds used in the book). -/
inductive Kind where
  | formal
  | statement
  | argument
  | dependency
  | assumption
  deriving DecidableEq

/-- [DEF] An obligation.  The book's tuple (tau, phi, rho, E, D, sigma) is
    reduced here to an identifier, a kind, a content and a status.  The
    evidence, dependency and residue fields are NOT modelled. -/
structure Obligation (L : Type) where
  id      : Nat
  kind    : Kind
  content : L
  status  : Status

/-- [DEF] A transition certificate T_i = (Q_i, Delta_i, Theta_i).  `succ`
    lists pairs (o, o') in Ob_{i-1} x Ob_i; `disch` is Delta_i; `assumed` is
    Theta_i.  Obligations are referred to by `Nat` identifiers. -/
structure Transition (L : Type) where
  succ    : List (Nat × Nat)
  disch   : List Nat
  assumed : List L

/-- [DEF] A stage pairs a transition with the list of identifiers of the
    obligations of Ob_{i-1} that it must account for. -/
structure Stage (L : Type) where
  inputs : List Nat
  tr     : Transition L

/-- [DEF] succ_i(o): the successors of `o` under a transition. -/
def succs {L : Type} (t : Transition L) (o : Nat) : List Nat :=
  (t.succ.filter (fun p => p.1 == o)).map (fun p => p.2)

/-- [DEF] One step of the descendant relation, extended to lists. -/
def step {L : Type} (t : Transition L) : List Nat → List Nat
  | []      => []
  | o :: os => succs t o ++ step t os

/-- [DEF] S_n(o), generalised to a list: the descendants after all stages. -/
def desc {L : Type} : List (Stage L) → List Nat → List Nat
  | [],      S => S
  | s :: ss, S => desc ss (step s.tr S)

/-- [DEF] `o` is discharged by the transition or is accounted for by a
    successor (the well-formedness condition on one input). -/
def Covers {L : Type} (t : Transition L) (o : Nat) : Prop :=
  o ∈ t.disch ∨ ∃ p ∈ t.succ, p.1 = o

/-- [DEF] A stage is well-formed when it accounts for all its inputs. -/
def WellFormed {L : Type} (s : Stage L) : Prop :=
  ∀ o ∈ s.inputs, Covers s.tr o

/-- [DEF] Is `o` an input of the first stage of a ledger?  (Vacuous for the
    empty ledger.) -/
def Accepts {L : Type} : List (Stage L) → Nat → Prop
  | [],     _ => True
  | s :: _, o => o ∈ s.inputs

/-- [DEF] A ledger is well-formed when each stage is, and each successor
    produced by a stage is an input of the next stage. -/
def WFLedger {L : Type} : List (Stage L) → Prop
  | []        => True
  | s :: rest =>
      WellFormed s ∧ (∀ p ∈ s.tr.succ, Accepts rest p.2) ∧ WFLedger rest

/-- [DEF] `o` has a certified discharge in its ancestry: some descendant is
    in Delta_k at some stage k. -/
def DischargedIn {L : Type} : List (Stage L) → Nat → Prop
  | [],        _ => False
  | s :: rest, o =>
      o ∈ s.tr.disch ∨ ∃ o' ∈ succs s.tr o, DischargedIn rest o'

/-- [PROOF-UNCHECKED] `step` distributes over append.  A short induction;
    the `simp` call is the step most likely to need adjustment. -/
theorem step_append {L : Type} (t : Transition L) (a b : List Nat) :
    step t (a ++ b) = step t a ++ step t b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [step, ih, List.append_assoc]

/-- [STMT; proof is `sorry`] Theorem thm:trace (RV-020), in the form: in a
    well-formed ledger, an input obligation with no certified discharge in
    its ancestry has a descendant after the last stage.
    Plan: induction on the ledger, generalising `o`.  In the cons case,
    `Covers` and `not DischargedIn` give a successor p.2 of o with
    `not DischargedIn rest p.2` and `Accepts rest p.2`; the induction
    hypothesis gives `desc rest [p.2] ≠ []`; `step_append` and a lemma
    `desc ss (a ++ b) = desc ss a ++ desc ss b` lift this to
    `desc rest (step s.tr [o])`.  That distributivity lemma is not stated
    above and is part of the unfinished work. -/
theorem trace {L : Type} (ledger : List (Stage L)) (o : Nat)
    (hwf : WFLedger ledger) (hin : Accepts ledger o)
    (hnd : ¬ DischargedIn ledger o) :
    desc ledger [o] ≠ [] := by
  sorry

#print axioms step_append
#print axioms trace

end VWC
