/-
  VWC/Consequence.lean
  Companion to Appendix D of "Verification Without Correspondence".

  VERIFICATION STATUS: NOT COMPILED.  Depends on VWC/Ledger.lean.
  Imports: VWC.Ledger (core Lean 4 only; no Mathlib).
  Axioms declared by this file: none.  The Tarskian conditions C1-C3 and the
  soundness hypotheses are carried as structure fields or theorem
  hypotheses, not as global axioms.
-/
import VWC.Ledger

namespace VWC

/-- [DEF] A Tarskian consequence relation on contents of type `L`, over
    finite contexts represented as lists.  Fields `refl`, `mono`, `cut` are
    the conditions C1-C3 of Appendix A.  Divergence from the book: contexts
    are lists, not sets, and are finite. -/
structure Consequence (L : Type) where
  ent  : List L → L → Prop
  refl : ∀ (G : List L) (f : L), f ∈ G → ent G f
  mono : ∀ (G D : List L) (f : L), (∀ x, x ∈ G → x ∈ D) → ent G f → ent D f
  cut  : ∀ (G : List L) (f g : L), ent G f → ent (f :: G) g → ent G g

/-- [DEF] The certified context Ctx_i(o) of an obligation `o` at a stage,
    with `cont` giving the content of an obligation identifier. -/
def stageCtx {L : Type} (cont : Nat → L) (s : Stage L) (o : Nat) : List L :=
  (succs s.tr o).map cont ++ s.tr.disch.map cont ++ s.tr.assumed

/-- [DEF] The cumulative pool A_n of discharged contents and assumptions. -/
def pool {L : Type} (cont : Nat → L) : List (Stage L) → List L
  | []        => []
  | s :: rest => s.tr.disch.map cont ++ s.tr.assumed ++ pool cont rest

/-- [DEF] The cumulative context Gamma_n(S) of a list of obligations. -/
def cumCtx {L : Type} (cont : Nat → L) (ledger : List (Stage L))
    (S : List Nat) : List L :=
  (desc ledger S).map cont ++ pool cont ledger

/-- [DEF] Each stage is preserving at every obligation reached from `S`
    (the local hypothesis of the first statement of RV-008). -/
def LocallyPreserving {L : Type} (C : Consequence L) (cont : Nat → L) :
    List (Stage L) → List Nat → Prop
  | [],        _ => True
  | s :: rest, S =>
      (∀ o ∈ S, C.ent (stageCtx cont s o) (cont o)) ∧
        LocallyPreserving C cont rest (step s.tr S)

/-- [STMT; proof is `sorry`] First statement of Theorem thm:compose
    (RV-008): local preservation along the descendants gives
    Gamma_n(o) |= cont(o).  Plan: a derived lemma
    `ent_of_all : (forall x in D, ent G x) -> ent D f -> ent G f`
    (from `cut` and `mono`, by induction on `D`) together with `mono` and
    induction on the ledger.  Not attempted. -/
theorem compose_first {L : Type} (C : Consequence L) (cont : Nat → L)
    (ledger : List (Stage L)) (o : Nat)
    (hp : LocallyPreserving C cont ledger [o]) :
    C.ent (cumCtx cont ledger [o]) (cont o) := by
  sorry

/-- [DEF] Soundness of a consequence relation for an interpretation, where
    `hold` is the instance predicate Hold_I (instance data). -/
def SoundFor {L : Type} (C : Consequence L) (hold : L → Prop) : Prop :=
  ∀ (G : List L) (f : L), C.ent G f → (∀ x, x ∈ G → hold x) → hold f

/-- [PROOF-UNCHECKED] The core of the second statement of RV-008: if the
    context entails `f`, the relation is sound, and every premise holds,
    then `f` holds.  Immediate from the definition of `SoundFor`.  The
    book's second statement also needs admissibility, warrant, and the
    classification of premise sources; none of these is modelled here, so
    this is NOT a formalisation of that statement. -/
theorem transport_core {L : Type} (C : Consequence L) (hold : L → Prop)
    (sound : SoundFor C hold) (G : List L) (f : L) (h : C.ent G f)
    (hG : ∀ x, x ∈ G → hold x) : hold f :=
  sound G f h hG

#print axioms compose_first
#print axioms transport_core

end VWC
