/-
  VWC/ToyExamples.lean
  Companion to Appendix D of "Verification Without Correspondence".

  VERIFICATION STATUS: NOT COMPILED.  Depends on VWC/Ledger.lean.
  Imports: VWC.Ledger (core only).
  These `example`s are sanity checks of the DEFINITIONS on a two-stage toy
  ledger.  They do not test any theorem of the book, and a successful
  compile would not show that the definitions match Appendix A.
-/
import VWC.Ledger

namespace VWC

/-- Toy transitions over contents of type `String`.  Obligation 0 is
    carried to obligation 1 at stage one, and obligation 1 is discharged at
    stage two. -/
def t1 : Transition String := { succ := [(0, 1)], disch := [], assumed := [] }
def t2 : Transition String := { succ := [], disch := [1], assumed := [] }

def toy : List (Stage String) :=
  [ { inputs := [0], tr := t1 }, { inputs := [1], tr := t2 } ]

/-- [DEF-CHECK; unchecked] Descendants of obligation 0 after both stages:
    none, because obligation 1 is discharged at stage two. -/
example : desc toy [0] = [] := by decide

/-- [DEF-CHECK; unchecked] After stage one alone, obligation 1 remains. -/
example : desc [({ inputs := [0], tr := t1 } : Stage String)] [0] = [1] := by
  decide

end VWC
