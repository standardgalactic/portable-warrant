import Lake
open Lake DSL

-- NOT COMPILED.  The Mathlib dependency is needed only by VWC/MathlibToy.lean.
-- Pin `rev` to the Mathlib revision matching the chosen lean-toolchain and
-- record it in Appendix D.  Left unpinned deliberately: no version was checked.
package vwc

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "UNPINNED"

@[default_target]
lean_lib VWC
