# Independent audit of the ATLAS "Geometry of Manifolds" formalization

Status: working audit, kept separate from Appendix E. Single reader (an AI assistant); reproducible artifacts listed in §1. Nothing here has been reviewed by a human Lean or differential-geometry expert.

## 0. Question and scope

The ATLAS paper (Rammal et al., arXiv:2605.29955) reports 40 of 72 target statements formalized for *Geometry of Manifolds* (55.6%). The question is whether those 40 are (a) merely accepted by Lean, (b) faithful translations of the source statements, or (c) substantive contributions beyond Mathlib. These are tracked as three separate properties. The allegations of McCarthy and Nugent, as quoted by Bastounis–Circelli–Hansen, are treated as hypotheses to test (§6), not as findings. This audit covers one book and a purposive sample of 19 items. It does not evaluate the repository as a whole.

Evidence labels used throughout:

- **L**: checked by running Lean in this workspace.
- **R**: reproduced from the repository's `report.json` by script.
- **T**: read in source text (Lean file or lecture notes) by one reader.
- **J**: a judgment of mine that a second reader could dispute.

## 1. Artifact record

| Item | Value |
|---|---|
| Repository | `facebookresearch/atlas-lean`, HEAD `99cc25d8ba4a63e69844131ec508bb46ad526694` (7 Oct 2026) |
| Book directory | `v1/Atlas/GeometryOfManifolds/` (`report.json`, `targets.yaml`, `GeometryOfManifolds.lean`, `code/*.lean`, 82 files) |
| Lean toolchain | `leanprover/lean4:v4.29.0` (from `v1/lean-toolchain`); installed by elan |
| Mathlib | rev `8a178386ffc0f5fef0b77738bb5449d50efeea95` (from `v1/lakefile.toml`); cache fetched with `lake exe cache get` (8,232 files) |
| Source text | MIT OCW 18.966, Spring 2007 (Auroux), lecture PDFs lect01–lect25 downloaded from OCW. Whether this is byte-identical to the edition ATLAS used is **not verified**. SHA-256 prefixes, lect02 `729dda5e98ab`, lect03 `6d2529d0eab2`, lect04 `aef643afc6da`, lect05 `636cbc86e801`, lect06 `dd2d935e1713`, lect16 `2a68f4fdb0732c3d`. |
| Build | `lake build Atlas.GeometryOfManifolds.GeometryOfManifolds`: 8,330 jobs, exit 0, 22:28–22:46 ADT on 2 cores. 155 `declaration uses sorry` warnings in the log (`reproduce/build.full.log`). |

Commands (also in `reproduce/`):

```
sh elan-init.sh -y --default-toolchain none   # elan then fetches lean 4.29.0 from v1/lean-toolchain
cd v1 && lake exe cache get          # Mathlib cache
lake build Atlas.GeometryOfManifolds.GeometryOfManifolds
lake env lean AuditAxioms.lean       # #print axioms for the 71 matched declarations
lake env lean AuditInstances2.lean   # instance table for the framework classes
lake env lean AuditInstances3.lean   # defs/theorems whose type is one of the framework classes
lake env lean AuditWitness.lean      # axioms and types of the witnesses found
```

The repository's own report says `"compilation_output": "Compilation skipped"` (R). The compilation check in §2 is therefore my own and not a restatement of theirs.

## 2. Property (a): Lean acceptance

- **L** The library builds without errors at the recorded commit and environment. Every file in `code/` is imported by `GeometryOfManifolds.lean`.
- **L** Re-running `#print axioms` on all 71 matched declarations reproduces the report's `axioms` field: the presence or absence of `sorryAx` agrees in all 71 cases.
- Consequence: acceptance by Lean is not in doubt for these declarations. It says little by itself, because `sorry` is accepted (155 warnings) and because an abstract class can be satisfied by hypotheses.

## 3. What the report's own data show (R)

| Group | Targets | Reported pass |
|---|---|---|
| Definitions | 25 | 20 (80%) |
| Theorem-type (theorem 20, proposition 16, corollary 7, lemma 4) | 47 | 20 (42.6%) |
| All | 72 | 40 (55.6%) |

So half of the 40 reported successes are definitions. Of the 20 theorem-type passes:

- 6 depend on `sorryAx`: `elliptic_has_parametrix`, `elliptic_solvability`, `green_operator_decomposition`, `corollary2_green_operator_summary`, `dolbeault_cohomology_iso_harmonic`, `gompf_lefschetz_symplectic` (L).
- 14 do not.
- For `elliptic_has_parametrix`, `elliptic_solvability` and `green_operator_decomposition`, the proof body is literally `by sorry` (T: `HodgeTheory.lean` lines 1324, 1526, 1507), yet the report's `sorry_deps` field reads "None — fully proved, no sorry in dependency chain" while its `axioms` field lists `sorryAx`. The report is internally inconsistent here; the judges' prose states the sorry openly.
- Of the 31 failed declarations with a matched Lean name, 17 depend on `sorryAx` (L). One target ("Proposition 1", Chern class = Euler class) has no matched declaration.
- Faithfulness for 27 of the 40 passes is exactly 3, the threshold (R).

**The pass criterion is disclosed.** The ATLAS paper (§3) states that statements whose proof is not provided in the source "may be axiomatized", that success is judged non-transitively, and that `sorryAx` inherited from another evaluated target is not penalized. The six sorry-dependent passes follow that policy; the source lectures say "the following results can be found in Wells' book" for Theorems 1–4 of Lecture 16 (T). This is a matter of what "formalized" means in the headline figure, not a concealed defect.

## 4. The framework through which most passes are expressed

Most theorem-type passes are stated over `DifferentialFormSpace Ω VF`, an axiomatic class (`DifferentialForms.lean:14`) bundling d, ι, L, fMul and wedge with their algebraic identities, not over Mathlib manifolds (T).

- **L** Sorry-free instances exist only for toy models (`trivialDFS`, `polyDFS` on polynomials over ℝ in degrees 0–1, `symp2DFS`). The instances over Mathlib manifolds (`instManifoldDFS`) and over Euclidean space (`euclideanDFS`) contain `sorry` in their fields (T: `ManifoldDFS.lean` 15 occurrences, e.g. line 779 `ext_fdα := by intros; exact sorry`; `EuclideanDFS.lean` 4).
- **L** The classes `HasSobolevSpaces`, `IsKahler` and `IsEllipticEndo` (outside the sorry-stated `laplacian_is_elliptic_axiom`) have no witness anywhere in the library. `IsCompactOrientedRiemannian` is obtained only from `IsCompactSymplectic`, which has three witnesses. `AuditInstances3.lean` finds no definition or theorem of type `HasSobolevSpaces`, `IsKahler` or `HamiltonianFlow` other than structure fields.
- **L** `HasTubularExpMapData` and `HasIFTData` are witnessed only by `tubularExpMapData_exists` and `iftData_exists`, both of which depend on `sorryAx`. `HasRelativeHomotopyOperator` is witnessed only by `hasRelativeHomotopyOperator_of_primitives`, which takes its content as hypotheses.
- The ATLAS pipeline has a tag for this pattern (`orphan_class`); the report's judges mention it in places.

Consequence (J): a theorem proved over this class is a correct theorem about every model of the axioms, but the library never connects it to a manifold in sorry-free form. A reader cannot take such a theorem as a statement about smooth manifolds without the extra connecting step.

## 5. Sample and findings

Sampling: purposive and stratified, not random. Strata: passed definitions (6 of 20), passed theorem-type without sorry (7 of 14), passed with sorry (3 of 6 statements read in full; the other three read through the report), failed (3 of 32). This cannot estimate rates for the 40; it can show whether patterns exist.

Codes. **Correspondence**: B1 faithful within the disclosed abstraction; B2 faithful but narrower than the source; B3 conditional (substantive content moved to a hypothesis, a structure field, or a `sorry`); B4 semantically loose (admits unintended instances). **Contribution**: C1 genuine proof not in Mathlib; C2 transcription of the lecture's short algebraic argument; C3 thin Mathlib glue; C4 statement only (source defers); C5 definition only.

| idx | Source item | Lean declaration | Corr. | Contr. | Basis |
|---|---|---|---|---|---|
| 0 | Def 1 symplectic / Hamiltonian VF | `IsSymplecticVectorField` | B1 | C5 | T. L_Xω = 0; equivalence with "ι_Xω closed" is a proved lemma; the Hamiltonian half is a separate definition. |
| 3 | Def 3 standard basis | `SymplecticBasis` | B1 | C5 | T. |
| 8 | Def 5 isotropic / coisotropic / Lagrangian | `IsLagrangian` | B2 | C5 | T/L. Only the Lagrangian case is defined; no isotropic or coisotropic definition exists in the library. |
| 33 | Def 1 parametrix | `HasParametrix` | B4 | C5 | T. "Smoothing" is expressed through `IsSobRegE/F : ℕ → E → Prop`, free fields of the structure; with `IsSobReg := fun _ _ => True` every operator satisfies `IsSmoothingOp`. |
| 41 | Def 4 harmonic forms | `HarmonicForms` | B1 | C5 | T. |
| 1 | Def 2 deformation equivalent | `IsDeformationEquivalent` | B4 | C5 | T. "Continuous" refers to an arbitrary `TopologicalSpace (Ω 2)` instance. |
| 13 | Prop 3 Hamiltonian flow symplectic | `hamiltonian_flow_preserves_symplectic_form` | B1 | C2 | T. Four-line Cartan argument as in the lecture; the flow's ODE and the constancy principle are fields of `HamiltonianFlow`. |
| 27 | Prop 5 Sp∩O = Sp∩GL = O∩GL = U(n) | `sp_cap_O_eq_U` | B2 | C1 | T. Proves `Sp∩O = U`, with `Un := GLnC ∩ O2n` by definition (`MatrixGroupIntersections.lean:32`); docstring says the others "follow by the same argument". Helper lemmas for the other inclusions exist. Proof is real and sorry-free. |
| 4 | Prop 2 NX ≅ T*X | `lagrangianQuotientDualEquiv` | B2 | C3 | T. Proves V/E ≃ E* for a Lagrangian subspace of a symplectic vector space (fibrewise); no bundle, no manifold. Built from Mathlib's `liftQ`, `linearEquivOfInjective`, dual rank. |
| 2 | Prop 1 relative Poincaré lemma | `relative_poincare_lemma` | B3 | C2 | T/L. Takes a `HasRelativeHomotopyOperator` (K, the homotopy formula, K vanishes on X) as hypothesis and sets μ = Kβ. The lecture constructs μ by radial integration (T, lect05); that construction is not carried out. |
| 47 | Thm 5 Hodge | `hodge_representative_exists_unique` | B3 | C2 | T/L. Hypothesis `Nonempty (HasGreenOperatorDecomp …)`; its only witness is the sorry'd `green_operator_decomposition`. |
| 48 | Lemma 1 four Kähler identities | `kahler_identities_all_four` | B3 | C2 | T. Conclusions 3 and 4 are `fun α => identity3_L_dstar α` and `identity4_Λ_d α`, i.e. the hypotheses; conclusion 1 is a structure field; only conclusion 2 is derived (via adjointness, itself a hypothesis). The lecture defers 3 and 4 to Wells, and the judges say so. |
| 26 | Prop 4 acs submanifold symplectic | `acs_submanifold_symplectic` | B2 | C2 | T. Pointwise statement for a J-invariant subspace W ⊂ T_xM; passing from a submanifold X to W = T_xX is left to the reader. |
| 30 | Thm 1 parametrix exists | `elliptic_has_parametrix` | B1 | C4 | T/L. `by sorry`. Specialized to endomorphisms of forms of degree ≥ 1; relies on the unwitnessed `HasSobolevSpaces`. |
| 40 | Thm 3 elliptic solvability | `elliptic_solvability` | B1 | C4 | T/L. `by sorry`; same restriction. |
| 44 | Thm 4 Green operator | `green_operator_decomposition` | B1 | C4 | T/L. `by sorry`; the bounded-on-W^s clause is recast as preservation of a free regularity predicate. |
| 14 | Thm 3 tubular neighbourhood | `tubular_neighborhood_theorem` | B3 | C2 | T/L. A `def` assembling `TubularNeighborhoodData` from instance arguments `HasTubularExpMapData`, `HasIFTData`; their witnesses depend on `sorryAx`. Reported as failed; the artifacts agree. |
| 5 | Thm 1 fixed points (H¹ = 0) | `symplectomorphism_fixed_points` | B1 (see note) | C3 | T/L. Stated over Mathlib manifolds. The reduction to a closed 1-form is `weinstein_identification_bridge`, proved by `sorry`; the final step is Mathlib's extreme value theorem. Reported as failed on proof integrity; the artifacts agree. |
| 6 | Cor 1 i* isomorphism | `cohomology_isomorphism` | B3 | C2 | T. `deg0_injectivity` is a field of the hypothesis structure and restates part of the conclusion. Reported as failed; the artifacts agree. |

Note on idx 5 (J, **unresolved**): `IsClosed1Form` and `DeRhamH1Vanishes` treat a "1-form" as a function `μ : M → (E →L[ℝ] ℝ)` with symmetric `mfderiv`. That is not obviously chart-invariant, so it is not clear that `DeRhamH1Vanishes` encodes H¹(M;ℝ) = 0 for a general manifold. A decisive check would be to test whether `DeRhamH1Vanishes (𝓡 1) Circle` is provable. I did not do this.

### Confirmed discrepancies (T or L, between a reported pass and the source or between report fields)

1. Prop 5 (idx 27) is reported faithful at score 3, but the Lean theorem states one of the equalities in the source's chain, with U(n) defined as GL∩O.
2. Definition 5 (idx 8) is reported as passing at score 3, but the isotropic and coisotropic cases are absent.
3. `elliptic_has_parametrix`, `elliptic_solvability` and `green_operator_decomposition` have `sorry` bodies, while the report's `sorry_deps` field says "None — fully proved".
4. Relative Poincaré lemma (idx 2) passes while Corollary 1 (idx 6) fails for a similar pattern (content in a hypothesis structure), so the rubric was applied unevenly (J, but both pieces of evidence are in the report).
5. `kahler_identities_all_four` has two of four conclusions equal to hypotheses and is labelled "all four" in its name and docstring.

### Interpretive concerns (J)

- Definitions 1 (parametrix) and 2 (deformation equivalence) admit degenerate instances through free predicate or topology data.
- Most theorem-type passes live in an axiomatic class that is never connected to manifolds without `sorry` (§4).
- Passes at faithfulness 3 may be correct readings under the rubric but are not evidence of an unconditional statement.

### Unresolved

- Whether `DeRhamH1Vanishes` captures H¹ = 0.
- The 14 passed definitions and 7 passed theorem-type statements without `sorry` that I did not read in full, and three sorry-dependent passes I assessed only through the report.
- Whether the OCW edition equals the edition used by ATLAS.
- Whether the lecture-note statements themselves carry a hidden hypothesis the Lean encoding drops or adds (I checked only the sampled ones).

## 6. The two allegations as hypotheses

Source of the quotations: Bastounis–Circelli–Hansen, reproducing a Lean-community thread I could not read in the original (Appendix E items 30–31 remain **unverified**).

- **H1 (McCarthy)**: for the book with the 56% figure, "0% of the statements here are accurately formalized". The 56% matches only *Geometry of Manifolds* in Table 1 (T: 40/72 = 55.6%; the next nearest are 59.5% and 59.8%). The criterion for "accurately" and the "fatal error like above" are not available to me.
  - **Not supported as stated.** Several sampled passes are accurate under the paper's own criterion: idx 0, 3, 41, 13, and 26 at the pointwise level.
  - **Partly supported under a stricter reading.** If "accurate" means unconditional and about actual manifolds, then none of the 13 sampled theorem-type items qualifies, except idx 5, which is a reported failure. The sampled theorem-type passes are either conditional (idx 2, 47, 48), narrower than the source (27, 4, 26), or statements without proof (30, 40, 44).
- **H2 (Nugent)**: this was stated for the *algebraic geometry* folder (successes = what is in Mathlib; failures = everything else). It was not stated for this book, so I test only an analogue.
  - **Not supported for this book.** Mathlib has no symplectic geometry, Hodge theory or Kähler geometry; the passes are custom definitions, linear algebra (idx 27, 4, 8), short derivations in the custom framework, and deferred statements. Mathlib reuse is visible only in glue (idx 4, 5, 27).
  - A different pattern does appear: passes concentrate on definitional or algebraic content, and the analytic content (tubular neighbourhood, IFT, ellipticity, Sobolev theory) is either `sorry` or a hypothesis.

Overall reading (J): the 40 of 72 is an honestly computed number under a stated, permissive criterion. Counted as "40 formalized theorems" it overstates what was achieved. It is 20 definitions plus 20 theorem-type items, of which 6 are deferred statements and about half of the rest are conditional or narrower than the source.

## 7. Limits

- One reader, an AI assistant; the classification is not blind to the report's own scores, and I read the judges' feedback before several of the Lean files.
- Sample of 19 of 72 targets, purposive, no inferential claims about rates.
- Lecture statements were read from text extraction of the OCW PDFs; notation may be damaged in places (e.g. `Λ`, `∗`).
- `#print axioms` shows what a declaration depends on, not whether its statement is the intended one.
- The heuristic name-based sorry closure I first tried (`sorrydeps.py`) over-approximates because of name collisions and is not used for any finding; every sorry claim above is from `#print axioms`, a direct reading, or the report's own field.

## 8. What would make this stronger

1. A second reader with Lean and symplectic-geometry background, working from `reproduce/report_table.csv` and blind to the judges' scores.
2. Settle idx 5 by testing `DeRhamH1Vanishes` on the circle.
3. Read the remaining 24 passes and a larger random sample of the failures.
4. Obtain the original thread, then compare McCarthy's examples with this table.
