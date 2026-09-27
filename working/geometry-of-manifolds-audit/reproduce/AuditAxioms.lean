import Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
import Atlas.GeometryOfManifolds.code.ChernFormGrading
import Atlas.GeometryOfManifolds.code.CohomologyIsomorphismConcrete
import Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Atlas.GeometryOfManifolds.code.ConnectionsCurvature
import Atlas.GeometryOfManifolds.code.Counterexamples
import Atlas.GeometryOfManifolds.code.DonaldsonApproxHolomorphic
import Atlas.GeometryOfManifolds.code.DonaldsonHolomorphicApprox
import Atlas.GeometryOfManifolds.code.DonaldsonLefschetz
import Atlas.GeometryOfManifolds.code.EllipticParametrix
import Atlas.GeometryOfManifolds.code.FourManifoldsSW
import Atlas.GeometryOfManifolds.code.GaugeAction
import Atlas.GeometryOfManifolds.code.HamiltonianVectorFields
import Atlas.GeometryOfManifolds.code.HodgeTheory
import Atlas.GeometryOfManifolds.code.KahlerManifolds
import Atlas.GeometryOfManifolds.code.LefschetzFibrationMathlib
import Atlas.GeometryOfManifolds.code.LefschetzPencils
import Atlas.GeometryOfManifolds.code.MatrixGroupIntersections
import Atlas.GeometryOfManifolds.code.MoserDarboux
import Atlas.GeometryOfManifolds.code.NijenhuisGoals
import Atlas.GeometryOfManifolds.code.ParametrixOnManifold
import Atlas.GeometryOfManifolds.code.PontrjaginObstructions
import Atlas.GeometryOfManifolds.code.SWModuliGoal62
import Atlas.GeometryOfManifolds.code.SpinCConnectionsAffine
import Atlas.GeometryOfManifolds.code.SymplecticFibrations
import Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Atlas.GeometryOfManifolds.code.SymplecticManifolds
import Atlas.GeometryOfManifolds.code.SymplecticStandardBasis
import Atlas.GeometryOfManifolds.code.SymplectomorphismFixedPoints
import Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood
set_option pp.fieldNotation false
/- idx 6 -/
#print axioms DeRhamConcrete.cohomology_isomorphism
/- idx 65 -/
#print axioms DiracOperator
/- idx 57 -/
#print axioms Donaldson.donaldson_proposition_1_book
/- idx 61 -/
#print axioms FiberSum
/- idx 42 -/
#print axioms IsEllipticOperatorOnManifold
/- idx 56 -/
#print axioms LefschetzFibrationMathlib
/- idx 25 -/
#print axioms SymplecticLinearAlgebra.compatible_forms_convex_linear
/- idx 19 -/
#print axioms almost_complex_structure_criterion
/- idx 23 -/
#print axioms chern_number_formula
/- idx 66 -/
#print axioms clifford_isomorphisms_exist
/- idx 58 -/
#print axioms donaldson_holomorphic_approximation_exp_bound
/- idx 59 -/
#print axioms donaldson_theorem3_axiom
/- idx 32 -/
#print axioms elliptic_fredholm
/- idx 31 -/
#print axioms elliptic_regularity
/- idx 20 -/
#print axioms firstChernClassRep
/- idx 67 -/
#print axioms gauge_action_preserves_solutions
/- idx 18 -/
#print axioms hirzebruch_signature_theorem
/- idx 38 -/
#print axioms isIntegrable_of_hasHolomorphicCoords
/- idx 60 -/
#print axioms kodaira_thurston_first_betti
/- idx 12 -/
#print axioms lagrangian_intersection_c1_close
/- idx 49 -/
#print axioms lemma2_L2_adjointness
/- idx 15 -/
#print axioms local_moser_theorem4_book
/- idx 68 -/
#print axioms positive_scalar_curvature_vanishing
/- idx 24 -/
#print axioms sections_principle_Mathlib
/- idx 70 -/
#print axioms spinc_connections_affine
/- idx 69 -/
#print axioms spinc_theorem3_complete
/- idx 62 -/
#print axioms sw_moduli_space_theorem1
/- idx 5 -/
#print axioms symplectomorphism_fixed_points
/- idx 53 -/
#print axioms thurston_symplectic_fibration
/- idx 14 -/
#print axioms tubular_neighborhood_theorem
/- idx 16 -/
#print axioms weinstein_lagrangian_neighborhood_book3
/- idx 34 -/
#print axioms Codifferential
/- idx 27 -/
#print axioms CompatibleTriple.sp_cap_O_eq_U
/- idx 28 -/
#print axioms Connection
/- idx 41 -/
#print axioms HarmonicForms
/- idx 33 -/
#print axioms HasParametrix
/- idx 1 -/
#print axioms IsDeformationEquivalent
/- idx 71 -/
#print axioms IsSWSolution
/- idx 63 -/
#print axioms IsSWSolutionWith
/- idx 0 -/
#print axioms IsSymplecticVectorField
/- idx 37 -/
#print axioms JActsOnForms.laplacian_C_eq_laplacian
/- idx 29 -/
#print axioms MetricCompatible
/- idx 43 -/
#print axioms ParametrixOnManifold.HasParametrixOnManifold
/- idx 64 -/
#print axioms SWModuliSpace
/- idx 55 -/
#print axioms SymplecticFibration
/- idx 8 -/
#print axioms SymplecticLinearAlgebra.IsLagrangian
/- idx 7 -/
#print axioms SymplecticLinearAlgebra.IsSymplecticSubspace
/- idx 3 -/
#print axioms SymplecticLinearAlgebra.SymplecticBasis
/- idx 9 -/
#print axioms SymplecticLinearAlgebra.symplecticVolumeForm
/- idx 10 -/
#print axioms SymplecticManifold
/- idx 11 -/
#print axioms Symplectomorphism
/- idx 4 -/
#print axioms WeinsteinNeighborhood.lagrangianQuotientDualEquiv
/- idx 26 -/
#print axioms acs_submanifold_symplectic
/- idx 45 -/
#print axioms corollary2_green_operator_summary
/- idx 52 -/
#print axioms corollary4_kahler_hodge
/- idx 50 -/
#print axioms dolbeault_cohomology_iso_harmonic
/- idx 30 -/
#print axioms elliptic_has_parametrix
/- idx 40 -/
#print axioms elliptic_solvability
/- idx 17 -/
#print axioms gauge_transformation_curvature
/- idx 54 -/
#print axioms gompf_lefschetz_symplectic
/- idx 44 -/
#print axioms green_operator_decomposition
/- idx 13 -/
#print axioms hamiltonian_flow_preserves_symplectic_form
/- idx 46 -/
#print axioms hodge_decomposition_orthogonal
/- idx 47 -/
#print axioms hodge_representative_exists_unique
/- idx 36 -/
#print axioms hodge_star_pq_type
/- idx 48 -/
#print axioms kahler_identities_all_four
/- idx 51 -/
#print axioms kahler_laplacian_identity
/- idx 35 -/
#print axioms laplacian
/- idx 39 -/
#print axioms nijenhuis_dual_map_is_d_20_typed
/- idx 2 -/
#print axioms relative_poincare_lemma
/- idx 22 -/
#print axioms totalChernFormGeometric
