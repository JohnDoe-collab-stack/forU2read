import Lake
open Lake DSL

package «compat_obstructions» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CompatObstructions» where
  roots := #[
    `COFRS.Foundations,
    `COFRS.Dynamics,
    `COFRS.ConverseNormalForm,
    `COFRS.RegulationAndReduction,
    `COFRS.Synthesis,
    `COFRS.Examples.GodelByCode,
    `COFRS.Examples.DiagonalizationMediationCausalityThesis,
    `COFRS.Examples.CorrelationRegimeAppendix,
    `COFRS.Examples.AutoreflexiveQueryArchitecture,
    `COFRS.Examples.GeometryDynamicsIndependence,
    `COFRS.Examples.DynamicCompatDimN,
    `COFRS.Examples.RelativeCoherenceSpectra,
    `COFRS.Examples.OrdinalCoherenceSpectra,
    `COFRS.Examples.FiniteSpectralHeight,
    `COFRS.Examples.IndependenceRelationMediationChain,
    `COFRS.Examples.IndependenceToAutoreflexiveQueryBridge,
    `COFRS.Examples.IndependenceToAutoreflexiveQueryStrongBridge,
    `COFRS.Examples.IndependenceToAutoreflexiveQueryRefiningLiftBridge,
    `COFRS.Examples.ReferentialInduction,
    `COFRS.Examples.EntropicClosureDefect,
    `COFRS.Combinatorics.FinCompression,
    `COFRS.Main,
    ]

/- AXIOM_AUDIT_BEGIN -/
/-!
## Axiom audit
This is a Lake configuration file and defines no Lean library declarations to audit.
-/
-- (no declarations in this file)
/- AXIOM_AUDIT_END -/
