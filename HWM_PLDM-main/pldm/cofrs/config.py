from dataclasses import dataclass

from pldm.configs import ConfigBase


@dataclass
class COFRSConfig(ConfigBase):
    enabled: bool = False

    # Run a lightweight mediator audit for hierarchical D4RL planning.
    audit_hierarchical_d4rl: bool = True

    # Number of environments to use for the audit (kept small on purpose).
    audit_n_envs: int = 2

    # Seed controlling permutations used by the audit.
    audit_seed: int = 0

    # L2 norm threshold used to count "action changed" events.
    action_change_eps: float = 1e-6

    # Threshold for "swap follows permutation" comparisons.
    action_perm_eps: float = 1e-6

    # Include an ablation counterfactual (constant/zero mediator).
    audit_include_ablation: bool = True

    # Optional small-N closure probe (flat vs hierarchical) on a fresh set of envs.
    closure_probe_enabled: bool = False
    closure_probe_n_envs: int = 2
    closure_probe_max_steps: int = 100
    closure_probe_seed_offset: int = 10000
