# Plan — Universal obs-only no-go and minimal lift (Empirical protocol)

This note states the *empirical* protocol-level plan that mirrors the COFRS spine:

1. **Universal obs-only no-go at decision time** (fiber barrier): exhibit paired situations where the decision-time observable is identical while the relevant future truth differs.
2. **Lift / mediator existence**: exhibit a model/policy family that restores correctness by using an internal mediator that is not present in the observable interface at decision time.
3. **Causal mediation (intervention signature)**: audit that correctness depends on the mediator by interventions (ablation + permutation/swap), ruling out accidental visible shortcuts.

In this repository, this plan is instantiated by the ASLMT empirical suite under `Empirical/aslmt/`.

- For the v7 “pair-grade OOD-required” witness, the fiber barrier is audited by `pair_eval.*.obs_barrier_ok` and the protocol-grade criterion is enforced by the strict verifier.
- For the law-v5b and law-v3b families, the mediator is audited by explicit ablation and swap/permutation tests.
