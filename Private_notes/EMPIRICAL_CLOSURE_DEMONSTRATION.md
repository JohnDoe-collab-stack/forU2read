# Empirical Demonstration by Certificate: Controlled Closure → Unique-Branch Readout

This note specifies a **non-cherry-pickable**, **falsifiable**, and **independently verifiable**
empirical demonstration of the claim:

> An agent learns **controlled closure** and then **reads the unique remaining branch**.

No acceptance is based on a single aggregate score threshold. The demonstration is by
**episode-level certificates** and a **structural verifier** that searches for counterexamples.

---

## 0. Setting (finite algebraic world)

An episode defines a finite latent space:

- `X = {0,…,N−1}` (latent states).
- `tables : (V,N)` view interface; base view is `0`.
- `sigma : (N,)` with values in `{0,1}` (target signature).
- `x ∈ X` (true latent).
- `base_obs := tables[0,x]`.
- budget `T := max_steps`.
- STOP action id `STOP := V`.

A transcript prefix is:

- `τ_t := (base_obs, (a_0,r_0), …, (a_{t-1},r_{t-1}))`.

Define the **exact candidate set** induced by the transcript:

- `F_{τ_t} := { s ∈ X : tables[0,s]=base_obs ∧ ∀i<t, (a_i≠STOP ⇒ tables[a_i,s]=r_i) }`.

Define the **exact ambiguity**:

- `Amb_σ(F_{τ_t}) := |{ sigma[s] : s ∈ F_{τ_t} }|`.

Define **objective closure**:

- `τ_t` is closed ⇔ `Amb_σ(F_{τ_t}) = 1`.

When closed, define the unique value:

- `σ*(τ_t)` = the unique value of `sigma[s]` on `F_{τ_t}`.

---

## 1. What must be demonstrated (episode-level, falsifiable)

The agent outputs:

- a length-`T` transcript `(actions[0..T-1], responses[0..T-1])`, padded with STOP after the first STOP,
- a prediction `ŷ ∈ {0,1}`.

An episode is **CERTIFIED OK** iff all of the following properties hold:

### P1 — Protocol legality

- `a_t ∈ {1,…,V−1} ∪ {STOP}` (view0 forbidden),
- no repeated non-STOP views (if that is a protocol rule),
- STOP persistence: if `a_t = STOP` then for all `u>t`, `a_u = STOP`.

### P2 — Closure at STOP (invariant-controlled stopping)

Let `t_stop` be the first index with `a_{t_stop}=STOP` (or `t_stop=T` if STOP never occurs). Then:

- `Amb_σ(F_{τ_{t_stop}}) = 1`.

### P3 — Unique-branch readout

- `ŷ = σ*(τ_{t_stop})`.

This is checked only through `F_{τ_{t_stop}}` recomputed exactly from the transcript.

### P4 — Monotone contraction (recommended)

For all `t<T`:

- `F_{τ_{t+1}} ⊆ F_{τ_t}` and thus `Amb_σ(F_{τ_{t+1}}) ≤ Amb_σ(F_{τ_t})`.

### P5 — Non-degeneracy

- `F_{τ_0} ≠ ∅`,
- `F_{τ_{t_stop}} ≠ ∅`.

Any violation is a counterexample.

---

## 2. Robustness (without score thresholds)

We fix **in advance** a frozen benchmark:

- exact IID seeds,
- exact OOD seeds,
- episodes per seed,
- fixed config `(N,V,T,obs_vocab,…)`.

**Robust** means:

> The structural verifier finds **zero counterexamples** to P1–P3 (and ideally P4–P5) on the frozen IID benchmark and on the frozen OOD benchmark.

No “average accuracy” acceptance rule is used.

---

## 3. Anti-cheating / anti-selection rules

To prevent any cherry-picking:

1) **Pre-registration**: publish frozen seeds/config before running.
2) **Full coverage**: the certificate must include *all* episodes; verifier fails if line count is not exact.
3) **Provenance**: record SHA256 hashes for:
   - certify script,
   - verify script,
   - episode generator,
   - model weights (or checkpoint file).
4) **Independent verification**: verifier does not depend on training code; it only recomputes `F_τ` and `Amb`.
5) **Counterexample disclosure**: if it fails, publish the counterexample list with reproduction.

---

## 4. Required artifacts (“proof objects”)

### 4.1 Episode certificate JSONL (one line per episode)

Each line must contain everything needed to verify P1–P5.

Minimal schema:

```json
{
  "run_meta": {
    "run_tag": "...",
    "timestamp": "...",
    "sha256": {
      "certify_script": "...",
      "verify_script": "...",
      "env_script": "...",
      "model_weights": "..."
    },
    "config": {
      "N": 64, "V": 8, "T": 3, "obs_vocab": 16,
      "split": "iid|ood",
      "seed": 0
    }
  },
  "episode_id": 12345,
  "episode": {
    "tables": [[...],[...],...],
    "sigma": [...],
    "x": 17,
    "base_obs": 5
  },
  "agent": {
    "actions": [2,7,8],
    "responses": [9,3,0],
    "y_pred": 1
  }
}
```

### 4.2 Verification reports

- `verify_report.json`: counts + violation list.
- `verify_report.txt`: human-readable summary.

---

## 5. Structural verifier algorithm (exact)

For each JSONL line:

1) Recompute `F_{τ_0} := { s : tables[0,s]=base_obs }`.
2) For `t=0..T-1`, update:
   - if `a_t != STOP`, set `F := F ∩ { s : tables[a_t,s]=r_t }`,
   - else do nothing (STOP does not refine).
3) At each `t`, compute:
   - `Amb(t) = |unique(sigma[s] for s in F)|` (0 if `F` empty).
4) Let `t_stop` be first `t` where `a_t=STOP` else `t_stop=T`.
5) Check P1–P5.
6) If violation, record counterexample with:
   - `episode_id`, violated property, `actions`, `responses`, `t_stop`, `Amb_trace`, and `|F|` trace.

The verifier returns “OK” iff the violation list is empty.

---

## 6. Demonstrating “learned” vs “hardcoded”: negative controls (optional but strong)

Produce additional certificates for interventions expected to fail structurally:

- Forced random action: should violate P2 massively.
- Remove informative views: should violate P2.
- Swap interventions: should violate P2/P3 detectably.

The verifier should then output counterexamples, proving the task is nontrivial.

---

## 7. What this demonstration concludes (and does not)

If the verifier finds zero counterexamples on frozen IID and OOD benchmarks:

- We conclude, empirically and reproducibly, that the agent produces legal transcripts, achieves objective closure at STOP, and reads the unique branch value.

This does not prove universality for all `N,V,T` or all possible distributions.

---

## 8. Paper-level one-liner (faithful to the above)

> We replace passive prediction by controlled closure: in a finite latent algebra, the agent chooses queries that contract the exact candidate set `F_τ`. Closure is certified by `Amb_σ(F_τ)=1`, and prediction is verified as the unique branch readout `σ*(τ)`, with episode-level certificates checked by an independent structural verifier on frozen IID/OOD benchmarks.

