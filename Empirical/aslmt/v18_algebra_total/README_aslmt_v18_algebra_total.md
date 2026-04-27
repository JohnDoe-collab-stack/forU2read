# v18 — Algebra Total (multi-interface closure)

Cette famille instancie directement l’algèbre des distinctions / pertes décrite dans :

- `/mnt/c/Users/frederick/Documents/forU2read/Private_notes/distinction_arithmetic.md`
- `/mnt/c/Users/frederick/Documents/forU2read/Private_notes/algebra_to_architecture.md`

## Objet

Un épisode contient :

- un état latent `h ∈ {0,…,n-1}` (classe cachée),
- un vecteur caché `k ∈ {0,1}^{k_dim}`,
- une observation de base `O_base(h)` (visible-only),
- une séquence de requêtes `a_t ∈ {0,…,m-1}`,
- des réponses `r_t = R(h,k,a_t)` conditionnées par l’action.

La cible est :

- `Y(h,k)` (classification binaire), construite pour exiger `k` (donc requête).

## Point algébrique

On a une famille de vues requêtables indexée par `a`. Chaque requête ajoute une vue, donc une conjonction (meet)
des partitions. Le protocole vérifie :

- visible-only échoue (barrière),
- la réussite dépend des réponses action-conditionnées,
- swap / ablation sur le médiateur casse exactement ce mécanisme.

## Commandes

Smoke (CPU) :

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v18_algebra_total
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u aslmt_campaign_v18_algebra_total_matrix_diagstop.py --profile smoke --device cpu --n-classes-list 16
```

Solid (GPU) :

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v18_algebra_total
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u aslmt_campaign_v18_algebra_total_matrix_diagstop.py --profile solid --device cuda --n-classes-list 16,32
```

Paramètres par défaut :

- `m_actions = 4`
- `k_dim = 2` (cible = XOR de deux bits requêtés, donc multi-interface réel)
