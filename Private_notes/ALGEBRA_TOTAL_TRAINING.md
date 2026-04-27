# v18_algebra_total — entraînement direct sur l’algèbre (distinctions → pertes → clôture)

Ce document relie explicitement la famille empirique :

`/mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v18_algebra_total`

aux deux notes :

- `/mnt/c/Users/frederick/Documents/forU2read/Private_notes/distinction_arithmetic.md`
- `/mnt/c/Users/frederick/Documents/forU2read/Private_notes/algebra_to_architecture.md`

## 1) Objets

Un épisode fixe :

- `h ∈ {0,…,n-1}` : classe latente (visible au solveur),
- `k ∈ {0,1}^{k_dim}` : bits cachés,
- `Y(h,k)` : vérité cible binaire,
- `m_actions` : famille de vues requêtables.

La politique produit une action **par composante** :

`a ∈ {0,…,m_actions-1}^{k_dim}`.

La réponse de l’environnement est :

`r ∈ {0,1}^{k_dim}`.

## 2) Clôture active (mécanisme)

Pour chaque composante `j`, il existe une interface correcte :

`a_j = (h + j) mod m_actions`.

La réponse vaut :

- `r_j = k_j` si `a_j` est choisi,
- `r_j = 0` sinon.

La cible vaut :

`Y = (k_0 ⊕ k_1) ⊕ (h mod 2)`.

Donc :

- visible-only (h seul) ne ferme pas `Y`,
- la clôture exige obtenir `k_0` et `k_1` via les deux actions correctes.

## 3) Lecture “algèbre des pertes”

Intuition (sur `ΔX`) :

- `R_σ` : distinctions requises par `Y`,
- chaque vue `E_i` induit des confusions `C_i`,
- la perte requise de la vue est `L_i = R_σ ∩ C_i`,
- la conjonction de vues contracte la perte par intersection :
  `L_res(I) = ⋂_{i∈I} L_i`.

Dans `v18`, la politique choisit une famille d’interfaces (une par composante) de sorte que la perte résiduelle tombe à vide :

- `q_acc ≈ 1` implique `r ≈ k` (sur les composantes auditées),
- puis la tête de décision ferme `Y` :
  `A_acc ≈ 1`.

## 4) Audit minimal

Le verifier exige (IID et OOD) :

- baseline visible-only : `B_acc` proche du hasard,
- solveur actif : `A_acc` haut,
- médiateur : `z_acc` haut,
- requête : `q_acc` haut.

Ainsi, la réussite suit explicitement :

`z → requête → réponse conditionnée → décision`.

## 5) Commandes

Smoke (CPU) :

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v18_algebra_total
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u aslmt_campaign_v18_algebra_total_matrix_diagstop.py --profile smoke --device cpu --n-classes-list 16 --seed-from 0 --seed-to 0
```

Solid (GPU) :

```bash
cd /mnt/c/Users/frederick/Documents/forU2read/Empirical/aslmt/v18_algebra_total
/home/frederick/.venvs/cofrs-gpu/bin/python3 -u aslmt_campaign_v18_algebra_total_matrix_diagstop.py --profile solid --device cuda --n-classes-list 16 --seed-from 0 --seed-to 4
```

