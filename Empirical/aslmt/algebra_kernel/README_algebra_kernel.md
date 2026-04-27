# Algebra Kernel (exact)

Ce dossier contient un **noyau algébrique exact** pour la “clôture par distinctions” :

- partitions / confusions,
- distinctions requises `R_σ`,
- pertes `L_σ(E)`,
- résidu multi-interface `L_res(I)`,
- invariants `ρ_σ`,
- gains marginaux `Δ`,
- sélection greedy exacte de vues (requêtes).

Objectif : fournir une capacité **universelle** (au sens : pour toute instance finie encodable)
qui ne dépend pas d’un entraînement.

Le learning (quand présent) sert uniquement à :

- inférer une instance (`X`, `σ`, interfaces) depuis un monde brut,
- proposer des vues,
- mais la décision “algèbre” est calculée par ce noyau.

