Un invariant global classique vise une quantité ou une structure conservée par la dynamique (énergie, mesure, conjugaison, rang, etc.), sans référence explicite à des interfaces d’observation.

L’invariant relatif de clôture prédictive porte sur la dynamique vue à travers deux marginales et leur raffinement joint. Il encode la configuration de trois partitions sur une même fibre : la partition induite par la première marginale, celle induite par la seconde, et la partition dynamique minimale qui identifie exactement les états au profil futur indistinguable.

Il mesure une position relative : comment les partitions observationnelles se placent par rapport à la partition exigée par la dynamique, donc le degré d’accessibilité de la structure dynamique depuis les interfaces disponibles.

L’irréductibilité marginale signifie que chaque marginale identifie au moins une paire d’états que la dynamique doit distinguer, ce qui caractérise une obstruction structurelle à la clôture prédictive.

Ajout : cet invariant sert aussi de principe de construction. Une fois une marginale reconnue irréductiblement insuffisante, la configuration prescrit une extension d’interface ou une médiation jointe qui restitue les distinctions dynamiques perdues, jusqu’à obtenir une clôture prédictive sur l’interface enrichie.

## Classe d’invariants relatifs de clôture prédictive

### Données

- Un ensemble (ou type) d’états présents `X`.
- Deux interfaces marginales :
  - `p_A : X → Y_A`
  - `p_B : X → Y_B`
    et leurs partitions induites :
  - `E_A := Ker(p_A)`
  - `E_B := Ker(p_B)`.
- Une notion de **signature future** (ou de profil dynamique) :
  - `Sig : X → S`
    et la partition dynamique minimale associée :
  - `E_Sig := {(x,x') | Sig(x)=Sig(x')}`.

### Objet invariant

L’invariant relatif est la **configuration de partitions** :

- `I_AB(h) := [X ; E_A, E_B, E_Sig]`

prise à isomorphisme près (bijections `X ≃ X'` transportant simultanément `E_A,E_B,E_Sig`).

Équivalent : le diagramme intrinsèque

- `X → X/E_A × X/E_B × X/E_Sig`.

### Invariants dérivés (structure)

- **Dimension dynamique** : `|X/E_Sig| = |im(Sig)|`.
- **Accessibilité marginale** (clôture depuis une marginale) :
  - `E_A ⊆ E_Sig` (la marginale A est suffisante pour la signature)
  - `E_B ⊆ E_Sig`.
- **Irréductibilité marginale** :
  - `E_A ⊄ E_Sig` et `E_B ⊄ E_Sig`
    (chaque marginale écrase au moins une distinction dynamiquement nécessaire).

## Exemple fini (non trivial, court) : XOR comme signature future

On prend :

- `X = {00, 01, 10, 11}` (bits)
- `p_A(x)` = premier bit
- `p_B(x)` = second bit
- `Sig(x) := xor(x)` (signature future jouet)

### Partitions induites

- `E_A := Ker(p_A)` partitionne `X` en :
  - fibre `p_A = 0` : `{00, 01}`
  - fibre `p_A = 1` : `{10, 11}`

- `E_B := Ker(p_B)` partitionne `X` en :
  - fibre `p_B = 0` : `{00, 10}`
  - fibre `p_B = 1` : `{01, 11}`

- `E_Sig := {(x,x') | Sig(x)=Sig(x')}` partitionne `X` en :
  - classe `Sig = 0` : `{00, 11}`
  - classe `Sig = 1` : `{01, 10}`

### Irréductibilité marginale (témoins explicites)

Chaque marginale identifie une paire que `E_Sig` sépare :

- `00 ~_{E_A} 01` (même `p_A`), tandis que `Sig(00)=0` et `Sig(01)=1`.
- `00 ~_{E_B} 10` (même `p_B`), tandis que `Sig(00)=0` et `Sig(10)=1`.

Ces deux paires rendent concret le fait que les partitions observationnelles (A et B) sont plus grossières
que la partition dynamique minimale `E_Sig`.

### Lisibilité au joint

Le joint `(p_A, p_B)` est injectif sur `X`, donc `Ker(p_A × p_B)` est l’égalité.
Dans ce jouet, la signature devient lisible au joint :

`Sig(x) = xor(p_A(x), p_B(x))`.

Ce petit exemple fait apparaître :

- l’insuffisance structurée de chaque marginale,
- la clôture prédictive rendue disponible par le joint,
- et l’objet invariant `I_AB = [X; E_A, E_B, E_Sig]` comme position relative de partitions.

### Définition de la classe

La **classe des invariants relatifs de clôture prédictive** est l’ensemble de tous les objets `I_AB = [X;E_A,E_B,E_Sig]` construits de cette manière, pour des choix variés de :

- `X`,
- interfaces marginales `(p_A,p_B)`,
- et notions de signature future `Sig`.

Cette classe ne décrit pas seulement la dynamique “en soi”, elle décrit aussi la position de la partition dynamiquement suffisante relativement aux interfaces disponibles, donc le régime de clôture prédictive accessible.
