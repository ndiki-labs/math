# Relecture et formalisation de la borne supérieure

## Dépendances de la preuve

Ce tableau recense les résultats utilisés dans la composition finale et les sections utiles des certificats qui établissent plusieurs résultats. L'index des annexes localise les textes d'origine et les calculs exacts. Certains vérificateurs d'origine rejouent aussi des calculs qui documentent des étapes antérieures de la recherche. [Index des annexes](certificates.json)

| Proposition requise | Annexes et sections de preuve |
| --- | --- |
| Chaque couleur a un nombre d'indépendance d'au plus 12 | D'`answer-4` à `answer-6`, puis les deux cas d'`answer-33` fondés sur les tailles des stables qui se recoupent. |
| Une couleur de 176 arêtes possède un bloc d'ordre au moins 25 avec le nombre d'arêtes requis | `answer-7`, pour le budget des blocs et la borne sur les arêtes extérieures. |
| Le bloc dense ne peut avoir un ordre compris entre 25 et 31 | `answer-19` §1, `answer-22` pour les retraits de sommets de degré minimal, `answer-24` pour l'ordre 30 et `answer-27` §1. Les réductions initiales utilisent les résultats d’`answer-8` à `answer-10` sur la circonférence, la maille impaire et l’exclusion de $K_6$ à ces ordres. Les arguments utilisent aussi les conditions sur les chemins dans les sous-graphes bipartis induits et les bornes d'`answer-12` à `answer-18`, d'`answer-25` et d'`answer-26`. |
| Un bloc restant d'ordre 32 ou 33 est sans $K_6$ et sans $K_{4,4}$ induit | `answer-10` et `answer-11`, le dernier calcul sur les noyaux d'`answer-33` et l'exclusion des noyaux prescrits dans `answer-35`. |
| Un contre-exemple minimal à la borne de densité a un ordre compris entre 23 et 33, un degré minimal d'au moins 8, la 3-connexité et une maille impaire de 3 ou 5 | `answer-47`, avec ses bornes par blocs, l'analyse des séparateurs et l'argument du plus court cycle impair. |
| La maille impaire 5 est impossible | `answer-48`, qui utilise les coupes des pentagones d'`answer-9` et les règles d'attache des heptagones d'`answer-8`. |
| La taille maximale d'une clique du graphe minimal est au plus 4, puis au plus 3 | `answer-49` et `answer-50`, qui reprennent les comptages de chemins pour les oreilles courtes ou les arguments de voisinage d'`answer-10`, `answer-47` et `answer-49`. |
| Le graphe minimal ne peut contenir de triangle | `answer-51`, avec les quatre cas d'oreilles courtes et le comptage final sur un plus court chemin. |
| $K_{32}$ admet un coloriage qui évite le cycle | [Preuve Lean du coloriage sur 32 sommets](lean/RamseyC9/LowerBound.lean). |

La commande `replay.py --integrity-only` contrôle l'ordre des dépendances explicitement déclarées dans les champs `prior_answers` des certificats archivés. La composition finale utilise la borne sur les noyaux maximaux d'`answer-35`. Son vérificateur `core-bounds.py` charge la description des noyaux d'`answer-17` et la borne bipartie d'`answer-25`. Il utilise les contraintes d'indépendance et les bornes initiales sur la taille des noyaux d'`answer-33`. Ces résultats précèdent `answer-35`. Les calculs ultérieurs sur les pentagones et les configurations restantes dans le même vérificateur étayent d'autres conclusions.

## Passage à l'ordre 23

`answer-47` donne un graphe non biparti d'ordre 23 avec $\delta(H)\ge8$. S'il était sans triangle, il satisferait les hypothèses du théorème 1.8 de Brandt, Faudree et Goddard puisqu'il est distinct de $C_5$ et que $8>23/3$. Le théorème fournit un cycle de chaque longueur de quatre à $\min\{23,2(23-\alpha(H))\}\ge22$, y compris neuf. Le dénombrement d'`answer-48`, qui couvre les ordres 24 à 33, complète ainsi le cas sans triangle. [Brandt, Faudree et Goddard, théorème 1.8](https://people.computing.clemson.edu/~goddard/papers/weakpanFinal.pdf)

## Résultats externes aux principales étapes

| Résultat | Hypothèses utilisées dans la preuve |
| --- | --- |
| Nikiforov et Schelp, théorème 2 | Dans les deux réductions sur les stables, les deux couleurs évitent $C_9$ sur le graphe complet considéré. On prend $n=9$ et $\beta=1/3$ pour l'ordre 15 ou $\beta=4/9$ pour l'ordre 14. Les deux valeurs vérifient $0<\beta\le\lfloor n/2\rfloor/n$. [Texte original](https://arxiv.org/pdf/math/0602627) |
| Wang et Chen et formule de Hansson | Les deux ensembles valent $\{C_9,C_{10}\}$. Le cycle le plus court a une longueur de neuf et le plus court cycle pair a une longueur de dix dans chaque ensemble. La formule donne donc $9+10/2-1=13$ et s'applique au coloriage complet à deux couleurs du stable de taille 13. [Wang et Chen](https://doi.org/10.1002/jgt.22564) · [Hansson, définition de $m$ et conjecture 1.11](https://arxiv.org/pdf/1605.04301) |
| Nikiforov et Schelp, lemme 14 | Sur les dix sommets du $C_{10}$ monochromatique, le graphe de sa couleur est hamiltonien. Ce graphe et son complémentaire évitent $C_9$. On applique le lemme avec $n=5$. [Texte original, §4.1](https://arxiv.org/pdf/math/0602627#page=14) |
| Kopylov et raffinement de stabilité | On applique la borne à un bloc 2-connexe de circonférence strictement inférieure à neuf. Le théorème de Kopylov s'applique aux ordres du bloc au moins égaux à neuf. Le théorème 2.1 s'applique avec $t=4$, $k=9$ et un ordre du bloc d'au moins $3t=12$. [Article sur la stabilité](https://arxiv.org/pdf/1704.02866) |
| Brandt, puis Brandt, Faudree et Goddard | Pour la borne en arêtes, le graphe est non biparti et vérifie $e>\lfloor(n-1)^2/4\rfloor+1$. Le théorème 1.7 s'applique aux graphes non bipartis de degré minimal $\delta\ge(n+2)/3$ et donne une maille d'au plus quatre sans condition de connexité. Dans chaque application, on établit séparément la circonférence nécessaire pour en déduire un $C_9$. [Brandt](https://doi.org/10.1016/S0166-218X(97)00032-2) · [Théorème 1.7](https://people.computing.clemson.edu/~goddard/papers/weakpanFinal.pdf) |
| Lin, Wang et Zhou, théorème 1.2 | Pour $k=8$, le graphe minimal est 3-connexe, non biparti et vérifie $\delta\ge8$. Son ordre et l'interdiction de $K_6$ écartent la seule exception énoncée, $K_{k+1}=K_9$. Article publié dans le *Journal of Graph Theory*, volume 110 (2025), p. 431–436. [Énoncé dans la version 2](https://arxiv.org/html/2410.00648v2) · [Article publié](https://doi.org/10.1002/jgt.23281) |

## Corrections relevées lors de la préparation du manuscrit

1. **Voisinage à distance deux dans `answer-51`.** Le texte indique « au moins huit » sommets autour d'un sommet $x$ fortement attaché et du voisin $y$ choisi. Puisque $y$ a au plus deux attaches au noyau, il a au moins six voisins extérieurs, dont $x$. Son voisinage fermé compte donc au moins **sept** sommets et se trouve à distance au plus deux de $x$. Quatre tels voisinages disjoints nécessiteraient au moins 28 sommets, au-delà du maximum de 25. Le comptage plus fin qui suit utilise déjà $7-j$ autres voisins pour un sommet à $j$ attaches. Le vérificateur utilise cette expression et vérifie les contraintes de distance. La borne de trois sommets fortement attachés s'applique avec le comptage corrigé.
2. **Paramètre de Kopylov dans `answer-47`.** Avec la convention $h(s,k,a)=\binom{k-a}{2}+a(s-k+a)$, on obtient $h(s,9,4)=4s-10$. Le texte archivé utilise le majorant plus faible, valide, $4s-5$. Dans le cas de stabilité, il y a $s-5$ sommets hors de la clique distinguée. Au plus trois peuvent garder leurs quatre voisins communs. Soustraire $s-8$ au nombre exact donne $3s-2$, qui implique aussi la borne archivée $3s+3$. Les deux majorants utilisés pour le cas de base se déduisent de ces calculs. [Définition et théorèmes de Füredi et coll.](https://arxiv.org/pdf/1704.02866)

L'archive conserve les octets d'origine. Ces corrections accompagnent la lecture des annexes archivées.

## Seconde implémentation du calcul pour $K_5$

Le vérificateur de relecture construit les 1 094 noyaux à partir du multiensemble d'attaches à la clique. Il calcule les chemins simples par parcours en profondeur, reconstruit les profils admissibles et contrôle la dernière borne de coupe. Il retrouve la répartition $815+278+1$ et les onze comparaisons de coupe pour le noyau restant. Il applique les règles mathématiques de l'annexe écrite de manière autonome. La preuve comporte aussi l'argument d'existence de l'oreille et la déduction de la borne d'arêtes à partir des contraintes sur les profils. [Vérificateur de relecture](review/k5_check.py) · [Décomptes reproduits](review/k5-result.json)

## Périmètre de la formalisation

Lean vérifie `RamseyC9.no_ramsey_through_32` et ramène `RamseyC9.IsRamseyNumber 33` à `RamseyC9.HasRamseyProperty 33`. Il vérifie aussi les calculs des seuils de coupe et du nombre de voisinages disjoints. L'énoncé public en Lean décrit un cycle de longueur neuf par une application injective sur les sommets et neuf contraintes sur les arêtes consécutives, y compris celle qui ferme le cycle. Le module sur les graphes de couleur relie cette définition à un cycle dans un graphe simple et établit l'existence d'une couleur à au moins 176 arêtes.

Lean vérifie le plafond de 175 arêtes pour des blocs d'ordre au plus 24, sous les contraintes de taille et de nombre d'arêtes par bloc, et les neuf seuils des blocs d'ordre supérieur. Étant données la décomposition en blocs et la borne extrémale, il construit un bloc induit dense. Lean vérifie aussi la réduction à un sous-graphe induit minimal dans la classe héréditaire et les lemmes de chemins qui ferment un cycle de longueur neuf. [Budget des blocs](lean/RamseyC9/BlockBudget.lean) · [Réduction aux sous-graphes induits](lean/RamseyC9/DensityReduction.lean) · [Lemmes de chemins](lean/RamseyC9/Paths.lean)

Le théorème de composition prend cinq hypothèses explicites qui restent à démontrer dans Lean.

1. La borne d'indépendance de 12 par couleur dans un coloriage qui évite tout cycle monochromatique de longueur neuf.
2. L'existence de la décomposition en blocs requise.
3. La borne extrémale sur le nombre d'arêtes des graphes sans cycle de longueur neuf.
4. La réduction du bloc dense aux ordres 32 et 33 et à la classe héréditaire.
5. L'exclusion d'un graphe dense minimal dans cette classe.

[Théorème de composition](lean/RamseyC9/UpperBound.lean)

Pour le cas $K_5$, Lean certifie le recensement des 1 094 encodages et l'inclusion de tout encodage admissible après tri. Il reste à relier chaque graphe candidat à un encodage et à démontrer que les exclusions du vérificateur impliquent la borne voulue sur le graphe. La relecture mathématique indépendante de l'ensemble de l'argument de la borne supérieure reste à faire. [Recensement](lean/RamseyC9/K5EarKernels.lean)
