# Le nombre de Ramsey à trois couleurs du cycle de longueur neuf

**Christian Hissibini**\
*NDIKI Labs*

*Manuscrit de travail pour relecture mathématique · 27 novembre 2026*\
[Dossier autonome en français](https://github.com/ndiki-labs/math/blob/main/erdos-556-ramsey-c9/README.fr.md)

Nous présentons un argument assisté par ordinateur pour établir $R(C_9,C_9,C_9)=33$. Episteme a mené l'essentiel de l'exploration de la preuve avec son moteur de raisonnement, Episteme-R. La borne inférieure repose sur un coloriage en quatre blocs, vérifié dans Lean 4. Pour la borne supérieure, nous majorons le nombre d'indépendance des graphes de couleur, ramenons le problème à un graphe induit dense d'ordre minimal et vérifions les attaches possibles autour de cycles courts et de cliques. Le dossier contient les annexes de preuve et le code source des vérificateurs. La formalisation de la borne supérieure dans Lean reste partielle.

## 1. Énoncé et borne inférieure

On note $R_3(C_9)$ le plus petit entier $N$ tel que tout coloriage à trois couleurs des arêtes de $K_N$ contienne un cycle monochromatique sur neuf sommets distincts. Un tel cycle peut avoir des cordes.

Le cas $n=9$ relève de la conjecture de Bondy et Erdős, répertoriée comme problème d'Erdős no 556. Elle prévoit que $R_3(C_n)\le4n-3$ pour tout $n\ge4$. Leur article de 1973 sur les nombres de Ramsey des cycles à deux couleurs donne $R(C_9,C_9)=17$, que l'on utilise dans la réduction sur les ensembles stables. Faudree, Schelten et Schiermeyer ont prouvé $R_3(C_7)=25$ en 2003. L'édition 2026 du panorama de Radziszowski répertorie $C_9$ comme le premier cas impair ouvert. Bosse et Song ont établi le seuil de 33 pour les coloriages de Gallai, qui excluent les triangles arc-en-ciel. [Problème d'Erdős no 556](https://www.erdosproblems.com/556) · [Bondy et Erdős, 1973](https://doi.org/10.1016/S0095-8956(73)80005-X) · [Faudree, Schelten et Schiermeyer, 2003](https://doi.org/10.7151/DMGT.1191) · [Radziszowski, DS1.18, §6.3.1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/0) · [Bosse et Song](https://arxiv.org/abs/1802.06503)

On répartit les 32 sommets en quatre blocs de huit. Les blocs 1 et 2 forment une moitié, les blocs 3 et 4 l'autre. On utilise la première couleur à l'intérieur de chaque bloc, la deuxième entre les deux blocs de chaque moitié et la troisième entre les deux moitiés. Les cycles de la première couleur restent dans un seul bloc. Chacune des deux autres couleurs forme un graphe biparti. Ce coloriage évite donc tout $C_9$ monochromatique et donne $R_3(C_9)\ge33$. Sa restriction à un ensemble de sommets plus petit fournit la construction correspondante à cet ordre. [Preuve Lean de la borne inférieure](lean/RamseyC9/LowerBound.lean)

## 2. Réduction à un bloc dense

Supposons qu'un coloriage à trois couleurs de $K_{33}$ évite tout $C_9$ monochromatique. Chaque graphe de couleur a un nombre d'indépendance d'au plus 12. La preuve s'appuie sur les résultats de stabilité à deux couleurs de Nikiforov et Schelp et sur le théorème de Ramsey pour des ensembles de cycles de Wang et Chen. Elle exclut d'abord les stables de tailles 16 et 15, puis ceux de taille 14. Elle ramène ensuite un stable de taille 13 à deux cliques bleues séparées par une coupe verte, avec des exceptions bleues en étoile de formes prescrites. La dernière étape utilise deux stables de couleurs différentes qui se recoupent. Dans l'application du théorème de Hall, une clique de sept sommets fournit quatre sommets distincts, chacun voisin commun de deux sommets consécutifs dans une suite de cinq sommets extérieurs. Une arête entre les deux extrémités ferme alors un cycle de longueur neuf. Les arguments structurels complets figurent dans les annexes `answer-4`, `answer-5`, `answer-6` et `answer-33`. [Nikiforov et Schelp, théorème 2 et lemme 14](https://arxiv.org/abs/math/0602627) · [Wang et Chen](https://doi.org/10.1002/jgt.22564) · [Index des annexes](certificates.json)

Au moins un graphe de couleur $G$ contient $\binom{33}{2}/3=176$ arêtes ou davantage. Posons $f(t)=\operatorname{ex}(t,C_9)$ et soit $B$ un plus grand bloc de $G$, en comptant les ponts comme des blocs. Les ensembles d'arêtes des blocs sont disjoints et leurs ordres vérifient $\sum_D(|D|-1)\le32$. La récurrence suivante majore le nombre total d'arêtes lorsque chaque bloc a un ordre d'au plus $j$.

$$
F_j(0)=0,\qquad F_j(t)=\max\left(F_j(t-1),\max_{1\le s\le\min(t,j-1)}\{F_j(t-s)+f(s+1)\}\right)
$$

Les valeurs exactes de $f$ donnent $F_{24}(32)=175$ et imposent $b=|B|\ge25$. Deux blocs de cet ordre dépasseraient le budget de 32. Dans une union disjointe des blocs extérieurs, on peut identifier un sommet de chaque bloc en un sommet commun. Cette opération conserve le nombre d'arêtes extérieures et ne crée aucun $C_9$. On en déduit $e(B)\ge176-f(34-b)$. [Seuil d'arêtes par couleur en Lean](lean/RamseyC9/ColourGraphs.lean) · [Füredi et Gunderson, théorème 1](https://arxiv.org/abs/1310.6766) · [Annexe `answer-7`](certificates.json)

| $b$ | 25 | 26 | 27 | 28 | 29 | 30 | 31 | 32 | 33 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Minimum pour $e(B)$ | 147 | 148 | 155 | 161 | 166 | 170 | 173 | 175 | 176 |

Puisque $b\ge25$ et $\alpha(B)\le12$, le bloc est non biparti. L'argument d'`answer-7` majore sa maille impaire par sept. Les exclusions des mailles impaires sept et cinq dans `answer-8` et `answer-9` imposent alors un triangle. L'analyse des attaches aux cliques dans `answer-10` exclut $K_6$ pour $25\le b\le31$. Aux ordres 32 et 33, elle montre que tout $K_6$ doit avoir une oreille de longueur trois. [Index des annexes](certificates.json)

À l'ordre 25, `answer-19` combine le seuil d'arêtes de Brandt avec la borne de circonférence d'`answer-8` pour imposer un $C_9$. Pour les ordres 26 à 31, les arguments d'`answer-22`, `answer-24` et `answer-27` et leurs dépendances procèdent par retraits successifs d'un sommet de degré minimal. À chaque retrait, on exclut un premier reste biparti ou on contrôle ses attaches dans le bloc d'origine. [Brandt](https://doi.org/10.1016/S0166-218X(97)00032-2) · [Index des annexes](certificates.json)

Aux ordres 32 et 33, `answer-11` utilise l'oreille imposée par `answer-10` pour exclure $K_6$. Les majorations d'`answer-33` et `answer-35` excluent les sous-graphes bipartis induits qui fournissent des chemins de longueurs $2,4,6$ entre deux sommets distincts d'une même partie et de longueurs $3,5,7$ entre des sommets de parties opposées. Un $K_{4,4}$ induit a cette propriété, ce qui l'exclut aussi. [Index des annexes](certificates.json)

## 3. Un graphe induit dense d'ordre minimal

Considérons la classe héréditaire des graphes sans $C_9$, sans $K_6$, sans $K_{4,4}$ induit et de nombre d'indépendance au plus 12. Posons $T(16)=57$ et $T(n)=7n-56$ pour $17\le n\le33$. Le bloc $B$ appartient à cette classe et dépasse $T(b)$ d'après le tableau précédent. Soit $H$ un graphe de cette classe d'ordre minimal $n\in[16,33]$ avec $e(H)>T(n)$.

Dans un graphe biparti de parties $X,Y$ de tailles $p,q\le12$, le comptage des ensembles de quatre sommets dans les voisinages donne $\sum_{x\in X}\binom{d(x)}4\le3\binom q4$, ainsi que l'inégalité obtenue en échangeant les parties. La convexité discrète fournit les majorants d'arêtes jusqu'à l'ordre 24. À un ordre supérieur, un graphe biparti dépasserait le nombre d'indépendance autorisé. À l'ordre 16, on distingue selon l'existence d'un cycle de longueur au moins neuf. S'il existe un tel cycle, la borne de Brandt s'applique au cas non biparti. Pour une circonférence d'au plus huit, le théorème de Kopylov et son raffinement de stabilité majorent les contributions des blocs. On obtient le cas de base. [Brandt](https://doi.org/10.1016/S0166-218X(97)00032-2) · [Füredi, Kostochka, Luo et Verstraëte, théorème 2.1 et énoncé du théorème de Kopylov](https://arxiv.org/abs/1704.02866)

Retirer un sommet de degré au plus $T(n)-T(n-1)$ donnerait un contre-exemple d'ordre plus petit. La borne sur le degré ainsi obtenue et la faible pancyclicité excluent les ordres 17 à 22. L'argument de séparation d'`answer-47` donne ensuite $23\le n\le33$, $\delta(H)\ge8$ et la 3-connexité. Le théorème sur les longueurs consécutives de cycles donne huit longueurs consécutives, toutes au moins égales à dix puisque $C_9$ est exclu. Le comptage des voisins extérieurs d'un plus court cycle impair ramène sa longueur à trois ou cinq. Si $n=23$ et que $H$ est sans triangle, alors $H$ est non biparti et $\delta(H)\ge8>23/3$. Le théorème 1.8 de Brandt, Faudree et Goddard donne un cycle de chaque longueur de quatre à $\min\{23,2(23-\alpha(H))\}\ge22$. Cela impose un $C_9$. Aux ordres 24 à 33, l'argument d'`answer-48` exclut la maille impaire cinq. Ainsi, $H$ contient un triangle. [Brandt, Faudree et Goddard, théorèmes 1.7 et 1.8](https://people.computing.clemson.edu/~goddard/papers/weakpanFinal.pdf) · [Lin, Wang et Zhou, JGT 110 (2025), théorème 1.2](https://doi.org/10.1002/jgt.23281) · [Index des annexes](certificates.json)

Pour $1\le |S|\le n-17$, on soustrait le majorant du nombre d'arêtes de $H-S$.

$$
e(H[S])+e(S,H-S)\ge 7|S|+1.
$$

La borne inférieure vaut $7|S|$ lorsque $|H-S|=16$. Les coupes des cliques de tailles 3, 4 et 5 comptent donc respectivement au moins 19, 23 et 26 arêtes. Tout ensemble de huit sommets est incident à au moins 49 arêtes à l'ordre 23, 56 à l'ordre 24 et 57 aux ordres suivants. Ces seuils servent dans les derniers cas. [Déductions arithmétiques vérifiées dans Lean](lean/RamseyC9/CutBounds.lean)

## 4. Cas des cliques et vérification finie

Une oreille d'une clique est un chemin simple dont les deux extrémités sont des sommets distincts de la clique et dont l'intérieur est à l'extérieur. Un chemin dans la clique peut fermer une oreille de longueur complémentaire en un $C_9$. On étudie les oreilles courtes par des vérifications finies sur des noyaux de huit sommets contenant la clique et l'oreille. Les voisinages extérieurs possibles sont représentés par des sous-ensembles de ces huit sommets. Un voisinage extérieur admissible ne peut contenir deux sommets reliés par un chemin de longueur sept à l'intérieur du noyau. Plus généralement, un chemin extérieur de longueur $d$ entre deux sommets extérieurs interdit un chemin de longueur $7-d$ dans le noyau entre leurs attaches respectives. Lorsque des voisinages doivent être disjoints, le degré minimal impose un minimum de sommets extérieurs.

| Taille maximale d'une clique | Argument et annexe de vérification |
| --- | --- |
| 5 | Un $K_5$ impose une oreille de longueur quatre. Sur 1 094 noyaux candidats de huit sommets, 815 sont exclus par la borne d'attaches et 278 par la taille des voisinages. Un comptage d'arêtes de coupe exclut le dernier cas. `answer-49` |
| 4 | Un $K_4$ impose une oreille de longueur quatre ou cinq. Le vérificateur examine 15 191 noyaux pour la longueur cinq et 2 716 pour la longueur quatre après exclusion de la longueur cinq. `answer-50` |
| 3 | La coupe entre un triangle et le reste compte au moins 19 arêtes et le retrait du triangle laisse un degré minimal d'au moins six. Le dénombrement initial donne 43 590, 3 999, 1 021 et 54 noyaux lorsque la plus longue oreille courte a respectivement une longueur de six, cinq, quatre ou trois. Un comptage des sommets sans marque termine le cas de longueur trois et le cas sans oreille courte. `answer-51` |

Dans le cas du triangle, les ensembles de sommets autour des sommets extérieurs qui ont au moins trois attaches sont deux à deux disjoints lorsque ces sommets sont à une distance d'au moins cinq. Pour chacun, on choisit un voisin $y$ à l'extérieur du noyau. L'ensemble formé de $y$ et de tous ses voisins extérieurs compte au moins sept sommets, puisque $y$ a au plus deux attaches au noyau de huit sommets. L'extérieur compte au plus 25 sommets, ce qui permet au plus trois de ces ensembles disjoints. L'annexe finale donne le comptage pour chaque type d'attache. [Notes de relecture des textes archivés](AUDIT.fr.md) · [Index des annexes](certificates.json)

L'analyse des cas exclut le graphe minimal $H$. Le coloriage supposé de $K_{33}$ est donc impossible. La borne supérieure qui en découle et la construction sur $K_{32}$ donnent l'égalité proposée pour les coloriages à trois couleurs sans restriction.

## Reproductibilité et relecture

Les vérifications finies se reproduisent indépendamment d'Episteme à partir des annexes, du code source des vérificateurs et des sorties de référence. L'index des annexes indique la provenance et l'empreinte SHA-256 de chaque pièce. La relecture mathématique doit aussi établir que les calculs couvrent tous les cas de chaque lemme. [Dossier et instructions de rejeu](README.fr.md)

Lean vérifie la borne inférieure et plusieurs étapes de la preuve de la borne supérieure, dont le budget numérique des blocs, la réduction à un sous-graphe induit dense minimal et les lemmes de chemins. Il vérifie aussi le recensement des 1 094 encodages du cas $K_5$. Le théorème de composition `RamseyC9.isRamseyNumber33_of_reductions` prend cinq hypothèses explicites qui restent à démontrer dans Lean. La preuve de `RamseyC9.HasRamseyProperty 33` achèvera la formalisation. [UpperBound.lean](lean/RamseyC9/UpperBound.lean#L9) · [Obligations de preuve](AUDIT.fr.md#périmètre-de-la-formalisation)

## Le rôle d'Episteme dans la recherche

Episteme a mené l'exploration structurée de la preuve sous la direction de l'auteur. Episteme-R (Episteme Reasoning), son moteur de raisonnement, a coordonné ce travail. La démarche illustre le contrat épistémique d'Episteme. Après le premier examen des méthodes d'Episteme-Math (Episteme Mathematics), Episteme-R a consigné l'obligation de preuve comme ouverte. Dans Episteme Research, Episteme a établi les bornes sur les stables, élaboré la réduction héréditaire par densité et traité les cas finis de cliques. Le dossier documente les déductions mathématiques et fournit des vérifications exactes reproductibles pour les calculs finis.

Le dossier cumulatif conserve 51 résultats et leur statut de vérification dans 48 jalons. Chaque jalon identifie le résultat cumulatif par son empreinte SHA-256 et le relie à ses pièces justificatives. Les 28 sorties de vérificateurs retenues dans le dossier autonome ont été reproduites à l'octet près. [Dossier de recherche et instructions de rejeu](README.fr.md)

Tout au long de la recherche, les contrôles exacts d'Episteme ont servi de garde-fou mathématique. Ils ont écarté des raccourcis invalides et trouvé des témoins qui ont mis à l'épreuve les bornes proposées au fil de la preuve. Un témoin rattache un pentagone à un $K_{3,3}$ par quatre arêtes, avec les ensembles d'attaches $\{0,2\},\{1\},\{1\}$ sur une même partie. Le graphe obtenu évite $C_3$ et $C_9$ et réfute la borne proposée de trois arêtes sous ces conditions locales. Dans `answer-8`, un autre témoin de 111 arêtes conserve un cycle de longueur 30 après retrait d'un triangle et réfute un majorant de circonférence. [Témoins archivés](README.fr.md#témoins-archivés)

Les modèles de langage externes n'avaient aucune autorité épistémique dans la preuve. OpenAI Codex a servi d'interface en langage naturel pour transmettre les consignes de l'auteur à Episteme et rédiger des résumés. Des retours de modèles de langage externes ont été consultés à titre informel sur les pistes intermédiaires. La justification mathématique repose sur les modules Lean 4, les annexes de preuve et les théorèmes qu'elles citent, ainsi que sur les vérificateurs déterministes archivés. [Provenance des outils](README.fr.md#provenance-des-outils)

Lean 4 vérifie la borne inférieure et les déductions formalisées décrites plus haut. Les calculs finis archivés ont été rejoués avec Python et un compilateur C++. [Instructions de vérification](README.fr.md)
