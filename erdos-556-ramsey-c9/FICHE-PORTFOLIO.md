# Le nombre de Ramsey à trois couleurs du cycle à neuf sommets

**Christian Hissibini** · *NDIKI Labs*

*Étude de cas Episteme pour relecture · 27 novembre 2026*

**À partir de combien de sommets un cycle monochromatique de longueur neuf devient-il inévitable lorsque chaque arête d'un graphe complet reçoit l'une de trois couleurs ?** Episteme a mené la recherche mathématique qui a abouti à une proposition de preuve de $R_3(C_9)=33$. Dans son panorama de 2026, Radziszowski répertorie le cycle de longueur neuf comme le plus petit cas impair ouvert de la conjecture de Bondy et Erdős (problème Erdős n° 556). Faudree, Schelten et Schiermeyer ont résolu le cas impair précédent, $R_3(C_7)=25$, en 2003. [Radziszowski, DS1.18, §6.3.1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/0#page=61) · [Faudree, Schelten et Schiermeyer, 2003](https://bibliotekanauki.pl/articles/743391.pdf)

Sur 32 sommets, quatre groupes de huit donnent un coloriage qui évite le cycle. Une couleur reste confinée à ces groupes. Les deux autres sont biparties et ne produisent que des cycles pairs. Lean 4 vérifie cette construction et ses restrictions aux graphes complets plus petits.

Sur 33 sommets, l'argument part de la couleur la plus fréquente, qui possède au moins 176 arêtes. Dans un éventuel contre-exemple, le nombre d'indépendance de chaque graphe de couleur est d'au plus 12. La réduction par densité conduit à un graphe induit dense d'ordre minimal, 3-connexe et de degré minimal au moins huit. Les chemins passant par les triangles et les petites cliques contraignent les cas restants, que la preuve écarte par des vérifications finies exactes.

**État scientifique.** Le manuscrit de travail présente l'argument et les annexes permettent de rejouer les calculs exacts. La relecture mathématique indépendante de la borne supérieure et sa formalisation intégrale dans Lean 4 restent à terminer.

**Le contrat épistémique d'Episteme en pratique.** Le premier examen des méthodes d'Episteme-Math (Episteme Mathematics) a laissé une obligation de preuve ouverte. Episteme-R (Episteme Reasoning) l'a consignée explicitement. Dans Episteme Research, Episteme a exploré les pistes de preuve, développé les réductions et vérifié les cas finis. Le dossier cumulatif conserve 51 résultats et leur statut de vérification dans 48 jalons. Chaque jalon identifie le résultat cumulatif par son empreinte SHA-256 et le relie à ses pièces justificatives. [Manuscrit](MANUSCRIT.md)

Les contrôles exacts ont permis d'écarter des raccourcis invalides. Une construction de 111 arêtes a montré qu'un cycle de longueur 30 peut subsister après le retrait d'un triangle sous les conditions locales étudiées. L'auteur a dirigé la recherche par une interface en langage naturel. Des retours externes ont contribué à l'examen des étapes intermédiaires. Les 28 sorties de vérificateurs du dossier autonome ont été reproduites à l'octet près à partir des sources archivées, indépendamment d'Episteme. [Dossier de preuve et provenance des outils](README.fr.md)
