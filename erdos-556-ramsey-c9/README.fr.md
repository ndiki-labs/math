# Ramsey $C_9$ · dossier scientifique autonome

**État au 27 novembre 2026.** Manuscrit de travail pour relecture mathématique. La borne inférieure $R_3(C_9)\ge33$ est vérifiée dans Lean 4. La borne supérieure est présentée par composition de lemmes et de calculs exacts. Sa vérification intégrale dans Lean et sa relecture mathématique indépendante restent ouvertes.

**Auteur — Christian Hissibini.** Le dossier comprend une fiche destinée à la vitrine de la plateforme Episteme.

[Lire le dossier en anglais](README.en.md)

- [Manuscrit](MANUSCRIT.md)
- [Fiche de la vitrine Episteme](FICHE-PORTFOLIO.md)
- [Chaîne de preuve, corrections et obligations Lean](AUDIT.fr.md)
- [Projet Lean 4](lean/RamseyC9.lean)
- [Archive des certificats](certificates.tar.xz) et [index des empreintes](certificates.json)

L'archive autonome sélectionne 28 ensembles de pièces du gel d'Episteme du 27 novembre 2026. Chaque ensemble contient le texte de preuve, le JSON de référence et le ZIP des sources du vérificateur. L’archive jointe porte l’empreinte SHA-256 `85d5284adccfbce053a51769a20055e32f88e747e13880a8214dcfcbd23b0a8c`. [Télécharger l’archive jointe](certificates.tar.xz) Les 84 fichiers conservent leur contenu, leur langue et leur empreinte d'origine. Le dossier général Erdős #556 garde les 51 acquis et leurs jalons. Son archive complète, `erdos-556-c9-answer-51.tar.xz`, porte l'empreinte SHA-256 `9813b89832b7ef08d201c63b63d157c578caf4531594f466e09941843b3de00a`. [Provenance de l'archive](certificates.json)

## Provenance des outils

Episteme, développé par NDIKI Labs, a coordonné l'exploration de la preuve, consigné les vérifications exactes dans les jalons et archivé les certificats. La version utilisée pour cette recherche portait le nom de code `PHARE`. Les modèles de langage externes n'avaient aucune autorité épistémique dans la preuve.

- OpenAI Codex, modèle `gpt-6.2-sol` les 26 et 27 novembre 2026, a servi d'interface en langage naturel entre l'auteur et Episteme. Il a relayé les consignes de l'auteur et aidé à rédiger les résumés. L'auteur l'a également utilisé pour lire les résultats et suivre l'avancement des tâches. L'identifiant du modèle a été confirmé dans le journal local de la session Codex.
- Google Gemini, avec le modèle Gemini 4 Neon, a fourni une partie des retours externes informels sur les pistes et résultats intermédiaires.
- Lean 4.34.1 a vérifié la borne inférieure et les déductions formalisées. Python 3.13.7 et Apple Clang 17 ont servi au rejeu des vérificateurs archivés.

## Vérifier le projet Lean

Depuis ce dossier, avec Elan et la version indiquée dans `lean/lean-toolchain`.

```sh
cd lean
lake build
```

Le noyau vérifie la construction de $K_{32}$ et ses restrictions, l'équivalence entre cycle monochromatique et cycle dans un graphe de couleur, le seuil de 176 arêtes et les inégalités arithmétiques des coupes. Le journal du build contient l'audit des axiomes de ces théorèmes. Le projet utilise la bibliothèque standard de Lean.

Pour la borne supérieure, Lean vérifie aussi le budget numérique des blocs, la réduction à un sous-graphe induit minimal, des lemmes de chemins qui ferment un cycle de longueur neuf et le recensement des 1 094 encodages du cas $K_5$. Le théorème de composition prend cinq obligations de preuve comme hypothèses explicites. [État de la formalisation et obligations restantes](AUDIT.fr.md#périmètre-de-la-formalisation)

## Lire et rejouer les preuves archivées

Le rejeu utilise Python 3.10 ou ultérieur et un compilateur C++20. Les 28 sorties ont été reproduites à l'octet près avec Python 3.13.7 et Apple Clang 17. Certaines étapes recompilent et recalculent leurs propres dépendances.

```sh
python3 -B replay.py --integrity-only
python3 -B replay.py --answers answer-47 answer-48 answer-49 answer-50 answer-51
python3 -B replay.py --all
```

Extraire les textes et les sources dans un répertoire de lecture séparé.

```sh
mkdir -p proof-appendices
LC_ALL=C tar -xJf certificates.tar.xz -C proof-appendices
```

Chaque entrée `proof` de `certificates.json` pointe vers son texte dans ce répertoire. Les notes de relecture donnent l'ordre de lecture et les corrections à appliquer aux textes d'origine. Le rejeu compare la sortie de chaque vérificateur au JSON de référence, à l'octet près. [Relecture de la borne supérieure](AUDIT.fr.md)

Le contrôle indépendant des 1 094 noyaux de la branche $K_5$ se lance avec `python3 -B review/k5_check.py`. [Sortie de référence](review/k5-result.json)

### Témoins archivés

- **Quatre attaches à un $K_{3,3}$ (`answer-44`).** Numéroter le pentagone $0,1,2,3,4$ dans l'ordre cyclique et nommer les deux parties du $K_{3,3}$ $\{a,b,c\}$ et $\{d,e,f\}$. Ajouter les quatre arêtes $a0,a2,b1,c1$. Ce graphe évite les triangles et les $C_9$. La vérification d'origine est documentée dans `bipartite-bicliques-c9/C9-BIPARTITE-BICLIQUES.md` dans l'archive complète identifiée plus haut.
- **Un cycle de longueur 30 après le retrait d'un triangle (`answer-8`).** La construction à 111 arêtes est décrite dans `odd-block-c9/C9-ODD-BLOCK.md` dans l'archive jointe. La commande `python3 -B replay.py --answers answer-8` rejoue la vérification exacte. [Archive des certificats](certificates.tar.xz)
