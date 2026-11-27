# The Three-Colour Ramsey Number of the 9-Cycle

**Christian Hissibini**\
*NDIKI Labs*

*Working manuscript for mathematical review · 27 November 2026*\
[Standalone dossier](https://github.com/ndiki-labs/math/tree/main/erdos-556-ramsey-c9)

We present a computer-assisted argument for $R(C_9,C_9,C_9)=33$. Episteme carried out the main proof exploration, guided by its reasoning engine, Episteme-R. The lower bound is given by a four-block colouring and is verified in Lean 4. The upper-bound argument uses an independence bound for the colour graphs, a reduction to a minimal dense induced graph, and finite checks of the possible attachments to short cycles and cliques. The research dossier contains the proof appendices and the source code for those checks. The Lean formalization of the upper bound remains partial.

## 1. Statement and lower bound

Write $R_3(C_9)$ for the least $N$ such that every colouring of the edges of $K_N$ with three colours contains a monochromatic cycle on nine distinct vertices. Copies of a cycle may have chords.

The case $n=9$ belongs to the conjecture of Bondy and Erdős that $R_3(C_n)\le4n-3$ for every $n\ge4$, recorded as Erdős Problem 556. Their 1973 work on two-colour cycle Ramsey numbers gives $R(C_9,C_9)=17$, which is used in the stable-set reduction. Faudree, Schelten and Schiermeyer proved $R_3(C_7)=25$ in 2003. The 2026 revision of Radziszowski's survey lists $C_9$ as the first open odd case. Bosse and Song established the threshold of 33 for Gallai colourings, which exclude rainbow triangles. [Erdős Problem 556](https://www.erdosproblems.com/556) · [Bondy and Erdős, 1973](https://doi.org/10.1016/S0095-8956(73)80005-X) · [Faudree, Schelten and Schiermeyer, 2003](https://doi.org/10.7151/DMGT.1191) · [Radziszowski, DS1.18, §6.3.1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/0) · [Bosse and Song](https://arxiv.org/abs/1802.06503)

Partition the 32 vertices into four blocks of size eight, with blocks 1 and 2 in one half and blocks 3 and 4 in the other. Use the first colour within each block, the second between the two blocks of either half, and the third between the halves. A cycle in the first colour stays within a single block, while each of the other colours is bipartite. Thus this colouring avoids monochromatic $C_9$, proving $R_3(C_9)\ge33$. Restricting it to any smaller vertex set gives the corresponding counterexample there. [Lean proof of the lower bound](lean/RamseyC9/LowerBound.lean)

## 2. Reduction to a dense block

Suppose a three-colouring of $K_{33}$ avoids monochromatic $C_9$. Each colour graph has independence number at most 12. The proof uses the two-colour stability results of Nikiforov and Schelp and the cycle-set Ramsey theorem of Wang and Chen. It first rules out independent sets of sizes 16 and 15, then rules out size 14. It reduces a 13-set to two blue cliques with a green cross-cut, allowing prescribed blue stars. The closure uses two overlapping independent sets of different colours. In its Hall step, a clique of seven vertices supplies four distinct common neighbours along a path of five exterior vertices, giving a 9-cycle when the two ends of the path are joined. The full structural arguments are in appendices `answer-4`, `answer-5`, `answer-6` and `answer-33`. [Nikiforov and Schelp, Theorem 2 and Lemma 14](https://arxiv.org/abs/math/0602627) · [Wang and Chen](https://doi.org/10.1002/jgt.22564) · [Appendix index](certificates.json)

One colour graph $G$ has at least $\binom{33}{2}/3=176$ edges. Let $f(t)=\operatorname{ex}(t,C_9)$ and let $B$ be a largest block of $G$, counting bridges as blocks. Edge sets of blocks are disjoint and their orders satisfy $\sum_D(|D|-1)\le32$. The recurrence

$$
F_j(0)=0,\qquad F_j(t)=\max\left(F_j(t-1),\max_{1\le s\le\min(t,j-1)}\{F_j(t-s)+f(s+1)\}\right)
$$

bounds the edge sum if the individual block orders are at most $j$. With the exact values of $f$, the bound $F_{24}(32)=175$ forces $b=|B|\ge25$. There cannot be two blocks of order at least 25. Identifying one vertex from each exterior block in an otherwise disjoint union preserves the total exterior edge count and creates no $C_9$. This gives $e(B)\ge176-f(34-b)$, as recorded below. [Lean proof of the colour threshold](lean/RamseyC9/ColourGraphs.lean) · [Füredi and Gunderson, Theorem 1](https://arxiv.org/abs/1310.6766) · [Appendix `answer-7`](certificates.json)

| $b$ | 25 | 26 | 27 | 28 | 29 | 30 | 31 | 32 | 33 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Required $e(B)$ | 147 | 148 | 155 | 161 | 166 | 170 | 173 | 175 | 176 |

Since $b\ge25$ and $\alpha(B)\le12$, the block is nonbipartite. The argument in `answer-7` bounds its odd girth by seven. The exclusions of odd girths seven and five in `answer-8` and `answer-9` then force a triangle. The clique-attachment argument in `answer-10` rules out $K_6$ for $25\le b\le31$ and identifies a necessary three-edge ear for any $K_6$ at orders 32 and 33. [Appendix index](certificates.json)

At order 25, `answer-19` combines Brandt's edge threshold with the circumference bound from `answer-8` to force a $C_9$. Orders 26–31 are excluded by the minimum-degree deletion arguments in `answer-22`, `answer-24` and `answer-27` and their dependencies. At each deletion the argument either excludes a first bipartite remainder or controls its attachments in the original block. [Brandt](https://doi.org/10.1016/S0166-218X(97)00032-2) · [Appendix index](certificates.json)

At orders 32 and 33, `answer-11` uses the necessary ear from `answer-10` to exclude $K_6$. The core estimates in `answer-33` and `answer-35` exclude induced bipartite subgraphs that supply paths of lengths $2,4,6$ between distinct vertices in the same part and $3,5,7$ between vertices in opposite parts. An induced $K_{4,4}$ has this path property, so it too is excluded. [Appendix index](certificates.json)

## 3. A minimal dense induced graph

Consider the hereditary class of graphs without $C_9$, $K_6$ or an induced $K_{4,4}$ and with independence number at most 12. Put $T(16)=57$ and $T(n)=7n-56$ for $17\le n\le33$. The block $B$ belongs to this class and exceeds $T(b)$ by the preceding table. Choose a graph $H$ in the class of smallest order $n\in[16,33]$ satisfying $e(H)>T(n)$.

For a bipartite graph with parts $X,Y$ of sizes $p,q\le12$, counting four-subsets of neighbourhoods gives $\sum_{x\in X}\binom{d(x)}4\le3\binom q4$ and the corresponding inequality with the parts interchanged. Discrete convexity supplies the bipartite edge caps up to order 24. Larger bipartite graphs violate the independence cap. At order 16, the proof splits according to whether the graph has a cycle of length at least nine. If it does, Brandt's bound applies to the nonbipartite case. For circumference at most eight, Kopylov's theorem and its stability refinement bound the contributions of the blocks. This proves the base case. [Brandt](https://doi.org/10.1016/S0166-218X(97)00032-2) · [Füredi, Kostochka, Luo and Verstraëte, Theorem 2.1 and the statement of Kopylov's theorem](https://arxiv.org/abs/1704.02866)

Removing a vertex of degree at most $T(n)-T(n-1)$ would give a smaller counterexample. The resulting degree bound and weak pancyclicity rule out orders 17–22. The separator argument in `answer-47` then gives $23\le n\le33$, $\delta(H)\ge8$, and 3-connectivity. The consecutive-cycle theorem implies eight consecutive lengths, all at least ten, since a 9-cycle is forbidden. The shortest odd cycle has length three or five, by counting its external neighbours. If $n=23$ and $H$ is triangle-free, then $H$ is nonbipartite and $\delta(H)\ge8>23/3$. Theorem 1.8 of Brandt, Faudree and Goddard gives weak pancyclicity from length four through $\min\{23,2(23-\alpha(H))\}\ge22$. This forces a $C_9$. For orders 24–33 the pentagon argument in `answer-48` excludes odd girth five. Thus $H$ contains a triangle. [Brandt, Faudree and Goddard, Theorems 1.7–1.8](https://people.computing.clemson.edu/~goddard/papers/weakpanFinal.pdf) · [Lin, Wang and Zhou, JGT 110 (2025), Theorem 1.2](https://doi.org/10.1002/jgt.23281) · [Appendix index](certificates.json)

For $1\le |S|\le n-17$, subtracting the bound on $H-S$ gives

$$
e(H[S])+e(S,H-S)\ge 7|S|+1.
$$

The lower bound is $7|S|$ when $|H-S|=16$. Hence cliques of sizes 3, 4 and 5 have cuts of size at least 19, 23 and 26, respectively. An eight-vertex set is incident with at least 49 edges at order 23, at least 56 at order 24, and at least 57 thereafter. These thresholds power the remaining cases. [Lean proofs of the arithmetic deductions](lean/RamseyC9/CutBounds.lean)

## 4. Clique cases and finite verification

An ear of a clique is a simple path whose two endpoints are distinct clique vertices and whose interior is outside the clique. A path within the clique closes an ear of a complementary length to give a $C_9$. The short-ear cases are checked on eight-vertex nuclei containing the clique and the ear. The finite tests use possible external neighbourhoods as subsets of this eight-vertex set. For example, two distinct labels in the same neighbourhood cannot be joined by a path of length seven inside the set. More generally, an exterior path of length $d$ between two exterior vertices forbids a path of length $7-d$ inside the set between their respective attachment labels. When neighbourhoods must be disjoint, minimum degree gives a lower bound on the number of exterior vertices they would require.

| Maximum clique | Argument and finite appendix |
| --- | --- |
| 5 | A $K_5$ forces an ear of length four. Of 1,094 candidate eight-vertex sets, 815 fail the attachment cap, 278 fail the neighbourhood-size bound, and the remaining case fails a cut count. `answer-49` |
| 4 | A $K_4$ forces an ear of length four or five. The checker examines 15,191 nuclei for length five and 2,716 for length four after excluding length five. `answer-50` |
| 3 | A triangle has at least 19 outgoing edges, and its deletion leaves minimum degree at least six. The preliminary counts are 43,590, 3,999, 1,021 and 54 nuclei for longest available short ears of lengths six, five, four and three, respectively. Counting unmarked vertices completes the length-three case and the case with no short ear. `answer-51` |

For the triangle branch the sets around exterior vertices with at least three attachments are pairwise disjoint when the distance between such vertices is at least five. Choose a neighbour $y$ in the exterior of each such vertex. The set consisting of $y$ and all of its exterior neighbours has size at least seven, since $y$ has at most two attachments to the eight-vertex set. The exterior has at most 25 vertices, so there are at most three of these disjoint sets. The detailed count for each type of attachment is in the terminal appendix. [Audit notes on the archived text](AUDIT.md) · [Appendix index](certificates.json)

The case analysis rules out the minimal graph $H$. Consequently the supposed colouring of $K_{33}$ cannot exist. Combining the resulting upper bound with the construction on $K_{32}$ gives the proposed equality. This argument concerns the unrestricted three-colour problem for $C_9$.

## Reproduction and review

The finite checks can be reproduced independently of Episteme from the proof appendices, checker source files and reference outputs supplied with the dossier. The appendix index records the provenance and SHA-256 of each item. The mathematical review must also establish that the computations cover all cases of each stated lemma. [Dossier and reproduction instructions](README.en.md)

Lean verifies the lower bound and several steps of the upper-bound argument, including the numerical block budget, the reduction to a minimal dense induced subgraph and the path lemmas. It also verifies the census of 1,094 encodings for the $K_5$ case. The composition theorem `RamseyC9.isRamseyNumber33_of_reductions` takes five explicit hypotheses whose Lean proofs are pending. Proving `RamseyC9.HasRamseyProperty 33` would complete the formalization. [UpperBound.lean](lean/RamseyC9/UpperBound.lean#L9) · [Proof obligations](AUDIT.md#formalization-boundary)

## The role of Episteme in the investigation

Episteme carried out the structured proof investigation under the author's direction, coordinated by its reasoning core, Episteme-R (Episteme Reasoning). The investigation illustrates Episteme's epistemic contract. After the initial assessment of methods from Episteme-Math (Episteme Mathematics), Episteme-R recorded the proof obligation as open. In Episteme Research, Episteme developed the independence bounds, the hereditary density reduction and the finite clique cases. The dossier documents the mathematical deductions and supplies replayable exact checks for the finite calculations.

The cumulative research record preserves 51 results with their verification status across 48 checkpoints. Each checkpoint identifies the cumulative result by its SHA-256 digest and links it to supporting materials. The 28 checker outputs selected for the standalone dossier were reproduced byte for byte. [Research record and replay instructions](README.en.md)

Throughout the investigation, Episteme's exact checks served as a mathematical safeguard. They ruled out unsound shortcuts and found witnesses that tested proposed bounds as the proof developed. One witness attaches a 5-cycle to $K_{3,3}$ by four edges, with attachment sets $\{0,2\},\{1\},\{1\}$ on one side. The resulting graph avoids both $C_3$ and $C_9$ and refutes the proposed three-edge bound under these local conditions. In `answer-8`, a separate 111-edge witness retains a cycle of length 30 after deleting a triangle, refuting a proposed circumference bound. [Archived witnesses](README.en.md#archived-witnesses)

External language models held no epistemic authority in the proof. OpenAI Codex was used as a natural-language interface to relay the author's instructions to Episteme and draft prose summaries. External LLM feedback was consulted informally on intermediate strategy. The mathematical justification rests on the Lean 4 modules, the proof appendices and their cited theorems, and the archived deterministic checkers. [Tooling provenance](README.en.md#tooling-provenance)

Lean 4 checks the lower bound and the formalized deductions described above. The archived finite calculations were reproduced with Python and a C++ compiler. [Verification instructions](README.en.md)
