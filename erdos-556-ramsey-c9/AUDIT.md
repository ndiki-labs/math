# Upper-bound review and formalization

## Dependency map

This map records the ingredients actually used in the final composition and the sections of multi-result certificates on which it depends. The [appendix index](certificates.json) locates the original documents and exact computations. Several original checkers replay additional, historically useful calculations alongside the needed ones.

| Proposition needed | Proof appendices and sections |
| --- | --- |
| Every colour has independence number at most 12 | `answer-4` to `answer-6`, then `answer-33` through the two cases for the sizes of the overlapping independent sets |
| A colour with 176 edges has a block of order at least 25, with the required edge count | `answer-7`, the block budget and exterior edge bound |
| The dense block cannot have order 25–31 | `answer-19` §1, `answer-22` on minimum-degree deletion, `answer-24` on order 30, `answer-27` §1. The initial block reductions use `answer-8` to `answer-10` for circumference, odd girth and the exclusion of $K_6$ at these orders. The arguments also use the induced bipartite path conditions and bounds in `answer-12` to `answer-18` and `answer-25`–`answer-26`. |
| A remaining block of order 32–33 has no $K_6$ and no induced $K_{4,4}$ | `answer-10`–`answer-11`, the last nucleus calculation in `answer-33`, and `answer-35` through its exclusion of the prescribed cores |
| Minimal dense violation has order 23–33, degree at least 8 and is 3-connected, with odd girth 3 or 5 | `answer-47`, including its block bounds, separator analysis and shortest odd-cycle argument |
| Odd girth 5 is impossible | `answer-48`, using the pentagon cuts from `answer-9` and the heptagon attachment rules from `answer-8` |
| The minimal graph has clique number at most 4, then at most 3 | `answer-49` and `answer-50`. Both reuse the short-ear path counts or neighbourhood arguments originating in `answer-10`, `answer-47` and `answer-49`. |
| A triangle in the minimal graph is impossible | `answer-51`, the four short-ear cases and the final shortest-path count |
| $K_{32}$ admits an avoiding colouring | [`colouring32_avoids_c9`](lean/RamseyC9/LowerBound.lean) |

The ordering test in `replay.py --integrity-only` checks the explicit `prior_answers` fields of the archived certificates. The part of `answer-35` that is used by the final composition is the maximal-core bound. Its checker `core-bounds.py` loads the core geometry of `answer-17` and the bipartite bound of `answer-25`. It uses the independence constraints and initial core-size limits supplied by `answer-33`. These inputs precede `answer-35`. The later pentagon and residual-packing calculations in the same archived checker concern other conclusions.

## The order-23 transition

`answer-47` gives $\delta(H)\ge8$ and a nonbipartite graph at order 23. If it were triangle-free, it would satisfy the hypotheses of Theorem 1.8 in Brandt, Faudree and Goddard. In particular it is distinct from $C_5$ and $8>23/3$. The theorem supplies every length from four through $\min\{23,2(23-\alpha(H))\}\ge22$, including nine. Thus `answer-48`, whose census covers orders 24–33, completes the triangle-free branch. [Brandt, Faudree and Goddard, Theorem 1.8](https://people.computing.clemson.edu/~goddard/papers/weakpanFinal.pdf)

## External results at the main transitions

| Result | Hypotheses used in this proof |
| --- | --- |
| Nikiforov and Schelp, Theorem 2 | In both stable-set reductions the two edge colours avoid $C_9$ on the full complete graph. Set $n=9$ and take $\beta=1/3$ at order 15 or $\beta=4/9$ at order 14. Both meet $0<\beta\le\lfloor n/2\rfloor/n$. [Original text](https://arxiv.org/pdf/math/0602627) |
| Wang and Chen and the Hansson formula | Both sets are $\{C_9,C_{10}\}$. The minimum cycle length is nine and the minimum even cycle length is ten in each set, so the formula yields $9+10/2-1=13$. The formula applies to the full two-colouring of the independent 13-set. [Wang and Chen](https://doi.org/10.1002/jgt.22564) · [Hansson, Definition of $m$ and Conjecture 1.11](https://arxiv.org/pdf/1605.04301) |
| Nikiforov and Schelp, Lemma 14 | On the ten vertices of the monochromatic $C_{10}$, its colour is Hamiltonian and both it and its complement avoid $C_9$. Use the lemma at $n=5$. [Original text, §4.1](https://arxiv.org/pdf/math/0602627#page=14) |
| Kopylov and the stability refinement | The graph to which the bound is applied is an individual 2-connected block with circumference less than nine. Kopylov applies for its orders at least nine. Use Theorem 2.1 of the later exposition at $t=4$, $k=9$ and block order at least $3t=12$. [Original stability paper](https://arxiv.org/pdf/1704.02866) |
| Brandt and Brandt, Faudree and Goddard | The edge condition is strict, $e>\lfloor(n-1)^2/4\rfloor+1$, and the graph is nonbipartite. The degree condition in Theorem 1.7 is $\delta\ge(n+2)/3$ for nonbipartite graphs, with girth at most four and no connectivity requirement. In either application the circumference is established separately whenever it is used to obtain $C_9$. [Brandt](https://doi.org/10.1016/S0166-218X(97)00032-2) · [Theorem 1.7](https://people.computing.clemson.edu/~goddard/papers/weakpanFinal.pdf) |
| Lin, Wang and Zhou, Theorem 1.2 | At $k=8$ the minimal graph is 3-connected, nonbipartite and has $\delta\ge8$. The sole stated exception $K_{k+1}=K_9$ is excluded by its order and by the forbidden clique. The paper is published in *Journal of Graph Theory*, volume 110 (2025), pp. 431–436. [Version 2, theorem statement](https://arxiv.org/html/2410.00648v2) · [Published article](https://doi.org/10.1002/jgt.23281) |

## Corrections identified while preparing the manuscript

1. **Radius-two neighbourhood in `answer-51`.** Its prose gives “at least eight” vertices around a high-attachment vertex $x$ and its selected neighbour $y$. Since $y$ has at most two attachments to the nucleus, it has at least six neighbours in the exterior, including $x$. The closed neighbourhood of $y$ therefore contains at least **seven** vertices and lies within distance two of $x$. Four such disjoint neighbourhoods require at least 28 vertices, above the maximum 25. The next finer count already uses $7-j$ other neighbours for a vertex with $j$ attachments. The checker uses that expression and verifies the distance constraints. The counting correction preserves this step's bound of three high-attachment vertices.
2. **Kopylov parameter in `answer-47`.** For the convention $h(s,k,a)=\binom{k-a}{2}+a(s-k+a)$, the value $h(s,9,4)$ is $4s-10$. The archived text uses $4s-5$, a valid, weaker upper bound. In the stability alternative there are $s-5$ vertices outside the distinguished clique, of which at most three can keep all four common neighbours. Subtracting $s-8$ from the exact count gives $3s-2$, which also implies the archived bound $3s+3$. Both printed base-case bounds therefore still follow. [Definition and theorems in Füredi et al.](https://arxiv.org/pdf/1704.02866)

The archive preserves the original bytes. These corrections are part of the reading instructions for the archived appendices.

## Second implementation of the $K_5$ calculation

The [review checker](review/k5_check.py) constructs the 1,094 nuclei from the multiset of clique attachments. It computes simple paths with ordinary depth-first walks, rebuilds all admissible profiles and checks the final cut cap. It recovers the split $815+278+1$ and the eleven cut comparisons for the one surviving nucleus. The checker implements the mathematical rules from the written appendix and does not call the archived implementation. This second implementation covers the finite calculation. The argument for the existence of the ear and the implication from the profile constraints to the desired edge bound are separate parts of the mathematical proof. [Reproduced counts](review/k5-result.json)

## Formalization boundary

Lean checks `RamseyC9.no_ramsey_through_32` and reduces `RamseyC9.IsRamseyNumber 33` to `RamseyC9.HasRamseyProperty 33`. It also checks the arithmetic for the cut thresholds and the number of disjoint neighbourhoods. The public Lean statement describes a 9-cycle by an injective vertex map and the nine consecutive edge constraints, including the closing edge. The colour-graph module connects this definition to a cycle in a simple graph and proves the existence of a colour with at least 176 edges.

Lean checks the 175-edge budget for blocks of order at most 24, subject to the block size and edge bounds, and all nine thresholds for larger blocks. Given a block decomposition and the extremal edge bound, it extracts a dense induced block. Lean also checks the reduction to a minimal induced subgraph in the hereditary class and the path lemmas that close a 9-cycle. [Block budget](lean/RamseyC9/BlockBudget.lean) · [Induced-subgraph reduction](lean/RamseyC9/DensityReduction.lean) · [Path lemmas](lean/RamseyC9/Paths.lean)

The composition theorem takes five explicit hypotheses that still need Lean proofs.

1. The independence bound of 12 for each colour in a colouring that avoids a monochromatic 9-cycle.
2. The existence of the required block decomposition.
3. The extremal edge bound for graphs with no 9-cycle.
4. The restriction of the dense block to orders 32 and 33 and to the hereditary class.
5. The exclusion of a minimal dense graph in that class.

[Composition theorem](lean/RamseyC9/UpperBound.lean)

For the $K_5$ case, Lean certifies the census of 1,094 encodings and that sorting any admissible encoding produces an entry. The proof still needs to connect every candidate graph to an encoding and to show that the checker's exclusions imply the required bound for the graph. Independent mathematical review of the complete upper-bound argument remains pending. [Census](lean/RamseyC9/K5EarKernels.lean)
