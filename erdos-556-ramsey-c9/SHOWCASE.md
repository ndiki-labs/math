# The Three-Colour Ramsey Number of the 9-Cycle

**Christian Hissibini** · *NDIKI Labs*

*Episteme case study for review · 27 November 2026*

**How many vertices are needed before a monochromatic 9-cycle is unavoidable when the edges of a complete graph are coloured with three colours?** Episteme led the mathematical investigation behind a proposed proof of $R_3(C_9)=33$. Radziszowski's 2026 survey lists the nine-cycle as the smallest open odd case of the Bondy–Erdős conjecture (Erdős Problem 556). Faudree, Schelten and Schiermeyer settled the preceding odd case, $R_3(C_7)=25$, in 2003. [Radziszowski, DS1.18, §6.3.1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/0#page=61) · [Faudree, Schelten and Schiermeyer, 2003](https://bibliotekanauki.pl/articles/743391.pdf)

On 32 vertices, four groups of eight give a colouring that avoids the cycle. The first colour is confined to the groups. The other two colours are bipartite and yield only even cycles. Lean 4 verifies the construction and its restrictions to smaller complete graphs.

On 33 vertices, the argument starts from the most frequent colour, which has at least 176 edges. In a putative counterexample, each colour graph has independence number at most 12. The density reduction leads to a minimal dense induced graph that is 3-connected and has minimum degree at least eight. Paths through triangles and small cliques constrain the remaining cases, which the proof rules out through exact finite checks.

**Scientific status.** The working manuscript presents the argument and the appendices support exact replay. Independent mathematical review of the upper bound and completion of its Lean 4 formalization are pending.

**Episteme's epistemic contract in practice.** The initial assessment of methods from Episteme-Math (Episteme Mathematics) left a proof obligation open. Episteme-R (Episteme Reasoning) explicitly recorded that obligation. In Episteme Research, Episteme explored proof strategies, developed the reductions and checked the finite cases. The cumulative record preserves 51 results with their verification status across 48 checkpoints, each identified by the cumulative result's SHA-256 digest and linked to supporting materials. [Manuscript](MANUSCRIPT.md)

Exact checks caught invalid shortcuts. A 111-edge construction showed that a cycle of length 30 can remain after deleting a triangle under the local conditions studied. The author directed the investigation through a natural-language interface. External feedback helped review intermediate steps. The 28 checker outputs in the standalone dossier were reproduced byte for byte against their reference outputs, using the archived sources independently of Episteme. [Proof dossier and tooling provenance](README.en.md)
