# Ramsey $C_9$ · Standalone research dossier

**Status on 27 November 2026.** Working manuscript for mathematical review. Lean 4 verifies the lower bound $R_3(C_9)\ge33$. The upper bound combines mathematical lemmas with exact computations. Independent mathematical review and full Lean formalization of the upper bound are pending.

**Author — Christian Hissibini.** The dossier includes a case study for the Episteme showcase.

- [Manuscript](MANUSCRIPT.md)
- [Episteme showcase case study](SHOWCASE.md)
- [Proof dependencies, corrections and remaining Lean obligations](AUDIT.md)
- [Lean 4 project](lean/RamseyC9.lean)
- [Certificate archive](certificates.tar.xz) and [digest index](certificates.json)

The standalone archive selects 28 sets of materials from the Episteme snapshot of 27 November 2026. Each contains the proof text, reference JSON and a ZIP of checker source files. The bundled archive has SHA-256 digest `85d5284adccfbce053a51769a20055e32f88e747e13880a8214dcfcbd23b0a8c`. [Download the bundled archive](certificates.tar.xz) The 84 files preserve the original contents, languages and digests. The original Erdős 556 dossier retains all 51 results and their checkpoints. Its full archive, `erdos-556-c9-answer-51.tar.xz`, has SHA-256 digest `9813b89832b7ef08d201c63b63d157c578caf4531594f466e09941843b3de00a`. [Archive provenance](certificates.json)

[French edition](README.fr.md)

## Tooling provenance

Episteme, developed by NDIKI Labs, coordinated the proof search, recorded exact checks at checkpoints and archived the certificates. The version used in this investigation was codenamed `PHARE`. External language models held no epistemic authority in the proof.

- OpenAI Codex, using model `gpt-6.2-sol` on 26 and 27 November 2026, served as the natural-language interface between the author and Episteme. It relayed the author's instructions and helped draft prose summaries. The author also used it to read results and track task progress. The local Codex session log confirms the model identifier.
- Google Gemini, using the Gemini 4 Neon model, supplied part of the informal external feedback on intermediate strategies and results.
- Lean 4.34.1 verified the lower bound and the formalized deductions. Python 3.13.7 and Apple Clang 17 were used to replay the archived checkers.

## Checking the Lean project

Run these commands from this directory with Elan and the version specified in `lean/lean-toolchain`.

```sh
cd lean
lake build
```

The kernel verifies the construction on $K_{32}$ and its restrictions, the equivalence between monochromatic cycles and cycles in a colour graph, the 176-edge threshold and the arithmetic for the cut bounds. The build log records the axiom check for those theorems. The project uses the Lean standard library.

For the upper bound, Lean also checks the numerical block budget, the reduction to a minimal induced subgraph, path lemmas for closing a 9-cycle and the census of 1,094 encodings for the $K_5$ case. The composition theorem takes five proof obligations as explicit hypotheses. [Formalization status and remaining obligations](AUDIT.md#formalization-boundary)

## Reading and replaying the archived proofs

Replay uses Python 3.10 or later and a C++20 compiler. All 28 outputs were reproduced byte for byte with Python 3.13.7 and Apple Clang 17. Some stages compile and recompute their dependencies.

```sh
python3 -B replay.py --integrity-only
python3 -B replay.py --answers answer-47 answer-48 answer-49 answer-50 answer-51
python3 -B replay.py --all
```

Extract the proof notes and source files into a separate directory for review.

```sh
mkdir -p proof-appendices
LC_ALL=C tar -xJf certificates.tar.xz -C proof-appendices
```

Each `proof` entry in `certificates.json` points to its source text in that directory. The review notes give the reading order and the corrections to apply when reading the original texts. The replay compares each checker's output with the reference JSON byte for byte. [Upper-bound review](AUDIT.md)

Run `python3 -B review/k5_check.py` for the independent check of the 1,094 nuclei in the $K_5$ case. [Reference output](review/k5-result.json)

### Archived witnesses

- **Four attachments to $K_{3,3}$ (`answer-44`).** Label the pentagon $0,1,2,3,4$ in cyclic order and the two parts of $K_{3,3}$ as $\{a,b,c\}$ and $\{d,e,f\}$. Add the four edges $a0,a2,b1,c1$. This graph has neither a triangle nor a $C_9$. The original check is documented in `bipartite-bicliques-c9/C9-BIPARTITE-BICLIQUES.md` in the full source archive identified above.
- **A 30-cycle after deleting a triangle (`answer-8`).** The 111-edge construction is described in `odd-block-c9/C9-ODD-BLOCK.md` in the bundled archive. Run `python3 -B replay.py --answers answer-8` to replay the exact check. [Bundled certificate archive](certificates.tar.xz)
