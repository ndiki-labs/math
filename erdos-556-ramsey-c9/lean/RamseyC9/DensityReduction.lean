import RamseyC9.ColourGraphs
import RamseyC9.CutBounds
import RamseyC9.BlockBudget

namespace RamseyC9

def Graph.HasIndependentSet (G : Graph n) (size : Nat) : Prop :=
  ∃ vertices : Fin size → Fin n, Function.Injective vertices ∧
    ∀ u v, ¬ G.Adj (vertices u) (vertices v)

def Graph.ContainsClique (G : Graph n) (size : Nat) : Prop :=
  ∃ vertices : Fin size → Fin n, Function.Injective vertices ∧
    ∀ u v, u ≠ v → G.Adj (vertices u) (vertices v)

private theorem injective_lastCases {vertices : Fin size → Fin n} (outside : Fin n)
    (hinj : Function.Injective vertices) (hfresh : ∀ i, vertices i ≠ outside) :
    Function.Injective (Fin.lastCases outside vertices) := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact fun _ => rfl
    | cast j =>
      intro heq
      exact False.elim (hfresh j (by simpa using heq.symm))
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      intro heq
      exact False.elim (hfresh i (by simpa using heq))
    | cast j =>
      intro heq
      exact congrArg Fin.castSucc (hinj (by simpa using heq))

/-- A fresh vertex with no neighbours in an independent set extends it by one. -/
theorem Graph.contains_larger_independentSet {G : Graph n} (vertices : Fin size → Fin n)
    (hinj : Function.Injective vertices) (hstable : ∀ u v, ¬ G.Adj (vertices u) (vertices v))
    (outside : Fin n) (hfresh : ∀ i, vertices i ≠ outside)
    (hno : ∀ i, ¬ G.Adj outside (vertices i)) : G.HasIndependentSet (size + 1) := by
  let extended : Fin (size + 1) → Fin n := Fin.lastCases outside vertices
  refine ⟨extended, injective_lastCases outside hinj hfresh, ?_⟩
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa [extended] using G.loopless outside
    | cast j => simpa [extended] using hno j
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      intro hadj
      exact hno i (G.symmetric (by simpa [extended] using hadj))
    | cast j => simpa [extended] using hstable i j

/-- A fresh vertex adjacent to every vertex of a clique extends it by one.
This justifies the forbidden complete attachment to a triangle, a $K_4$
or a $K_5$ in the corresponding maximal-clique branch. -/
theorem Graph.contains_clique_of_complete_attachment {G : Graph n} (clique : Fin size → Fin n)
    (hinj : Function.Injective clique)
    (hclique : ∀ u v, u ≠ v → G.Adj (clique u) (clique v)) (outside : Fin n)
    (hfresh : ∀ i, clique i ≠ outside) (hjoins : ∀ i, G.Adj outside (clique i)) :
    G.ContainsClique (size + 1) := by
  let extended : Fin (size + 1) → Fin n := Fin.lastCases outside clique
  refine ⟨extended, injective_lastCases outside hinj hfresh, ?_⟩
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => intro hne; exact False.elim (hne rfl)
    | cast j => intro _; simpa [extended] using hjoins j
  | cast i =>
    induction j using Fin.lastCases with
    | last => intro _; simpa [extended] using G.symmetric (hjoins i)
    | cast j =>
      intro hne
      simpa [extended] using hclique i j (fun h => hne (congrArg Fin.castSucc h))

/-- The first four labels give one part and the last four the other. -/
def Graph.ContainsInducedK44 (G : Graph n) : Prop :=
  ∃ vertices : Fin 8 → Fin n, Function.Injective vertices ∧
    ∀ u v, G.Adj (vertices u) (vertices v) ↔
      (u.val < 4 ∧ 4 ≤ v.val) ∨ (v.val < 4 ∧ 4 ≤ u.val)

def Graph.Bipartite (G : Graph n) : Prop :=
  ∃ part : Fin n → Bool, ∀ u v, G.Adj u v → part u ≠ part v

private theorem hasIndependentSet_of_list {G : Graph n} {size : Nat}
    (vertices : List (Fin n)) (hnodup : vertices.Nodup) (hsize : size ≤ vertices.length)
    (hstable : ∀ u ∈ vertices, ∀ v ∈ vertices, ¬ G.Adj u v) : G.HasIndependentSet size := by
  have hindex (i : Fin size) : i.val < vertices.length := Nat.lt_of_lt_of_le i.isLt hsize
  refine ⟨fun i => vertices[i.val]'(hindex i), ?_, ?_⟩
  · intro i j heq
    exact Fin.ext (hnodup.eq_of_getElem_eq (hindex i) (hindex j) heq)
  · intro i j
    exact hstable _ (List.getElem_mem (hindex i)) _ (List.getElem_mem (hindex j))

/-- A graph on at least 25 vertices with no independent set of size 13
is nonbipartite. -/
theorem Graph.not_bipartite_of_no_independent_thirteen {G : Graph n} (hn : 25 ≤ n)
    (hstable : ¬ G.HasIndependentSet 13) : ¬ G.Bipartite := by
  rintro ⟨part, hcross⟩
  let vertices := List.finRange n
  have hsplit : n = (vertices.filter part).length + (vertices.filter (fun a => !part a)).length := by
    simpa only [vertices, List.length_finRange, List.countP_eq_length_filter,
      decide_not, Bool.decide_coe] using
      (List.length_eq_countP_add_countP part (l := vertices))
  have hlarge : 13 ≤ (vertices.filter part).length ∨
      13 ≤ (vertices.filter (fun a => !part a)).length := by omega
  apply hstable
  rcases hlarge with htrue | hfalse
  · apply hasIndependentSet_of_list _ (List.Pairwise.filter part (List.nodup_finRange n)) htrue
    intro u hu v hv huv
    exact hcross u v huv ((List.mem_filter.mp hu).2.trans (List.mem_filter.mp hv).2.symm)
  · refine hasIndependentSet_of_list _
      (List.Pairwise.filter (fun a => !part a) (List.nodup_finRange n)) hfalse ?_
    intro u hu v hv huv
    have hu' : part u = false := by simpa using (List.mem_filter.mp hu).2
    have hv' : part v = false := by simpa using (List.mem_filter.mp hv).2
    exact hcross u v huv (hu'.trans hv'.symm)

/-- The hereditary graph class used in the minimum-order argument of `answer-47`. -/
structure DensityRestrictions (G : Graph n) : Prop where
  noCycle : ¬ G.ContainsC9
  noIndependentSet : ¬ G.HasIndependentSet 13
  noClique : ¬ G.ContainsClique 6
  noInducedBiclique : ¬ G.ContainsInducedK44

theorem DensityRestrictions.induced {G : Graph n} (h : DensityRestrictions G)
    (vertices : Fin m → Fin n) (hinj : Function.Injective vertices) :
    DensityRestrictions (G.induced vertices) := by
  constructor
  · exact fun hcycle => h.noCycle (G.containsC9_of_induced vertices hinj hcycle)
  · rintro ⟨stable, hstable, hadj⟩
    exact h.noIndependentSet ⟨vertices ∘ stable, fun _ _ heq => hstable (hinj heq), hadj⟩
  · rintro ⟨clique, hclique, hadj⟩
    exact h.noClique ⟨vertices ∘ clique, fun _ _ heq => hclique (hinj heq), hadj⟩
  · rintro ⟨parts, hparts, hadj⟩
    exact h.noInducedBiclique ⟨vertices ∘ parts, fun _ _ heq => hparts (hinj heq), hadj⟩

/-- Among graphs in the hereditary class violating the density bound,
some graph has all its smaller induced subgraphs of order at least 16
within the bound. -/
theorem exists_minimal_dense_graph {n : Nat} (G : Graph n)
    (hlower : 16 ≤ n) (hupper : n ≤ 33) (hclass : DensityRestrictions G)
    (hedges : densityBound n < G.edgeCount) :
    ∃ (order : Nat) (H : Graph order), 16 ≤ order ∧ order ≤ 33 ∧
      DensityRestrictions H ∧ densityBound order < H.edgeCount ∧
      ∀ (m : Nat) (vertices : Fin m → Fin order),
        16 ≤ m → m < order → Function.Injective vertices →
          (H.induced vertices).edgeCount ≤ densityBound m := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ (m : Nat) (_ : m < n) (H : Graph m),
        16 ≤ m ∧ DensityRestrictions H ∧ densityBound m < H.edgeCount
    · obtain ⟨m, hlt, H, hm, hH, hdense⟩ := h
      exact ih m hlt H hm (by omega) hH hdense
    · refine ⟨n, G, hlower, hupper, hclass, hedges, ?_⟩
      intro m vertices hm hlt hinj
      by_cases hsmall : densityBound m < (G.induced vertices).edgeCount
      · exact False.elim (h ⟨m, hlt, G.induced vertices, hm, hclass.induced vertices hinj, hsmall⟩)
      · omega

theorem densityBound_lt_of_last_block (G : Graph n) (horder : n = 32 ∨ n = 33)
    (hedges : requiredBlockEdges n ≤ G.edgeCount) : densityBound n < G.edgeCount := by
  rcases horder with rfl | rfl
  · exact Nat.lt_of_lt_of_le (by decide : densityBound 32 < requiredBlockEdges 32) hedges
  · exact Nat.lt_of_lt_of_le (by decide : densityBound 33 < requiredBlockEdges 33) hedges

#print axioms DensityRestrictions.induced
#print axioms Graph.contains_clique_of_complete_attachment
#print axioms Graph.contains_larger_independentSet
#print axioms Graph.not_bipartite_of_no_independent_thirteen
#print axioms exists_minimal_dense_graph
#print axioms densityBound_lt_of_last_block

end RamseyC9
