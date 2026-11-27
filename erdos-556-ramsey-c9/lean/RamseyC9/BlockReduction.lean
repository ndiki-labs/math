import RamseyC9.DensityReduction
import RamseyC9.Paths

namespace RamseyC9

/-- A subset of the vertices, enumerated without repetitions. -/
structure VertexSubset (n : Nat) where
  order : Nat
  vertex : Fin order → Fin n
  injective : Function.Injective vertex

theorem VertexSubset.exists_outside (b : VertexSubset n) (horder : b.order < n) :
    ∃ x : Fin n, ∀ i, b.vertex i ≠ x := by
  classical
  by_cases h : ∃ x : Fin n, ∀ i, b.vertex i ≠ x
  · exact h
  · exfalso
    have hsubset : List.finRange n ⊆ (List.finRange b.order).map b.vertex := by
      intro x _
      have hpreimage : ∃ i, b.vertex i = x :=
        Classical.byContradiction fun hnone => h ⟨x, fun i hi => hnone ⟨i, hi⟩⟩
      obtain ⟨i, rfl⟩ := hpreimage
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hlength := (List.nodup_finRange n).length_le_of_subset hsubset
    simp only [List.length_finRange, List.length_map] at hlength
    omega

/-- The properties of the block decomposition used in `answer-7`.
Subsets of order one can be omitted because they contribute no edges or cost. -/
structure Graph.BlockDecomposition (G : Graph n) where
  blocks : List (VertexSubset n)
  order_ge_two : ∀ b ∈ blocks, 2 ≤ b.order
  connected : ∀ b ∈ blocks, b.order = 2 ∨ (G.induced b.vertex).IsTwoConnected
  vertex_budget : (blocks.map fun b => b.order - 1).sum ≤ n - 1
  edge_sum : G.edgeCount = (blocks.map fun b => (G.induced b.vertex).edgeCount).sum
  outside_attachment : ∀ b ∈ blocks, ∀ x, (∀ i, b.vertex i ≠ x) →
    ∀ i j, G.Adj x (b.vertex i) → G.Adj x (b.vertex j) → i = j

/-- Apply the verified numerical budget to actual induced subgraphs. The
block decomposition and the extremal theorem enter as explicit hypotheses. -/
theorem Graph.exists_large_block_of_decomposition {G : Graph 33} (blocks : G.BlockDecomposition)
    (hdense : 176 ≤ G.edgeCount) (havoid : ¬ G.ContainsC9)
    (hextremal : ∀ (n : Nat) (H : Graph n), ¬ H.ContainsC9 →
      H.edgeCount ≤ cycleFreeEdgeBound n) :
    ∃ b ∈ blocks.blocks, 25 ≤ b.order ∧ b.order ≤ 33 ∧
      requiredBlockEdges b.order ≤ (G.induced b.vertex).edgeCount ∧
      (G.induced b.vertex).IsTwoConnected ∧ ¬ (G.induced b.vertex).ContainsC9 := by
  let data := blocks.blocks.map fun b => (b.order, (G.induced b.vertex).edgeCount)
  have hcost : (data.map fun b => b.1 - 1).sum ≤ 32 := by
    simp only [data, List.map_map, Function.comp_def]
    exact blocks.vertex_budget
  have hlocal : ∀ b ∈ data, 2 ≤ b.1 ∧ b.2 ≤ cycleFreeEdgeBound b.1 := by
    intro b hb
    obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hb
    refine ⟨blocks.order_ge_two piece hpiece, hextremal _ _ ?_⟩
    exact fun hcycle => havoid (G.containsC9_of_induced piece.vertex piece.injective hcycle)
  have htotal : 176 ≤ (data.map Prod.snd).sum := by
    rw [blocks.edge_sum] at hdense
    simp only [data, List.map_map, Function.comp_def]
    exact hdense
  obtain ⟨entry, hentry, hlo, hhi, hcount⟩ := exists_large_block_of_budget data hcost hlocal htotal
  obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hentry
  refine ⟨piece, hpiece, hlo, hhi, hcount, ?_, ?_⟩
  · rcases blocks.connected piece hpiece with htwo | hconnected
    · omega
    · exact hconnected
  · exact fun hcycle => havoid (G.containsC9_of_induced piece.vertex piece.injective hcycle)

/-- Every 12-vertex independent set in a block contains the unique attachment
of an exterior vertex, if the host graph has no 13-vertex independent set.
This is the independence restriction used for order 32 in `answer-35`. -/
theorem Graph.block_stable_attachment {G : Graph n} (blocks : G.BlockDecomposition)
    (b : VertexSubset n) (hb : b ∈ blocks.blocks) (outside : Fin n)
    (hfresh : ∀ i, b.vertex i ≠ outside) (hcap : ¬ G.HasIndependentSet 13)
    (stable : Fin 12 → Fin b.order) (hinj : Function.Injective stable)
    (hstable : ∀ i j, ¬ (G.induced b.vertex).Adj (stable i) (stable j)) :
    ∃ i, G.Adj outside (b.vertex (stable i)) ∧
      ∀ j, G.Adj outside (b.vertex (stable j)) → j = i := by
  classical
  by_cases h : ∃ i, G.Adj outside (b.vertex (stable i))
  · obtain ⟨i, hi⟩ := h
    refine ⟨i, hi, fun j hj => hinj ?_⟩
    exact blocks.outside_attachment b hb outside hfresh _ _ hj hi
  · exfalso
    exact hcap (G.contains_larger_independentSet (b.vertex ∘ stable)
      (fun _ _ heq => hinj (b.injective heq)) hstable outside (fun i => hfresh (stable i))
      (fun i hi => h ⟨i, hi⟩))

#print axioms Graph.exists_large_block_of_decomposition
#print axioms Graph.block_stable_attachment
#print axioms VertexSubset.exists_outside

end RamseyC9
