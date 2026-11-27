import RamseyC9.BlockReduction
import RamseyC9.LowerBound

namespace RamseyC9

/-- Compose the checked reductions. Each remaining graph theorem is a
hypothesis, so the statement exposes precisely where the formal proof
still needs the mathematical arguments in the appendices. -/
theorem isRamseyNumber33_of_reductions
    (independence_bound : ∀ (colour : EdgeColouring 33)
      (hsym : ∀ u v, colour u v = colour v u), ¬ MonochromaticC9 colour →
        ∀ c, ¬ (colourGraph colour hsym c).HasIndependentSet 13)
    (decomposition : ∀ G : Graph 33, Nonempty G.BlockDecomposition)
    (extremal_bound : ∀ (n : Nat) (G : Graph n), ¬ G.ContainsC9 →
      G.edgeCount ≤ cycleFreeEdgeBound n)
    (block_restrictions : ∀ (G : Graph 33) (blocks : G.BlockDecomposition)
      (b : VertexSubset 33), b ∈ blocks.blocks →
      25 ≤ b.order → b.order ≤ 33 → (G.induced b.vertex).IsTwoConnected →
      ¬ G.ContainsC9 → ¬ G.HasIndependentSet 13 →
      requiredBlockEdges b.order ≤ (G.induced b.vertex).edgeCount →
        (b.order = 32 ∨ b.order = 33) ∧ DensityRestrictions (G.induced b.vertex))
    (exclude_minimal : ∀ (n : Nat) (G : Graph n),
      16 ≤ n → n ≤ 33 → DensityRestrictions G → densityBound n < G.edgeCount →
      (∀ (m : Nat) (vertices : Fin m → Fin n),
        16 ≤ m → m < n → Function.Injective vertices →
          (G.induced vertices).edgeCount ≤ densityBound m) → False) :
    IsRamseyNumber 33 := by
  classical
  apply ramsey_number_iff_upper_bound.mpr
  intro colour hsym
  by_cases hcycle : MonochromaticC9 colour
  · exact hcycle
  · exfalso
    obtain ⟨c, hdense, havoid⟩ := exists_dense_c9_free_colourGraph colour hsym hcycle
    let G := colourGraph colour hsym c
    obtain ⟨blocks⟩ := decomposition G
    obtain ⟨block, hmem, hlo, hhi, hedges, hconn, _⟩ :=
      Graph.exists_large_block_of_decomposition blocks hdense havoid extremal_bound
    let B := G.induced block.vertex
    obtain ⟨horder, hclass⟩ := block_restrictions G blocks block hmem hlo hhi hconn havoid
      (independence_bound colour hsym hcycle c) hedges
    obtain ⟨n, H, hnlo, hnhi, hH, hHdense, hmin⟩ := exists_minimal_dense_graph B
      (by omega) hhi hclass (densityBound_lt_of_last_block B horder hedges)
    exact exclude_minimal n H hnlo hnhi hH hHdense hmin

#print axioms isRamseyNumber33_of_reductions

end RamseyC9
