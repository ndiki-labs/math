import RamseyC9.Statement

namespace RamseyC9

/-- Simple graphs over the labelled vertices of a fixed finite order. -/
structure Graph (n : Nat) where
  Adj : Fin n → Fin n → Prop
  symmetric : ∀ {u v}, Adj u v → Adj v u
  loopless : ∀ u, ¬ Adj u u

def Graph.ContainsC9 (G : Graph n) : Prop :=
  ∃ vertices : Fin 9 → Fin n, Function.Injective vertices ∧
    ∀ i, G.Adj (vertices i) (vertices (next i))

/-- Pull back the edges along a vertex map. For an injective map this is
the induced subgraph on its image, with vertices relabelled by `Fin m`. -/
def Graph.induced (G : Graph n) (vertices : Fin m → Fin n) : Graph m where
  Adj u v := G.Adj (vertices u) (vertices v)
  symmetric := G.symmetric
  loopless u := G.loopless (vertices u)

theorem Graph.containsC9_of_induced {G : Graph n} (vertices : Fin m → Fin n)
    (hinj : Function.Injective vertices) (h : (G.induced vertices).ContainsC9) : G.ContainsC9 := by
  obtain ⟨cycle, hcycle, hadj⟩ := h
  exact ⟨vertices ∘ cycle, fun _ _ heq => hcycle (hinj heq), hadj⟩

/-- The simple graph formed by the edges of one colour. -/
def colourGraph (colour : EdgeColouring n) (hsym : ∀ u v, colour u v = colour v u)
    (c : Fin 3) : Graph n where
  Adj u v := u ≠ v ∧ colour u v = c
  symmetric := fun ⟨hne, hc⟩ => ⟨hne.symm, (hsym _ _).symm.trans hc⟩
  loopless := fun _ h => h.1 rfl

private theorem ne_next (i : Fin 9) : i ≠ next i := by
  intro h
  have heq := congrArg Fin.val h
  change i.val = (i.val + 1) % 9 at heq
  have hi := i.isLt
  omega

/-- A monochromatic ordered cycle and a cycle in a colour graph give the same witnesses. -/
theorem monochromatic_iff_colour_graph (colour : EdgeColouring n)
    (hsym : ∀ u v, colour u v = colour v u) :
    MonochromaticC9 colour ↔ ∃ c, (colourGraph colour hsym c).ContainsC9 := by
  constructor
  · rintro ⟨vertices, hinj, c, hc⟩
    exact ⟨c, vertices, hinj, fun i => ⟨fun h => ne_next i (hinj h), hc i⟩⟩
  · rintro ⟨c, vertices, hinj, hc⟩
    exact ⟨vertices, hinj, c, fun i => (hc i).2⟩

private def edgePairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => decide (u < v)).map fun v => (u, v)

/-- Count each undirected edge once, taking the smaller endpoint first. -/
noncomputable def Graph.edgeCount (G : Graph n) : Nat := by
  classical
  exact (edgePairs n).countP fun edge => decide (G.Adj edge.1 edge.2)

set_option maxRecDepth 4096 in
private theorem pairs33_length : (edgePairs 33).length = 528 := by decide

/-- Count the edges of colour `c` on `K₃₃`, taking the smaller endpoint first. -/
def colourEdgeCount33 (colour : EdgeColouring 33) (c : Fin 3) : Nat :=
  ((edgePairs 33).map fun edge => colour edge.1 edge.2).count c

theorem colourGraph_edgeCount33 (colour : EdgeColouring 33)
    (hsym : ∀ u v, colour u v = colour v u) (c : Fin 3) :
    (colourGraph colour hsym c).edgeCount = colourEdgeCount33 colour c := by
  classical
  unfold Graph.edgeCount colourEdgeCount33
  rw [List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro edge he
  have hlt : edge.1 < edge.2 := by
    obtain ⟨u, _, h⟩ := List.mem_flatMap.mp he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    simpa using (List.mem_filter.mp hv).2
  simp [colourGraph, Fin.ne_of_lt hlt]

private theorem count_colours (colours : List (Fin 3)) :
    colours.count 0 + colours.count 1 + colours.count 2 = colours.length := by
  induction colours with
  | nil => rfl
  | cons c rest ih =>
    by_cases h₀ : c = 0
    · subst c
      simp
      omega
    · by_cases h₁ : c = 1
      · subst c
        simp
        omega
      · have h₂ : c = 2 := by
          apply Fin.ext
          have hne₀ : c.val ≠ 0 := fun heq => h₀ (Fin.ext heq)
          have hne₁ : c.val ≠ 1 := fun heq => h₁ (Fin.ext heq)
          have hc := c.isLt
          change c.val = 2
          omega
        subst c
        simp
        omega

/-- One of the three colours accounts for at least 176 of the 528 edges. -/
theorem densest_colour33 (colour : EdgeColouring 33) :
    ∃ c, 176 ≤ colourEdgeCount33 colour c := by
  have htotal := count_colours ((edgePairs 33).map fun edge => colour edge.1 edge.2)
  rw [List.length_map, pairs33_length] at htotal
  change colourEdgeCount33 colour 0 + colourEdgeCount33 colour 1 +
    colourEdgeCount33 colour 2 = 528 at htotal
  by_cases h₀ : 176 ≤ colourEdgeCount33 colour 0
  · exact ⟨0, h₀⟩
  · by_cases h₁ : 176 ≤ colourEdgeCount33 colour 1
    · exact ⟨1, h₁⟩
    · exact ⟨2, by omega⟩

/-- A counterexample colouring produces a dense graph without a 9-cycle. -/
theorem exists_dense_c9_free_colourGraph (colour : EdgeColouring 33)
    (hsym : ∀ u v, colour u v = colour v u) (havoid : ¬ MonochromaticC9 colour) :
    ∃ c, 176 ≤ (colourGraph colour hsym c).edgeCount ∧
      ¬ (colourGraph colour hsym c).ContainsC9 := by
  obtain ⟨c, hc⟩ := densest_colour33 colour
  refine ⟨c, ?_, fun hcycle => havoid ?_⟩
  · simpa only [colourGraph_edgeCount33] using hc
  · exact (monochromatic_iff_colour_graph colour hsym).mpr ⟨c, hcycle⟩

#print axioms monochromatic_iff_colour_graph
#print axioms densest_colour33
#print axioms exists_dense_c9_free_colourGraph

end RamseyC9
