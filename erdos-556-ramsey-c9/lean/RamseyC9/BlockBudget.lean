import RamseyC9.Statement

namespace RamseyC9

private def chooseTwo (n : Nat) : Nat := n * (n - 1) / 2

/-- The numerical edge bounds from Füredi–Gunderson used in `answer-7`. -/
def cycleFreeEdgeBound (order : Nat) : Nat :=
  if order < 9 then chooseTwo order
  else if order < 14 then
    28 * ((order - 1) / 7) + chooseTwo ((order - 1) % 7 + 1)
  else order * order / 4

/-- The budget in `answer-7` for blocks of order at most 24, indexed by
the available sum of block orders minus one. -/
private def smallBlockBudget (available : Nat) : Nat :=
  let bounds := #[0, 1, 3, 6, 10, 15, 21, 28, 29, 31, 34, 38, 43, 49, 56, 64,
    72, 81, 90, 100, 110, 121, 132, 144, 145, 147, 150, 154, 159, 165, 172, 173, 175]
  bounds[available]?.getD 0

private def exteriorBudget (available : Nat) : Nat := cycleFreeEdgeBound (available + 1)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem smallBlockBudget_step : ∀ t : Fin 33, ∀ s : Fin 24,
    1 ≤ s.val → s.val ≤ t.val →
      cycleFreeEdgeBound (s.val + 1) + smallBlockBudget (t.val - s.val) ≤
        smallBlockBudget t.val := by decide

private theorem exteriorBudget_step : ∀ t s : Fin 9,
    s.val ≤ t.val → cycleFreeEdgeBound (s.val + 1) + exteriorBudget (t.val - s.val) ≤
      exteriorBudget t.val := by decide

private def blockCost (block : Nat × Nat) : Nat := block.1 - 1

private theorem sum_le_budget (allowed : Nat × Nat → Prop)
    (budget : Nat → Nat) (limit : Nat)
    (step : ∀ b, allowed b → ∀ t, blockCost b ≤ t → t ≤ limit →
      b.2 + budget (t - blockCost b) ≤ budget t)
    (blocks : List (Nat × Nat)) (t : Nat)
    (ht : t ≤ limit) (hcost : (blocks.map blockCost).sum ≤ t)
    (hallowed : ∀ b ∈ blocks, allowed b) : (blocks.map Prod.snd).sum ≤ budget t := by
  induction blocks generalizing t with
  | nil => simp
  | cons b rest ih =>
    simp only [List.map_cons, List.sum_cons] at hcost ⊢
    have hb : blockCost b ≤ t := by omega
    have htail : (rest.map Prod.snd).sum ≤ budget (t - blockCost b) :=
      ih (t - blockCost b) (by omega) (by omega) fun d hd =>
        hallowed d (List.mem_cons_of_mem b hd)
    exact Nat.le_trans (Nat.add_le_add_left htail _) (step b (hallowed b (by simp)) t hb ht)

/-- A list of blocks of orders 2–24 has at most 175 edges if it obeys
the vertex budget and the numerical edge bound for each block. -/
theorem block_edges_le_175 (blocks : List (Nat × Nat))
    (hcost : (blocks.map fun b => b.1 - 1).sum ≤ 32)
    (horder : ∀ b ∈ blocks, 2 ≤ b.1 ∧ b.1 ≤ 24)
    (hedges : ∀ b ∈ blocks, b.2 ≤ cycleFreeEdgeBound b.1) :
    (blocks.map Prod.snd).sum ≤ 175 := by
  change (blocks.map Prod.snd).sum ≤ smallBlockBudget 32
  refine sum_le_budget (fun b => 2 ≤ b.1 ∧ b.1 ≤ 24 ∧ b.2 ≤ cycleFreeEdgeBound b.1)
    smallBlockBudget 32 ?_ blocks 32 (by decide) hcost ?_
  · intro b hb t hbt ht
    have hmin : 1 ≤ blockCost b := by unfold blockCost; omega
    have hmax : blockCost b < 24 := by unfold blockCost; omega
    have hsize : blockCost b + 1 = b.1 := by unfold blockCost; omega
    have hstep := smallBlockBudget_step ⟨t, by omega⟩ ⟨blockCost b, hmax⟩ hmin hbt
    change cycleFreeEdgeBound (blockCost b + 1) + smallBlockBudget (t - blockCost b) ≤
      smallBlockBudget t at hstep
    rw [hsize] at hstep
    exact Nat.le_trans (Nat.add_le_add_right hb.2.2 _) hstep
  · intro b hb
    exact ⟨(horder b hb).1, (horder b hb).2, hedges b hb⟩

private theorem exterior_edges_le (blocks : List (Nat × Nat)) (t : Nat)
    (ht : t ≤ 8) (hcost : (blocks.map blockCost).sum ≤ t)
    (hlocal : ∀ b ∈ blocks, 2 ≤ b.1 ∧ b.2 ≤ cycleFreeEdgeBound b.1) :
    (blocks.map Prod.snd).sum ≤ exteriorBudget t := by
  refine sum_le_budget (fun b => 2 ≤ b.1 ∧ b.2 ≤ cycleFreeEdgeBound b.1)
    exteriorBudget 8 ?_ blocks t ht hcost hlocal
  intro b hb u hbu hu
  have hsize : blockCost b + 1 = b.1 := by unfold blockCost; omega
  have hstep := exteriorBudget_step ⟨u, by omega⟩ ⟨blockCost b, by omega⟩ hbu
  change cycleFreeEdgeBound (blockCost b + 1) + exteriorBudget (u - blockCost b) ≤
    exteriorBudget u at hstep
  rw [hsize] at hstep
  exact Nat.le_trans (Nat.add_le_add_right hb.2 _) hstep

/-- The lower edge thresholds in `answer-7` for a block of order 25–33. -/
def requiredBlockEdges (order : Nat) : Nat := 176 - cycleFreeEdgeBound (34 - order)

theorem requiredBlockEdges_table :
    (List.range 9).map (fun i => requiredBlockEdges (25 + i)) =
      [147, 148, 155, 161, 166, 170, 173, 175, 176] := by decide

/-- The numerical part of the passage from 176 edges to a large block.
The list records one pair `(order, edge count)` for each block. -/
theorem exists_large_block_of_budget (blocks : List (Nat × Nat))
    (hcost : (blocks.map fun b => b.1 - 1).sum ≤ 32)
    (hlocal : ∀ b ∈ blocks, 2 ≤ b.1 ∧ b.2 ≤ cycleFreeEdgeBound b.1)
    (htotal : 176 ≤ (blocks.map Prod.snd).sum) :
    ∃ b ∈ blocks, 25 ≤ b.1 ∧ b.1 ≤ 33 ∧ requiredBlockEdges b.1 ≤ b.2 := by
  have hlarge : ∃ b ∈ blocks, 25 ≤ b.1 := by
    classical
    by_cases h : ∃ b ∈ blocks, 25 ≤ b.1
    · exact h
    · have hsmall : ∀ b ∈ blocks, 2 ≤ b.1 ∧ b.1 ≤ 24 := by
        intro b hb
        refine ⟨(hlocal b hb).1, ?_⟩
        by_cases hn : 25 ≤ b.1
        · exact False.elim (h ⟨b, hb, hn⟩)
        · omega
      have hcap := block_edges_le_175 blocks hcost hsmall fun b hb => (hlocal b hb).2
      omega
  obtain ⟨b, hb, hbig⟩ := hlarge
  obtain ⟨before, after, rfl⟩ := List.append_of_mem hb
  simp only [List.map_append, List.map_cons, List.sum_append_nat, List.sum_cons] at hcost htotal
  change (before.map blockCost).sum + (b.1 - 1 + (after.map blockCost).sum) ≤ 32 at hcost
  have horder : b.1 ≤ 33 := by omega
  have houtside : ((before ++ after).map blockCost).sum ≤ 33 - b.1 := by
    simp only [List.map_append, List.sum_append_nat]
    omega
  have hrest := exterior_edges_le (before ++ after) (33 - b.1) (by omega) houtside (by
    intro d hd
    apply hlocal d
    simp only [List.mem_append, List.mem_cons] at hd ⊢
    exact hd.elim Or.inl (fun h => Or.inr (Or.inr h)))
  simp only [List.map_append, List.sum_append_nat] at hrest
  have heq : 33 - b.1 + 1 = 34 - b.1 := by omega
  unfold exteriorBudget at hrest
  rw [heq] at hrest
  exact ⟨b, hb, hbig, horder, by unfold requiredBlockEdges; omega⟩

#print axioms block_edges_le_175
#print axioms exists_large_block_of_budget
#print axioms requiredBlockEdges_table

end RamseyC9
