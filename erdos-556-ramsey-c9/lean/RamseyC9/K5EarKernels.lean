import RamseyC9.Statement

namespace RamseyC9

/-- For each of five clique vertices, store its neighbours among the three
internal vertices of a four-edge ear as a three-bit mask. Enumerating the
masks in nondecreasing order removes permutations of the clique labels. -/
private def sortedMasks : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | count + 1, lower => ((List.range 8).filter fun mask => decide (lower ≤ mask)).flatMap
      fun mask => (sortedMasks count mask).map fun tail => mask :: tail

/-- No internal ear vertex sees all five clique vertices. Each end of
the ear has a clique neighbour and their union contains at least two
vertices, so the neighbours at the two ends can be chosen distinct. -/
def k5EarAdmissible (masks : List Nat) : Bool :=
  (List.range 3).all (fun i => decide (masks.countP (fun mask => mask.testBit i) ≤ 4)) &&
    decide (0 < masks.countP (fun mask => mask.testBit 0)) &&
    decide (0 < masks.countP (fun mask => mask.testBit 2)) &&
    decide (2 ≤ masks.countP (fun mask => mask.testBit 0 || mask.testBit 2))

/-- The second component specifies whether the first and last internal
vertices of the ear are joined. The two consecutive ear edges are fixed.
This is the census in `answer-49` before its path and cut tests. -/
def k5EarKernels : List (List Nat × Bool) :=
  ((sortedMasks 5 0).filter k5EarAdmissible).flatMap fun masks => [(masks, false), (masks, true)]

private theorem mem_sortedMasks (masks : List Nat) (lower : Nat)
    (hsorted : masks.Pairwise (· ≤ ·)) (hbound : ∀ mask ∈ masks, lower ≤ mask ∧ mask < 8) :
    masks ∈ sortedMasks masks.length lower := by
  induction masks generalizing lower with
  | nil => simp [sortedMasks]
  | cons mask rest ih =>
    obtain ⟨hmin, hmax⟩ := hbound mask (by simp)
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    have hrest : rest ∈ sortedMasks rest.length mask := ih mask htail fun row hrow =>
      ⟨hhead row hrow, (hbound row (List.mem_cons_of_mem _ hrow)).2⟩
    change mask :: rest ∈ ((List.range 8).filter fun m => decide (lower ≤ m)).flatMap _
    exact List.mem_flatMap.mpr ⟨mask, by simp [hmin, hmax], List.mem_map.mpr ⟨rest, hrest, rfl⟩⟩

/-- Every sorted, admissible five-mask encoding is included in the census. -/
theorem mem_k5EarKernels {masks : List Nat} (chord : Bool) (hsize : masks.length = 5)
    (hsorted : masks.Pairwise (· ≤ ·)) (hbound : ∀ mask ∈ masks, mask < 8)
    (hadmissible : k5EarAdmissible masks = true) : (masks, chord) ∈ k5EarKernels := by
  have hm := mem_sortedMasks masks 0 hsorted (fun m hm => ⟨Nat.zero_le _, hbound m hm⟩)
  rw [hsize] at hm
  exact List.mem_flatMap.mpr ⟨masks, List.mem_filter.mpr ⟨hm, hadmissible⟩, by cases chord <;> simp⟩

/-- Sorting an admissible encoding preserves its masks up to permutation
and gives an entry of the finite census. -/
theorem sorted_k5_ear_encoding_mem (masks : List Nat) (chord : Bool)
    (hsize : masks.length = 5) (hbound : ∀ mask ∈ masks, mask < 8)
    (hadmissible : k5EarAdmissible masks = true) :
    (masks.mergeSort (fun a b => decide (a ≤ b)), chord) ∈ k5EarKernels := by
  have hperm := List.mergeSort_perm masks (fun a b => decide (a ≤ b))
  refine mem_k5EarKernels chord (hperm.length_eq.trans hsize) ?_ ?_ ?_
  · have hsorted := List.pairwise_mergeSort
      (le := fun a b : Nat => decide (a ≤ b))
      (by simp only [decide_eq_true_eq]; exact fun _ _ _ => Nat.le_trans)
      (by intro a b; rcases Nat.le_total a b with h | h <;> simp [h]) masks
    simpa only [decide_eq_true_eq] using hsorted
  · intro m hm
    exact hbound m (hperm.mem_iff.mp hm)
  · simpa only [k5EarAdmissible, hperm.countP_eq] using hadmissible

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem k5EarKernels_count : k5EarKernels.length = 1094 := by decide

#print axioms mem_k5EarKernels
#print axioms sorted_k5_ear_encoding_mem
#print axioms k5EarKernels_count

end RamseyC9
