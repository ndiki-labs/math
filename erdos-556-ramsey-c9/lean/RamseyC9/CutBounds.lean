import RamseyC9.Statement

namespace RamseyC9

/-- The density threshold used for proper induced subgraphs in the upper-bound argument. -/
def densityBound (order : Nat) : Nat := if order = 16 then 57 else 7 * order - 56

/-- Subtract the induced remainder's edge bound from the whole graph's edge count. -/
theorem incident_edges_lower_bound (order size total kept incident : Nat)
    (hremainder : 17 ≤ order - size) (hedges : 7 * order - 55 ≤ total)
    (hkept : kept ≤ densityBound (order - size)) (hsplit : total = kept + incident) :
    7 * size + 1 ≤ incident := by
  simp [densityBound, show order - size ≠ 16 by omega] at hkept
  omega

/-- The order-16 base case lowers the incidence threshold by one. -/
theorem incident_edges_at_base (order size total kept incident : Nat)
    (hremainder : order = size + 16) (hedges : 7 * order - 55 ≤ total)
    (hkept : kept ≤ densityBound 16) (hsplit : total = kept + incident) :
    7 * size ≤ incident := by
  simp [densityBound] at hkept
  omega

/-- The forced cuts around the three clique sizes considered in the upper bound. -/
theorem clique_cut_lower_bounds (size internal cut : Nat)
    (hincidence : 7 * size + 1 ≤ internal + cut) :
    (size = 3 → internal = 3 → 19 ≤ cut) ∧
    (size = 4 → internal = 6 → 23 ≤ cut) ∧
    (size = 5 → internal = 10 → 26 ≤ cut) := by
  exact ⟨fun hs hi => by omega, fun hs hi => by omega, fun hs hi => by omega⟩

/-- Seven vertices per disjoint neighbourhood suffice for the count in the last ear case. -/
theorem high_attachment_count (outside regions : Nat)
    (houtside : outside ≤ 25) (hdisjoint : 7 * regions ≤ outside) : regions ≤ 3 := by
  omega

#print axioms incident_edges_lower_bound
#print axioms incident_edges_at_base
#print axioms clique_cut_lower_bounds
#print axioms high_attachment_count

end RamseyC9
