import RamseyC9.ColourGraphs

namespace RamseyC9

/-- A simple path of a specified length between labelled vertices. -/
structure Graph.SimplePath (G : Graph n) (length : Nat) (start finish : Fin n) where
  vertex : Fin (length + 1) → Fin n
  injective : Function.Injective vertex
  first : vertex ⟨0, Nat.succ_pos length⟩ = start
  last : vertex (Fin.last length) = finish
  consecutive (i : Fin length) : G.Adj (vertex i.castSucc) (vertex i.succ)

def Graph.SimplePath.liftInduced {G : Graph n} (vertices : Fin m → Fin n)
    (hinj : Function.Injective vertices) {a b : Fin m}
    (path : (G.induced vertices).SimplePath length a b) :
    G.SimplePath length (vertices a) (vertices b) where
  vertex := vertices ∘ path.vertex
  injective := fun _ _ heq => path.injective (hinj heq)
  first := congrArg vertices path.first
  last := congrArg vertices path.last
  consecutive := path.consecutive

/-- A graph on at least three vertices is 2-connected if deleting any
one vertex leaves a path between any two of the remaining vertices. -/
def Graph.IsTwoConnected (G : Graph n) : Prop :=
  3 ≤ n ∧ ∀ removed a b, a ≠ removed → b ≠ removed →
    ∃ (length : Nat) (path : G.SimplePath length a b), ∀ i, path.vertex i ≠ removed

/-- Between distinct vertices of a clique, every positive path length below
the clique order is attained using only clique vertices. -/
theorem Graph.clique_paths {G : Graph n} (clique : Fin m → Fin n)
    (hinj : Function.Injective clique) (hedge : ∀ u v, u ≠ v → G.Adj (clique u) (clique v))
    (a b : Fin m) (hne : a ≠ b) (hpositive : 0 < length) (hsmall : length < m) :
    ∃ path : G.SimplePath length (clique a) (clique b),
      ∀ i, ∃ j, path.vertex i = clique j := by
  let pool := (List.finRange m).filter fun x => decide (x ≠ a ∧ x ≠ b)
  have hpool {x} (hx : x ∈ pool) : x ≠ a ∧ x ≠ b :=
    of_decide_eq_true (List.mem_filter.mp hx).2
  have hpoolSize : m ≤ pool.length + 2 := by
    have hsubset : List.finRange m ⊆ a :: b :: pool := by
      intro x hx
      by_cases ha : x = a
      · simp [ha]
      by_cases hb : x = b
      · simp [hb]
      · simp [pool, ha, hb, hx]
    simpa using (List.nodup_finRange m).length_le_of_subset hsubset
  let mid := pool.take (length - 1)
  have hmidSize : mid.length = length - 1 := by
    rw [show mid = pool.take (length - 1) from rfl, List.length_take]
    exact Nat.min_eq_left (by omega)
  let indices := a :: (mid ++ [b])
  have hsize : indices.length = length + 1 := by
    simp only [indices, List.length_cons, List.length_append, hmidSize, List.length_nil]
    omega
  have hnodup : indices.Nodup := by
    have hmidNodup : mid.Nodup :=
      (List.Pairwise.filter _ (List.nodup_finRange m)).take
    refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hmidNodup, by simp, ?_⟩⟩
    · intro ha
      rcases List.mem_append.mp ha with h | h
      · exact (hpool (List.mem_of_mem_take h)).1 rfl
      · exact hne (by simpa using h)
    · intro x hx y hy
      have hy' : y = b := by simpa using hy
      exact hy' ▸ (hpool (List.mem_of_mem_take hx)).2
  let label (i : Fin (length + 1)) := indices[i.val]'(by rw [hsize]; exact i.isLt)
  have hlabel : Function.Injective label := fun i j heq =>
    Fin.ext (hnodup.eq_of_getElem_eq _ _ heq)
  have hstart : label ⟨0, Nat.succ_pos length⟩ = a := rfl
  have hfinish : label (Fin.last length) = b := by
    have hl : length = mid.length + 1 := by omega
    have hindex : (Fin.last length).val = mid.length + 1 := hl
    simp only [label, hindex, indices, List.getElem_cons_succ]
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp
  let path : G.SimplePath length (clique a) (clique b) :=
    { vertex := clique ∘ label
      injective := fun _ _ heq => hlabel (hinj heq)
      first := congrArg clique hstart
      last := congrArg clique hfinish
      consecutive := fun i => hedge _ _ (fun h => by
        have heq := congrArg Fin.val (hlabel h)
        simp at heq) }
  exact ⟨path, fun i => ⟨label i, rfl⟩⟩

/-- Join two simple paths going in opposite directions between the same endpoints.
The paths with their respective final vertices omitted must be disjoint. -/
theorem Graph.containsC9_of_two_paths {G : Graph n} {a b : Fin n} {d e : Nat}
    (left : G.SimplePath d a b) (right : G.SimplePath e b a)
    (hd : 0 < d) (he : 0 < e) (hlength : d + e = 9)
    (hdisjoint : ∀ i j, i.val < d → j.val < e → left.vertex i ≠ right.vertex j) :
    G.ContainsC9 := by
  let cycle (i : Fin 9) : Fin n :=
    if hi : i.val < d then left.vertex ⟨i.val, by omega⟩
    else right.vertex ⟨i.val - d, by omega⟩
  have leftPart (i : Fin 9) (hi : i.val < d) :
      cycle i = left.vertex ⟨i.val, by omega⟩ := dite_eq_left hi
  have rightPart (i : Fin 9) (hi : d ≤ i.val) :
      cycle i = right.vertex ⟨i.val - d, by omega⟩ := dite_eq_right (by omega)
  have first : cycle ⟨0, by decide⟩ = a :=
    (leftPart _ hd).trans left.first
  refine ⟨cycle, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val < d
    · by_cases hj : j.val < d
      · rw [leftPart i hi, leftPart j hj] at hij
        exact Fin.ext (congrArg (fun idx : Fin (d + 1) => idx.val) (left.injective hij))
      · rw [leftPart i hi, rightPart j (by omega)] at hij
        exact False.elim (hdisjoint _ _ hi (by change j.val - d < e; omega) hij)
    · by_cases hj : j.val < d
      · rw [rightPart i (by omega), leftPart j hj] at hij
        exact False.elim (hdisjoint _ _ hj (by change i.val - d < e; omega) hij.symm)
      · rw [rightPart i (by omega), rightPart j (by omega)] at hij
        have heq := congrArg Fin.val (right.injective hij)
        apply Fin.ext
        change i.val - d = j.val - d at heq
        omega
  · intro i
    by_cases hclose : i.val + 1 = 9
    · have hnext : next i = ⟨0, by decide⟩ :=
        Fin.ext (by simp [next, hclose])
      have hi : d ≤ i.val := by omega
      rw [hnext, first, rightPart i hi]
      let idx : Fin e := ⟨i.val - d, by omega⟩
      have hlast : idx.succ = Fin.last e := Fin.ext (by
        change i.val - d + 1 = e
        omega)
      have hstep := right.consecutive idx
      rw [hlast, right.last] at hstep
      exact hstep
    · have hnext : (next i).val = i.val + 1 := by
        exact Nat.mod_eq_of_lt (by omega)
      by_cases hi : i.val < d
      · let idx : Fin d := ⟨i.val, hi⟩
        rw [leftPart i hi]
        by_cases hborder : i.val + 1 = d
        · rw [rightPart (next i) (by omega)]
          have hr : (⟨(next i).val - d, by omega⟩ : Fin (e + 1)) = ⟨0, Nat.succ_pos e⟩ :=
            Fin.ext (by simp [hnext, hborder])
          rw [hr, right.first]
          have hl : idx.succ = Fin.last d := Fin.ext hborder
          have hstep := left.consecutive idx
          rw [hl, left.last] at hstep
          exact hstep
        · rw [leftPart (next i) (by omega)]
          have hl : (⟨(next i).val, by omega⟩ : Fin (d + 1)) = idx.succ := Fin.ext hnext
          rw [hl]
          exact left.consecutive idx
      · let idx : Fin e := ⟨i.val - d, by omega⟩
        rw [rightPart i (by omega), rightPart (next i) (by omega)]
        have hr : (⟨(next i).val - d, by omega⟩ : Fin (e + 1)) = idx.succ := Fin.ext (by
          change (next i).val - d = i.val - d + 1
          omega)
        rw [hr]
        exact right.consecutive idx

/-- A vertex outside a seven-edge path cannot attach to both endpoints of
the path in a graph with no 9-cycle. This is the single-profile exclusion
used by the finite clique checkers. -/
theorem Graph.containsC9_of_seven_path {G : Graph n} {a b : Fin n}
    (path : G.SimplePath 7 a b) (outside : Fin n)
    (hfresh : ∀ i, path.vertex i ≠ outside)
    (hstart : G.Adj outside a) (hfinish : G.Adj b outside) : G.ContainsC9 := by
  let cycle (i : Fin 9) : Fin n :=
    if hi : i.val < 8 then path.vertex ⟨i.val, hi⟩ else outside
  have inside (i : Fin 9) (hi : i.val < 8) : cycle i = path.vertex ⟨i.val, hi⟩ := dite_eq_left hi
  have external (i : Fin 9) (hi : ¬ i.val < 8) : cycle i = outside := dite_eq_right hi
  refine ⟨cycle, ?_, ?_⟩
  · intro i j heq
    by_cases hi : i.val < 8
    · by_cases hj : j.val < 8
      · rw [inside i hi, inside j hj] at heq
        exact Fin.ext (congrArg (fun idx : Fin 8 => idx.val) (path.injective heq))
      · rw [inside i hi, external j hj] at heq
        exact False.elim (hfresh _ heq)
    · by_cases hj : j.val < 8
      · rw [external i hi, inside j hj] at heq
        exact False.elim (hfresh _ heq.symm)
      · exact Fin.ext (by omega)
  · intro i
    by_cases hi : i.val < 7
    · have hnext : (next i).val = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      let idx : Fin 7 := ⟨i.val, hi⟩
      rw [inside i (by omega), inside (next i) (by omega)]
      have heq : (⟨(next i).val, by omega⟩ : Fin 8) = idx.succ := Fin.ext hnext
      rw [heq]
      exact path.consecutive idx
    · by_cases heq : i.val = 7
      · have hi' : i = ⟨7, by decide⟩ := Fin.ext heq
        subst i
        change G.Adj (path.vertex (Fin.last 7)) outside
        rwa [path.last]
      · have hi' : i = ⟨8, by decide⟩ := Fin.ext (by change i.val = 8; omega)
        subst i
        change G.Adj outside (path.vertex ⟨0, by decide⟩)
        rwa [path.first]

/-- An outside attachment profile cannot contain both ends of a simple
seven-edge path in the induced core. -/
theorem Graph.not_both_attachments {G : Graph n} (havoid : ¬ G.ContainsC9)
    (core : Fin m → Fin n) (hinj : Function.Injective core) {a b : Fin m}
    (path : (G.induced core).SimplePath 7 a b) (outside : Fin n)
    (hfresh : ∀ i, core i ≠ outside) :
    ¬ (G.Adj outside (core a) ∧ G.Adj outside (core b)) := by
  rintro ⟨hstart, hfinish⟩
  exact havoid (G.containsC9_of_seven_path (path.liftInduced core hinj) outside
    (fun i => hfresh (path.vertex i)) hstart (G.symmetric hfinish))

/-- An ear of length (d) on a clique closes to a 9-cycle whenever the
complementary length (9-d) is positive and smaller than the clique order. -/
theorem Graph.containsC9_of_clique_ear {G : Graph n} (clique : Fin m → Fin n)
    (hinj : Function.Injective clique) (hedge : ∀ u v, u ≠ v → G.Adj (clique u) (clique v))
    {a b : Fin m} (hne : a ≠ b) {d : Nat} (hpositive : 0 < d)
    (hbelow : d < 9) (hlarge : 9 - d < m)
    (ear : G.SimplePath d (clique a) (clique b))
    (hfresh : ∀ i, 0 < i.val → i.val < d → ∀ j, ear.vertex i ≠ clique j) :
    G.ContainsC9 := by
  obtain ⟨inner, hinner⟩ := G.clique_paths clique hinj hedge b a hne.symm (by omega) hlarge
  refine G.containsC9_of_two_paths ear inner hpositive (by omega) (by omega) ?_
  intro i j hi hj heq
  rcases Nat.eq_zero_or_pos i.val with hzero | hipos
  · have hi0 : i = ⟨0, Nat.succ_pos d⟩ := Fin.ext hzero
    rw [hi0, ear.first] at heq
    have hjLast := congrArg Fin.val (inner.injective (inner.last.trans heq))
    simp at hjLast
    omega
  · obtain ⟨k, hk⟩ := hinner j
    exact hfresh i hipos hi k (heq.trans hk)

#print axioms Graph.containsC9_of_clique_ear
#print axioms Graph.containsC9_of_two_paths
#print axioms Graph.containsC9_of_seven_path
#print axioms Graph.not_both_attachments

end RamseyC9
