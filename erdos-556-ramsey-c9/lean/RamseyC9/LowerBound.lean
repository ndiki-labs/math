import RamseyC9.Statement

namespace RamseyC9

private def block (v : Fin 32) : Nat := v.val / 8
private def half (v : Fin 32) : Nat := v.val / 16

/-- Colour 0 lies inside an eight-vertex block. Colours 1 and 2 cross bipartitions. -/
def colouring32 (u v : Fin 32) : Fin 3 :=
  if block u = block v then 0 else if half u = half v then 1 else 2

theorem colouring32_symmetric (u v : Fin 32) : colouring32 u v = colouring32 v u := by
  simp only [colouring32, eq_comm (a := block u) (b := block v),
    eq_comm (a := half u) (b := half v)]

private theorem eq_at_start (f : Fin 9 → Nat) (h : ∀ i, f i = f (next i)) :
    ∀ i, f i = f 0 := by
  have walk (j : Nat) (hj : j < 9) : f ⟨j, hj⟩ = f 0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have step := h ⟨j, by omega⟩
      have hn : next ⟨j, by omega⟩ = ⟨j + 1, hj⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hj
      rw [hn] at step
      exact step.symm.trans (ih (by omega))
  intro i
  exact walk i.val i.isLt

private theorem no_alternating_cycle (f : Fin 9 → Nat) (hbit : ∀ i, f i ≤ 1)
    (h : ∀ i, f i ≠ f (next i)) : False := by
  have twoSteps (j : Nat) (hj : j + 2 < 9) :
      f ⟨j, by omega⟩ = f ⟨j + 2, hj⟩ := by
    let a : Fin 9 := ⟨j, by omega⟩
    let b : Fin 9 := ⟨j + 1, by omega⟩
    let c : Fin 9 := ⟨j + 2, hj⟩
    have hab : next a = b := Fin.ext (Nat.mod_eq_of_lt b.isLt)
    have hbc : next b = c := Fin.ext (Nat.mod_eq_of_lt c.isLt)
    have h₁ := h a
    have h₂ := h b
    rw [hab] at h₁
    rw [hbc] at h₂
    change f a = f c
    have ha := hbit a
    have hb := hbit b
    have hc := hbit c
    omega
  have h₀ : f 0 = f 2 := twoSteps 0 (by decide)
  have h₂ : f 2 = f 4 := twoSteps 2 (by decide)
  have h₄ : f 4 = f 6 := twoSteps 4 (by decide)
  have h₆ : f 6 = f 8 := twoSteps 6 (by decide)
  have h₈ : f 8 ≠ f 0 := h 8
  exact h₈ ((h₀.trans (h₂.trans (h₄.trans h₆))).symm)

private theorem no_injection_fin9_fin8 (f : Fin 9 → Fin 8)
    (hf : Function.Injective f) : False := by
  have hn : ((List.finRange 9).map f).Nodup := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange 9).imp (fun hne heq => hne (hf heq))
  have hs : (List.finRange 9).map f ⊆ List.finRange 8 := by
    intro x _
    exact List.mem_finRange x
  have h := hn.length_le_of_subset hs
  simp at h

/-- The explicit four-block colouring has no monochromatic cycle of length nine. -/
theorem colouring32_avoids_c9 : ¬ MonochromaticC9 colouring32 := by
  rintro ⟨v, hv, c, hc⟩
  by_cases h₀ : c = 0
  · have edges : ∀ i, block (v i) = block (v (next i)) := by
      intro i
      have h := hc i
      rw [h₀] at h
      by_cases heq : block (v i) = block (v (next i))
      · exact heq
      · simp only [colouring32, ite_eq_right heq] at h
        split at h <;> contradiction
    have sameBlock := eq_at_start (fun i => block (v i)) edges
    let offset (i : Fin 9) : Fin 8 := ⟨(v i).val % 8, Nat.mod_lt _ (by decide)⟩
    apply no_injection_fin9_fin8 offset
    intro i j h
    apply hv
    apply Fin.ext
    have heq := congrArg Fin.val h
    have hblock := (sameBlock i).trans (sameBlock j).symm
    change (v i).val % 8 = (v j).val % 8 at heq
    change (v i).val / 8 = (v j).val / 8 at hblock
    omega
  · by_cases h₁ : c = 1
    · apply no_alternating_cycle (fun i => block (v i) % 2)
      · intro i
        omega
      · intro i
        have h := hc i
        rw [h₁] at h
        unfold colouring32 at h
        split at h
        · contradiction
        · rename_i differentBlocks
          split at h
          · rename_i sameHalf
            unfold block at differentBlocks
            unfold half at sameHalf
            change (v i).val / 8 % 2 ≠ (v (next i)).val / 8 % 2
            omega
          · contradiction
    · have h₂ : c = 2 := by
        apply Fin.ext
        have hc₀ : c.val ≠ 0 := fun eq => h₀ (Fin.ext eq)
        have hc₁ : c.val ≠ 1 := fun eq => h₁ (Fin.ext eq)
        have hlt := c.isLt
        change c.val = 2
        omega
      apply no_alternating_cycle (fun i => half (v i))
      · intro i
        have hi := (v i).isLt
        change (v i).val / 16 ≤ 1
        omega
      · intro i
        have h := hc i
        rw [h₂] at h
        unfold colouring32 at h
        split at h
        · contradiction
        · split at h
          · contradiction
          · assumption

/-- Every order at most 32 admits a three-colouring without a monochromatic C₉. -/
theorem no_ramsey_through_32 (n : Nat) (hn : n ≤ 32) : ¬ HasRamseyProperty n := by
  intro allColourings
  let embed (v : Fin n) : Fin 32 := ⟨v.val, Nat.lt_of_lt_of_le v.isLt hn⟩
  obtain ⟨v, hv, c, hc⟩ := allColourings (fun x y => colouring32 (embed x) (embed y))
    (fun x y => colouring32_symmetric (embed x) (embed y))
  apply colouring32_avoids_c9
  refine ⟨embed ∘ v, ?_, c, hc⟩
  intro i j h
  exact hv (Fin.ext (congrArg (fun x : Fin 32 => x.val) h))

/-- The remaining upper bound suffices to identify the exact Ramsey number. -/
theorem ramsey_number_iff_upper_bound : IsRamseyNumber 33 ↔ HasRamseyProperty 33 :=
  ⟨And.left, fun h => ⟨h, fun n hn => no_ramsey_through_32 n (by omega)⟩⟩

#print axioms colouring32_avoids_c9
#print axioms no_ramsey_through_32
#print axioms ramsey_number_iff_upper_bound

end RamseyC9
