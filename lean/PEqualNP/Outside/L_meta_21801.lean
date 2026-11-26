import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21801 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274966 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [11, 4]⟩, ⟨.not, [12]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [15, 10]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp
