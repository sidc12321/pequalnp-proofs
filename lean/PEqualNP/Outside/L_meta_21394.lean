import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21394 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112093 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [8, 0]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [3, 1]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [10, 1]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [9, 19]⟩], 20⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp
