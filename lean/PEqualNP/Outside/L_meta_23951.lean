import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23951_aux
open PEqualNP.CircuitLowerBounds

private def witnessCircuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [2, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [6, 11]⟩], 12⟩

private theorem fanIn : PEqualNP.MetaComplexity.FanInTwo witnessCircuit := by
  intro g hg
  simp only [witnessCircuit, List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23951_aux

open PEqualNP.Outside.L_meta_23951_aux in
theorem PEqualNP.Outside.L_meta_23951 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4958 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨witnessCircuit,fanIn,by decide,?_⟩
  decide +kernel
