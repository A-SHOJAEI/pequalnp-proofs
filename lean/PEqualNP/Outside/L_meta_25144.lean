import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Circuit found by search (simulated annealing / SAT); the proof checks it on every input.
theorem PEqualNP.Outside.L_meta_25144 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630322109 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : Circuit := ⟨[⟨GateOp.or, [5, 0]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [10, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.not, [13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo]
  · intro i j
    revert i j
    decide +kernel
