import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Circuit found by search (simulated annealing / SAT); the proof checks it on every input.
theorem PEqualNP.Outside.L_meta_20847 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (18092097 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  let C : Circuit := ⟨[⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [11, 14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.or, [16, 18]⟩], 19⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
