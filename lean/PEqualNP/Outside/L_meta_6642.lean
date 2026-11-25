import PEqualNP.Defs
import Mathlib.Data.Set.Card

namespace PEqualNP.Outside.L_meta_6642

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma length_foldl_evalStep (gs : List Gate) (w : List Bool) :
    (gs.foldl evalStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, evalStep, List.length_cons]
    rw [ih]
    simp
    omega

def fixGate (bound : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.or, [] => ⟨GateOp.and, [bound]⟩
  | _, _ => g

def fixCircuit (n : ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.map (fixGate (n + C.gates.length))
    output := C.output }

lemma fixGate_and_single (bound w : ℕ) :
    fixGate bound ⟨GateOp.and, [w]⟩ = ⟨GateOp.and, [w]⟩ := rfl

lemma fixGate_op_or_eq (bound : ℕ) (g : Gate) (hor : (fixGate bound g).op = GateOp.or) :
    fixGate bound g = g ∧ g.op = GateOp.or ∧ g.inputs ≠ [] := by
  cases g with
  | mk op inp =>
    cases op <;> cases inp <;> simp [fixGate] at hor ⊢

lemma evalStep_fixGate (bound : ℕ) (g : Gate) (w : List Bool) (hb : w.length < bound) :
    evalStep w (fixGate bound g) = evalStep w g := by
  unfold fixGate
  cases hop : g.op <;> cases hinp : g.inputs
  all_goals simp only
  unfold evalStep
  rw [hop, hinp]
  have hnone : w.getD bound false = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, List.any_nil, hnone]

lemma foldl_evalStep_map_fixGate (bound : ℕ) (gs : List Gate) (w : List Bool)
    (hb : w.length + gs.length ≤ bound) :
    (gs.map (fixGate bound)).foldl evalStep w = gs.foldl evalStep w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hlt : w.length < bound := by simp at hb; omega
    rw [evalStep_fixGate bound g w hlt]
    apply ih (evalStep w g)
    simp only [evalStep, List.length_append, List.length_singleton]
    simp at hb
    omega

lemma list_map_set {α : Type} (f : α → α) (l : List α) (k : ℕ) (a : α) :
    (l.set k a).map f = (l.map f).set k (f a) := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simp [ih k]

lemma fixCircuit_wires_eq (n : ℕ) (C : Circuit) (inp : List Bool) (hinp : inp.length = n) :
    (fixCircuit n C).wires inp = C.wires inp := by
  unfold fixCircuit Circuit.wires
  exact foldl_evalStep_map_fixGate (n + C.gates.length) C.gates inp (by omega)

lemma fixCircuit_take_wires_eq (n : ℕ) (C : Circuit) (k : ℕ) (inp : List Bool) (hinp : inp.length = n) :
    ({ gates := List.take k (fixCircuit n C).gates, output := (fixCircuit n C).output : Circuit }).wires inp =
      ({ gates := List.take k C.gates, output := C.output : Circuit }).wires inp := by
  unfold fixCircuit Circuit.wires
  change (List.take k (C.gates.map (fixGate (n + C.gates.length)))).foldl evalStep inp =
    (List.take k C.gates).foldl evalStep inp
  rw [← List.map_take]
  apply foldl_evalStep_map_fixGate (n + C.gates.length) (List.take k C.gates) inp
  simp only [List.length_take]
  omega

lemma fixCircuit_set_eval_eq (n : ℕ) (C : Circuit) (k w : ℕ) (inp : List Bool) (hinp : inp.length = n) :
    ({ gates := (fixCircuit n C).gates.set k ⟨GateOp.and, [w]⟩, output := (fixCircuit n C).output : Circuit }).eval inp =
      ({ gates := C.gates.set k ⟨GateOp.and, [w]⟩, output := C.output : Circuit }).eval inp := by
  unfold fixCircuit Circuit.eval Circuit.wires
  simp only
  have hset : (C.gates.map (fixGate (n + C.gates.length))).set k ⟨GateOp.and, [w]⟩ =
      (C.gates.set k ⟨GateOp.and, [w]⟩).map (fixGate (n + C.gates.length)) := by
    rw [list_map_set, fixGate_and_single]
  rw [hset]
  change (((C.gates.set k ⟨GateOp.and, [w]⟩).map (fixGate (n + C.gates.length))).foldl evalStep inp).getD C.output false =
    ((C.gates.set k ⟨GateOp.and, [w]⟩).foldl evalStep inp).getD C.output false
  rw [foldl_evalStep_map_fixGate (n + C.gates.length) (C.gates.set k ⟨GateOp.and, [w]⟩) inp (by simp; omega)]

lemma getD_true_lt {l : List Bool} {i : ℕ} (h : l.getD i false = true) : i < l.length := by
  by_contra hge
  have hnone : l.getD i false = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hge)]
    rfl
  rw [hnone] at h
  cases h

lemma main_proof :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => {x2 : Fin x1.gates.length | (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard;
    have x2 : (x2 : ℕ) → (Fin x2 → Fin x2 → Prop) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : PEqualNP.CircuitLowerBounds.Circuit) =>
      ∀ (x5 : Fin x4.gates.length),
        (x4.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          ∀ x7 ∈ (x4.gates.get x5).inputs,
            ∃ (x9 : Fin x2) (x10 : Fin x2),
              x3 x9 x10 ∧
                have x11 : List Bool := List.ofFn fun (x11 : Fin x2) => Decidable.decide (x11 = x9 ∨ x11 = x10);
                { gates := x4.gates.set ↑x5 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x11 = Bool.false ∧
                  have x12 : List Bool := { gates := List.take (↑x5) x4.gates, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit }.wires x11;
                  x12.getD x7 Bool.false = Bool.false ∧ ∃ x13 ∈ (x4.gates.get x5).inputs, x12.getD x13 Bool.false = Bool.true;
    have x3 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit) =>
      ∀ (x5 : Fin x4.gates.length), (x4.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ∃ (x7 : ℕ) (x8 : ℕ), (x4.gates.get x5).inputs = [x7, x8] ∧ x7 ≠ x8 ∧ x7 < x3 + ↑x5 ∧ x8 < x3 + ↑x5;
    ∀ (x4 : ℕ) (x5 : Fin x4 → Fin x4 → Prop) (x6 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x6 →
      x2 x4 x5 x6 →
      ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x9 ∧
        x1 x9 ≤ x1 x6 ∧
        x2 x4 x5 x9 ∧
        x3 x4 x9 ∧
        ∀ (x10 : Fin x4 → Bool), x9.eval (List.ofFn x10) = x6.eval (List.ofFn x10) := by
  intro x1 x2 x3 n E C hMono hx2
  set C' := fixCircuit n C
  have hlen : C'.gates.length = C.gates.length := by simp [C', fixCircuit]
  have hMono' : Monotone2 C' := by
    intro g hg
    simp only [C', fixCircuit, List.mem_map] at hg
    rcases hg with ⟨⟨op, inp⟩, hg0, rfl⟩
    have h0 := hMono ⟨op, inp⟩ hg0
    cases op <;> cases inp
    all_goals simp only [fixGate]
    all_goals first | exact h0 | exact ⟨Or.inl rfl, by simp⟩
  have hx1le : x1 C' ≤ x1 C := by
    let e : Fin C'.gates.length ≃ Fin C.gates.length := finCongr hlen
    have hsub : e '' {k : Fin C'.gates.length | (C'.gates.get k).op = GateOp.or} ⊆
        {k : Fin C.gates.length | (C.gates.get k).op = GateOp.or} := by
      rintro k ⟨k', hk', rfl⟩
      have hget : C'.gates.get k' = fixGate (n + C.gates.length) (C.gates.get (e k')) := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp only [C', fixCircuit, List.getElem_map]
        rfl
      have hk'' : (C'.gates.get k').op = GateOp.or := hk'
      rw [hget] at hk''
      exact (fixGate_op_or_eq _ _ hk'').2.1
    have h1 := Set.ncard_image_of_injective {k : Fin C'.gates.length | (C'.gates.get k).op = GateOp.or} e.injective
    change {k : Fin C'.gates.length | (C'.gates.get k).op = GateOp.or}.ncard ≤
      {k : Fin C.gates.length | (C.gates.get k).op = GateOp.or}.ncard
    rw [← h1]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hx2' : x2 n E C' := by
    intro k hk w hw
    set k0 : Fin C.gates.length := ⟨k.val, by omega⟩
    have hget : C'.gates.get k = fixGate (n + C.gates.length) (C.gates.get k0) := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp [C', fixCircuit, k0]
    rw [hget] at hk hw
    obtain ⟨hfixeq, hop0, _⟩ := fixGate_op_or_eq _ _ hk
    rw [hfixeq] at hw
    obtain ⟨u, v, huv, heval, hw0, w', hw'mem, hw'1⟩ := hx2 k0 hop0 w hw
    refine ⟨u, v, huv, ?_, ?_, ?_⟩
    · rw [fixCircuit_set_eval_eq n C k.val w _ List.length_ofFn]
      exact heval
    · rw [fixCircuit_take_wires_eq n C k.val _ List.length_ofFn]
      exact hw0
    · refine ⟨w', ?_, ?_⟩
      · rw [hget, hfixeq]
        exact hw'mem
      · rw [fixCircuit_take_wires_eq n C k.val _ List.length_ofFn]
        exact hw'1
  have hx3' : x3 n C' := by
    intro k hk
    set k0 : Fin C.gates.length := ⟨k.val, by omega⟩
    have hget : C'.gates.get k = fixGate (n + C.gates.length) (C.gates.get k0) := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp [C', fixCircuit, k0]
    have hneNil : (C'.gates.get k).inputs ≠ [] := by
      rw [hget] at hk ⊢
      obtain ⟨hfixeq, _, hne⟩ := fixGate_op_or_eq _ _ hk
      rwa [hfixeq]
    have hle2 : (C'.gates.get k).inputs.length ≤ 2 :=
      (hMono' (C'.gates.get k) (List.get_mem _ _)).2
    match hinp : (C'.gates.get k).inputs with
    | [] => exact absurd hinp hneNil
    | [a] =>
      exfalso
      obtain ⟨u, v, _huv, _heval, ha0, w', hw'mem, hw'1⟩ := hx2' k hk a (by rw [hinp]; simp)
      rw [hinp] at hw'mem
      simp only [List.mem_singleton] at hw'mem
      subst hw'mem
      rw [ha0] at hw'1
      cases hw'1
    | [a, b] =>
      obtain ⟨u1, v1, _, _, ha0, w1, hw1mem, hw1true⟩ := hx2' k hk a (by rw [hinp]; simp)
      rw [hinp] at hw1mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1mem
      have hab : a ≠ b := by
        intro heq
        subst heq
        rcases hw1mem with rfl | rfl <;> (rw [ha0] at hw1true; cases hw1true)
      have hbtrue : ({ gates := List.take k.val C'.gates, output := C'.output : Circuit }.wires
          (List.ofFn fun i : Fin n => decide (i = u1 ∨ i = v1))).getD b false = true := by
        rcases hw1mem with rfl | rfl
        · rw [ha0] at hw1true; cases hw1true
        · exact hw1true
      have hblt : b < n + k.val := by
        have hlt := getD_true_lt hbtrue
        change b < ((List.take k.val C'.gates).foldl evalStep (List.ofFn fun i : Fin n => decide (i = u1 ∨ i = v1))).length at hlt
        rw [length_foldl_evalStep, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt k.isLt)] at hlt
        exact hlt
      obtain ⟨u2, v2, _, _, hb0, w2, hw2mem, hw2true⟩ := hx2' k hk b (by rw [hinp]; simp)
      rw [hinp] at hw2mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw2mem
      have hatrue : ({ gates := List.take k.val C'.gates, output := C'.output : Circuit }.wires
          (List.ofFn fun i : Fin n => decide (i = u2 ∨ i = v2))).getD a false = true := by
        rcases hw2mem with rfl | rfl
        · exact hw2true
        · rw [hb0] at hw2true; cases hw2true
      have halt : a < n + k.val := by
        have hlt := getD_true_lt hatrue
        change a < ((List.take k.val C'.gates).foldl evalStep (List.ofFn fun i : Fin n => decide (i = u2 ∨ i = v2))).length at hlt
        rw [length_foldl_evalStep, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt k.isLt)] at hlt
        exact hlt
      exact ⟨a, b, rfl, hab, halt, hblt⟩
    | _ :: _ :: _ :: _ =>
      rw [hinp] at hle2
      simp at hle2
  refine ⟨C', hMono', hx1le, hx2', hx3', ?_⟩
  intro x
  unfold Circuit.eval
  rw [fixCircuit_wires_eq n C (List.ofFn x) List.length_ofFn]
  rfl

end PEqualNP.Outside.L_meta_6642

theorem PEqualNP.Outside.L_meta_6642 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => {x2 : Fin x1.gates.length | (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x2 : (x2 : ℕ) → (Fin x2 → Fin x2 → Prop) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x5 : Fin x4.gates.length),     (x4.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ x7 ∈ (x4.gates.get x5).inputs,         ∃ (x9 : Fin x2) (x10 : Fin x2),           x3 x9 x10 ∧             have x11 : List Bool := List.ofFn fun (x11 : Fin x2) => Decidable.decide (x11 = x9 ∨ x11 = x10);             { gates := x4.gates.set ↑x5 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x11 = Bool.false ∧               have x12 : List Bool := { gates := List.take (↑x5) x4.gates, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit }.wires x11;               x12.getD x7 Bool.false = Bool.false ∧ ∃ x13 ∈ (x4.gates.get x5).inputs, x12.getD x13 Bool.false = Bool.true; have x3 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), (x4.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ (x7 : ℕ) (x8 : ℕ), (x4.gates.get x5).inputs = [x7, x8] ∧ x7 ≠ x8 ∧ x7 < x3 + ↑x5 ∧ x8 < x3 + ↑x5; ∀ (x4 : ℕ) (x5 : Fin x4 → Fin x4 → Prop) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x2 x4 x5 x6 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x1 x9 ≤ x1 x6 ∧ x2 x4 x5 x9 ∧ x3 x4 x9 ∧ ∀ (x10 : Fin x4 → Bool), x9.eval (List.ofFn x10) = x6.eval (List.ofFn x10) := by
  exact PEqualNP.Outside.L_meta_6642.main_proof
