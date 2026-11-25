import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.Represents

-- The live-set search, its completeness proof and the circuit compilation are adapted from
-- lean/PEqualNP/Outside/L_meta_8299.lean in this repository (itself adapted from
-- lean/PEqualNP/Outside/L_meta_6345.lean), here with 96 (true entry, false entry) pairs of
-- rows 0 to 3. The row-4 argument, the search on natural numbers, its cutting into pieces
-- and the conclusion are new.

namespace PEqualNP.Outside.L_meta_10133

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 192

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 96 := ((x >>> 96) &&& ~~~x).setWidth 96

def cuts (ws : List W) : BitVec 96 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 96) ++ (0 : BitVec 96)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xffff070707070707070707070707, 0xffff0000383838383838383838383838, 0xffffffff00000000404040404040404040404040, 0xffffffff0000000000000000808080808080808080808080, 0x0, 0xff000000ff00ff0000010101010101010101010101, 0xff000000ff00000000ff080808080808080808080808, 0xff000000ff00000000ff00101010101010101010101010, 0xff000000c2c2c2c2c2c2c2c2c2c2c2c2, 0xff000000ff00000000000000242424242424242424242424]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 96) (w : W) : Prop :=
  w.getLsbD (96 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 96) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (96 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (96 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 96, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 96) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 192 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 96)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 192 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 192) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 192) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 192, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 192 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 192 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 192 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 192 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 192) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 192 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 5 → Fin 5 → Bool := fun u v => (24894758 : ℕ).testBit (5 * u.val + v.val)

def posL : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 2), (1, 0), (1, 3), (2, 0), (2, 1), (2, 2), (2, 4), (3, 0), (3, 1), (3, 2), (3, 4)]

def negL : List (Fin 5 × Fin 5) :=
  [(0, 0), (0, 3), (0, 4), (1, 1), (1, 2), (1, 4), (2, 3), (3, 3)]

def samp (k : Fin 192) : Fin 5 × Fin 5 :=
  if k.val < 96 then negL.getD (k.val % 8) (0, 0) else posL.getD ((k.val - 96) / 8) (0, 0)

theorem input_rows : ∀ k : Fin 192,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 192, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 192) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

-- Row 4 repeats rows 2 and 3, so the search above samples rows 0 to 3 only, where the
-- input of row 4 is always off. Every circuit representing `A` reads that input in some
-- gate, and such a gate repeats a wire already there on the sampled rows, so one gate of
-- the circuit is not needed by the search. Wire semantics and monotonicity are from
-- lean/PEqualNP/Outside/L_meta_1500.lean (there credited to sanchan, L-meta-667);
-- `wiresFrom_indep`, `reads_four`, `waste_gate` and `compile_waste` are new.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

lemma wiresFrom_indep (gs : List Gate) (t : ℕ) (ht : ∀ g ∈ gs, t ∉ g.inputs) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, i ≠ t → w₁.getD i false = w₂.getD i false) →
      ∀ i, i ≠ t → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ h i hi
    exact h i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen h i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1, hstep2]
    apply ih (fun g' hg' => ht g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    have hval : g.op.eval (g.inputs.map fun k => w₁.getD k false) =
        g.op.eval (g.inputs.map fun k => w₂.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact h k (fun e => ht g List.mem_cons_self (e ▸ hk))
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
      exact h j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq, hlen, getD_snoc_eq]
        exact hval
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem reads_four (C : Circuit) (hm : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    ∃ g ∈ C.gates, 4 ∈ g.inputs := by
  by_contra hno
  push_neg at hno
  have e40 := hr 4 0
  have e00 := hr 0 0
  have e43 := hr 4 3
  have l40 : PEqualNP.Represents.oneEach (4 : Fin 5) (0 : Fin 5) =
      [false, false, false, false, true, true, false, false, false, false] := by decide
  have l00 : PEqualNP.Represents.oneEach (0 : Fin 5) (0 : Fin 5) =
      [true, false, false, false, false, true, false, false, false, false] := by decide
  have l43 : PEqualNP.Represents.oneEach (4 : Fin 5) (3 : Fin 5) =
      [false, false, false, false, true, false, false, false, true, false] := by decide
  have a40 : A 4 0 = true := by decide
  have a00 : A 0 0 = false := by decide
  have a43 : A 4 3 = false := by decide
  rw [l40, a40] at e40
  rw [l00, a00] at e00
  rw [l43, a43] at e43
  change (wiresFrom C.gates _).getD C.output false = _ at e40 e00 e43
  by_cases ho : C.output = 4
  · rw [ho, getD_wiresFrom_lt _ _ _ (by simp)] at e43
    exact Bool.noConfusion e43
  · have hind := wiresFrom_indep C.gates 4 hno
      [false, false, false, false, true, true, false, false, false, false]
      [false, false, false, false, false, true, false, false, false, false] rfl (by
        intro i hi
        rcases Nat.lt_or_ge i 10 with h | h
        · interval_cases i <;> simp_all
        · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ (by simpa using h)])
      C.output ho
    have hmono := wiresFrom_mono C.gates (fun g hg => (hm g hg).1)
      [false, false, false, false, false, true, false, false, false, false]
      [true, false, false, false, false, true, false, false, false, false] rfl (by
        intro i hi
        rcases Nat.lt_or_ge i 10 with h | h
        · interval_cases i <;> simp_all
        · rw [List.getD_eq_default _ _ (by simpa using h)] at hi
          exact Bool.noConfusion hi)
      C.output
    rw [hind] at e40
    have := hmono e40
    rw [e00] at this
    exact Bool.noConfusion this

private theorem waste_gate (w : List W) (g : Gate) (hg : legal g) (t : ℕ)
    (ht : w.getD t 0 = 0) (hin : t ∈ g.inputs) :
    ∃ z, (z = 0 ∨ ∃ j, z = w.getD j 0) ∧
      ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil => simp at hin
  | cons i tail =>
    cases tail with
    | nil =>
      refine ⟨w.getD i 0, .inr ⟨i, rfl⟩, ?_⟩
      rcases hop with rfl | rfl
      · intro k
        simp only [step, List.map_cons, List.map_nil, read_bit]
        simp [GateOp.eval]
      · intro k
        simp only [step, List.map_cons, List.map_nil, read_bit]
        simp [GateOp.eval]
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        have hij : t = i ∨ t = j := by simpa using hin
        rcases hop with rfl | rfl
        · refine ⟨w.getD i 0 &&& w.getD j 0, .inl ?_, ?_⟩
          · rcases hij with rfl | rfl
            · rw [ht]
              simp
            · rw [ht]
              simp
          · intro k
            simp only [step, List.map_cons, List.map_nil, read_bit]
            simp [GateOp.eval, bit]
        · rcases hij with rfl | rfl
          · refine ⟨w.getD j 0, .inr ⟨j, rfl⟩, ?_⟩
            intro k
            simp only [step, List.map_cons, List.map_nil, read_bit]
            rw [ht]
            simp [GateOp.eval, bit]
          · refine ⟨w.getD i 0, .inr ⟨i, rfl⟩, ?_⟩
            intro k
            simp only [step, List.map_cons, List.map_nil, read_bit]
            rw [ht]
            simp [GateOp.eval, bit]

private theorem compile_waste (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w) (t : ℕ) (htl : t < w.length)
    (ht : w.getD t 0 = 0) (hread : ∃ g ∈ gs, t ∈ g.inputs)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal (gs.length - 1) av := by
  induction gs generalizing w av with
  | nil =>
    obtain ⟨g, hg', _⟩ := hread
    simp at hg'
  | cons g gs ih =>
    have he' (z : W) (hstep : ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k)) :
        ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k
      simpa only [List.foldl_cons, hstep] using he k
    have appendOK {z : W} (h : z = 0 ∨ z = BitVec.allOnes 192 ∨ z ∈ av) :
        represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    by_cases hg0 : t ∈ g.inputs
    · obtain ⟨z, hz, hstep⟩ := waste_gate w g (hg g (by simp)) t ht hg0
      have hrep : z = 0 ∨ z = BitVec.allOnes 192 ∨ z ∈ av := by
        rcases hz with rfl | ⟨j, rfl⟩
        · exact .inl rfl
        · rcases read_wire w j with h | h
          · exact .inl h
          · exact hw _ h
      have hb := compile gs out (fun g' h => hg g' (by simp [h])) (w ++ [z]) av (appendOK hrep)
        (he' z hstep)
      simpa using hb
    · have hread' : ∃ g' ∈ gs, t ∈ g'.inputs := by
        obtain ⟨g', hg', ht'⟩ := hread
        rcases List.mem_cons.mp hg' with rfl | h
        · exact absurd ht' hg0
        · exact ⟨g', h, ht'⟩
      have hpos : 1 ≤ gs.length := by
        obtain ⟨g', hg', _⟩ := hread'
        exact List.length_pos_of_mem hg'
      obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
      have htl' : t < (w ++ [z]).length := by simp; omega
      have ht' : (w ++ [z]).getD t 0 = 0 := by rw [List.getD_append _ _ _ _ htl]; exact ht
      have fn (av' : Finset W) (hw' : represents av' (w ++ [z])) :
          build basicOps goal (gs.length - 1) av' :=
        ih (fun g' h => hg g' (by simp [h])) (w ++ [z]) av' hw' htl' ht' hread' (he' z hstep)
      have hlen : (g :: gs).length - 1 = (gs.length - 1) + 1 := by simp; omega
      rw [hlen]
      rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
      · exact Or.inl (fn av (appendOK (.inl h)))
      · exact Or.inl (fn av (appendOK (.inr (.inl h))))
      · exact Or.inl (fn av (appendOK (.inr (.inr h))))
      · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_⟩
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
        · simp_all

theorem get_build9 (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal (C.gates.length - 1) inputs.toFinset :=
  compile_waste C.gates C.output hg rawInputs inputs.toFinset initial_rep 4 (by decide)
    (by decide +kernel) (reads_four C hg hr) (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih


-- The same search on natural numbers: the kernel runs `Nat` bit operations much faster than
-- the `BitVec` ones. `opt_eq` says the two searches agree.
def MF : ℕ := 79228162514264337593543950335

def sepN (x : ℕ) : ℕ := ((x >>> 96) &&& (2 ^ 192 - 1 - x)) % 2 ^ 96

def cutsN (ws : List ℕ) : ℕ := ws.foldr (fun w v => sepN w ||| v) 0

def opsN (x y : ℕ) : List ℕ := [x &&& y, x ||| y]

def goalN : ℕ := 0xffffffffffffffffffffffff000000000000000000000000

def dispatchN (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) : Bool :=
  let base := cutsN r
  (opsN a b).any fun w =>
    let v := sepN w ||| base
    ((v == MF) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepN a == MF) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sepN b == MF) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepN a ||| sepN b == MF) && next (extra - 2) (w :: a :: b :: r))

def optN : ℕ → ℕ → List ℕ → Bool
  | 0, _, ws => ws == [goalN]
  | k + 1, extra, ws => ws == [goalN] ||
    (pairs ws).any (fun (a, b, r) => dispatchN extra (optN k) a b r)

theorem toNat_sep (x : W) : (sep x).toNat = sepN x.toNat := by
  simp only [sep, sepN, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_not]

theorem toNat_cuts (ws : List W) : (cuts ws).toNat = cutsN (ws.map BitVec.toNat) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [cuts, cutsN, List.foldr_cons, List.map_cons, BitVec.toNat_or, toNat_sep] at ih ⊢
    rw [ih]

theorem full_toNat : (-1 : BitVec 96).toNat = MF := by decide

theorem beq_full (v : BitVec 96) : (v == -1) = (v.toNat == MF) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← full_toNat, BitVec.toNat_inj]

theorem goal_toNat : goal.toNat = goalN := by decide

theorem beq_goal (ws : List W) : (ws.map BitVec.toNat == [goalN]) = (ws == [goal]) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← goal_toNat]
  constructor
  · intro h
    have inj : Function.Injective (fun x : W => x.toNat) := fun a b e => BitVec.eq_of_toNat_eq e
    exact List.map_injective_iff.mpr inj (h.trans List.map_singleton.symm)
  · rintro rfl
    rfl

theorem singles_map {β γ : Type} (f : β → γ) (l : List β) :
    singles (l.map f) = (singles l).map (fun p => (f p.1, p.2.map f)) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, singles, ih, List.map_map]
    rfl

theorem pairs_map {β γ : Type} (f : β → γ) (l : List β) :
    pairs (l.map f) = (pairs l).map (fun p => (f p.1, f p.2.1, p.2.2.map f)) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, pairs, ih, singles_map, List.map_map, List.map_append]
    rfl

theorem dispatch_eq (extra k : ℕ)
    (ih : ∀ (e : ℕ) (l : List W), optN k e (l.map BitVec.toNat) = optimized k e l)
    (a b : W) (r : List W) :
    dispatchN extra (optN k) a.toNat b.toNat (r.map BitVec.toNat) =
      dispatch extra (optimized k) a b r := by
  have hops : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
    simp [opsN, ops, BitVec.toNat_and, BitVec.toNat_or]
  simp only [dispatchN, dispatch, hops, List.any_map]
  congr 1
  funext w
  simp only [Function.comp, beq_full, BitVec.toNat_or, toNat_sep, toNat_cuts]
  rw [← ih extra (w :: r), ← ih (extra - 1) (w :: a :: r), ← ih (extra - 1) (w :: b :: r),
    ← ih (extra - 2) (w :: a :: b :: r)]
  rfl

theorem opt_eq : ∀ (k e : ℕ) (ws : List W), optN k e (ws.map BitVec.toNat) = optimized k e ws
  | 0, e, ws => by simp only [optN, optimized, beq_goal]
  | k + 1, e, ws => by
    simp only [optN, optimized, beq_goal, pairs_map, List.any_map]
    congr 2
    funext p
    exact dispatch_eq e k (opt_eq k) p.1 p.2.1 p.2.2

def opt1 (g : Bool) (c : ℕ × List ℕ) : List (ℕ × List ℕ) := if g then [c] else []

theorem any_opt1 (g : Bool) (c : ℕ × List ℕ) (f : ℕ × List ℕ → Bool) :
    (opt1 g c).any f = (g && f c) := by
  cases g <;> simp [opt1]

-- The children of one gate choice, in the order `dispatchN` tries them.
def childrenN (extra : ℕ) (a b : ℕ) (r : List ℕ) : List (ℕ × List ℕ) :=
  let base := cutsN r
  (opsN a b).flatMap fun w =>
    let v := sepN w ||| base
    opt1 (v == MF) (extra, w :: r) ++
    opt1 ((extra != 0) && (v ||| sepN a == MF)) (extra - 1, w :: a :: r) ++
    opt1 ((extra != 0) && (v ||| sepN b == MF)) (extra - 1, w :: b :: r) ++
    opt1 ((extra ≥ 2) && (v ||| sepN a ||| sepN b == MF)) (extra - 2, w :: a :: b :: r)

theorem dispatch_children (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) :
    dispatchN extra next a b r = (childrenN extra a b r).any (fun c => next c.1 c.2) := by
  simp only [dispatchN, childrenN, List.any_flatMap, List.any_append, any_opt1]
  congr 1
  funext w
  simp only [Bool.and_or_distrib_left, Bool.and_assoc, Bool.or_assoc]

-- A search state: gates left, spare room, wires. The proof below cuts the search into
-- pieces small enough for the kernel, along these states.
def nstep (s : ℕ × ℕ × List ℕ) (ij : ℕ × ℕ) : ℕ × ℕ × List ℕ :=
  let p := (pairs s.2.2).getD ij.1 (0, 0, [])
  let c := (childrenN s.2.1 p.1 p.2.1 p.2.2).getD ij.2 (0, [])
  (s.1 - 1, c.1, c.2)

def Dead (s : ℕ × ℕ × List ℕ) : Prop := optN s.1 s.2.1 s.2.2 = false

def pg (s : ℕ × ℕ × List ℕ) (p : ℕ × ℕ × List ℕ) : Bool :=
  !dispatchN s.2.1 (optN (s.1 - 1)) p.1 p.2.1 p.2.2

theorem dead_of (s : ℕ × ℕ × List ℕ) (hk : 1 ≤ s.1) (hg : (s.2.2 == [goalN]) = false)
    (hall : ((pairs s.2.2).drop 0).all (pg s) = true) : Dead s := by
  unfold Dead
  obtain ⟨k, hk'⟩ : ∃ k, s.1 = k + 1 := ⟨s.1 - 1, by omega⟩
  rw [hk', optN, hg, Bool.false_or, List.any_eq_false]
  intro x hx hd
  have h := List.all_eq_true.mp hall x (by simpa using hx)
  simp only [pg, hk', Nat.add_sub_cancel] at h
  obtain ⟨a, b, r⟩ := x
  simp only [Bool.not_eq_true'] at h
  simp only [h] at hd
  exact Bool.noConfusion hd

theorem seg {α : Type} (g : α → Bool) (L : List α) (lo n : ℕ)
    (h1 : ((L.drop lo).take n).all g = true) (h2 : (L.drop (lo + n)).all g = true) :
    (L.drop lo).all g = true := by
  rw [← List.take_append_drop n (L.drop lo), List.all_append, h1, List.drop_drop, h2]
  rfl

theorem take_one {α : Type} (g : α → Bool) (L : List α) (i : ℕ) (d : α) (hi : i < L.length)
    (h : g (L.getD i d) = true) : ((L.drop i).take 1).all g = true := by
  rw [List.drop_eq_getElem_cons hi]
  have hp : L.getD i d = L[i] := by simp [List.getD_eq_getElem?_getD, hi]
  simp only [List.take_succ_cons, List.take_zero, List.all_cons, List.all_nil, Bool.and_true]
  rw [← hp]
  exact h

theorem pair_one (s : ℕ × ℕ × List ℕ) (i m : ℕ) (hi : i < (pairs s.2.2).length)
    (hm : (childrenN s.2.1 ((pairs s.2.2).getD i (0, 0, [])).1
      ((pairs s.2.2).getD i (0, 0, [])).2.1
      ((pairs s.2.2).getD i (0, 0, [])).2.2).length = m)
    (hch : ∀ j < m, Dead (nstep s (i, j))) :
    (((pairs s.2.2).drop i).take 1).all (pg s) = true := by
  apply take_one _ _ i (0, 0, []) hi
  set p := (pairs s.2.2).getD i (0, 0, []) with hp
  simp only [pg, dispatch_children, Bool.not_eq_true', List.any_eq_false]
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
  have h := hch j (hm ▸ hj)
  unfold Dead nstep at h
  simp only [← hp] at h
  have hc' : (childrenN s.2.1 p.1 p.2.1 p.2.2).getD j (0, []) =
      (childrenN s.2.1 p.1 p.2.1 p.2.2)[j] := by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [hc'] at h
  simpa using h

theorem inputs_nodup : inputs.Nodup := by decide +kernel

theorem inputs_length : inputs.length = 10 := by decide +kernel

def inputsN : List ℕ :=
  [0xffff070707070707070707070707, 0xffff0000383838383838383838383838, 0xffffffff00000000404040404040404040404040, 0xffffffff0000000000000000808080808080808080808080, 0x0, 0xff000000ff00ff0000010101010101010101010101, 0xff000000ff00000000ff080808080808080808080808, 0xff000000ff00000000ff00101010101010101010101010, 0xff000000c2c2c2c2c2c2c2c2c2c2c2c2, 0xff000000ff00000000000000242424242424242424242424]

theorem inputsN_eq : inputs.map BitVec.toNat = inputsN := by decide +kernel

def stFull : ℕ × ℕ × List ℕ := (9, 0, inputsN)

set_option maxRecDepth 100000 in
theorem rng_1 : (((pairs stFull.2.2).drop 0).take 13).all (pg stFull) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_2 : (((pairs stFull.2.2).drop 13).take 3).all (pg stFull) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_3 : (((pairs stFull.2.2).drop 16).take 2).all (pg stFull) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_4 : (((pairs stFull.2.2).drop 18).take 12).all (pg stFull) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_5 : (((pairs stFull.2.2).drop 30).take 9).all (pg stFull) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_6 : (((pairs stFull.2.2).drop 39).take 6).all (pg stFull) = true := by
  decide +kernel

theorem dead_7 : Dead stFull :=
  dead_of stFull (by decide +kernel) (by decide +kernel)
    (seg (pg stFull) (pairs stFull.2.2) 0 13 rng_1
    (seg (pg stFull) (pairs stFull.2.2) 13 3 rng_2
    (seg (pg stFull) (pairs stFull.2.2) 16 2 rng_3
    (seg (pg stFull) (pairs stFull.2.2) 18 12 rng_4
    (seg (pg stFull) (pairs stFull.2.2) 30 9 rng_5
    (seg (pg stFull) (pairs stFull.2.2) 39 6 rng_6
    (by decide +kernel)))))))

def stMain : ℕ × ℕ × List ℕ := (9, 1, [0xffff070707070707070707070707, 0xffff0000383838383838383838383838, 0xffffffff00000000404040404040404040404040, 0xffffffff0000000000000000808080808080808080808080, 0xff000000ff00ff0000010101010101010101010101, 0xff000000ff00000000ff080808080808080808080808, 0xff000000ff00000000ff00101010101010101010101010, 0xff000000c2c2c2c2c2c2c2c2c2c2c2c2, 0xff000000ff00000000000000242424242424242424242424])

set_option maxRecDepth 100000 in
theorem rng_8 : (((pairs stMain.2.2).drop 0).take 3).all (pg stMain) = true := by
  decide +kernel

def st_9 : ℕ × ℕ × List ℕ := nstep stMain (3, 0)

set_option maxRecDepth 100000 in
theorem dead_10 : Dead st_9 := by
  unfold Dead
  decide +kernel

def st_11 : ℕ × ℕ × List ℕ := nstep stMain (3, 1)

set_option maxRecDepth 100000 in
theorem dead_12 : Dead st_11 := by
  unfold Dead
  decide +kernel

def st_13 : ℕ × ℕ × List ℕ := nstep stMain (3, 2)

set_option maxRecDepth 100000 in
theorem dead_14 : Dead st_13 := by
  unfold Dead
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_15 : (((pairs stMain.2.2).drop 4).take 3).all (pg stMain) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_16 : (((pairs stMain.2.2).drop 7).take 4).all (pg stMain) = true := by
  decide +kernel

def st_17 : ℕ × ℕ × List ℕ := nstep stMain (11, 0)

set_option maxRecDepth 100000 in
theorem rng_18 : (((pairs st_17.2.2).drop 0).take 13).all (pg st_17) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_19 : (((pairs st_17.2.2).drop 13).take 15).all (pg st_17) = true := by
  decide +kernel

theorem dead_20 : Dead st_17 :=
  dead_of st_17 (by decide +kernel) (by decide +kernel)
    (seg (pg st_17) (pairs st_17.2.2) 0 13 rng_18
    (seg (pg st_17) (pairs st_17.2.2) 13 15 rng_19
    (by decide +kernel)))

def st_21 : ℕ × ℕ × List ℕ := nstep stMain (11, 1)

set_option maxRecDepth 100000 in
theorem dead_22 : Dead st_21 := by
  unfold Dead
  decide +kernel

def st_23 : ℕ × ℕ × List ℕ := nstep stMain (11, 2)

set_option maxRecDepth 100000 in
theorem dead_24 : Dead st_23 := by
  unfold Dead
  decide +kernel

def st_25 : ℕ × ℕ × List ℕ := nstep stMain (12, 0)

set_option maxRecDepth 100000 in
theorem rng_26 : (((pairs st_25.2.2).drop 0).take 13).all (pg st_25) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_27 : (((pairs st_25.2.2).drop 13).take 15).all (pg st_25) = true := by
  decide +kernel

theorem dead_28 : Dead st_25 :=
  dead_of st_25 (by decide +kernel) (by decide +kernel)
    (seg (pg st_25) (pairs st_25.2.2) 0 13 rng_26
    (seg (pg st_25) (pairs st_25.2.2) 13 15 rng_27
    (by decide +kernel)))

def st_29 : ℕ × ℕ × List ℕ := nstep stMain (12, 1)

set_option maxRecDepth 100000 in
theorem dead_30 : Dead st_29 := by
  unfold Dead
  decide +kernel

def st_31 : ℕ × ℕ × List ℕ := nstep stMain (12, 2)

set_option maxRecDepth 100000 in
theorem dead_32 : Dead st_31 := by
  unfold Dead
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_33 : (((pairs stMain.2.2).drop 13).take 1).all (pg stMain) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_34 : (((pairs stMain.2.2).drop 14).take 1).all (pg stMain) = true := by
  decide +kernel

def st_35 : ℕ × ℕ × List ℕ := nstep stMain (15, 0)

set_option maxRecDepth 100000 in
theorem rng_36 : (((pairs st_35.2.2).drop 0).take 11).all (pg st_35) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_37 : (((pairs st_35.2.2).drop 11).take 5).all (pg st_35) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_38 : (((pairs st_35.2.2).drop 16).take 6).all (pg st_35) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_39 : (((pairs st_35.2.2).drop 22).take 6).all (pg st_35) = true := by
  decide +kernel

theorem dead_40 : Dead st_35 :=
  dead_of st_35 (by decide +kernel) (by decide +kernel)
    (seg (pg st_35) (pairs st_35.2.2) 0 11 rng_36
    (seg (pg st_35) (pairs st_35.2.2) 11 5 rng_37
    (seg (pg st_35) (pairs st_35.2.2) 16 6 rng_38
    (seg (pg st_35) (pairs st_35.2.2) 22 6 rng_39
    (by decide +kernel)))))

def st_41 : ℕ × ℕ × List ℕ := nstep stMain (15, 1)

set_option maxRecDepth 100000 in
theorem dead_42 : Dead st_41 := by
  unfold Dead
  decide +kernel

def st_43 : ℕ × ℕ × List ℕ := nstep stMain (15, 2)

set_option maxRecDepth 100000 in
theorem dead_44 : Dead st_43 := by
  unfold Dead
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_45 : (((pairs stMain.2.2).drop 16).take 3).all (pg stMain) = true := by
  decide +kernel

def st_46 : ℕ × ℕ × List ℕ := nstep stMain (19, 0)

set_option maxRecDepth 100000 in
theorem rng_47 : (((pairs st_46.2.2).drop 0).take 25).all (pg st_46) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_48 : (((pairs st_46.2.2).drop 25).take 3).all (pg st_46) = true := by
  decide +kernel

theorem dead_49 : Dead st_46 :=
  dead_of st_46 (by decide +kernel) (by decide +kernel)
    (seg (pg st_46) (pairs st_46.2.2) 0 25 rng_47
    (seg (pg st_46) (pairs st_46.2.2) 25 3 rng_48
    (by decide +kernel)))

def st_50 : ℕ × ℕ × List ℕ := nstep stMain (19, 1)

set_option maxRecDepth 100000 in
theorem dead_51 : Dead st_50 := by
  unfold Dead
  decide +kernel

def st_52 : ℕ × ℕ × List ℕ := nstep stMain (19, 2)

set_option maxRecDepth 100000 in
theorem dead_53 : Dead st_52 := by
  unfold Dead
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_54 : (((pairs stMain.2.2).drop 20).take 4).all (pg stMain) = true := by
  decide +kernel

def st_55 : ℕ × ℕ × List ℕ := nstep stMain (24, 0)

set_option maxRecDepth 100000 in
theorem rng_56 : (((pairs st_55.2.2).drop 0).take 25).all (pg st_55) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_57 : (((pairs st_55.2.2).drop 25).take 3).all (pg st_55) = true := by
  decide +kernel

theorem dead_58 : Dead st_55 :=
  dead_of st_55 (by decide +kernel) (by decide +kernel)
    (seg (pg st_55) (pairs st_55.2.2) 0 25 rng_56
    (seg (pg st_55) (pairs st_55.2.2) 25 3 rng_57
    (by decide +kernel)))

def st_59 : ℕ × ℕ × List ℕ := nstep stMain (24, 1)

set_option maxRecDepth 100000 in
theorem dead_60 : Dead st_59 := by
  unfold Dead
  decide +kernel

def st_61 : ℕ × ℕ × List ℕ := nstep stMain (24, 2)

set_option maxRecDepth 100000 in
theorem dead_62 : Dead st_61 := by
  unfold Dead
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_63 : (((pairs stMain.2.2).drop 25).take 4).all (pg stMain) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_64 : (((pairs stMain.2.2).drop 29).take 1).all (pg stMain) = true := by
  decide +kernel

def st_65 : ℕ × ℕ × List ℕ := nstep stMain (30, 0)

set_option maxRecDepth 100000 in
theorem rng_66 : (((pairs st_65.2.2).drop 0).take 1).all (pg st_65) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_67 : (((pairs st_65.2.2).drop 1).take 5).all (pg st_65) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_68 : (((pairs st_65.2.2).drop 6).take 11).all (pg st_65) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_69 : (((pairs st_65.2.2).drop 17).take 3).all (pg st_65) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_70 : (((pairs st_65.2.2).drop 20).take 8).all (pg st_65) = true := by
  decide +kernel

theorem dead_71 : Dead st_65 :=
  dead_of st_65 (by decide +kernel) (by decide +kernel)
    (seg (pg st_65) (pairs st_65.2.2) 0 1 rng_66
    (seg (pg st_65) (pairs st_65.2.2) 1 5 rng_67
    (seg (pg st_65) (pairs st_65.2.2) 6 11 rng_68
    (seg (pg st_65) (pairs st_65.2.2) 17 3 rng_69
    (seg (pg st_65) (pairs st_65.2.2) 20 8 rng_70
    (by decide +kernel))))))

def st_72 : ℕ × ℕ × List ℕ := nstep stMain (30, 1)

set_option maxRecDepth 100000 in
theorem dead_73 : Dead st_72 := by
  unfold Dead
  decide +kernel

def st_74 : ℕ × ℕ × List ℕ := nstep stMain (30, 2)

set_option maxRecDepth 100000 in
theorem dead_75 : Dead st_74 := by
  unfold Dead
  decide +kernel

set_option maxRecDepth 100000 in
theorem rng_76 : (((pairs stMain.2.2).drop 31).take 5).all (pg stMain) = true := by
  decide +kernel

theorem dead_77 : Dead stMain :=
  dead_of stMain (by decide +kernel) (by decide +kernel)
    (seg (pg stMain) (pairs stMain.2.2) 0 3 rng_8
    (seg (pg stMain) (pairs stMain.2.2) 3 1 (pair_one stMain 3 3 (by decide +kernel) (by decide +kernel) (fun j hj => match j, hj with
    | 0, _ => dead_10
    | 1, _ => dead_12
    | 2, _ => dead_14
    | _ + 3, h => absurd h (by omega)))
    (seg (pg stMain) (pairs stMain.2.2) 4 3 rng_15
    (seg (pg stMain) (pairs stMain.2.2) 7 4 rng_16
    (seg (pg stMain) (pairs stMain.2.2) 11 1 (pair_one stMain 11 3 (by decide +kernel) (by decide +kernel) (fun j hj => match j, hj with
    | 0, _ => dead_20
    | 1, _ => dead_22
    | 2, _ => dead_24
    | _ + 3, h => absurd h (by omega)))
    (seg (pg stMain) (pairs stMain.2.2) 12 1 (pair_one stMain 12 3 (by decide +kernel) (by decide +kernel) (fun j hj => match j, hj with
    | 0, _ => dead_28
    | 1, _ => dead_30
    | 2, _ => dead_32
    | _ + 3, h => absurd h (by omega)))
    (seg (pg stMain) (pairs stMain.2.2) 13 1 rng_33
    (seg (pg stMain) (pairs stMain.2.2) 14 1 rng_34
    (seg (pg stMain) (pairs stMain.2.2) 15 1 (pair_one stMain 15 3 (by decide +kernel) (by decide +kernel) (fun j hj => match j, hj with
    | 0, _ => dead_40
    | 1, _ => dead_42
    | 2, _ => dead_44
    | _ + 3, h => absurd h (by omega)))
    (seg (pg stMain) (pairs stMain.2.2) 16 3 rng_45
    (seg (pg stMain) (pairs stMain.2.2) 19 1 (pair_one stMain 19 3 (by decide +kernel) (by decide +kernel) (fun j hj => match j, hj with
    | 0, _ => dead_49
    | 1, _ => dead_51
    | 2, _ => dead_53
    | _ + 3, h => absurd h (by omega)))
    (seg (pg stMain) (pairs stMain.2.2) 20 4 rng_54
    (seg (pg stMain) (pairs stMain.2.2) 24 1 (pair_one stMain 24 3 (by decide +kernel) (by decide +kernel) (fun j hj => match j, hj with
    | 0, _ => dead_58
    | 1, _ => dead_60
    | 2, _ => dead_62
    | _ + 3, h => absurd h (by omega)))
    (seg (pg stMain) (pairs stMain.2.2) 25 4 rng_63
    (seg (pg stMain) (pairs stMain.2.2) 29 1 rng_64
    (seg (pg stMain) (pairs stMain.2.2) 30 1 (pair_one stMain 30 3 (by decide +kernel) (by decide +kernel) (fun j hj => match j, hj with
    | 0, _ => dead_71
    | 1, _ => dead_73
    | 2, _ => dead_75
    | _ + 3, h => absurd h (by omega)))
    (seg (pg stMain) (pairs stMain.2.2) 31 5 rng_76
    (by decide +kernel))))))))))))))))))

def smallG (l : List ℕ) : Bool := !(optN 9 (10 - l.length) l)

def subs : List (List ℕ) := inputsN.sublists.filter (fun l => decide (l.length < 10))

theorem subs_main : subs.getD 1007 [] = stMain.2.2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem subs_low : ((subs.drop 0).take 1007).all smallG = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem subs_high : (subs.drop (1007 + 1)).all smallG = true := by decide +kernel

theorem front_small : subs.all smallG = true := by
  have hmain : smallG (subs.getD 1007 []) = true := by
    rw [subs_main]
    have h : optN 9 1 stMain.2.2 = false := dead_77
    change (!(optN 9 (10 - 9) stMain.2.2)) = true
    rw [show (10 - 9 : ℕ) = 1 from rfl, h]
    rfl
  exact seg smallG subs 0 1007 subs_low
    (seg smallG subs 1007 1 (take_one smallG subs 1007 [] (by decide +kernel) hmain) subs_high)

theorem full_none : optN 9 0 inputsN = false := dead_7

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build9 C hm hr)
  have hl3 : live basicOps goal 9 S := extend_live (by simp only [Circuit.size] at hs; omega) hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 9 l (10 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hN : optN 9 (10 - l.length) (l.map BitVec.toNat) = true := by
    rw [opt_eq]
    exact hsearch
  have hsl : l.Sublist inputs := List.filter_sublist
  by_cases hlen : l.length < 10
  · have hmem : l.map BitVec.toNat ∈ inputsN.sublists := by
      rw [← inputsN_eq]
      exact List.mem_sublists.mpr (hsl.map _)
    have hrow := List.all_eq_true.mp front_small (l.map BitVec.toNat)
      (List.mem_filter.mpr ⟨hmem, by simpa using hlen⟩)
    simp only [smallG, List.length_map, hN] at hrow
    exact Bool.noConfusion hrow
  · have hle := hsl.length_le
    rw [inputs_length] at hle
    have heq : l = inputs := hsl.eq_of_length (by rw [inputs_length]; omega)
    rw [heq, inputs_length, inputsN_eq] at hN
    rw [show (10 - 10 : ℕ) = 0 from rfl, full_none] at hN
    exact Bool.noConfusion hN

end PEqualNP.Outside.L_meta_10133

theorem PEqualNP.Outside.L_meta_10133 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (24894758 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_10133.no_small C hm hs hr
