import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9772_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset (mem_filter mem_inter mem_insert mem_singleton filter_subset mem_image mem_sdiff card_le_card mem_singleton_self card_pos card_eq_one mem_univ mem_union not_nonempty_iff_eq_empty eq_of_subset_of_card_le card_empty singleton_subset_iff card_insert_of_notMem disjoint_left card_singleton card_eq_zero card_pair not_nonempty_empty card_image_of_injOn card_image_of_injective inter_subset_left card_union_of_disjoint notMem_empty mem_product inter_subset_right eq_empty_iff_forall_notMem sdiff_subset inter_eq_left sum_congr nonempty_iff_ne_empty eq_singleton_iff_unique_mem card_filter mem_biUnion card_lt_card mem_erase mem_toLeft card_sdiff_add_card_eq_card image_subset_image mem_insert_self mem_range)
def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b
@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl
abbrev Dag := List (Bool × ℕ × ℕ)
def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2
def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]
def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w
def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false
def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j
def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)
def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card
def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w
def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []
def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1
def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)
def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)
def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)
def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)
def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)
def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))
def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))
def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)
def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)
def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D
def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))
def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)
def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)
def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ
def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1
def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)
def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)
def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)
def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)
def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)
def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}
def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))
def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b
theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl
theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]
theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]
theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega
theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]
theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]
theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]
theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]
theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]
theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)
theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk
theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]
theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]
abbrev Ref := Bool ⊕ ℕ
def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false
def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)
def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)
def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false
def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])
def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B
def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r
theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h
theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl
theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)
theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr
theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]
theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha
theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩
theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl
theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]
theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]
theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]
theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩
theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2
theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen
theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)
theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]
theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl
theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (mem_range.mpr hj)
  tauto
def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a
def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1
def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))
theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]
theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩
theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega
theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'
theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩
theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD
theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩
section SurplusFlow
variable {n : ℕ} {D : Dag}
theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [mem_range]; omega
theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]
theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]
theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := mem_range.mp hj
  have := hS j hj2
  omega
theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega
theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [card_filter, arcs, Finset.sum_product]
  refine sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]
theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]
theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega
theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, card_filter]
  refine sum_congr rfl (fun j hj => ?_)
  have := (hS j (mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega
theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩
theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))
theorem sum_fanout (hS : Strict n D) :
    ∑ w ∈ Finset.range (n + D.length), fanout D w = 2 * D.length := by
  rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
  intro e he
  have := sb_src_lt hS e he
  exact mem_range.mpr (by omega)
theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega
theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
theorem Bplus_le_total (n : ℕ) (D : Dag) : Bplus n D ≤ totalSurplus n D := by
  rw [totalSurplus_split]; omega
theorem Bplus_le_twelve (h13 : totalSurplus n D ≤ 13) (h0 : 1 ≤ Bzero n D) :
    Bplus n D ≤ 12 := by
  rw [totalSurplus_split] at h13; omega
theorem live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := card_pos.mp (hL w (by omega))
      simp only [readers, mem_filter, mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2
theorem mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]
theorem val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp
theorem val_zero (hS : Strict n D) (w : ℕ) : val D (fun _ : Fin n => false) w = false := by
  by_cases hw : w < n + D.length
  · exact val_unique hS _ (fun _ => false) (fun _ _ => rfl)
      (fun j _ => by cases tag D j <;> rfl) w hw
  · exact val_ge D _ w (by omega)
theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]
theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]
theorem supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]
theorem carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, card_filter, card_filter,
      ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun j hj => ?_)
    have := hpred j (mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [mem_filter, mem_image, mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega
theorem sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, mem_filter, mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact not_nonempty_empty hw.2
theorem sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, mem_inter, mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, card_image_of_injective _ Fin.val_injective]
theorem carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, mem_filter, mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [mem_inter] at hv
    exact Or.inl ⟨by omega, v, mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, mem_inter.mpr ⟨h1, hv.2⟩⟩
theorem carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, mem_filter, mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact mem_singleton_self x
      · rw [supp_input, mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, mem_filter, mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩
theorem mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
theorem sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp
theorem card_units (n : ℕ) (D : Dag) : (units n D).card = totalSurplus n D := by
  rw [units, Finset.card_sigma, totalSurplus, surplusOn]
  simp
theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)
theorem card_unitsOn (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (unitsOn n D K).card = surplusOn D K := by
  rw [unitsOn, sb_card_units_filter n D (fun w => w ∈ K), Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hK]
theorem mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, mem_biUnion, mem_filter, mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact notMem_empty v hv
theorem mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega
theorem sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [mem_inter, mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, mem_inter.mpr ⟨mem_singleton_self v, h⟩⟩
theorem sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm
theorem reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v
theorem card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  card_image_of_injOn (sb_reserved_inj b hb)
theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact card_le_card (reserved_subset hS b hb)
theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact card_sdiff_add_card_eq_card (reserved_subset hS b hb)
theorem surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, mem_union, mem_filter, mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [mem_filter, mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, card_union_of_disjoint h3, h4,
    card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr inter_subset_right))]
end SurplusFlow
def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))
theorem tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]
theorem tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]
theorem tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]
theorem liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]
theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w
theorem tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this
theorem relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]
theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]
theorem tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]
theorem tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]
theorem relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩
theorem relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']
theorem relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]
theorem relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'
theorem relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩
theorem relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]
theorem tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp
theorem relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, mem_filter, mem_univ, true_and, mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha
theorem tr_sum_liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → ℕ) :
    ∑ w ∈ (Finset.range m).filter (fun w => P (liftP σ w)), g (liftP σ w) =
      ∑ w ∈ (Finset.range m).filter P, g w := by
  refine Finset.sum_nbij' (liftP σ) (liftP σ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ hm a).mpr ha.1, ha.2⟩
  · intro a ha
    simp only [mem_filter, mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ⁻¹ hm a).mpr ha.1, by rw [tr_liftP_inv']; exact ha.2⟩
  · intro a _; exact liftP_inv σ a
  · intro a _; exact tr_liftP_inv' σ a
  · intro a _; rfl
theorem tr_surplus_filter {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ w, Q (liftP σ w) ↔ P w) :
    surplusOn (relabel σ D) ((inner n (relabel σ D)).filter Q) =
      surplusOn D ((inner n D).filter P) := by
  rcases eq_or_ne D [] with rfl | hne
  · simp [surplusOn, relabel, fanout, readers]
  · have hpos := List.length_pos_iff.mpr hne
    have hm : n ≤ n + D.length - 1 := by omega
    unfold surplusOn inner
    rw [relabel_length]
    exact (tr_sum_liftP σ hm Q (fun w => fanout (relabel σ D) w - 1)).symm.trans
      (sum_congr (Finset.filter_congr fun w _ => hPQ w)
        fun w _ => by rw [relabel_fanout])
theorem relabel_totalSurplus {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    totalSurplus n (relabel σ D) = totalSurplus n D := by
  simpa [totalSurplus] using
    tr_surplus_filter σ D (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)
theorem relabel_Bplus {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bplus n (relabel σ D) = Bplus n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)
theorem relabel_Bzero {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bzero n (relabel σ D) = Bzero n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)
theorem relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    eligSet n (relabel σ D) = (eligSet n D).image σ := by
  ext v
  simp only [eligSet, mem_biUnion, mem_image, branchW, mem_filter,
    mem_range]
  constructor
  · rintro ⟨w', ⟨hw', hf⟩, hv⟩
    obtain ⟨w, rfl⟩ : ∃ w, w' = liftP σ w := ⟨liftP σ⁻¹ w', (tr_liftP_inv' σ w').symm⟩
    rw [relabel_supp σ hS, mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [relabel_fanout] at hf
    rw [relabel_length, tr_liftP_lt_iff σ (Nat.le_add_right _ _)] at hw'
    exact ⟨a, ⟨w, ⟨hw', hf⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨w, ⟨hw, hf⟩, ha⟩, rfl⟩
    refine ⟨liftP σ w, ⟨?_, ?_⟩, ?_⟩
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · rw [relabel_fanout]; exact hf
    · rw [relabel_supp σ hS]; exact Finset.mem_image_of_mem _ ha
theorem relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, mem_sdiff, mem_univ, true_and,
    mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)
def edgeList : List (ℕ × ℕ) :=
  [(0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def edgeListOff0 : List (ℕ × ℕ) :=
  [(1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def G14Edge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true
abbrev Adj (u v : Fin 14) : Prop :=
  (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList
def adjBits (u : Fin 14) : ℕ :=
  match u.val with
  | 0 => 1024 | 1 => 8832 | 2 => 12544 | 3 => 6272 | 4 => 11264 | 5 => 5632 | 6 => 2816 | 7 => 10 | 8 => 68 | 9 => 98 | 10 => 49 | 11 => 88 | 12 => 44 | _ => 22
def hc_adjB (u v : Fin 14) : Bool := (adjBits u).testBit v.val
theorem hc_adjB_iff : ∀ u v : Fin 14, hc_adjB u v = true ↔ Adj u v := by
  decide +kernel
theorem sem_adjB_false {u v : Fin 14} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff]; cases hc_adjB u v <;> decide
theorem adj_symm {u v : Fin 14} (h : Adj u v) : Adj v u := h.symm
theorem adj_irrefl (u : Fin 14) : ¬ Adj u u := by
  revert u; decide +kernel
theorem g14Edge_iff_adj (x : Fin 14 → Bool) :
    G14Edge x ↔ ∃ u v : Fin 14, Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩; exact ⟨u, v, Or.inl huv, hx, hy⟩
  · rintro ⟨u, v, huv | hvu, hx, hy⟩
    · exact ⟨u, v, huv, hx, hy⟩
    · exact ⟨v, u, hvu, hy, hx⟩
def g14_nbB (v : Fin 14) : Finset (Fin 14) :=
  match v.val with
  | 0 => {10} | 1 => {7,9,13} | 2 => {8,12,13} | 3 => {7,11,12}
  | 4 => {10,11,13} | 5 => {9,10,12} | 6 => {8,9,11} | 7 => {1,3}
  | 8 => {2,6} | 9 => {1,5,6} | 10 => {0,4,5} | 11 => {3,4,6}
  | 12 => {2,3,5} | _ => {1,2,4}
def g14_deg3B (v : Fin 14) : Bool := match v.val with | 0 => false | 1 => true | 2 => true | 3 => true | 4 => true | 5 => true | 6 => true | 7 => false | 8 => false | 9 => true | 10 => true | 11 => true | 12 => true | _ => true
theorem g14_deg3B_iff : ∀ v : Fin 14, g14_deg3B v = true ↔ (g14_nbB v).card = 3 := by
  decide +kernel
def sem_g14_nb (v : Fin 14) : Finset (Fin 14) := g14_nbB v
theorem g14_nb_eq (v : Fin 14) : sem_g14_nb v = g14_nbB v := rfl
theorem g14_mem_nb {i a : Fin 14} : a ∈ sem_g14_nb i ↔ Adj i a := by
  revert i a; decide +kernel
theorem degree_pos : ∀ v : Fin 14, 0 < (g14_nbB v).card := by
  decide +kernel
theorem degree_le_three : ∀ v : Fin 14, (g14_nbB v).card ≤ 3 := by
  decide +kernel
theorem degree_two_or_three : ∀ v : Fin 14, v ≠ 0 → (g14_nbB v).card = 2 ∨ (g14_nbB v).card = 3 := by
  decide +kernel
theorem common_nbr_le_one : ∀ u v : Fin 14, u ≠ v →
    (g14_nbB u ∩ g14_nbB v).card ≤ 1 := by
  decide +kernel
theorem sup_g14_inter (i j : Fin 14) (hij : i ≠ j) (P : Finset (Fin 14)) :
    (sem_g14_nb i ∩ (sem_g14_nb j ∩ P)).card ≤ 1 := by
  have hsub : sem_g14_nb i ∩ (sem_g14_nb j ∩ P) ⊆ g14_nbB i ∩ g14_nbB j := by
    intro x hx
    rw [mem_inter, mem_inter] at hx
    exact mem_inter.2 ⟨hx.1, hx.2.1⟩
  exact (card_le_card hsub).trans (common_nbr_le_one i j hij)
theorem nbr_diff_exists : ∀ u v : Fin 14, u ≠ v → u ≠ 0 → ∃ z : Fin 14, Adj u z ∧ ¬ Adj v z := by
  have h : ∀ u v : Fin 14, u ≠ v → u ≠ 0 → ∃ z : Fin 14, hc_adjB u z = true ∧ hc_adjB v z = false := by
    decide +kernel
  intro u v huv hu0
  obtain ⟨z, h1, h2⟩ := h u v huv hu0
  exact ⟨z, (hc_adjB_iff u z).1 h1, sem_adjB_false.1 h2⟩
theorem zero_sub_045 : ∀ u : Fin 14, u ≠ 0 → u ≠ 4 → u ≠ 5 → Adj 0 10 ∧ ¬ Adj u 10 := by
  have h : ∀ u : Fin 14, u ≠ 0 → u ≠ 4 → u ≠ 5 → hc_adjB 0 10 = true ∧ hc_adjB u 10 = false := by
    decide +kernel
  intro u h0 h4 h5
  obtain ⟨h1, h2⟩ := h u h0 h4 h5
  exact ⟨(hc_adjB_iff 0 10).1 h1, sem_adjB_false.1 h2⟩
theorem g14_nb_inj {i j : Fin 14} (h : sem_g14_nb i = sem_g14_nb j) : i = j := by
  have hdec : ∀ a b : Fin 14, g14_nbB a = g14_nbB b → a = b := by decide +kernel
  exact hdec i j h
def IsCoverOff0 (S : Finset (Fin 14)) : Prop :=
  ∀ u v : Fin 14, u ≠ 0 → v ≠ 0 → Adj u v → u ∈ S ∨ v ∈ S
def IsIndepOff0 (I : Finset (Fin 14)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, u ≠ 0 → v ≠ 0 → ¬ Adj u v
def IsAut (σ : Equiv.Perm (Fin 14)) : Prop :=
  ∀ u v : Fin 14, Adj (σ u) (σ v) ↔ Adj u v
def aut0_fn (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | _ => 13
def aut0_inv (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | _ => 13
def aut0 : Equiv.Perm (Fin 14) := ⟨aut0_fn, aut0_inv, by decide +kernel, by decide +kernel⟩
def aut1_fn (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 2 | 7 => 7 | 8 => 8 | 9 => 13 | 10 => 10 | 11 => 12 | 12 => 11 | _ => 9
def aut1_inv (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 2 | 7 => 7 | 8 => 8 | 9 => 13 | 10 => 10 | 11 => 12 | 12 => 11 | _ => 9
def aut1 : Equiv.Perm (Fin 14) := ⟨aut1_fn, aut1_inv, by decide +kernel, by decide +kernel⟩
def aut2_fn (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 6 | 4 => 4 | 5 => 5 | 6 => 3 | 7 => 8 | 8 => 7 | 9 => 12 | 10 => 10 | 11 => 11 | 12 => 9 | _ => 13
def aut2_inv (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 6 | 4 => 4 | 5 => 5 | 6 => 3 | 7 => 8 | 8 => 7 | 9 => 12 | 10 => 10 | 11 => 11 | 12 => 9 | _ => 13
def aut2 : Equiv.Perm (Fin 14) := ⟨aut2_fn, aut2_inv, by decide +kernel, by decide +kernel⟩
def aut3_fn (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 6 | 4 => 5 | 5 => 4 | 6 => 1 | 7 => 8 | 8 => 7 | 9 => 13 | 10 => 10 | 11 => 9 | 12 => 11 | _ => 12
def aut3_inv (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 6 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 3 | 7 => 8 | 8 => 7 | 9 => 11 | 10 => 10 | 11 => 12 | 12 => 13 | _ => 9
def aut3 : Equiv.Perm (Fin 14) := ⟨aut3_fn, aut3_inv, by decide +kernel, by decide +kernel⟩
def aut4_fn (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 11 | 10 => 10 | 11 => 9 | 12 => 13 | _ => 12
def aut4_inv (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 11 | 10 => 10 | 11 => 9 | 12 => 13 | _ => 12
def aut4 : Equiv.Perm (Fin 14) := ⟨aut4_fn, aut4_inv, by decide +kernel, by decide +kernel⟩
def aut5_fn (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 2 | 7 => 7 | 8 => 8 | 9 => 12 | 10 => 10 | 11 => 13 | 12 => 9 | _ => 11
def aut5_inv (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 2 | 7 => 7 | 8 => 8 | 9 => 12 | 10 => 10 | 11 => 13 | 12 => 9 | _ => 11
def aut5 : Equiv.Perm (Fin 14) := ⟨aut5_fn, aut5_inv, by decide +kernel, by decide +kernel⟩
def aut6_fn (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 6 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 3 | 7 => 8 | 8 => 7 | 9 => 11 | 10 => 10 | 11 => 12 | 12 => 13 | _ => 9
def aut6_inv (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 6 | 4 => 5 | 5 => 4 | 6 => 1 | 7 => 8 | 8 => 7 | 9 => 13 | 10 => 10 | 11 => 9 | 12 => 11 | _ => 12
def aut6 : Equiv.Perm (Fin 14) := ⟨aut6_fn, aut6_inv, by decide +kernel, by decide +kernel⟩
def aut7_fn (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 1 | 7 => 8 | 8 => 7 | 9 => 9 | 10 => 10 | 11 => 13 | 12 => 12 | _ => 11
def aut7_inv (v : Fin 14) : Fin 14 := match v.val with | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 1 | 7 => 8 | 8 => 7 | 9 => 9 | 10 => 10 | 11 => 13 | 12 => 12 | _ => 11
def aut7 : Equiv.Perm (Fin 14) := ⟨aut7_fn, aut7_inv, by decide +kernel, by decide +kernel⟩
theorem aut0_isAut : IsAut aut0 := by intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut1_isAut : IsAut aut1 := by intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut2_isAut : IsAut aut2 := by intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut3_isAut : IsAut aut3 := by intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut4_isAut : IsAut aut4 := by intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut5_isAut : IsAut aut5 := by intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut6_isAut : IsAut aut6 := by intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
theorem aut7_isAut : IsAut aut7 := by intro u v; simp only [← hc_adjB_iff]; revert u v; decide +kernel
def autOf (k : Fin 8) : Equiv.Perm (Fin 14) :=
  match k.val with
  | 0 => aut0 | 1 => aut1 | 2 => aut2 | 3 => aut3 | 4 => aut4 | 5 => aut5 | 6 => aut6 | _ => aut7
theorem autOf_isAut (k : Fin 8) : IsAut (autOf k) := by
  fin_cases k
  · exact aut0_isAut
  · exact aut1_isAut
  · exact aut2_isAut
  · exact aut3_isAut
  · exact aut4_isAut
  · exact aut5_isAut
  · exact aut6_isAut
  · exact aut7_isAut
theorem g14Edge_aut (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) (x : Fin 14 → Bool) :
    G14Edge (fun i => x (σ i)) ↔ G14Edge x := by
  simp only [g14Edge_iff_adj]
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩
    exact ⟨σ u, σ v, (hσ u v).2 huv, hx, hy⟩
  · rintro ⟨u, v, huv, hx, hy⟩
    refine ⟨σ⁻¹ u, σ⁻¹ v, (hσ (σ⁻¹ u) (σ⁻¹ v)).1 ?_, by simpa using hx, by simpa using hy⟩
    simpa using huv
def hc_rep (idx : Fin 157) : Finset (Fin 14) :=
  match idx.val with
  | 0 => {0,1,2} | 1 => {0,1,3} | 2 => {0,1,4} | 3 => {0,1,8}
  | 4 => {0,1,10} | 5 => {0,1,11} | 6 => {0,4,5} | 7 => {0,4,7}
  | 8 => {0,4,9} | 9 => {0,7,8} | 10 => {0,7,9} | 11 => {0,7,10}
  | 12 => {0,9,10} | 13 => {0,9,11} | 14 => {0,9,12} | 15 => {1,2,3}
  | 16 => {1,2,4} | 17 => {1,2,5} | 18 => {1,2,10} | 19 => {1,2,11}
  | 20 => {1,3,4} | 21 => {1,3,8} | 22 => {1,3,10} | 23 => {1,4,5}
  | 24 => {1,4,8} | 25 => {1,4,12} | 26 => {1,8,10} | 27 => {1,8,11}
  | 28 => {1,10,11} | 29 => {1,11,12} | 30 => {4,5,7} | 31 => {4,7,8}
  | 32 => {4,7,9} | 33 => {4,9,12} | 34 => {7,8,9} | 35 => {7,8,10}
  | 36 => {7,9,10} | 37 => {7,9,11} | 38 => {7,9,12} | 39 => {7,9,13}
  | 40 => {9,10,11} | 41 => {9,10,12} | 42 => {9,11,12} | 43 => {0,1,2,3}
  | 44 => {0,1,2,4} | 45 => {0,1,2,5} | 46 => {0,1,2,10} | 47 => {0,1,2,11}
  | 48 => {0,1,3,4} | 49 => {0,1,3,8} | 50 => {0,1,3,10} | 51 => {0,1,4,5}
  | 52 => {0,1,4,8} | 53 => {0,1,4,12} | 54 => {0,1,8,10} | 55 => {0,1,8,11}
  | 56 => {0,1,10,11} | 57 => {0,1,11,12} | 58 => {0,4,5,7} | 59 => {0,4,7,8}
  | 60 => {0,4,7,9} | 61 => {0,4,9,12} | 62 => {0,7,8,9} | 63 => {0,7,8,10}
  | 64 => {0,7,9,10} | 65 => {0,7,9,11} | 66 => {0,7,9,12} | 67 => {0,7,9,13}
  | 68 => {0,9,10,11} | 69 => {0,9,10,12} | 70 => {0,9,11,12} | 71 => {1,2,3,4}
  | 72 => {1,2,3,6} | 73 => {1,2,3,10} | 74 => {1,2,4,5} | 75 => {1,2,5,11}
  | 76 => {1,2,10,11} | 77 => {1,3,4,5} | 78 => {1,3,4,8} | 79 => {1,3,8,10}
  | 80 => {1,4,5,8} | 81 => {1,4,8,12} | 82 => {1,8,10,11} | 83 => {1,8,11,12}
  | 84 => {1,10,11,12} | 85 => {4,5,7,8} | 86 => {4,7,8,9} | 87 => {4,7,9,12}
  | 88 => {7,8,9,10} | 89 => {7,8,9,11} | 90 => {7,8,9,12} | 91 => {7,9,10,11}
  | 92 => {7,9,10,12} | 93 => {7,9,10,13} | 94 => {7,9,11,12} | 95 => {9,10,11,12}
  | 96 => {9,11,12,13} | 97 => {0,1,2,3,4} | 98 => {0,1,2,3,6} | 99 => {0,1,2,3,10}
  | 100 => {0,1,2,4,5} | 101 => {0,1,2,5,11} | 102 => {0,1,2,10,11} | 103 => {0,1,3,4,5}
  | 104 => {0,1,3,4,8} | 105 => {0,1,3,8,10} | 106 => {0,1,4,5,8} | 107 => {0,1,4,8,12}
  | 108 => {0,1,8,10,11} | 109 => {0,1,8,11,12} | 110 => {0,1,10,11,12} | 111 => {0,4,5,7,8}
  | 112 => {0,4,7,8,9} | 113 => {0,4,7,9,12} | 114 => {0,7,8,9,10} | 115 => {0,7,8,9,11}
  | 116 => {0,7,8,9,12} | 117 => {0,7,9,10,11} | 118 => {0,7,9,10,12} | 119 => {0,7,9,10,13}
  | 120 => {0,7,9,11,12} | 121 => {0,9,10,11,12} | 122 => {0,9,11,12,13} | 123 => {1,2,3,4,5}
  | 124 => {1,2,3,4,6} | 125 => {1,2,3,6,10} | 126 => {1,3,4,5,8} | 127 => {1,8,10,11,12}
  | 128 => {4,7,8,9,12} | 129 => {7,8,9,10,11} | 130 => {7,8,9,10,12} | 131 => {7,8,9,11,12}
  | 132 => {7,9,10,11,12} | 133 => {7,9,11,12,13} | 134 => {9,10,11,12,13} | 135 => {0,1,2,3,4,5}
  | 136 => {0,1,2,3,4,6} | 137 => {0,1,2,3,6,10} | 138 => {0,1,3,4,5,8} | 139 => {0,1,8,10,11,12}
  | 140 => {0,4,7,8,9,12} | 141 => {0,7,8,9,10,11} | 142 => {0,7,8,9,10,12} | 143 => {0,7,8,9,11,12}
  | 144 => {0,7,9,10,11,12} | 145 => {0,7,9,11,12,13} | 146 => {0,9,10,11,12,13} | 147 => {1,2,3,4,5,6}
  | 148 => {7,8,9,10,11,12} | 149 => {7,8,9,11,12,13} | 150 => {7,9,10,11,12,13} | 151 => {0,1,2,3,4,5,6}
  | 152 => {0,7,8,9,10,11,12} | 153 => {0,7,8,9,11,12,13} | 154 => {0,7,9,10,11,12,13} | 155 => {7,8,9,10,11,12,13}
  | _ => {0,7,8,9,10,11,12,13}
def repMask (idx : Fin 157) : ℕ :=
  match idx.val with
  | 0 => 7 | 1 => 11 | 2 => 19 | 3 => 259 | 4 => 1027 | 5 => 2051 | 6 => 49 | 7 => 145
  | 8 => 529 | 9 => 385 | 10 => 641 | 11 => 1153 | 12 => 1537 | 13 => 2561 | 14 => 4609 | 15 => 14
  | 16 => 22 | 17 => 38 | 18 => 1030 | 19 => 2054 | 20 => 26 | 21 => 266 | 22 => 1034 | 23 => 50
  | 24 => 274 | 25 => 4114 | 26 => 1282 | 27 => 2306 | 28 => 3074 | 29 => 6146 | 30 => 176 | 31 => 400
  | 32 => 656 | 33 => 4624 | 34 => 896 | 35 => 1408 | 36 => 1664 | 37 => 2688 | 38 => 4736 | 39 => 8832
  | 40 => 3584 | 41 => 5632 | 42 => 6656 | 43 => 15 | 44 => 23 | 45 => 39 | 46 => 1031 | 47 => 2055
  | 48 => 27 | 49 => 267 | 50 => 1035 | 51 => 51 | 52 => 275 | 53 => 4115 | 54 => 1283 | 55 => 2307
  | 56 => 3075 | 57 => 6147 | 58 => 177 | 59 => 401 | 60 => 657 | 61 => 4625 | 62 => 897 | 63 => 1409
  | 64 => 1665 | 65 => 2689 | 66 => 4737 | 67 => 8833 | 68 => 3585 | 69 => 5633 | 70 => 6657 | 71 => 30
  | 72 => 78 | 73 => 1038 | 74 => 54 | 75 => 2086 | 76 => 3078 | 77 => 58 | 78 => 282 | 79 => 1290
  | 80 => 306 | 81 => 4370 | 82 => 3330 | 83 => 6402 | 84 => 7170 | 85 => 432 | 86 => 912 | 87 => 4752
  | 88 => 1920 | 89 => 2944 | 90 => 4992 | 91 => 3712 | 92 => 5760 | 93 => 9856 | 94 => 6784 | 95 => 7680
  | 96 => 14848 | 97 => 31 | 98 => 79 | 99 => 1039 | 100 => 55 | 101 => 2087 | 102 => 3079 | 103 => 59
  | 104 => 283 | 105 => 1291 | 106 => 307 | 107 => 4371 | 108 => 3331 | 109 => 6403 | 110 => 7171 | 111 => 433
  | 112 => 913 | 113 => 4753 | 114 => 1921 | 115 => 2945 | 116 => 4993 | 117 => 3713 | 118 => 5761 | 119 => 9857
  | 120 => 6785 | 121 => 7681 | 122 => 14849 | 123 => 62 | 124 => 94 | 125 => 1102 | 126 => 314 | 127 => 7426
  | 128 => 5008 | 129 => 3968 | 130 => 6016 | 131 => 7040 | 132 => 7808 | 133 => 14976 | 134 => 15872 | 135 => 63
  | 136 => 95 | 137 => 1103 | 138 => 315 | 139 => 7427 | 140 => 5009 | 141 => 3969 | 142 => 6017 | 143 => 7041
  | 144 => 7809 | 145 => 14977 | 146 => 15873 | 147 => 126 | 148 => 8064 | 149 => 15232 | 150 => 16000 | 151 => 127
  | 152 => 8065 | 153 => 15233 | 154 => 16001 | 155 => 16256 | _ => 16257
def canonI : Finset (Finset (Fin 14)) := Finset.univ.image hc_rep
theorem hc_rep_of_mem {R : Finset (Fin 14)} (h : R ∈ canonI) :
    ∃ idx : Fin 157, hc_rep idx = R := by
  obtain ⟨idx, -, rfl⟩ := mem_image.1 h
  exact ⟨idx, rfl⟩
def setMask (S : Finset (Fin 14)) : ℕ :=
  (if (0 : Fin 14) ∈ S then 2 ^ 0 else 0) |||
  (if (1 : Fin 14) ∈ S then 2 ^ 1 else 0) |||
  (if (2 : Fin 14) ∈ S then 2 ^ 2 else 0) |||
  (if (3 : Fin 14) ∈ S then 2 ^ 3 else 0) |||
  (if (4 : Fin 14) ∈ S then 2 ^ 4 else 0) |||
  (if (5 : Fin 14) ∈ S then 2 ^ 5 else 0) |||
  (if (6 : Fin 14) ∈ S then 2 ^ 6 else 0) |||
  (if (7 : Fin 14) ∈ S then 2 ^ 7 else 0) |||
  (if (8 : Fin 14) ∈ S then 2 ^ 8 else 0) |||
  (if (9 : Fin 14) ∈ S then 2 ^ 9 else 0) |||
  (if (10 : Fin 14) ∈ S then 2 ^ 10 else 0) |||
  (if (11 : Fin 14) ∈ S then 2 ^ 11 else 0) |||
  (if (12 : Fin 14) ∈ S then 2 ^ 12 else 0) |||
  (if (13 : Fin 14) ∈ S then 2 ^ 13 else 0)
theorem ite_two_pow_testBit (p : Prop) [Decidable p] (k b : ℕ) :
    (if p then 2 ^ k else 0).testBit b = (decide (k = b) && decide p) := by
  split_ifs with hp <;> simp [Nat.testBit_two_pow, hp]
theorem setMask_testBit (S : Finset (Fin 14)) (i : Fin 14) :
    (setMask S).testBit i.val = decide (i ∈ S) := by
  fin_cases i <;>
    (simp only [setMask, Nat.testBit_or, ite_two_pow_testBit]; simp)
theorem ite_two_pow_lt (p : Prop) [Decidable p] (k : ℕ) (hk : k < 14) :
    (if p then 2 ^ k else 0) < 2 ^ 14 := by
  split_ifs
  · exact Nat.pow_lt_pow_right (by omega) hk
  · omega
theorem setMask_lt (S : Finset (Fin 14)) : setMask S < 16384 := by
  change setMask S < 2 ^ 14
  unfold setMask
  repeat (apply Nat.or_lt_two_pow)
  all_goals exact ite_two_pow_lt _ _ (by omega)
theorem setMask_inj {S T : Finset (Fin 14)} (h : setMask S = setMask T) : S = T := by
  ext i
  have h1 := congrArg (fun m => m.testBit i.val) h
  rw [setMask_testBit, setMask_testBit] at h1
  simpa using h1
theorem repMask_eq : ∀ idx : Fin 157, setMask (hc_rep idx) = repMask idx := by
  decide +kernel
def findCanonIdx (m : ℕ) : Option (Fin 157) :=
  match m with
  | 7 => some 0 | 11 => some 1 | 19 => some 2 | 259 => some 3 | 1027 => some 4 | 2051 => some 5
  | 49 => some 6 | 145 => some 7 | 529 => some 8 | 385 => some 9 | 641 => some 10 | 1153 => some 11
  | 1537 => some 12 | 2561 => some 13 | 4609 => some 14 | 14 => some 15 | 22 => some 16 | 38 => some 17
  | 1030 => some 18 | 2054 => some 19 | 26 => some 20 | 266 => some 21 | 1034 => some 22 | 50 => some 23
  | 274 => some 24 | 4114 => some 25 | 1282 => some 26 | 2306 => some 27 | 3074 => some 28 | 6146 => some 29
  | 176 => some 30 | 400 => some 31 | 656 => some 32 | 4624 => some 33 | 896 => some 34 | 1408 => some 35
  | 1664 => some 36 | 2688 => some 37 | 4736 => some 38 | 8832 => some 39 | 3584 => some 40 | 5632 => some 41
  | 6656 => some 42 | 15 => some 43 | 23 => some 44 | 39 => some 45 | 1031 => some 46 | 2055 => some 47
  | 27 => some 48 | 267 => some 49 | 1035 => some 50 | 51 => some 51 | 275 => some 52 | 4115 => some 53
  | 1283 => some 54 | 2307 => some 55 | 3075 => some 56 | 6147 => some 57 | 177 => some 58 | 401 => some 59
  | 657 => some 60 | 4625 => some 61 | 897 => some 62 | 1409 => some 63 | 1665 => some 64 | 2689 => some 65
  | 4737 => some 66 | 8833 => some 67 | 3585 => some 68 | 5633 => some 69 | 6657 => some 70 | 30 => some 71
  | 78 => some 72 | 1038 => some 73 | 54 => some 74 | 2086 => some 75 | 3078 => some 76 | 58 => some 77
  | 282 => some 78 | 1290 => some 79 | 306 => some 80 | 4370 => some 81 | 3330 => some 82 | 6402 => some 83
  | 7170 => some 84 | 432 => some 85 | 912 => some 86 | 4752 => some 87 | 1920 => some 88 | 2944 => some 89
  | 4992 => some 90 | 3712 => some 91 | 5760 => some 92 | 9856 => some 93 | 6784 => some 94 | 7680 => some 95
  | 14848 => some 96 | 31 => some 97 | 79 => some 98 | 1039 => some 99 | 55 => some 100 | 2087 => some 101
  | 3079 => some 102 | 59 => some 103 | 283 => some 104 | 1291 => some 105 | 307 => some 106 | 4371 => some 107
  | 3331 => some 108 | 6403 => some 109 | 7171 => some 110 | 433 => some 111 | 913 => some 112 | 4753 => some 113
  | 1921 => some 114 | 2945 => some 115 | 4993 => some 116 | 3713 => some 117 | 5761 => some 118 | 9857 => some 119
  | 6785 => some 120 | 7681 => some 121 | 14849 => some 122 | 62 => some 123 | 94 => some 124 | 1102 => some 125
  | 314 => some 126 | 7426 => some 127 | 5008 => some 128 | 3968 => some 129 | 6016 => some 130 | 7040 => some 131
  | 7808 => some 132 | 14976 => some 133 | 15872 => some 134 | 63 => some 135 | 95 => some 136 | 1103 => some 137
  | 315 => some 138 | 7427 => some 139 | 5009 => some 140 | 3969 => some 141 | 6017 => some 142 | 7041 => some 143
  | 7809 => some 144 | 14977 => some 145 | 15873 => some 146 | 126 => some 147 | 8064 => some 148 | 15232 => some 149
  | 16000 => some 150 | 127 => some 151 | 8065 => some 152 | 15233 => some 153 | 16001 => some 154 | 16256 => some 155
  | 16257 => some 156
  | _ => none
theorem findCanonIdx_some (m : ℕ) (idx : Fin 157) (h : findCanonIdx m = some idx) :
    m = repMask idx := by
  unfold findCanonIdx at h
  split at h <;> cases h <;> rfl
def autMask (k : Fin 8) (m : ℕ) : ℕ :=
  (if m.testBit 0 then 2 ^ (autOf k 0).val else 0) |||
  (if m.testBit 1 then 2 ^ (autOf k 1).val else 0) |||
  (if m.testBit 2 then 2 ^ (autOf k 2).val else 0) |||
  (if m.testBit 3 then 2 ^ (autOf k 3).val else 0) |||
  (if m.testBit 4 then 2 ^ (autOf k 4).val else 0) |||
  (if m.testBit 5 then 2 ^ (autOf k 5).val else 0) |||
  (if m.testBit 6 then 2 ^ (autOf k 6).val else 0) |||
  (if m.testBit 7 then 2 ^ (autOf k 7).val else 0) |||
  (if m.testBit 8 then 2 ^ (autOf k 8).val else 0) |||
  (if m.testBit 9 then 2 ^ (autOf k 9).val else 0) |||
  (if m.testBit 10 then 2 ^ (autOf k 10).val else 0) |||
  (if m.testBit 11 then 2 ^ (autOf k 11).val else 0) |||
  (if m.testBit 12 then 2 ^ (autOf k 12).val else 0) |||
  (if m.testBit 13 then 2 ^ (autOf k 13).val else 0)
theorem autMask_testBit (k : Fin 8) (m : ℕ) (i : Fin 14) :
    (autMask k m).testBit i.val = m.testBit ((autOf k)⁻¹ i).val := by
  have hc : ∀ (j : Fin 14), ((autOf k j).val = i.val) ↔ j = (autOf k)⁻¹ i := by
    intro j
    constructor
    · intro h; exact ((Equiv.eq_symm_apply (autOf k)).2 (Fin.ext h))
    · intro h; exact congrArg Fin.val ((Equiv.eq_symm_apply (autOf k)).1 h)
  have hterm : ∀ (j : Fin 14),
      (if m.testBit j.val = true then 2 ^ (autOf k j).val else 0).testBit i.val =
      (decide (j = (autOf k)⁻¹ i) && m.testBit j.val) := by
    intro j; rw [ite_two_pow_testBit, decide_eq_decide.2 (hc j)]; cases m.testBit j.val <;> rfl
  have hexp : (autMask k m).testBit i.val =
      ((decide ((0 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 0) ||
      (decide ((1 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 1) ||
      (decide ((2 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 2) ||
      (decide ((3 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 3) ||
      (decide ((4 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 4) ||
      (decide ((5 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 5) ||
      (decide ((6 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 6) ||
      (decide ((7 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 7) ||
      (decide ((8 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 8) ||
      (decide ((9 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 9) ||
      (decide ((10 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 10) ||
      (decide ((11 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 11) ||
      (decide ((12 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 12) ||
      (decide ((13 : Fin 14) = (autOf k)⁻¹ i) && m.testBit 13)) := by
    change ((if m.testBit (0 : Fin 14).val = true then 2 ^ (autOf k 0).val else 0) |||
      (if m.testBit (1 : Fin 14).val = true then 2 ^ (autOf k 1).val else 0) |||
      (if m.testBit (2 : Fin 14).val = true then 2 ^ (autOf k 2).val else 0) |||
      (if m.testBit (3 : Fin 14).val = true then 2 ^ (autOf k 3).val else 0) |||
      (if m.testBit (4 : Fin 14).val = true then 2 ^ (autOf k 4).val else 0) |||
      (if m.testBit (5 : Fin 14).val = true then 2 ^ (autOf k 5).val else 0) |||
      (if m.testBit (6 : Fin 14).val = true then 2 ^ (autOf k 6).val else 0) |||
      (if m.testBit (7 : Fin 14).val = true then 2 ^ (autOf k 7).val else 0) |||
      (if m.testBit (8 : Fin 14).val = true then 2 ^ (autOf k 8).val else 0) |||
      (if m.testBit (9 : Fin 14).val = true then 2 ^ (autOf k 9).val else 0) |||
      (if m.testBit (10 : Fin 14).val = true then 2 ^ (autOf k 10).val else 0) |||
      (if m.testBit (11 : Fin 14).val = true then 2 ^ (autOf k 11).val else 0) |||
      (if m.testBit (12 : Fin 14).val = true then 2 ^ (autOf k 12).val else 0) |||
      (if m.testBit (13 : Fin 14).val = true then 2 ^ (autOf k 13).val else 0)).testBit i.val = _
    simp only [Nat.testBit_or, hterm]
    rfl
  rw [hexp]
  generalize (autOf k)⁻¹ i = t
  fin_cases t <;> simp
theorem setMask_image_aut (k : Fin 8) (S : Finset (Fin 14)) :
    setMask (S.image (autOf k)) = autMask k (setMask S) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 14
  · have hL : (setMask (S.image (autOf k))).testBit b =
        decide ((⟨b, hb⟩ : Fin 14) ∈ S.image (autOf k)) :=
      setMask_testBit (S.image (autOf k)) ⟨b, hb⟩
    rw [hL]
    have him : (⟨b, hb⟩ : Fin 14) ∈ S.image (autOf k) ↔ (autOf k)⁻¹ ⟨b, hb⟩ ∈ S := by
      constructor
      · intro hmem
        obtain ⟨x, hx, hxi⟩ := mem_image.1 hmem
        have : x = (autOf k)⁻¹ ⟨b, hb⟩ := by rw [← hxi]; simp
        exact this ▸ hx
      · intro hx; exact mem_image.2 ⟨(autOf k)⁻¹ ⟨b, hb⟩, hx, by simp⟩
    have hR : (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 14).val =
        decide ((autOf k)⁻¹ ⟨b, hb⟩ ∈ S) := by
      rw [autMask_testBit, setMask_testBit]
    change _ = (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 14).val
    rw [hR, decide_eq_decide]
    exact him
  · have hL : (setMask (S.image (autOf k))).testBit b = false :=
      Nat.testBit_lt_two_pow ((setMask_lt _).trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 14 ≤ b)))
    have hltR : autMask k (setMask S) < 2 ^ 14 := by
      unfold autMask
      repeat (apply Nat.or_lt_two_pow)
      all_goals exact ite_two_pow_lt _ _ (Fin.isLt _)
    have hR : (autMask k (setMask S)).testBit b = false :=
      Nat.testBit_lt_two_pow (hltR.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 14 ≤ b)))
    rw [hL, hR]
def isIndepOff0Mask (m : ℕ) : Bool :=
  edgeListOff0.all (fun e => !(m.testBit e.1 && m.testBit e.2))
def pop14 (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) + (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) + (if m.testBit 7 then 1 else 0) +
  (if m.testBit 8 then 1 else 0) + (if m.testBit 9 then 1 else 0) +
  (if m.testBit 10 then 1 else 0) + (if m.testBit 11 then 1 else 0) +
  (if m.testBit 12 then 1 else 0) + (if m.testBit 13 then 1 else 0)
theorem isIndepOff0Mask_of_indep {I : Finset (Fin 14)} (hI : IsIndepOff0 I) :
    isIndepOff0Mask (setMask I) = true := by
  have hedge : ∀ u v : Fin 14, u ≠ 0 → v ≠ 0 → Adj u v →
      !((setMask I).testBit u.val && (setMask I).testBit v.val) = true := by
    intro u v hu0 hv0 huv
    rw [setMask_testBit, setMask_testBit]
    by_cases hu : u ∈ I <;> by_cases hv : v ∈ I
    · exact absurd huv (hI u hu v hv hu0 hv0)
    · simp [hu, hv]
    · simp [hu, hv]
    · simp [hu, hv]
  unfold isIndepOff0Mask edgeListOff0
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hedge 1 7 (by decide) (by decide) (by decide), hedge 1 9 (by decide) (by decide) (by decide), hedge 1 13 (by decide) (by decide) (by decide), hedge 2 8 (by decide) (by decide) (by decide), hedge 2 12 (by decide) (by decide) (by decide), hedge 2 13 (by decide) (by decide) (by decide), hedge 3 7 (by decide) (by decide) (by decide), hedge 3 11 (by decide) (by decide) (by decide), hedge 3 12 (by decide) (by decide) (by decide), hedge 4 10 (by decide) (by decide) (by decide), hedge 4 11 (by decide) (by decide) (by decide), hedge 4 13 (by decide) (by decide) (by decide), hedge 5 9 (by decide) (by decide) (by decide), hedge 5 10 (by decide) (by decide) (by decide), hedge 5 12 (by decide) (by decide) (by decide), hedge 6 8 (by decide) (by decide) (by decide), hedge 6 9 (by decide) (by decide) (by decide), hedge 6 11 (by decide) (by decide) (by decide)⟩
theorem pop14_eq_card (I : Finset (Fin 14)) : pop14 (setMask I) = I.card := by
  have h1 : I.card = ∑ x ∈ (Finset.univ : Finset (Fin 14)), if x ∈ I then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have huniv : (Finset.univ : Finset (Fin 14)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    decide
  rw [h1, huniv]
  simp only [Finset.sum_insert, Finset.sum_singleton, mem_insert, mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  dsimp only [pop14]
  rw [show (setMask I).testBit 0 = decide ((0 : Fin 14) ∈ I) from setMask_testBit I 0,
      show (setMask I).testBit 1 = decide ((1 : Fin 14) ∈ I) from setMask_testBit I 1,
      show (setMask I).testBit 2 = decide ((2 : Fin 14) ∈ I) from setMask_testBit I 2,
      show (setMask I).testBit 3 = decide ((3 : Fin 14) ∈ I) from setMask_testBit I 3,
      show (setMask I).testBit 4 = decide ((4 : Fin 14) ∈ I) from setMask_testBit I 4,
      show (setMask I).testBit 5 = decide ((5 : Fin 14) ∈ I) from setMask_testBit I 5,
      show (setMask I).testBit 6 = decide ((6 : Fin 14) ∈ I) from setMask_testBit I 6,
      show (setMask I).testBit 7 = decide ((7 : Fin 14) ∈ I) from setMask_testBit I 7,
      show (setMask I).testBit 8 = decide ((8 : Fin 14) ∈ I) from setMask_testBit I 8,
      show (setMask I).testBit 9 = decide ((9 : Fin 14) ∈ I) from setMask_testBit I 9,
      show (setMask I).testBit 10 = decide ((10 : Fin 14) ∈ I) from setMask_testBit I 10,
      show (setMask I).testBit 11 = decide ((11 : Fin 14) ∈ I) from setMask_testBit I 11,
      show (setMask I).testBit 12 = decide ((12 : Fin 14) ∈ I) from setMask_testBit I 12,
      show (setMask I).testBit 13 = decide ((13 : Fin 14) ∈ I) from setMask_testBit I 13]
  simp only [decide_eq_true_eq]
  omega
theorem g14_canon_all : ∀ mL mR : Fin 128,
    let m := mL.val + 128 * mR.val
    isIndepOff0Mask m = true → 3 ≤ pop14 m →
    (findCanonIdx (autMask 0 m)).isSome || (findCanonIdx (autMask 1 m)).isSome ||
    (findCanonIdx (autMask 2 m)).isSome || (findCanonIdx (autMask 3 m)).isSome ||
    (findCanonIdx (autMask 4 m)).isSome || (findCanonIdx (autMask 5 m)).isSome ||
    (findCanonIdx (autMask 6 m)).isSome || (findCanonIdx (autMask 7 m)).isSome = true := by
  decide +kernel
theorem exists_aut_canon {I : Finset (Fin 14)} (hI : IsIndepOff0 I) (hge : 3 ≤ I.card) :
    ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI := by
  set m := setMask I with hm
  have hlt : m < 16384 := setMask_lt I
  have hmL : m % 128 < 128 := Nat.mod_lt _ (by decide)
  have hmR : m / 128 < 128 := by omega
  have hsplit : m % 128 + 128 * (m / 128) = m := by omega
  have hall := g14_canon_all ⟨m % 128, hmL⟩ ⟨m / 128, hmR⟩
  dsimp only at hall
  rw [hsplit] at hall
  have hres := hall (isIndepOff0Mask_of_indep hI) (by rw [pop14_eq_card]; exact hge)
  have hex : ∃ k : Fin 8, (findCanonIdx (autMask k m)).isSome = true := by
    simp only [Bool.or_eq_true] at hres
    rcases hres with ((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨4, h4⟩
    · exact ⟨5, h5⟩
    · exact ⟨6, h6⟩
    · exact ⟨7, h7⟩
  obtain ⟨k, hk⟩ := hex
  obtain ⟨idx, hidx⟩ := Option.isSome_iff_exists.1 hk
  refine ⟨autOf k, autOf_isAut k, mem_image.2 ⟨idx, mem_univ _, ?_⟩⟩
  apply setMask_inj
  rw [repMask_eq, setMask_image_aut, ← hm]
  exact (findCanonIdx_some _ _ hidx).symm
theorem g14_not_empty : ¬ G14Edge (fun _ => false) := by
  rintro ⟨_, _, _, h, _⟩; exact Bool.noConfusion h
theorem g14_not_single (v : Fin 14) : ¬ G14Edge (fun i => decide (i = v)) := by
  rw [g14Edge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  rw [ha, hb] at hab
  exact adj_irrefl v hab
theorem g14_pair {u v : Fin 14} (h : Adj u v) :
    G14Edge (fun i => decide (i = u) || decide (i = v)) :=
  (g14Edge_iff_adj _).2 ⟨u, v, h, by simp, by simp⟩
theorem g14_essential (i : Fin 14) : ∃ x y : Fin 14 → Bool,
    (∀ j, j ≠ i → x j = y j) ∧ G14Edge x ∧ ¬ G14Edge y := by
  obtain ⟨m, hm⟩ := card_pos.1 (degree_pos i)
  have hadj : Adj i m := g14_mem_nb.1 hm
  exact ⟨fun j => decide (j = i) || decide (j = m), fun j => decide (j = m),
    fun j hj => by simp [hj], g14_pair hadj, g14_not_single m⟩
def Correct (D : Dag) : Prop :=
  ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ G14Edge x
theorem g14_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x) :
    ∃ D : Dag, StrictLive 14 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h08 : Adj (0 : Fin 14) 10 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 14) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (g14_pair h08)⟩
      · exact ⟨fun _ => false, fun h => g14_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => g14_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := g14_essential i
      refine ⟨x, y, hxy, fun h => hy ((hC y).1 ?_)⟩
      rw [← h]; exact (hC x).2 hx)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩
theorem g14_supp_out {D : Dag} (hD : Correct D) : supp 14 D (outW 14 D) = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun v hv =>
    g14_not_single v ((hD _).mp (mem_supp.mp hv))
theorem g14_relabel (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) :
    StrictLive 14 (relabel σ D) ∧ Correct (relabel σ D) ∧
      (relabel σ D).length = D.length ∧
      totalSurplus 14 (relabel σ D) = totalSurplus 14 D ∧
      Bplus 14 (relabel σ D) = Bplus 14 D ∧ Bzero 14 (relabel σ D) = Bzero 14 D ∧
      eligSet 14 (relabel σ D) = (eligSet 14 D).image σ ∧
      ineligSet 14 (relabel σ D) = (ineligSet 14 D).image σ := by
  refine ⟨relabel_strictLive σ h, fun x => ?_, relabel_length σ D, relabel_totalSurplus σ D,
    relabel_Bplus σ h.1, relabel_Bzero σ h.1, relabel_eligSet σ h.1, relabel_ineligSet σ h.1⟩
  rw [relabel_out σ h.1 h.2.2 x, hD]
  exact g14Edge_aut σ hσ x
theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  simpa [ineligSet] using h
theorem g14_cover_iff_indep (D : Dag) :
    IsCoverOff0 (eligSet 14 D) ↔ IsIndepOff0 (ineligSet 14 D) := by
  constructor
  · intro hcov u hu v hv hu0 hv0 huv
    have h1 := mem_sdiff.mp hu
    have h2 := mem_sdiff.mp hv
    exact (hcov u v hu0 hv0 huv).elim h1.2 h2.2
  · intro hind u v hu0 hv0 huv
    by_contra hc; push Not at hc
    exact hind u (mem_sdiff.mpr ⟨mem_univ _, hc.1⟩)
      v (mem_sdiff.mpr ⟨mem_univ _, hc.2⟩) hu0 hv0 huv
theorem g14_wlog {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hind : IsIndepOff0 (ineligSet 14 D)) (hge : 3 ≤ (ineligSet 14 D).card) :
    ∃ D' : Dag, StrictLive 14 D' ∧ Correct D' ∧ D'.length = D.length ∧
      totalSurplus 14 D' = totalSurplus 14 D ∧
      Bplus 14 D' = Bplus 14 D ∧ Bzero 14 D' = Bzero 14 D ∧
      (ineligSet 14 D').card = (ineligSet 14 D).card ∧
      ineligSet 14 D' ∈ canonI := by
  obtain ⟨σ, hσ, hmem⟩ := exists_aut_canon hind hge
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := g14_relabel σ hσ h hD
  refine ⟨relabel σ D, h1, h2, h3, h4, h5, h6, ?_, h8 ▸ hmem⟩
  rw [h8, card_image_of_injective _ σ.injective]
theorem g14_budget {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 24) :
    totalSurplus 14 D = D.length - 13 ∧ totalSurplus 14 D ≤ 11 := by
  have := surplus_identity h
  exact ⟨by omega, by omega⟩
def WeakPureBranch14 (D : Dag) (b : Fin 14 → ℕ) : Prop :=
  ∀ v ∈ eligSet 14 D, 2 ≤ fanout D (b v) ∧ v ∈ supp 14 D (b v) ∧
    (v ≠ 0 → supp 14 D (b v) = {v}) ∧ (v = 0 → supp 14 D (b v) ⊆ {0, 4, 5})
theorem weak_reserved_inj (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet 14 D : Set (Fin 14)) := by
  intro u hu v hv heq
  have hbuv : b u = b v := congrArg Sigma.fst heq
  by_cases hu0 : u = 0
  · subst hu0
    by_cases hv0 : v = 0
    · exact hv0.symm
    · have h0m : (0 : Fin 14) ∈ supp 14 D (b 0) := (hb 0 hu).2.1
      rw [hbuv, (hb v hv).2.2.1 hv0, mem_singleton] at h0m
      exact absurd h0m.symm hv0
  · have hv' : v ∈ supp 14 D (b v) := (hb v hv).2.1
    rw [← hbuv, (hb u hu).2.2.1 hu0, mem_singleton] at hv'
    exact hv'.symm
theorem weak_reserved_subset (hS : Strict 14 D) (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b) :
    reservedUnits 14 D b ⊆ unitsPlus 14 D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
  obtain ⟨hf, hmem, -, -⟩ := hb v hv
  rw [unitsPlus, mem_filter, mem_units]
  exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b v) (by omega)),
    by show 0 + 1 < fanout D (b v); omega⟩, ⟨v, hmem⟩⟩
theorem weak_card_reserved (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b) :
    (reservedUnits 14 D b).card = (eligSet 14 D).card :=
  card_image_of_injOn (weak_reserved_inj b hb)
theorem weak_elig_le_Bplus (hS : Strict 14 D) (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b) :
    (eligSet 14 D).card ≤ Bplus 14 D := by
  rw [← weak_card_reserved b hb, ← card_unitsPlus]
  exact card_le_card (weak_reserved_subset hS b hb)
theorem weak_card_residual (hS : Strict 14 D) (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b) :
    (residualUnits 14 D b).card + (eligSet 14 D).card = Bplus 14 D := by
  rw [← weak_card_reserved b hb, ← card_unitsPlus]
  exact card_sdiff_add_card_eq_card (weak_reserved_subset hS b hb)
theorem weak_surplus_carrierT_eq (hS : Strict 14 D) (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b)
    (T : Finset (Fin 14))
    (hT : (0 : Fin 14) ∈ ineligSet 14 D ∨ (0 : Fin 14) ∈ T ∨ ((4 : Fin 14) ∉ T ∧ (5 : Fin 14) ∉ T)) :
    surplusOn D (carrierT 14 D T) = (T ∩ eligSet 14 D).card +
      ((residualUnits 14 D b).filter (fun u => (supp 14 D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT 14 D T) =
      ((units 14 D).filter (fun u => (supp 14 D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter 14 D (fun w => (supp 14 D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, mem_filter] at hw
      have hni : w ∉ inner 14 D := fun hc => hnot (mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units 14 D).filter (fun u => (supp 14 D u.1 ∩ T).Nonempty) =
      (reservedUnits 14 D b).filter (fun u => (supp 14 D u.1 ∩ T).Nonempty) ∪
        (residualUnits 14 D b).filter (fun u => (supp 14 D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := weak_reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, mem_union, mem_filter, mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits 14 D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits 14 D b).filter (fun u => (supp 14 D u.1 ∩ T).Nonempty))
      ((residualUnits 14 D b).filter (fun u => (supp 14 D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits 14 D b).filter (fun u => (supp 14 D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet 14 D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [mem_filter, mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      by_cases hv0 : v = 0
      · subst hv0
        rcases hT with h0I | h0T | ⟨h4T, h5T⟩
        · exact absurd hv (mem_sdiff.mp h0I).2
        · exact ⟨h0T, hv⟩
        · obtain ⟨x, hx⟩ := hne
          rw [mem_inter] at hx
          have hsub := (hb 0 hv).2.2.2 rfl hx.1
          simp only [mem_insert, mem_singleton] at hsub
          rcases hsub with rfl | rfl | rfl
          · exact ⟨hx.2, hv⟩
          · exact absurd hx.2 h4T
          · exact absurd hx.2 h5T
      · rw [(hb v hv).2.2.1 hv0, sb_singleton_inter_nonempty] at hne
        exact ⟨hne, hv⟩
    · rintro ⟨hT', hv⟩
      exact ⟨hv, ⟨v, mem_inter.mpr ⟨(hb v hv).2.1, hT'⟩⟩⟩
  rw [h1, h2, card_union_of_disjoint h3, h4,
    card_image_of_injOn ((weak_reserved_inj b hb).mono
      (Finset.coe_subset.mpr inter_subset_right))]
theorem weak_surplus_carrierT_le (hS : Strict 14 D) (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b)
    (T : Finset (Fin 14))
    (hT : (0 : Fin 14) ∈ ineligSet 14 D ∨ (0 : Fin 14) ∈ T ∨ ((4 : Fin 14) ∉ T ∧ (5 : Fin 14) ∉ T)) :
    surplusOn D (carrierT 14 D T) + (eligSet 14 D).card ≤
      (T ∩ eligSet 14 D).card + Bplus 14 D := by
  have h1 := weak_surplus_carrierT_eq hS b hb T hT
  have h2 := weak_card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits 14 D b)
    (fun u => (supp 14 D u.1 ∩ T).Nonempty)
  omega
theorem weak_to_pure (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b)
    (h0 : (0 : Fin 14) ∈ ineligSet 14 D) : PureBranch 14 D b := fun v hv =>
  ⟨(hb v hv).1, (hb v hv).2.2.1 (fun hv0 => (mem_sdiff.mp h0).2 (hv0 ▸ hv))⟩
def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true
def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x
def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧
    (∀ u, ∃ a, G u a) ∧ (∀ u v, G u v → (∃ a, G u a ∧ a ≠ v) ∨ (∃ a, G v a ∧ a ≠ u))
def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)
def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)
def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i
def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)
theorem sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)
section SemCore
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]
theorem sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]
theorem sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]
theorem sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu
theorem sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)
theorem sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact notMem_empty v hv
theorem sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]
theorem sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]
theorem sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact inter_subset_left
  · rw [sb_src_true]; exact inter_subset_right
theorem sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb
theorem sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm
theorem sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm
theorem sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm
theorem sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega
theorem sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [mem_filter, mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩
theorem sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  card_pos.mpr ⟨_, sem_step_reader h⟩
theorem sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega
theorem sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]
def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)
theorem sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))
def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b
theorem sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest
theorem sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (mem_inter.mp hv).1)
      · rcases mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)
theorem sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac
theorem sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩
theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))
theorem sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hsep : ∀ u : Fin n, u ≠ v → ∃ z, G v z ∧ ¬ G u z)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, -, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep u huv
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  exact h1 ((hC _).mp (hout.trans ((hC _).mpr h2)))
def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)
theorem sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]
theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)
theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hsep : ∀ u : Fin n, u ≠ v → ∃ z, G v z ∧ ¬ G u z)
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v hsep w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (singleton_subset_iff.mpr hw)
theorem sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, mem_filter, mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [mem_inter, mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, mem_inter.mpr ⟨h, mem_singleton_self v⟩⟩
theorem sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, mem_filter, mem_product, mem_range,
    mem_univ, and_true, sem_mem_carrier1]
theorem sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega
theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩
theorem sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hsep : ∀ u : Fin n, u ≠ v → ∃ z, G v z ∧ ¬ G u z) (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0⟩ := hG.2.2.1 v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := card_eq_one.mp hcard
  rw [he, mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hsep hv
      (sem_mem_exit1.mp (by rw [he]; exact mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha
theorem sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n}
    (hsepu : ∀ w : Fin n, w ≠ u → ∃ z, G u z ∧ ¬ G w z)
    (hsepv : ∀ w : Fin n, w ≠ v → ∃ z, G v z ∧ ¬ G w z)
    (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, hsu, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC hsepu (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, hnv, hxv, -⟩ := sem_inelig_consumer hG h hC hsepv (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, mem_singleton] at m1
  rw [hxv, mem_singleton] at m2
  subst m1
  subst m2
  rcases hG.2.2.2 u v huv with ⟨a, hua, hav⟩ | ⟨a, hva, hau⟩
  · have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
    rw [hsv, mem_singleton] at h5
    exact hav h5
  · have h5 : a ∈ supp n D (src D (j, !(!s))) := hnv a hva
    rw [Bool.not_not, hsu, mem_singleton] at h5
    exact hau h5
theorem sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac
theorem sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ x ∈ supp n D (src D (j, s)) ∧
      x ∉ supp n D (n + j) ∧ Disjoint (supp n D (src D (j, s))) A := by
  by_contra hcon
  have hmask : ∀ j s, j < D.length → tag D j = true → x ∈ supp n D (src D (j, s)) →
      x ∉ supp n D (n + j) → val D (sem_ind A) (src D (j, s)) = true ∧
        val D (sem_ins x (sem_ind A)) (src D (j, s)) = true := by
    intro j s hj ht h1 h2
    have hnd : ¬ Disjoint (supp n D (src D (j, s))) A :=
      fun hd => hcon ⟨j, s, hj, ht, h1, h2, hd⟩
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨a, ha1, ha2⟩ := hnd
    exact ⟨sem_val_of_supp hS ha1 (by simp [sem_ind, ha2]),
      sem_val_of_supp hS ha1 (by simp [sem_ins, sem_ind, ha2])⟩
  have key : ∀ w, x ∉ supp n D w → val D (sem_ind A) w = val D (sem_ins x (sem_ind A)) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn, val_input D _ w hn]
        have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
        rw [hs, mem_singleton] at hw
        exact sem_ins_agree x _ _ (fun hc => hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [val_gate hS _ j hj, val_gate hS _ j hj]
          cases ht : tag D j
          · rw [sem_supp_or hS hj ht, mem_union, not_or] at hw
            rw [ih _ ha hw.1, ih _ hb hw.2]
          · have hw2 := hw
            rw [sem_supp_and hS hj ht, mem_inter, not_and] at hw2
            by_cases hxa : x ∈ supp n D (opA D j)
            · have h1 := hmask j false hj ht (by rw [sb_src_false]; exact hxa) hw
              rw [sb_src_false] at h1
              rw [ih _ hb (hw2 hxa), h1.1, h1.2]
            · by_cases hxb : x ∈ supp n D (opB D j)
              · have h1 := hmask j true hj ht (by rw [sb_src_true]; exact hxb) hw
                rw [sb_src_true] at h1
                rw [ih _ ha hxa, h1.1, h1.2]
              · rw [ih _ ha hxa, ih _ hb hxb]
        · rw [val_ge D _ w (by omega), val_ge D _ w (by omega)]
  have hout := key (outW n D) (by rw [sem_supp_out hG hC]; exact notMem_empty x)
  obtain ⟨a, ha, hxa⟩ := hnb
  have h2 : sem_Edge G (sem_ins x (sem_ind A)) :=
    ⟨x, a, hxa, sem_ins_self x _, by simp [sem_ins, sem_ind, ha]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA ((hC _).mp h3)
theorem sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact mem_filter.mpr ⟨mem_range.mpr
      (sem_supp_lt (mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (card_le_card inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [mem_inter] at hv
        exact ⟨⟨v, mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, mem_filter, mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩
end SemCore
theorem sem_g14_has_nbr : ∀ u : Fin 14, ∃ a, hc_adjB u a = true := by decide +kernel
theorem sem_g14_edge_deg : ∀ u v : Fin 14, hc_adjB u v = true →
    (∃ a, hc_adjB u a = true ∧ a ≠ v) ∨ (∃ a, hc_adjB v a = true ∧ a ≠ u) := by decide +kernel
theorem sem_g14_second_ne0 : ∀ u v : Fin 14, u ≠ 0 → ∃ a, hc_adjB u a = true ∧ a ≠ v := by decide +kernel
theorem sem_g14_gr : sem_Gr (fun u v : Fin 14 => Adj u v) :=
  ⟨fun _ _ => adj_symm, adj_irrefl,
    fun u => by obtain ⟨a, ha⟩ := sem_g14_has_nbr u; exact ⟨a, (hc_adjB_iff u a).mp ha⟩,
    fun u v huv => by
      rcases sem_g14_edge_deg u v ((hc_adjB_iff u v).mpr huv) with ⟨a, h1, h2⟩ | ⟨a, h1, h2⟩
      · exact Or.inl ⟨a, (hc_adjB_iff u a).mp h1, h2⟩
      · exact Or.inr ⟨a, (hc_adjB_iff v a).mp h1, h2⟩⟩
theorem sem_g14_comp {D : Dag} (hD : Correct D) : sem_Comp 14 (fun u v : Fin 14 => Adj u v) D :=
  fun x => (hD x).trans (g14Edge_iff_adj x)
theorem sem_dom_sub0 {D : Dag} (hS : Strict 14 D) (hD : Correct D) (b : ℕ)
    (hdom : sem_Dom 14 D b (0 : Fin 14).val) : supp 14 D b ⊆ {0, 4, 5} := by
  intro u hu
  simp only [mem_insert, mem_singleton]
  by_contra hne
  push Not at hne
  obtain ⟨h010, hu10⟩ := zero_sub_045 u hne.1 hne.2.1 hne.2.2
  have hxb : val D (sem_two u 10) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins 0 (sem_two u 10)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ 0 (sem_ins_agree 0 (sem_two u 10)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge (fun a c : Fin 14 => Adj a c) (sem_two u 10) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
    · exact adj_irrefl _ hac
    · exact hu10 hac
    · exact hu10 (adj_symm hac)
    · exact adj_irrefl _ hac
  have h2 : sem_Edge (fun a c : Fin 14 => Adj a c) (sem_ins 0 (sem_two u 10)) :=
    ⟨0, 10, h010, sem_ins_self 0 _, by simp [sem_ins, sem_two]⟩
  exact h1 ((sem_g14_comp hD _).mp (hout.trans ((sem_g14_comp hD _).mpr h2)))
theorem exists_weakPureBranch {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ b : Fin 14 → ℕ, WeakPureBranch14 D b := by
  classical
  have hS := h.1
  have hC := sem_g14_comp hD
  have hex : ∀ v : Fin 14, ∃ b, v ∈ eligSet 14 D →
      2 ≤ fanout D b ∧ v ∈ supp 14 D b ∧
      (v ≠ 0 → supp 14 D b = {v}) ∧ (v = 0 → supp 14 D b ⊆ {0, 4, 5}) := by
    intro v
    by_cases hv : v ∈ eligSet 14 D
    · have hexv : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp 14 D w := mem_eligSet.mp hv
      obtain ⟨h1, h2⟩ := Nat.find_spec hexv
      have hch : sem_Chain 14 D v.val (Nat.find hexv) :=
        sem_carrier_chain hS v _ h2 (fun u hu huv => by
          have := Nat.find_min hexv hu; by_contra hc; exact this ⟨by omega, huv⟩)
      refine ⟨Nat.find hexv, fun _ => ⟨h1, h2, fun hv0 => ?_, fun hv0 => ?_⟩⟩
      · exact Finset.Subset.antisymm
          (sem_dom_pure sem_g14_gr hS hC v (fun u hu => nbr_diff_exists v u hu.symm hv0) _ (sem_chain_dom hS hch))
          (singleton_subset_iff.mpr h2)
      · subst hv0; exact sem_dom_sub0 hS hD _ (sem_chain_dom hS hch)
    · exact ⟨0, fun hc => absurd hc hv⟩
  choose b hb using hex
  exact ⟨b, fun v hv => hb v hv⟩
theorem exists_pureBranch_of0 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h0 : (0 : Fin 14) ∈ ineligSet 14 D) : ∃ b : Fin 14 → ℕ, PureBranch 14 D b := by
  obtain ⟨b, hb⟩ := exists_weakPureBranch h hD
  exact ⟨b, weak_to_pure b hb h0⟩
theorem elig_isCoverOff0 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    IsCoverOff0 (eligSet 14 D) :=
  fun u v hu0 hv0 huv => sem_elig_cover sem_g14_gr h (sem_g14_comp hD)
    (fun w hw => nbr_diff_exists u w hw.symm hu0) (fun w hw => nbr_diff_exists v w hw.symm hv0) huv
theorem g14_wlog_canon (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x)
    (hsize : C.size ≤ 24) :
    ∃ D : Dag, StrictLive 14 D ∧ Correct D ∧ D.length ≤ 24 ∧
      totalSurplus 14 D ≤ 11 ∧ 3 ≤ (ineligSet 14 D).card ∧ ineligSet 14 D ∈ canonI := by
  obtain ⟨D0, h0, hlen0, hD0⟩ := g14_normalize C hmono hC
  have hlen : D0.length ≤ 24 := by omega
  obtain ⟨b, hb⟩ := exists_weakPureBranch h0 hD0
  have hcov := elig_isCoverOff0 h0 hD0
  have hge3 : 3 ≤ (ineligSet 14 D0).card := by
    have h1 := weak_elig_le_Bplus h0.1 b hb
    have h2 := Bplus_le_total 14 D0
    have h3 := (g14_budget h0 hlen).2
    have h4 := inelig_card_add 14 D0
    omega
  obtain ⟨D, h1, h2, h3, -, -, -, -, h8⟩ :=
    g14_wlog h0 hD0 ((g14_cover_iff_indep D0).mp hcov) hge3
  have hlen' : D.length ≤ 24 := by omega
  obtain ⟨b', hb'⟩ := exists_weakPureBranch h1 h2
  have hge3' : 3 ≤ (ineligSet 14 D).card := by
    have ha := weak_elig_le_Bplus h1.1 b' hb'
    have hb0 := Bplus_le_total 14 D
    have hc := (g14_budget h1 hlen').2
    have hd := inelig_card_add 14 D
    omega
  exact ⟨D, h1, h2, hlen', (g14_budget h1 hlen').2, hge3', h8⟩
theorem sem_inelig_consumer_zero {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h0 : (0 : Fin 14) ∈ ineligSet 14 D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      (0 : Fin 14) ∈ supp 14 D (src D e) ∧ supp 14 D (src D e) ⊆ {0, 4, 5} ∧
      supp 14 D (14 + e.1) ⊆ {4, 5} ∧ (10 : Fin 14) ∈ supp 14 D (src D (e.1, !e.2)) ∧
      exitArcs 14 D (carrierT 14 D {0}) = {e} ∧ merges 14 D (carrierT 14 D {0}) = ∅ := by
  have hS := h.1
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  have hfl := carrier_flow_union h ({0} : Finset (Fin 14)) (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus h0, card_singleton] at hfl
  obtain ⟨j0, hj0, ht0, -, hju0, -, s0, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC (by decide : Adj 0 10)
  have hm0 : (j0, s0) ∈ exitArcs 14 D (carrierT 14 D {0}) := sem_mem_exit1.mpr ⟨hj0, h1, hju0⟩
  have hcard : (exitArcs 14 D (carrierT 14 D {0})).card = 1 := by
    have := card_pos.mpr ⟨_, hm0⟩; omega
  have hmer : merges 14 D (carrierT 14 D {0}) = ∅ := card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := card_eq_one.mp hcard
  rw [he, mem_singleton] at hm0
  subst hm0
  have hsub : supp 14 D (src D (j0, s0)) ⊆ {0, 4, 5} :=
    sem_dom_sub0 hS hD _ (sem_chain_dom hS (sem_inelig_chain hS h0 h1))
  refine ⟨(j0, s0), hj0, ht0, h1, hsub, ?_, h3, he, hmer⟩
  intro x hx
  have hx1 := hsub (sem_supp_and_sub hS hj0 ht0 s0 hx)
  simp only [mem_insert, mem_singleton] at hx1 ⊢
  rcases hx1 with rfl | rfl | rfl
  · exact absurd hx hju0
  · exact Or.inl rfl
  · exact Or.inr rfl
def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})
def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)
section SemCodes
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1
theorem sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]
theorem sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2
theorem sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]
theorem sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
    tag D e.1 = true := by
  obtain ⟨hj, h1, h2⟩ := sem_mem_W.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [sem_supp_or hS hj ht, mem_union]
  obtain ⟨j, s⟩ := e
  cases s
  · left; simpa [src] using h1
  · right; simpa [src] using h1
theorem sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [card_singleton] at h1
theorem sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩
theorem sem_cover_free (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x a b y : Fin n} (hab : ¬ G a b) (hxy : G x y) (hya : ¬ G y a) (hyb : ¬ G y b) :
    ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) ∧ b ∉ supp n D (src D e) := by
  have hsym := hG.1
  have hirr := hG.2.1
  have hA : ∀ u ∈ ({a, b, y} : Finset (Fin n)), ∀ v ∈ ({a, b, y} : Finset (Fin n)),
      ¬ G u v := by
    intro u hu v hv
    simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
    · exact hirr a
    · exact hab
    · exact fun h => hya (hsym _ _ h)
    · exact fun h => hab (hsym _ _ h)
    · exact hirr b
    · exact fun h => hyb (hsym _ _ h)
    · exact hya
    · exact hyb
    · exact hirr y
  obtain ⟨j, s, hj, -, h1, h2, hd⟩ := sem_exposure hG hS hC {a, b, y} hA x ⟨y, by simp, hxy⟩
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, h2⟩, fun h => disjoint_left.mp hd h (by simp),
    fun h => disjoint_left.mp hd h (by simp)⟩
theorem sem_antichain (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x a : Fin n}
    (hdiff : ∃ z, G x z ∧ ¬ G a z) : ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) := by
  obtain ⟨z, hxz, haz⟩ := hdiff
  obtain ⟨e, he, h1, -⟩ := sem_cover_free hG hS hC (a := a) (b := a) (hG.2.1 a) hxz
    (fun h => haz (hG.1 _ _ h)) (fun h => haz (hG.1 _ _ h))
  exact ⟨e, he, h1⟩
end SemCodes
theorem sem_rtg_comparable {α : Type} {R : α → α → Prop}
    (hfun : ∀ a a' b, R a b → R a' b → a = a') {u v c : α}
    (hu : Relation.ReflTransGen R u c) (hv : Relation.ReflTransGen R v c) :
    Relation.ReflTransGen R u v ∨ Relation.ReflTransGen R v u := by
  induction hu with
  | refl => exact Or.inr hv
  | tail hab hbc ih =>
    rcases Relation.ReflTransGen.cases_tail hv with h | ⟨b', hvb', hb'c⟩
    · left
      rw [← h]
      exact Relation.ReflTransGen.tail hab hbc
    · have hbb : b' = _ := hfun _ _ _ hb'c hbc
      rw [hbb] at hvb'
      exact ih hvb'
def sem_MinBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v) ∧
    ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b v ≤ w
def sem_Arm (n : ℕ) (D : Dag) (X : Finset (Fin n)) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ fanout D a = 1 ∧ ∀ x ∈ X, x ∈ supp n D a ∧ x ∈ supp n D b
section SemArms
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))
theorem sem_minBranch_first {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : sem_FirstBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1, (hb v hv).2.2.1⟩
theorem sem_minBranch_pure {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩
theorem sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) (hx : x ∈ supp n D (n + j)) :
    tag D j = false ∧ ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
  have hnot : ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
    intro hc
    have hm : j ∈ merges n D (carrierT n D {x}) := by
      rw [merges, mem_filter, mem_range]
      exact ⟨hj, sem_mem_carrier1.mpr hx, sem_mem_carrier1.mpr hc.1, sem_mem_carrier1.mpr hc.2⟩
    rw [hM] at hm
    exact notMem_empty _ hm
  refine ⟨?_, hnot⟩
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rw [sem_supp_and hS hj ht, mem_inter] at hx
  exact hnot hx
theorem sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + (({x} : Finset (Fin n)) ∩ eligSet n D).card +
        ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).card := by
  have h1 := sem_flow1 hG h hC x
  have h2 := surplus_carrierT_eq h.1 b hb {x}
  have h3 : (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ {x}).Nonempty) =
      (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) := by
    refine Finset.filter_congr (fun u _ => ?_)
    constructor
    · rintro ⟨y, hy⟩
      rw [mem_inter, mem_singleton] at hy
      exact hy.2 ▸ hy.1
    · intro hx
      exact ⟨x, mem_inter.mpr ⟨hx, mem_singleton_self x⟩⟩
  rw [h3] at h2
  omega
theorem sem_descent (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) :
    ∀ c, (∀ x ∈ X, x ∈ supp n D c) →
      (∀ x ∈ X, ∀ w, c ≤ w → x ∈ supp n D w → fanout D w ≤ 1) →
      ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
        Relation.ReflTransGen (sem_Arm n D X) c (src D e) := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  intro c
  generalize hk : n + D.length - c = k
  induction k using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro hc hlow
    have hclt := sem_supp_lt (hc x0 hx0)
    have hcne : c ≠ outW n D := by
      intro he
      have := hc x0 hx0
      rw [he, sem_supp_out hG hC] at this
      exact notMem_empty _ this
    have hf1 : 1 ≤ fanout D c := h.2.1 c (by unfold outW at hcne; omega)
    have hf : fanout D c = 1 := le_antisymm (hlow x0 hx0 c (le_refl c) (hc x0 hx0)) hf1
    obtain ⟨j, hjr⟩ := card_pos.mp hf1
    simp only [readers, mem_filter, mem_range] at hjr
    obtain ⟨hj, hop⟩ := hjr
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = c := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    have hcj : c < n + j := hs ▸ sem_src_lt hS hj s
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hj hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hj ht, mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hc x hx
        · right; rw [h1]; exact hc x hx
      obtain ⟨e, he1, he2⟩ := ih (n + D.length - (n + j)) (by omega) (n + j) rfl hall
        (fun x hx w hw => hlow x hx w (by omega))
      refine ⟨e, he1, Relation.ReflTransGen.head ⟨?_, hf, fun x hx => ⟨hc x hx, hall x hx⟩⟩ he2⟩
      rw [← hs]
      exact sem_step_src hj s
    · refine ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hj, ?_, fun hc2 => hcar ⟨x, hx, hc2⟩⟩, ?_⟩
      · rw [hs]; exact hc x hx
      · rw [hs]
theorem sem_two_arms (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (show 1 < (readers D r).card from hf)
  have hread : ∀ j ∈ readers D r, j < D.length ∧ r < n + j ∧ (opA D j = r ∨ opB D j = r) := by
    intro j hj
    simp only [readers, mem_filter, mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D r, ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
      ((e.1 = j ∧ src D e = r) ∨ Relation.ReflTransGen (sem_Arm n D X) (n + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hrj, hop⟩ := hread j hj
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = r := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hjl hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hjl ht, mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hr x hx
        · right; rw [h1]; exact hr x hx
      obtain ⟨e, he1, he2⟩ := sem_descent hG h hC X ⟨x0, hx0⟩ hM (n + j) hall
        (fun x hx w hw => hlow x hx w (by omega))
      exact ⟨e, he1, Or.inr he2⟩
    · exact ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hjl, by rw [hs]; exact hr x hx,
        fun hc2 => hcar ⟨x, hx, hc2⟩⟩, Or.inl ⟨rfl, hs⟩⟩
  have hRstep : ∀ a b, sem_Arm n D X a b → sem_step n D a b := fun _ _ hab => hab.1
  have hfun : ∀ a a' b, sem_Arm n D X a b → sem_Arm n D X a' b → a = a' := by
    intro a a' b h1 h2
    by_contra hne2
    obtain ⟨hb1, hb2, hba⟩ := h1.1
    obtain ⟨-, -, hba'⟩ := h2.1
    have hjb : b - n < D.length := by omega
    have hcarb : x0 ∈ supp n D (n + (b - n)) := by
      rw [Nat.add_sub_cancel' hb2]; exact (h1.2.2 x0 hx0).2
    apply (sem_zm_gate hS (hM x0 hx0) hjb hcarb).2
    have ha := (h1.2.2 x0 hx0).1
    have ha' := (h2.2.2 x0 hx0).1
    rcases hba with e1 | e1 <;> rcases hba' with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D r, ∀ jb ∈ readers D r, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm n D X) (n + ja) (n + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨hjla, hrja, -⟩ := hread ja hja
    obtain ⟨hjlb, hrjb, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hle := sem_rtg_le hS hRstep hu1
      have hur : u = r := by
        by_contra hur
        obtain ⟨-, -, hbu⟩ := hu2.1
        rw [Nat.add_sub_cancel_left] at hbu
        apply (sem_zm_gate hS (hM x0 hx0) hjlb (hu2.2.2 x0 hx0).2).2
        have hu := (hu2.2.2 x0 hx0).1
        have hrr := hr x0 hx0
        rcases hbu with e1 | e1 <;> rcases hopb with e2 | e2
        · exact absurd (e1.symm.trans e2) hur
        · rw [e1, e2]; exact ⟨hu, hrr⟩
        · rw [e1, e2]; exact ⟨hrr, hu⟩
        · exact absurd (e1.symm.trans e2) hur
      omega
  obtain ⟨P, hP1, hP2⟩ := hterm j1 hj1
  obtain ⟨Q, hQ1, hQ2⟩ := hterm j2 hj2
  refine ⟨P, Q, fun hPQ => ?_, fun x hx => ⟨hP1 x hx, hQ1 x hx⟩⟩
  have hsame : Q = P := by
    rcases sem_same_gate hPQ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨hjP, hxP, hnP⟩ := sem_mem_W.mp (hP1 x0 hx0)
      have hxQ := (sem_mem_W.mp (hQ1 x0 hx0)).2.1
      rw [h1] at hxQ
      apply hnP
      rw [sem_supp_and hS hjP (sem_W_and hS (hP1 x0 hx0)), mem_inter]
      obtain ⟨j, s⟩ := P
      cases s
      · exact ⟨by simpa [src] using hxP, by simpa [src, sem_bar] using hxQ⟩
      · exact ⟨by simpa [src, sem_bar] using hxQ, by simpa [src] using hxP⟩
  rw [hsame] at hQ2
  obtain ⟨-, hrj1, -⟩ := hread j1 hj1
  obtain ⟨-, hrj2, -⟩ := hread j2 hj2
  rcases hP2 with ⟨hPa, hPb⟩ | hPp <;> rcases hQ2 with ⟨hQa, hQb⟩ | hQp
  · exact hne (hPa.symm.trans hQa)
  · have := sem_rtg_le hS hRstep hQp
    omega
  · have := sem_rtg_le hS hRstep hPp
    omega
  · rcases sem_rtg_comparable hfun hPp hQp with h1 | h1
    · exact hcross j1 hj1 j2 hj2 hne h1
    · exact hcross j2 hj2 j1 hj1 (Ne.symm hne) h1
theorem sem_saturated (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {u0 : Σ _ : ℕ, ℕ}
    (hres : residualUnits n D b = {u0}) {x : Fin n} (hsat : 3 ≤ (sem_W n D x).card) :
    (sem_W n D x).card = 3 ∧ merges n D (carrierT n D {x}) = ∅ ∧ x ∈ eligSet n D ∧
      x ∈ supp n D u0.1 := by
  have h1 := sem_code_count hG h hC b hb x
  have h2 : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (card_le_card inter_subset_left).trans (by simp)
  have h3 := Finset.card_filter_le (residualUnits n D b) (fun u => x ∈ supp n D u.1)
  rw [hres, card_singleton] at h3
  rw [hres] at h1
  refine ⟨by omega, card_eq_zero.mp (by omega), ?_, ?_⟩
  · by_contra hx
    have h4 : ({x} : Finset (Fin n)) ∩ eligSet n D = ∅ := by
      rw [Finset.singleton_inter_of_notMem hx]
    rw [h4, card_empty] at h1
    omega
  · have h4 : 0 < (({u0} : Finset (Σ _ : ℕ, ℕ)).filter (fun u => x ∈ supp n D u.1)).card := by
      omega
    obtain ⟨u, hu⟩ := card_pos.mp h4
    rw [mem_filter, mem_singleton] at hu
    exact hu.1 ▸ hu.2
end SemArms
section SemPaths
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem sem_ind_single (a : Fin n) : sem_ind ({a} : Finset (Fin n)) = single a := by
  funext k; simp [sem_ind, single]
theorem sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]
theorem sem_ins_ind_edge (hG : sem_Gr G) {i : Fin n} {S : Finset (Fin n)}
    (h : sem_Edge G (sem_ins i (sem_ind S))) :
    (∃ a ∈ S, G i a) ∨ ∃ a ∈ S, ∃ b ∈ S, G a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv] at huv; exact absurd huv (hG.2.1 i)
  · rw [hu] at huv; exact Or.inl ⟨v, hv, huv⟩
  · rw [hv] at huv; exact Or.inl ⟨u, hu, hG.1 _ _ huv⟩
  · exact Or.inr ⟨u, hu, v, hv, huv⟩
theorem sem_chain_dom_at (hS : Strict n D) {v b t : ℕ} (h : sem_Chain n D v b) (hbt : b ≤ t) :
    b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep hrest ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest'⟩
      · have h1 := sem_step_lt hS hstep.1
        have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest'
theorem sem_dom_eq_at (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b t : ℕ)
    (hdom : b = v.val ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v.val t)
    (hb : val D x b = val D y b) : val D x t = val D y t := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))
theorem sem_chain_fork (hS : Strict n D) {a c q : ℕ} (hc : sem_Chain n D a c)
    (hq : Relation.ReflTransGen (sem_step n D) a q) :
    Relation.ReflTransGen (sem_step n D) c q ∨ (sem_Chain n D q c ∧ q ≠ c) := by
  revert hq
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hq => Or.inl hq
  | @head a a' hstep hrest ih =>
    intro hq
    rcases Relation.ReflTransGen.cases_head hq with heq | ⟨a'', hs, hrest'⟩
    · right
      have h1 := sem_step_lt hS hstep.1
      have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
      refine ⟨?_, by omega⟩
      rw [← heq]
      exact Relation.ReflTransGen.head hstep hrest
    · have hcc : a' = a'' := sem_step_unique hstep.1 hs hstep.2
      subst hcc
      exact ih hrest'
theorem sem_sibling_indep (hS : Strict n D) (v : Fin n) {j : ℕ} (hj : j < D.length) (s : Bool)
    (hch : sem_Chain n D v.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (x y : Fin n → Bool) (hxy : ∀ k, k ≠ v → x k = y k) :
    val D x (src D (j, s)) = val D y (src D (j, s)) := by
  by_contra hne
  have hp : Relation.ReflTransGen (sem_step n D) v.val (src D (j, s)) :=
    sem_rtg_mono (fun _ _ h => h.1) (sem_changed_path hS x y v hxy _ hne)
  have hstepc : sem_step n D (src D (j, !s)) (n + j) := sem_step_src hj (!s)
  have hstepq : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
  have hlt1 := sem_src_lt hS hj s
  have hlt2 := sem_src_lt hS hj (!s)
  rcases sem_chain_fork hS hch hp with h1 | ⟨h1, h2⟩
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨c', hs, hrest⟩
    · exact sem_src_ne hS hj s heq.symm
    · have hcc : n + j = c' := sem_step_unique hstepc hs hf
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h) hrest
      omega
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨q', hs, hrest⟩
    · exact h2 heq
    · have hcc : n + j = q' := sem_step_unique hstepq hs.1 hs.2
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h.1) hrest
      omega
theorem sem_dom_split (hS : Strict n D) (hC : sem_Comp n G D) (x : Fin n → Bool) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) (h0 : ¬ sem_Edge G x) (h1 : sem_Edge G (sem_ins v x)) :
    val D x b = false ∧ val D (sem_ins v x) b = true := by
  have hne : val D x b ≠ val D (sem_ins v x) b := by
    intro heq
    have h2 := sem_dom_eq hS x _ v (sem_ins_agree v x) b hdom heq
    exact h0 ((hC x).mp (by rw [h2]; exact (hC _).mpr h1))
  have hmono := val_mono hS x (sem_ins v x) (sem_ins_ge v x) b
  cases hx : val D x b
  · refine ⟨rfl, ?_⟩
    cases hy : val D (sem_ins v x) b
    · exact absurd (hx.trans hy.symm) hne
    · rfl
  · exact absurd (hx.trans (hmono hx).symm) hne
theorem sem_factor (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs N : Finset (Fin n)) (hN : N ⊆ Bs)
    (h0 : val D (sem_ins i (sem_ind (Bs \ N))) w = false)
    (h1 : ∀ a ∈ N, val D (sem_ins i (sem_ind {a})) w = true)
    (hz : ∀ a ∈ N, val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧ supp n D (src D (j, s)) ∩ Bs = N := by
  have hJ : ∀ c, sem_Chain n D i.val c → (val D (sem_ins i (sem_ind (Bs \ N))) c = true ∨
      ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ c ∧ sem_Chain n D i.val (src D (j, !s)) ∧
        fanout D (src D (j, !s)) = 1 ∧ val D (sem_ind (Bs \ N)) (src D (j, s)) = false) := by
    intro c hc
    induction hc with
    | refl => left; rw [val_input D _ _ i.isLt]; exact sem_ins_self i _
    | tail hab hbc ih =>
      obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hbc.1
      have hlt := sem_src_lt hS hj s
      rcases ih with hy | ⟨j', s', hj', ht', hle, hc', hf', hv'⟩
      · cases ht : tag D j
        · left
          rw [sem_val_gate_src hS _ hj s, ht, gop_false, hy]
          rfl
        · by_cases hq : val D (sem_ins i (sem_ind (Bs \ N))) (src D (j, !s)) = true
          · left
            rw [sem_val_gate_src hS _ hj s, ht, gop_true, hy, hq]
            rfl
          · right
            refine ⟨j, !s, hj, ht, le_refl _, by rw [Bool.not_not]; exact hab,
              by rw [Bool.not_not]; exact hbc.2, ?_⟩
            by_contra hc2
            rw [Bool.not_eq_false] at hc2
            exact hq (val_mono hS _ _ (sem_ins_ge i _) _ hc2)
      · right
        exact ⟨j', s', hj', ht', by omega, hc', hf', hv'⟩
  rcases hJ w hch with hy | ⟨j, s, hj, ht, hle, hc, hf, hv⟩
  · rw [h0] at hy
    exact absurd hy Bool.false_ne_true
  · refine ⟨j, s, hj, ht, hle, hc, ?_⟩
    have hchg : sem_Chain n D i.val (n + j) :=
      Relation.ReflTransGen.tail hc ⟨sem_step_src hj (!s), hf⟩
    ext a
    rw [mem_inter]
    constructor
    · rintro ⟨ha1, ha2⟩
      by_contra haN
      have := sem_val_of_supp hS ha1 (x := sem_ind (Bs \ N))
        (by simp [sem_ind, ha2, haN])
      rw [hv] at this
      exact Bool.false_ne_true this
    · intro haN
      refine ⟨?_, hN haN⟩
      have hgne : val D (sem_ind {a}) (n + j) ≠ val D (sem_ins i (sem_ind {a})) (n + j) := by
        intro heq
        have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (sem_ind {a})) (n + j) w
          (sem_chain_dom_at hS hchg hle) heq
        rw [hz a haN, h1 a haN] at h2
        exact Bool.false_ne_true h2
      have hgy : val D (sem_ins i (sem_ind {a})) (n + j) = true := by
        by_contra hc2
        rw [Bool.not_eq_true] at hc2
        apply hgne
        rw [hc2]
        by_contra hc3
        rw [Bool.not_eq_false] at hc3
        rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
        exact Bool.noConfusion hc2
      rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
      have hind := sem_sibling_indep hS i hj s hc hf _ _ (sem_ins_agree i (sem_ind {a}))
      rw [hgy.1, sem_ind_single] at hind
      exact mem_supp.mpr hind
theorem sem_exact_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n), S ⊆ Bs → (∀ a ∈ S, ¬ G i a) →
      val D (sem_ins i (sem_ind S)) w = false)
    (h1 : ∀ a ∈ Bs, G i a →
      val D (sem_ins i (sem_ind {a})) w = true ∧ val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  classical
  obtain ⟨j, s, hj, ht, hle, hc, hsupp⟩ := sem_factor hS i w hch Bs (Bs.filter (fun a => G i a))
    (filter_subset _ _)
    (h0 _ sdiff_subset (fun a ha hia => by
      rw [mem_sdiff, mem_filter] at ha
      exact ha.2 ⟨ha.1, hia⟩))
    (fun a ha => (h1 a (mem_filter.mp ha).1 (mem_filter.mp ha).2).1)
    (fun a ha => (h1 a (mem_filter.mp ha).1 (mem_filter.mp ha).2).2)
  refine ⟨j, s, hj, ht, hle, hc, fun a ha => ?_⟩
  constructor
  · intro has
    have : a ∈ supp n D (src D (j, s)) ∩ Bs := mem_inter.mpr ⟨has, ha⟩
    rw [hsupp, mem_filter] at this
    exact this.2
  · intro hia
    have : a ∈ Bs.filter (fun a => G i a) := mem_filter.mpr ⟨ha, hia⟩
    rw [← hsupp] at this
    exact (mem_inter.mp this).1
theorem sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hsep : ∀ u : Fin n, u ≠ i → ∃ z, G i z ∧ ¬ G u z)
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i hsep b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega
theorem sem_path_chain {a t : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a t) :
    sem_Chain n D a t ∨ ∃ b, sem_Chain n D a b ∧ 2 ≤ fanout D b := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @head a a' hstep _ ih =>
    by_cases hf : fanout D a = 1
    · rcases ih with h1 | ⟨b, h1, h2⟩
      · exact Or.inl (Relation.ReflTransGen.head ⟨hstep, hf⟩ h1)
      · exact Or.inr ⟨b, Relation.ReflTransGen.head ⟨hstep, hf⟩ h1, h2⟩
    · have := sem_step_fanout hstep
      exact Or.inr ⟨a, Relation.ReflTransGen.refl, by omega⟩
theorem sem_inelig_reach (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hsep : ∀ u : Fin n, u ≠ i → ∃ z, G i z ∧ ¬ G u z) (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) ∨
      ∃ b, sem_Chain n D i.val b ∧ 2 ≤ fanout D b ∧ supp n D b = ∅ := by
  have hlt : i.val < n + D.length := by have := i.isLt; omega
  have hp : Relation.ReflTransGen (sem_step n D) i.val (outW n D) := live_reaches_out h i.val hlt
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, h1, h2, sem_branch_empty hG h.1 hC hsep hi h1 h2⟩
theorem sem_bzero_mem (hS : Strict n D) {b : ℕ} (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) :
    b ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
  mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b) (by omega)),
    by rw [he]; exact not_nonempty_empty⟩
theorem sem_bzero_branch (hS : Strict n D) (hB0 : Bzero n D = 0) {b : ℕ} (hf : 2 ≤ fanout D b) :
    (supp n D b).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have h1 : fanout D b - 1 ≤ ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty),
      (fanout D w - 1) :=
    Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _)
      (sem_bzero_mem hS hf hne)
  unfold Bzero surplusOn at hB0
  omega
theorem sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hsep : ∀ u : Fin n, u ≠ i → ∃ z, G i z ∧ ¬ G u z)
    (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hsep hi h1 h2] at h3
    exact absurd h3 not_nonempty_empty
theorem sem_exact_nbhd (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i : Fin n}
    (hch : sem_Chain n D i.val (outW n D)) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  obtain ⟨j, s, hj, ht, -, hc, hsupp⟩ := sem_exact_at (G := G) hS i (outW n D) hch Bs
    (fun S hS1 hS2 => by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases sem_ins_ind_edge hG ((hC _).mp hc) with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
      · exact hS2 a ha hia
      · exact hBs a (hS1 ha) b (hS1 hb) hab)
    (fun a _ hia => by
      constructor
      · exact (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
      · by_contra hc
        rw [Bool.not_eq_false, sem_ind_single] at hc
        exact sem_single_no_edge hG a ((hC _).mp hc))
  exact ⟨j, s, hj, ht, hc, hsupp⟩
theorem sem_shared_exact (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i j : Fin n} {w : ℕ}
    (hch : sem_Chain n D i.val w) (hdj : sem_Dom n D w j.val)
    (hnsub : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    ∃ k s, k < D.length ∧ tag D k = true ∧ n + k ≤ w ∧
      sem_Chain n D i.val (src D (k, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a) := by
  classical
  have hX0 : ¬ sem_Edge G (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) := by
    intro hc
    rcases sem_ins_ind_edge hG hc with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
    · exact (mem_filter.mp ha).2 hia
    · exact hBs a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hab
  obtain ⟨a0, ha0, hja0, hia0⟩ := hnsub
  have hX1 : sem_Edge G (sem_ins j (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a))))) :=
    ⟨j, a0, hja0, sem_ins_self j _, by simp [sem_ins, sem_ind, ha0, hia0]⟩
  have hwX := (sem_dom_split hS hC _ j w hdj hX0 hX1).1
  refine sem_exact_at hS i w hch Bs (fun S hS1 hS2 => ?_) (fun a _ hia => ?_)
  · by_contra hc
    rw [Bool.not_eq_false] at hc
    have hmono := val_mono hS (sem_ins i (sem_ind S))
      (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) (fun k hk => by
        simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (mem_filter.mpr ⟨hS1 hk, hS2 k hk⟩)) w hc
    rw [hwX] at hmono
    exact Bool.false_ne_true hmono
  · have h2 := sem_dom_split hS hC (sem_ind {a}) i w (sem_chain_dom hS hch)
      (by rw [sem_ind_single]; exact sem_single_no_edge hG a)
      ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
    exact ⟨h2.2, h2.1⟩
theorem sem_full_support (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hsep : ∀ u : Fin n, u ≠ i → ∃ z, G i z ∧ ¬ G u z) (hi : i ∈ ineligSet n D) {e : ℕ × Bool} (he : sem_W n D i = {e})
    (hor : ∀ j, Relation.ReflTransGen (sem_step n D) (n + e.1) (n + j) → j ≠ e.1 →
      tag D j = false) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  obtain ⟨e0, hj0, ht0, hsrc0, hemp0, hnb0, hx0, -⟩ := sem_inelig_consumer hG h hC hsep hi
  have hee : e = e0 := Finset.singleton_injective (he.symm.trans hx0)
  subst hee
  obtain ⟨g, s⟩ := e
  intro t
  refine ⟨fun ht => ?_, fun ht => hnb0 t ht⟩
  by_contra hnt
  have hgate : val D (sem_two i t) (n + g) = true := by
    rw [sem_val_gate_src hS _ hj0 s, ht0, gop_true, Bool.and_eq_true]
    exact ⟨sem_val_of_supp hS (by rw [hsrc0]; exact mem_singleton_self i)
      (by simp [sem_two]), sem_val_of_supp hS ht (by simp [sem_two])⟩
  have hall : ∀ c, Relation.ReflTransGen (sem_step n D) (n + g) c →
      val D (sem_two i t) c = true := by
    intro c hc
    induction hc with
    | refl => exact hgate
    | tail hab hbc ih =>
      obtain ⟨j, s', hj, rfl, rfl⟩ := sem_step_iff.mp hbc
      have hne : j ≠ g := by
        have := sem_rtg_le hS (fun _ _ h => h) hab
        have := sem_src_lt hS hj s'
        omega
      rw [sem_val_gate_src hS _ hj s', hor j (Relation.ReflTransGen.tail hab hbc) hne,
        gop_false, ih]
      rfl
  have hout := hall _ (live_reaches_out h (n + g) (by omega))
  obtain ⟨u, v, huv, hu, hv⟩ := (hC _).mp hout
  simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] at huv
  · exact hG.2.1 _ huv
  · exact hnt huv
  · exact hnt (hG.1 _ _ huv)
  · exact hG.2.1 _ huv
end SemPaths
section SemDiff
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem sem_mem_diff {x y : Fin n} {w : ℕ} :
    w ∈ carrierDiff n D x y ↔ x ∈ supp n D w ∧ y ∉ supp n D w := by
  simp only [carrierDiff, mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨sem_supp_lt h.1, h⟩⟩
theorem sem_mem_exit_diff {x y : Fin n} {e : ℕ × Bool} :
    e ∈ exitArcs n D (carrierDiff n D x y) ↔ e.1 < D.length ∧
      (x ∈ supp n D (src D e) ∧ y ∉ supp n D (src D e)) ∧
      ¬ (x ∈ supp n D (n + e.1) ∧ y ∉ supp n D (n + e.1)) := by
  simp only [exitArcs, arcs, mem_filter, mem_product, mem_range,
    mem_univ, and_true, sem_mem_diff]
theorem sem_surplus_diff (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    {x y : Fin n} (hxy : x ≠ y) (hx : x ∈ eligSet n D) :
    surplusOn D (carrierDiff n D x y) = 1 + ((residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
  have h1 : surplusOn D (carrierDiff n D x y) =
      ((units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
    rw [sb_card_units_filter n D (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [mem_filter] at hw
      exact sem_mem_diff.mpr hw.2
    · have hni : w ∉ inner n D := fun hc => hnot (mem_filter.mpr ⟨hc, sem_mem_diff.mp hw⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) =
      {(⟨b x, 0⟩ : Σ _ : ℕ, ℕ)} ∪ (residualUnits n D b).filter
        (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, mem_union, mem_filter, mem_sdiff,
      mem_singleton]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · left
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hr
        have hxv := hu.2.1
        rw [(hb v hv).2, mem_singleton] at hxv
        rw [hxv]
      · exact Or.inr ⟨⟨⟨hu.1, ⟨x, hu.2.1⟩⟩, hr⟩, hu.2⟩
    · rintro (rfl | hu)
      · have hbx := hb x hx
        refine ⟨(mem_filter.mp (hsub (mem_image.mpr ⟨x, hx, rfl⟩))).1, ?_, ?_⟩
        · rw [hbx.2]; exact mem_singleton_self x
        · rw [hbx.2, mem_singleton]; exact fun hc => hxy hc.symm
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : (⟨b x, 0⟩ : Σ _ : ℕ, ℕ) ∉ (residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    intro hc
    exact (mem_sdiff.mp (mem_filter.mp hc).1).2 (mem_image.mpr ⟨x, hx, rfl⟩)
  rw [h1, h2, Finset.singleton_union, card_insert_of_notMem h3]
  omega
theorem sem_first_joint (hS : Strict n D) {x y : Fin n} (hxy : x ≠ y) {w : ℕ}
    (hw : x ∈ supp n D w ∧ y ∈ supp n D w) :
    ∃ j s, j < D.length ∧ tag D j = false ∧ x ∈ supp n D (n + j) ∧ y ∈ supp n D (n + j) ∧
      x ∈ supp n D (src D (j, s)) ∧ y ∉ supp n D (src D (j, s)) ∧
      y ∈ supp n D (src D (j, !s)) ∧ x ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ u, x ∈ supp n D u ∧ y ∈ supp n D u := ⟨w, hw⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hmin : ∀ u, u < Nat.find hex → ¬ (x ∈ supp n D u ∧ y ∈ supp n D u) :=
    fun u hu => Nat.find_min hex hu
  generalize Nat.find hex = f at h1 h2 hmin
  have hlt := sem_supp_lt h1
  have hn : n ≤ f := by
    by_contra hc
    have hs : supp n D f = {⟨f, by omega⟩} := supp_input D ⟨f, by omega⟩
    rw [hs, mem_singleton] at h1 h2
    exact hxy (h1.trans h2.symm)
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  cases ht : tag D j
  · have h1' := h1
    have h2' := h2
    rw [sem_supp_or hS hj ht, mem_union] at h1' h2'
    refine ⟨j, ?_⟩
    rcases h1' with hxa | hxb
    · have hya : y ∉ supp n D (opA D j) := fun hc => hna ⟨hxa, hc⟩
      have hyb : y ∈ supp n D (opB D j) := h2'.resolve_left hya
      exact ⟨false, hj, ht, h1, h2, by simpa [src] using hxa, by simpa [src] using hya,
        by simpa [src] using hyb, by simpa [src] using fun hc => hnb ⟨hc, hyb⟩⟩
    · have hyb : y ∉ supp n D (opB D j) := fun hc => hnb ⟨hxb, hc⟩
      have hya : y ∈ supp n D (opA D j) := h2'.resolve_right hyb
      exact ⟨true, hj, ht, h1, h2, by simpa [src] using hxb, by simpa [src] using hyb,
        by simpa [src] using hya, by simpa [src] using fun hc => hna ⟨hc, hya⟩⟩
  · exfalso
    rw [sem_supp_and hS hj ht, mem_inter] at h1 h2
    exact hna ⟨h1.1, h2.1⟩
theorem sem_diff_two_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {x c z : Fin n} (hxc : x ≠ c)
    (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1)
    {w : ℕ} (hw : x ∈ supp n D w ∧ c ∈ supp n D w) (hxz : G x z) (hcz : ¬ G c z) :
    surplusOn D (carrierDiff n D x c) = 1 ∧ merges n D (carrierDiff n D x c) = ∅ ∧
      (exitArcs n D (carrierDiff n D x c)).card = 2 ∧
      ∃ e ∈ exitArcs n D (carrierDiff n D x c), tag D e.1 = false ∧ c ∈ supp n D (n + e.1) := by
  have hS := h.1
  have hsur : surplusOn D (carrierDiff n D x c) = 1 := by
    rw [sem_surplus_diff hS b hb hxc hx, Finset.filter_eq_empty_iff.mpr
      (fun u hu hc => hc.2 (hres u hu hc.1)), card_empty]
  have hfl := carrier_flow_diff h x c hxc
    (by rw [sem_supp_out hG hC]; exact notMem_empty x)
  rw [hsur] at hfl
  obtain ⟨j1, s1, hj1, ht1, hx1, hc1, hxs1, hcs1, -, -⟩ := sem_first_joint hS hxc hw
  have he1 : (j1, s1) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj1, ⟨hxs1, hcs1⟩, fun hc => hc.2 hc1⟩
  have hA : ∀ u ∈ ({c, z} : Finset (Fin n)), ∀ v ∈ ({c, z} : Finset (Fin n)), ¬ G u v := by
    intro u hu v hv
    simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · exact hG.2.1 c
    · exact hcz
    · exact fun hc => hcz (hG.1 _ _ hc)
    · exact hG.2.1 z
  obtain ⟨j2, s2, hj2, -, hx2, hn2, hd2⟩ := sem_exposure hG hS hC {c, z} hA x ⟨z, by simp, hxz⟩
  have he2 : (j2, s2) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj2, ⟨hx2, fun hc => disjoint_left.mp hd2 hc (by simp)⟩,
      fun hc => hn2 hc.1⟩
  have hne : (j1, s1) ≠ (j2, s2) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    exact hn2 (heq.1 ▸ hx1)
  have h2 : 2 ≤ (exitArcs n D (carrierDiff n D x c)).card :=
    Finset.one_lt_card.mpr ⟨_, he1, _, he2, hne⟩
  exact ⟨hsur, card_eq_zero.mp (by omega), by omega, (j1, s1), he1, ht1, hc1⟩
theorem sem_and_sibling_nbrs (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {j : ℕ} (hj : j < D.length) (s : Bool) (ht : tag D j = true)
    (hch : sem_Chain n D i.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (hout : n + j ≤ outW n D) {a : Fin n} (hia : G i a) : a ∈ supp n D (src D (j, s)) := by
  have hchg : sem_Chain n D i.val (n + j) :=
    Relation.ReflTransGen.tail hch ⟨sem_step_src hj (!s), hf⟩
  have hx0 : val D (single a) (outW n D) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact sem_single_no_edge hG a ((hC _).mp hc)
  have hy1 : val D (sem_ins i (single a)) (outW n D) = true :=
    (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩
  have hgy : val D (sem_ins i (single a)) (n + j) = true := by
    by_contra hc2
    rw [Bool.not_eq_true] at hc2
    have hgx : val D (single a) (n + j) = false := by
      by_contra hc3
      rw [Bool.not_eq_false] at hc3
      rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
      exact Bool.noConfusion hc2
    have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (single a)) (n + j) (outW n D)
      (sem_chain_dom_at hS hchg hout) (hgx.trans hc2.symm)
    rw [hx0, hy1] at h2
    exact Bool.false_ne_true h2
  rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
  have hind := sem_sibling_indep hS i hj s hch hf _ _ (sem_ins_agree i (single a))
  rw [hgy.1] at hind
  exact mem_supp.mpr hind
end SemDiff
def sup_Occ (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop := ∃ w, supp n D w ∩ P = M
def sup_big (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (merges n D (carrierT n D P)).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)
def sup_Wit (n : ℕ) (D : Dag) (P U : Finset (Fin n)) (f : Fin n) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ f ∈ P ∧ f ∈ supp n D (src D e) ∧
    f ∉ supp n D (n + e.1) ∧ supp n D (src D e) ∩ P ⊆ U ∧ (supp n D (src D e) ∩ P).card ≤ 2
def sup_cost (n : ℕ) (D : Dag) (P : Finset (Fin n)) (e : ℕ × Bool) : (ℕ × Bool) ⊕ ℕ :=
  if supp n D (n + e.1) ∩ P = ∅ then Sum.inl e else Sum.inr e.1
def sup_CostOK (n : ℕ) (D : Dag) (P : Finset (Fin n)) (c : (ℕ × Bool) ⊕ ℕ) : Prop :=
  Sum.elim (fun e => e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2)
    (fun j => j ∈ merges n D (carrierT n D P) ∧ (supp n D (n + j) ∩ P).card = 1) c
section SupMask
variable {n : ℕ} {D : Dag}
theorem sup_occ_wire (P : Finset (Fin n)) (w : ℕ) : sup_Occ n D P (supp n D w ∩ P) := ⟨w, rfl⟩
theorem sup_occ_sub {P M : Finset (Fin n)} (h : sup_Occ n D P M) : M ⊆ P := by
  obtain ⟨w, rfl⟩ := h
  exact inter_subset_right
theorem sup_mem_carrier {P : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D P ↔ (supp n D w ∩ P).Nonempty := by
  simp only [carrierT, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨v, hv⟩ := h
    exact ⟨sem_supp_lt (mem_inter.mp hv).1, v, hv⟩
theorem sup_occ_big (hS : Strict n D) {P M : Finset (Fin n)} (hM : 2 ≤ M.card)
    (h : sup_Occ n D P M) : ∃ j ∈ sup_big n D P, supp n D (n + j) ∩ P = M := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, -, -, hj, hmer, -, -⟩ := sem_first_mask hS P M hM w hw
  exact ⟨j, mem_filter.mpr ⟨hmer, by rw [hj]; exact hM⟩, hj⟩
theorem sup_card_le_big (hS : Strict n D) (P : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D P M) : F.card ≤ (sup_big n D P).card := by
  have hsub : F ⊆ (sup_big n D P).image (fun j => supp n D (n + j) ∩ P) := by
    intro M hM
    obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF M hM).1 (hF M hM).2
    exact mem_image.mpr ⟨j, hj, hjM⟩
  exact (card_le_card hsub).trans Finset.card_image_le
theorem sup_triple_parent (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 7)
    (hT : T.card = 3) (h : sup_Occ n D P T) :
    (∃ A, sup_Occ n D P A ∧ A.card = 2 ∧ A ⊆ T) ∨
      (∃ A, sup_Occ n D P A ∧ A.card = 4 ∧ T ⊆ A) ∨
      (∃ A B, A ≠ B ∧ sup_Occ n D P A ∧ sup_Occ n D P B ∧ A.card = 5 ∧ B.card = 5 ∧
        T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, hj, -, hjT, -, -, hpar⟩ := sem_first_mask hS P T (by omega) w hw
  have hoA : sup_Occ n D P (supp n D (opA D j) ∩ P) := sup_occ_wire P _
  have hoB : sup_Occ n D P (supp n D (opB D j) ∩ P) := sup_occ_wire P _
  rcases hpar with ⟨ht, hA, hB⟩ | ⟨-, hA, hB, hun, -, -⟩
  · have hAB : (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) = T := by
      rw [← hjT, sem_supp_and hS hj ht]
      ext v
      simp only [mem_inter]
      tauto
    generalize supp n D (opA D j) ∩ P = A at hoA hA hAB
    generalize supp n D (opB D j) ∩ P = B at hoB hB hAB
    have hcA := card_lt_card hA
    have hcB := card_lt_card hB
    have hu : (A ∪ B).card ≤ 7 :=
      (card_le_card (Finset.union_subset (sup_occ_sub hoA) (sup_occ_sub hoB))).trans hP
    have hie := Finset.card_union_add_card_inter A B
    rw [hAB] at hie
    by_cases h4 : A.card = 4
    · exact Or.inr (Or.inl ⟨A, hoA, h4, hA.subset⟩)
    by_cases h4' : B.card = 4
    · exact Or.inr (Or.inl ⟨B, hoB, h4', hB.subset⟩)
    refine Or.inr (Or.inr ⟨A, B, ?_, hoA, hoB, by omega, by omega, hA.subset, hB.subset, hAB⟩)
    intro hEq
    rw [hEq, Finset.inter_self] at hAB
    rw [hAB] at hcB
    omega
  · generalize supp n D (opA D j) ∩ P = A at hoA hA hun
    generalize supp n D (opB D j) ∩ P = B at hoB hB hun
    have hcA := card_lt_card hA
    have hcB := card_lt_card hB
    have hc := Finset.card_union_le A B
    rw [hun] at hc
    by_cases h2 : A.card = 2
    · exact Or.inl ⟨A, hoA, h2, hA.subset⟩
    · exact Or.inl ⟨B, hoB, by omega, hB.subset⟩
theorem sup_pair_unique {T T' A : Finset (Fin n)} (hA : A.card = 2) (h1 : A ⊆ T)
    (h2 : A ⊆ T') (hint : T ≠ T' → (T ∩ T').card ≤ 1) : T = T' := by
  by_contra hne
  have h3 := card_le_card (Finset.subset_inter h1 h2)
  have h4 := hint hne
  omega
theorem sup_four_unique {T T' A : Finset (Fin n)} (hT : T.card = 3) (hT' : T'.card = 3)
    (hA : A.card = 4) (h1 : T ⊆ A) (h2 : T' ⊆ A) (hint : T ≠ T' → (T ∩ T').card ≤ 1) :
    T = T' := by
  by_contra hne
  have h3 := card_le_card (Finset.union_subset h1 h2)
  have h4 := Finset.card_union_add_card_inter T T'
  have h5 := hint hne
  omega
theorem sup_five_cap {T1 T2 T3 A : Finset (Fin n)} (h1 : T1.card = 3) (h2 : T2.card = 3)
    (h3 : T3.card = 3) (hA : A.card ≤ 5) (s1 : T1 ⊆ A) (s2 : T2 ⊆ A) (s3 : T3 ⊆ A)
    (i12 : (T1 ∩ T2).card ≤ 1) (i13 : (T1 ∩ T3).card ≤ 1) (i23 : (T2 ∩ T3).card ≤ 1) :
    False := by
  have hu := card_le_card (Finset.union_subset (Finset.union_subset s1 s2) s3)
  have e1 := Finset.card_union_add_card_inter T1 T2
  have e2 := Finset.card_union_add_card_inter (T1 ∪ T2) T3
  have e3 : ((T1 ∪ T2) ∩ T3).card ≤ (T1 ∩ T3).card + (T2 ∩ T3).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  omega
theorem sup_aux_exists (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1) :
    ∃ Aux : Finset (Finset (Fin n)), L.card ≤ Aux.card ∧ ∀ A ∈ Aux, sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) := by
  classical
  refine ⟨P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)), ?_,
    fun A hA => (mem_filter.mp hA).2⟩
  generalize hAux : P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)) = Aux
  have hmem : ∀ A, sup_Occ n D P A →
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) → A ∈ Aux := by
    intro A h1 h2
    rw [← hAux]
    exact mem_filter.mpr ⟨Finset.mem_powerset.mpr (sup_occ_sub h1), h1, h2⟩
  have hprop : ∀ A ∈ Aux, (A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5 := by
    intro A hA
    rw [← hAux] at hA
    exact (mem_filter.mp hA).2.2
  have hrow : ∀ T ∈ L, 2 ≤ ∑ A ∈ Aux,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) := by
    intro T hT
    rcases sup_triple_parent hS hP (h3 T hT).1 (h3 T hT).2 with
      ⟨A, ho, hc, hs⟩ | ⟨A, ho, hc, hs⟩ | ⟨A, B, hne, hoA, hoB, hcA, hcB, hsA, hsB, -⟩
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inl ⟨hc, T, hT, hs⟩)))
      simp [hc, hs]
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inr (Or.inl hc))))
      simp [hc, hs]
    · have hsub : ({A, B} : Finset (Finset (Fin n))) ⊆ Aux := by
        intro x hx
        rw [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hmem _ hoA (Or.inr (Or.inr hcA))
        · exact hmem _ hoB (Or.inr (Or.inr hcB))
      refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
      rw [Finset.sum_pair hne]
      simp [hcA, hcB, hsA, hsB]
  have hcol : ∀ A ∈ Aux, ∑ T ∈ L,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) ≤ 2 := by
    intro A hA
    by_cases h5 : A.card = 5
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) = (L.filter (fun T => T ⊆ A)).card := by
        rw [card_filter]
        exact sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      by_contra hgt
      obtain ⟨T1, T2, T3, m1, m2, m3, n12, n13, n23⟩ :=
        Finset.two_lt_card_iff.mp (show 2 < (L.filter (fun T => T ⊆ A)).card by omega)
      rw [mem_filter] at m1 m2 m3
      exact sup_five_cap (h3 _ m1.1).1 (h3 _ m2.1).1 (h3 _ m3.1).1 h5.le m1.2 m2.2 m3.2
        (hint _ m1.1 _ m2.1 n12) (hint _ m1.1 _ m3.1 n13) (hint _ m2.1 _ m3.1 n23)
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) =
          2 * (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card := by
        rw [card_filter, Finset.mul_sum]
        exact sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      have hle : (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro T hT T' hT'
        rw [mem_filter] at hT hT'
        have c3 := (h3 T hT.1).1
        have c3' := (h3 T' hT'.1).1
        rcases hprop A hA with ⟨h2, -⟩ | h4 | h5'
        · have e1 : A ⊆ T := hT.2.resolve_right (fun h => by
            have := card_le_card h; omega)
          have e2 : A ⊆ T' := hT'.2.resolve_right (fun h => by
            have := card_le_card h; omega)
          exact sup_pair_unique h2 e1 e2 (hint T hT.1 T' hT'.1)
        · have e1 : T ⊆ A := hT.2.resolve_left (fun h => by
            have := card_le_card h; omega)
          have e2 : T' ⊆ A := hT'.2.resolve_left (fun h => by
            have := card_le_card h; omega)
          exact sup_four_unique c3 c3' h4 e1 e2 (hint T hT.1 T' hT'.1)
        · exact absurd h5' h5
      omega
  have h1 := Finset.card_nsmul_le_sum L _ 2 hrow
  have h2 := Finset.sum_le_card_nsmul Aux _ 2 hcol
  rw [Finset.sum_comm] at h1
  simp only [smul_eq_mul] at h1 h2
  omega
theorem sup_charge (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1)
    (X : Finset (Finset (Fin n)))
    (hX : ∀ M ∈ X, sup_Occ n D P M ∧ 2 ≤ M.card ∧ M ∉ L ∧ M.card ≠ 4 ∧ M.card ≠ 5 ∧
      (M.card = 2 → ∀ T ∈ L, ¬ M ⊆ T)) :
    2 * L.card + X.card ≤ (sup_big n D P).card := by
  classical
  obtain ⟨Aux, hcard, hAux⟩ := sup_aux_exists hS hP L h3 hint
  have hd1 : Disjoint L Aux := by
    rw [disjoint_left]
    intro T hT hTA
    have := (h3 T hT).1
    rcases (hAux T hTA).2 with ⟨h, -⟩ | h | h <;> omega
  have hd2 : Disjoint (L ∪ Aux) X := by
    rw [disjoint_left]
    intro M hM hMX
    obtain ⟨-, -, hnL, hn4, hn5, hno⟩ := hX M hMX
    rcases mem_union.mp hM with h | h
    · exact hnL h
    · rcases (hAux M h).2 with ⟨h2, T, hT, hs⟩ | h4 | h5
      · exact hno h2 T hT hs
      · exact hn4 h4
      · exact hn5 h5
  have hle := sup_card_le_big hS P ((L ∪ Aux) ∪ X) (by
    intro M hM
    rcases mem_union.mp hM with h | h
    · rcases mem_union.mp h with h | h
      · exact ⟨by have := (h3 M h).1; omega, (h3 M h).2⟩
      · refine ⟨?_, (hAux M h).1⟩
        rcases (hAux M h).2 with ⟨h, -⟩ | h | h <;> omega
    · exact ⟨(hX M h).2.1, (hX M h).1⟩)
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1] at hle
  omega
theorem sup_wit_exists {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {P U X : Finset (Fin n)} (hUP : U ⊆ P)
    (hU : U.card ≤ 2 ∨ (U.card = 3 ∧ ¬ sup_Occ n D P U))
    (hX : ∀ a ∈ X, ∀ b ∈ X, ¬ G a b) (hPX : P \ U ⊆ X) {f : Fin n} (hf : f ∈ U)
    (hnb : ∃ a ∈ X, G f a) : ∃ e, sup_Wit n D P U f e := by
  obtain ⟨j, s, hj, ht, h1, h2, hd⟩ := sem_exposure hG hS hC X hX f hnb
  have hsub : supp n D (src D (j, s)) ∩ P ⊆ U := by
    intro v hv
    rw [mem_inter] at hv
    by_contra hvU
    exact disjoint_left.mp hd hv.1 (hPX (mem_sdiff.mpr ⟨hv.2, hvU⟩))
  refine ⟨(j, s), hj, ht, hUP hf, h1, h2, hsub, ?_⟩
  rcases hU with hU | ⟨hU3, hmiss⟩
  · exact (card_le_card hsub).trans hU
  · have hne : supp n D (src D (j, s)) ∩ P ≠ U := fun h => hmiss ⟨_, h⟩
    have := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    omega
theorem sup_wit_out (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) :
    supp n D (n + e.1) ∩ P ⊆ (supp n D (src D e) ∩ P).erase f := by
  obtain ⟨hj, ht, -, -, h2, -, -⟩ := h
  intro v hv
  rw [mem_inter] at hv
  rw [mem_erase, mem_inter]
  exact ⟨fun hvf => h2 (hvf ▸ hv.1), sem_supp_and_sub hS hj ht e.2 hv.1, hv.2⟩
theorem sup_wit_single {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e)
    (hno : ∀ M, M ⊆ U → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M) :
    supp n D (src D e) ∩ P = {f} := by
  obtain ⟨-, -, hfP, h1, -, hsub, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := mem_inter.mpr ⟨h1, hfP⟩
  have hc2 : (supp n D (src D e) ∩ P).card ≠ 2 :=
    fun h2 => hno _ hsub h2 hfm (sup_occ_wire P _)
  exact (eq_of_subset_of_card_le (singleton_subset_iff.mpr hfm)
    (by rw [card_singleton]; omega)).symm
theorem sup_cost_inl {P : Finset (Fin n)} {e e0 : ℕ × Bool}
    (h : sup_cost n D P e = Sum.inl e0) : e = e0 ∧ supp n D (n + e.1) ∩ P = ∅ := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inl.inj h, h0⟩
theorem sup_cost_inr {P : Finset (Fin n)} {e : ℕ × Bool} {j : ℕ}
    (h : sup_cost n D P e = Sum.inr j) : e.1 = j ∧ (supp n D (n + e.1) ∩ P).Nonempty := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inr.inj h, nonempty_iff_ne_empty.mpr h0⟩
theorem sup_cost_ok (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) : sup_CostOK n D P (sup_cost n D P e) := by
  have hout := sup_wit_out hS h
  obtain ⟨hj, ht, hfP, h1, -, -, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := mem_inter.mpr ⟨h1, hfP⟩
  unfold sup_cost
  split_ifs with h0
  · show e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2
    refine ⟨?_, hc⟩
    rw [exitArcs, mem_filter]
    refine ⟨mem_product.mpr ⟨mem_range.mpr hj, mem_univ _⟩,
      sup_mem_carrier.mpr ⟨f, hfm⟩, ?_⟩
    rw [sup_mem_carrier, h0]
    exact not_nonempty_empty
  · show e.1 ∈ merges n D (carrierT n D P) ∧ (supp n D (n + e.1) ∩ P).card = 1
    have hne : (supp n D (n + e.1) ∩ P).Nonempty := nonempty_iff_ne_empty.mpr h0
    have hle := card_le_card hout
    rw [Finset.card_erase_of_mem hfm] at hle
    have hpos := card_pos.mpr hne
    refine ⟨?_, by omega⟩
    obtain ⟨v, hv⟩ := hne
    rw [mem_inter] at hv
    have hA := sem_supp_and_sub hS hj ht false hv.1
    have hB := sem_supp_and_sub hS hj ht true hv.1
    rw [sb_src_false] at hA
    rw [sb_src_true] at hB
    rw [merges, mem_filter, mem_range]
    exact ⟨hj, sup_mem_carrier.mpr ⟨v, mem_inter.mpr hv⟩,
      sup_mem_carrier.mpr ⟨v, mem_inter.mpr ⟨hA, hv.2⟩⟩,
      sup_mem_carrier.mpr ⟨v, mem_inter.mpr ⟨hB, hv.2⟩⟩⟩
theorem sup_wit_same_pos (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e)
    (hne : (supp n D (n + e.1) ∩ P).Nonempty) : f = f' := by
  by_contra hff
  obtain ⟨q, hq⟩ := hne
  have h1 := sup_wit_out hS h hq
  have h2 := sup_wit_out hS h' hq
  rw [mem_erase] at h1 h2
  have hsub : ({q, f, f'} : Finset (Fin n)) ⊆ supp n D (src D e) ∩ P := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact h1.2
    · exact mem_inter.mpr ⟨h.2.2.2.1, h.2.2.1⟩
    · exact mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  have hc := card_le_card hsub
  have h3 : ({q, f, f'} : Finset (Fin n)).card = 3 := by
    rw [card_insert_of_notMem, card_pair hff]
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨h1.1, h2.1⟩
  have := h.2.2.2.2.2.2
  omega
theorem sup_cost_ne_of_single (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e')
    (hs : supp n D (src D e) ∩ P = {f}) (hff : f ≠ f') :
    sup_cost n D P e ≠ sup_cost n D P e' := by
  intro heq
  have h0 : supp n D (n + e.1) ∩ P = ∅ := by
    have hout := sup_wit_out hS h
    rw [hs, Finset.erase_singleton] at hout
    exact Finset.subset_empty.mp hout
  have hc : sup_cost n D P e = Sum.inl e := by simp [sup_cost, h0]
  rw [hc] at heq
  have he := (sup_cost_inl heq.symm).1
  subst he
  have hm : f' ∈ supp n D (src D e') ∩ P := mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  rw [hs, mem_singleton] at hm
  exact hff hm.symm
theorem sup_fibre_le (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (c : (ℕ × Bool) ⊕ ℕ) :
    (Lab.filter (fun f => sup_cost n D P (wit f) = c)).card ≤ 2 := by
  rcases c with e0 | j0
  · by_cases hne : (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inl e0)).Nonempty
    · obtain ⟨f0, hf0⟩ := hne
      rw [mem_filter] at hf0
      have hcard := (hwit f0 hf0.1).2.2.2.2.2.2
      rw [(sup_cost_inl hf0.2).1] at hcard
      refine le_trans (card_le_card ?_) hcard
      intro f hf
      rw [mem_filter] at hf
      have hw := hwit f hf.1
      rw [(sup_cost_inl hf.2).1] at hw
      exact mem_inter.mpr ⟨hw.2.2.2.1, hw.2.2.1⟩
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  · have hinj : Set.InjOn (fun f => (wit f).2)
        (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inr j0) : Set (Fin n)) := by
      intro f hf f' hf' hs
      rw [Finset.mem_coe, mem_filter] at hf hf'
      obtain ⟨h1, hn1⟩ := sup_cost_inr hf.2
      obtain ⟨h1', -⟩ := sup_cost_inr hf'.2
      have hee : wit f = wit f' := Prod.ext (h1.trans h1'.symm) hs
      have hw' := hwit f' hf'.1
      rw [← hee] at hw'
      exact sup_wit_same_pos hS (hwit f hf.1) hw' hn1
    have hle := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset Bool))
      (fun f => (wit f).2) (fun _ _ => mem_univ _) hinj
    simpa using hle
theorem sup_wit_card (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) :
    Lab.card ≤ 2 * (Lab.image (fun f => sup_cost n D P (wit f))).card :=
  Finset.card_le_mul_card_image Lab 2 (fun c _ => sup_fibre_le hS Lab U wit hwit c)
theorem sup_wit_card_single (hS : Strict n D) {P : Finset (Fin n)} (Lab S : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f}) :
    2 * S.card + (Lab \ S).card ≤
      2 * (Lab.image (fun f => sup_cost n D P (wit f))).card := by
  have h1 : (S.image (fun f => sup_cost n D P (wit f))).card = S.card :=
    card_image_of_injOn (fun f hf f' hf' heq => by
      by_contra hne
      exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' (hSL hf')) (hsing f hf) hne heq)
  have h2 := sup_wit_card hS (Lab \ S) U wit (fun f hf => hwit f (mem_sdiff.mp hf).1)
  have hd : Disjoint (S.image (fun f => sup_cost n D P (wit f)))
      ((Lab \ S).image (fun f => sup_cost n D P (wit f))) := by
    rw [disjoint_left]
    intro c hc1 hc2
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hc1
    obtain ⟨f', hf', heq⟩ := mem_image.mp hc2
    rw [mem_sdiff] at hf'
    exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' hf'.1) (hsing f hf)
      (fun h => hf'.2 (h ▸ hf)) heq.symm
  have h3 : (S.image (fun f => sup_cost n D P (wit f)) ∪
      (Lab \ S).image (fun f => sup_cost n D P (wit f))).card ≤
      (Lab.image (fun f => sup_cost n D P (wit f))).card :=
    card_le_card (Finset.union_subset (image_subset_image hSL)
      (image_subset_image sdiff_subset))
  rw [card_union_of_disjoint hd, h1] at h3
  omega
theorem sup_master_disj (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (C : Finset ((ℕ × Bool) ⊕ ℕ)) (hC : ∀ c ∈ C, sup_CostOK n D P c)
    (hdis : Disjoint E C.toLeft) :
    (sup_big n D P).card + E.card + C.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  have hl : ∀ e ∈ C.toLeft, e ∈ exitArcs n D (carrierT n D P) ∧
      (supp n D (src D e) ∩ P).card ≤ 2 := fun e he => hC _ (mem_toLeft.mp he)
  have hr : ∀ j ∈ C.toRight, j ∈ merges n D (carrierT n D P) ∧
      (supp n D (n + j) ∩ P).card = 1 := fun j hj => hC _ (Finset.mem_toRight.mp hj)
  have h1 : E.card + C.toLeft.card ≤ (exitArcs n D (carrierT n D P)).card := by
    rw [← card_union_of_disjoint hdis]
    refine card_le_card (fun e he => ?_)
    rcases mem_union.mp he with h | h
    · exact hE e h
    · exact (hl e h).1
  have h2 : (sup_big n D P).card + C.toRight.card ≤ (merges n D (carrierT n D P)).card := by
    rw [← card_union_of_disjoint]
    · refine card_le_card (fun j hj => ?_)
      rcases mem_union.mp hj with h | h
      · exact (mem_filter.mp h).1
      · exact (hr j h).1
    · rw [disjoint_left]
      intro j h1 h2
      have a := (mem_filter.mp h1).2
      have b := (hr j h2).2
      omega
  have h3 := Finset.card_toLeft_add_card_toRight (u := C)
  omega
theorem sup_count_disj (hS : Strict n D) (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (Lab S : Finset (Fin n)) (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f})
    (hdis : ∀ e ∈ E, ∀ f ∈ Lab, e ≠ wit f) :
    2 * ((sup_big n D P).card + E.card) + 2 * S.card + (Lab \ S).card ≤
      2 * ((exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card) := by
  have h1 := sup_wit_card_single hS Lab S U wit hwit hSL hsing
  have hdis' : Disjoint E (Lab.image (fun f => sup_cost n D P (wit f))).toLeft := by
    rw [disjoint_left]
    intro e he hL
    rw [mem_toLeft, mem_image] at hL
    obtain ⟨f, hf, hcf⟩ := hL
    have hwe : wit f = e := by
      unfold sup_cost at hcf
      split at hcf
      · exact Sum.inl.inj hcf
      · exact absurd hcf (by simp)
    exact hdis e he f hf hwe.symm
  have h2 := sup_master_disj P E hE (Lab.image (fun f => sup_cost n D P (wit f))) (by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hc
    exact sup_cost_ok hS (hwit f hf)) hdis'
  omega
end SupMask
def k4_Pos14 (D : Dag) (pos : Fin 14 → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet 14 D, i ≠ 0 → (pos i).1 < D.length ∧ supp 14 D (14 + (pos i).1) = ∅ ∧
    (∀ a, Adj i a → a ∈ supp 14 D (src D (pos i))) ∧
    supp 14 D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ((0 : Fin 14) ∈ ineligSet 14 D → (pos 0).1 < D.length ∧ supp 14 D (14 + (pos 0).1) ⊆ {4, 5} ∧
    (10 : Fin 14) ∈ supp 14 D (src D (pos 0)) ∧
    (0 : Fin 14) ∈ supp 14 D (src D ((pos 0).1, !(pos 0).2)) ∧
    supp 14 D (src D ((pos 0).1, !(pos 0).2)) ⊆ {0, 4, 5}) ∧
  ∀ i ∈ ineligSet 14 D, ∀ i' ∈ ineligSet 14 D, pos i = pos i' → i = i'
theorem k4_assigned14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ pos : Fin 14 → ℕ × Bool, k4_Pos14 D pos := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  have hex : ∀ i : Fin 14, ∃ e : ℕ × Bool,
      (i ∈ ineligSet 14 D → i ≠ 0 → e.1 < D.length ∧ supp 14 D (14 + e.1) = ∅ ∧
        (∀ a, Adj i a → a ∈ supp 14 D (src D e)) ∧ supp 14 D (src D (e.1, !e.2)) = {i}) ∧
      (i = 0 → (0 : Fin 14) ∈ ineligSet 14 D → e.1 < D.length ∧ supp 14 D (14 + e.1) ⊆ {4, 5} ∧
        (10 : Fin 14) ∈ supp 14 D (src D e) ∧
        (0 : Fin 14) ∈ supp 14 D (src D (e.1, !e.2)) ∧ supp 14 D (src D (e.1, !e.2)) ⊆ {0, 4, 5}) := by
    intro i
    by_cases hi : i ∈ ineligSet 14 D
    · by_cases hi0 : i = 0
      · subst hi0
        obtain ⟨e, h1, -, h3a, h3b, h4, h5, -, -⟩ := sem_inelig_consumer_zero h hD hi
        exact ⟨(e.1, !e.2), fun _ hne => absurd rfl hne,
          fun _ _ => ⟨h1, h4, h5, by simpa using h3a, by simpa using h3b⟩⟩
      · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ :=
          sem_inelig_consumer hG h hC (fun u hu => nbr_diff_exists i u hu.symm hi0) hi
        exact ⟨(e.1, !e.2), fun _ _ => ⟨h1, h4, h5, by simpa using h3⟩, fun h0 => absurd h0 hi0⟩
    · exact ⟨(0, false), fun hc => absurd hc hi, fun h0 hc => absurd (h0 ▸ hc) hi⟩
  choose pos hpos using hex
  refine ⟨pos, fun i hi hi0 => (hpos i).1 hi hi0, fun h0 => (hpos 0).2 rfl h0, fun i hi i' hi' he => ?_⟩
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hi'0 : i' = 0
    · exact hi'0.symm
    · have h0m : (0 : Fin 14) ∈ supp 14 D (src D ((pos 0).1, !(pos 0).2)) := ((hpos 0).2 rfl hi).2.2.2.1
      rw [he, ((hpos i').1 hi' hi'0).2.2.2, mem_singleton] at h0m
      exact absurd h0m.symm hi'0
  · by_cases hi'0 : i' = 0
    · subst hi'0
      have h0m : (0 : Fin 14) ∈ supp 14 D (src D ((pos 0).1, !(pos 0).2)) := ((hpos 0).2 rfl hi').2.2.2.1
      rw [← he, ((hpos i).1 hi hi0).2.2.2, mem_singleton] at h0m
      exact absurd h0m.symm hi0
    · have h1 := ((hpos i).1 hi hi0).2.2.2
      rw [he, ((hpos i').1 hi' hi'0).2.2.2] at h1
      exact (Finset.singleton_injective h1).symm
theorem pos0_pure_of_45 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (h0 : (0 : Fin 14) ∈ ineligSet 14 D) (h4 : (4 : Fin 14) ∈ ineligSet 14 D)
    (h5 : (5 : Fin 14) ∈ ineligSet 14 D) :
    supp 14 D (src D ((pos 0).1, !(pos 0).2)) = {0} ∧ supp 14 D (14 + (pos 0).1) = ∅ := by
  obtain ⟨-, hsubG, -, h0m, hsub⟩ := hpos.2.1 h0
  have hn4 : (4 : Fin 14) ∉ supp 14 D (src D ((pos 0).1, !(pos 0).2)) := fun h4m => by
    have hp := sem_inelig_pure sem_g14_gr h.1 (sem_g14_comp hD)
      (fun u hu => nbr_diff_exists 4 u hu.symm (by decide)) h4 h4m
    rw [hp, mem_singleton] at h0m; exact (by decide : (0 : Fin 14) ≠ 4) h0m
  have hn5 : (5 : Fin 14) ∉ supp 14 D (src D ((pos 0).1, !(pos 0).2)) := fun h5m => by
    have hp := sem_inelig_pure sem_g14_gr h.1 (sem_g14_comp hD)
      (fun u hu => nbr_diff_exists 5 u hu.symm (by decide)) h5 h5m
    rw [hp, mem_singleton] at h0m; exact (by decide : (0 : Fin 14) ≠ 5) h0m
  have h0eq : supp 14 D (src D ((pos 0).1, !(pos 0).2)) = {0} := by
    refine Finset.Subset.antisymm (fun x hx => ?_) (singleton_subset_iff.2 h0m)
    have hx' := hsub hx
    simp only [mem_insert, mem_singleton] at hx' ⊢
    rcases hx' with rfl | rfl | rfl
    · rfl
    · exact absurd hx hn4
    · exact absurd hx hn5
  refine ⟨h0eq, Finset.eq_empty_of_forall_notMem (fun x hx => ?_)⟩
  have h1 : x ∈ supp 14 D (src D ((pos 0).1, !(pos 0).2)) := by
    have hx' := hsubG hx
    simp only [mem_insert, mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · have hp := sem_inelig_pure sem_g14_gr h.1 (sem_g14_comp hD)
        (fun u hu => nbr_diff_exists 4 u hu.symm (by decide)) h4 hx
      have ht : tag D (pos 0).1 = true := by
        obtain ⟨hj, -, h10, -, -⟩ := hpos.2.1 h0
        have hW : pos 0 ∈ sem_W 14 D 10 := sem_mem_W.2 ⟨hj, h10, fun hc => by
          have := hsubG hc; simp at this⟩
        exact sem_W_and h.1 hW
      exact absurd (sem_supp_and_sub h.1 (hpos.2.1 h0).1 ht (!(pos 0).2) hx) hn4
    · have ht : tag D (pos 0).1 = true := by
        obtain ⟨hj, -, h10, -, -⟩ := hpos.2.1 h0
        have hW : pos 0 ∈ sem_W 14 D 10 := sem_mem_W.2 ⟨hj, h10, fun hc => by
          have := hsubG hc; simp at this⟩
        exact sem_W_and h.1 hW
      exact absurd (sem_supp_and_sub h.1 (hpos.2.1 h0).1 ht (!(pos 0).2) hx) hn5
  rw [h0eq, mem_singleton] at h1
  subst h1
  have := hsubG hx; simp at this
def WeakMinBranch14 (D : Dag) (b : Fin 14 → ℕ) : Prop :=
  ∀ v ∈ eligSet 14 D, 2 ≤ fanout D (b v) ∧ v ∈ supp 14 D (b v) ∧
    (v ≠ 0 → supp 14 D (b v) = {v}) ∧ (v = 0 → supp 14 D (b v) ⊆ {0, 4, 5}) ∧
    sem_Chain 14 D v.val (b v) ∧ ∀ w, 2 ≤ fanout D w → v ∈ supp 14 D w → b v ≤ w
theorem weakMinBranch_pure {D : Dag} {b : Fin 14 → ℕ} (hb : WeakMinBranch14 D b) :
    WeakPureBranch14 D b := fun v hv =>
  ⟨(hb v hv).1, (hb v hv).2.1, (hb v hv).2.2.1, (hb v hv).2.2.2.1⟩
theorem weakMin_to_min {D : Dag} {b : Fin 14 → ℕ} (hb : WeakMinBranch14 D b)
    (h0 : (0 : Fin 14) ∈ ineligSet 14 D) : sem_MinBranch 14 D b := fun v hv =>
  ⟨(hb v hv).1, (hb v hv).2.2.1 (fun hv0 => (mem_sdiff.mp h0).2 (hv0 ▸ hv)),
   (hb v hv).2.2.2.2.1, (hb v hv).2.2.2.2.2⟩
theorem exists_weakMinBranch14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ b : Fin 14 → ℕ, WeakMinBranch14 D b := by
  classical
  have hS := h.1
  have hC := sem_g14_comp hD
  have hex : ∀ v : Fin 14, ∃ b, v ∈ eligSet 14 D →
      2 ≤ fanout D b ∧ v ∈ supp 14 D b ∧
      (v ≠ 0 → supp 14 D b = {v}) ∧ (v = 0 → supp 14 D b ⊆ {0, 4, 5}) ∧
      sem_Chain 14 D v.val b ∧ ∀ w, 2 ≤ fanout D w → v ∈ supp 14 D w → b ≤ w := by
    intro v
    by_cases hv : v ∈ eligSet 14 D
    · have hexv : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp 14 D w := mem_eligSet.mp hv
      obtain ⟨h1, h2⟩ := Nat.find_spec hexv
      have hch : sem_Chain 14 D v.val (Nat.find hexv) :=
        sem_carrier_chain hS v _ h2 (fun u hu huv => by
          have := Nat.find_min hexv hu; by_contra hc; exact this ⟨by omega, huv⟩)
      refine ⟨Nat.find hexv, fun _ => ⟨h1, h2, fun hv0 => ?_, fun hv0 => ?_, hch,
        fun w hw1 hw2 => Nat.find_min' hexv ⟨hw1, hw2⟩⟩⟩
      · exact Finset.Subset.antisymm
          (sem_dom_pure sem_g14_gr hS hC v (fun u hu => nbr_diff_exists v u hu.symm hv0) _ (sem_chain_dom hS hch))
          (singleton_subset_iff.mpr h2)
      · subst hv0; exact sem_dom_sub0 hS hD _ (sem_chain_dom hS hch)
    · exact ⟨0, fun hc => absurd hc hv⟩
  choose b hb using hex
  exact ⟨b, fun v hv => hb v hv⟩
theorem weak_code_count {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : WeakPureBranch14 D b) (x : Fin 14)
    (hx : (0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5)) :
    (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card =
      1 + (({x} : Finset (Fin 14)) ∩ eligSet 14 D).card +
        ((residualUnits 14 D b).filter (fun u => x ∈ supp 14 D u.1)).card := by
  have h1 := sem_flow1 sem_g14_gr h (sem_g14_comp hD) x
  have hT : (0 : Fin 14) ∈ ineligSet 14 D ∨ (0 : Fin 14) ∈ ({x} : Finset (Fin 14)) ∨
      ((4 : Fin 14) ∉ ({x} : Finset (Fin 14)) ∧ (5 : Fin 14) ∉ ({x} : Finset (Fin 14))) := by
    rcases hx with h0 | ⟨h4, h5⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inr ⟨by simp [Ne.symm h4], by simp [Ne.symm h5]⟩)
  have h2 := weak_surplus_carrierT_eq h.1 b hb {x} hT
  have h3 : (residualUnits 14 D b).filter (fun u => (supp 14 D u.1 ∩ {x}).Nonempty) =
      (residualUnits 14 D b).filter (fun u => x ∈ supp 14 D u.1) := by
    ext u; simp only [mem_filter]; refine and_congr_right fun _ => ?_
    exact ⟨fun ⟨y, hy⟩ => by rw [mem_inter, mem_singleton] at hy; exact hy.2 ▸ hy.1,
      fun hx => ⟨x, mem_inter.2 ⟨hx, mem_singleton_self x⟩⟩⟩
  rw [h3] at h2; omega
theorem weak_saturated {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : WeakPureBranch14 D b) {u0 : Σ _ : ℕ, ℕ}
    (hres : residualUnits 14 D b = {u0}) {x : Fin 14}
    (hx : (0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5))
    (hsat : 3 ≤ (sem_W 14 D x).card) :
    (sem_W 14 D x).card = 3 ∧ merges 14 D (carrierT 14 D {x}) = ∅ ∧ x ∈ eligSet 14 D ∧
      x ∈ supp 14 D u0.1 := by
  have h1 := weak_code_count h hD b hb x hx
  have h2 : (({x} : Finset (Fin 14)) ∩ eligSet 14 D).card ≤ 1 :=
    (card_le_card inter_subset_left).trans (by simp)
  have h3 := Finset.card_filter_le (residualUnits 14 D b) (fun u => x ∈ supp 14 D u.1)
  rw [hres, card_singleton] at h3
  rw [hres] at h1
  refine ⟨by omega, card_eq_zero.mp (by omega), ?_, ?_⟩
  · by_contra hxe
    have h4 : ({x} : Finset (Fin 14)) ∩ eligSet 14 D = ∅ := by rw [Finset.singleton_inter_of_notMem hxe]
    rw [h4, card_empty] at h1; omega
  · have h4 : 0 < (({u0} : Finset (Σ _ : ℕ, ℕ)).filter (fun u => x ∈ supp 14 D u.1)).card := by omega
    obtain ⟨u, hu⟩ := card_pos.mp h4
    rw [mem_filter, mem_singleton] at hu
    exact hu.1 ▸ hu.2
theorem weak_common_terminals {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : WeakMinBranch14 D b) (hone : Bplus 14 D = (eligSet 14 D).card + 1)
    (X : Finset (Fin 14)) (hX : X.Nonempty)
    (hXok : ∀ x ∈ X, (0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 0 ∧ x ≠ 4 ∧ x ≠ 5))
    (hsat : ∀ x ∈ X, 3 ≤ (sem_W 14 D x).card) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W 14 D x ∧ Q ∈ sem_W 14 D x := by
  have hS := h.1
  have hbp := weakMinBranch_pure hb
  have hcard : (residualUnits 14 D b).card = 1 := by
    have := weak_card_residual hS b hbp; omega
  obtain ⟨u0, hres⟩ := card_eq_one.mp hcard
  have hu0 : u0 ∈ residualUnits 14 D b := by rw [hres]; exact mem_singleton_self _
  have hu0u : u0 ∈ units 14 D := (mem_filter.mp (mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by have := (mem_units.mp hu0u).2; omega
  have hx45 : ∀ x ∈ X, (0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5) := fun x hx =>
    (hXok x hx).elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
  refine sem_two_arms sem_g14_gr h (sem_g14_comp hD) X hX
    (fun x hx => (weak_saturated h hD b hbp hres (hx45 x hx) (hsat x hx)).2.1)
    u0.1 (fun x hx => (weak_saturated h hD b hbp hres (hx45 x hx) (hsat x hx)).2.2.2) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, -, hxe, hxr⟩ := weak_saturated h hD b hbp hres (hx45 x hx) (hsat x hx)
  by_contra hc
  have hw2 : 2 ≤ fanout D w := by omega
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 14 D := by
    rw [unitsPlus, mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
      by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 14 D b
  · obtain ⟨v, hv, hveq⟩ := mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    by_cases hv0 : v = 0
    · subst hv0
      rcases hXok x hx with h0I | ⟨hx0, hx4, hx5⟩
      · exact (mem_sdiff.mp h0I).2 hv
      · have hsub := (hb 0 hv).2.2.2.1 rfl (hbv.symm ▸ hxw)
        simp only [mem_insert, mem_singleton] at hsub
        rcases hsub with rfl | rfl | rfl
        · exact hx0 rfl
        · exact hx4 rfl
        · exact hx5 rfl
    · have hsv := (hb v hv).2.2.1 hv0
      rw [hbv] at hsv
      rw [hsv, mem_singleton] at hxw
      have hmin := (hb x hxe).2.2.2.2.2 u0.1 hfr hxr
      rw [hxw, hbv] at hmin
      omega
  · have hwres : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 14 D b := mem_sdiff.mpr ⟨hwu, hwr⟩
    rw [hres, mem_singleton] at hwres
    have : w = u0.1 := congrArg Sigma.fst hwres
    omega
theorem bz_card {n : ℕ} {D : Dag} (hS : Strict n D) (Z : Finset ℕ)
    (hZ : ∀ b ∈ Z, 2 ≤ fanout D b ∧ supp n D b = ∅) : Z.card ≤ Bzero n D := by
  have hsub : Z ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
    fun b hb => sem_bzero_mem hS (hZ b hb).1 (hZ b hb).2
  calc Z.card = ∑ _w ∈ Z, 1 := by simp
    _ ≤ ∑ w ∈ Z, (fanout D w - 1) :=
        Finset.sum_le_sum (fun w hw => by have := (hZ w hw).1; omega)
    _ ≤ Bzero n D := Finset.sum_le_sum_of_subset hsub
theorem cnt_main2 {n : ℕ} {D : Dag} (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L3 : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L3, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L3, ∀ T' ∈ L3, T ≠ T' → (T ∩ T').card ≤ 1)
    (L2 : Finset (Finset (Fin n)))
    (h2 : ∀ M ∈ L2, M.card = 2 ∧ sup_Occ n D P M ∧ ∀ T ∈ L3, ¬ M ⊆ T)
    (E : Finset (ℕ × Bool)) (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P))
    (Lab : Finset (Fin n)) (U : Fin n → Finset (Fin n))
    (hw : ∀ f ∈ Lab, ∃ e, sup_Wit n D P (U f) f e)
    (hUL3 : ∀ f ∈ Lab, ∀ T ∈ L3, (U f ∩ T).card ≤ 1)
    (hUL2 : ∀ f ∈ Lab, ∀ M ∈ L2, (U f ∩ M).card ≤ 1)
    (hEdis : ∀ e ∈ E, ∀ f ∈ Lab, ∀ w, sup_Wit n D P (U f) f w → e ≠ w) :
    2 * L3.card + L2.card + E.card + Lab.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  classical
  choose! wit hwit using hw
  let S := Lab.filter (fun f => ∀ M, M ⊆ U f → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M)
  have hSL : S ⊆ Lab := filter_subset _ _
  have hno : ∀ f ∈ Lab \ S, ∃ M, M ⊆ U f ∧ M.card = 2 ∧ f ∈ M ∧ sup_Occ n D P M := by
    intro f hf
    rw [mem_sdiff, mem_filter] at hf
    by_contra hc
    exact hf.2 ⟨hf.1, fun M h1 h2 h4 h5 => hc ⟨M, h1, h2, h4, h5⟩⟩
  choose! pr hpr using hno
  have hL2dis : Disjoint L2 ((Lab \ S).image pr) := by
    rw [disjoint_left]
    intro M hM2 hMpr
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hMpr
    have hsub := (hpr f hf).1
    have hcard := (hpr f hf).2.1
    have := card_le_card (Finset.subset_inter hsub (Finset.Subset.refl _))
    have := hUL2 f (mem_sdiff.1 hf).1 _ hM2
    omega
  have hX := sup_charge hS hP L3 h3 hint (L2 ∪ (Lab \ S).image pr) (by
    intro M hM
    rcases mem_union.1 hM with hM2 | hMpr
    · obtain ⟨hc, ho, hnoT⟩ := h2 M hM2
      refine ⟨ho, by omega, fun hL => by have := (h3 _ hL).1; omega, by omega, by omega,
        fun _ T hT => hnoT T hT⟩
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 hMpr
      obtain ⟨h1, h2', -, h4⟩ := hpr f hf
      refine ⟨h4, by omega, fun hL => by have := (h3 _ hL).1; omega, by omega, by omega,
        fun _ T hT hsub => ?_⟩
      have := card_le_card (Finset.subset_inter h1 hsub)
      have := hUL3 f (mem_sdiff.1 hf).1 T hT
      omega)
  rw [card_union_of_disjoint hL2dis] at hX
  have hcnt := sup_count_disj hS P E hE Lab S U wit hwit hSL
    (fun f hf => sup_wit_single (hwit f (hSL hf)) (mem_filter.1 hf).2)
    (fun e he f hf => hEdis e he f hf (wit f) (hwit f hf))
  have hfib : (Lab \ S).card ≤ 2 * ((Lab \ S).image pr).card := by
    refine Finset.card_le_mul_card_image _ 2 (fun M _ => ?_)
    by_cases hne : ((Lab \ S).filter (fun f => pr f = M)).Nonempty
    · obtain ⟨g, hg⟩ := hne
      rw [mem_filter] at hg
      have hM2 : M.card = 2 := hg.2 ▸ (hpr g hg.1).2.1
      rw [← hM2]
      refine card_le_card (fun f hf => ?_)
      rw [mem_filter] at hf
      exact hf.2 ▸ (hpr f hf.1).2.2.1
    · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  have := card_sdiff_add_card_eq_card hSL
  omega
section L3bGen
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem ri_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) {x c : Fin n} (hxc : x ≠ c) (hdiff : ∃ z, G x z ∧ ¬ G c z) (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1) {w : ℕ}
    (hw : x ∈ supp n D w ∧ c ∈ supp n D w) :
    ∃ e0, ∀ e ∈ sem_W n D x, e ≠ e0 → c ∈ supp n D (src D e) := by
  classical
  obtain ⟨z, hxz, hcz⟩ := hdiff
  obtain ⟨-, -, h2, e1, he1, ht1, -⟩ := sem_diff_two_exits hG h hC b hb hxc hx hres hw hxz hcz
  have hc1 : ((exitArcs n D (carrierDiff n D x c)).erase e1).card = 1 := by
    rw [Finset.card_erase_of_mem he1, h2]
  obtain ⟨e0, he0⟩ := card_eq_one.1 hc1
  refine ⟨e0, fun e he hne => ?_⟩
  by_contra hce
  obtain ⟨h1, h4, h5⟩ := sem_mem_W.1 he
  have hmem : e ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.2 ⟨h1, ⟨h4, hce⟩, fun hc => h5 hc.1⟩
  have hne1 : e ≠ e1 := fun hee => by
    have ht := sem_W_and h.1 he; rw [hee, ht1] at ht; exact Bool.noConfusion ht
  have hemem : e ∈ (exitArcs n D (carrierDiff n D x c)).erase e1 := mem_erase.2 ⟨hne1, hmem⟩
  rw [he0, mem_singleton] at hemem
  exact hne hemem
theorem gct_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : sem_MinBranch n D b) {u0 : Σ _ : ℕ, ℕ} (hu0 : u0 ∈ residualUnits n D b)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hsat : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅ ∧ x ∈ supp n D u0.1 ∧
      ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → u = u0) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hu0u : u0 ∈ units n D := (mem_filter.mp (mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (hsat x hx).1) u0.1
    (fun x hx => (hsat x hx).2.1) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, hxr, huniq⟩ := hsat x hx
  have hxe : x ∈ eligSet n D := mem_eligSet.2 ⟨u0.1, hfr, hxr⟩
  by_contra hc
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
      by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have h1 := huniq _ (mem_sdiff.mpr ⟨hwu, hwr⟩) hxw
    have : w = u0.1 := congrArg Sigma.fst h1
    omega
theorem full_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i v : Fin n} (hsep : ∀ u : Fin n, u ≠ i → ∃ z, G i z ∧ ¬ G u z) (hi : i ∈ ineligSet n D) {e : ℕ × Bool}
    (he : sem_W n D i = {e}) (hiv : G i v)
    (hv : ∀ p ∈ sem_W n D v, p.1 ≠ e.1 → ¬ supp n D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  refine sem_full_support hG h hC hsep hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W n D i := by rw [he]; exact mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step n D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := sem_noempty_unique hG h hC hB0 hsep hi hreach2
    have hf : fanout D w = 1 := by
      have h1 := sem_step_fanout hw2
      by_contra hne
      have h2 := sem_branch_empty hG hS hC hsep hi hch (by omega)
      have h4 := sem_bzero_branch hS hB0 (b := w) (by omega)
      rw [h2] at h4
      exact not_nonempty_empty h4
    have hsub : supp n D w ⊆ {i} := sem_dom_pure hG hS hC i hsep w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp n D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W n D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)
end L3bGen
def sideL : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6}
def sideR : Finset (Fin 14) := {7, 8, 9, 10, 11, 12, 13}
def os_ptL (k : Fin 7) : Fin 14 := ⟨k.val, by omega⟩
def os_ptR (k : Fin 7) : Fin 14 := ⟨7 + k.val, by omega⟩
theorem os_ptL_inj : Function.Injective os_ptL := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simpa [os_ptL] using this)
theorem os_ptR_inj : Function.Injective os_ptR := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; dsimp [os_ptR] at this; omega)
def maskFin7 (m : Fin 128) : Finset (Fin 7) :=
  Finset.univ.filter (fun k : Fin 7 => m.val.testBit k.val)
theorem exists_maskFin7 (S : Finset (Fin 7)) : ∃ m : Fin 128, maskFin7 m = S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by ext k; simp [maskFin7]⟩
  | insert a s _ ih =>
    obtain ⟨m, hm⟩ := ih
    have hpow : 2 ^ a.val < 2 ^ 7 := Nat.pow_lt_pow_right (by omega) a.isLt
    refine ⟨⟨m.val ||| 2 ^ a.val, Nat.or_lt_two_pow m.isLt hpow⟩, ?_⟩
    ext k
    simp only [maskFin7, mem_filter, mem_univ, true_and, Nat.testBit_or,
      Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, mem_insert]
    have hmk : m.val.testBit k.val = true ↔ k ∈ s := by
      have := Finset.ext_iff.1 hm k
      simpa [maskFin7] using this
    rw [hmk, Fin.ext_iff]
    tauto
theorem g14_sides : ∀ a b : Fin 14, hc_adjB a b = true →
    decide (a.val < 7) ≠ decide (b.val < 7) := by decide +kernel
theorem sideL_indep : ∀ a ∈ sideL, ∀ b ∈ sideL, ¬ Adj a b := by
  intro a ha b hb hab
  have h1 := g14_sides a b ((hc_adjB_iff a b).2 hab)
  have h2 : ∀ x ∈ sideL, decide (x.val < 7) = true := by decide +kernel
  rw [h2 a ha, h2 b hb] at h1; exact h1 rfl
theorem sideR_indep : ∀ a ∈ sideR, ∀ b ∈ sideR, ¬ Adj a b := by
  intro a ha b hb hab
  have h1 := g14_sides a b ((hc_adjB_iff a b).2 hab)
  have h2 : ∀ x ∈ sideR, decide (x.val < 7) = false := by decide +kernel
  rw [h2 a ha, h2 b hb] at h1; exact h1 rfl
theorem g14_lost {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (J : Finset (Fin 14))
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ i ≠ 0 ∧ 2 ≤ (sem_g14_nb i ∩ P).card ∧
      ¬ sup_Occ 14 D P (sem_g14_nb i ∩ P)) :
    J.card ≤ Bzero 14 D := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  have hocc : ∀ i ∈ J, ∀ q, (∀ a ∈ P, (a ∈ supp 14 D q ↔ Adj i a)) → False := by
    intro i hi q hq
    refine (hJ i hi).2.2.2 ⟨q, ?_⟩
    ext a
    rw [mem_inter, mem_inter, g14_mem_nb]
    exact ⟨fun h1 => ⟨(hq a h1.2).1 h1.1, h1.2⟩, fun h1 => ⟨(hq a h1.2).2 h1.1, h1.2⟩⟩
  have hb : ∀ i ∈ J, ∃ b, sem_Chain 14 D i.val b ∧ 2 ≤ fanout D b ∧ supp 14 D b = ∅ := by
    intro i hi
    rcases sem_inelig_reach hG h hC (fun u hu => nbr_diff_exists i u hu.symm (hJ i hi).2.1) (hJ i hi).1 with hch | hb
    · obtain ⟨j, s, -, -, -, hq⟩ := sem_exact_nbhd hG h.1 hC P hPi hch
      exact absurd hq (hocc i hi _)
    · exact hb
  choose! br hbr using hb
  have hinj : Set.InjOn br J := by
    intro i hi j hj hij
    by_contra hne
    have hle := sup_g14_inter i j hne P
    have hge := (hJ j hj).2.2.1
    have hsub_ne : ((sem_g14_nb j ∩ P) \ (sem_g14_nb i ∩ (sem_g14_nb j ∩ P))).Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro hemp
      have hs : sem_g14_nb j ∩ P ⊆ sem_g14_nb i ∩ (sem_g14_nb j ∩ P) := Finset.sdiff_eq_empty_iff_subset.1 hemp
      have := card_le_card hs
      omega
    obtain ⟨a, ha⟩ := hsub_ne
    rw [mem_sdiff, mem_inter, mem_inter, mem_inter] at ha
    have hja : Adj j a := g14_mem_nb.1 ha.1.1
    have hia : ¬ Adj i a := fun h' => ha.2 ⟨g14_mem_nb.2 h', ha.1.1, ha.1.2⟩
    have h1 := sem_shared_exact hG h.1 hC P hPi (hbr i hi).1
      (hij ▸ sem_chain_dom h.1 (hbr j hj).1) ⟨a, ha.1.2, hja, hia⟩
    obtain ⟨_, _, -, -, -, -, hq⟩ := h1
    exact hocc i hi _ hq
  calc J.card = (J.image br).card := (card_image_of_injOn hinj).symm
    _ ≤ Bzero 14 D := bz_card h.1 (J.image br) (fun b hb => by
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hb
        exact (hbr i hi).2)
theorem g14_count {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) (hP7 : P.card ≤ 7) (hPe : P ⊆ eligSet 14 D)
    (hP0 : (0 : Fin 14) ∈ ineligSet 14 D ∨ (0 : Fin 14) ∈ P ∨ ((4 : Fin 14) ∉ P ∧ (5 : Fin 14) ∉ P))
    (Oc3 Oc2 Ct Iin : Finset (Fin 14))
    (hOc3 : ∀ i ∈ Oc3, (sem_g14_nb i ∩ P).card = 3 ∧ sup_Occ 14 D P (sem_g14_nb i ∩ P))
    (hOc2 : ∀ i ∈ Oc2, (sem_g14_nb i ∩ P).card = 2 ∧ sup_Occ 14 D P (sem_g14_nb i ∩ P))
    (hCt : ∀ c ∈ Ct, c ∉ Oc3 ∧ c ∉ Oc2 ∧
      (((sem_g14_nb c ∩ P).card = 3 ∨ c ∈ Iin) → ¬ sup_Occ 14 D P (sem_g14_nb c ∩ P)))
    (hIin : ∀ i ∈ Iin, i ∈ ineligSet 14 D ∧
      (i ≠ 0 → 2 ≤ (sem_g14_nb i ∩ P).card) ∧
      (i = 0 → (10 : Fin 14) ∈ P ∧ (4 : Fin 14) ∉ P ∧ (5 : Fin 14) ∉ P ∧
        ∀ c ∈ Ct, (10 : Fin 14) ∉ sem_g14_nb c ∩ P)) :
    2 * Oc3.card + Oc2.card + Iin.card + (Ct.biUnion (fun c => sem_g14_nb c ∩ P)).card +
      (eligSet 14 D).card ≤ 2 * P.card + Bplus 14 D := by
  classical
  have hG := sem_g14_gr
  have hC := sem_g14_comp hD
  obtain ⟨b, hb⟩ := exists_weakPureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned14 h hD
  have hEinj : Set.InjOn pos Iin := fun i hi j hj hij =>
    hpos.2.2 i (hIin i hi).1 j (hIin j hj).1 hij
  have hnbP_inj : ∀ S : Finset (Fin 14), (∀ i ∈ S, 2 ≤ (sem_g14_nb i ∩ P).card) →
      Set.InjOn (fun i => sem_g14_nb i ∩ P) S := by
    intro S hS i hi j hj heq
    by_contra hne
    have hle := sup_g14_inter i j hne P
    have hsub : sem_g14_nb j ∩ P ⊆ sem_g14_nb i ∩ (sem_g14_nb j ∩ P) := by
      intro x hx
      have hx' : x ∈ sem_g14_nb i ∩ P := by dsimp only at heq; rwa [heq]
      exact mem_inter.2 ⟨(mem_inter.1 hx').1, hx⟩
    have := card_le_card hsub
    have := hS j hj
    omega
  have hE : ∀ e ∈ Iin.image pos, e ∈ exitArcs 14 D (carrierT 14 D P) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := mem_image.1 he
    by_cases hi0 : i = 0
    · subst hi0
      obtain ⟨h10P, h4P, h5P, -⟩ := (hIin 0 hi).2.2 rfl
      obtain ⟨hj, hsubG, h10s, -, -⟩ := hpos.2.1 (hIin 0 hi).1
      rw [exitArcs, mem_filter]
      refine ⟨mem_product.2 ⟨mem_range.2 hj, mem_univ _⟩,
        sup_mem_carrier.2 ⟨10, mem_inter.2 ⟨h10s, h10P⟩⟩, ?_⟩
      rw [sup_mem_carrier]
      rintro ⟨x, hx⟩
      rw [mem_inter] at hx
      have hx45 := hsubG hx.1
      simp only [mem_insert, mem_singleton] at hx45
      rcases hx45 with rfl | rfl
      · exact h4P hx.2
      · exact h5P hx.2
    · obtain ⟨hj, hemp, hnb, -⟩ := hpos.1 i (hIin i hi).1 hi0
      have hne : (sem_g14_nb i ∩ P).Nonempty := card_pos.1 (by have := (hIin i hi).2.1 hi0; omega)
      obtain ⟨a, ha⟩ := hne
      rw [mem_inter] at ha
      rw [exitArcs, mem_filter]
      refine ⟨mem_product.2 ⟨mem_range.2 hj, mem_univ _⟩,
        sup_mem_carrier.2 ⟨a, mem_inter.2 ⟨hnb a (g14_mem_nb.1 ha.1), ha.2⟩⟩, ?_⟩
      rw [sup_mem_carrier, hemp, Finset.empty_inter]
      exact not_nonempty_empty
  have hlab : ∀ f ∈ Ct.biUnion (fun c => sem_g14_nb c ∩ P), ∃ c ∈ Ct, f ∈ sem_g14_nb c ∩ P :=
    fun f hf => mem_biUnion.1 hf
  choose! ct hct using hlab
  have hmain := cnt_main2 h.1 hP7 (Oc3.image (fun i => sem_g14_nb i ∩ P))
    (fun T hT => by
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hT
      exact hOc3 i hi)
    (fun T hT T' hT' hne => by
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hT
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hT'
      have hsub : (sem_g14_nb i ∩ P) ∩ (sem_g14_nb j ∩ P) ⊆ sem_g14_nb i ∩ (sem_g14_nb j ∩ P) := by
        intro x hx; simp only [mem_inter] at hx ⊢; exact ⟨hx.1.1, hx.2.1, hx.2.2⟩
      exact (card_le_card hsub).trans (sup_g14_inter i j (fun hij => hne (hij ▸ rfl)) P))
    (Oc2.image (fun i => sem_g14_nb i ∩ P))
    (fun M hM => by
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hM
      refine ⟨(hOc2 i hi).1, (hOc2 i hi).2, fun T hT hsub => ?_⟩
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hT
      have hij : i ≠ j := fun h => by
        have h2 := (hOc2 i hi).1; have h3 := (hOc3 j hj).1; rw [h] at h2; omega
      have hle := sup_g14_inter i j hij P
      have hsub' : sem_g14_nb i ∩ P ⊆ sem_g14_nb i ∩ (sem_g14_nb j ∩ P) := by
        intro x hx; exact mem_inter.2 ⟨(mem_inter.1 hx).1, hsub hx⟩
      have hc := card_le_card hsub'
      have h2 := (hOc2 i hi).1
      omega)
    (Iin.image pos) hE (Ct.biUnion (fun c => sem_g14_nb c ∩ P)) (fun f => sem_g14_nb (ct f) ∩ P)
    (fun f hf => by
      obtain ⟨hc, hfc⟩ := hct f hf
      refine sup_wit_exists hG h.1 hC (X := insert (ct f) (P \ (sem_g14_nb (ct f) ∩ P)))
        inter_subset_right ?_ ?_ (fun a ha => Finset.mem_insert_of_mem ha) hfc
        ⟨ct f, mem_insert_self _ _, adj_symm (g14_mem_nb.1 (mem_inter.1 hfc).1)⟩
      · by_cases hd3 : (sem_g14_nb (ct f) ∩ P).card = 3
        · exact Or.inr ⟨hd3, (hCt _ hc).2.2 (Or.inl hd3)⟩
        · have hle3 : (sem_g14_nb (ct f) ∩ P).card ≤ 3 :=
            (card_le_card inter_subset_left).trans (by rw [g14_nb_eq]; exact degree_le_three _)
          exact Or.inl (by omega)
      · have hno : ∀ a ∈ P \ (sem_g14_nb (ct f) ∩ P), ¬ Adj (ct f) a := by
          intro a ha hadj
          rw [mem_sdiff, mem_inter, g14_mem_nb] at ha
          exact ha.2 ⟨hadj, ha.1⟩
        intro a ha b hb
        rcases mem_insert.1 ha with rfl | ha <;> rcases mem_insert.1 hb with rfl | hb
        · exact adj_irrefl _
        · exact hno b hb
        · exact fun hab => hno a ha (adj_symm hab)
        · exact hPi a (mem_sdiff.1 ha).1 b (mem_sdiff.1 hb).1)
    (fun f hf T hT => by
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hT
      have hsub : (sem_g14_nb (ct f) ∩ P) ∩ (sem_g14_nb i ∩ P) ⊆ sem_g14_nb i ∩ (sem_g14_nb (ct f) ∩ P) := by
        intro x hx; simp only [mem_inter] at hx ⊢; exact ⟨hx.2.1, hx.1.1, hx.1.2⟩
      exact (card_le_card hsub).trans (sup_g14_inter i (ct f) (fun hij => (hCt _ (hct f hf).1).1 (hij ▸ hi)) P))
    (fun f hf M hM => by
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hM
      have hsub : (sem_g14_nb (ct f) ∩ P) ∩ (sem_g14_nb i ∩ P) ⊆ sem_g14_nb i ∩ (sem_g14_nb (ct f) ∩ P) := by
        intro x hx; simp only [mem_inter] at hx ⊢; exact ⟨hx.2.1, hx.1.1, hx.1.2⟩
      exact (card_le_card hsub).trans (sup_g14_inter i (ct f) (fun hij => (hCt _ (hct f hf).1).2.1 (hij ▸ hi)) P))
    (fun e he f hf w hw hew => by
      obtain ⟨i, hi, rfl⟩ := mem_image.1 he
      obtain ⟨hc, -⟩ := hct f hf
      have hwsub : supp 14 D (src D (pos i)) ∩ P ⊆ sem_g14_nb (ct f) ∩ P := hew ▸ hw.2.2.2.2.2.1
      by_cases hi0 : i = 0
      · subst hi0
        obtain ⟨h10P, -, -, hno10⟩ := (hIin 0 hi).2.2 rfl
        have h10m : (10 : Fin 14) ∈ supp 14 D (src D (pos 0)) ∩ P :=
          mem_inter.2 ⟨(hpos.2.1 (hIin 0 hi).1).2.2.1, h10P⟩
        exact hno10 (ct f) hc (hwsub h10m)
      · have hnbi : sem_g14_nb i ∩ P ⊆ supp 14 D (src D (pos i)) ∩ P := fun a ha => by
          rw [mem_inter] at ha ⊢
          exact ⟨(hpos.1 i (hIin i hi).1 hi0).2.2.1 a (g14_mem_nb.1 ha.1), ha.2⟩
        by_cases hci : ct f = i
        · rw [hci] at hwsub
          have heq : supp 14 D (src D (pos i)) ∩ P = sem_g14_nb i ∩ P := Finset.Subset.antisymm hwsub hnbi
          exact (hCt (ct f) hc).2.2 (Or.inr (hci ▸ hi)) ⟨src D (pos i), hci ▸ heq⟩
        · have hle := sup_g14_inter i (ct f) (Ne.symm hci) P
          have hsub' : sem_g14_nb i ∩ P ⊆ sem_g14_nb i ∩ (sem_g14_nb (ct f) ∩ P) := fun a ha =>
            mem_inter.2 ⟨(mem_inter.1 ha).1, hwsub (hnbi ha)⟩
          have hcard := card_le_card hsub'
          have hge2 := (hIin i hi).2.1 hi0
          omega)
  have h4 := carrier_flow_union h P (by rw [g14_supp_out hD]; simp)
  have h5 := weak_surplus_carrierT_le h.1 b hb P hP0
  rw [inter_eq_left.2 hPe] at h5
  rw [card_image_of_injOn (hnbP_inj Oc3 (fun i hi => by have := (hOc3 i hi).1; omega)),
    card_image_of_injOn (hnbP_inj Oc2 (fun i hi => by have := (hOc2 i hi).1; omega)),
    card_image_of_injOn hEinj] at hmain
  omega
def kPos7 : Finset (Fin 7) := {1, 2, 3, 4, 5, 6}
theorem g14_sideR_step {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ m : Fin 128,
      let I := ineligSet 14 D
      let P := sideR \ I
      let Oc := maskFin7 m
      let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 3)
      let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 2)
      let Ct := kPos7 \ Oc
      let IinBase := kPos7.filter (fun k : Fin 7 => os_ptL k ∈ I ∧ g14_nbB (os_ptL k) ⊆ P)
      let Lab := Ct.biUnion (fun k => g14_nbB (os_ptL k) ∩ P)
      let extra0 := if (0 : Fin 14) ∈ I ∧ (10 : Fin 14) ∉ I ∧ (10 : Fin 14) ∉ Lab then 1 else 0
      (∀ k ∈ Oc, k ∈ kPos7 ∧ g14_nbB (os_ptL k) ⊆ P) ∧
      2 * Oc3.card + Oc2.card + IinBase.card + extra0 + Lab.card +
        (14 - I.card) ≤ 2 * P.card + Bplus 14 D ∧
      (IinBase \ Oc).card ≤ Bzero 14 D := by
  classical
  set I := ineligSet 14 D
  set P := sideR \ I
  have hPl : P ⊆ sideR := sdiff_subset
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b := fun a ha b hb => sideR_indep a (hPl ha) b (hPl hb)
  have hP7 : P.card ≤ 7 := (card_le_card hPl).trans (by decide)
  have hPe : P ⊆ eligSet 14 D := fun a ha => by
    by_contra hne; exact (mem_sdiff.1 ha).2 (sem_mem_inelig.2 hne)
  have h45notP : (4 : Fin 14) ∉ P ∧ (5 : Fin 14) ∉ P :=
    ⟨fun h4 => (by decide : (4 : Fin 14) ∉ sideR) (hPl h4),
     fun h5 => (by decide : (5 : Fin 14) ∉ sideR) (hPl h5)⟩
  let Oc := kPos7.filter (fun k : Fin 7 =>
    g14_nbB (os_ptL k) ⊆ P ∧ sup_Occ 14 D P (sem_g14_nb (os_ptL k) ∩ P))
  obtain ⟨m, hm⟩ := exists_maskFin7 Oc
  refine ⟨m, ?_⟩
  dsimp only
  rw [hm]
  let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 3)
  let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptL k)).card = 2)
  let Ct := kPos7 \ Oc
  let IinBase := kPos7.filter (fun k : Fin 7 => os_ptL k ∈ I ∧ g14_nbB (os_ptL k) ⊆ P)
  let Lab := Ct.biUnion (fun k => g14_nbB (os_ptL k) ∩ P)
  let Iin := if (0 : Fin 14) ∈ I ∧ (10 : Fin 14) ∉ I ∧ (10 : Fin 14) ∉ Lab then insert (0 : Fin 7) IinBase else IinBase
  have hpos_ne0 : ∀ k : Fin 7, k ∈ kPos7 → os_ptL k ≠ 0 := by decide +kernel
  have h0not : (0 : Fin 7) ∉ IinBase := fun h0 =>
    (by decide : (0 : Fin 7) ∉ kPos7) (mem_filter.1 h0).1
  have hIinCard : Iin.card = IinBase.card + (if (0 : Fin 14) ∈ I ∧ (10 : Fin 14) ∉ I ∧ (10 : Fin 14) ∉ Lab then 1 else 0) := by
    dsimp only [Iin]
    split_ifs
    · rw [card_insert_of_notMem h0not]
    · omega
  have hLabEq : ((Ct.image os_ptL).biUnion (fun c => sem_g14_nb c ∩ P)) = Lab := by
    ext x
    simp only [Lab, mem_biUnion, mem_image, mem_inter, g14_nb_eq]
    constructor
    · rintro ⟨c, ⟨k, hk, rfl⟩, hx⟩; exact ⟨k, hk, hx⟩
    · rintro ⟨k, hk, hx⟩; exact ⟨os_ptL k, ⟨k, hk, rfl⟩, hx⟩
  have hdegL : ∀ k : Fin 7, k ∈ kPos7 → (g14_nbB (os_ptL k)).card = 3 := by decide +kernel
  have hcnt := g14_count h hD P hPi hP7 hPe (Or.inr (Or.inr h45notP))
    (Oc3.image os_ptL) (Oc2.image os_ptL) (Ct.image os_ptL) (Iin.image os_ptL)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      rw [mem_filter] at hk
      have hko := mem_filter.1 hk.1
      have hinter : sem_g14_nb (os_ptL k) ∩ P = g14_nbB (os_ptL k) := by
        rw [g14_nb_eq, inter_eq_left.2 hko.2.1]
      exact ⟨by rw [hinter]; exact hk.2, hko.2.2⟩)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      rw [mem_filter] at hk
      have hko := mem_filter.1 hk.1
      have hinter : sem_g14_nb (os_ptL k) ∩ P = g14_nbB (os_ptL k) := by
        rw [g14_nb_eq, inter_eq_left.2 hko.2.1]
      exact ⟨by rw [hinter]; exact hk.2, hko.2.2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hc
      have hkpos : k ∈ kPos7 := (mem_sdiff.1 hk).1
      have hnk : k ∉ Oc := (mem_sdiff.1 hk).2
      refine ⟨fun h3 => ?_, fun h2 => ?_, fun hor hocc => ?_⟩
      · obtain ⟨k', hk', heq⟩ := mem_image.1 h3
        rw [os_ptL_inj heq] at hk'; exact hnk (mem_filter.1 hk').1
      · obtain ⟨k', hk', heq⟩ := mem_image.1 h2
        rw [os_ptL_inj heq] at hk'; exact hnk (mem_filter.1 hk').1
      · rcases hor with h3 | hin
        · have hsub : g14_nbB (os_ptL k) ⊆ P := by
            have heq : sem_g14_nb (os_ptL k) ∩ P = g14_nbB (os_ptL k) :=
              eq_of_subset_of_card_le inter_subset_left (by rw [h3, hdegL k hkpos])
            rw [← heq]; exact inter_subset_right
          exact hnk (mem_filter.2 ⟨hkpos, hsub, hocc⟩)
        · obtain ⟨k', hk', heq⟩ := mem_image.1 hin
          have hk'eq := os_ptL_inj heq; subst hk'eq
          have hsub : g14_nbB (os_ptL k') ⊆ P := by
            dsimp only [Iin] at hk'
            split_ifs at hk'
            · rcases mem_insert.1 hk' with rfl | hkB
              · exact absurd hkpos (by decide)
              · exact (mem_filter.1 hkB).2.2
            · exact (mem_filter.1 hk').2.2
          exact hnk (mem_filter.2 ⟨hkpos, hsub, hocc⟩))
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      dsimp only [Iin] at hk
      split_ifs at hk with hcond
      · rcases mem_insert.1 hk with rfl | hkB
        · refine ⟨hcond.1, fun hc => absurd rfl hc, fun _ =>
            ⟨mem_sdiff.2 ⟨by decide, hcond.2.1⟩, h45notP.1, h45notP.2, fun c hc h10c => hcond.2.2 ?_⟩⟩
          rw [← hLabEq]; exact mem_biUnion.2 ⟨c, hc, h10c⟩
        · have hkpos : k ∈ kPos7 := (mem_filter.1 hkB).1
          have hki := (mem_filter.1 hkB).2
          have hkne0 : os_ptL k ≠ 0 := hpos_ne0 k hkpos
          have hinter : sem_g14_nb (os_ptL k) ∩ P = g14_nbB (os_ptL k) := by
            rw [g14_nb_eq, inter_eq_left.2 hki.2]
          exact ⟨hki.1, fun _ => by rw [hinter, hdegL k hkpos]; omega, fun h0 => absurd h0 hkne0⟩
      · have hkpos : k ∈ kPos7 := (mem_filter.1 hk).1
        have hki := (mem_filter.1 hk).2
        have hkne0 : os_ptL k ≠ 0 := hpos_ne0 k hkpos
        have hinter : sem_g14_nb (os_ptL k) ∩ P = g14_nbB (os_ptL k) := by
          rw [g14_nb_eq, inter_eq_left.2 hki.2]
        exact ⟨hki.1, fun _ => by rw [hinter, hdegL k hkpos]; omega, fun h0 => absurd h0 hkne0⟩)
  have hlost := g14_lost h hD P hPi ((IinBase \ Oc).image os_ptL)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      rw [mem_sdiff] at hk
      have hkpos : k ∈ kPos7 := (mem_filter.1 hk.1).1
      have hki := (mem_filter.1 hk.1).2
      have hkne0 : os_ptL k ≠ 0 := hpos_ne0 k hkpos
      have hinter : sem_g14_nb (os_ptL k) ∩ P = g14_nbB (os_ptL k) := by
        rw [g14_nb_eq, inter_eq_left.2 hki.2]
      refine ⟨hki.1, hkne0, by rw [hinter, hdegL k hkpos]; omega, fun hocc => hk.2 ?_⟩
      exact mem_filter.2 ⟨hkpos, hki.2, hocc⟩)
  rw [card_image_of_injective _ os_ptL_inj] at hlost
  rw [card_image_of_injective _ os_ptL_inj, card_image_of_injective _ os_ptL_inj,
    card_image_of_injective _ os_ptL_inj, hLabEq, hIinCard] at hcnt
  have hel := inelig_card_add 14 D
  refine ⟨fun k hk => ⟨(mem_filter.1 hk).1, (mem_filter.1 hk).2.1⟩, ?_, hlost⟩
  dsimp only [Oc3, Oc2, Ct, IinBase, Lab, P, I] at hcnt ⊢; omega
def okL_pred (I P : Finset (Fin 14)) (k : Fin 7) : Prop :=
  g14_nbB (os_ptR k) ⊆ P ∨ (os_ptR k = 10 ∧ (0 : Fin 14) ∈ I ∧ (4 : Fin 14) ∈ P ∧ (5 : Fin 14) ∈ P)
instance (I P : Finset (Fin 14)) (k : Fin 7) : Decidable (okL_pred I P k) := by
  unfold okL_pred; infer_instance
theorem g14_sideL_exact {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ m : Fin 128,
      let I := ineligSet 14 D
      let P := sideL \ I
      let Oc := maskFin7 m
      let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 3)
      let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 2)
      let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
      let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ okL_pred I P k)
      let Lab := Ct.biUnion (fun k => g14_nbB (os_ptR k) ∩ P)
      (∀ k : Fin 7, k ∈ Oc ↔ okL_pred I P k ∧ sup_Occ 14 D P (sem_g14_nb (os_ptR k) ∩ P)) ∧
      2 * Oc3.card + Oc2.card + Iin.card + Lab.card +
        (14 - I.card) ≤ 2 * P.card + Bplus 14 D ∧
      (Iin \ Oc).card ≤ Bzero 14 D := by
  classical
  set I := ineligSet 14 D
  set P := sideL \ I
  have hPl : P ⊆ sideL := sdiff_subset
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b := fun a ha b hb => sideL_indep a (hPl ha) b (hPl hb)
  have hP7 : P.card ≤ 7 := (card_le_card hPl).trans (by decide)
  have hPe : P ⊆ eligSet 14 D := fun a ha => by
    by_contra hne; exact (mem_sdiff.1 ha).2 (sem_mem_inelig.2 hne)
  have hP0 : (0 : Fin 14) ∈ ineligSet 14 D ∨ (0 : Fin 14) ∈ P ∨ ((4 : Fin 14) ∉ P ∧ (5 : Fin 14) ∉ P) := by
    by_cases h0 : (0 : Fin 14) ∈ I
    · exact Or.inl h0
    · exact Or.inr (Or.inl (mem_sdiff.2 ⟨by decide, h0⟩))
  have hne0R : ∀ k : Fin 7, os_ptR k ≠ 0 := by decide +kernel
  have hok_ge2 : ∀ k : Fin 7, okL_pred I P k → 2 ≤ (sem_g14_nb (os_ptR k) ∩ P).card := by
    intro k hk
    rcases hk with hsub | ⟨h10, -, h4P, h5P⟩
    · rw [g14_nb_eq, inter_eq_left.2 hsub]
      rcases degree_two_or_three (os_ptR k) (hne0R k) with hd | hd <;> omega
    · rw [h10]
      have hsub : ({4, 5} : Finset (Fin 14)) ⊆ sem_g14_nb 10 ∩ P := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_inter.2 ⟨by decide, h4P⟩
        · exact mem_inter.2 ⟨by decide, h5P⟩
      exact (by decide : 2 ≤ ({4, 5} : Finset (Fin 14)).card).trans (card_le_card hsub)
  let Oc := Finset.univ.filter (fun k : Fin 7 =>
    okL_pred I P k ∧ sup_Occ 14 D P (sem_g14_nb (os_ptR k) ∩ P))
  obtain ⟨m, hm⟩ := exists_maskFin7 Oc
  refine ⟨m, ?_⟩
  dsimp only
  rw [hm]
  let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 3)
  let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 2)
  let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
  let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ okL_pred I P k)
  let Lab := Ct.biUnion (fun k => g14_nbB (os_ptR k) ∩ P)
  have hLabEq : ((Ct.image os_ptR).biUnion (fun c => sem_g14_nb c ∩ P)) = Lab := by
    ext x
    simp only [Lab, mem_biUnion, mem_image, mem_inter, g14_nb_eq]
    constructor
    · rintro ⟨c, ⟨k, hk, rfl⟩, hx⟩; exact ⟨k, hk, hx⟩
    · rintro ⟨k, hk, hx⟩; exact ⟨os_ptR k, ⟨k, hk, rfl⟩, hx⟩
  have hcnt := g14_count h hD P hPi hP7 hPe hP0
    (Oc3.image os_ptR) (Oc2.image os_ptR) (Ct.image os_ptR) (Iin.image os_ptR)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      rw [mem_filter] at hk
      exact ⟨by rw [g14_nb_eq]; exact hk.2, (mem_filter.1 hk.1).2.2⟩)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      rw [mem_filter] at hk
      exact ⟨by rw [g14_nb_eq]; exact hk.2, (mem_filter.1 hk.1).2.2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hc
      have hnk : k ∉ Oc := (mem_sdiff.1 hk).2
      refine ⟨fun h3 => ?_, fun h2 => ?_, fun hor hocc => ?_⟩
      · obtain ⟨k', hk', heq⟩ := mem_image.1 h3
        rw [os_ptR_inj heq] at hk'; exact hnk (mem_filter.1 hk').1
      · obtain ⟨k', hk', heq⟩ := mem_image.1 h2
        rw [os_ptR_inj heq] at hk'; exact hnk (mem_filter.1 hk').1
      · rcases hor with h3 | hin
        · have hsub : g14_nbB (os_ptR k) ⊆ P := by
            have hle3 := degree_le_three (os_ptR k)
            have heq : sem_g14_nb (os_ptR k) ∩ P = g14_nbB (os_ptR k) :=
              eq_of_subset_of_card_le inter_subset_left (by rw [h3]; omega)
            rw [← heq]; exact inter_subset_right
          exact hnk (mem_filter.2 ⟨mem_univ _, Or.inl hsub, hocc⟩)
        · obtain ⟨k', hk', heq⟩ := mem_image.1 hin
          rw [os_ptR_inj heq] at hk'
          exact hnk (mem_filter.2 ⟨mem_univ _, (mem_filter.1 hk').2.2, hocc⟩))
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      have hki := (mem_filter.1 hk).2
      exact ⟨hki.1, fun _ => hok_ge2 k hki.2, fun h0 => absurd h0 (hne0R k)⟩)
  have hlost := g14_lost h hD P hPi ((Iin \ Oc).image os_ptR)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
      rw [mem_sdiff] at hk
      have hki := (mem_filter.1 hk.1).2
      refine ⟨hki.1, hne0R k, hok_ge2 k hki.2, fun hocc => hk.2 ?_⟩
      exact mem_filter.2 ⟨mem_univ _, hki.2, hocc⟩)
  rw [card_image_of_injective _ os_ptR_inj] at hlost
  rw [card_image_of_injective _ os_ptR_inj, card_image_of_injective _ os_ptR_inj,
    card_image_of_injective _ os_ptR_inj, hLabEq] at hcnt
  have hel := inelig_card_add 14 D
  refine ⟨fun k => by simp [Oc, P, I], ?_, hlost⟩
  dsimp only [Oc3, Oc2, Ct, Iin, Lab, P, I] at hcnt ⊢; omega
theorem g14_sideL_step {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ m : Fin 128,
      let I := ineligSet 14 D
      let P := sideL \ I
      let Oc := maskFin7 m
      let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 3)
      let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 2)
      let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
      let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ okL_pred I P k)
      let Lab := Ct.biUnion (fun k => g14_nbB (os_ptR k) ∩ P)
      (∀ k ∈ Oc, okL_pred I P k) ∧
      2 * Oc3.card + Oc2.card + Iin.card + Lab.card +
        (14 - I.card) ≤ 2 * P.card + Bplus 14 D ∧
      (Iin \ Oc).card ≤ Bzero 14 D := by
  obtain ⟨m, hiff, h1, h2⟩ := g14_sideL_exact h hD
  exact ⟨m, fun k hk => ((hiff k).1 hk).1, h1, h2⟩
abbrev ru (D : Dag) (b : Fin 14 → ℕ) (x : Fin 14) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 14 D b).filter (fun u => x ∈ supp 14 D u.1)
theorem ru_mem {D : Dag} {b : Fin 14 → ℕ} {x : Fin 14} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ ru D b x) : x ∈ supp 14 D u.1 := (mem_filter.1 hu).2
theorem mem_elig_of_ru {D : Dag} {b : Fin 14 → ℕ} {u : Σ _ : ℕ, ℕ}
    (hu : u ∈ residualUnits 14 D b) {x : Fin 14} (hx : x ∈ supp 14 D u.1) : x ∈ eligSet 14 D :=
  mem_eligSet.2 ⟨u.1, by
    have h1 := (mem_units.mp (mem_filter.mp (mem_sdiff.mp hu).1).1).2
    omega, hx⟩
theorem cc_le {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) (x : Fin 14) :
    (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_g14_gr h (sem_g14_comp hD) b hb x
  have h2 := card_le_card
    (inter_subset_left : ({x} : Finset (Fin 14)) ∩ eligSet 14 D ⊆ {x})
  rw [card_singleton] at h2
  dsimp only [ru]; omega
theorem weak_cc_le {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : WeakPureBranch14 D b) (x : Fin 14)
    (hx : (0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5)) :
    (sem_W 14 D x).card + (merges 14 D (carrierT 14 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := weak_code_count h hD b hb x hx
  have h2 := card_le_card
    (inter_subset_left : ({x} : Finset (Fin 14)) ∩ eligSet 14 D ⊆ {x})
  rw [card_singleton] at h2
  dsimp only [ru]; omega
theorem tight_card_le2 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (ht : Bplus 14 D ≤ (eligSet 14 D).card) (x : Fin 14)
    (hx : (0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5)) : (sem_W 14 D x).card ≤ 2 := by
  obtain ⟨b, hb⟩ := exists_weakPureBranch h hD
  have hr := weak_card_residual h.1 b hb
  have hc := weak_cc_le h hD b hb x hx
  have h0 : (ru D b x).card ≤ (residualUnits 14 D b).card := card_le_card (filter_subset _ _)
  omega
theorem as_mem {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    {i a : Fin 14} (hi : i ∈ ineligSet 14 D) (hi0 : i ≠ 0) (hia : Adj i a) :
    pos i ∈ sem_W 14 D a := by
  obtain ⟨h1, h2, h3, -⟩ := hpos.1 i hi hi0
  exact sem_mem_W.2 ⟨h1, h3 a hia, by rw [h2]; exact notMem_empty a⟩
theorem as_mem0 {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (h0 : (0 : Fin 14) ∈ ineligSet 14 D) : pos 0 ∈ sem_W 14 D 10 := by
  obtain ⟨h1, h2, h3, -, -⟩ := hpos.2.1 h0
  exact sem_mem_W.2 ⟨h1, h3, fun hc => by have := h2 hc; simp at this⟩
theorem pa_ed {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos14 D pos) {x y : Fin 14} (hxy : Adj x y) :
    ∃ e, e ∈ sem_W 14 D x ∧ sem_bar e ∈ sem_W 14 D y ∧
      (∀ i ∈ ineligSet 14 D, i ≠ 0 → e = pos i → y = i) ∧
      (∀ i ∈ ineligSet 14 D, i ≠ 0 → sem_bar e = pos i → x = i) := by
  obtain ⟨e, he1, he2, -, -, -⟩ := sem_edge_slots sem_g14_gr h.1 (sem_g14_comp hD) hxy
  refine ⟨e, he1, he2, fun i hi hi0 he => ?_, fun i hi hi0 he => ?_⟩
  · have h1 := (sem_mem_W.1 he2).2.1
    rw [show sem_bar e = (e.1, !e.2) from rfl, he, (hpos.1 i hi hi0).2.2.2, mem_singleton] at h1
    exact h1
  · have h1 := (sem_mem_W.1 he1).2.1
    have h2 : src D e = src D ((pos i).1, !(pos i).2) := by
      rw [← he]; simp [sem_bar]
    rw [h2, (hpos.1 i hi hi0).2.2.2, mem_singleton] at h1
    exact h1
theorem pa_ed_not_mem {D : Dag} (h : StrictLive 14 D) {e : ℕ × Bool} {y : Fin 14}
    (hbe : sem_bar e ∈ sem_W 14 D y) : e ∉ sem_W 14 D y := by
  intro he
  obtain ⟨hj, hsy, hny⟩ := sem_mem_W.1 he
  have hby := (sem_mem_W.1 hbe).2.1
  have ht := sem_W_and h.1 he
  have hmem : y ∈ supp 14 D (14 + e.1) := by
    rw [sem_supp_and h.1 hj ht, mem_inter]
    cases hs : e.2 <;> simp [src, sem_bar, hs] at hsy hby ⊢ <;> exact ⟨by assumption, by assumption⟩
  exact hny hmem
theorem full_g14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos) {i v : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hi0 : i ≠ 0) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ (pos i).1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  have hsep : ∀ u : Fin 14, u ≠ i → ∃ z, Adj i z ∧ ¬ Adj u z := fun u hu => nbr_diff_exists i u hu.symm hi0
  obtain ⟨e, -, -, -, -, -, hex, -⟩ := sem_inelig_consumer sem_g14_gr h (sem_g14_comp hD) hsep hi
  have hbar : sem_bar (pos i) = e := by
    have hm : sem_bar (pos i) ∈ sem_W 14 D i := by
      obtain ⟨h1, h2, -, h4⟩ := hpos.1 i hi hi0
      exact sem_mem_W.2 ⟨h1, by rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h4]; exact mem_singleton_self i,
        by dsimp only [sem_bar]; rw [h2]; exact notMem_empty i⟩
    rw [sem_W, hex, mem_singleton] at hm; exact hm
  have hfg := full_gen sem_g14_gr h (sem_g14_comp hD) hB0 hsep hi hex hiv
    (fun p hp hne => hv p hp (by rw [← hbar] at hne; exact hne))
  intro t; simpa [← hbar, sem_bar_bar] using hfg t
theorem pa_card3 {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hc3 : ({a, b, c} : Finset α).card = 3 := by
    rw [card_insert_of_notMem, card_pair hbc]
    simp [hab, hac]
  exact hc3 ▸ card_le_card hsub
theorem pa_card4 {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ s.card := by
  have hsub : ({a, b, c, d} : Finset α) ⊆ s := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hc4 : ({a, b, c, d} : Finset α).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hcd]
    · simp [hbc, hbd]
    · simp [hab, hac, had]
  exact hc4 ▸ card_le_card hsub
theorem pa_three {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hle : s.card ≤ 3) :
    ∀ x ∈ s, x = a ∨ x = b ∨ x = c := by
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hc3 : ({a, b, c} : Finset α).card = 3 := by
    rw [card_insert_of_notMem, card_pair hbc]
    simp [hab, hac]
  have heq : ({a, b, c} : Finset α) = s := eq_of_subset_of_card_le hsub (by omega)
  intro x hx; rw [← heq] at hx; simpa using hx
theorem two_in_deg3' {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos14 D pos) {u i1 i2 v : Fin 14}
    (h1 : i1 ∈ ineligSet 14 D) (h2 : i2 ∈ ineligSet 14 D) (hv1 : v ≠ i1) (hv2 : v ≠ i2)
    (hg : i1 ≠ 0 ∧ i2 ≠ 0 ∧ i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true) :
    3 ≤ (sem_W 14 D u).card := by
  obtain ⟨hi10, hi20, hne, g1, g2, gv⟩ := hg
  obtain ⟨e, he, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gv)
  exact pa_card3 (as_mem hpos h1 hi10 ((hc_adjB_iff _ _).1 g1))
    (as_mem hpos h2 hi20 ((hc_adjB_iff _ _).1 g2)) he
    (fun heq => hne (hpos.2.2 i1 h1 i2 h2 heq))
    (fun heq => hv1 (hfv i1 h1 hi10 heq.symm))
    (fun heq => hv2 (hfv i2 h2 hi20 heq.symm))
theorem two_in_deg3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos14 D pos) {u i1 i2 v : Fin 14}
    (h1 : i1 ∈ ineligSet 14 D) (h2 : i2 ∈ ineligSet 14 D) (hv : v ∉ ineligSet 14 D)
    (hg : i1 ≠ 0 ∧ i2 ≠ 0 ∧ i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true) :
    3 ≤ (sem_W 14 D u).card :=
  two_in_deg3' (v := v) h hD hpos h1 h2 (fun he => hv (he ▸ h1)) (fun he => hv (he ▸ h2)) hg
theorem full_of_two_in_deg3' {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos) {u i1 i2 v : Fin 14}
    (h1 : i1 ∈ ineligSet 14 D) (h2 : i2 ∈ ineligSet 14 D) (hv1 : v ≠ i1) (hv2 : v ≠ i2)
    (hg : i1 ≠ 0 ∧ i2 ≠ 0 ∧ i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true)
    (hle : (sem_W 14 D u).card ≤ 3) :
    (∀ t, t ∈ supp 14 D (src D (pos i1)) ↔ Adj i1 t) ∧
    (∀ t, t ∈ supp 14 D (src D (pos i2)) ↔ Adj i2 t) := by
  obtain ⟨hi10, hi20, hne, g1, g2, gv⟩ := hg
  obtain ⟨e, he, hbe, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gv)
  have hWu := pa_three (as_mem hpos h1 hi10 ((hc_adjB_iff _ _).1 g1))
    (as_mem hpos h2 hi20 ((hc_adjB_iff _ _).1 g2)) he
    (fun heq => hne (hpos.2.2 i1 h1 i2 h2 heq))
    (fun heq => hv1 (hfv i1 h1 hi10 heq.symm))
    (fun heq => hv2 (hfv i2 h2 hi20 heq.symm)) hle
  have h2m : i2 ∈ supp 14 D (src D (sem_bar (pos i2))) := by
    rw [show src D (sem_bar (pos i2)) = src D ((pos i2).1, !(pos i2).2) from rfl, (hpos.1 i2 h2 hi20).2.2.2]
    exact mem_singleton_self i2
  have h1m : i1 ∈ supp 14 D (src D (sem_bar (pos i1))) := by
    rw [show src D (sem_bar (pos i1)) = src D ((pos i1).1, !(pos i1).2) from rfl, (hpos.1 i1 h1 hi10).2.2.2]
    exact mem_singleton_self i1
  have hvm : v ∈ supp 14 D (src D (sem_bar e)) := (sem_mem_W.1 hbe).2.1
  constructor
  · exact full_g14 h hD hB0 hpos h1 hi10 ((hc_adjB_iff _ _).1 g1) (fun p hp hne1 hsub => by
      rcases hWu p hp with rfl | rfl | rfl
      · exact hne1 rfl
      · exact hne (mem_singleton.1 (hsub h2m)).symm
      · exact hv1 (mem_singleton.1 (hsub hvm)))
  · exact full_g14 h hD hB0 hpos h2 hi20 ((hc_adjB_iff _ _).1 g2) (fun p hp hne2 hsub => by
      rcases hWu p hp with rfl | rfl | rfl
      · exact hne (mem_singleton.1 (hsub h1m))
      · exact hne2 rfl
      · exact hv2 (mem_singleton.1 (hsub hvm)))
theorem full_of_two_in_deg3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos) {u i1 i2 v : Fin 14}
    (h1 : i1 ∈ ineligSet 14 D) (h2 : i2 ∈ ineligSet 14 D) (hv : v ∉ ineligSet 14 D)
    (hg : i1 ≠ 0 ∧ i2 ≠ 0 ∧ i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true)
    (hle : (sem_W 14 D u).card ≤ 3) :
    (∀ t, t ∈ supp 14 D (src D (pos i1)) ↔ Adj i1 t) ∧
    (∀ t, t ∈ supp 14 D (src D (pos i2)) ↔ Adj i2 t) :=
  full_of_two_in_deg3' (v := v) h hD hB0 hpos h1 h2 (fun he => hv (he ▸ h1)) (fun he => hv (he ▸ h2)) hg hle
theorem g14_deg3_third : ∀ x a b : Fin 14, (g14_nbB x).card = 3 → x ≠ a → x ≠ b →
    hc_adjB a b = false → ∃ y : Fin 14, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by
  decide +kernel
theorem g14_deg3_cover_free {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {x a b : Fin 14}
    (hd : (g14_nbB x).card = 3) (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 14 D x ∧ a ∉ supp 14 D (src D e) ∧ b ∉ supp 14 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := g14_deg3_third x a b hd hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_g14_gr h.1 (sem_g14_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)
theorem deg3_ne0 : ∀ x : Fin 14, (g14_nbB x).card = 3 → x ≠ 0 := by decide +kernel
theorem ps_nonadj {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos14 D pos) {i x r : Fin 14} (hi : i ∈ ineligSet 14 D) (hi0 : i ≠ 0)
    (hix : Adj i x) (hir : Adj i r) (hrx : r ≠ x) (hdx : (g14_nbB x).card = 3)
    (hcx : (sem_W 14 D x).card ≤ 2) :
    ∃ D_x, D_x ≠ pos i ∧ sem_W 14 D x = {pos i, D_x} ∧
      ∀ w : Fin 14, w ≠ x → ¬ Adj r w → D_x ∉ sem_W 14 D w := by
  obtain ⟨D_x, hDx, hnr⟩ := sem_antichain sem_g14_gr h.1 (sem_g14_comp hD)
    (nbr_diff_exists x r hrx.symm (deg3_ne0 x hdx))
  have hne : D_x ≠ pos i := fun heq => hnr (heq ▸ (hpos.1 i hi hi0).2.2.1 r hir)
  have hWx : sem_W 14 D x = {pos i, D_x} := by
    symm
    refine eq_of_subset_of_card_le (fun e he => ?_) (by rw [card_pair hne.symm]; exact hcx)
    rw [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact as_mem hpos hi hi0 hix
    · exact hDx
  refine ⟨D_x, hne, hWx, fun w hwx hnrw hDw => ?_⟩
  obtain ⟨e, he, hnw, hnr'⟩ := g14_deg3_cover_free h hD hdx hwx.symm hrx.symm (fun h => hnrw (adj_symm h))
  rw [hWx, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · exact hnr' ((hpos.1 i hi hi0).2.2.1 r hir)
  · exact hnw (sem_mem_W.1 hDw).2.1
theorem ps_side {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos14 D pos) {i x : Fin 14} (hi : i ∈ ineligSet 14 D) (hi0 : i ≠ 0)
    (hix : Adj i x) (hdx : (g14_nbB x).card = 3) (hcx : (sem_W 14 D x).card ≤ 2) :
    ∃ D_x, D_x ≠ pos i ∧ sem_W 14 D x = {pos i, D_x} ∧
      ∀ w : Fin 14, w ≠ x → decide (w.val < 7) = decide (x.val < 7) → D_x ∉ sem_W 14 D w := by
  obtain ⟨r, hirB, hrx⟩ := sem_g14_second_ne0 i x hi0
  have hir : Adj i r := (hc_adjB_iff i r).1 hirB
  obtain ⟨D_x, hne, hWx, hna⟩ := ps_nonadj h hD hpos hi hi0 hix hir hrx hdx hcx
  refine ⟨D_x, hne, hWx, fun w hwx hsw => hna w hwx (fun hrw => ?_)⟩
  have h1 := g14_sides i r ((hc_adjB_iff _ _).2 hir)
  have h2 := g14_sides i x ((hc_adjB_iff _ _).2 hix)
  have h3 := g14_sides r w ((hc_adjB_iff _ _).2 hrw)
  cases hx7 : decide (x.val < 7) <;> cases hr7 : decide (r.val < 7) <;> cases hi7 : decide (i.val < 7) <;>
    simp_all
theorem pa_m1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos14 D pos) (z k v iz ik : Fin 14)
    (hiz : iz ∈ ineligSet 14 D) (hik : ik ∈ ineligSet 14 D)
    (hz : z ∉ ineligSet 14 D) (hk : k ∉ ineligSet 14 D) (hv : v ∉ ineligSet 14 D)
    (hg : hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧
      hc_adjB z v = true ∧ v ≠ k ∧ (g14_nbB k).card = 3 ∧
      decide (v.val < 7) = decide (k.val < 7) ∧ iz ≠ 0 ∧ ik ≠ 0)
    (hcz : (sem_W 14 D z).card ≤ 2) (hck : (sem_W 14 D k).card ≤ 2) : False := by
  obtain ⟨giz, gik, gzk, gzv, hvk, hdk, hsvk, hiz0, hik0⟩ := hg
  rw [hc_adjB_iff] at giz gik gzk gzv
  obtain ⟨Dk, -, hWk, hpk⟩ := ps_side h hD hpos hik hik0 gik hdk hck
  obtain ⟨fk, hfk, hbfk, hfky, hfkx⟩ := pa_ed h hD hpos gzk
  obtain ⟨fv, hfv, hbfv, hfvy, -⟩ := pa_ed h hD hpos gzv
  have hbk : sem_bar fk = Dk := by
    rw [hWk, mem_insert, mem_singleton] at hbfk
    exact hbfk.resolve_left (fun hh => hz (hfkx ik hik hik0 hh ▸ hik))
  have hne : fk ≠ fv := fun hh => hpk v hvk hsvk (hbk ▸ hh ▸ hbfv)
  have h3 := pa_card3 (as_mem hpos hiz hiz0 giz) hfk hfv
    (fun hh => hk (hfky iz hiz hiz0 hh.symm ▸ hiz))
    (fun hh => hv (hfvy iz hiz hiz0 hh.symm ▸ hiz)) hne
  omega
theorem ps_side_3star {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos14 D pos) (u k1 k2 v ik1 ik2 : Fin 14)
    (hik1 : ik1 ∈ ineligSet 14 D) (hik2 : ik2 ∈ ineligSet 14 D)
    (hu : u ∉ ineligSet 14 D)
    (hg : hc_adjB u k1 = true ∧ hc_adjB u k2 = true ∧ hc_adjB u v = true ∧
      hc_adjB ik1 k1 = true ∧ hc_adjB ik2 k2 = true ∧
      k1 ≠ k2 ∧ k1 ≠ v ∧ k2 ≠ v ∧
      (g14_nbB k1).card = 3 ∧ (g14_nbB k2).card = 3 ∧
      decide (k2.val < 7) = decide (k1.val < 7) ∧ decide (v.val < 7) = decide (k1.val < 7) ∧
      ik1 ≠ 0 ∧ ik2 ≠ 0)
    (hc1 : (sem_W 14 D k1).card ≤ 2) (hc2 : (sem_W 14 D k2).card ≤ 2) :
    3 ≤ (sem_W 14 D u).card := by
  obtain ⟨gk1, gk2, gv, gi1, gi2, h12, h1v, h2v, hd1, hd2, hs12, hs1v, hik10, hik20⟩ := hg
  rw [hc_adjB_iff] at gk1 gk2 gv gi1 gi2
  obtain ⟨D1, -, hW1, hp1⟩ := ps_side h hD hpos hik1 hik10 gi1 hd1 hc1
  obtain ⟨D2, -, hW2, hp2⟩ := ps_side h hD hpos hik2 hik20 gi2 hd2 hc2
  obtain ⟨f1, hf1, hbf1, -, hf1x⟩ := pa_ed h hD hpos gk1
  obtain ⟨f2, hf2, hbf2, -, hf2x⟩ := pa_ed h hD hpos gk2
  obtain ⟨fv, hfv, hbfv, -, -⟩ := pa_ed h hD hpos gv
  have hb1 : sem_bar f1 = D1 := by
    rw [hW1, mem_insert, mem_singleton] at hbf1
    exact hbf1.resolve_left (fun hh => hu (hf1x ik1 hik1 hik10 hh ▸ hik1))
  have hb2 : sem_bar f2 = D2 := by
    rw [hW2, mem_insert, mem_singleton] at hbf2
    exact hbf2.resolve_left (fun hh => hu (hf2x ik2 hik2 hik20 hh ▸ hik2))
  have h12' : f1 ≠ f2 := fun hh => hp1 k2 h12.symm hs12 (hb1 ▸ hh ▸ hbf2)
  have h1v' : f1 ≠ fv := fun hh => hp1 v h1v.symm hs1v (hb1 ▸ hh ▸ hbfv)
  have h2v' : f2 ≠ fv := fun hh => hp2 v h2v.symm (hs1v.trans hs12.symm) (hb2 ▸ hh ▸ hbfv)
  exact pa_card3 hf1 hf2 hfv h12' h1v' h2v'
theorem pa_setup_one {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1) :
    ∃ (pos : Fin 14 → ℕ × Bool) (P Q : ℕ × Bool),
      k4_Pos14 D pos ∧
      (∀ x : Fin 14, ((0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5)) → (sem_W 14 D x).card ≤ 3) ∧
      P ≠ Q ∧
      ∀ x : Fin 14, ((0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 0 ∧ x ≠ 4 ∧ x ≠ 5)) →
        3 ≤ (sem_W 14 D x).card → P ∈ sem_W 14 D x ∧ Q ∈ sem_W 14 D x := by
  classical
  obtain ⟨b, hmin⟩ := exists_weakMinBranch14 h hD
  have hbp := weakMinBranch_pure hmin
  obtain ⟨pos, hpos⟩ := k4_assigned14 h hD
  have hres1 : (residualUnits 14 D b).card = 1 := by
    have := weak_card_residual h.1 b hbp; omega
  have hc3 : ∀ x : Fin 14, ((0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5)) → (sem_W 14 D x).card ≤ 3 := by
    intro x hx
    have h1 := weak_cc_le h hD b hbp x hx
    have h2 : (ru D b x).card ≤ 1 := (card_le_card (filter_subset _ _)).trans_eq hres1
    omega
  let X := Finset.univ.filter (fun x : Fin 14 =>
    ((0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 0 ∧ x ≠ 4 ∧ x ≠ 5)) ∧ 3 ≤ (sem_W 14 D x).card)
  by_cases hX : X.Nonempty
  · obtain ⟨P, Q, hPQ1, hPQ⟩ := weak_common_terminals h hD b hmin hB1 X hX
      (fun x hx => (mem_filter.1 hx).2.1) (fun x hx => (mem_filter.1 hx).2.2)
    exact ⟨pos, P, Q, hpos, hc3, fun hh => hPQ1 (congrArg Prod.fst hh),
      fun x hok hx => hPQ x (mem_filter.2 ⟨mem_univ _, hok, hx⟩)⟩
  · refine ⟨pos, (0, false), (0, true), hpos, hc3, by decide, fun x hok hx => ?_⟩
    exact absurd ⟨x, mem_filter.2 ⟨mem_univ _, hok, hx⟩⟩ hX
theorem mI {S T : Finset (Fin 14)} (h : S = T) {x : Fin 14} (hx : x ∈ T := by decide) : x ∈ S := h ▸ hx
theorem nI {S T : Finset (Fin 14)} (h : S = T) {x : Fin 14} (hx : x ∉ T := by decide) : x ∉ S := h ▸ hx
structure KW where
  m : Fin 3
  a : Fin 14
  b : Fin 14
  c : Fin 14
  d : Fin 14
  e : Fin 14
  f : Fin 14
def tight_wit (idx : Fin 157) : KW :=
  match idx.val with
  | 0 => ⟨0,13,1,2,4,0,0⟩ | 1 => ⟨2,2,12,13,8,3,1⟩ | 2 => ⟨0,13,1,4,2,0,0⟩
  | 3 => ⟨1,2,13,12,8,1,0⟩ | 4 => ⟨1,4,13,11,10,1,0⟩ | 5 => ⟨1,4,13,10,11,1,0⟩
  | 6 => ⟨0,10,4,5,0,0,0⟩ | 7 => ⟨1,1,13,9,7,4,0⟩ | 8 => ⟨1,1,13,7,9,4,0⟩
  | 9 => ⟨2,9,1,6,5,7,8⟩ | 10 => ⟨0,1,7,9,13,0,0⟩ | 11 => ⟨2,9,1,5,6,7,10⟩
  | 12 => ⟨0,5,9,10,12,0,0⟩ | 13 => ⟨0,6,9,11,8,0,0⟩ | 14 => ⟨0,5,9,12,10,0,0⟩
  | 15 => ⟨0,12,2,3,5,0,0⟩ | 16 => ⟨0,13,1,2,4,0,0⟩ | 17 => ⟨0,9,1,5,6,0,0⟩
  | 18 => ⟨0,13,1,2,4,0,0⟩ | 19 => ⟨0,13,1,2,4,0,0⟩ | 20 => ⟨0,11,3,4,6,0,0⟩
  | 21 => ⟨1,2,12,13,8,3,0⟩ | 22 => ⟨2,2,12,13,8,3,1⟩ | 23 => ⟨0,9,1,5,6,0,0⟩
  | 24 => ⟨0,13,1,4,2,0,0⟩ | 25 => ⟨0,13,1,4,2,0,0⟩ | 26 => ⟨1,2,13,12,8,1,0⟩
  | 27 => ⟨0,6,8,11,9,0,0⟩ | 28 => ⟨1,6,9,8,11,1,0⟩ | 29 => ⟨0,3,11,12,7,0,0⟩
  | 30 => ⟨0,10,4,5,0,0,0⟩ | 31 => ⟨1,1,13,9,7,4,0⟩ | 32 => ⟨0,1,7,9,13,0,0⟩
  | 33 => ⟨1,1,13,7,9,4,0⟩ | 34 => ⟨0,1,7,9,13,0,0⟩ | 35 => ⟨2,9,1,6,5,7,8⟩
  | 36 => ⟨0,1,7,9,13,0,0⟩ | 37 => ⟨0,1,7,9,13,0,0⟩ | 38 => ⟨0,1,7,9,13,0,0⟩
  | 39 => ⟨0,1,7,9,13,0,0⟩ | 40 => ⟨0,6,9,11,8,0,0⟩ | 41 => ⟨2,11,3,6,4,12,9⟩
  | 42 => ⟨0,3,11,12,7,0,0⟩ | 43 => ⟨0,12,2,3,5,0,0⟩ | 44 => ⟨0,13,1,2,4,0,0⟩
  | 45 => ⟨0,9,1,5,6,0,0⟩ | 46 => ⟨0,13,1,2,4,0,0⟩ | 47 => ⟨0,13,1,2,4,0,0⟩
  | 48 => ⟨0,11,3,4,6,0,0⟩ | 49 => ⟨1,2,12,13,8,3,0⟩ | 50 => ⟨1,4,11,13,10,3,0⟩
  | 51 => ⟨0,9,1,5,6,0,0⟩ | 52 => ⟨0,13,1,4,2,0,0⟩ | 53 => ⟨0,13,1,4,2,0,0⟩
  | 54 => ⟨1,2,13,12,8,1,0⟩ | 55 => ⟨0,6,8,11,9,0,0⟩ | 56 => ⟨0,4,10,11,13,0,0⟩
  | 57 => ⟨0,3,11,12,7,0,0⟩ | 58 => ⟨0,10,4,5,0,0,0⟩ | 59 => ⟨1,1,13,9,7,4,0⟩
  | 60 => ⟨0,1,7,9,13,0,0⟩ | 61 => ⟨0,5,9,12,10,0,0⟩ | 62 => ⟨0,1,7,9,13,0,0⟩
  | 63 => ⟨2,9,1,5,6,7,10⟩ | 64 => ⟨0,1,7,9,13,0,0⟩ | 65 => ⟨0,1,7,9,13,0,0⟩
  | 66 => ⟨0,1,7,9,13,0,0⟩ | 67 => ⟨0,1,7,9,13,0,0⟩ | 68 => ⟨0,4,10,11,13,0,0⟩
  | 69 => ⟨0,5,9,10,12,0,0⟩ | 70 => ⟨0,3,11,12,7,0,0⟩ | 71 => ⟨0,11,3,4,6,0,0⟩
  | 72 => ⟨0,9,1,6,5,0,0⟩ | 73 => ⟨0,12,2,3,5,0,0⟩ | 74 => ⟨0,9,1,5,6,0,0⟩
  | 75 => ⟨0,9,1,5,6,0,0⟩ | 76 => ⟨0,13,1,2,4,0,0⟩ | 77 => ⟨0,9,1,5,6,0,0⟩
  | 78 => ⟨0,11,3,4,6,0,0⟩ | 79 => ⟨1,2,12,13,8,3,0⟩ | 80 => ⟨0,9,1,5,6,0,0⟩
  | 81 => ⟨0,2,8,12,13,0,0⟩ | 82 => ⟨0,6,8,11,9,0,0⟩ | 83 => ⟨0,2,8,12,13,0,0⟩
  | 84 => ⟨0,3,11,12,7,0,0⟩ | 85 => ⟨0,10,4,5,0,0,0⟩ | 86 => ⟨0,1,7,9,13,0,0⟩
  | 87 => ⟨0,1,7,9,13,0,0⟩ | 88 => ⟨0,1,7,9,13,0,0⟩ | 89 => ⟨0,1,7,9,13,0,0⟩
  | 90 => ⟨0,1,7,9,13,0,0⟩ | 91 => ⟨0,1,7,9,13,0,0⟩ | 92 => ⟨0,1,7,9,13,0,0⟩
  | 93 => ⟨0,1,7,9,13,0,0⟩ | 94 => ⟨0,1,7,9,13,0,0⟩ | 95 => ⟨0,3,11,12,7,0,0⟩
  | 96 => ⟨0,1,9,13,7,0,0⟩ | 97 => ⟨0,11,3,4,6,0,0⟩ | 98 => ⟨0,9,1,6,5,0,0⟩
  | 99 => ⟨0,12,2,3,5,0,0⟩ | 100 => ⟨0,9,1,5,6,0,0⟩ | 101 => ⟨0,9,1,5,6,0,0⟩
  | 102 => ⟨0,4,10,11,13,0,0⟩ | 103 => ⟨0,9,1,5,6,0,0⟩ | 104 => ⟨0,11,3,4,6,0,0⟩
  | 105 => ⟨1,2,12,13,8,3,0⟩ | 106 => ⟨0,9,1,5,6,0,0⟩ | 107 => ⟨0,2,8,12,13,0,0⟩
  | 108 => ⟨0,4,10,11,13,0,0⟩ | 109 => ⟨0,2,8,12,13,0,0⟩ | 110 => ⟨0,3,11,12,7,0,0⟩
  | 111 => ⟨0,10,4,5,0,0,0⟩ | 112 => ⟨0,1,7,9,13,0,0⟩ | 113 => ⟨0,1,7,9,13,0,0⟩
  | 114 => ⟨0,1,7,9,13,0,0⟩ | 115 => ⟨0,1,7,9,13,0,0⟩ | 116 => ⟨0,1,7,9,13,0,0⟩
  | 117 => ⟨0,1,7,9,13,0,0⟩ | 118 => ⟨0,1,7,9,13,0,0⟩ | 119 => ⟨0,1,7,9,13,0,0⟩
  | 120 => ⟨0,1,7,9,13,0,0⟩ | 121 => ⟨0,3,11,12,7,0,0⟩ | 122 => ⟨0,1,9,13,7,0,0⟩
  | 123 => ⟨0,9,1,5,6,0,0⟩ | 124 => ⟨0,9,1,6,5,0,0⟩ | 125 => ⟨0,9,1,6,5,0,0⟩
  | 126 => ⟨0,9,1,5,6,0,0⟩ | 127 => ⟨0,2,8,12,13,0,0⟩ | 128 => ⟨0,1,7,9,13,0,0⟩
  | 129 => ⟨0,1,7,9,13,0,0⟩ | 130 => ⟨0,1,7,9,13,0,0⟩ | 131 => ⟨0,1,7,9,13,0,0⟩
  | 132 => ⟨0,1,7,9,13,0,0⟩ | 133 => ⟨0,1,7,9,13,0,0⟩ | 134 => ⟨0,1,9,13,7,0,0⟩
  | 135 => ⟨0,9,1,5,6,0,0⟩ | 136 => ⟨0,9,1,6,5,0,0⟩ | 137 => ⟨0,9,1,6,5,0,0⟩
  | 138 => ⟨0,9,1,5,6,0,0⟩ | 139 => ⟨0,2,8,12,13,0,0⟩ | 140 => ⟨0,1,7,9,13,0,0⟩
  | 141 => ⟨0,1,7,9,13,0,0⟩ | 142 => ⟨0,1,7,9,13,0,0⟩ | 143 => ⟨0,1,7,9,13,0,0⟩
  | 144 => ⟨0,1,7,9,13,0,0⟩ | 145 => ⟨0,1,7,9,13,0,0⟩ | 146 => ⟨0,1,9,13,7,0,0⟩
  | 147 => ⟨0,9,1,5,6,0,0⟩ | 148 => ⟨0,1,7,9,13,0,0⟩ | 149 => ⟨0,1,7,9,13,0,0⟩
  | 150 => ⟨0,1,7,9,13,0,0⟩ | 151 => ⟨0,9,1,5,6,0,0⟩ | 152 => ⟨0,1,7,9,13,0,0⟩
  | 153 => ⟨0,1,7,9,13,0,0⟩ | 154 => ⟨0,1,7,9,13,0,0⟩ | 155 => ⟨0,1,7,9,13,0,0⟩
  | _ => ⟨0,1,7,9,13,0,0⟩
def tight_m0 (I : Finset (Fin 14)) (w : KW) : Prop :=
  w.b ∈ I ∧ w.c ∈ I ∧ w.d ≠ w.b ∧ w.d ≠ w.c ∧ ((0 : Fin 14) ∈ I ∨ (w.a ≠ 4 ∧ w.a ≠ 5)) ∧
  w.b ≠ 0 ∧ w.c ≠ 0 ∧ w.b ≠ w.c ∧ hc_adjB w.b w.a = true ∧ hc_adjB w.c w.a = true ∧ hc_adjB w.a w.d = true
def tight_m1a (I : Finset (Fin 14)) (w : KW) : Prop :=
  w.d ∈ I ∧ w.e ∈ I ∧ w.a ∉ I ∧ w.b ∉ I ∧ w.c ∉ I ∧
  ((0 : Fin 14) ∈ I ∨ (w.a ≠ 4 ∧ w.a ≠ 5 ∧ w.b ≠ 4 ∧ w.b ≠ 5))
def tight_m1b (w : KW) : Prop :=
  hc_adjB w.d w.a = true ∧ hc_adjB w.e w.b = true ∧ hc_adjB w.a w.b = true ∧
  hc_adjB w.a w.c = true ∧ w.c ≠ w.b ∧ g14_deg3B w.b = true ∧
  decide (w.c.val < 7) = decide (w.b.val < 7) ∧ w.d ≠ 0 ∧ w.e ≠ 0
def tight_m2a (I : Finset (Fin 14)) (w : KW) : Prop :=
  w.e ∈ I ∧ w.f ∈ I ∧ w.a ∉ I ∧
  ((0 : Fin 14) ∈ I ∨ (w.a ≠ 4 ∧ w.a ≠ 5 ∧ w.b ≠ 4 ∧ w.b ≠ 5 ∧ w.c ≠ 4 ∧ w.c ≠ 5)) ∧
  hc_adjB w.a w.b = true ∧ hc_adjB w.a w.c = true ∧ hc_adjB w.a w.d = true
def tight_m2b (w : KW) : Prop :=
  hc_adjB w.e w.b = true ∧ hc_adjB w.f w.c = true ∧
  w.b ≠ w.c ∧ w.b ≠ w.d ∧ w.c ≠ w.d ∧ g14_deg3B w.b = true ∧ g14_deg3B w.c = true ∧
  decide (w.c.val < 7) = decide (w.b.val < 7) ∧ decide (w.d.val < 7) = decide (w.b.val < 7) ∧
  w.e ≠ 0 ∧ w.f ≠ 0
instance (I : Finset (Fin 14)) (w : KW) : Decidable (tight_m0 I w) := by unfold tight_m0; infer_instance
instance (I : Finset (Fin 14)) (w : KW) : Decidable (tight_m1a I w) := by unfold tight_m1a; infer_instance
instance (w : KW) : Decidable (tight_m1b w) := by unfold tight_m1b; infer_instance
instance (I : Finset (Fin 14)) (w : KW) : Decidable (tight_m2a I w) := by unfold tight_m2a; infer_instance
instance (w : KW) : Decidable (tight_m2b w) := by unfold tight_m2b; infer_instance
def tight_ok (I : Finset (Fin 14)) (w : KW) : Prop :=
  (w.m.val = 0 → tight_m0 I w) ∧
  (w.m.val = 1 → tight_m1a I w ∧ tight_m1b w) ∧
  (w.m.val = 2 → tight_m2a I w ∧ tight_m2b w)
instance (I : Finset (Fin 14)) (w : KW) : Decidable (tight_ok I w) := by
  unfold tight_ok; infer_instance
theorem tight_wit_ok : ∀ idx : Fin 157, tight_ok (hc_rep idx) (tight_wit idx) := by
  decide +kernel
theorem tight_le_all {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (ht : Bplus 14 D ≤ (eligSet 14 D).card) (idx : Fin 157)
    (hI : ineligSet 14 D = hc_rep idx) : False := by
  obtain ⟨pos, hpos⟩ := k4_assigned14 h hD
  have hw := tight_wit_ok idx
  rw [← hI] at hw
  unfold tight_ok tight_m0 tight_m1a tight_m1b tight_m2a tight_m2b at hw
  rcases htw : tight_wit idx with ⟨m, a, b, c, d, e, f⟩
  rw [htw] at hw
  dsimp only at hw
  fin_cases m
  · obtain ⟨hb, hc, hdb, hdc, hok, hg⟩ := hw.1 rfl
    have h3 := two_in_deg3' h hD hpos hb hc hdb hdc hg
    have h2 := tight_card_le2 h hD ht a hok
    omega
  · obtain ⟨⟨hd, he, ha, hb, hc, hok⟩, ⟨hda, heb, hab, hac, hcb, hdb, hscb, hd0, he0⟩⟩ := hw.2.1 rfl
    have hoka : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a ≠ 4 ∧ a ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.1, h'.2.1⟩)
    have hokb : (0 : Fin 14) ∈ ineligSet 14 D ∨ (b ≠ 4 ∧ b ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.2.2.1, h'.2.2.2⟩)
    exact pa_m1 h hD hpos a b c d e hd he ha hb hc
      ⟨hda, heb, hab, hac, hcb, (g14_deg3B_iff _).1 hdb, hscb, hd0, he0⟩
      (tight_card_le2 h hD ht a hoka) (tight_card_le2 h hD ht b hokb)
  · obtain ⟨⟨he, hf, ha, hok, hab, hac, had⟩, ⟨heb, hfc, hbc, hbd, hcd, hdb, hdc, hsbc, hsbd, he0, hf0⟩⟩ := hw.2.2 rfl
    have hoka : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a ≠ 4 ∧ a ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.1, h'.2.1⟩)
    have hokb : (0 : Fin 14) ∈ ineligSet 14 D ∨ (b ≠ 4 ∧ b ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.2.2.1, h'.2.2.2.1⟩)
    have hokc : (0 : Fin 14) ∈ ineligSet 14 D ∨ (c ≠ 4 ∧ c ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.2.2.2.2.1, h'.2.2.2.2.2⟩)
    have h3 := ps_side_3star h hD hpos a b c d e f he hf ha
      ⟨hab, hac, had, heb, hfc, hbc, hbd, hcd, (g14_deg3B_iff _).1 hdb, (g14_deg3B_iff _).1 hdc, hsbc, hsbd, he0, hf0⟩
      (tight_card_le2 h hD ht b hokb) (tight_card_le2 h hD ht c hokc)
    have h2 := tight_card_le2 h hD ht a hoka
    omega
def res1_ctx (D : Dag) (pos : Fin 14 → ℕ × Bool) (P Q : ℕ × Bool) : Prop :=
  k4_Pos14 D pos ∧
  (∀ x : Fin 14, ((0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5)) → (sem_W 14 D x).card ≤ 3) ∧
  P ≠ Q ∧
  ∀ x : Fin 14, ((0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 0 ∧ x ≠ 4 ∧ x ≠ 5)) →
    3 ≤ (sem_W 14 D x).card → P ∈ sem_W 14 D x ∧ Q ∈ sem_W 14 D x
theorem res1_setup_c4 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (idx : Fin 157) (hI : ineligSet 14 D = hc_rep idx)
    (hc4 : (ineligSet 14 D).card = 4) :
    Bzero 14 D = 0 ∧ ∃ (pos : Fin 14 → ℕ × Bool) (P Q : ℕ × Bool), res1_ctx D pos P Q := by
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hBgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
    by_contra hle; exact tight_le_all h hD (by omega) idx hI
  have hB1 : Bplus 14 D = (eligSet 14 D).card + 1 := by omega
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB1
  exact ⟨hB0, pos, P, Q, hctx⟩
theorem no_i0_gen {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    {x i1 i2 v : Fin 14} (h1 : i1 ∈ ineligSet 14 D) (h2 : i2 ∈ ineligSet 14 D)
    (hv1 : v ≠ i1) (hv2 : v ≠ i2)
    (hokx : (0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 0 ∧ x ≠ 4 ∧ x ≠ 5))
    (hg : i1 ≠ 0 ∧ i2 ≠ 0 ∧ i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x v = true)
    (hk1 : (∀ t, t ∈ supp 14 D (src D (pos i1)) ↔ Adj i1 t) →
      P = pos i1 ∨ Q = pos i1 → False)
    (hk2 : (∀ t, t ∈ supp 14 D (src D (pos i2)) ↔ Adj i2 t) →
      P = pos i2 ∨ Q = pos i2 → False) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  have hokx' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (x ≠ 4 ∧ x ≠ 5) :=
    hokx.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
  have hx3 := two_in_deg3' h hD hpos h1 h2 hv1 hv2 hg
  obtain ⟨hfull1, hfull2⟩ := full_of_two_in_deg3' h hD hB0 hpos h1 h2 hv1 hv2 hg (hc3 x hokx')
  obtain ⟨hi10, hi20, hne, g1, g2, gv⟩ := hg
  obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gv)
  have hWx := pa_three (as_mem hpos h1 hi10 ((hc_adjB_iff _ _).1 g1))
    (as_mem hpos h2 hi20 ((hc_adjB_iff _ _).1 g2)) hev
    (fun e => hne (hpos.2.2 i1 h1 i2 h2 e))
    (fun e => hv1 (hfv i1 h1 hi10 e.symm))
    (fun e => hv2 (hfv i2 h2 hi20 e.symm)) (hc3 x hokx')
  have ⟨hPx, hQx⟩ := hsat x hokx hx3
  rcases hWx P hPx with hP1 | hP2 | hPv
  · exact hk1 hfull1 (Or.inl hP1)
  · exact hk2 hfull2 (Or.inl hP2)
  · rcases hWx Q hQx with hQ1 | hQ2 | hQv
    · exact hk1 hfull1 (Or.inr hQ1)
    · exact hk2 hfull2 (Or.inr hQ2)
    · exact hPQ (hPv.trans hQv.symm)
structure Noi0 where
  x : Fin 14
  i1 : Fin 14
  i2 : Fin 14
  v : Fin 14
  k1 : KW
  k2 : KW
def no_i0_4_idx (k : Fin 21) : Fin 157 :=
  match k.val with
  | 0 => 43 | 1 => 44 | 2 => 46 | 3 => 47 | 4 => 48 | 5 => 52 | 6 => 53 | 7 => 55
  | 8 => 56 | 9 => 57 | 10 => 58 | 11 => 60 | 12 => 61 | 13 => 62 | 14 => 64 | 15 => 67
  | 16 => 69 | 17 => 76 | 18 => 81 | 19 => 85 | _ => 86
def no_i0_4_wit (k : Fin 21) : Noi0 :=
  match k.val with
  | 0 => ⟨12,2,3,5,⟨2,6,9,11,8,1,3⟩,⟨0,13,1,2,4,0,0⟩⟩
  | 1 => ⟨13,1,2,4,⟨2,3,11,12,7,4,2⟩,⟨2,5,9,10,12,1,4⟩⟩
  | 2 => ⟨13,1,2,4,⟨1,5,12,9,10,2,0⟩,⟨1,5,9,12,10,1,0⟩⟩
  | 3 => ⟨13,1,2,4,⟨1,3,12,7,11,2,0⟩,⟨1,6,9,8,11,1,0⟩⟩
  | 4 => ⟨11,3,4,6,⟨0,13,1,4,2,0,0⟩,⟨2,5,9,12,10,1,3⟩⟩
  | 5 => ⟨13,1,4,2,⟨1,6,11,9,8,4,0⟩,⟨1,6,9,11,8,1,0⟩⟩
  | 6 => ⟨13,1,4,2,⟨1,3,11,7,12,4,0⟩,⟨1,5,9,10,12,1,0⟩⟩
  | 7 => ⟨6,8,11,9,⟨1,4,13,10,11,1,0⟩,⟨1,2,13,12,8,1,0⟩⟩
  | 8 => ⟨4,10,11,13,⟨1,6,9,8,11,1,0⟩,⟨1,5,9,12,10,1,0⟩⟩
  | 9 => ⟨3,11,12,7,⟨1,2,13,8,12,1,0⟩,⟨1,4,13,10,11,1,0⟩⟩
  | 10 => ⟨10,4,5,0,⟨1,1,9,13,7,5,0⟩,⟨1,1,13,9,7,4,0⟩⟩
  | 11 => ⟨1,7,9,13,⟨1,5,10,12,9,4,0⟩,⟨1,3,11,12,7,4,0⟩⟩
  | 12 => ⟨5,9,12,10,⟨1,2,13,8,12,4,0⟩,⟨1,1,13,7,9,4,0⟩⟩
  | 13 => ⟨1,7,9,13,⟨0,6,8,9,11,0,0⟩,⟨2,12,2,3,5,8,7⟩⟩
  | 14 => ⟨1,7,9,13,⟨0,5,9,10,12,0,0⟩,⟨2,11,3,4,6,7,10⟩⟩
  | 15 => ⟨1,7,9,13,⟨2,11,4,6,3,13,9⟩,⟨2,11,3,4,6,7,13⟩⟩
  | 16 => ⟨5,9,10,12,⟨2,11,3,4,6,12,10⟩,⟨2,11,3,6,4,12,9⟩⟩
  | 17 => ⟨13,1,2,4,⟨1,3,12,7,11,2,0⟩,⟨1,6,9,8,11,1,0⟩⟩
  | 18 => ⟨2,8,12,13,⟨0,13,1,4,2,0,0⟩,⟨0,13,1,4,2,0,0⟩⟩
  | 19 => ⟨10,4,5,0,⟨1,1,9,13,7,5,0⟩,⟨1,1,13,9,7,4,0⟩⟩
  | _ => ⟨1,7,9,13,⟨0,6,8,9,11,0,0⟩,⟨1,2,13,12,8,4,0⟩⟩
def kw_m0a (I : Finset (Fin 14)) (w : KW) : Prop :=
  w.b ∈ I ∧ w.c ∈ I ∧ w.d ≠ w.b ∧ w.d ≠ w.c ∧ ((0 : Fin 14) ∈ I ∨ (w.a ≠ 0 ∧ w.a ≠ 4 ∧ w.a ≠ 5))
def kw_m0b (i0 : Fin 14) (w : KW) : Prop :=
  w.b ≠ 0 ∧ w.c ≠ 0 ∧ w.b ≠ w.c ∧ hc_adjB w.b w.a = true ∧ hc_adjB w.c w.a = true ∧ hc_adjB w.a w.d = true ∧ hc_adjB i0 w.a = false
def kw_m1a (I : Finset (Fin 14)) (w : KW) : Prop :=
  w.d ∈ I ∧ w.e ∈ I ∧ w.a ∉ I ∧ w.b ∉ I ∧ w.c ∉ I ∧
  ((0 : Fin 14) ∈ I ∨ (w.a ≠ 0 ∧ w.a ≠ 4 ∧ w.a ≠ 5 ∧ w.b ≠ 0 ∧ w.b ≠ 4 ∧ w.b ≠ 5))
def kw_m1b (i0 : Fin 14) (w : KW) : Prop :=
  hc_adjB w.d w.a = true ∧ hc_adjB w.e w.b = true ∧ hc_adjB w.a w.b = true ∧
  hc_adjB w.a w.c = true ∧ w.c ≠ w.b ∧ g14_deg3B w.b = true ∧
  decide (w.c.val < 7) = decide (w.b.val < 7) ∧ hc_adjB i0 w.a = false ∧ hc_adjB i0 w.b = false ∧
  w.d ≠ 0 ∧ w.e ≠ 0
def kw_m2a (I : Finset (Fin 14)) (w : KW) : Prop :=
  w.e ∈ I ∧ w.f ∈ I ∧ w.a ∉ I ∧
  ((0 : Fin 14) ∈ I ∨ (w.a ≠ 0 ∧ w.a ≠ 4 ∧ w.a ≠ 5 ∧ w.b ≠ 0 ∧ w.b ≠ 4 ∧ w.b ≠ 5 ∧ w.c ≠ 0 ∧ w.c ≠ 4 ∧ w.c ≠ 5))
def kw_m2b (w : KW) : Prop :=
  hc_adjB w.a w.b = true ∧ hc_adjB w.a w.c = true ∧ hc_adjB w.a w.d = true ∧
  hc_adjB w.e w.b = true ∧ hc_adjB w.f w.c = true ∧
  w.b ≠ w.c ∧ w.b ≠ w.d ∧ w.c ≠ w.d ∧ g14_deg3B w.b = true ∧ g14_deg3B w.c = true
def kw_m2c (i0 : Fin 14) (w : KW) : Prop :=
  decide (w.c.val < 7) = decide (w.b.val < 7) ∧ decide (w.d.val < 7) = decide (w.b.val < 7) ∧
  hc_adjB i0 w.a = false ∧ hc_adjB i0 w.b = false ∧ hc_adjB i0 w.c = false ∧
  w.e ≠ 0 ∧ w.f ≠ 0
instance (I : Finset (Fin 14)) (w : KW) : Decidable (kw_m0a I w) := by unfold kw_m0a; infer_instance
instance (i0 : Fin 14) (w : KW) : Decidable (kw_m0b i0 w) := by unfold kw_m0b; infer_instance
instance (I : Finset (Fin 14)) (w : KW) : Decidable (kw_m1a I w) := by unfold kw_m1a; infer_instance
instance (i0 : Fin 14) (w : KW) : Decidable (kw_m1b i0 w) := by unfold kw_m1b; infer_instance
instance (I : Finset (Fin 14)) (w : KW) : Decidable (kw_m2a I w) := by unfold kw_m2a; infer_instance
instance (w : KW) : Decidable (kw_m2b w) := by unfold kw_m2b; infer_instance
instance (i0 : Fin 14) (w : KW) : Decidable (kw_m2c i0 w) := by unfold kw_m2c; infer_instance
def kw_ok (I : Finset (Fin 14)) (i0 : Fin 14) (w : KW) : Prop :=
  (w.m.val = 0 → kw_m0a I w ∧ kw_m0b i0 w) ∧
  (w.m.val = 1 → kw_m1a I w ∧ kw_m1b i0 w) ∧
  (w.m.val = 2 → kw_m2a I w ∧ kw_m2b w ∧ kw_m2c i0 w)
instance (I : Finset (Fin 14)) (i0 : Fin 14) (w : KW) : Decidable (kw_ok I i0 w) := by
  unfold kw_ok; infer_instance
theorem no_i0_4_wit_ok : ∀ k : Fin 21,
    let I := hc_rep (no_i0_4_idx k)
    let w := no_i0_4_wit k
    I.card = 4 ∧ w.i1 ∈ I ∧ w.i2 ∈ I ∧ w.v ≠ w.i1 ∧ w.v ≠ w.i2 ∧ ((0 : Fin 14) ∈ I ∨ (w.x ≠ 0 ∧ w.x ≠ 4 ∧ w.x ≠ 5)) ∧
    w.i1 ≠ 0 ∧ w.i2 ≠ 0 ∧ w.i1 ≠ w.i2 ∧ hc_adjB w.i1 w.x = true ∧ hc_adjB w.i2 w.x = true ∧ hc_adjB w.x w.v = true ∧
    kw_ok I w.i1 w.k1 ∧ kw_ok I w.i2 w.k2 := by
  decide +kernel
theorem kw_kill {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    {i0 : Fin 14} {w : KW}
    (hkw : kw_ok (ineligSet 14 D) i0 w)
    (hfull : ∀ t, t ∈ supp 14 D (src D (pos i0)) ↔ Adj i0 t)
    (hPQ0 : P = pos i0 ∨ Q = pos i0) : False := by
  obtain ⟨hpos, -, -, hsat⟩ := hctx
  have hnot3 : ∀ y : Fin 14, ((0 : Fin 14) ∈ ineligSet 14 D ∨ (y ≠ 0 ∧ y ≠ 4 ∧ y ≠ 5)) →
      hc_adjB i0 y = false → (sem_W 14 D y).card ≤ 2 := fun y hoky hna => by
    by_contra hlt
    have hmem : pos i0 ∈ sem_W 14 D y := by
      rcases hPQ0 with rfl | rfl
      · exact (hsat y hoky (by omega)).1
      · exact (hsat y hoky (by omega)).2
    exact sem_adjB_false.1 hna ((hfull y).1 (sem_mem_W.1 hmem).2.1)
  unfold kw_ok kw_m0a kw_m0b kw_m1a kw_m1b kw_m2a kw_m2b kw_m2c at hkw
  rcases w with ⟨m, a, b, c, d, e, f⟩
  dsimp only at hkw
  fin_cases m
  · obtain ⟨⟨hb, hc, hdb, hdc, hoka⟩, ⟨hb0, hc0, hbc, gba, gca, gad, hna⟩⟩ := hkw.1 rfl
    have h3 := two_in_deg3' h hD hpos hb hc hdb hdc ⟨hb0, hc0, hbc, gba, gca, gad⟩
    have h2 := hnot3 a hoka hna
    omega
  · obtain ⟨⟨hd, he, ha, hb, hc, hok⟩, ⟨hda, heb, hab, hac, hcb, hdb, hscb, hna, hnb, hd0, he0⟩⟩ := hkw.2.1 rfl
    have hoka : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a ≠ 0 ∧ a ≠ 4 ∧ a ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.1, h'.2.1, h'.2.2.1⟩)
    have hokb : (0 : Fin 14) ∈ ineligSet 14 D ∨ (b ≠ 0 ∧ b ≠ 4 ∧ b ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2⟩)
    exact pa_m1 h hD hpos a b c d e hd he ha hb hc
      ⟨hda, heb, hab, hac, hcb, (g14_deg3B_iff _).1 hdb, hscb, hd0, he0⟩ (hnot3 a hoka hna) (hnot3 b hokb hnb)
  · obtain ⟨⟨he, hf, ha, hok⟩, ⟨hab, hac, had, heb, hfc, hbc, hbd, hcd, hdb, hdc⟩, ⟨hsbc, hsbd, hna, hnb, hnc, he0, hf0⟩⟩ := hkw.2.2 rfl
    have hoka : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a ≠ 0 ∧ a ≠ 4 ∧ a ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.1, h'.2.1, h'.2.2.1⟩)
    have hokb : (0 : Fin 14) ∈ ineligSet 14 D ∨ (b ≠ 0 ∧ b ≠ 4 ∧ b ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1⟩)
    have hokc : (0 : Fin 14) ∈ ineligSet 14 D ∨ (c ≠ 0 ∧ c ≠ 4 ∧ c ≠ 5) :=
      hok.elim Or.inl (fun h' => Or.inr ⟨h'.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2⟩)
    have h3 := ps_side_3star h hD hpos a b c d e f he hf ha
      ⟨hab, hac, had, heb, hfc, hbc, hbd, hcd, (g14_deg3B_iff _).1 hdb, (g14_deg3B_iff _).1 hdc, hsbc, hsbd, he0, hf0⟩
      (hnot3 b hokb hnb) (hnot3 c hokc hnc)
    have h2 := hnot3 a hoka hna
    omega
theorem elim_no_i0_4 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 21)
    (hI : ineligSet 14 D = hc_rep (no_i0_4_idx k)) : False := by
  have hw := no_i0_4_wit_ok k
  dsimp only at hw
  rw [← hI] at hw
  obtain ⟨hc4, hi1, hi2, hv1, hv2, hokx, hi10, hi20, hne, g1, g2, gv, hkw1, hkw2⟩ := hw
  obtain ⟨hB0, pos, P, Q, hctx⟩ := res1_setup_c4 h hD h11 (no_i0_4_idx k) hI hc4
  exact no_i0_gen h hD hB0 hctx hi1 hi2 hv1 hv2 hokx ⟨hi10, hi20, hne, g1, g2, gv⟩
    (fun hf hp => kw_kill h hD hctx hkw1 hf hp)
    (fun hf hp => kw_kill h hD hctx hkw2 hf hp)
def cnt_b1_R_idx (k : Fin 22) : Fin 157 :=
  match k.val with
  | 0 => 45 | 1 => 51 | 2 => 71 | 3 => 72 | 4 => 73 | 5 => 74 | 6 => 75 | 7 => 77
  | 8 => 78 | 9 => 80 | 10 => 97 | 11 => 98 | 12 => 100 | 13 => 103 | 14 => 123 | 15 => 124
  | 16 => 125 | 17 => 126 | 18 => 135 | 19 => 136 | 20 => 147 | _ => 151
def cnt_b1_L_idx (k : Fin 46) : Fin 157 :=
  match k.val with
  | 0 => 65 | 1 => 66 | 2 => 68 | 3 => 70 | 4 => 83 | 5 => 84 | 6 => 87 | 7 => 88
  | 8 => 89 | 9 => 90 | 10 => 91 | 11 => 92 | 12 => 93 | 13 => 94 | 14 => 95 | 15 => 96
  | 16 => 115 | 17 => 116 | 18 => 117 | 19 => 118 | 20 => 119 | 21 => 120 | 22 => 121 | 23 => 122
  | 24 => 127 | 25 => 128 | 26 => 129 | 27 => 130 | 28 => 131 | 29 => 132 | 30 => 133 | 31 => 134
  | 32 => 141 | 33 => 142 | 34 => 143 | 35 => 144 | 36 => 145 | 37 => 146 | 38 => 148 | 39 => 149
  | 40 => 150 | 41 => 152 | 42 => 153 | 43 => 154 | 44 => 155 | _ => 156
def cnt_b2_R_idx (k : Fin 4) : Fin 157 :=
  match k.val with
  | 0 => 101 | 1 => 106 | 2 => 137 | _ => 138
def cnt_b2_L_idx (k : Fin 6) : Fin 157 :=
  match k.val with
  | 0 => 109 | 1 => 110 | 2 => 113 | 3 => 114 | 4 => 139 | _ => 140
theorem cnt_b1_R_comb : ∀ k : Fin 22,
    let I := hc_rep (cnt_b1_R_idx k)
    let P := sideR \ I
    let IinBase := kPos7.filter (fun j : Fin 7 => os_ptL j ∈ I ∧ g14_nbB (os_ptL j) ⊆ P)
    ∀ m : Fin 128,
    let Oc := maskFin7 m
    (∀ j ∈ Oc, j ∈ kPos7 ∧ g14_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 2)
    let Ct := kPos7 \ Oc
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptL j) ∩ P)
    let extra0 := if (0 : Fin 14) ∈ I ∧ (10 : Fin 14) ∉ I ∧ (10 : Fin 14) ∉ Lab then 1 else 0
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + IinBase.card + extra0 + Lab.card + (14 - I.card) + (IinBase \ Oc).card) ∨
    (11 < (15 - I.card) + (IinBase \ Oc).card) := by
  decide +kernel
theorem elim_cnt_b1_R {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 22)
    (hI : ineligSet 14 D = hc_rep (cnt_b1_R_idx k)) : False := by
  have hBgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
    by_contra hle; exact tight_le_all h hD (by omega) (cnt_b1_R_idx k) hI
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideR_step h hD
  have hcomb := cnt_b1_R_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases hcomb hsub with h1 | h2 <;> omega
theorem cnt_b1_L_comb : ∀ k : Fin 46,
    let I := hc_rep (cnt_b1_L_idx k)
    let P := sideL \ I
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptR j ∈ I ∧ okL_pred I P j)
    ∀ m : Fin 128,
    let Oc := maskFin7 m
    (∀ j ∈ Oc, okL_pred I P j) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptR j) ∩ P).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptR j) ∩ P).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptR j) ∩ P)
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card + (14 - I.card) + (Iin \ Oc).card) ∨
    (11 < (15 - I.card) + (Iin \ Oc).card) := by
  decide +kernel
theorem elim_cnt_b1_L {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 46)
    (hI : ineligSet 14 D = hc_rep (cnt_b1_L_idx k)) : False := by
  have hBgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
    by_contra hle; exact tight_le_all h hD (by omega) (cnt_b1_L_idx k) hI
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideL_step h hD
  have hcomb := cnt_b1_L_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases hcomb hsub with h1 | h2 <;> omega
theorem elim_adj_w3_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1) (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (x y ix1 ix2 iy1 iy2 : Fin 14)
    (hix1 : ix1 ∈ ineligSet 14 D) (hix2 : ix2 ∈ ineligSet 14 D)
    (hiy1 : iy1 ∈ ineligSet 14 D) (hiy2 : iy2 ∈ ineligSet 14 D)
    (hx : x ∉ ineligSet 14 D) (hy : y ∉ ineligSet 14 D)
    (hg : ix1 ≠ 0 ∧ ix2 ≠ 0 ∧ iy1 ≠ 0 ∧ iy2 ≠ 0 ∧
      ix1 ≠ ix2 ∧ iy1 ≠ iy2 ∧ ix1 ≠ iy1 ∧ ix1 ≠ iy2 ∧ ix2 ≠ iy1 ∧ ix2 ≠ iy2 ∧
      hc_adjB ix1 x = true ∧ hc_adjB ix2 x = true ∧ hc_adjB x y = true ∧
      hc_adjB iy1 y = true ∧ hc_adjB iy2 y = true) : False := by
  obtain ⟨h01, h02, h03, h04, h12, h34, h13, h14, h23, h24, gx1, gx2, gxy, gy1, gy2⟩ := hg
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  have hx3 := two_in_deg3 h hD hpos hix1 hix2 hy ⟨h01, h02, h12, gx1, gx2, gxy⟩
  have hy3 := two_in_deg3 h hD hpos hiy1 hiy2 hx ⟨h03, h04, h34, gy1, gy2, (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gxy))⟩
  obtain ⟨ex, hex, hbex, hfxy, hfx⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gxy)
  obtain ⟨ey, hey, hbey, hfyx, hfy⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 gxy))
  have hWx := pa_three (as_mem hpos hix1 h01 ((hc_adjB_iff _ _).1 gx1))
    (as_mem hpos hix2 h02 ((hc_adjB_iff _ _).1 gx2)) hex
    (fun e => h12 (hpos.2.2 _ hix1 _ hix2 e))
    (fun e => hy (hfxy _ hix1 h01 e.symm ▸ hix1))
    (fun e => hy (hfxy _ hix2 h02 e.symm ▸ hix2)) (hc3 x (Or.inl h0I))
  have hWy := pa_three (as_mem hpos hiy1 h03 ((hc_adjB_iff _ _).1 gy1))
    (as_mem hpos hiy2 h04 ((hc_adjB_iff _ _).1 gy2)) hey
    (fun e => h34 (hpos.2.2 _ hiy1 _ hiy2 e))
    (fun e => hx (hfyx _ hiy1 h03 e.symm ▸ hiy1))
    (fun e => hx (hfyx _ hiy2 h04 e.symm ▸ hiy2)) (hc3 y (Or.inl h0I))
  have hno : ∀ e, e ∈ sem_W 14 D x → e ∈ sem_W 14 D y → e = ex := by
    intro e he1 he2
    rcases hWx e he1 with rfl | rfl | rfl
    · rcases hWy _ he2 with hh | hh | hh
      · exact absurd (hpos.2.2 _ hix1 _ hiy1 hh) h13
      · exact absurd (hpos.2.2 _ hix1 _ hiy2 hh) h14
      · exact absurd (hfyx _ hix1 h01 hh.symm ▸ hix1) hx
    · rcases hWy _ he2 with hh | hh | hh
      · exact absurd (hpos.2.2 _ hix2 _ hiy1 hh) h23
      · exact absurd (hpos.2.2 _ hix2 _ hiy2 hh) h24
      · exact absurd (hfyx _ hix2 h02 hh.symm ▸ hix2) hx
    · rfl
  exact hPQ ((hno P (hsat x (Or.inl h0I) hx3).1 (hsat y (Or.inl h0I) hy3).1).trans
    (hno Q (hsat x (Or.inl h0I) hx3).2 (hsat y (Or.inl h0I) hy3).2).symm)
theorem elim_disj_w3_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1) (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (x y ix1 ix2 vx iy1 iy2 vy : Fin 14)
    (hix1 : ix1 ∈ ineligSet 14 D) (hix2 : ix2 ∈ ineligSet 14 D)
    (hiy1 : iy1 ∈ ineligSet 14 D) (hiy2 : iy2 ∈ ineligSet 14 D)
    (hvx : vx ∉ ineligSet 14 D) (hvy : vy ∉ ineligSet 14 D)
    (hg : ix1 ≠ 0 ∧ ix2 ≠ 0 ∧ iy1 ≠ 0 ∧ iy2 ≠ 0 ∧
      ix1 ≠ ix2 ∧ iy1 ≠ iy2 ∧ ix1 ≠ iy1 ∧ ix1 ≠ iy2 ∧ ix2 ≠ iy1 ∧ ix2 ≠ iy2 ∧
      hc_adjB ix1 x = true ∧ hc_adjB ix2 x = true ∧ hc_adjB x vx = true ∧
      hc_adjB iy1 y = true ∧ hc_adjB iy2 y = true ∧ hc_adjB y vy = true) : False := by
  obtain ⟨h01, h02, h03, h04, h12, h34, h13, h14, h23, h24, gx1, gx2, gvx, gy1, gy2, gvy⟩ := hg
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  have hx3 := two_in_deg3 h hD hpos hix1 hix2 hvx ⟨h01, h02, h12, gx1, gx2, gvx⟩
  have hy3 := two_in_deg3 h hD hpos hiy1 hiy2 hvy ⟨h03, h04, h34, gy1, gy2, gvy⟩
  obtain ⟨ex, hex, -, hfx, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvx)
  obtain ⟨ey, hey, -, hfy, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvy)
  have hWx := pa_three (as_mem hpos hix1 h01 ((hc_adjB_iff _ _).1 gx1))
    (as_mem hpos hix2 h02 ((hc_adjB_iff _ _).1 gx2)) hex
    (fun e => h12 (hpos.2.2 _ hix1 _ hix2 e))
    (fun e => hvx (hfx _ hix1 h01 e.symm ▸ hix1))
    (fun e => hvx (hfx _ hix2 h02 e.symm ▸ hix2)) (hc3 x (Or.inl h0I))
  have hWy := pa_three (as_mem hpos hiy1 h03 ((hc_adjB_iff _ _).1 gy1))
    (as_mem hpos hiy2 h04 ((hc_adjB_iff _ _).1 gy2)) hey
    (fun e => h34 (hpos.2.2 _ hiy1 _ hiy2 e))
    (fun e => hvy (hfy _ hiy1 h03 e.symm ▸ hiy1))
    (fun e => hvy (hfy _ hiy2 h04 e.symm ▸ hiy2)) (hc3 y (Or.inl h0I))
  have hno : ∀ e, e ∈ sem_W 14 D x → e ∈ sem_W 14 D y → e = ex := by
    intro e he1 he2
    rcases hWx e he1 with rfl | rfl | rfl
    · rcases hWy _ he2 with hh | hh | hh
      · exact absurd (hpos.2.2 _ hix1 _ hiy1 hh) h13
      · exact absurd (hpos.2.2 _ hix1 _ hiy2 hh) h14
      · exact absurd (hfy _ hix1 h01 hh.symm ▸ hix1) hvy
    · rcases hWy _ he2 with hh | hh | hh
      · exact absurd (hpos.2.2 _ hix2 _ hiy1 hh) h23
      · exact absurd (hpos.2.2 _ hix2 _ hiy2 hh) h24
      · exact absurd (hfy _ hix2 h02 hh.symm ▸ hix2) hvy
    · rfl
  exact hPQ ((hno P (hsat x (Or.inl h0I) hx3).1 (hsat y (Or.inl h0I) hy3).1).trans
    (hno Q (hsat x (Or.inl h0I) hx3).2 (hsat y (Or.inl h0I) hy3).2).symm)
theorem elim_tri_w3_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1) (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (x y z i1 i2 i3 vx vy vz : Fin 14)
    (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D) (hi3 : i3 ∈ ineligSet 14 D)
    (hvx : vx ∉ ineligSet 14 D) (hvy : vy ∉ ineligSet 14 D) (hvz : vz ∉ ineligSet 14 D)
    (hg : i1 ≠ 0 ∧ i2 ≠ 0 ∧ i3 ≠ 0 ∧ i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 ∧
      hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x vx = true ∧
      hc_adjB i2 y = true ∧ hc_adjB i3 y = true ∧ hc_adjB y vy = true ∧
      hc_adjB i1 z = true ∧ hc_adjB i3 z = true ∧ hc_adjB z vz = true) : False := by
  obtain ⟨h01, h02, h03, h12, h13, h23, gx1, gx2, gvx, gy2, gy3, gvy, gz1, gz3, gvz⟩ := hg
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  have hx3 := two_in_deg3 h hD hpos hi1 hi2 hvx ⟨h01, h02, h12, gx1, gx2, gvx⟩
  have hy3 := two_in_deg3 h hD hpos hi2 hi3 hvy ⟨h02, h03, h23, gy2, gy3, gvy⟩
  have hz3 := two_in_deg3 h hD hpos hi1 hi3 hvz ⟨h01, h03, h13, gz1, gz3, gvz⟩
  obtain ⟨ex, hex, -, hfx, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvx)
  obtain ⟨ey, hey, -, hfy, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvy)
  obtain ⟨ez, hez, -, hfz, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvz)
  have hWx := pa_three (as_mem hpos hi1 h01 ((hc_adjB_iff _ _).1 gx1))
    (as_mem hpos hi2 h02 ((hc_adjB_iff _ _).1 gx2)) hex
    (fun e => h12 (hpos.2.2 _ hi1 _ hi2 e))
    (fun e => hvx (hfx _ hi1 h01 e.symm ▸ hi1))
    (fun e => hvx (hfx _ hi2 h02 e.symm ▸ hi2)) (hc3 x (Or.inl h0I))
  have hWy := pa_three (as_mem hpos hi2 h02 ((hc_adjB_iff _ _).1 gy2))
    (as_mem hpos hi3 h03 ((hc_adjB_iff _ _).1 gy3)) hey
    (fun e => h23 (hpos.2.2 _ hi2 _ hi3 e))
    (fun e => hvy (hfy _ hi2 h02 e.symm ▸ hi2))
    (fun e => hvy (hfy _ hi3 h03 e.symm ▸ hi3)) (hc3 y (Or.inl h0I))
  have hWz := pa_three (as_mem hpos hi1 h01 ((hc_adjB_iff _ _).1 gz1))
    (as_mem hpos hi3 h03 ((hc_adjB_iff _ _).1 gz3)) hez
    (fun e => h13 (hpos.2.2 _ hi1 _ hi3 e))
    (fun e => hvz (hfz _ hi1 h01 e.symm ▸ hi1))
    (fun e => hvz (hfz _ hi3 h03 e.symm ▸ hi3)) (hc3 z (Or.inl h0I))
  have honly : ∀ e, e ∈ sem_W 14 D x → e ∈ sem_W 14 D y → e ∈ sem_W 14 D z → e = ex := by
    intro e he1 he2 he3
    rcases hWx e he1 with rfl | rfl | rfl
    · rcases hWy _ he2 with hh | hh | hh
      · exact absurd (hpos.2.2 _ hi1 _ hi2 hh) h12
      · exact absurd (hpos.2.2 _ hi1 _ hi3 hh) h13
      · exact absurd (hfy _ hi1 h01 hh.symm ▸ hi1) hvy
    · rcases hWz _ he3 with hh | hh | hh
      · exact absurd (hpos.2.2 _ hi2 _ hi1 hh) h12.symm
      · exact absurd (hpos.2.2 _ hi2 _ hi3 hh) h23
      · exact absurd (hfz _ hi2 h02 hh.symm ▸ hi2) hvz
    · rfl
  exact hPQ ((honly P (hsat x (Or.inl h0I) hx3).1 (hsat y (Or.inl h0I) hy3).1 (hsat z (Or.inl h0I) hz3).1).trans
    (honly Q (hsat x (Or.inl h0I) hx3).2 (hsat y (Or.inl h0I) hy3).2 (hsat z (Or.inl h0I) hz3).2).symm)
theorem elim_share_w3_self_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1) (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (x y i0 i1 i2 vx vy iv : Fin 14)
    (hi0 : i0 ∈ ineligSet 14 D) (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hiv : iv ∈ ineligSet 14 D)
    (hx : x ∉ ineligSet 14 D) (hvx : vx ∉ ineligSet 14 D) (hvy : vy ∉ ineligSet 14 D)
    (hg : i0 ≠ 0 ∧ i1 ≠ 0 ∧ i2 ≠ 0 ∧ iv ≠ 0 ∧ i0 ≠ i1 ∧ i0 ≠ i2 ∧ i1 ≠ i2 ∧ vx ≠ vy ∧
      hc_adjB i0 x = true ∧ hc_adjB i1 x = true ∧ hc_adjB x vx = true ∧
      hc_adjB i0 y = true ∧ hc_adjB i2 y = true ∧ hc_adjB y vy = true ∧
      hc_adjB iv vx = true ∧ (g14_nbB vx).card = 3 ∧
      decide (vy.val < 7) = decide (vx.val < 7)) : False := by
  obtain ⟨h00, h01, h02, h0v, h10, h20, h12, hvxy, gx0, gx1, gxv, gy0, gy2, gyv, giv, hdvx, hsv⟩ := hg
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  have hx3 := two_in_deg3 h hD hpos hi0 hi1 hvx ⟨h00, h01, h10, gx0, gx1, gxv⟩
  have hy3 := two_in_deg3 h hD hpos hi0 hi2 hvy ⟨h00, h02, h20, gy0, gy2, gyv⟩
  obtain ⟨ex, hex, hbex, hfxy, hfx⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gxv)
  obtain ⟨ey, hey, hbey, hfyx, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gyv)
  have hWx := pa_three (as_mem hpos hi0 h00 ((hc_adjB_iff _ _).1 gx0))
    (as_mem hpos hi1 h01 ((hc_adjB_iff _ _).1 gx1)) hex
    (fun e => h10 (hpos.2.2 _ hi0 _ hi1 e))
    (fun e => hvx (hfxy _ hi0 h00 e.symm ▸ hi0))
    (fun e => hvx (hfxy _ hi1 h01 e.symm ▸ hi1)) (hc3 x (Or.inl h0I))
  have hWy := pa_three (as_mem hpos hi0 h00 ((hc_adjB_iff _ _).1 gy0))
    (as_mem hpos hi2 h02 ((hc_adjB_iff _ _).1 gy2)) hey
    (fun e => h20 (hpos.2.2 _ hi0 _ hi2 e))
    (fun e => hvy (hfyx _ hi0 h00 e.symm ▸ hi0))
    (fun e => hvy (hfyx _ hi2 h02 e.symm ▸ hi2)) (hc3 y (Or.inl h0I))
  have hPQ_ex : P = ex ∨ Q = ex := by
    rcases hWx P (hsat x (Or.inl h0I) hx3).1 with hP | hP | hP
    · rcases hWx Q (hsat x (Or.inl h0I) hx3).2 with hQ | hQ | hQ
      · exact absurd (hP.trans hQ.symm) hPQ
      · rcases hWy Q (hsat y (Or.inl h0I) hy3).2 with hh | hh | hh
        · exact absurd (hpos.2.2 _ hi1 _ hi0 (hQ.symm.trans hh)) h10.symm
        · exact absurd (hpos.2.2 _ hi1 _ hi2 (hQ.symm.trans hh)) h12
        · exact absurd (hfyx _ hi1 h01 (hh.symm.trans hQ) ▸ hi1) hvy
      · exact Or.inr hQ
    · rcases hWy P (hsat y (Or.inl h0I) hy3).1 with hh | hh | hh
      · exact absurd (hpos.2.2 _ hi1 _ hi0 (hP.symm.trans hh)) h10.symm
      · exact absurd (hpos.2.2 _ hi1 _ hi2 (hP.symm.trans hh)) h12
      · exact absurd (hfyx _ hi1 h01 (hh.symm.trans hP) ▸ hi1) hvy
    · exact Or.inl hP
  by_cases hvx3 : 3 ≤ (sem_W 14 D vx).card
  · have hex_in : ex ∈ sem_W 14 D vx := by
      rcases hPQ_ex with h1 | h1
      · exact h1 ▸ (hsat vx (Or.inl h0I) hvx3).1
      · exact h1 ▸ (hsat vx (Or.inl h0I) hvx3).2
    exact pa_ed_not_mem h hbex hex_in
  · have hcvx : (sem_W 14 D vx).card ≤ 2 := by omega
    obtain ⟨Dv, -, hWv, hpv⟩ := ps_side h hD hpos hiv h0v ((hc_adjB_iff _ _).1 giv) hdvx hcvx
    have hbx : sem_bar ex = Dv := by
      rw [hWv, mem_insert, mem_singleton] at hbex
      exact hbex.resolve_left (fun hh => hx (hfx iv hiv h0v hh ▸ hiv))
    have hex_in_y : ex ∈ sem_W 14 D y := by
      rcases hPQ_ex with h1 | h1
      · exact h1 ▸ (hsat y (Or.inl h0I) hy3).1
      · exact h1 ▸ (hsat y (Or.inl h0I) hy3).2
    rcases hWy ex hex_in_y with hh | hh | hh
    · exact hvx (hfxy _ hi0 h00 hh ▸ hi0)
    · exact hvx (hfxy _ hi2 h02 hh ▸ hi2)
    · exact hpv vy hvxy.symm hsv (hbx ▸ hh ▸ hbey)
theorem elim_3path_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (u v w iu iv iw : Fin 14)
    (hiu : iu ∈ ineligSet 14 D) (hiv : iv ∈ ineligSet 14 D) (hiw : iw ∈ ineligSet 14 D)
    (hu : u ∉ ineligSet 14 D) (hv : v ∉ ineligSet 14 D) (hw : w ∉ ineligSet 14 D)
    (hg : iu ≠ 0 ∧ iv ≠ 0 ∧ iw ≠ 0 ∧ iu ≠ iv ∧ iu ≠ iw ∧ iv ≠ iw ∧
      hc_adjB iu u = true ∧ hc_adjB iv v = true ∧ hc_adjB iw w = true ∧
      hc_adjB u v = true ∧ hc_adjB v w = true)
    (hu3 : 3 ≤ (sem_W 14 D u).card) (hv3 : 3 ≤ (sem_W 14 D v).card) (hw3 : 3 ≤ (sem_W 14 D w).card) :
    False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨h0u, h0v, h0w, huv, huw, hvw, giu, giv, giw, guv, gvw⟩ := hg
  rw [hc_adjB_iff] at giu giv giw guv gvw
  have hmemPQ : ∀ (a b ia : Fin 14), ia ∈ ineligSet 14 D → ia ≠ 0 → b ∉ ineligSet 14 D →
      Adj ia a → Adj a b → 3 ≤ (sem_W 14 D a).card → 3 ≤ (sem_W 14 D b).card →
      pos ia = P ∨ pos ia = Q := by
    intro a b ia hia hia0 hb gia gab ha3 hb3
    obtain ⟨e, he, hbe, hfa, -⟩ := pa_ed h hD hpos gab
    have henotb : e ∉ sem_W 14 D b := pa_ed_not_mem h hbe
    have heP : e ≠ P := fun hh => henotb (hh ▸ (hsat b (Or.inl h0I) hb3).1)
    have heQ : e ≠ Q := fun hh => henotb (hh ▸ (hsat b (Or.inl h0I) hb3).2)
    have hWa := pa_three (hsat a (Or.inl h0I) ha3).1 (hsat a (Or.inl h0I) ha3).2 he
      hPQ heP.symm heQ.symm (hc3 a (Or.inl h0I))
    rcases hWa (pos ia) (as_mem hpos hia hia0 gia) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (hfa ia hia hia0 h1.symm ▸ hia) hb
  have hPu := hmemPQ u v iu hiu h0u hv giu guv hu3 hv3
  have hPv := hmemPQ v u iv hiv h0v hu giv (adj_symm guv) hv3 hu3
  have hPw := hmemPQ w v iw hiw h0w hv giw (adj_symm gvw) hw3 hv3
  rcases hPu with h1 | h1 <;> rcases hPv with h2 | h2 <;> rcases hPw with h3 | h3
  · exact huv (hpos.2.2 _ hiu _ hiv (h1.trans h2.symm))
  · exact huv (hpos.2.2 _ hiu _ hiv (h1.trans h2.symm))
  · exact huw (hpos.2.2 _ hiu _ hiw (h1.trans h3.symm))
  · exact hvw (hpos.2.2 _ hiv _ hiw (h2.trans h3.symm))
  · exact hvw (hpos.2.2 _ hiv _ hiw (h2.trans h3.symm))
  · exact huw (hpos.2.2 _ hiu _ hiw (h1.trans h3.symm))
  · exact huv (hpos.2.2 _ hiu _ hiv (h1.trans h2.symm))
  · exact huv (hpos.2.2 _ hiu _ hiv (h1.trans h2.symm))
theorem hnot33_pair {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    (a b ia ib : Fin 14)
    (hia : ia ∈ ineligSet 14 D) (hib : ib ∈ ineligSet 14 D)
    (ha : a ∉ ineligSet 14 D) (hb : b ∉ ineligSet 14 D)
    (hoka : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a ≠ 0 ∧ a ≠ 4 ∧ a ≠ 5))
    (hokb : (0 : Fin 14) ∈ ineligSet 14 D ∨ (b ≠ 0 ∧ b ≠ 4 ∧ b ≠ 5))
    (hg : ia ≠ 0 ∧ ib ≠ 0 ∧ ia ≠ ib ∧ hc_adjB ia a = true ∧ hc_adjB ib b = true ∧
      hc_adjB a b = true ∧ hc_adjB ia b = false ∧ hc_adjB ib a = false)
    (hsa : 3 ≤ (sem_W 14 D a).card) (hsb : 3 ≤ (sem_W 14 D b).card) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨h0a, h0b, habi, gia, gib, gab, gnba, gnab⟩ := hg
  rw [hc_adjB_iff] at gia gib gab
  obtain ⟨ea, hea, hbea, hfa, -⟩ := pa_ed h hD hpos gab
  obtain ⟨eb, heb, hbeb, hfb, -⟩ := pa_ed h hD hpos (adj_symm gab)
  have hoka' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a ≠ 4 ∧ a ≠ 5) := hoka.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
  have hokb' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (b ≠ 4 ∧ b ≠ 5) := hokb.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
  have hne_eaP : ea ≠ P := fun hh => pa_ed_not_mem h hbea (hh ▸ (hsat b hokb hsb).1)
  have hne_eaQ : ea ≠ Q := fun hh => pa_ed_not_mem h hbea (hh ▸ (hsat b hokb hsb).2)
  have hne_ebP : eb ≠ P := fun hh => pa_ed_not_mem h hbeb (hh ▸ (hsat a hoka hsa).1)
  have hne_ebQ : eb ≠ Q := fun hh => pa_ed_not_mem h hbeb (hh ▸ (hsat a hoka hsa).2)
  have hWa := pa_three (hsat a hoka hsa).1 (hsat a hoka hsa).2 hea hPQ hne_eaP.symm hne_eaQ.symm (hc3 a hoka')
  have hWb := pa_three (hsat b hokb hsb).1 (hsat b hokb hsb).2 heb hPQ hne_ebP.symm hne_ebQ.symm (hc3 b hokb')
  have hpa_PQ : pos ia = P ∨ pos ia = Q := by
    rcases hWa (pos ia) (as_mem hpos hia h0a gia) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (hfa ia hia h0a h1.symm ▸ hia) hb
  have hpb_PQ : pos ib = P ∨ pos ib = Q := by
    rcases hWb (pos ib) (as_mem hpos hib h0b gib) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (hfb ib hib h0b h1.symm ▸ hib) ha
  have hWa' : ∀ p ∈ sem_W 14 D a, p = pos ia ∨ p = pos ib ∨ p = ea := by
    intro p hp
    rcases hpa_PQ with h1 | h1 <;> rcases hpb_PQ with h2 | h2
    · exact absurd (hpos.2.2 _ hia _ hib (h1.trans h2.symm)) habi
    · rcases hWa p hp with rfl | rfl | rfl
      · exact Or.inl h1.symm
      · exact Or.inr (Or.inl h2.symm)
      · exact Or.inr (Or.inr rfl)
    · rcases hWa p hp with rfl | rfl | rfl
      · exact Or.inr (Or.inl h2.symm)
      · exact Or.inl h1.symm
      · exact Or.inr (Or.inr rfl)
    · exact absurd (hpos.2.2 _ hia _ hib (h1.trans h2.symm)) habi
  have hfull := full_g14 h hD hB0 hpos hia h0a gia (fun p hp hne1 hsub => by
    rcases hWa' p hp with rfl | rfl | rfl
    · exact hne1 rfl
    · have hm : ib ∈ supp 14 D (src D (sem_bar (pos ib))) := by
        rw [show src D (sem_bar (pos ib)) = src D ((pos ib).1, !(pos ib).2) from rfl, (hpos.1 ib hib h0b).2.2.2]
        exact mem_singleton_self ib
      exact habi.symm (mem_singleton.1 (hsub hm))
    · exact hb (mem_singleton.1 (hsub (sem_mem_W.1 hbea).2.1) ▸ hia))
  have hmem_b : pos ia ∈ sem_W 14 D b := by
    rcases hpa_PQ with h1 | h1
    · exact h1 ▸ (hsat b hokb hsb).1
    · exact h1 ▸ (hsat b hokb hsb).2
  exact sem_adjB_false.1 gnba ((hfull b).1 (sem_mem_W.1 hmem_b).2.1)
theorem elim_alt_pair {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    (a1 a2 b0 b1 b2 ia1 ia2 ib0 ib1 ib2 : Fin 14)
    (hia1 : ia1 ∈ ineligSet 14 D) (hia2 : ia2 ∈ ineligSet 14 D)
    (hib0 : ib0 ∈ ineligSet 14 D) (hib1 : ib1 ∈ ineligSet 14 D) (hib2 : ib2 ∈ ineligSet 14 D)
    (ha1 : a1 ∉ ineligSet 14 D) (ha2 : a2 ∉ ineligSet 14 D)
    (hb0 : b0 ∉ ineligSet 14 D) (hb1 : b1 ∉ ineligSet 14 D) (hb2 : b2 ∉ ineligSet 14 D)
    (hoka1 : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a1 ≠ 0 ∧ a1 ≠ 4 ∧ a1 ≠ 5))
    (hoka2 : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a2 ≠ 0 ∧ a2 ≠ 4 ∧ a2 ≠ 5))
    (hg : ia1 ≠ 0 ∧ ia2 ≠ 0 ∧ ib0 ≠ 0 ∧ ib1 ≠ 0 ∧ ib2 ≠ 0 ∧
      ia1 ≠ ia2 ∧ b0 ≠ b1 ∧ b1 ≠ b2 ∧ b0 ≠ b2 ∧
      hc_adjB ia1 a1 = true ∧ hc_adjB a1 b0 = true ∧ hc_adjB a1 b1 = true ∧
      hc_adjB ia2 a2 = true ∧ hc_adjB a2 b1 = true ∧ hc_adjB a2 b2 = true ∧
      hc_adjB ib0 b0 = true ∧ hc_adjB ib1 b1 = true ∧ hc_adjB ib2 b2 = true ∧
      (g14_nbB b0).card = 3 ∧ (g14_nbB b1).card = 3 ∧ (g14_nbB b2).card = 3 ∧
      decide (b0.val < 7) = decide (b1.val < 7) ∧ decide (b1.val < 7) = decide (b2.val < 7))
    (hsa1 : 3 ≤ (sem_W 14 D a1).card) (hsa2 : 3 ≤ (sem_W 14 D a2).card)
    (hcb0 : (sem_W 14 D b0).card ≤ 2) (hcb1 : (sem_W 14 D b1).card ≤ 2)
    (hcb2 : (sem_W 14 D b2).card ≤ 2) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨h0a1, h0a2, h00, h01, h02, hia12, h01', h12', h02', ga1, gab0, gab1, ga2, ga2b1, ga2b2,
    gb0, gb1, gb2, hd0, hd1, hd2, hs01, hs12⟩ := hg
  rw [hc_adjB_iff] at ga1 gab0 gab1 ga2 ga2b1 ga2b2 gb0 gb1 gb2
  obtain ⟨D0, -, hW0, hp0⟩ := ps_side h hD hpos hib0 h00 gb0 hd0 hcb0
  obtain ⟨D1, -, hW1, hp1⟩ := ps_side h hD hpos hib1 h01 gb1 hd1 hcb1
  obtain ⟨D2, -, hW2, hp2⟩ := ps_side h hD hpos hib2 h02 gb2 hd2 hcb2
  obtain ⟨f0, hf0, hbf0, hf0y, hf0x⟩ := pa_ed h hD hpos gab0
  obtain ⟨f1, hf1, hbf1, hf1y, hf1x⟩ := pa_ed h hD hpos gab1
  obtain ⟨g1, hg1, hbg1, hg1y, hg1x⟩ := pa_ed h hD hpos ga2b1
  obtain ⟨g2, hg2, hbg2, hg2y, hg2x⟩ := pa_ed h hD hpos ga2b2
  have hb0e : sem_bar f0 = D0 := by
    rw [hW0, mem_insert, mem_singleton] at hbf0
    exact hbf0.resolve_left (fun hh => ha1 (hf0x ib0 hib0 h00 hh ▸ hib0))
  have hb1e : sem_bar f1 = D1 := by
    rw [hW1, mem_insert, mem_singleton] at hbf1
    exact hbf1.resolve_left (fun hh => ha1 (hf1x ib1 hib1 h01 hh ▸ hib1))
  have hbg1e : sem_bar g1 = D1 := by
    rw [hW1, mem_insert, mem_singleton] at hbg1
    exact hbg1.resolve_left (fun hh => ha2 (hg1x ib1 hib1 h01 hh ▸ hib1))
  have hbg2e : sem_bar g2 = D2 := by
    rw [hW2, mem_insert, mem_singleton] at hbg2
    exact hbg2.resolve_left (fun hh => ha2 (hg2x ib2 hib2 h02 hh ▸ hib2))
  have hf01 : f0 ≠ f1 := fun hh => hp0 b1 h01'.symm hs01.symm (hb0e ▸ hh ▸ hbf1)
  have hg12 : g1 ≠ g2 := fun hh => hp1 b2 h12'.symm hs12.symm (hbg1e ▸ hh ▸ hbg2)
  have hoka1' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a1 ≠ 4 ∧ a1 ≠ 5) := hoka1.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
  have hoka2' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a2 ≠ 4 ∧ a2 ≠ 5) := hoka2.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
  have hWa1 := pa_three (as_mem hpos hia1 h0a1 ga1) hf0 hf1
    (fun hh => hb0 (hf0y ia1 hia1 h0a1 hh.symm ▸ hia1))
    (fun hh => hb1 (hf1y ia1 hia1 h0a1 hh.symm ▸ hia1)) hf01 (hc3 a1 hoka1')
  have hWa2 := pa_three (as_mem hpos hia2 h0a2 ga2) hg1 hg2
    (fun hh => hb1 (hg1y ia2 hia2 h0a2 hh.symm ▸ hia2))
    (fun hh => hb2 (hg2y ia2 hia2 h0a2 hh.symm ▸ hia2)) hg12 (hc3 a2 hoka2')
  have honly : ∀ e, e ∈ sem_W 14 D a1 → e ∈ sem_W 14 D a2 → e = f1 := by
    intro e he1 he2
    rcases hWa1 e he1 with rfl | rfl | rfl
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (hpos.2.2 _ hia1 _ hia2 hh) hia12
      · exact absurd (hg1y ia1 hia1 h0a1 hh.symm ▸ hia1) hb1
      · exact absurd (hg2y ia1 hia1 h0a1 hh.symm ▸ hia1) hb2
    · rcases hWa2 _ he2 with hh | hh | hh
      · exact absurd (hf0y ia2 hia2 h0a2 hh ▸ hia2) hb0
      · exact absurd (hb0e ▸ hh ▸ hbg1) (hp0 b1 h01'.symm hs01.symm)
      · exact absurd (hb0e ▸ hh ▸ hbg2) (hp0 b2 h02'.symm (hs01.trans hs12).symm)
    · rfl
  exact hPQ ((honly P (hsat a1 hoka1 hsa1).1 (hsat a2 hoka2 hsa2).1).trans
    (honly Q (hsat a1 hoka1 hsa1).2 (hsat a2 hoka2 hsa2).2).symm)
theorem elim_95_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1)
    (hIeq : ineligSet 14 D = {0, 4, 5, 7, 8}) : False := by
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h4I : (4 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h5I : (5 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  obtain ⟨hp0_pure, -⟩ := pos0_pure_of_45 h hD hpos h0I h4I h5I
  have p0 := as_mem0 hpos h0I
  have p4 := as_mem hpos h4I (by decide) (by decide : Adj 4 10)
  have p5 := as_mem hpos h5I (by decide) (by decide : Adj 5 10)
  have n04 : pos 0 ≠ pos 4 := fun e => (by decide : (0 : Fin 14) ≠ 4) (hpos.2.2 _ h0I _ h4I e)
  have n05 : pos 0 ≠ pos 5 := fun e => (by decide : (0 : Fin 14) ≠ 5) (hpos.2.2 _ h0I _ h5I e)
  have n45 : pos 4 ≠ pos 5 := fun e => (by decide : (4 : Fin 14) ≠ 5) (hpos.2.2 _ h4I _ h5I e)
  have h10_3 := pa_card3 p0 p4 p5 n04 n05 n45
  have hW10 := pa_three p0 p4 p5 n04 n05 n45 (hc3 10 (Or.inl h0I))
  have hPQ_in : ∀ e, e = P ∨ e = Q → e = pos 0 ∨ e = pos 4 ∨ e = pos 5 := by
    intro e he
    rcases he with rfl | rfl
    · exact hW10 _ (hsat 10 (Or.inl h0I) h10_3).1
    · exact hW10 _ (hsat 10 (Or.inl h0I) h10_3).2
  have hle2L : ∀ (x ix v : Fin 14), ix ∈ ineligSet 14 D → v ∉ ineligSet 14 D →
      (ix ≠ 0 ∧ ix ≠ 4 ∧ ix ≠ 5 ∧ hc_adjB ix x = true ∧ hc_adjB x v = true) →
      (sem_W 14 D x).card ≤ 2 := by
    intro x ix v hix hv hg
    by_contra hlt
    have hx3 : 3 ≤ (sem_W 14 D x).card := by omega
    obtain ⟨h0, h4, h5, gix, gxv⟩ := hg
    rw [hc_adjB_iff] at gix gxv
    obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos gxv
    have hpi := as_mem hpos hix h0 gix
    have hPi : P ≠ pos ix := fun hh => by
      rcases hPQ_in P (Or.inl rfl) with h1 | h1 | h1
      · exact h0 (hpos.2.2 _ hix _ h0I (hh.symm.trans h1))
      · exact h4 (hpos.2.2 _ hix _ h4I (hh.symm.trans h1))
      · exact h5 (hpos.2.2 _ hix _ h5I (hh.symm.trans h1))
    have hQi : Q ≠ pos ix := fun hh => by
      rcases hPQ_in Q (Or.inr rfl) with h1 | h1 | h1
      · exact h0 (hpos.2.2 _ hix _ h0I (hh.symm.trans h1))
      · exact h4 (hpos.2.2 _ hix _ h4I (hh.symm.trans h1))
      · exact h5 (hpos.2.2 _ hix _ h5I (hh.symm.trans h1))
    have hev0 : ev ≠ pos 0 := fun hh => by
      have hm := (sem_mem_W.1 hbev).2.1
      rw [show sem_bar ev = (ev.1, !ev.2) from rfl, hh, hp0_pure, mem_singleton] at hm
      exact hv (hm ▸ h0I)
    have hPev : P ≠ ev := fun hh => by
      rcases hPQ_in P (Or.inl rfl) with h1 | h1 | h1
      · exact hev0 (hh.symm.trans h1)
      · exact hv (hfv 4 h4I (by decide) (hh.symm.trans h1) ▸ h4I)
      · exact hv (hfv 5 h5I (by decide) (hh.symm.trans h1) ▸ h5I)
    have hQev : Q ≠ ev := fun hh => by
      rcases hPQ_in Q (Or.inr rfl) with h1 | h1 | h1
      · exact hev0 (hh.symm.trans h1)
      · exact hv (hfv 4 h4I (by decide) (hh.symm.trans h1) ▸ h4I)
      · exact hv (hfv 5 h5I (by decide) (hh.symm.trans h1) ▸ h5I)
    have h4c := pa_card4 (hsat x (Or.inl h0I) hx3).1 (hsat x (Or.inl h0I) hx3).2 hpi hev
      hPQ hPi hPev hQi hQev (fun hh => hv (hfv ix hix h0 hh.symm ▸ hix))
    have := hc3 x (Or.inl h0I); omega
  have h1c := hle2L 1 7 9 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  have h2c := hle2L 2 8 12 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  have h6c := hle2L 6 8 9 (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  have h13 : 3 ≤ (sem_W 14 D 13).card := by
    by_contra hc; exact pa_m1 h hD hpos 1 13 9 7 4
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h1c (by omega)
  have h9 : 3 ≤ (sem_W 14 D 9).card := by
    by_contra hc; exact pa_m1 h hD hpos 1 9 13 7 5
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h1c (by omega)
  exact elim_alt_pair h hD ⟨hpos, hc3, hPQ, hsat⟩ 13 9 2 1 6 4 5 8 7 8
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (Or.inl h0I) (Or.inl h0I) (by decide) h13 h9 h2c h1c h6c
theorem elim_114_only_m : ∀ m : Fin 128,
    let I : Finset (Fin 14) := {0, 7, 8, 9, 10}
    let P := sideL \ I
    let Oc := maskFin7 m
    let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 3)
    let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ okL_pred I P k)
    let Lab := Ct.biUnion (fun k => g14_nbB (os_ptR k) ∩ P)
    (∀ k ∈ Oc, okL_pred I P k) →
    2 * Oc3.card + Oc2.card + Iin.card + Lab.card ≤ 13 →
    (Iin \ Oc).card ≤ 1 →
    Oc = ({0, 1, 3} : Finset (Fin 7)) := by
  decide +kernel
theorem elim_114_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hB1 : Bplus 14 D = (eligSet 14 D).card + 1)
    (hIeq : ineligSet 14 D = {0, 7, 8, 9, 10}) : False := by
  classical
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h7I : (7 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h8I : (8 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h9I : (9 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h10I : (10 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hc5 : (ineligSet 14 D).card = 5 := by rw [hIeq]; decide
  have hB0le1 : Bzero 14 D ≤ 1 := by omega
  obtain ⟨m, hiff, hcnt, hlost⟩ := g14_sideL_exact h hD
  have hPeq : sideL \ ineligSet 14 D = ({1, 2, 3, 4, 5, 6} : Finset (Fin 14)) := by rw [hIeq]; decide
  set L6 : Finset (Fin 14) := {1, 2, 3, 4, 5, 6}
  have hmeq : maskFin7 m = ({0, 1, 3} : Finset (Fin 7)) := by
    apply elim_114_only_m m
    · intro k hk; rw [← hIeq]; exact ((hiff k).1 hk).1
    · rw [← hIeq]; have hP6 : (sideL \ ineligSet 14 D).card = 6 := by rw [hPeq]; decide
      omega
    · rw [← hIeq]; omega
  have hocc_of : ∀ k : Fin 7, k ∈ ({0, 1, 3} : Finset (Fin 7)) →
      sup_Occ 14 D L6 (sem_g14_nb (os_ptR k) ∩ L6) := fun k hk => by
    have h1 := ((hiff k).1 (hmeq ▸ hk)).2
    rwa [hPeq] at h1
  have hno_of : ∀ k : Fin 7, k ∈ ({4, 5, 6} : Finset (Fin 7)) →
      ¬ sup_Occ 14 D L6 (sem_g14_nb (os_ptR k) ∩ L6) := fun k hk hocc => by
    have hok : okL_pred (ineligSet 14 D) (sideL \ ineligSet 14 D) k := by
      rw [hIeq]; fin_cases k <;> simp at hk <;> decide +kernel
    have hmem : k ∈ maskFin7 m := (hiff k).2 ⟨hok, by rwa [hPeq]⟩
    rw [hmeq] at hmem
    fin_cases k <;> simp at hk hmem
  obtain ⟨b, hmin⟩ := exists_weakMinBranch14 h hD
  have hbp := weak_to_pure b (weakMinBranch_pure hmin) h0I
  have hres1 : (residualUnits 14 D b).card = 1 := by have := card_residual h.1 b hbp; omega
  obtain ⟨u0, hres⟩ := card_eq_one.1 hres1
  obtain ⟨pos, hpos⟩ := k4_assigned14 h hD
  have h1_3 := two_in_deg3 (u := 1) h hD hpos h7I h9I (by rw [hIeq]; decide : (13 : Fin 14) ∉ _) (by decide)
  have h5_3 := two_in_deg3 (u := 5) h hD hpos h9I h10I (by rw [hIeq]; decide : (12 : Fin 14) ∉ _) (by decide)
  have h6_3 := two_in_deg3 (u := 6) h hD hpos h8I h9I (by rw [hIeq]; decide : (11 : Fin 14) ∉ _) (by decide)
  have h1u : (1 : Fin 14) ∈ supp 14 D u0.1 := (sem_saturated sem_g14_gr h (sem_g14_comp hD) b hbp hres h1_3).2.2.2
  have h5u : (5 : Fin 14) ∈ supp 14 D u0.1 := (sem_saturated sem_g14_gr h (sem_g14_comp hD) b hbp hres h5_3).2.2.2
  have h6u : (6 : Fin 14) ∈ supp 14 D u0.1 := (sem_saturated sem_g14_gr h (sem_g14_comp hD) b hbp hres h6_3).2.2.2
  set T0 : Finset (Fin 14) := supp 14 D u0.1 ∩ L6
  have hT0_3 : 3 ≤ T0.card := pa_card3 (mem_inter.2 ⟨h1u, by decide⟩)
    (mem_inter.2 ⟨h5u, by decide⟩) (mem_inter.2 ⟨h6u, by decide⟩)
    (by decide) (by decide) (by decide)
  let ct : Fin 14 → Fin 14 := fun f =>
    if f = 1 ∨ f = 2 then 13 else if f = 5 then 12 else 11
  have hct_k : ∀ f ∈ L6, ∃ k ∈ ({4, 5, 6} : Finset (Fin 7)), os_ptR k = ct f ∧ f ∈ sem_g14_nb (ct f) ∩ L6 := by
    intro f hf; dsimp only [L6] at hf; simp only [mem_insert, mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨6, by decide, by decide, by decide⟩
    · exact ⟨6, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact ⟨5, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
  have hL6_ind : ∀ a ∈ L6, ∀ b ∈ L6, ¬ Adj a b := fun a ha b hb =>
    sideL_indep a (sdiff_subset (hPeq ▸ ha)) b (sdiff_subset (hPeq ▸ hb))
  have hw : ∀ f ∈ L6, ∃ e, sup_Wit 14 D L6 (sem_g14_nb (ct f) ∩ L6) f e := by
    intro f hf
    obtain ⟨k, hk, hkf, hfc⟩ := hct_k f hf
    refine sup_wit_exists sem_g14_gr h.1 (sem_g14_comp hD) (X := insert (ct f) (L6 \ (sem_g14_nb (ct f) ∩ L6)))
      inter_subset_right ?_ ?_ (fun a ha => Finset.mem_insert_of_mem ha) hfc
      ⟨ct f, mem_insert_self _ _, adj_symm (g14_mem_nb.1 (mem_inter.1 hfc).1)⟩
    · refine Or.inr ⟨?_, hkf ▸ hno_of k hk⟩
      fin_cases f <;> simp [L6] at hf <;> decide +kernel
    · have hno : ∀ a ∈ L6 \ (sem_g14_nb (ct f) ∩ L6), ¬ Adj (ct f) a := fun a ha hadj => by
        rw [mem_sdiff, mem_inter, g14_mem_nb] at ha; exact ha.2 ⟨hadj, ha.1⟩
      intro a ha b hb
      rcases mem_insert.1 ha with rfl | ha <;> rcases mem_insert.1 hb with rfl | hb
      · exact adj_irrefl _
      · exact hno b hb
      · exact fun hab => hno a ha (adj_symm hab)
      · exact hL6_ind a (mem_sdiff.1 ha).1 b (mem_sdiff.1 hb).1
  choose! wit hwit using hw
  let S := L6.filter (fun f => ∀ M, M ⊆ sem_g14_nb (ct f) ∩ L6 → M.card = 2 → f ∈ M → ¬ sup_Occ 14 D L6 M)
  have hSL : S ⊆ L6 := filter_subset _ _
  have hno : ∀ f ∈ L6 \ S, ∃ M, M ⊆ sem_g14_nb (ct f) ∩ L6 ∧ M.card = 2 ∧ f ∈ M ∧ sup_Occ 14 D L6 M := by
    intro f hf
    rw [mem_sdiff, mem_filter] at hf
    by_contra hc
    exact hf.2 ⟨hf.1, fun M h1 h2 h4 h5 => hc ⟨M, h1, h2, h4, h5⟩⟩
  choose! pr hpr using hno
  set L2 : Finset (Finset (Fin 14)) := ({0, 1, 3} : Finset (Fin 7)).image (fun k => sem_g14_nb (os_ptR k) ∩ L6)
  have hL2_card : L2.card = 3 := by decide +kernel
  have hL2_c2 : ∀ M ∈ L2, M.card = 2 ∧ sup_Occ 14 D L6 M := by
    intro M hM
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hM
    exact ⟨by fin_cases k <;> simp at hk <;> decide +kernel, hocc_of k hk⟩
  have hL2dis : Disjoint L2 ((L6 \ S).image pr) := by
    rw [disjoint_left]
    intro M hM2 hMpr
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hM2
    obtain ⟨f, hf, hprf⟩ := mem_image.1 hMpr
    have hsub := (hpr f hf).1
    have hc2 := (hpr f hf).2.1
    rw [hprf] at hsub hc2
    have hne : os_ptR k ≠ ct f := by
      have hfL := (mem_sdiff.1 hf).1
      fin_cases k <;> simp at hk <;> fin_cases f <;> simp [L6] at hfL <;> decide
    have hle := sup_g14_inter (os_ptR k) (ct f) hne L6
    have hsub' : sem_g14_nb (os_ptR k) ∩ L6 ⊆ sem_g14_nb (os_ptR k) ∩ (sem_g14_nb (ct f) ∩ L6) :=
      fun x hx => mem_inter.2 ⟨(mem_inter.1 hx).1, hsub hx⟩
    have := card_le_card hsub'; omega
  have hT0_not : T0 ∉ L2 ∪ (L6 \ S).image pr := by
    intro hm
    rcases mem_union.1 hm with h1 | h2
    · have := (hL2_c2 T0 h1).1; omega
    · obtain ⟨f, hf, hprf⟩ := mem_image.1 h2
      have := (hpr f hf).2.1; rw [hprf] at this; omega
  have hbig := sup_card_le_big h.1 L6 (insert T0 (L2 ∪ (L6 \ S).image pr)) (by
    intro M hM
    rcases mem_insert.1 hM with rfl | hM'
    · exact ⟨by omega, ⟨u0.1, rfl⟩⟩
    · rcases mem_union.1 hM' with h1 | h2
      · exact ⟨by have := (hL2_c2 M h1).1; omega, (hL2_c2 M h1).2⟩
      · obtain ⟨f, hf, rfl⟩ := mem_image.1 h2
        exact ⟨by have := (hpr f hf).2.1; omega, (hpr f hf).2.2.2⟩)
  rw [card_insert_of_notMem hT0_not, card_union_of_disjoint hL2dis, hL2_card] at hbig
  set E : Finset (ℕ × Bool) := ({7, 8, 9, 10} : Finset (Fin 14)).image pos
  have hEcard : E.card = 4 := by
    rw [card_image_of_injOn (fun i hi j hj hij => hpos.2.2 i (by fin_cases i <;> simp at hi <;> rw [hIeq] <;> decide)
      j (by fin_cases j <;> simp at hj <;> rw [hIeq] <;> decide) hij)]
    decide
  have hEexit : ∀ e ∈ E, e ∈ exitArcs 14 D (carrierT 14 D L6) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := mem_image.1 he
    have hiI : i ∈ ineligSet 14 D := by fin_cases i <;> simp at hi <;> rw [hIeq] <;> decide
    have hi0 : i ≠ 0 := by fin_cases i <;> simp at hi <;> decide
    obtain ⟨hj, hemp, hnb, -⟩ := hpos.1 i hiI hi0
    have hne : (sem_g14_nb i ∩ L6).Nonempty := by fin_cases i <;> simp at hi <;> decide +kernel
    obtain ⟨a, ha⟩ := hne
    rw [mem_inter] at ha
    rw [exitArcs, mem_filter]
    refine ⟨mem_product.2 ⟨mem_range.2 hj, mem_univ _⟩,
      sup_mem_carrier.2 ⟨a, mem_inter.2 ⟨hnb a (g14_mem_nb.1 ha.1), ha.2⟩⟩, ?_⟩
    rw [sup_mem_carrier, hemp, Finset.empty_inter]; exact not_nonempty_empty
  have hEdis : ∀ e ∈ E, ∀ f ∈ L6, e ≠ wit f := by
    intro e he f hf hew
    obtain ⟨i, hi, rfl⟩ := mem_image.1 he
    have hiI : i ∈ ineligSet 14 D := by fin_cases i <;> simp at hi <;> rw [hIeq] <;> decide
    have hi0 : i ≠ 0 := by fin_cases i <;> simp at hi <;> decide
    have hnbi : sem_g14_nb i ∩ L6 ⊆ supp 14 D (src D (pos i)) ∩ L6 := fun a ha => by
      rw [mem_inter] at ha ⊢
      exact ⟨(hpos.1 i hiI hi0).2.2.1 a (g14_mem_nb.1 ha.1), ha.2⟩
    have hwsub : supp 14 D (src D (pos i)) ∩ L6 ⊆ sem_g14_nb (ct f) ∩ L6 := hew ▸ (hwit f hf).2.2.2.2.2.1
    have hne : i ≠ ct f := by fin_cases i <;> simp at hi <;> fin_cases f <;> simp [L6] at hf <;> decide
    have hle := sup_g14_inter i (ct f) hne L6
    have hsub' : sem_g14_nb i ∩ L6 ⊆ sem_g14_nb i ∩ (sem_g14_nb (ct f) ∩ L6) := fun a ha =>
      mem_inter.2 ⟨(mem_inter.1 ha).1, hwsub (hnbi ha)⟩
    have hge2 : 2 ≤ (sem_g14_nb i ∩ L6).card := by fin_cases i <;> simp at hi <;> decide +kernel
    have := card_le_card hsub'; omega
  have hcnt_d := sup_count_disj h.1 L6 E hEexit L6 S (fun f => sem_g14_nb (ct f) ∩ L6) wit hwit hSL
    (fun f hf => sup_wit_single (hwit f (hSL hf)) (mem_filter.1 hf).2) hEdis
  have hfib : (L6 \ S).card ≤ 2 * ((L6 \ S).image pr).card := by
    refine Finset.card_le_mul_card_image _ 2 (fun M _ => ?_)
    by_cases hne : ((L6 \ S).filter (fun f => pr f = M)).Nonempty
    · obtain ⟨g, hg⟩ := hne
      rw [mem_filter] at hg
      have hM2 : M.card = 2 := hg.2 ▸ (hpr g hg.1).2.1
      rw [← hM2]
      refine card_le_card (fun f hf => by rw [mem_filter] at hf; exact hf.2 ▸ (hpr f hf.1).2.2.1)
    · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  have hfl := carrier_flow_union h L6 (by rw [g14_supp_out hD]; simp)
  have hL6e : L6 ⊆ eligSet 14 D := fun a ha => by
    by_contra hc; exact (mem_sdiff.1 (hPeq ▸ ha)).2 (sem_mem_inelig.2 hc)
  have hsup := weak_surplus_carrierT_le h.1 b (weakMinBranch_pure hmin) L6 (Or.inl h0I)
  rw [inter_eq_left.2 hL6e] at hsup
  have hSLc := card_sdiff_add_card_eq_card hSL
  have hL6c : L6.card = 6 := by decide
  omega
theorem elim_adj_p1_noB0 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (u v w iu iv iw : Fin 14)
    (hiu : iu ∈ ineligSet 14 D) (hiv : iv ∈ ineligSet 14 D) (hiw : iw ∈ ineligSet 14 D)
    (hu : u ∉ ineligSet 14 D) (hv : v ∉ ineligSet 14 D) (hw : w ∉ ineligSet 14 D)
    (hg : iu ≠ 0 ∧ iv ≠ 0 ∧ iw ≠ 0 ∧ iu ≠ iv ∧ iu ≠ iw ∧ iv ≠ iw ∧ u ≠ w ∧
      hc_adjB iu u = true ∧ hc_adjB iv v = true ∧ hc_adjB iw w = true ∧
      hc_adjB u v = true ∧ hc_adjB v w = true ∧
      (g14_nbB w).card = 3 ∧ decide (u.val < 7) = decide (w.val < 7))
    (hu3 : 3 ≤ (sem_W 14 D u).card) (hv3 : 3 ≤ (sem_W 14 D v).card) : False := by
  obtain ⟨h0u, h0v, h0w, huv, huw, hvw, hneuw, giu, giv, giw, guv, gvw, hdw, hsuw⟩ := hg
  by_cases hw3 : 3 ≤ (sem_W 14 D w).card
  · exact elim_3path_p1 h hD hctx h0I u v w iu iv iw hiu hiv hiw hu hv hw
      ⟨h0u, h0v, h0w, huv, huw, hvw, giu, giv, giw, guv, gvw⟩ hu3 hv3 hw3
  · obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
    rw [hc_adjB_iff] at giu giv giw guv gvw
    obtain ⟨eu, heu, hbeu, hfu, -⟩ := pa_ed h hD hpos (adj_symm guv)
    obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos guv
    have heunot : eu ∉ sem_W 14 D u := pa_ed_not_mem h hbeu
    have hevnot : ev ∉ sem_W 14 D v := pa_ed_not_mem h hbev
    have hWv := pa_three (hsat v (Or.inl h0I) hv3).1 (hsat v (Or.inl h0I) hv3).2 heu
      hPQ (fun hh => heunot (hh ▸ (hsat u (Or.inl h0I) hu3).1))
      (fun hh => heunot (hh ▸ (hsat u (Or.inl h0I) hu3).2)) (hc3 v (Or.inl h0I))
    have hWu := pa_three (hsat u (Or.inl h0I) hu3).1 (hsat u (Or.inl h0I) hu3).2 hev
      hPQ (fun hh => hevnot (hh ▸ (hsat v (Or.inl h0I) hv3).1))
      (fun hh => hevnot (hh ▸ (hsat v (Or.inl h0I) hv3).2)) (hc3 u (Or.inl h0I))
    have hpu : pos iu = P ∨ pos iu = Q := by
      rcases hWu (pos iu) (as_mem hpos hiu h0u giu) with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd (hfv iu hiu h0u h1.symm ▸ hiu) hv
    have hpv : pos iv = P ∨ pos iv = Q := by
      rcases hWv (pos iv) (as_mem hpos hiv h0v giv) with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd (hfu iv hiv h0v h1.symm ▸ hiv) hu
    have hWv' : ∀ e ∈ sem_W 14 D v, e = pos iu ∨ e = pos iv ∨ e = eu := by
      intro e he
      rcases hpu with h1 | h1 <;> rcases hpv with h2 | h2
      · exact absurd (hpos.2.2 _ hiu _ hiv (h1.trans h2.symm)) huv
      · rcases hWv e he with rfl | rfl | rfl
        · exact Or.inl h1.symm
        · exact Or.inr (Or.inl h2.symm)
        · exact Or.inr (Or.inr rfl)
      · rcases hWv e he with rfl | rfl | rfl
        · exact Or.inr (Or.inl h2.symm)
        · exact Or.inl h1.symm
        · exact Or.inr (Or.inr rfl)
      · exact absurd (hpos.2.2 _ hiu _ hiv (h1.trans h2.symm)) huv
    obtain ⟨Dw, -, hWw, hpw⟩ := ps_side h hD hpos hiw h0w giw hdw (by omega)
    obtain ⟨fw, hfw, hbfw, hfwy, hfwx⟩ := pa_ed h hD hpos gvw
    have hbw : sem_bar fw = Dw := by
      rw [hWw, mem_insert, mem_singleton] at hbfw
      exact hbfw.resolve_left (fun hh => hv (hfwx iw hiw h0w hh ▸ hiw))
    rcases hWv' fw hfw with hh | hh | hh
    · exact hw (hfwy iu hiu h0u hh ▸ hiu)
    · exact hw (hfwy iv hiv h0v hh ▸ hiv)
    · exact hpw u hneuw hsuw (hbw ▸ hh ▸ hbeu)
theorem elim_105_p1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB1 : Bplus 14 D = (eligSet 14 D).card + 1)
    (hIeq : ineligSet 14 D = {0, 1, 3, 8, 10}) : False := by
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := mI hIeq
  obtain ⟨pos, P, Q, hpos, hc3, hPQ, hsat⟩ := pa_setup_one h hD hB1
  have hctx : res1_ctx D pos P Q := ⟨hpos, hc3, hPQ, hsat⟩
  by_cases h2 : 3 ≤ (sem_W 14 D 2).card
  · have h13 : (sem_W 14 D 13).card ≤ 2 := by
      by_contra hc; exact elim_adj_p1_noB0 h hD hctx h0I 2 13 4 8 1 10 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) h2 (by omega)
    have h12 : (sem_W 14 D 12).card ≤ 2 := by
      by_contra hc; exact elim_adj_p1_noB0 h hD hctx h0I 2 12 5 8 3 10 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) h2 (by omega)
    have h4 : 3 ≤ (sem_W 14 D 4).card := by
      by_contra hc; exact pa_m1 h hD hpos 4 13 11 10 1 (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by omega) h13
    have h11 : (sem_W 14 D 11).card ≤ 2 := by
      by_contra hc; exact elim_adj_p1_noB0 h hD hctx h0I 4 11 6 10 3 8 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) h4 (by omega)
    exact elim_alt_pair h hD hctx 2 4 12 13 11 8 10 3 1 3 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (Or.inl h0I) (Or.inl h0I) (by decide) h2 h4 h12 h13 h11
  · have h2c : (sem_W 14 D 2).card ≤ 2 := by omega
    have h13 : 3 ≤ (sem_W 14 D 13).card := by
      by_contra hc; exact pa_m1 h hD hpos 13 2 4 1 8 (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by omega) h2c
    have h4c : (sem_W 14 D 4).card ≤ 2 := by
      by_contra hc; exact elim_adj_p1_noB0 h hD hctx h0I 13 4 11 1 10 3 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) h13 (by omega)
    have h11 : 3 ≤ (sem_W 14 D 11).card := by
      by_contra hc; exact pa_m1 h hD hpos 11 4 6 3 10 (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by omega) h4c
    have h6c : (sem_W 14 D 6).card ≤ 2 := by
      by_contra hc; exact elim_adj_p1_noB0 h hD hctx h0I 11 6 9 3 8 1 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) h11 (by omega)
    exact elim_alt_pair h hD hctx 13 11 2 4 6 1 3 8 10 8 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (Or.inl h0I) (Or.inl h0I) (by decide) h13 h11 h2c h4c h6c
theorem bplus_gt_p1_partition : ∀ idx : Fin 157, 97 ≤ idx.val →
    (∃ k : Fin 22, cnt_b1_R_idx k = idx) ∨
    (∃ k : Fin 46, cnt_b1_L_idx k = idx) ∨
    idx.val = 99 ∨ idx.val = 101 ∨ idx.val = 102 ∨ idx.val = 104 ∨ idx.val = 105 ∨
    idx.val = 106 ∨ idx.val = 107 ∨ idx.val = 108 ∨ idx.val = 109 ∨ idx.val = 110 ∨
    idx.val = 111 ∨ idx.val = 112 ∨ idx.val = 113 ∨ idx.val = 114 ∨ idx.val = 137 ∨
    idx.val = 138 ∨ idx.val = 139 ∨ idx.val = 140 := by
  decide +kernel
theorem bplus_gt_p1_ge5 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (idx : Fin 157) (hI : ineligSet 14 D = hc_rep idx)
    (hge5 : 97 ≤ idx.val) : (eligSet 14 D).card + 2 ≤ Bplus 14 D := by
  rcases bplus_gt_p1_partition idx hge5 with ⟨k, rfl⟩ | ⟨k, rfl⟩ | hman
  · exact (elim_cnt_b1_R h hD h11 k hI).elim
  · exact (elim_cnt_b1_L h hD h11 k hI).elim
  · by_contra hle
    have hBgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by by_contra h0; exact tight_le_all h hD (by omega) idx hI
    have hB1 : Bplus 14 D = (eligSet 14 D).card + 1 := by omega
    rcases hman with h99 | h101 | h102 | h104 | h105 | h106 | h107 | h108 |
      h109 | h110 | h111 | h112 | h113 | h114 | h137 | h138 | h139 | h140
    · have hIeq : ineligSet 14 D = {0,1,2,3,10} := by rw [hI, show idx = ⟨99, by decide⟩ from Fin.ext h99]; decide +kernel
      exact elim_share_w3_self_p1 h hD hB1 (mI hIeq) 12 13 2 3 1 5 4 10 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,2,5,11} := by rw [hI, show idx = ⟨101, by decide⟩ from Fin.ext h101]; decide +kernel
      exact elim_tri_w3_p1 h hD hB1 (mI hIeq) 9 12 13 1 5 2 6 3 4 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,2,10,11} := by rw [hI, show idx = ⟨102, by decide⟩ from Fin.ext h102]; decide +kernel
      exact elim_adj_w3_p1 h hD hB1 (mI hIeq) 4 13 10 11 1 2 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,3,4,8} := by rw [hI, show idx = ⟨104, by decide⟩ from Fin.ext h104]; decide +kernel
      exact elim_share_w3_self_p1 h hD hB1 (mI hIeq) 11 13 4 3 1 6 2 8 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,3,8,10} := by rw [hI, show idx = ⟨105, by decide⟩ from Fin.ext h105]; decide +kernel
      exact elim_105_p1 h hD hB1 hIeq
    · have hIeq : ineligSet 14 D = {0,1,4,5,8} := by rw [hI, show idx = ⟨106, by decide⟩ from Fin.ext h106]; decide +kernel
      exact elim_share_w3_self_p1 h hD hB1 (mI hIeq) 9 13 1 5 4 6 2 8 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,4,8,12} := by rw [hI, show idx = ⟨107, by decide⟩ from Fin.ext h107]; decide +kernel
      exact elim_adj_w3_p1 h hD hB1 (mI hIeq) 2 13 8 12 1 4 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,8,10,11} := by rw [hI, show idx = ⟨108, by decide⟩ from Fin.ext h108]; decide +kernel
      exact elim_share_w3_self_p1 h hD hB1 (mI hIeq) 4 6 11 10 8 13 9 1 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,8,11,12} := by rw [hI, show idx = ⟨109, by decide⟩ from Fin.ext h109]; decide +kernel
      exact elim_tri_w3_p1 h hD hB1 (mI hIeq) 2 3 6 8 12 11 13 7 9 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,10,11,12} := by rw [hI, show idx = ⟨110, by decide⟩ from Fin.ext h110]; decide +kernel
      exact elim_tri_w3_p1 h hD hB1 (mI hIeq) 3 4 5 12 11 10 7 13 9 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,4,5,7,8} := by rw [hI, show idx = ⟨111, by decide⟩ from Fin.ext h111]; decide +kernel
      exact elim_95_p1 h hD hB1 hIeq
    · have hIeq : ineligSet 14 D = {0,4,7,8,9} := by rw [hI, show idx = ⟨112, by decide⟩ from Fin.ext h112]; decide +kernel
      exact elim_share_w3_self_p1 h hD hB1 (mI hIeq) 1 6 9 7 8 13 11 4 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,4,7,9,12} := by rw [hI, show idx = ⟨113, by decide⟩ from Fin.ext h113]; decide +kernel
      exact elim_tri_w3_p1 h hD hB1 (mI hIeq) 1 3 5 9 7 12 13 11 10 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,7,8,9,10} := by rw [hI, show idx = ⟨114, by decide⟩ from Fin.ext h114]; decide +kernel
      exact elim_114_p1 h hD h11 hB1 hIeq
    · have hIeq : ineligSet 14 D = {0,1,2,3,6,10} := by rw [hI, show idx = ⟨137, by decide⟩ from Fin.ext h137]; decide +kernel
      exact elim_disj_w3_p1 h hD hB1 (mI hIeq) 9 12 1 6 5 2 3 5 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,3,4,5,8} := by rw [hI, show idx = ⟨138, by decide⟩ from Fin.ext h138]; decide +kernel
      exact elim_disj_w3_p1 h hD hB1 (mI hIeq) 9 11 1 5 6 3 4 6 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,1,8,10,11,12} := by rw [hI, show idx = ⟨139, by decide⟩ from Fin.ext h139]; decide +kernel
      exact elim_disj_w3_p1 h hD hB1 (mI hIeq) 2 4 8 12 13 10 11 13 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (by decide)
    · have hIeq : ineligSet 14 D = {0,4,7,8,9,12} := by rw [hI, show idx = ⟨140, by decide⟩ from Fin.ext h140]; decide +kernel
      exact elim_disj_w3_p1 h hD hB1 (mI hIeq) 1 2 7 9 13 8 12 13 (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (by decide)
theorem cnt_b2_R_comb : ∀ k : Fin 4,
    let I := hc_rep (cnt_b2_R_idx k)
    let P := sideR \ I
    let IinBase := kPos7.filter (fun j : Fin 7 => os_ptL j ∈ I ∧ g14_nbB (os_ptL j) ⊆ P)
    ∀ m : Fin 128,
    let Oc := maskFin7 m
    (∀ j ∈ Oc, j ∈ kPos7 ∧ g14_nbB (os_ptL j) ⊆ P) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptL j)).card = 2)
    let Ct := kPos7 \ Oc
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptL j) ∩ P)
    let extra0 := if (0 : Fin 14) ∈ I ∧ (10 : Fin 14) ∉ I ∧ (10 : Fin 14) ∉ Lab then 1 else 0
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + IinBase.card + extra0 + Lab.card + (14 - I.card) + (IinBase \ Oc).card) ∨
    (11 < (16 - I.card) + (IinBase \ Oc).card) := by
  decide +kernel
theorem cnt_b2_R_ge5 : ∀ k : Fin 4, 97 ≤ (cnt_b2_R_idx k).val := by decide
theorem elim_cnt_b2_R {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 4)
    (hI : ineligSet 14 D = hc_rep (cnt_b2_R_idx k)) : False := by
  have hBgt := bplus_gt_p1_ge5 h hD h11 (cnt_b2_R_idx k) hI (cnt_b2_R_ge5 k)
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideR_step h hD
  have hcomb := cnt_b2_R_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases hcomb hsub with h1 | h2 <;> omega
theorem cnt_b2_L_comb : ∀ k : Fin 6,
    let I := hc_rep (cnt_b2_L_idx k)
    let P := sideL \ I
    let Iin := Finset.univ.filter (fun j : Fin 7 => os_ptR j ∈ I ∧ okL_pred I P j)
    ∀ m : Fin 128,
    let Oc := maskFin7 m
    (∀ j ∈ Oc, okL_pred I P j) →
    let Oc3 := Oc.filter (fun j => (g14_nbB (os_ptR j) ∩ P).card = 3)
    let Oc2 := Oc.filter (fun j => (g14_nbB (os_ptR j) ∩ P).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Lab := Ct.biUnion (fun j => g14_nbB (os_ptR j) ∩ P)
    (2 * P.card + 11 < 2 * Oc3.card + Oc2.card + Iin.card + Lab.card + (14 - I.card) + (Iin \ Oc).card) ∨
    (11 < (16 - I.card) + (Iin \ Oc).card) := by
  decide +kernel
theorem cnt_b2_L_ge5 : ∀ k : Fin 6, 97 ≤ (cnt_b2_L_idx k).val := by decide
theorem elim_cnt_b2_L {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (k : Fin 6)
    (hI : ineligSet 14 D = hc_rep (cnt_b2_L_idx k)) : False := by
  have hBgt := bplus_gt_p1_ge5 h hD h11 (cnt_b2_L_idx k) hI (cnt_b2_L_ge5 k)
  obtain ⟨m, hsub, hcnt, hlost⟩ := g14_sideL_step h hD
  have hcomb := cnt_b2_L_comb k m
  dsimp only at hcomb hsub hcnt hlost
  rw [← hI] at hcomb
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases hcomb hsub with h1 | h2 <;> omega
theorem pa_card5 {α : Type} [DecidableEq α] {s : Finset α} {a b c d e : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : 5 ≤ s.card := by
  have hsub : ({a, b, c, d, e} : Finset α) ⊆ s := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := card_le_card hsub
  rwa [card_insert_of_notMem (by simp [hab, hac, had, hae]),
    card_insert_of_notMem (by simp [hbc, hbd, hbe]),
    card_insert_of_notMem (by simp [hcd, hce]),
    card_pair hde] at this
theorem pa_four {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : s.card ≤ 4) : ∀ e ∈ s, e = a ∨ e = b ∨ e = c ∨ e = d := by
  intro e he
  by_contra hne
  rw [not_or, not_or, not_or] at hne
  have := pa_card5 he ha hb hc hd hne.1 hne.2.1 hne.2.2.1 hne.2.2.2 hab hac had hbc hbd hcd
  omega
theorem mem_W_of_pos {D : Dag} {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    {j t : Fin 14} (hj : j ∈ ineligSet 14 D) (hj0 : j ≠ 0) (ht : t ∈ supp 14 D (src D (pos j))) :
    pos j ∈ sem_W 14 D t := by
  obtain ⟨h1, h2, -, -⟩ := hpos.1 j hj hj0
  exact sem_mem_W.2 ⟨h1, ht, by rw [h2]; exact notMem_empty t⟩
theorem pe_co_g14 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (b : Fin 14 → ℕ)
    (hb : PureBranch 14 D b) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    {v t j q : Fin 14} (hj : j ∈ ineligSet 14 D) (hv : v ∈ eligSet 14 D)
    (hres : ∀ u ∈ residualUnits 14 D b, v ∈ supp 14 D u.1 → t ∈ supp 14 D u.1)
    {w : ℕ} (hw : v ∈ supp 14 D w ∧ t ∈ supp 14 D w)
    (hg : j ≠ 0 ∧ (g14_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j q = true ∧
      v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false) :
    t ∈ supp 14 D (src D (pos j)) := by
  obtain ⟨hj0, hdv, hjv, hjq, hvt, hvq, htq⟩ := hg
  rw [hc_adjB_iff] at hjv hjq
  obtain ⟨e0, he0⟩ := ri_gen sem_g14_gr h (sem_g14_comp hD) b hb hvt
    (nbr_diff_exists v t hvt (deg3_ne0 v hdv)) hv hres hw
  by_contra hn
  have h0 : pos j = e0 := by
    by_contra hne
    exact hn (he0 _ (as_mem hpos hj hj0 hjv) hne)
  obtain ⟨e, he, h1, h2⟩ := g14_deg3_cover_free h hD hdv hvt hvq (sem_adjB_false.1 htq)
  exact h1 (he0 e he (fun hee => h2 (by rw [hee, ← h0]; exact (hpos.1 j hj hj0).2.2.1 q hjq)))
theorem ru_sub_excl {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    {v i1 i2 v3 t : Fin 14} (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (hv : v ∈ eligSet 14 D) (hv3 : v3 ∉ ineligSet 14 D)
    (hg : i1 ≠ 0 ∧ i2 ≠ 0 ∧ (g14_nbB v).card = 3 ∧ i1 ≠ i2 ∧
      hc_adjB i1 v = true ∧ hc_adjB i2 v = true ∧ hc_adjB v v3 = true)
    (hru1 : (ru D b v).card = 1) (hsub : ru D b v ⊆ ru D b t) (hvt : v ≠ t)
    (hq : ∃ q : Fin 14,
      (hc_adjB i1 q = true ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB i1 t = false) ∨
      (hc_adjB i2 q = true ∧ v ≠ q ∧ hc_adjB t q = false ∧ hc_adjB i2 t = false)) : False := by
  obtain ⟨hi10, hi20, hdv, hne, h1, h2, h3⟩ := hg
  have hcv : (sem_W 14 D v).card ≤ 3 := by have := cc_le h hD b hb v; omega
  obtain ⟨hf1, hf2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 hv3 ⟨hi10, hi20, hne, h1, h2, h3⟩ hcv
  obtain ⟨u, hu⟩ := card_pos.1 (by omega : 0 < (ru D b v).card)
  have hut := hsub hu
  have hres : ∀ u' ∈ residualUnits 14 D b, v ∈ supp 14 D u'.1 → t ∈ supp 14 D u'.1 :=
    fun u' hu' hv' => (mem_filter.1 (hsub (mem_filter.2 ⟨hu', hv'⟩))).2
  have hw : v ∈ supp 14 D u.1 ∧ t ∈ supp 14 D u.1 :=
    ⟨(mem_filter.1 hu).2, (mem_filter.1 hut).2⟩
  obtain ⟨q, ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩⟩ := hq
  · exact sem_adjB_false.1 a4 ((hf1 t).1 (pe_co_g14 h hD b hb hpos hi1 hv hres hw ⟨hi10, hdv, h1, a1, hvt, a2, a3⟩))
  · exact sem_adjB_false.1 a4 ((hf2 t).1 (pe_co_g14 h hD b hb hpos hi2 hv hres hw ⟨hi20, hdv, h2, a1, hvt, a2, a3⟩))
theorem pe_co_blow5 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos14 D pos)
    (a b a1 a2 qa1 qa2 b1 b2 vb : Fin 14)
    (ha : a ∈ eligSet 14 D) (ha1 : a1 ∈ ineligSet 14 D) (ha2 : a2 ∈ ineligSet 14 D)
    (hb1 : b1 ∈ ineligSet 14 D) (hb2 : b2 ∈ ineligSet 14 D)
    (hvb : vb ∉ ineligSet 14 D)
    (hg : a1 ≠ 0 ∧ a2 ≠ 0 ∧ b1 ≠ 0 ∧ b2 ≠ 0 ∧
      a ≠ b ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
      (g14_nbB a).card = 3 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧
      hc_adjB a1 qa1 = true ∧ a ≠ qa1 ∧ hc_adjB b qa1 = false ∧
      hc_adjB a2 qa2 = true ∧ a ≠ qa2 ∧ hc_adjB b qa2 = false ∧
      hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true)
    (hAn : 1 ≤ (ru D br a).card) (hsub : ru D br a ⊆ ru D br b) (hBle : (ru D br b).card ≤ 2) :
    False := by
  obtain ⟨ha10, ha20, hb10, hb20, hab, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12, hda, ga1, ga2,
    gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2, gb1, gb2, gvb⟩ := hg
  obtain ⟨u, hu⟩ := card_pos.1 (by omega : 0 < (ru D br a).card)
  have hres : ∀ u' ∈ residualUnits 14 D br, a ∈ supp 14 D u'.1 → b ∈ supp 14 D u'.1 :=
    fun u' hu' ha' => (mem_filter.1 (hsub (mem_filter.2 ⟨hu', ha'⟩))).2
  have hw : a ∈ supp 14 D u.1 ∧ b ∈ supp 14 D u.1 :=
    ⟨(mem_filter.1 hu).2, (mem_filter.1 (hsub hu)).2⟩
  have hm1 := mem_W_of_pos hpos ha1 ha10 (pe_co_g14 h hD br hbr hpos ha1 ha hres hw ⟨ha10, hda, ga1, gqa1, hab, haqa1, gbqa1⟩)
  have hm2 := mem_W_of_pos hpos ha2 ha20 (pe_co_g14 h hD br hbr hpos ha2 ha hres hw ⟨ha20, hda, ga2, gqa2, hab, haqa2, gbqa2⟩)
  have hb1m := as_mem hpos hb1 hb10 ((hc_adjB_iff _ _).1 gb1)
  have hb2m := as_mem hpos hb2 hb20 ((hc_adjB_iff _ _).1 gb2)
  obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
  have h5 := pa_card5 hm1 hm2 hb1m hb2m hev
    (fun e => ha12 (hpos.2.2 _ ha1 _ ha2 e))
    (fun e => ha1b1 (hpos.2.2 _ ha1 _ hb1 e))
    (fun e => ha1b2 (hpos.2.2 _ ha1 _ hb2 e))
    (fun e => hvb (hfv _ ha1 ha10 e.symm ▸ ha1))
    (fun e => ha2b1 (hpos.2.2 _ ha2 _ hb1 e))
    (fun e => ha2b2 (hpos.2.2 _ ha2 _ hb2 e))
    (fun e => hvb (hfv _ ha2 ha20 e.symm ▸ ha2))
    (fun e => hb12 (hpos.2.2 _ hb1 _ hb2 e))
    (fun e => hvb (hfv _ hb1 hb10 e.symm ▸ hb1))
    (fun e => hvb (hfv _ hb2 hb20 e.symm ▸ hb2))
  have hc4 := cc_le h hD br hbr b
  omega
theorem full_of_le2 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos) {i x c : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hi0 : i ≠ 0) (hc : c ∉ ineligSet 14 D)
    (hix : Adj i x) (hxc : Adj x c) (hdx : (g14_nbB x).card = 3)
    (hcx : (sem_W 14 D x).card ≤ 2) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  obtain ⟨Dx, -, hWx, -⟩ := ps_side h hD hpos hi hi0 hix hdx hcx
  obtain ⟨e, he, hbe, hfe, -⟩ := pa_ed h hD hpos hxc
  have hed : e = Dx := by
    rw [hWx, mem_insert, mem_singleton] at he
    exact he.resolve_left (fun hh => hc (hfe i hi hi0 hh ▸ hi))
  exact full_g14 h hD hB0 hpos hi hi0 hix (fun p hp hne hsub => by
    rw [hWx, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hne rfl
    · exact hc (mem_singleton.1 (hsub (hed ▸ (sem_mem_W.1 hbe).2.1)) ▸ hi))
theorem full_g14_or_arc {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos) {i : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hi0 : i ≠ 0) :
    (∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t) ∨
    ∃ p : ℕ × Bool, p.1 < D.length ∧ p.1 ≠ (pos i).1 ∧ tag D p.1 = true ∧
      supp 14 D (src D (sem_bar p)) ⊆ {i} ∧
      ∀ v, Adj i v → v ∈ supp 14 D (src D p) := by
  classical
  by_cases hf : ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t
  · exact Or.inl hf
  · right
    have hS := h.1
    have hsep : ∀ u : Fin 14, u ≠ i → ∃ z, Adj i z ∧ ¬ Adj u z := fun u hu => nbr_diff_exists i u hu.symm hi0
    obtain ⟨e, -, -, -, -, -, hex, -⟩ := sem_inelig_consumer sem_g14_gr h (sem_g14_comp hD) hsep hi
    have hbar : sem_bar (pos i) = e := by
      have hm : sem_bar (pos i) ∈ sem_W 14 D i := by
        obtain ⟨h1, h2, -, h4⟩ := hpos.1 i hi hi0
        exact sem_mem_W.2 ⟨h1, by rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h4]; exact mem_singleton_self i,
          by dsimp only [sem_bar]; rw [h2]; exact notMem_empty i⟩
      rw [sem_W, hex, mem_singleton] at hm; exact hm
    have hnotall : ¬ (∀ j, Relation.ReflTransGen (sem_step 14 D) (14 + e.1) (14 + j) → j ≠ e.1 → tag D j = false) := by
      intro hall
      have hfs := sem_full_support sem_g14_gr h (sem_g14_comp hD) hsep hi hex hall
      exact hf (fun t => by simpa [← hbar, sem_bar_bar] using hfs t)
    push Not at hnotall
    obtain ⟨j, hreach, hje, ht'⟩ := hnotall
    have ht : tag D j = true := by cases htj : tag D j <;> simp_all
    rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
    · exact absurd (by omega) hje
    · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
      have hjj : j' = j := by omega
      subst hjj
      have hew : e ∈ sem_W 14 D i := by rw [sem_W, hex]; exact mem_singleton_self e
      obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
      have hreach2 : Relation.ReflTransGen (sem_step 14 D) i.val w :=
        ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
          (sem_step_src he1 e.2)).trans hw1
      have hch := sem_noempty_unique sem_g14_gr h (sem_g14_comp hD) hB0 hsep hi hreach2
      have hf1 : fanout D w = 1 := by
        have h1 := sem_step_fanout hw2
        by_contra hne
        have h2 := sem_branch_empty sem_g14_gr hS (sem_g14_comp hD) hsep hi hch (by omega)
        have h4 := sem_bzero_branch hS hB0 (b := w) (by omega)
        rw [h2] at h4; exact not_nonempty_empty h4
      have hsub : supp 14 D w ⊆ {i} := sem_dom_pure sem_g14_gr hS (sem_g14_comp hD) i hsep w (sem_chain_dom hS hch)
      have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
      refine ⟨(j', !s), hj', by rw [← hbar] at hje; exact hje, ht, by dsimp only [sem_bar]; rw [hw']; exact hsub, fun v hiv => ?_⟩
      exact sem_and_sibling_nbrs sem_g14_gr hS (sem_g14_comp hD) hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf1)
        (by unfold outW; omega) hiv
theorem elim_disj_ps_pair {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hpos : k4_Pos14 D pos) (hPQ : P ≠ Q)
    (u v iu iv a1 a2 b1 b2 ia1 ia2 ib1 ib2 : Fin 14)
    (hiu : iu ∈ ineligSet 14 D) (hiv : iv ∈ ineligSet 14 D)
    (hia1 : ia1 ∈ ineligSet 14 D) (hia2 : ia2 ∈ ineligSet 14 D)
    (hib1 : ib1 ∈ ineligSet 14 D) (hib2 : ib2 ∈ ineligSet 14 D)
    (hu : u ∉ ineligSet 14 D) (hv : v ∉ ineligSet 14 D)
    (ha1 : a1 ∉ ineligSet 14 D) (ha2 : a2 ∉ ineligSet 14 D)
    (hb1 : b1 ∉ ineligSet 14 D) (hb2 : b2 ∉ ineligSet 14 D)
    (hg : iu ≠ 0 ∧ iv ≠ 0 ∧ ia1 ≠ 0 ∧ ia2 ≠ 0 ∧ ib1 ≠ 0 ∧ ib2 ≠ 0 ∧
      a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
      hc_adjB iu u = true ∧ hc_adjB iv v = true ∧
      hc_adjB u a1 = true ∧ hc_adjB u a2 = true ∧ hc_adjB v b1 = true ∧ hc_adjB v b2 = true ∧
      hc_adjB ia1 a1 = true ∧ hc_adjB ia2 a2 = true ∧ hc_adjB ib1 b1 = true ∧ hc_adjB ib2 b2 = true ∧
      (g14_nbB a1).card = 3 ∧ (g14_nbB a2).card = 3 ∧ (g14_nbB b1).card = 3 ∧ (g14_nbB b2).card = 3 ∧
      decide (a1.val < 7) = decide (a2.val < 7) ∧ decide (a1.val < 7) = decide (b1.val < 7) ∧
      decide (a1.val < 7) = decide (b2.val < 7))
    (hcu : (sem_W 14 D u).card ≤ 3) (hcv : (sem_W 14 D v).card ≤ 3)
    (hca1 : (sem_W 14 D a1).card ≤ 2) (hca2 : (sem_W 14 D a2).card ≤ 2)
    (hcb1 : (sem_W 14 D b1).card ≤ 2) (hcb2 : (sem_W 14 D b2).card ≤ 2)
    (hPu : P ∈ sem_W 14 D u) (hQu : Q ∈ sem_W 14 D u)
    (hPv : P ∈ sem_W 14 D v) (hQv : Q ∈ sem_W 14 D v) : False := by
  obtain ⟨h0u, h0v, h0a1, h0a2, h0b1, h0b2, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12,
    giu, giv, gua1, gua2, gvb1, gvb2, gia1, gia2, gib1, gib2,
    hda1, hda2, hdb1, hdb2, hsa12, hsa1b1, hsa1b2⟩ := hg
  rw [hc_adjB_iff] at giu giv gua1 gua2 gvb1 gvb2 gia1 gia2 gib1 gib2
  obtain ⟨Da1, -, hWa1, hpa1⟩ := ps_side h hD hpos hia1 h0a1 gia1 hda1 hca1
  obtain ⟨Da2, -, hWa2, hpa2⟩ := ps_side h hD hpos hia2 h0a2 gia2 hda2 hca2
  obtain ⟨Db1, -, hWb1, hpb1⟩ := ps_side h hD hpos hib1 h0b1 gib1 hdb1 hcb1
  obtain ⟨Db2, -, hWb2, -⟩ := ps_side h hD hpos hib2 h0b2 gib2 hdb2 hcb2
  obtain ⟨fa1, hfa1, hbfa1, hfa1y, hfa1x⟩ := pa_ed h hD hpos gua1
  obtain ⟨fa2, hfa2, hbfa2, hfa2y, hfa2x⟩ := pa_ed h hD hpos gua2
  obtain ⟨fb1, hfb1, hbfb1, hfb1y, hfb1x⟩ := pa_ed h hD hpos gvb1
  obtain ⟨fb2, hfb2, hbfb2, hfb2y, hfb2x⟩ := pa_ed h hD hpos gvb2
  have hba1 : sem_bar fa1 = Da1 := by
    rw [hWa1, mem_insert, mem_singleton] at hbfa1
    exact hbfa1.resolve_left (fun hh => hu (hfa1x ia1 hia1 h0a1 hh ▸ hia1))
  have hba2 : sem_bar fa2 = Da2 := by
    rw [hWa2, mem_insert, mem_singleton] at hbfa2
    exact hbfa2.resolve_left (fun hh => hu (hfa2x ia2 hia2 h0a2 hh ▸ hia2))
  have hbb1 : sem_bar fb1 = Db1 := by
    rw [hWb1, mem_insert, mem_singleton] at hbfb1
    exact hbfb1.resolve_left (fun hh => hv (hfb1x ib1 hib1 h0b1 hh ▸ hib1))
  have hWu := pa_three (as_mem hpos hiu h0u giu) hfa1 hfa2
    (fun hh => ha1 (hfa1y iu hiu h0u hh.symm ▸ hiu))
    (fun hh => ha2 (hfa2y iu hiu h0u hh.symm ▸ hiu))
    (fun hh => hpa1 a2 ha12.symm hsa12.symm (hba1 ▸ hh ▸ hbfa2)) hcu
  have hWv := pa_three (as_mem hpos hiv h0v giv) hfb1 hfb2
    (fun hh => hb1 (hfb1y iv hiv h0v hh.symm ▸ hiv))
    (fun hh => hb2 (hfb2y iv hiv h0v hh.symm ▸ hiv))
    (fun hh => hpb1 b2 hb12.symm (hsa1b2.symm.trans hsa1b1) (hbb1 ▸ hh ▸ hbfb2)) hcv
  have honly : ∀ e, e ∈ sem_W 14 D u → e ∈ sem_W 14 D v → e = pos iu := by
    intro e he1 he2
    rcases hWu e he1 with rfl | rfl | rfl
    · rfl
    · rcases hWv _ he2 with hh | hh | hh
      · exact absurd (hfa1y iv hiv h0v hh ▸ hiv) ha1
      · exact absurd (hba1 ▸ hh ▸ hbfb1) (hpa1 b1 ha1b1.symm hsa1b1.symm)
      · exact absurd (hba1 ▸ hh ▸ hbfb2) (hpa1 b2 ha1b2.symm hsa1b2.symm)
    · rcases hWv _ he2 with hh | hh | hh
      · exact absurd (hfa2y iv hiv h0v hh ▸ hiv) ha2
      · exact absurd (hba2 ▸ hh ▸ hbfb1) (hpa2 b1 ha2b1.symm (hsa1b1.symm.trans hsa12))
      · exact absurd (hba2 ▸ hh ▸ hbfb2) (hpa2 b2 ha2b2.symm (hsa1b2.symm.trans hsa12))
  exact hPQ ((honly P hPu hPv).trans (honly Q hQu hQv).symm)
theorem r2_push {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (br : Fin 14 → ℕ)
    (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (u v iu q : Fin 14) (hiu : iu ∈ ineligSet 14 D) (hu : u ∈ eligSet 14 D)
    (hg : iu ≠ 0 ∧ (g14_nbB u).card = 3 ∧ hc_adjB iu u = true ∧ hc_adjB iu q = true ∧
      u ≠ v ∧ u ≠ q ∧ hc_adjB v q = false)
    (hun : (ru D br u).Nonempty) (hsub : ru D br u ⊆ ru D br v) :
    v ∈ supp 14 D (src D (pos iu)) := by
  obtain ⟨w, hw⟩ := hun
  have hres : ∀ u' ∈ residualUnits 14 D br, u ∈ supp 14 D u'.1 → v ∈ supp 14 D u'.1 :=
    fun u' hu' h' => (mem_filter.1 (hsub (mem_filter.2 ⟨hu', h'⟩))).2
  exact pe_co_g14 h hD br hbr hpos hiu hu hres ⟨(mem_filter.1 hw).2, (mem_filter.1 (hsub hw)).2⟩ hg
theorem r2_ne00 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (br : Fin 14 → ℕ)
    (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (a b c ia ib : Fin 14) (hia : ia ∈ ineligSet 14 D) (hib : ib ∈ ineligSet 14 D)
    (ha : a ∉ ineligSet 14 D) (hb : b ∉ ineligSet 14 D) (hc : c ∉ ineligSet 14 D)
    (hg : hc_adjB ia a = true ∧ hc_adjB ib b = true ∧ hc_adjB a b = true ∧ hc_adjB a c = true ∧
      c ≠ b ∧ (g14_nbB b).card = 3 ∧ decide (c.val < 7) = decide (b.val < 7) ∧ ia ≠ 0 ∧ ib ≠ 0)
    (ha0 : ru D br a = ∅) (hb0 : ru D br b = ∅) : False := by
  have hca : (sem_W 14 D a).card ≤ 2 := by have := cc_le h hD br hbr a; rw [ha0, card_empty] at this; omega
  have hcb : (sem_W 14 D b).card ≤ 2 := by have := cc_le h hD br hbr b; rw [hb0, card_empty] at this; omega
  exact pa_m1 h hD hpos a b c ia ib hia hib ha hb hc hg hca hcb
theorem r2_same1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (u v iu iv n1 qu qv : Fin 14) (hiu : iu ∈ ineligSet 14 D) (hiv : iv ∈ ineligSet 14 D)
    (hu : u ∈ eligSet 14 D) (hv : v ∈ eligSet 14 D) (hn1 : n1 ∉ ineligSet 14 D)
    (hg : iu ≠ 0 ∧ iv ≠ 0 ∧ (g14_nbB u).card = 3 ∧ (g14_nbB v).card = 3 ∧ iu ≠ iv ∧ u ≠ v ∧ n1 ≠ iv ∧
      hc_adjB iu u = true ∧ hc_adjB iv v = true ∧ hc_adjB v n1 = true ∧
      hc_adjB iu qu = true ∧ u ≠ qu ∧ hc_adjB v qu = false ∧
      hc_adjB iv qv = true ∧ v ≠ qv ∧ hc_adjB u qv = false ∧ hc_adjB iv u = false)
    (hv1 : (ru D br v).card = 1) (heq : ru D br u = ru D br v) : False := by
  obtain ⟨h0u, h0v, hdu, hdv, hiuv, huv, hn1iv, giu, giv, gvn1, gqu, huqu, gvqu, gqv, hvqv, guqv, gnivu⟩ := hg
  have hvn : (ru D br v).Nonempty := card_pos.1 (by omega)
  have hun : (ru D br u).Nonempty := heq.symm ▸ hvn
  have hpu_in_v := mem_W_of_pos hpos hiu h0u (r2_push h hD br hbr hpos u v iu qu hiu hu ⟨h0u, hdu, giu, gqu, huv, huqu, gvqu⟩ hun (by rw [heq]))
  have hu_in_pv := r2_push h hD br hbr hpos v u iv qv hiv hv ⟨h0v, hdv, giv, gqv, huv.symm, hvqv, guqv⟩ hvn (by rw [heq])
  obtain ⟨e1, he1, hbe1, hf1, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvn1)
  have hWv_le3 : (sem_W 14 D v).card ≤ 3 := by have := cc_le h hD br hbr v; omega
  have hWv := pa_three (as_mem hpos hiv h0v ((hc_adjB_iff _ _).1 giv)) hpu_in_v he1
    (fun e => hiuv.symm (hpos.2.2 _ hiv _ hiu e))
    (fun e => hn1 (hf1 _ hiv h0v e.symm ▸ hiv))
    (fun e => hn1 (hf1 _ hiu h0u e.symm ▸ hiu)) hWv_le3
  have hfull := full_g14 h hD hB0 hpos hiv h0v ((hc_adjB_iff _ _).1 giv) (fun p hp hne1 hsub => by
    rcases hWv p hp with rfl | rfl | rfl
    · exact hne1 rfl
    · have hm : iu ∈ supp 14 D (src D (sem_bar (pos iu))) := by
        rw [show src D (sem_bar (pos iu)) = src D ((pos iu).1, !(pos iu).2) from rfl,
          (hpos.1 iu hiu h0u).2.2.2]; exact mem_singleton_self iu
      exact hiuv (mem_singleton.1 (hsub hm))
    · exact hn1iv (mem_singleton.1 (hsub (sem_mem_W.1 hbe1).2.1)))
  exact sem_adjB_false.1 gnivu ((hfull u).1 hu_in_pv)
theorem r2_hom2_edges {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (v iv w iw n2 : Fin 14) (hiv : iv ∈ ineligSet 14 D) (hiw : iw ∈ ineligSet 14 D)
    (hv : v ∉ ineligSet 14 D) (hw : w ∉ ineligSet 14 D) (hn2 : n2 ∉ ineligSet 14 D)
    (hg : w ≠ n2 ∧ iw ≠ 0 ∧ (g14_nbB w).card = 3 ∧ hc_adjB iv v = true ∧ hc_adjB iw w = true ∧
      hc_adjB v w = true ∧ hc_adjB v n2 = true ∧ decide (w.val < 7) = decide (n2.val < 7))
    (hw0 : ru D br w = ∅) :
    ∃ ew en2 : ℕ × Bool, ew ∈ sem_W 14 D v ∧ en2 ∈ sem_W 14 D v ∧
      ew ≠ en2 ∧ w ∈ supp 14 D (src D (sem_bar ew)) ∧ n2 ∈ supp 14 D (src D (sem_bar en2)) ∧
      (∀ i ∈ ineligSet 14 D, i ≠ 0 → ew = pos i → w = i) ∧ (∀ i ∈ ineligSet 14 D, i ≠ 0 → en2 = pos i → n2 = i) := by
  obtain ⟨hwn2, hiw0, hdw, giv, giw, gvw, gvn2, hswn⟩ := hg
  rw [hc_adjB_iff] at giv giw gvw gvn2
  have hcw : (sem_W 14 D w).card ≤ 2 := by have := cc_le h hD br hbr w; rw [hw0, card_empty] at this; omega
  obtain ⟨Dw, -, hWw, hpw⟩ := ps_side h hD hpos hiw hiw0 giw hdw hcw
  obtain ⟨ew, hew, hbew, hfw, hfwx⟩ := pa_ed h hD hpos gvw
  obtain ⟨en2, hen2, hben2, hfn2, -⟩ := pa_ed h hD hpos gvn2
  have hbw : sem_bar ew = Dw := by
    rw [hWw, mem_insert, mem_singleton] at hbew
    exact hbew.resolve_left (fun hh => hv (hfwx iw hiw hiw0 hh ▸ hiw))
  exact ⟨ew, en2, hew, hen2, fun hh => hpw n2 hwn2.symm hswn.symm (hbw ▸ hh ▸ hben2),
    (sem_mem_W.1 hbew).2.1, (sem_mem_W.1 hben2).2.1, hfw, hfn2⟩
theorem r2_hom2_full1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (v iv w iw n2 u qv : Fin 14) (hiv : iv ∈ ineligSet 14 D) (hiw : iw ∈ ineligSet 14 D)
    (hv : v ∈ eligSet 14 D) (hv' : v ∉ ineligSet 14 D) (hw : w ∉ ineligSet 14 D) (hn2 : n2 ∉ ineligSet 14 D)
    (hg : w ≠ n2 ∧ iv ≠ 0 ∧ iw ≠ 0 ∧ (g14_nbB v).card = 3 ∧ (g14_nbB w).card = 3 ∧
      w ≠ iv ∧ n2 ≠ iv ∧ v ≠ u ∧ v ≠ qv ∧
      hc_adjB iv v = true ∧ hc_adjB iw w = true ∧ hc_adjB v w = true ∧ hc_adjB v n2 = true ∧
      decide (w.val < 7) = decide (n2.val < 7) ∧
      hc_adjB iv qv = true ∧ hc_adjB u qv = false ∧ hc_adjB iv u = false)
    (hw0 : ru D br w = ∅) (hv1 : (ru D br v).card = 1) (hsub : ru D br v ⊆ ru D br u) : False := by
  obtain ⟨hwn2, hiv0, hiw0, hdv, hdw, hwiv, hn2iv, hvu, hvqv, giv, giw, gvw, gvn2, hswn, gqv, guqv, gnivu⟩ := hg
  obtain ⟨ew, en2, hew, hen2, hne, hbw, hbn2, hfw, hfn2⟩ :=
    r2_hom2_edges h hD br hbr hpos v iv w iw n2 hiv hiw hv' hw hn2 ⟨hwn2, hiw0, hdw, giv, giw, gvw, gvn2, hswn⟩ hw0
  have hu_in_pv := r2_push h hD br hbr hpos v u iv qv hiv hv ⟨hiv0, hdv, giv, gqv, hvu, hvqv, guqv⟩
    (card_pos.1 (by omega)) hsub
  have hWv_le3 : (sem_W 14 D v).card ≤ 3 := by have := cc_le h hD br hbr v; omega
  have hWv := pa_three (as_mem hpos hiv hiv0 ((hc_adjB_iff _ _).1 giv)) hew hen2
    (fun e => hw (hfw _ hiv hiv0 e.symm ▸ hiv)) (fun e => hn2 (hfn2 _ hiv hiv0 e.symm ▸ hiv)) hne hWv_le3
  have hfull := full_g14 h hD hB0 hpos hiv hiv0 ((hc_adjB_iff _ _).1 giv) (fun p hp hne1 hsub' => by
    rcases hWv p hp with rfl | rfl | rfl
    · exact hne1 rfl
    · exact hwiv (mem_singleton.1 (hsub' hbw))
    · exact hn2iv (mem_singleton.1 (hsub' hbn2)))
  exact sem_adjB_false.1 gnivu ((hfull u).1 hu_in_pv)
theorem r2_hom2_R_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (hR2 : (residualUnits 14 D br).card = 2)
    (v iv w iw n2 u iu qu t qv : Fin 14)
    (hiv : iv ∈ ineligSet 14 D) (hiw : iw ∈ ineligSet 14 D) (hiu : iu ∈ ineligSet 14 D)
    (hv : v ∈ eligSet 14 D) (hu : u ∈ eligSet 14 D)
    (hv' : v ∉ ineligSet 14 D) (hw : w ∉ ineligSet 14 D) (hn2 : n2 ∉ ineligSet 14 D)
    (hg : w ≠ n2 ∧ iv ≠ 0 ∧ iw ≠ 0 ∧ iu ≠ 0 ∧ (g14_nbB v).card = 3 ∧ (g14_nbB w).card = 3 ∧ (g14_nbB u).card = 3 ∧
      iv ≠ iu ∧ w ≠ iv ∧ n2 ≠ iv ∧ u ≠ v ∧ u ≠ qu ∧ v ≠ t ∧ v ≠ qv ∧
      hc_adjB iv v = true ∧ hc_adjB iw w = true ∧ hc_adjB iu u = true ∧
      hc_adjB v w = true ∧ hc_adjB v n2 = true ∧ decide (w.val < 7) = decide (n2.val < 7) ∧
      hc_adjB iu qu = true ∧ hc_adjB v qu = false ∧
      hc_adjB iv qv = true ∧ hc_adjB t qv = false ∧ hc_adjB iv t = false)
    (hw0 : ru D br w = ∅) (hv2 : (ru D br v).card = 2) (hun : (ru D br u).Nonempty) (ht2 : (ru D br t).card = 2) : False := by
  obtain ⟨hwn2, hiv0, hiw0, hiu0, hdv, hdw, hdu, hivu, hwiv, hn2iv, huv, huqu, hvt, hvqv,
    giv, giw, giu, gvw, gvn2, hswn, gqu, gvqu, gqv, gtqv, gnivt⟩ := hg
  obtain ⟨ew, en2, hew, hen2, hne, hbw, hbn2, hfw, hfn2⟩ :=
    r2_hom2_edges h hD br hbr hpos v iv w iw n2 hiv hiw hv' hw hn2 ⟨hwn2, hiw0, hdw, giv, giw, gvw, gvn2, hswn⟩ hw0
  have hvR : ru D br v = residualUnits 14 D br := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have htR : ru D br t = residualUnits 14 D br := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have hpu_in_v := mem_W_of_pos hpos hiu hiu0 (r2_push h hD br hbr hpos u v iu qu hiu hu ⟨hiu0, hdu, giu, gqu, huv, huqu, gvqu⟩ hun
    ((filter_subset _ _).trans hvR.symm.subset))
  have ht_in_pv := r2_push h hD br hbr hpos v t iv qv hiv hv ⟨hiv0, hdv, giv, gqv, hvt, hvqv, gtqv⟩
    (card_pos.1 (by omega)) (by rw [hvR, htR])
  have hWv_le4 : (sem_W 14 D v).card ≤ 4 := by have := cc_le h hD br hbr v; omega
  have hWv := pa_four (as_mem hpos hiv hiv0 ((hc_adjB_iff _ _).1 giv)) hpu_in_v hew hen2
    (fun e => hivu (hpos.2.2 _ hiv _ hiu e))
    (fun e => hw (hfw _ hiv hiv0 e.symm ▸ hiv)) (fun e => hn2 (hfn2 _ hiv hiv0 e.symm ▸ hiv))
    (fun e => hw (hfw _ hiu hiu0 e.symm ▸ hiu)) (fun e => hn2 (hfn2 _ hiu hiu0 e.symm ▸ hiu))
    hne hWv_le4
  have hfull := full_g14 h hD hB0 hpos hiv hiv0 ((hc_adjB_iff _ _).1 giv) (fun p hp hne1 hsub' => by
    rcases hWv p hp with rfl | rfl | rfl | rfl
    · exact hne1 rfl
    · have hm : iu ∈ supp 14 D (src D (sem_bar (pos iu))) := by
        rw [show src D (sem_bar (pos iu)) = src D ((pos iu).1, !(pos iu).2) from rfl,
          (hpos.1 iu hiu hiu0).2.2.2]; exact mem_singleton_self iu
      exact hivu.symm (mem_singleton.1 (hsub' hm))
    · exact hwiv (mem_singleton.1 (hsub' hbw))
    · exact hn2iv (mem_singleton.1 (hsub' hbn2)))
  exact sem_adjB_false.1 gnivt ((hfull t).1 ht_in_pv)
theorem r2_blow5 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (br : Fin 14 → ℕ) (hbr : PureBranch 14 D br) {pos : Fin 14 → ℕ × Bool} (hpos : k4_Pos14 D pos)
    (hR2 : (residualUnits 14 D br).card = 2)
    (v iv n1 u1 i1 q1 u2 i2 q2 u3 i3 q3 : Fin 14)
    (hiv : iv ∈ ineligSet 14 D) (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D) (hi3 : i3 ∈ ineligSet 14 D)
    (hu1 : u1 ∈ eligSet 14 D) (hu2 : u2 ∈ eligSet 14 D) (hu3 : u3 ∈ eligSet 14 D) (hn1 : n1 ∉ ineligSet 14 D)
    (hg : iv ≠ 0 ∧ i1 ≠ 0 ∧ i2 ≠ 0 ∧ i3 ≠ 0 ∧
      (g14_nbB u1).card = 3 ∧ (g14_nbB u2).card = 3 ∧ (g14_nbB u3).card = 3 ∧
      iv ≠ i1 ∧ iv ≠ i2 ∧ iv ≠ i3 ∧ i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 ∧
      u1 ≠ v ∧ u1 ≠ q1 ∧ u2 ≠ v ∧ u2 ≠ q2 ∧ u3 ≠ v ∧ u3 ≠ q3 ∧
      hc_adjB iv v = true ∧ hc_adjB v n1 = true ∧
      hc_adjB i1 u1 = true ∧ hc_adjB i1 q1 = true ∧ hc_adjB v q1 = false ∧
      hc_adjB i2 u2 = true ∧ hc_adjB i2 q2 = true ∧ hc_adjB v q2 = false ∧
      hc_adjB i3 u3 = true ∧ hc_adjB i3 q3 = true ∧ hc_adjB v q3 = false)
    (hv2 : (ru D br v).card = 2) (h1n : (ru D br u1).Nonempty) (h2n : (ru D br u2).Nonempty) (h3n : (ru D br u3).Nonempty) : False := by
  obtain ⟨h0v, h01, h02, h03, hd1, hd2, hd3, dv1, dv2, dv3, d12, d13, d23, hu1v, hu1q, hu2v, hu2q, hu3v, hu3q,
    giv, gvn1, gi1, gq1, gvq1, gi2, gq2, gvq2, gi3, gq3, gvq3⟩ := hg
  have hvR : ru D br v = residualUnits 14 D br := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have hp1 := mem_W_of_pos hpos hi1 h01 (r2_push h hD br hbr hpos u1 v i1 q1 hi1 hu1 ⟨h01, hd1, gi1, gq1, hu1v, hu1q, gvq1⟩ h1n ((filter_subset _ _).trans hvR.symm.subset))
  have hp2 := mem_W_of_pos hpos hi2 h02 (r2_push h hD br hbr hpos u2 v i2 q2 hi2 hu2 ⟨h02, hd2, gi2, gq2, hu2v, hu2q, gvq2⟩ h2n ((filter_subset _ _).trans hvR.symm.subset))
  have hp3 := mem_W_of_pos hpos hi3 h03 (r2_push h hD br hbr hpos u3 v i3 q3 hi3 hu3 ⟨h03, hd3, gi3, gq3, hu3v, hu3q, gvq3⟩ h3n ((filter_subset _ _).trans hvR.symm.subset))
  obtain ⟨e1, he1, -, hf1, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvn1)
  have h5 := pa_card5 (as_mem hpos hiv h0v ((hc_adjB_iff _ _).1 giv)) hp1 hp2 hp3 he1
    (fun e => dv1 (hpos.2.2 _ hiv _ hi1 e)) (fun e => dv2 (hpos.2.2 _ hiv _ hi2 e))
    (fun e => dv3 (hpos.2.2 _ hiv _ hi3 e)) (fun e => hn1 (hf1 _ hiv h0v e.symm ▸ hiv))
    (fun e => d12 (hpos.2.2 _ hi1 _ hi2 e)) (fun e => d13 (hpos.2.2 _ hi1 _ hi3 e))
    (fun e => hn1 (hf1 _ hi1 h01 e.symm ▸ hi1))
    (fun e => d23 (hpos.2.2 _ hi2 _ hi3 e)) (fun e => hn1 (hf1 _ hi2 h02 e.symm ▸ hi2))
    (fun e => hn1 (hf1 _ hi3 h03 e.symm ▸ hi3))
  have hc := cc_le h hD br hbr v; omega
theorem elim_quad_4 {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (hB0 : Bzero 14 D = 0)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    (iab i1 i2 a b c1 c2 d1 d2 xc1 xc2 xd1 xd2 : Fin 14)
    (hiab : iab ∈ ineligSet 14 D) (hi1 : i1 ∈ ineligSet 14 D) (hi2 : i2 ∈ ineligSet 14 D)
    (ha : a ∉ ineligSet 14 D) (hb : b ∉ ineligSet 14 D)
    (hc1 : c1 ∉ ineligSet 14 D) (hc2 : c2 ∉ ineligSet 14 D)
    (hd1 : d1 ∉ ineligSet 14 D) (hd2 : d2 ∉ ineligSet 14 D)
    (hxc1 : xc1 ∉ ineligSet 14 D) (hxc2 : xc2 ∉ ineligSet 14 D)
    (hxd1 : xd1 ∉ ineligSet 14 D) (hxd2 : xd2 ∉ ineligSet 14 D)
    (hoka : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a ≠ 0 ∧ a ≠ 4 ∧ a ≠ 5))
    (hokb : (0 : Fin 14) ∈ ineligSet 14 D ∨ (b ≠ 0 ∧ b ≠ 4 ∧ b ≠ 5))
    (hokc1 : (0 : Fin 14) ∈ ineligSet 14 D ∨ (c1 ≠ 0 ∧ c1 ≠ 4 ∧ c1 ≠ 5))
    (hokc2 : (0 : Fin 14) ∈ ineligSet 14 D ∨ (c2 ≠ 0 ∧ c2 ≠ 4 ∧ c2 ≠ 5))
    (hokd1 : (0 : Fin 14) ∈ ineligSet 14 D ∨ (d1 ≠ 0 ∧ d1 ≠ 4 ∧ d1 ≠ 5))
    (hokd2 : (0 : Fin 14) ∈ ineligSet 14 D ∨ (d2 ≠ 0 ∧ d2 ≠ 4 ∧ d2 ≠ 5))
    (hg : iab ≠ 0 ∧ i1 ≠ 0 ∧ i2 ≠ 0 ∧ iab ≠ i1 ∧ iab ≠ i2 ∧ i1 ≠ i2 ∧
      a ≠ b ∧ c1 ≠ c2 ∧ d1 ≠ d2 ∧ c1 ≠ d1 ∧ c1 ≠ d2 ∧ c2 ≠ d1 ∧ c2 ≠ d2 ∧
      b ≠ xc1 ∧ b ≠ xd2 ∧ a ≠ xc1 ∧ a ≠ xd1 ∧ b ≠ xd1 ∧
      hc_adjB iab a = true ∧ hc_adjB iab b = true ∧
      hc_adjB a c1 = true ∧ hc_adjB a c2 = true ∧ hc_adjB b d1 = true ∧ hc_adjB b d2 = true ∧
      hc_adjB i1 c1 = true ∧ hc_adjB i2 c2 = true ∧ hc_adjB i1 d1 = true ∧ hc_adjB i2 d2 = true ∧
      hc_adjB c1 xc1 = true ∧ hc_adjB c2 xc2 = true ∧ hc_adjB d1 xd1 = true ∧ hc_adjB d2 xd2 = true ∧
      hc_adjB iab c1 = false ∧ hc_adjB iab c2 = false ∧ hc_adjB iab d1 = false ∧ hc_adjB iab d2 = false ∧
      hc_adjB i1 a = false ∧ hc_adjB i2 a = false ∧ hc_adjB i1 b = false ∧ hc_adjB i2 b = false ∧
      (g14_nbB a).card = 3 ∧ (g14_nbB b).card = 3 ∧
      (g14_nbB c1).card = 3 ∧ (g14_nbB c2).card = 3 ∧
      (g14_nbB d1).card = 3 ∧ (g14_nbB d2).card = 3 ∧
      decide (a.val < 7) = decide (b.val < 7) ∧ decide (a.val < 7) = decide (xc1.val < 7) ∧
      decide (a.val < 7) = decide (xd1.val < 7) ∧ decide (a.val < 7) = decide (xd2.val < 7) ∧
      decide (c1.val < 7) = decide (c2.val < 7) ∧ decide (c1.val < 7) = decide (d1.val < 7) ∧
      decide (c1.val < 7) = decide (d2.val < 7))
    (hr10 : (∃ r : Fin 14, hc_adjB iab r = true ∧ r ≠ b ∧ hc_adjB r c1 = false ∧ hc_adjB r c2 = false) ∨
      (∃ r1 r2 : Fin 14, hc_adjB i1 r1 = true ∧ r1 ≠ c1 ∧ hc_adjB r1 b = false ∧
        hc_adjB i2 r2 = true ∧ r2 ≠ c2 ∧ hc_adjB r2 b = false))
    (hr01 : (∃ r : Fin 14, hc_adjB iab r = true ∧ r ≠ a ∧ hc_adjB r d1 = false ∧ hc_adjB r d2 = false) ∨
      (∃ r1 r2 : Fin 14, hc_adjB i1 r1 = true ∧ r1 ≠ d1 ∧ hc_adjB r1 a = false ∧
        hc_adjB i2 r2 = true ∧ r2 ≠ d2 ∧ hc_adjB r2 a = false)) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨h0ab, h01, h02, hab1, hab2, h12, hab, hc12, hd12, hc1d1, hc1d2, hc2d1, hc2d2,
    hbxc1, hbxd2, haxc1, haxd1, hbxd1,
    giaba, giabb, gac1, gac2, gbd1, gbd2, gi1c1, gi2c2, gi1d1, gi2d2,
    gc1x, gc2x, gd1x, gd2x, gnabc1, gnabc2, gnabd1, gnabd2, gni1a, gni2a, gni1b, gni2b,
    hda, hdb, hdc1, hdc2, hdd1, hdd2, hsab, hsaxc1, hsaxd1, hsaxd2, hsc12, hsc1d1, hsc1d2⟩ := hg
  have h10_kill : ∀ (u v u1 u2 v1 xv1 : Fin 14),
      u ∉ ineligSet 14 D → v ∉ ineligSet 14 D → u1 ∉ ineligSet 14 D → u2 ∉ ineligSet 14 D →
      v1 ∉ ineligSet 14 D → xv1 ∉ ineligSet 14 D →
      ((0 : Fin 14) ∈ ineligSet 14 D ∨ (u ≠ 0 ∧ u ≠ 4 ∧ u ≠ 5)) →
      ((0 : Fin 14) ∈ ineligSet 14 D ∨ (u1 ≠ 0 ∧ u1 ≠ 4 ∧ u1 ≠ 5)) →
      ((0 : Fin 14) ∈ ineligSet 14 D ∨ (u2 ≠ 0 ∧ u2 ≠ 4 ∧ u2 ≠ 5)) →
      ((0 : Fin 14) ∈ ineligSet 14 D ∨ (v1 ≠ 0 ∧ v1 ≠ 4 ∧ v1 ≠ 5)) →
      (u1 ≠ u2 ∧ v ≠ xv1 ∧ u1 ≠ v ∧ u2 ≠ v ∧
        hc_adjB iab u = true ∧ hc_adjB iab v = true ∧
        hc_adjB u u1 = true ∧ hc_adjB u u2 = true ∧ hc_adjB v v1 = true ∧
        hc_adjB i1 u1 = true ∧ hc_adjB i2 u2 = true ∧ hc_adjB i1 v1 = true ∧ hc_adjB v1 xv1 = true ∧
        hc_adjB iab u1 = false ∧ hc_adjB iab u2 = false ∧ hc_adjB iab v1 = false ∧
        hc_adjB i1 u = false ∧ hc_adjB i2 u = false ∧
        (g14_nbB v).card = 3 ∧ (g14_nbB u1).card = 3 ∧ (g14_nbB u2).card = 3 ∧
        decide (xv1.val < 7) = decide (v.val < 7) ∧ decide (u1.val < 7) = decide (u2.val < 7)) →
      ((∃ r : Fin 14, hc_adjB iab r = true ∧ r ≠ v ∧ hc_adjB r u1 = false ∧ hc_adjB r u2 = false) ∨
        (∃ r1 r2 : Fin 14, hc_adjB i1 r1 = true ∧ r1 ≠ u1 ∧ hc_adjB r1 v = false ∧
          hc_adjB i2 r2 = true ∧ r2 ≠ u2 ∧ hc_adjB r2 v = false)) →
      3 ≤ (sem_W 14 D u).card → (sem_W 14 D v).card ≤ 2 → False := by
    intro u v u1 u2 v1 xv1 hu hv hu1 hu2 hv1 hxv1 hoku hoku1 hoku2 hokv1 hgu hru hu3 hvle2
    obtain ⟨hu12, hvxv1, hu1v, hu2v, giu, giv, guu1, guu2, gvv1, gi1u1, gi2u2, gi1v1, gv1x,
      gnabu1, gnabu2, gnabv1, gni1u, gni2u, hdv, hdu1, hdu2, hsxv, hsu12⟩ := hgu
    have hu1le2 : (sem_W 14 D u1).card ≤ 2 := by
      by_contra hc; exact hnot33_pair h hD hB0 ⟨hpos, hc3, hPQ, hsat⟩ u u1 iab i1 hiab hi1 hu hu1 hoku hoku1
        ⟨h0ab, h01, hab1, giu, gi1u1, guu1, gnabu1, gni1u⟩ hu3 (by omega)
    have hu2le2 : (sem_W 14 D u2).card ≤ 2 := by
      by_contra hc; exact hnot33_pair h hD hB0 ⟨hpos, hc3, hPQ, hsat⟩ u u2 iab i2 hiab hi2 hu hu2 hoku hoku2
        ⟨h0ab, h02, hab2, giu, gi2u2, guu2, gnabu2, gni2u⟩ hu3 (by omega)
    have hv1_3 : 3 ≤ (sem_W 14 D v1).card := by
      by_contra hc; exact pa_m1 h hD hpos v1 v xv1 i1 iab hi1 hiab hv1 hv hxv1
        ⟨gi1v1, giv, (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gvv1)), gv1x, hvxv1.symm, hdv, hsxv, h01, h0ab⟩
        (by omega) hvle2
    have hfull_ab := full_of_le2 h hD hB0 hpos hiab h0ab hv1 ((hc_adjB_iff _ _).1 giv) ((hc_adjB_iff _ _).1 gvv1) hdv hvle2
    obtain ⟨Du1, hDu1ne, hWu1, hpu1⟩ := ps_side h hD hpos hi1 h01 ((hc_adjB_iff _ _).1 gi1u1) hdu1 hu1le2
    obtain ⟨Du2, hDu2ne, hWu2, -⟩ := ps_side h hD hpos hi2 h02 ((hc_adjB_iff _ _).1 gi2u2) hdu2 hu2le2
    obtain ⟨Dv, hDvne, hWv, -⟩ := ps_side h hD hpos hiab h0ab ((hc_adjB_iff _ _).1 giv) hdv hvle2
    obtain ⟨fu1, hfu1, hbfu1, hfu1y, hfu1x⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 guu1)
    obtain ⟨fu2, hfu2, hbfu2, hfu2y, hfu2x⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 guu2)
    have hbu1 : sem_bar fu1 = Du1 := by
      rw [hWu1, mem_insert, mem_singleton] at hbfu1
      exact hbfu1.resolve_left (fun hh => hu (hfu1x i1 hi1 h01 hh ▸ hi1))
    have hbu2 : sem_bar fu2 = Du2 := by
      rw [hWu2, mem_insert, mem_singleton] at hbfu2
      exact hbfu2.resolve_left (fun hh => hu (hfu2x i2 hi2 h02 hh ▸ hi2))
    have hfu12 : fu1 ≠ fu2 := fun hh => hpu1 u2 hu12.symm hsu12.symm (hbu1 ▸ hh ▸ hbfu2)
    have hoku' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (u ≠ 4 ∧ u ≠ 5) := hoku.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
    have hokv1' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (v1 ≠ 4 ∧ v1 ≠ 5) := hokv1.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
    have hWu := pa_three (as_mem hpos hiab h0ab ((hc_adjB_iff _ _).1 giu)) hfu1 hfu2
      (fun hh => hu1 (hfu1y iab hiab h0ab hh.symm ▸ hiab))
      (fun hh => hu2 (hfu2y iab hiab h0ab hh.symm ▸ hiab)) hfu12 (hc3 u hoku')
    have hnotab_v1 : pos iab ∉ sem_W 14 D v1 := fun hm =>
      sem_adjB_false.1 gnabv1 ((hfull_ab v1).1 (sem_mem_W.1 hm).2.1)
    have hPQ_in : ∀ e, e = P ∨ e = Q → e = fu1 ∨ e = fu2 := by
      intro e he
      have h1 : e ∈ sem_W 14 D u := he.elim (fun h1 => h1 ▸ (hsat u hoku hu3).1) (fun h1 => h1 ▸ (hsat u hoku hu3).2)
      have h2 : e ∈ sem_W 14 D v1 := he.elim (fun h1 => h1 ▸ (hsat v1 hokv1 hv1_3).1) (fun h1 => h1 ▸ (hsat v1 hokv1 hv1_3).2)
      rcases hWu e h1 with rfl | rfl | rfl
      · exact absurd h2 hnotab_v1
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hfu1_v1 : fu1 ∈ sem_W 14 D v1 := by
      rcases hPQ_in P (Or.inl rfl) with h1 | h1 <;> rcases hPQ_in Q (Or.inr rfl) with h2 | h2
      · exact absurd (h1.trans h2.symm) hPQ
      · exact h1 ▸ (hsat v1 hokv1 hv1_3).1
      · exact h2 ▸ (hsat v1 hokv1 hv1_3).2
      · exact absurd (h1.trans h2.symm) hPQ
    have hfu2_v1 : fu2 ∈ sem_W 14 D v1 := by
      rcases hPQ_in P (Or.inl rfl) with h1 | h1 <;> rcases hPQ_in Q (Or.inr rfl) with h2 | h2
      · exact absurd (h1.trans h2.symm) hPQ
      · exact h2 ▸ (hsat v1 hokv1 hv1_3).2
      · exact h1 ▸ (hsat v1 hokv1 hv1_3).1
      · exact absurd (h1.trans h2.symm) hPQ
    have hWv1 := pa_three (as_mem hpos hi1 h01 ((hc_adjB_iff _ _).1 gi1v1)) hfu1_v1 hfu2_v1
      (fun hh => hu1 (hfu1y i1 hi1 h01 hh.symm ▸ hi1))
      (fun hh => hu2 (hfu2y i1 hi1 h01 hh.symm ▸ hi1)) hfu12 (hc3 v1 hokv1')
    obtain ⟨fv, hfv, hbfv, hfvy, hfvx⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 gvv1))
    have hbv : sem_bar fv = Dv := by
      rw [hWv, mem_insert, mem_singleton] at hbfv
      exact hbfv.resolve_left (fun hh => hv1 (hfvx iab hiab h0ab hh ▸ hiab))
    rcases hWv1 fv hfv with hh | hh | hh
    · exact hv (hfvy i1 hi1 h01 hh ▸ hi1)
    · have hDeq : Dv = Du1 := hbv.symm.trans (hh ▸ hbu1)
      rcases hru with ⟨r, gir, hrv, hru1, -⟩ | ⟨r1, -, gir1, hr1u1, hr1v, -, -, -⟩
      · obtain ⟨Dv', hDv'ne, hWv', hna⟩ := ps_nonadj h hD hpos hiab h0ab ((hc_adjB_iff _ _).1 giv)
          ((hc_adjB_iff _ _).1 gir) hrv hdv hvle2
        have hDv'eq : Dv' = Dv := by
          have hm : Dv' ∈ ({pos iab, Dv} : Finset (ℕ × Bool)) := by rw [← hWv, hWv']; simp
          simp only [mem_insert, mem_singleton] at hm
          exact hm.resolve_left hDv'ne
        exact hna u1 hu1v (sem_adjB_false.1 hru1) (hDv'eq ▸ hDeq ▸ (by rw [hWu1]; simp))
      · obtain ⟨Du1', hDu1'ne, hWu1', hna⟩ := ps_nonadj h hD hpos hi1 h01 ((hc_adjB_iff _ _).1 gi1u1)
          ((hc_adjB_iff _ _).1 gir1) hr1u1 hdu1 hu1le2
        have hDu1'eq : Du1' = Du1 := by
          have hm : Du1' ∈ ({pos i1, Du1} : Finset (ℕ × Bool)) := by rw [← hWu1, hWu1']; simp
          simp only [mem_insert, mem_singleton] at hm
          exact hm.resolve_left hDu1'ne
        exact hna v hu1v.symm (sem_adjB_false.1 hr1v) (hDu1'eq ▸ hDeq ▸ (by rw [hWv]; simp))
    · have hDeq : Dv = Du2 := hbv.symm.trans (hh ▸ hbu2)
      rcases hru with ⟨r, gir, hrv, -, hru2⟩ | ⟨-, r2, -, -, -, gir2, hr2u2, hr2v⟩
      · obtain ⟨Dv', hDv'ne, hWv', hna⟩ := ps_nonadj h hD hpos hiab h0ab ((hc_adjB_iff _ _).1 giv)
          ((hc_adjB_iff _ _).1 gir) hrv hdv hvle2
        have hDv'eq : Dv' = Dv := by
          have hm : Dv' ∈ ({pos iab, Dv} : Finset (ℕ × Bool)) := by rw [← hWv, hWv']; simp
          simp only [mem_insert, mem_singleton] at hm
          exact hm.resolve_left hDv'ne
        exact hna u2 hu2v (sem_adjB_false.1 hru2) (hDv'eq ▸ hDeq ▸ (by rw [hWu2]; simp))
      · obtain ⟨Du2', hDu2'ne, hWu2', hna⟩ := ps_nonadj h hD hpos hi2 h02 ((hc_adjB_iff _ _).1 gi2u2)
          ((hc_adjB_iff _ _).1 gir2) hr2u2 hdu2 hu2le2
        have hDu2'eq : Du2' = Du2 := by
          have hm : Du2' ∈ ({pos i2, Du2} : Finset (ℕ × Bool)) := by rw [← hWu2, hWu2']; simp
          simp only [mem_insert, mem_singleton] at hm
          exact hm.resolve_left hDu2'ne
        exact hna v hu2v.symm (sem_adjB_false.1 hr2v) (hDu2'eq ▸ hDeq ▸ (by rw [hWv]; simp))
  by_cases ha3 : 3 ≤ (sem_W 14 D a).card
  · by_cases hb3 : 3 ≤ (sem_W 14 D b).card
    · have hc1l : (sem_W 14 D c1).card ≤ 2 := by
        by_contra hc; exact hnot33_pair h hD hB0 ⟨hpos, hc3, hPQ, hsat⟩ a c1 iab i1 hiab hi1 ha hc1 hoka hokc1
          ⟨h0ab, h01, hab1, giaba, gi1c1, gac1, gnabc1, gni1a⟩ ha3 (by omega)
      have hc2l : (sem_W 14 D c2).card ≤ 2 := by
        by_contra hc; exact hnot33_pair h hD hB0 ⟨hpos, hc3, hPQ, hsat⟩ a c2 iab i2 hiab hi2 ha hc2 hoka hokc2
          ⟨h0ab, h02, hab2, giaba, gi2c2, gac2, gnabc2, gni2a⟩ ha3 (by omega)
      have hd1l : (sem_W 14 D d1).card ≤ 2 := by
        by_contra hc; exact hnot33_pair h hD hB0 ⟨hpos, hc3, hPQ, hsat⟩ b d1 iab i1 hiab hi1 hb hd1 hokb hokd1
          ⟨h0ab, h01, hab1, giabb, gi1d1, gbd1, gnabd1, gni1b⟩ hb3 (by omega)
      have hd2l : (sem_W 14 D d2).card ≤ 2 := by
        by_contra hc; exact hnot33_pair h hD hB0 ⟨hpos, hc3, hPQ, hsat⟩ b d2 iab i2 hiab hi2 hb hd2 hokb hokd2
          ⟨h0ab, h02, hab2, giabb, gi2d2, gbd2, gnabd2, gni2b⟩ hb3 (by omega)
      have hoka' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (a ≠ 4 ∧ a ≠ 5) := hoka.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
      have hokb' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (b ≠ 4 ∧ b ≠ 5) := hokb.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
      exact elim_disj_ps_pair h hD hpos hPQ a b iab iab c1 c2 d1 d2 i1 i2 i1 i2
        hiab hiab hi1 hi2 hi1 hi2 ha hb hc1 hc2 hd1 hd2
        ⟨h0ab, h0ab, h01, h02, h01, h02, hc12, hc1d1, hc1d2, hc2d1, hc2d2, hd12,
          giaba, giabb, gac1, gac2, gbd1, gbd2, gi1c1, gi2c2, gi1d1, gi2d2,
          hdc1, hdc2, hdd1, hdd2, hsc12, hsc1d1, hsc1d2⟩
        (hc3 a hoka') (hc3 b hokb') hc1l hc2l hd1l hd2l
        (hsat a hoka ha3).1 (hsat a hoka ha3).2 (hsat b hokb hb3).1 (hsat b hokb hb3).2
    · have hc1b : c1 ≠ b := fun hh => by rw [hh] at gnabc1; rw [giabb] at gnabc1; exact Bool.noConfusion gnabc1
      have hc2b : c2 ≠ b := fun hh => by rw [hh] at gnabc2; rw [giabb] at gnabc2; exact Bool.noConfusion gnabc2
      exact h10_kill a b c1 c2 d1 xd1 ha hb hc1 hc2 hd1 hxd1 hoka hokc1 hokc2 hokd1
        ⟨hc12, hbxd1, hc1b, hc2b, giaba, giabb, gac1, gac2, gbd1, gi1c1, gi2c2, gi1d1, gd1x,
          gnabc1, gnabc2, gnabd1, gni1a, gni2a, hdb, hdc1, hdc2, hsaxd1.symm.trans hsab, hsc12⟩
        hr10 ha3 (by omega)
  · by_cases hb3 : 3 ≤ (sem_W 14 D b).card
    · have hd1a : d1 ≠ a := fun hh => by rw [hh] at gnabd1; rw [giaba] at gnabd1; exact Bool.noConfusion gnabd1
      have hd2a : d2 ≠ a := fun hh => by rw [hh] at gnabd2; rw [giaba] at gnabd2; exact Bool.noConfusion gnabd2
      exact h10_kill b a d1 d2 c1 xc1 hb ha hd1 hd2 hc1 hxc1 hokb hokd1 hokd2 hokc1
        ⟨hd12, haxc1, hd1a, hd2a, giabb, giaba, gbd1, gbd2, gac1, gi1d1, gi2d2, gi1c1, gc1x,
          gnabd1, gnabd2, gnabc1, gni1b, gni2b, hda, hdd1, hdd2, hsaxc1.symm, hsc1d1.symm.trans hsc1d2⟩
        hr01 hb3 (by omega)
    · have hale2 : (sem_W 14 D a).card ≤ 2 := by omega
      have hble2 : (sem_W 14 D b).card ≤ 2 := by omega
      have hc1_3 : 3 ≤ (sem_W 14 D c1).card := by
        by_contra hc; exact pa_m1 h hD hpos c1 a xc1 i1 iab hi1 hiab hc1 ha hxc1
          ⟨gi1c1, giaba, (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gac1)), gc1x, haxc1.symm, hda, hsaxc1.symm, h01, h0ab⟩
          (by omega) hale2
      have hd2_3 : 3 ≤ (sem_W 14 D d2).card := by
        by_contra hc; exact pa_m1 h hD hpos d2 b xd2 i2 iab hi2 hiab hd2 hb hxd2
          ⟨gi2d2, giabb, (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gbd2)), gd2x, hbxd2.symm, hdb, hsaxd2.symm.trans hsab, h02, h0ab⟩
          (by omega) hble2
      obtain ⟨Da, -, hWa, hpa⟩ := ps_side h hD hpos hiab h0ab ((hc_adjB_iff _ _).1 giaba) hda hale2
      obtain ⟨Db, -, hWb, hpb⟩ := ps_side h hD hpos hiab h0ab ((hc_adjB_iff _ _).1 giabb) hdb hble2
      obtain ⟨fc1a, hfc1a, hbfc1a, hfc1ay, hfc1ax⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 gac1))
      obtain ⟨fc1x, hfc1x, hbfc1x, hfc1xy, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gc1x)
      obtain ⟨fd2b, hfd2b, hbfd2b, hfd2by, hfd2bx⟩ := pa_ed h hD hpos (adj_symm ((hc_adjB_iff _ _).1 gbd2))
      obtain ⟨fd2x, hfd2x, hbfd2x, hfd2xy, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gd2x)
      have hba : sem_bar fc1a = Da := by
        rw [hWa, mem_insert, mem_singleton] at hbfc1a
        exact hbfc1a.resolve_left (fun hh => hc1 (hfc1ax iab hiab h0ab hh ▸ hiab))
      have hbb : sem_bar fd2b = Db := by
        rw [hWb, mem_insert, mem_singleton] at hbfd2b
        exact hbfd2b.resolve_left (fun hh => hd2 (hfd2bx iab hiab h0ab hh ▸ hiab))
      have hokc1' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (c1 ≠ 4 ∧ c1 ≠ 5) := hokc1.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
      have hokd2' : (0 : Fin 14) ∈ ineligSet 14 D ∨ (d2 ≠ 4 ∧ d2 ≠ 5) := hokd2.elim Or.inl (fun h' => Or.inr ⟨h'.2.1, h'.2.2⟩)
      have hWc1 := pa_three (as_mem hpos hi1 h01 ((hc_adjB_iff _ _).1 gi1c1)) hfc1a hfc1x
        (fun hh => ha (hfc1ay i1 hi1 h01 hh.symm ▸ hi1))
        (fun hh => hxc1 (hfc1xy i1 hi1 h01 hh.symm ▸ hi1))
        (fun hh => hpa xc1 haxc1.symm hsaxc1.symm (hba ▸ hh ▸ hbfc1x)) (hc3 c1 hokc1')
      have hWd2 := pa_three (as_mem hpos hi2 h02 ((hc_adjB_iff _ _).1 gi2d2)) hfd2b hfd2x
        (fun hh => hb (hfd2by i2 hi2 h02 hh.symm ▸ hi2))
        (fun hh => hxd2 (hfd2xy i2 hi2 h02 hh.symm ▸ hi2))
        (fun hh => hpb xd2 hbxd2.symm (hsaxd2.symm.trans hsab) (hbb ▸ hh ▸ hbfd2x)) (hc3 d2 hokd2')
      have honly : ∀ e, e ∈ sem_W 14 D d2 → e ∈ sem_W 14 D c1 → e = fd2x := by
        intro e he1 he2
        rcases hWd2 e he1 with rfl | rfl | rfl
        · rcases hWc1 _ he2 with hh | hh | hh
          · exact absurd (hpos.2.2 _ hi2 _ hi1 hh) h12.symm
          · exact absurd (hfc1ay i2 hi2 h02 hh.symm ▸ hi2) ha
          · exact absurd (hfc1xy i2 hi2 h02 hh.symm ▸ hi2) hxc1
        · rcases hWc1 _ he2 with hh | hh | hh
          · exact absurd (hfd2by i1 hi1 h01 hh ▸ hi1) hb
          · exact absurd (hbb ▸ hh ▸ hbfc1a) (hpb a hab hsab)
          · exact absurd (hbb ▸ hh ▸ hbfc1x) (hpb xc1 hbxc1.symm (hsaxc1.symm.trans hsab))
        · rfl
      exact hPQ ((honly P (hsat d2 hokd2 hd2_3).1 (hsat c1 hokc1 hc1_3).1).trans
        (honly Q (hsat d2 hokd2 hd2_3).2 (hsat c1 hokc1 hc1_3).2).symm)
theorem elim_49 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨49, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,1,3,8} := by rw [hI]; decide +kernel
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := mI hIeq
  obtain ⟨hB0, pos, P, Q, hctx⟩ := res1_setup_c4 h hD h11 ⟨49, by decide⟩ hI (by rw [hIeq]; decide)
  exact elim_quad_4 h hD hB0 hctx 8 3 1 2 6 12 13 11 9 5 4 4 5 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (by decide) (Or.inr ⟨7, 7, by decide⟩) (Or.inr ⟨7, 7, by decide⟩)
theorem elim_79 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨79, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {1,3,8,10} := by rw [hI]; decide +kernel
  obtain ⟨hB0, pos, P, Q, hctx⟩ := res1_setup_c4 h hD h11 ⟨79, by decide⟩ hI (by rw [hIeq]; decide)
  exact elim_quad_4 h hD hB0 hctx 8 3 1 2 6 12 13 11 9 5 4 4 5 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) (by decide) (Or.inr ⟨7, 7, by decide⟩) (Or.inr ⟨7, 7, by decide⟩)
theorem elim_50 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨50, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,1,3,10} := by rw [hI]; decide +kernel
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := mI hIeq
  obtain ⟨hB0, pos, P, Q, hctx⟩ := res1_setup_c4 h hD h11 ⟨50, by decide⟩ hI (by rw [hIeq]; decide)
  exact elim_quad_4 h hD hB0 hctx 10 3 1 4 5 11 13 12 9 6 2 2 6 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (by decide) (Or.inr ⟨7, 7, by decide⟩) (Or.inr ⟨7, 7, by decide⟩)
theorem elim_54 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨54, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,1,8,10} := by rw [hI]; decide +kernel
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := mI hIeq
  obtain ⟨hB0, pos, P, Q, hctx⟩ := res1_setup_c4 h hD h11 ⟨54, by decide⟩ hI (by rw [hIeq]; decide)
  exact elim_quad_4 h hD hB0 hctx 1 8 10 9 13 6 5 2 4 11 12 12 11 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (by decide) (Or.inl ⟨7, by decide⟩) (Or.inl ⟨7, by decide⟩)
theorem elim_59 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨59, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,4,7,8} := by rw [hI]; decide +kernel
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := mI hIeq
  obtain ⟨hB0, pos, P, Q, hctx⟩ := res1_setup_c4 h hD h11 ⟨59, by decide⟩ hI (by rw [hIeq]; decide)
  exact elim_quad_4 h hD hB0 hctx 4 7 8 11 13 3 6 1 2 12 9 9 12 (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (Or.inl h0I) (by decide) (Or.inl ⟨10, by decide⟩) (Or.inl ⟨10, by decide⟩)
theorem elim_82 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨82, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {1, 8, 10, 11} := by rw [hI]; decide +kernel
  obtain ⟨hB0, pos, P, Q, hpos, hc3, hPQ, hsat⟩ := res1_setup_c4 h hD h11 ⟨82, by decide⟩ hI (by rw [hIeq]; decide)
  have h1I : (1 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h8I : (8 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h11I : (11 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h6_3 := two_in_deg3 (u := 6) h hD hpos h8I h11I (nI hIeq : (9 : Fin 14) ∉ ineligSet 14 D) (by decide)
  obtain ⟨hfull8, hfull11⟩ := full_of_two_in_deg3 (u := 6) h hD hB0 hpos h8I h11I
    (nI hIeq : (9 : Fin 14) ∉ ineligSet 14 D) (by decide) (hc3 6 (Or.inr (by decide)))
  have h9le2 : (sem_W 14 D 9).card ≤ 2 := by
    by_contra hc; exact hnot33_pair h hD hB0 ⟨hpos, hc3, hPQ, hsat⟩ 6 9 8 1 h8I h1I
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (Or.inr (by decide)) (Or.inr (by decide))
      (by decide) h6_3 (by omega)
  obtain ⟨D9, -, hW9, hp9⟩ := ps_side h hD hpos h1I (by decide) (by decide : Adj 1 9) (by decide) h9le2
  obtain ⟨f69, hf69, hbf69, hf69y, hf69x⟩ := pa_ed h hD hpos (by decide : Adj 6 9)
  have hb69 : sem_bar f69 = D9 := by
    rw [hW9, mem_insert, mem_singleton] at hbf69
    exact hbf69.resolve_left (fun hh => (by rw [hIeq]; decide : (6 : Fin 14) ∉ _) (hf69x 1 h1I (by decide) hh ▸ h1I))
  have hW6 := pa_three (as_mem hpos h8I (by decide) (by decide : Adj 8 6))
    (as_mem hpos h11I (by decide) (by decide : Adj 11 6)) hf69
    (fun hh => (by decide : (8 : Fin 14) ≠ 11) (hpos.2.2 _ h8I _ h11I hh))
    (fun hh => (by rw [hIeq]; decide : (9 : Fin 14) ∉ _) (hf69y 8 h8I (by decide) hh.symm ▸ h8I))
    (fun hh => (by rw [hIeq]; decide : (9 : Fin 14) ∉ _) (hf69y 11 h11I (by decide) hh.symm ▸ h11I))
    (hc3 6 (Or.inr (by decide)))
  by_cases h2_3 : 3 ≤ (sem_W 14 D 2).card
  · have h13le2 : (sem_W 14 D 13).card ≤ 2 := by
      by_contra hc; exact hnot33_pair h hD hB0 ⟨hpos, hc3, hPQ, hsat⟩ 2 13 8 1 h8I h1I
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (Or.inr (by decide)) (Or.inr (by decide))
        (by decide) h2_3 (by omega)
    obtain ⟨D13, -, hW13, hp13⟩ := ps_side h hD hpos h1I (by decide) (by decide : Adj 1 13) (by decide) h13le2
    obtain ⟨f2_13, hf2_13, hbf2_13, hf2_13y, hf2_13x⟩ := pa_ed h hD hpos (by decide : Adj 2 13)
    obtain ⟨f2_12, hf2_12, hbf2_12, hf2_12y, -⟩ := pa_ed h hD hpos (by decide : Adj 2 12)
    have hb2_13 : sem_bar f2_13 = D13 := by
      rw [hW13, mem_insert, mem_singleton] at hbf2_13
      exact hbf2_13.resolve_left (fun hh => (by rw [hIeq]; decide : (2 : Fin 14) ∉ _) (hf2_13x 1 h1I (by decide) hh ▸ h1I))
    have hW2 := pa_three (as_mem hpos h8I (by decide) (by decide : Adj 8 2)) hf2_13 hf2_12
      (fun hh => (by rw [hIeq]; decide : (13 : Fin 14) ∉ _) (hf2_13y 8 h8I (by decide) hh.symm ▸ h8I))
      (fun hh => (by rw [hIeq]; decide : (12 : Fin 14) ∉ _) (hf2_12y 8 h8I (by decide) hh.symm ▸ h8I))
      (fun hh => hp13 12 (by decide) (by decide) (hb2_13 ▸ hh ▸ hbf2_12)) (hc3 2 (Or.inr (by decide)))
    have honly : ∀ e, e ∈ sem_W 14 D 6 → e ∈ sem_W 14 D 2 → e = pos 8 := by
      intro e he1 he2
      rcases hW6 e he1 with rfl | rfl | rfl
      · rfl
      · exact absurd ((hfull11 2).1 (sem_mem_W.1 he2).2.1) (by decide)
      · rcases hW2 _ he2 with hh | hh | hh
        · exact absurd (hf69y 8 h8I (by decide) hh ▸ h8I) (by rw [hIeq]; decide)
        · exact absurd (hb69 ▸ hh ▸ hbf2_13) (hp9 13 (by decide) (by decide))
        · exact absurd (hb69 ▸ hh ▸ hbf2_12) (hp9 12 (by decide) (by decide))
    exact hPQ ((honly P (hsat 6 (Or.inr (by decide)) h6_3).1 (hsat 2 (Or.inr (by decide)) h2_3).1).trans
      (honly Q (hsat 6 (Or.inr (by decide)) h6_3).2 (hsat 2 (Or.inr (by decide)) h2_3).2).symm)
  · have h13_3 : 3 ≤ (sem_W 14 D 13).card := by
      by_contra hc; exact pa_m1 h hD hpos 13 2 4 1 8 h1I h8I
        (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) (by omega) (by omega)
    have honly : ∀ e, e ∈ sem_W 14 D 6 → e ∈ sem_W 14 D 13 → e = f69 := by
      intro e he1 he2
      rcases hW6 e he1 with rfl | rfl | rfl
      · exact absurd ((hfull8 13).1 (sem_mem_W.1 he2).2.1) (by decide)
      · exact absurd ((hfull11 13).1 (sem_mem_W.1 he2).2.1) (by decide)
      · rfl
    exact hPQ ((honly P (hsat 6 (Or.inr (by decide)) h6_3).1 (hsat 13 (Or.inr (by decide)) h13_3).1).trans
      (honly Q (hsat 6 (Or.inr (by decide)) h6_3).2 (hsat 13 (Or.inr (by decide)) h13_3).2).symm)
theorem elim_63_only_m : ∀ m : Fin 128,
    let I : Finset (Fin 14) := {0, 7, 8, 10}
    let P := sideL \ I
    let Oc := maskFin7 m
    let Oc3 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 3)
    let Oc2 := Oc.filter (fun k => (g14_nbB (os_ptR k) ∩ P).card = 2)
    let Ct := (Finset.univ : Finset (Fin 7)) \ Oc
    let Iin := Finset.univ.filter (fun k : Fin 7 => os_ptR k ∈ I ∧ okL_pred I P k)
    let Lab := Ct.biUnion (fun k => g14_nbB (os_ptR k) ∩ P)
    (∀ k ∈ Oc, okL_pred I P k) →
    2 * Oc3.card + Oc2.card + Iin.card + Lab.card ≤ 13 →
    (Iin \ Oc).card = 0 →
    Oc = ({0, 1, 3} : Finset (Fin 7)) := by
  decide +kernel
theorem elim_63_S_ge3 : ∀ m : Fin 64,
    let L6 : Finset (Fin 14) := {1, 2, 3, 4, 5, 6}
    let S := L6.filter (fun x => Nat.testBit m.val (x.val - 1))
    let bad := ({9, 11, 12, 13} : Finset (Fin 14)).filter (fun c => 2 ≤ (g14_nbB c \ S).card)
    bad.card ≤ 1 → 3 ≤ S.card := by
  decide +kernel
theorem elim_3star_pair_sound {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (c1 c2 a1 b1 d1 a2 b2 d2 ia1 ib1 id1 ia2 ib2 : Fin 14)
    (hia1 : ia1 ∈ ineligSet 14 D) (hib1 : ib1 ∈ ineligSet 14 D) (hid1 : id1 ∈ ineligSet 14 D)
    (hia2 : ia2 ∈ ineligSet 14 D) (hib2 : ib2 ∈ ineligSet 14 D)
    (hc1 : c1 ∉ ineligSet 14 D) (hc2 : c2 ∉ ineligSet 14 D)
    (hg : ia1 ≠ 0 ∧ ib1 ≠ 0 ∧ id1 ≠ 0 ∧ ia2 ≠ 0 ∧ ib2 ≠ 0 ∧
      a1 ≠ b1 ∧ a1 ≠ d1 ∧ b1 ≠ d1 ∧ a2 ≠ b2 ∧ a2 ≠ d2 ∧ b2 ≠ d2 ∧
      hc_adjB c1 a1 = true ∧ hc_adjB c1 b1 = true ∧ hc_adjB c1 d1 = true ∧
      hc_adjB c2 a2 = true ∧ hc_adjB c2 b2 = true ∧ hc_adjB c2 d2 = true ∧
      hc_adjB ia1 a1 = true ∧ hc_adjB ib1 b1 = true ∧ hc_adjB id1 d1 = true ∧
      hc_adjB ia2 a2 = true ∧ hc_adjB ib2 b2 = true ∧
      (g14_nbB a1).card = 3 ∧ (g14_nbB b1).card = 3 ∧ (g14_nbB d1).card = 3 ∧
      (g14_nbB a2).card = 3 ∧ (g14_nbB b2).card = 3 ∧
      a1.val < 7 ∧ b1.val < 7 ∧ d1.val < 7 ∧ a2.val < 7 ∧ b2.val < 7 ∧ d2.val < 7 ∧
      ((a1 ≠ a2 ∧ a1 ≠ b2 ∧ a1 ≠ d2) ∨ (b1 ≠ a2 ∧ b1 ≠ b2 ∧ b1 ≠ d2)) ∧
      ((a1 ≠ a2 ∧ a1 ≠ b2 ∧ a1 ≠ d2 ∧ b1 ≠ a2 ∧ b1 ≠ b2 ∧ b1 ≠ d2) ∨
       (a1 ≠ a2 ∧ a1 ≠ b2 ∧ a1 ≠ d2 ∧ d1 ≠ a2 ∧ d1 ≠ b2 ∧ d1 ≠ d2) ∨
       (b1 ≠ a2 ∧ b1 ≠ b2 ∧ b1 ≠ d2 ∧ d1 ≠ a2 ∧ d1 ≠ b2 ∧ d1 ≠ d2)))
    (ha1 : (sem_W 14 D a1).card ≤ 2) (hb1 : (sem_W 14 D b1).card ≤ 2)
    (ha2 : (sem_W 14 D a2).card ≤ 2) (hb2 : (sem_W 14 D b2).card ≤ 2) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨h0a1, h0b1, h0d1, h0a2, h0b2, hab1, had1, hbd1, hab2, had2, hbd2,
    gc1a, gc1b, gc1d, gc2a, gc2b, gc2d, gia1, gib1, gid1, gia2, gib2,
    hda1, hdb1, hdd1, hda2, hdb2, la1, lb1, ld1, la2, lb2, ld2, hor1, hor2⟩ := hg
  have hs : ∀ x y : Fin 14, x.val < 7 → y.val < 7 → decide (x.val < 7) = decide (y.val < 7) :=
    fun x y hx hy => by simp [hx, hy]
  have hc1_3 := ps_side_3star h hD hpos c1 a1 b1 d1 ia1 ib1 hia1 hib1 hc1
    ⟨gc1a, gc1b, gc1d, gia1, gib1, hab1, had1, hbd1, hda1, hdb1, hs b1 a1 lb1 la1, hs d1 a1 ld1 la1, h0a1, h0b1⟩ ha1 hb1
  have hc2_3 := ps_side_3star h hD hpos c2 a2 b2 d2 ia2 ib2 hia2 hib2 hc2
    ⟨gc2a, gc2b, gc2d, gia2, gib2, hab2, had2, hbd2, hda2, hdb2, hs b2 a2 lb2 la2, hs d2 a2 ld2 la2, h0a2, h0b2⟩ ha2 hb2
  rw [hc_adjB_iff] at gc1a gc1b gc1d gc2a gc2b gc2d gia1 gib1 gid1 gia2 gib2
  obtain ⟨Da1, -, hWa1, hpa1⟩ := ps_side h hD hpos hia1 h0a1 gia1 hda1 ha1
  obtain ⟨Db1, -, hWb1, hpb1⟩ := ps_side h hD hpos hib1 h0b1 gib1 hdb1 hb1
  obtain ⟨Da2, -, hWa2, hpa2⟩ := ps_side h hD hpos hia2 h0a2 gia2 hda2 ha2
  obtain ⟨Db2, -, hWb2, -⟩ := ps_side h hD hpos hib2 h0b2 gib2 hdb2 hb2
  obtain ⟨fa1, hfa1, hbfa1, -, hfa1x⟩ := pa_ed h hD hpos gc1a
  obtain ⟨fb1, hfb1, hbfb1, -, hfb1x⟩ := pa_ed h hD hpos gc1b
  obtain ⟨fd1, hfd1, hbfd1, -, -⟩ := pa_ed h hD hpos gc1d
  obtain ⟨fa2, hfa2, hbfa2, -, hfa2x⟩ := pa_ed h hD hpos gc2a
  obtain ⟨fb2, hfb2, hbfb2, -, hfb2x⟩ := pa_ed h hD hpos gc2b
  obtain ⟨fd2, hfd2, hbfd2, -, -⟩ := pa_ed h hD hpos gc2d
  have hba1 : sem_bar fa1 = Da1 := by
    rw [hWa1, mem_insert, mem_singleton] at hbfa1
    exact hbfa1.resolve_left (fun hh => hc1 (hfa1x ia1 hia1 h0a1 hh ▸ hia1))
  have hbb1 : sem_bar fb1 = Db1 := by
    rw [hWb1, mem_insert, mem_singleton] at hbfb1
    exact hbfb1.resolve_left (fun hh => hc1 (hfb1x ib1 hib1 h0b1 hh ▸ hib1))
  have hba2 : sem_bar fa2 = Da2 := by
    rw [hWa2, mem_insert, mem_singleton] at hbfa2
    exact hbfa2.resolve_left (fun hh => hc2 (hfa2x ia2 hia2 h0a2 hh ▸ hia2))
  have hWc1 := pa_three hfa1 hfb1 hfd1
    (fun hh => hpa1 b1 hab1.symm (hs b1 a1 lb1 la1) (hba1 ▸ hh ▸ hbfb1))
    (fun hh => hpa1 d1 had1.symm (hs d1 a1 ld1 la1) (hba1 ▸ hh ▸ hbfd1))
    (fun hh => hpb1 d1 hbd1.symm (hs d1 b1 ld1 lb1) (hbb1 ▸ hh ▸ hbfd1)) (hc3 c1 (Or.inl h0I))
  have hWc2 := pa_three hfa2 hfb2 hfd2
    (fun hh => hpa2 b2 hab2.symm (hs b2 a2 lb2 la2) (hba2 ▸ hh ▸ hbfb2))
    (fun hh => hpa2 d2 had2.symm (hs d2 a2 ld2 la2) (hba2 ▸ hh ▸ hbfd2))
    (fun hh => (by
      have hbb2 : sem_bar fb2 = Db2 := by
        rw [hWb2, mem_insert, mem_singleton] at hbfb2
        exact hbfb2.resolve_left (fun hh' => hc2 (hfb2x ib2 hib2 h0b2 hh' ▸ hib2))
      have hpb2' : ∀ w : Fin 14, w ≠ b2 → decide (w.val < 7) = decide (b2.val < 7) → Db2 ∉ sem_W 14 D w := by
        obtain ⟨Db2', hne', hW', hp'⟩ := ps_side h hD hpos hib2 h0b2 gib2 hdb2 hb2
        have heq : Db2' = Db2 := by
          have hm : Db2' ∈ ({pos ib2, Db2} : Finset (ℕ × Bool)) := by rw [← hWb2, hW']; simp
          simp only [mem_insert, mem_singleton] at hm; exact hm.resolve_left hne'
        exact heq ▸ hp'
      exact hpb2' d2 hbd2.symm (hs d2 b2 ld2 lb2) (hbb2 ▸ hh ▸ hbfd2))) (hc3 c2 (Or.inl h0I))
  have hnot_c2 : ∀ (x : Fin 14) (fx Dx : ℕ × Bool), x.val < 7 → sem_bar fx = Dx →
      (∀ w, w ≠ x → decide (w.val < 7) = decide (x.val < 7) → Dx ∉ sem_W 14 D w) →
      x ≠ a2 → x ≠ b2 → x ≠ d2 → fx ∉ sem_W 14 D c2 := by
    intro x fx Dx lx hbx hpx hxa hxb hxd hmem
    rcases hWc2 fx hmem with hh | hh | hh
    · exact hpx a2 hxa.symm (hs a2 x la2 lx) (hbx ▸ hh ▸ hbfa2)
    · exact hpx b2 hxb.symm (hs b2 x lb2 lx) (hbx ▸ hh ▸ hbfb2)
    · exact hpx d2 hxd.symm (hs d2 x ld2 lx) (hbx ▸ hh ▸ hbfd2)
  by_cases hd1_3 : 3 ≤ (sem_W 14 D d1).card
  · have hfd1_not : fd1 ∉ sem_W 14 D d1 := pa_ed_not_mem h hbfd1
    have hPQ_sub : ∀ e, e = P ∨ e = Q → e = fa1 ∨ e = fb1 := by
      intro e he
      have h1 : e ∈ sem_W 14 D c1 := he.elim (fun h' => h' ▸ (hsat c1 (Or.inl h0I) hc1_3).1) (fun h' => h' ▸ (hsat c1 (Or.inl h0I) hc1_3).2)
      have h2 : e ∈ sem_W 14 D d1 := he.elim (fun h' => h' ▸ (hsat d1 (Or.inl h0I) hd1_3).1) (fun h' => h' ▸ (hsat d1 (Or.inl h0I) hd1_3).2)
      rcases hWc1 e h1 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd h2 hfd1_not
    have hfa1_in : fa1 ∈ sem_W 14 D c2 := by
      rcases hPQ_sub P (Or.inl rfl) with h1 | h1 <;> rcases hPQ_sub Q (Or.inr rfl) with h2 | h2
      · exact absurd (h1.trans h2.symm) hPQ
      · exact h1 ▸ (hsat c2 (Or.inl h0I) hc2_3).1
      · exact h2 ▸ (hsat c2 (Or.inl h0I) hc2_3).2
      · exact absurd (h1.trans h2.symm) hPQ
    have hfb1_in : fb1 ∈ sem_W 14 D c2 := by
      rcases hPQ_sub P (Or.inl rfl) with h1 | h1 <;> rcases hPQ_sub Q (Or.inr rfl) with h2 | h2
      · exact absurd (h1.trans h2.symm) hPQ
      · exact h2 ▸ (hsat c2 (Or.inl h0I) hc2_3).2
      · exact h1 ▸ (hsat c2 (Or.inl h0I) hc2_3).1
      · exact absurd (h1.trans h2.symm) hPQ
    rcases hor1 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact hnot_c2 a1 fa1 Da1 la1 hba1 hpa1 h1 h2 h3 hfa1_in
    · exact hnot_c2 b1 fb1 Db1 lb1 hbb1 hpb1 h1 h2 h3 hfb1_in
  · obtain ⟨Dd1, -, hWd1, hpd1⟩ := ps_side h hD hpos hid1 h0d1 gid1 hdd1 (by omega)
    obtain ⟨fd1', hfd1', hbfd1', -, hfd1'x⟩ := pa_ed h hD hpos gc1d
    have hbd1' : sem_bar fd1' = Dd1 := by
      rw [hWd1, mem_insert, mem_singleton] at hbfd1'
      exact hbfd1'.resolve_left (fun hh => hc1 (hfd1'x id1 hid1 h0d1 hh ▸ hid1))
    have hWc1' := pa_three hfa1 hfb1 hfd1'
      (fun hh => hpa1 b1 hab1.symm (hs b1 a1 lb1 la1) (hba1 ▸ hh ▸ hbfb1))
      (fun hh => hpa1 d1 had1.symm (hs d1 a1 ld1 la1) (hba1 ▸ hh ▸ hbfd1'))
      (fun hh => hpb1 d1 hbd1.symm (hs d1 b1 ld1 lb1) (hbb1 ▸ hh ▸ hbfd1')) (hc3 c1 (Or.inl h0I))
    rcases hor2 with ⟨ha2', hb2', hc2', hd2', he2', hf2'⟩ | ⟨ha2', hb2', hc2', hd2', he2', hf2'⟩ | ⟨ha2', hb2', hc2', hd2', he2', hf2'⟩
    · have honly : ∀ e, e ∈ sem_W 14 D c1 → e ∈ sem_W 14 D c2 → e = fd1' := fun e he1 he2 => by
        rcases hWc1' e he1 with rfl | rfl | rfl
        · exact absurd he2 (hnot_c2 a1 e Da1 la1 hba1 hpa1 ha2' hb2' hc2')
        · exact absurd he2 (hnot_c2 b1 e Db1 lb1 hbb1 hpb1 hd2' he2' hf2')
        · rfl
      exact hPQ ((honly P (hsat c1 (Or.inl h0I) hc1_3).1 (hsat c2 (Or.inl h0I) hc2_3).1).trans
        (honly Q (hsat c1 (Or.inl h0I) hc1_3).2 (hsat c2 (Or.inl h0I) hc2_3).2).symm)
    · have honly : ∀ e, e ∈ sem_W 14 D c1 → e ∈ sem_W 14 D c2 → e = fb1 := fun e he1 he2 => by
        rcases hWc1' e he1 with rfl | rfl | rfl
        · exact absurd he2 (hnot_c2 a1 e Da1 la1 hba1 hpa1 ha2' hb2' hc2')
        · rfl
        · exact absurd he2 (hnot_c2 d1 e Dd1 ld1 hbd1' hpd1 hd2' he2' hf2')
      exact hPQ ((honly P (hsat c1 (Or.inl h0I) hc1_3).1 (hsat c2 (Or.inl h0I) hc2_3).1).trans
        (honly Q (hsat c1 (Or.inl h0I) hc1_3).2 (hsat c2 (Or.inl h0I) hc2_3).2).symm)
    · have honly : ∀ e, e ∈ sem_W 14 D c1 → e ∈ sem_W 14 D c2 → e = fa1 := fun e he1 he2 => by
        rcases hWc1' e he1 with rfl | rfl | rfl
        · rfl
        · exact absurd he2 (hnot_c2 b1 e Db1 lb1 hbb1 hpb1 ha2' hb2' hc2')
        · exact absurd he2 (hnot_c2 d1 e Dd1 ld1 hbd1' hpd1 hd2' he2' hf2')
      exact hPQ ((honly P (hsat c1 (Or.inl h0I) hc1_3).1 (hsat c2 (Or.inl h0I) hc2_3).1).trans
        (honly Q (hsat c1 (Or.inl h0I) hc1_3).2 (hsat c2 (Or.inl h0I) hc2_3).2).symm)
def pack6 (b1 b2 b3 b4 b5 b6 : Bool) : ℕ :=
  (if b1 then 1 else 0) + (if b2 then 2 else 0) + (if b3 then 4 else 0) +
  (if b4 then 8 else 0) + (if b5 then 16 else 0) + (if b6 then 32 else 0)
theorem pack6_lt (b1 b2 b3 b4 b5 b6 : Bool) : pack6 b1 b2 b3 b4 b5 b6 < 64 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide
theorem pack6_bit (b1 b2 b3 b4 b5 b6 : Bool) :
    (pack6 b1 b2 b3 b4 b5 b6).testBit 0 = b1 ∧ (pack6 b1 b2 b3 b4 b5 b6).testBit 1 = b2 ∧
    (pack6 b1 b2 b3 b4 b5 b6).testBit 2 = b3 ∧ (pack6 b1 b2 b3 b4 b5 b6).testBit 3 = b4 ∧
    (pack6 b1 b2 b3 b4 b5 b6).testBit 4 = b5 ∧ (pack6 b1 b2 b3 b4 b5 b6).testBit 5 = b6 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide
theorem elim_63_S3_ge3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {pos : Fin 14 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : res1_ctx D pos P Q)
    (hIeq : ineligSet 14 D = {0, 7, 8, 10}) :
    3 ≤ (({1, 2, 3, 4, 5, 6} : Finset (Fin 14)).filter (fun x => 3 ≤ (sem_W 14 D x).card)).card := by
  classical
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := mI hIeq
  set L6 : Finset (Fin 14) := {1, 2, 3, 4, 5, 6}
  set S3 : Finset (Fin 14) := L6.filter (fun x => 3 ≤ (sem_W 14 D x).card)
  have hbad_pair : ∀ c1 ∈ ({9, 11, 12, 13} : Finset (Fin 14)), ∀ c2 ∈ ({9, 11, 12, 13} : Finset (Fin 14)),
      c1 ≠ c2 → 2 ≤ (g14_nbB c1 \ S3).card → 2 ≤ (g14_nbB c2 \ S3).card → False := by
    let i63 : Fin 14 → Fin 14 := fun x => match x.val with | 1 => 7 | 3 => 7 | 2 => 8 | 6 => 8 | _ => 10
    have hi63_ok : ∀ x ∈ L6, i63 x ∈ ({0, 7, 8, 10} : Finset (Fin 14)) ∧ i63 x ≠ 0 ∧
        hc_adjB (i63 x) x = true ∧ (g14_nbB x).card = 3 ∧ x.val < 7 := by decide +kernel
    have hnb_sub : ∀ c ∈ ({9, 11, 12, 13} : Finset (Fin 14)), g14_nbB c ⊆ L6 := by decide +kernel
    have hthird : ∀ c ∈ ({9, 11, 12, 13} : Finset (Fin 14)), ∀ a ∈ g14_nbB c, ∀ b ∈ g14_nbB c, a ≠ b →
        ∃ d ∈ g14_nbB c, a ≠ d ∧ b ≠ d := by decide +kernel
    have hpick : ∀ (c : Fin 14), c ∈ ({9, 11, 12, 13} : Finset (Fin 14)) →
        2 ≤ (g14_nbB c \ S3).card →
        ∃ a b d ia ib id_ : Fin 14,
          ia ∈ ineligSet 14 D ∧ ib ∈ ineligSet 14 D ∧ id_ ∈ ineligSet 14 D ∧
          ia ≠ 0 ∧ ib ≠ 0 ∧ id_ ≠ 0 ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
          hc_adjB c a = true ∧ hc_adjB c b = true ∧ hc_adjB c d = true ∧
          hc_adjB ia a = true ∧ hc_adjB ib b = true ∧ hc_adjB id_ d = true ∧
          (g14_nbB a).card = 3 ∧ (g14_nbB b).card = 3 ∧ (g14_nbB d).card = 3 ∧
          a.val < 7 ∧ b.val < 7 ∧ d.val < 7 ∧
          (sem_W 14 D a).card ≤ 2 ∧ (sem_W 14 D b).card ≤ 2 := by
      intro c hc h2
      have hpair : ∃ a ∈ g14_nbB c \ S3, ∃ b ∈ g14_nbB c \ S3, a ≠ b := Finset.one_lt_card.1 (by omega)
      obtain ⟨a, ha, b, hb, hab⟩ := hpair
      have ha1 : a ∈ g14_nbB c := (mem_sdiff.1 ha).1
      have hb1 : b ∈ g14_nbB c := (mem_sdiff.1 hb).1
      have haL : a ∈ L6 := hnb_sub c hc ha1
      have hbL : b ∈ L6 := hnb_sub c hc hb1
      have hale : (sem_W 14 D a).card ≤ 2 := by
        by_contra hlt; exact (mem_sdiff.1 ha).2 (mem_filter.2 ⟨haL, by omega⟩)
      have hble : (sem_W 14 D b).card ≤ 2 := by
        by_contra hlt; exact (mem_sdiff.1 hb).2 (mem_filter.2 ⟨hbL, by omega⟩)
      obtain ⟨d, hd1, had, hbd⟩ := hthird c hc a ha1 b hb1 hab
      have hdL : d ∈ L6 := hnb_sub c hc hd1
      obtain ⟨hia, h0a, gia, hda, hla⟩ := hi63_ok a haL
      obtain ⟨hib, h0b, gib, hdb, hlb⟩ := hi63_ok b hbL
      obtain ⟨hid, h0d, gid, hdd, hld⟩ := hi63_ok d hdL
      exact ⟨a, b, d, i63 a, i63 b, i63 d, hIeq ▸ hia, hIeq ▸ hib, hIeq ▸ hid,
        h0a, h0b, h0d, hab, had, hbd,
        (hc_adjB_iff _ _).2 (g14_mem_nb.1 ha1), (hc_adjB_iff _ _).2 (g14_mem_nb.1 hb1),
        (hc_adjB_iff _ _).2 (g14_mem_nb.1 hd1), gia, gib, gid, hda, hdb, hdd, hla, hlb, hld, hale, hble⟩
    intro c1 hc1 c2 hc2 hne h21 h22
    obtain ⟨a1, b1, d1, ia1, ib1, id1, hia1, hib1, hid1, h0a1, h0b1, h0d1, hab1, had1, hbd1,
      gc1a, gc1b, gc1d, gia1, gib1, gid1, hda1, hdb1, hdd1, la1, lb1, ld1, hale1, hble1⟩ := hpick c1 hc1 h21
    obtain ⟨a2, b2, d2, ia2, ib2, -, hia2, hib2, -, h0a2, h0b2, -, hab2, had2, hbd2,
      gc2a, gc2b, gc2d, gia2, gib2, -, hda2, hdb2, -, la2, lb2, ld2, hale2, hble2⟩ := hpick c2 hc2 h22
    have hor : ((a1 ≠ a2 ∧ a1 ≠ b2 ∧ a1 ≠ d2) ∨ (b1 ≠ a2 ∧ b1 ≠ b2 ∧ b1 ≠ d2)) ∧
      ((a1 ≠ a2 ∧ a1 ≠ b2 ∧ a1 ≠ d2 ∧ b1 ≠ a2 ∧ b1 ≠ b2 ∧ b1 ≠ d2) ∨
       (a1 ≠ a2 ∧ a1 ≠ b2 ∧ a1 ≠ d2 ∧ d1 ≠ a2 ∧ d1 ≠ b2 ∧ d1 ≠ d2) ∨
       (b1 ≠ a2 ∧ b1 ≠ b2 ∧ b1 ≠ d2 ∧ d1 ≠ a2 ∧ d1 ≠ b2 ∧ d1 ≠ d2)) := by
      have hint : (g14_nbB c1 ∩ g14_nbB c2).card ≤ 1 := common_nbr_le_one c1 c2 hne
      have hnb1 : a1 ∈ g14_nbB c1 ∧ b1 ∈ g14_nbB c1 ∧ d1 ∈ g14_nbB c1 :=
        ⟨g14_mem_nb.2 ((hc_adjB_iff _ _).1 gc1a),
         g14_mem_nb.2 ((hc_adjB_iff _ _).1 gc1b),
         g14_mem_nb.2 ((hc_adjB_iff _ _).1 gc1d)⟩
      have hnb2 : ∀ x, x = a2 ∨ x = b2 ∨ x = d2 → x ∈ g14_nbB c2 := by
        rintro x (rfl | rfl | rfl)
        · exact g14_mem_nb.2 ((hc_adjB_iff _ _).1 gc2a)
        · exact g14_mem_nb.2 ((hc_adjB_iff _ _).1 gc2b)
        · exact g14_mem_nb.2 ((hc_adjB_iff _ _).1 gc2d)
      have hnot2 : ∀ x y, x ≠ y → x ∈ g14_nbB c1 → y ∈ g14_nbB c1 →
          (x = a2 ∨ x = b2 ∨ x = d2) → (y = a2 ∨ y = b2 ∨ y = d2) → False := by
        intro x y hxy hx1 hy1 hx2 hy2
        have hsub : ({x, y} : Finset (Fin 14)) ⊆ g14_nbB c1 ∩ g14_nbB c2 := by
          intro z hz; simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact mem_inter.2 ⟨hx1, hnb2 z hx2⟩
          · exact mem_inter.2 ⟨hy1, hnb2 z hy2⟩
        have := card_le_card hsub
        rw [card_pair hxy] at this; omega
      by_cases ha : a1 = a2 ∨ a1 = b2 ∨ a1 = d2
      · have hbn : b1 ≠ a2 ∧ b1 ≠ b2 ∧ b1 ≠ d2 := by
          refine ⟨fun hh => hnot2 a1 b1 hab1 hnb1.1 hnb1.2.1 ha (Or.inl hh),
            fun hh => hnot2 a1 b1 hab1 hnb1.1 hnb1.2.1 ha (Or.inr (Or.inl hh)),
            fun hh => hnot2 a1 b1 hab1 hnb1.1 hnb1.2.1 ha (Or.inr (Or.inr hh))⟩
        have hdn : d1 ≠ a2 ∧ d1 ≠ b2 ∧ d1 ≠ d2 := by
          refine ⟨fun hh => hnot2 a1 d1 had1 hnb1.1 hnb1.2.2 ha (Or.inl hh),
            fun hh => hnot2 a1 d1 had1 hnb1.1 hnb1.2.2 ha (Or.inr (Or.inl hh)),
            fun hh => hnot2 a1 d1 had1 hnb1.1 hnb1.2.2 ha (Or.inr (Or.inr hh))⟩
        exact ⟨Or.inr hbn, Or.inr (Or.inr ⟨hbn.1, hbn.2.1, hbn.2.2, hdn.1, hdn.2.1, hdn.2.2⟩)⟩
      · push Not at ha
        by_cases hb : b1 = a2 ∨ b1 = b2 ∨ b1 = d2
        · have hdn : d1 ≠ a2 ∧ d1 ≠ b2 ∧ d1 ≠ d2 := by
            refine ⟨fun hh => hnot2 b1 d1 hbd1 hnb1.2.1 hnb1.2.2 hb (Or.inl hh),
              fun hh => hnot2 b1 d1 hbd1 hnb1.2.1 hnb1.2.2 hb (Or.inr (Or.inl hh)),
              fun hh => hnot2 b1 d1 hbd1 hnb1.2.1 hnb1.2.2 hb (Or.inr (Or.inr hh))⟩
          exact ⟨Or.inl ha, Or.inr (Or.inl ⟨ha.1, ha.2.1, ha.2.2, hdn.1, hdn.2.1, hdn.2.2⟩)⟩
        · push Not at hb
          exact ⟨Or.inl ha, Or.inl ⟨ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2⟩⟩
    exact elim_3star_pair_sound h hD hctx h0I c1 c2 a1 b1 d1 a2 b2 d2 ia1 ib1 id1 ia2 ib2
      hia1 hib1 hid1 hia2 hib2
      (by simp only [mem_insert, mem_singleton] at hc1; rcases hc1 with rfl | rfl | rfl | rfl <;> exact nI hIeq)
      (by simp only [mem_insert, mem_singleton] at hc2; rcases hc2 with rfl | rfl | rfl | rfl <;> exact nI hIeq)
      ⟨h0a1, h0b1, h0d1, h0a2, h0b2, hab1, had1, hbd1, hab2, had2, hbd2,
        gc1a, gc1b, gc1d, gc2a, gc2b, gc2d, gia1, gib1, gid1, gia2, gib2,
        hda1, hdb1, hdd1, hda2, hdb2, la1, lb1, ld1, la2, lb2, ld2, hor.1, hor.2⟩
      hale1 hble1 hale2 hble2
  let b1 := decide ((1 : Fin 14) ∈ S3)
  let b2 := decide ((2 : Fin 14) ∈ S3)
  let b3 := decide ((3 : Fin 14) ∈ S3)
  let b4 := decide ((4 : Fin 14) ∈ S3)
  let b5 := decide ((5 : Fin 14) ∈ S3)
  let b6 := decide ((6 : Fin 14) ∈ S3)
  let maskVal : ℕ := pack6 b1 b2 b3 b4 b5 b6
  have hlt64 : maskVal < 64 := pack6_lt b1 b2 b3 b4 b5 b6
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := pack6_bit b1 b2 b3 b4 b5 b6
  have hS3_eq : S3 = L6.filter (fun x => Nat.testBit maskVal (x.val - 1)) := by
    ext x; simp only [mem_filter]
    constructor
    · intro hx
      have hxL : x ∈ L6 := (mem_filter.1 hx).1
      refine ⟨hxL, ?_⟩
      dsimp only [L6] at hxL; simp only [mem_insert, mem_singleton] at hxL
      rcases hxL with rfl | rfl | rfl | rfl | rfl | rfl
      · change maskVal.testBit 0 = true; rw [hb1]; exact decide_eq_true hx
      · change maskVal.testBit 1 = true; rw [hb2]; exact decide_eq_true hx
      · change maskVal.testBit 2 = true; rw [hb3]; exact decide_eq_true hx
      · change maskVal.testBit 3 = true; rw [hb4]; exact decide_eq_true hx
      · change maskVal.testBit 4 = true; rw [hb5]; exact decide_eq_true hx
      · change maskVal.testBit 5 = true; rw [hb6]; exact decide_eq_true hx
    · rintro ⟨hxL, htb⟩
      dsimp only [L6] at hxL; simp only [mem_insert, mem_singleton] at hxL
      rcases hxL with rfl | rfl | rfl | rfl | rfl | rfl
      · change maskVal.testBit 0 = true at htb; rw [hb1] at htb; exact of_decide_eq_true htb
      · change maskVal.testBit 1 = true at htb; rw [hb2] at htb; exact of_decide_eq_true htb
      · change maskVal.testBit 2 = true at htb; rw [hb3] at htb; exact of_decide_eq_true htb
      · change maskVal.testBit 3 = true at htb; rw [hb4] at htb; exact of_decide_eq_true htb
      · change maskVal.testBit 4 = true at htb; rw [hb5] at htb; exact of_decide_eq_true htb
      · change maskVal.testBit 5 = true at htb; rw [hb6] at htb; exact of_decide_eq_true htb
  have hbad1 : (({9, 11, 12, 13} : Finset (Fin 14)).filter (fun c => 2 ≤ (g14_nbB c \ S3).card)).card ≤ 1 := by
    by_contra hgt
    have hlt1 : 1 < (({9, 11, 12, 13} : Finset (Fin 14)).filter (fun c => 2 ≤ (g14_nbB c \ S3).card)).card := by omega
    obtain ⟨c1, hc1, c2, hc2, hne⟩ := Finset.one_lt_card.1 hlt1
    rw [mem_filter] at hc1 hc2
    exact hbad_pair c1 hc1.1 c2 hc2.1 hne hc1.2 hc2.2
  have hres := elim_63_S_ge3 ⟨maskVal, hlt64⟩
  dsimp only at hres
  rw [← hS3_eq] at hres
  exact hres hbad1
theorem elim_63 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨63, by decide⟩) : False := by
  classical
  have hIeq : ineligSet 14 D = {0, 7, 8, 10} := by rw [hI]; decide +kernel
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := mI hIeq
  obtain ⟨hB0, pos, P, Q, hpos, hc3, hPQ, hsat⟩ := res1_setup_c4 h hD h11 ⟨63, by decide⟩ hI (by rw [hIeq]; decide)
  have hctx : res1_ctx D pos P Q := ⟨hpos, hc3, hPQ, hsat⟩
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hc4 : (ineligSet 14 D).card = 4 := by rw [hIeq]; decide
  have hB1 : Bplus 14 D = (eligSet 14 D).card + 1 := by
    have hgt : (eligSet 14 D).card + 1 ≤ Bplus 14 D := by
      by_contra hle; exact tight_le_all h hD (by omega) ⟨63, by decide⟩ hI
    omega
  obtain ⟨b, hmin⟩ := exists_weakMinBranch14 h hD
  have hbp := weak_to_pure b (weakMinBranch_pure hmin) h0I
  have hres1 : (residualUnits 14 D b).card = 1 := by have := card_residual h.1 b hbp; omega
  obtain ⟨u0, hres⟩ := card_eq_one.1 hres1
  set L6 : Finset (Fin 14) := {1, 2, 3, 4, 5, 6}
  have hPeq : sideL \ ineligSet 14 D = L6 := by rw [hIeq]; decide
  set S3 : Finset (Fin 14) := L6.filter (fun x => 3 ≤ (sem_W 14 D x).card)
  have hS3_ge3 : 3 ≤ S3.card := elim_63_S3_ge3 h hD hctx hIeq
  have h7810_I : ∀ i ∈ ({7, 8, 10} : Finset (Fin 14)), i ∈ ineligSet 14 D := fun i hi => by
    simp only [mem_insert, mem_singleton] at hi; rcases hi with rfl | rfl | rfl <;> exact mI hIeq
  have h7810_0 : ∀ i ∈ ({7, 8, 10} : Finset (Fin 14)), i ≠ 0 := fun i hi => by
    simp only [mem_insert, mem_singleton] at hi; rcases hi with rfl | rfl | rfl <;> decide
  have h7810_nb2 : ∀ i ∈ ({7, 8, 10} : Finset (Fin 14)), (sem_g14_nb i ∩ L6).card = 2 := fun i hi => by
    simp only [mem_insert, mem_singleton] at hi; rcases hi with rfl | rfl | rfl <;> decide +kernel
  have h7810_notL6 : ∀ i ∈ ({7, 8, 10} : Finset (Fin 14)), i ∉ L6 := fun i hi => by
    simp only [mem_insert, mem_singleton] at hi; rcases hi with rfl | rfl | rfl <;> decide
  obtain ⟨m, hiff, hcnt, hlost⟩ := g14_sideL_exact h hD
  have hmeq : maskFin7 m = ({0, 1, 3} : Finset (Fin 7)) := by
    apply elim_63_only_m m
    · intro k hk; rw [← hIeq]; exact ((hiff k).1 hk).1
    · rw [← hIeq]; have hP6 : (sideL \ ineligSet 14 D).card = 6 := by rw [hPeq]; decide
      omega
    · rw [← hIeq]; omega
  have hocc_of : ∀ k : Fin 7, k ∈ ({0, 1, 3} : Finset (Fin 7)) →
      sup_Occ 14 D L6 (sem_g14_nb (os_ptR k) ∩ L6) := fun k hk => by
    have h1 := ((hiff k).1 (hmeq ▸ hk)).2; rwa [hPeq] at h1
  have hno_of : ∀ k : Fin 7, k ∈ ({2, 4, 5, 6} : Finset (Fin 7)) →
      ¬ sup_Occ 14 D L6 (sem_g14_nb (os_ptR k) ∩ L6) := fun k hk hocc => by
    have hok : okL_pred (ineligSet 14 D) (sideL \ ineligSet 14 D) k := by
      rw [hIeq]; simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide +kernel
    have hmem : k ∈ maskFin7 m := (hiff k).2 ⟨hok, by rwa [hPeq]⟩
    rw [hmeq] at hmem; simp only [mem_insert, mem_singleton] at hk hmem
    rcases hk with rfl | rfl | rfl | rfl <;> simp at hmem
  set T0 : Finset (Fin 14) := supp 14 D u0.1 ∩ L6
  have hS3_sub_T0 : S3 ⊆ T0 := fun x hx => by
    rw [mem_filter] at hx
    exact mem_inter.2 ⟨(sem_saturated sem_g14_gr h (sem_g14_comp hD) b hbp hres hx.2).2.2.2, hx.1⟩
  have hT0_3 : 3 ≤ T0.card := hS3_ge3.trans (card_le_card hS3_sub_T0)
  let ct : Fin 14 → Fin 14 := fun f =>
    if f = 1 ∨ f = 2 then 13 else if f = 5 then 12 else 11
  have hct_in : ∀ f : Fin 14, ct f = 13 ∨ ct f = 12 ∨ ct f = 11 := fun f => by
    dsimp only [ct]; split_ifs <;> simp
  have h7810_ne_ct : ∀ i ∈ ({7, 8, 10} : Finset (Fin 14)), ∀ f : Fin 14, i ≠ ct f := fun i hi f => by
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> rcases hct_in f with h' | h' | h' <;> (rw [h']; decide)
  have hct_k : ∀ f ∈ L6, ∃ k ∈ ({2, 4, 5, 6} : Finset (Fin 7)), os_ptR k = ct f ∧ f ∈ sem_g14_nb (ct f) ∩ L6 := by
    intro f hf; dsimp only [L6] at hf; simp only [mem_insert, mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨6, by decide, by decide, by decide⟩
    · exact ⟨6, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact ⟨5, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide⟩
  have hL6_ind : ∀ a ∈ L6, ∀ b ∈ L6, ¬ Adj a b := fun a ha b hb =>
    sideL_indep a (sdiff_subset (hPeq ▸ ha)) b (sdiff_subset (hPeq ▸ hb))
  have hw : ∀ f ∈ L6, ∃ e, sup_Wit 14 D L6 (sem_g14_nb (ct f) ∩ L6) f e := by
    intro f hf
    obtain ⟨k, hk, hkf, hfc⟩ := hct_k f hf
    refine sup_wit_exists sem_g14_gr h.1 (sem_g14_comp hD) (X := insert (ct f) (L6 \ (sem_g14_nb (ct f) ∩ L6)))
      inter_subset_right ?_ ?_ (fun a ha => Finset.mem_insert_of_mem ha) hfc
      ⟨ct f, mem_insert_self _ _, adj_symm (g14_mem_nb.1 (mem_inter.1 hfc).1)⟩
    · refine Or.inr ⟨?_, hkf ▸ hno_of k hk⟩
      dsimp only [L6] at hf; simp only [mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · have hno : ∀ a ∈ L6 \ (sem_g14_nb (ct f) ∩ L6), ¬ Adj (ct f) a := fun a ha hadj => by
        rw [mem_sdiff, mem_inter, g14_mem_nb] at ha; exact ha.2 ⟨hadj, ha.1⟩
      intro a ha b hb
      rcases mem_insert.1 ha with rfl | ha <;> rcases mem_insert.1 hb with rfl | hb
      · exact adj_irrefl _
      · exact hno b hb
      · exact fun hab => hno a ha (adj_symm hab)
      · exact hL6_ind a (mem_sdiff.1 ha).1 b (mem_sdiff.1 hb).1
  choose! wit hwit using hw
  let S_sing := L6.filter (fun f => ∀ M, M ⊆ sem_g14_nb (ct f) ∩ L6 → M.card = 2 → f ∈ M → ¬ sup_Occ 14 D L6 M)
  have hSL : S_sing ⊆ L6 := filter_subset _ _
  have hno : ∀ f ∈ L6 \ S_sing, ∃ M, M ⊆ sem_g14_nb (ct f) ∩ L6 ∧ M.card = 2 ∧ f ∈ M ∧ sup_Occ 14 D L6 M := by
    intro f hf; rw [mem_sdiff, mem_filter] at hf; by_contra hc
    exact hf.2 ⟨hf.1, fun M h1 h2 h4 h5 => hc ⟨M, h1, h2, h4, h5⟩⟩
  choose! pr hpr using hno
  set L2 : Finset (Finset (Fin 14)) := ({0, 1, 3} : Finset (Fin 7)).image (fun k => sem_g14_nb (os_ptR k) ∩ L6)
  have hL2_card : L2.card = 3 := by decide +kernel
  have hL2_c2 : ∀ M ∈ L2, M.card = 2 ∧ sup_Occ 14 D L6 M := fun M hM => by
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hM
    exact ⟨by simp only [mem_insert, mem_singleton] at hk; rcases hk with rfl | rfl | rfl <;> decide +kernel, hocc_of k hk⟩
  have hL2dis : Disjoint L2 ((L6 \ S_sing).image pr) := by
    rw [disjoint_left]
    intro M hM2 hMpr
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hM2
    obtain ⟨f, hf, hprf⟩ := mem_image.1 hMpr
    have hsub := (hpr f hf).1; have hc2 := (hpr f hf).2.1; rw [hprf] at hsub hc2
    have hne : os_ptR k ≠ ct f := by
      simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> rcases hct_in f with h' | h' | h' <;> (rw [h']; decide)
    have hle := sup_g14_inter (os_ptR k) (ct f) hne L6
    have hsub' : sem_g14_nb (os_ptR k) ∩ L6 ⊆ sem_g14_nb (os_ptR k) ∩ (sem_g14_nb (ct f) ∩ L6) :=
      fun x hx => mem_inter.2 ⟨(mem_inter.1 hx).1, hsub hx⟩
    have := card_le_card hsub'; omega
  have hT0_not : T0 ∉ L2 ∪ (L6 \ S_sing).image pr := by
    intro hm
    rcases mem_union.1 hm with h1 | h2
    · have := (hL2_c2 T0 h1).1; omega
    · obtain ⟨f, hf, hprf⟩ := mem_image.1 h2
      have := (hpr f hf).2.1; rw [hprf] at this; omega
  set F : Finset (Finset (Fin 14)) := insert T0 (L2 ∪ (L6 \ S_sing).image pr)
  have hF_card : F.card = 4 + ((L6 \ S_sing).image pr).card := by
    rw [card_insert_of_notMem hT0_not, card_union_of_disjoint hL2dis, hL2_card]; omega
  have hF_ok : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ 14 D L6 M := by
    intro M hM
    rcases mem_insert.1 hM with rfl | hM'
    · exact ⟨by omega, ⟨u0.1, rfl⟩⟩
    · rcases mem_union.1 hM' with h1 | h2
      · exact ⟨by have := (hL2_c2 M h1).1; omega, (hL2_c2 M h1).2⟩
      · obtain ⟨f, hf, rfl⟩ := mem_image.1 h2
        exact ⟨by have := (hpr f hf).2.1; omega, (hpr f hf).2.2.2⟩
  have hbig_ge : 4 + ((L6 \ S_sing).image pr).card ≤ (sup_big 14 D L6).card :=
    hF_card ▸ sup_card_le_big h.1 L6 F hF_ok
  set E : Finset (ℕ × Bool) := ({7, 8, 10} : Finset (Fin 14)).image pos
  have hEcard : E.card = 3 := by
    rw [card_image_of_injOn (fun i hi j hj hij => hpos.2.2 i (h7810_I i hi) j (h7810_I j hj) hij)]
    decide
  have hEexit : ∀ e ∈ E, e ∈ exitArcs 14 D (carrierT 14 D L6) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := mem_image.1 he
    obtain ⟨hj, hemp, hnb, -⟩ := hpos.1 i (h7810_I i hi) (h7810_0 i hi)
    obtain ⟨a, ha⟩ := card_pos.1 (show 0 < (sem_g14_nb i ∩ L6).card by rw [h7810_nb2 i hi]; omega)
    rw [mem_inter] at ha
    rw [exitArcs, mem_filter]
    refine ⟨mem_product.2 ⟨mem_range.2 hj, mem_univ _⟩,
      sup_mem_carrier.2 ⟨a, mem_inter.2 ⟨hnb a (g14_mem_nb.1 ha.1), ha.2⟩⟩, ?_⟩
    rw [sup_mem_carrier, hemp, Finset.empty_inter]; exact not_nonempty_empty
  have hEdis : ∀ e ∈ E, ∀ f ∈ L6, e ≠ wit f := by
    intro e he f hf hew
    obtain ⟨i, hi, rfl⟩ := mem_image.1 he
    have hnbi : sem_g14_nb i ∩ L6 ⊆ supp 14 D (src D (pos i)) ∩ L6 := fun a ha => by
      rw [mem_inter] at ha ⊢; exact ⟨(hpos.1 i (h7810_I i hi) (h7810_0 i hi)).2.2.1 a (g14_mem_nb.1 ha.1), ha.2⟩
    have hwsub : supp 14 D (src D (pos i)) ∩ L6 ⊆ sem_g14_nb (ct f) ∩ L6 := hew ▸ (hwit f hf).2.2.2.2.2.1
    have hle := sup_g14_inter i (ct f) (h7810_ne_ct i hi f) L6
    have hsub' : sem_g14_nb i ∩ L6 ⊆ sem_g14_nb i ∩ (sem_g14_nb (ct f) ∩ L6) := fun a ha =>
      mem_inter.2 ⟨(mem_inter.1 ha).1, hwsub (hnbi ha)⟩
    have hge2 : 2 ≤ (sem_g14_nb i ∩ L6).card := (h7810_nb2 i hi).symm.le
    have := card_le_card hsub'; omega
  have hfib : (L6 \ S_sing).card ≤ 2 * ((L6 \ S_sing).image pr).card := by
    refine Finset.card_le_mul_card_image _ 2 (fun M _ => ?_)
    by_cases hne : ((L6 \ S_sing).filter (fun f => pr f = M)).Nonempty
    · obtain ⟨g, hg⟩ := hne; rw [mem_filter] at hg
      have hM2 : M.card = 2 := hg.2 ▸ (hpr g hg.1).2.1
      rw [← hM2]
      refine card_le_card (fun f hf => by rw [mem_filter] at hf; exact hf.2 ▸ (hpr f hf.1).2.2.1)
    · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  have hfl := carrier_flow_union h L6 (by rw [g14_supp_out hD]; simp)
  have hL6e : L6 ⊆ eligSet 14 D := fun a ha => by
    by_contra hc; exact (mem_sdiff.1 (hPeq ▸ ha)).2 (sem_mem_inelig.2 hc)
  have hsup := weak_surplus_carrierT_le h.1 b (weakMinBranch_pure hmin) L6 (Or.inl h0I)
  rw [inter_eq_left.2 hL6e] at hsup
  have hSLc := card_sdiff_add_card_eq_card hSL
  have hL6c : L6.card = 6 := by decide
  have hflow_le13 : (exitArcs 14 D (carrierT 14 D L6)).card + (merges 14 D (carrierT 14 D L6)).card ≤ 13 := by omega
  set C := L6.image (fun f => sup_cost 14 D L6 (wit f))
  have hCok : ∀ c ∈ C, sup_CostOK 14 D L6 c := fun c hc => by
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hc; exact sup_cost_ok h.1 (hwit f hf)
  have hCdis : Disjoint E C.toLeft := by
    rw [disjoint_left]; intro e he hL
    rw [mem_toLeft, mem_image] at hL
    obtain ⟨f, hf, hcf⟩ := hL
    have hwe : wit f = e := (sup_cost_inl hcf).1
    exact hEdis e he f hf hwe.symm
  have hC_ge : 2 * S_sing.card + (L6 \ S_sing).card ≤ 2 * C.card :=
    sup_wit_card_single h.1 L6 S_sing (fun f => sem_g14_nb (ct f) ∩ L6) wit hwit hSL
      (fun f hf => sup_wit_single (hwit f (hSL hf)) (mem_filter.1 hf).2)
  have hfull_all : ∀ i ∈ ({7, 8, 10} : Finset (Fin 14)), ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
    intro i hi
    rcases full_g14_or_arc h hD hB0 hpos (h7810_I i hi) (h7810_0 i hi) with hfull | ⟨p, hp1, hpne, hpt, hpsub, hpnb⟩
    · exact hfull
    · exfalso
      have hp_out : supp 14 D (14 + p.1) ∩ L6 = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        intro x hx; rw [mem_inter] at hx
        have hxi : x ∈ supp 14 D (src D (sem_bar p)) := by
          have := sem_supp_and_sub h.1 hp1 hpt (!p.2) hx.1; simpa [sem_bar] using this
        have hxe : x = i := mem_singleton.1 (hpsub hxi)
        exact h7810_notL6 i hi (hxe ▸ hx.2)
      have hp_exit : p ∈ exitArcs 14 D (carrierT 14 D L6) := by
        obtain ⟨a, ha⟩ := card_pos.1 (show 0 < (sem_g14_nb i ∩ L6).card by rw [h7810_nb2 i hi]; omega)
        rw [mem_inter] at ha
        rw [exitArcs, mem_filter]
        exact ⟨mem_product.2 ⟨mem_range.2 hp1, mem_univ _⟩,
          sup_mem_carrier.2 ⟨a, mem_inter.2 ⟨hpnb a (g14_mem_nb.1 ha.1), ha.2⟩⟩,
          by rw [sup_mem_carrier, hp_out]; exact not_nonempty_empty⟩
      have hp_notE : p ∉ E := by
        intro hpE; obtain ⟨j, hj, hjp⟩ := mem_image.1 hpE
        by_cases hij : i = j
        · subst hij; exact hpne (congrArg Prod.fst hjp.symm)
        · have hjm : j ∈ supp 14 D (src D (sem_bar p)) := by
            rw [← hjp, show src D (sem_bar (pos j)) = src D ((pos j).1, !(pos j).2) from rfl,
              (hpos.1 j (h7810_I j hj) (h7810_0 j hj)).2.2.2]; exact mem_singleton_self j
          exact hij (mem_singleton.1 (hpsub hjm)).symm
      have hp_notW : ∀ f ∈ L6, p ≠ wit f := by
        intro f hf hpw
        have hnbi : sem_g14_nb i ∩ L6 ⊆ supp 14 D (src D p) ∩ L6 := fun a ha => by
          rw [mem_inter] at ha ⊢; exact ⟨hpnb a (g14_mem_nb.1 ha.1), ha.2⟩
        have hwsub : supp 14 D (src D p) ∩ L6 ⊆ sem_g14_nb (ct f) ∩ L6 := hpw ▸ (hwit f hf).2.2.2.2.2.1
        have hle := sup_g14_inter i (ct f) (h7810_ne_ct i hi f) L6
        have hsub' : sem_g14_nb i ∩ L6 ⊆ sem_g14_nb i ∩ (sem_g14_nb (ct f) ∩ L6) := fun a ha =>
          mem_inter.2 ⟨(mem_inter.1 ha).1, hwsub (hnbi ha)⟩
        have hge2 : 2 ≤ (sem_g14_nb i ∩ L6).card := (h7810_nb2 i hi).symm.le
        have := card_le_card hsub'; omega
      have hcnt' := sup_count_disj h.1 L6 (insert p E)
        (fun e he => by rcases mem_insert.1 he with rfl | he'; exact hp_exit; exact hEexit e he')
        L6 S_sing (fun f => sem_g14_nb (ct f) ∩ L6) wit hwit hSL
        (fun f hf => sup_wit_single (hwit f (hSL hf)) (mem_filter.1 hf).2)
        (fun e he f hf => by rcases mem_insert.1 he with rfl | he'; exact hp_notW f hf; exact hEdis e he' f hf)
      rw [card_insert_of_notMem hp_notE, hEcard] at hcnt'
      omega
  have hS3_sub_P : S3 ⊆ supp 14 D (src D P) ∩ L6 := fun x hx => by
    rw [mem_filter] at hx
    exact mem_inter.2 ⟨(sem_mem_W.1 (hsat x (Or.inl h0I) hx.2).1).2.1, hx.1⟩
  have hP_card3 : 3 ≤ (supp 14 D (src D P) ∩ L6).card := hS3_ge3.trans (card_le_card hS3_sub_P)
  have hP_notE : P ∉ E := by
    intro hPE; obtain ⟨i, hi, hiP⟩ := mem_image.1 hPE
    have hsub : S3 ⊆ sem_g14_nb i ∩ L6 := fun x hx => by
      have hm := mem_inter.1 (hS3_sub_P hx)
      rw [← hiP] at hm
      exact mem_inter.2 ⟨g14_mem_nb.2 ((hfull_all i hi x).1 hm.1), hm.2⟩
    have hc2 : (sem_g14_nb i ∩ L6).card = 2 := h7810_nb2 i hi
    have := card_le_card hsub; omega
  have hP_notCL : P ∉ C.toLeft := by
    intro hPL; have hle2 := (hCok (Sum.inl P) (mem_toLeft.1 hPL)).2; omega
  obtain ⟨x0, hx0⟩ := card_pos.1 (by omega : 0 < S3.card)
  have hx0_W : P ∈ sem_W 14 D x0 := (hsat x0 (Or.inl h0I) (mem_filter.1 hx0).2).1
  have hjP_lt : P.1 < D.length := (sem_mem_W.1 hx0_W).1
  have hP_and : tag D P.1 = true := sem_W_and h.1 hx0_W
  set M : Finset (Fin 14) := supp 14 D (14 + P.1) ∩ L6
  by_cases hM0 : M.card = 0
  · have hMe : M = ∅ := card_eq_zero.1 hM0
    have hP_exit : P ∈ exitArcs 14 D (carrierT 14 D L6) := by
      rw [exitArcs, mem_filter]
      exact ⟨mem_product.2 ⟨mem_range.2 hjP_lt, mem_univ _⟩,
        sup_mem_carrier.2 ⟨x0, hS3_sub_P hx0⟩,
        by rw [sup_mem_carrier]; change ¬ M.Nonempty; rw [hMe]; exact not_nonempty_empty⟩
    have hmd := sup_master_disj L6 (insert P E)
      (fun e he => by rcases mem_insert.1 he with rfl | he'; exact hP_exit; exact hEexit e he')
      C hCok (Finset.disjoint_insert_left.2 ⟨hP_notCL, hCdis⟩)
    rw [card_insert_of_notMem hP_notE, hEcard] at hmd
    omega
  · by_cases hM1 : M.card = 1
    · obtain ⟨m0, hm0⟩ := card_eq_one.1 hM1
      have hm0_in : m0 ∈ supp 14 D (14 + P.1) ∧ m0 ∈ L6 :=
        mem_inter.1 (show m0 ∈ M from hm0 ▸ mem_singleton_self m0)
      have hm0_A : m0 ∈ supp 14 D (opA D P.1) := sem_supp_and_sub h.1 hjP_lt hP_and false hm0_in.1
      have hm0_B : m0 ∈ supp 14 D (opB D P.1) := sem_supp_and_sub h.1 hjP_lt hP_and true hm0_in.1
      have hjP_mer : P.1 ∈ merges 14 D (carrierT 14 D L6) := mem_filter.2 ⟨mem_range.2 hjP_lt,
        sup_mem_carrier.2 ⟨m0, mem_inter.2 hm0_in⟩,
        sup_mem_carrier.2 ⟨m0, mem_inter.2 ⟨hm0_A, hm0_in.2⟩⟩,
        sup_mem_carrier.2 ⟨m0, mem_inter.2 ⟨hm0_B, hm0_in.2⟩⟩⟩
      by_cases hjP_C : Sum.inr P.1 ∈ C
      ·
        obtain ⟨f0, hf0L, hf0c⟩ := mem_image.1 hjP_C
        have hf0_notS : f0 ∉ S_sing := fun hf0S => by
          have hsing := sup_wit_single (hwit f0 hf0L) (mem_filter.1 hf0S).2
          have hout := sup_wit_out h.1 (hwit f0 hf0L)
          rw [hsing, Finset.erase_singleton, Finset.subset_empty] at hout
          have hne := (sup_cost_inr hf0c).2
          rw [hout] at hne; exact not_nonempty_empty hne
        have hf0_sd : f0 ∈ L6 \ S_sing := mem_sdiff.2 ⟨hf0L, hf0_notS⟩
        have huniq : ∀ f ∈ L6 \ S_sing, sup_cost 14 D L6 (wit f) = Sum.inr P.1 → f = f0 := by
          intro f hf hfc
          by_contra hne
          have hfL := (mem_sdiff.1 hf).1
          have hw1 : (wit f).1 = P.1 := (sup_cost_inr hfc).1
          have hw0 : (wit f0).1 = P.1 := (sup_cost_inr hf0c).1
          have hneP : wit f ≠ P := fun hh => by have := (hwit f hfL).2.2.2.2.2.2; rw [hh] at this; omega
          have hneP0 : wit f0 ≠ P := fun hh => by have := (hwit f0 hf0L).2.2.2.2.2.2; rw [hh] at this; omega
          have hbar_of : ∀ e : ℕ × Bool, e.1 = P.1 → e ≠ P → e = sem_bar P := by
            intro ⟨j1, b1⟩ hj1 hne'
            apply Prod.ext
            · exact hj1
            · dsimp only [sem_bar]
              cases b1 <;> cases hP2 : P.2 <;> simp
              · exact hne' (Prod.ext hj1 hP2.symm)
              · exact hne' (Prod.ext hj1 hP2.symm)
          have hbar1 : wit f = sem_bar P := hbar_of (wit f) hw1 hneP
          have hbar0 : wit f0 = sem_bar P := hbar_of (wit f0) hw0 hneP0
          have hm0_bar : m0 ∈ supp 14 D (src D (sem_bar P)) ∩ L6 := by
            refine mem_inter.2 ⟨?_, hm0_in.2⟩
            have := sem_supp_and_sub h.1 hjP_lt hP_and (!P.2) hm0_in.1
            simpa [sem_bar] using this
          have hf_bar : f ∈ supp 14 D (src D (sem_bar P)) ∩ L6 := by
            rw [← hbar1]; exact mem_inter.2 ⟨(hwit f hfL).2.2.2.1, hfL⟩
          have hf0_bar : f0 ∈ supp 14 D (src D (sem_bar P)) ∩ L6 := by
            rw [← hbar0]; exact mem_inter.2 ⟨(hwit f0 hf0L).2.2.2.1, hf0L⟩
          have hm0_nef : m0 ≠ f := fun hh => (hwit f hfL).2.2.2.2.1 (hw1.symm ▸ hh ▸ hm0_in.1)
          have hm0_nef0 : m0 ≠ f0 := fun hh => (hwit f0 hf0L).2.2.2.2.1 (hw0.symm ▸ hh ▸ hm0_in.1)
          have h3 := pa_card3 hm0_bar hf_bar hf0_bar hm0_nef hm0_nef0 hne
          have hle2 := (hwit f hfL).2.2.2.2.2.2; rw [hbar1] at hle2; omega
        have h2er := sup_wit_card h.1 ((L6 \ S_sing).erase f0) (fun f => sem_g14_nb (ct f) ∩ L6) wit
          (fun f hf => hwit f (mem_sdiff.1 (Finset.mem_of_mem_erase hf)).1)
        have hnot_img : Sum.inr P.1 ∉ ((L6 \ S_sing).erase f0).image (fun f => sup_cost 14 D L6 (wit f)) := by
          intro hm; obtain ⟨f, hf, hfc⟩ := mem_image.1 hm
          exact (mem_erase.1 hf).1 (huniq f (Finset.mem_of_mem_erase hf) hfc)
        have hsub_img : insert (Sum.inr P.1) (((L6 \ S_sing).erase f0).image (fun f => sup_cost 14 D L6 (wit f))) ⊆
            (L6 \ S_sing).image (fun f => sup_cost 14 D L6 (wit f)) := by
          intro c hc
          rcases mem_insert.1 hc with rfl | hc'
          · exact mem_image.2 ⟨f0, hf0_sd, hf0c⟩
          · exact image_subset_image (Finset.erase_subset _ _) hc'
        have hcard_sd : (((L6 \ S_sing).erase f0).image (fun f => sup_cost 14 D L6 (wit f))).card + 1 ≤
            ((L6 \ S_sing).image (fun f => sup_cost 14 D L6 (wit f))).card := by
          have := card_le_card hsub_img; rw [card_insert_of_notMem hnot_img] at this; exact this
        have hSimg : (S_sing.image (fun f => sup_cost 14 D L6 (wit f))).card = S_sing.card :=
          card_image_of_injOn (fun f hf f' hf' heq => by
            by_contra hne
            exact sup_cost_ne_of_single h.1 (hwit f (hSL hf)) (hwit f' (hSL hf'))
              (sup_wit_single (hwit f (hSL hf)) (mem_filter.1 hf).2) hne heq)
        have hdSC : Disjoint (S_sing.image (fun f => sup_cost 14 D L6 (wit f)))
            ((L6 \ S_sing).image (fun f => sup_cost 14 D L6 (wit f))) := by
          rw [disjoint_left]; intro c hc1 hc2
          obtain ⟨f, hf, rfl⟩ := mem_image.1 hc1
          obtain ⟨f', hf', heq⟩ := mem_image.1 hc2
          rw [mem_sdiff] at hf'
          exact sup_cost_ne_of_single h.1 (hwit f (hSL hf)) (hwit f' hf'.1)
            (sup_wit_single (hwit f (hSL hf)) (mem_filter.1 hf).2) (fun hh => hf'.2 (hh ▸ hf)) heq.symm
        have hC_un : (S_sing.image (fun f => sup_cost 14 D L6 (wit f)) ∪
            (L6 \ S_sing).image (fun f => sup_cost 14 D L6 (wit f))).card ≤ C.card :=
          card_le_card (Finset.union_subset (image_subset_image hSL)
            (image_subset_image sdiff_subset))
        rw [card_union_of_disjoint hdSC, hSimg] at hC_un
        have herc := Finset.card_erase_of_mem hf0_sd
        have hpos_sd : 1 ≤ (L6 \ S_sing).card := card_pos.2 ⟨f0, hf0_sd⟩
        have hmd := sup_master_disj L6 E hEexit C hCok hCdis
        omega
      ·
        have hC'_ok : ∀ c ∈ insert (Sum.inr P.1) C, sup_CostOK 14 D L6 c := fun c hc => by
          rcases mem_insert.1 hc with rfl | hc'
          · exact ⟨hjP_mer, hM1⟩
          · exact hCok c hc'
        have hC'_dis : Disjoint E (insert (Sum.inr P.1) C).toLeft := by
          rw [disjoint_left]; intro e he hL
          rw [mem_toLeft, mem_insert] at hL
          rcases hL with h1 | h2
          · cases h1
          · exact disjoint_left.1 hCdis he (mem_toLeft.2 h2)
        have hmd := sup_master_disj L6 E hEexit (insert (Sum.inr P.1) C) hC'_ok hC'_dis
        rw [card_insert_of_notMem hjP_C, hEcard] at hmd
        omega
    ·
      have hM2 : 2 ≤ M.card := by omega
      set S_B : Finset (Fin 14) := supp 14 D (src D (sem_bar P)) ∩ L6
      have hM_sub_SB : M ⊆ S_B := fun x hx => by
        rw [mem_inter] at hx ⊢
        have := sem_supp_and_sub h.1 hjP_lt hP_and (!P.2) hx.1
        exact ⟨by simpa [sem_bar] using this, hx.2⟩
      have hSB2 : 2 ≤ S_B.card := hM2.trans (card_le_card hM_sub_SB)
      by_cases hSBM : S_B = M
      ·
        obtain ⟨jB, -, hjB_le, hjB_eq, hjB_mer, -, -⟩ :=
          sem_first_mask h.1 L6 M hM2 (src D (sem_bar P)) hSBM
        have hjB_big : jB ∈ sup_big 14 D L6 := mem_filter.2 ⟨hjB_mer, by rw [hjB_eq]; exact hM2⟩
        have hsrc_lt : src D (sem_bar P) < 14 + P.1 := by
          obtain ⟨ha, hb, -⟩ := h.1 P.1 hjP_lt
          cases hbP : P.2 <;> simp [sem_bar, src, hbP] <;> assumption
        have hjB_ne : jB ≠ P.1 := by omega
        obtain ⟨m0, hm0⟩ := card_pos.1 (by omega : 0 < M.card)
        have hm0_in := mem_inter.1 hm0
        have hjP_big : P.1 ∈ sup_big 14 D L6 := mem_filter.2 ⟨mem_filter.2 ⟨mem_range.2 hjP_lt,
          sup_mem_carrier.2 ⟨m0, hm0⟩,
          sup_mem_carrier.2 ⟨m0, mem_inter.2 ⟨sem_supp_and_sub h.1 hjP_lt hP_and false hm0_in.1, hm0_in.2⟩⟩,
          sup_mem_carrier.2 ⟨m0, mem_inter.2 ⟨sem_supp_and_sub h.1 hjP_lt hP_and true hm0_in.1, hm0_in.2⟩⟩⟩, hM2⟩
        have hF_er : F ⊆ ((sup_big 14 D L6).erase P.1).image (fun j => supp 14 D (14 + j) ∩ L6) := by
          intro T hT
          by_cases hTM : T = M
          · rw [hTM]; exact mem_image.2 ⟨jB, mem_erase.2 ⟨hjB_ne, hjB_big⟩, hjB_eq⟩
          · obtain ⟨j, hj, hjT⟩ := sup_occ_big h.1 (hF_ok T hT).1 (hF_ok T hT).2
            exact mem_image.2 ⟨j, mem_erase.2 ⟨fun hje => hTM (hjT.symm.trans (hje ▸ rfl)), hj⟩, hjT⟩
        have hbig_5 : 5 + ((L6 \ S_sing).image pr).card ≤ (sup_big 14 D L6).card := by
          have h1 := (card_le_card hF_er).trans Finset.card_image_le
          rw [Finset.card_erase_of_mem hjP_big, hF_card] at h1
          have hpos : 1 ≤ (sup_big 14 D L6).card := card_pos.2 ⟨P.1, hjP_big⟩
          omega
        have hmd := sup_master_disj L6 E hEexit C hCok hCdis
        omega
      ·
        have hSB3 : 3 ≤ S_B.card := by
          have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hM_sub_SB, Ne.symm hSBM⟩); omega
        have hx0_notSB : x0 ∉ S_B := fun hx0SB => by
          have h1 : x0 ∈ supp 14 D (src D P) := (mem_inter.1 (hS3_sub_P hx0)).1
          have h2 : x0 ∈ supp 14 D (src D (sem_bar P)) := (mem_inter.1 hx0SB).1
          have h3 : x0 ∈ supp 14 D (14 + P.1) := by
            rw [sem_supp_and h.1 hjP_lt hP_and, mem_inter]
            cases hbP : P.2 <;> simp [sem_bar, src, hbP] at h1 h2 ⊢ <;> exact ⟨by assumption, by assumption⟩
          exact (sem_mem_W.1 hx0_W).2.2 h3
        have hSB_neT0 : S_B ≠ T0 := fun hh => hx0_notSB (hh.symm ▸ hS3_sub_T0 hx0)
        have hSB_notF : S_B ∉ F := by
          intro hm
          rcases mem_insert.1 hm with h1 | h2
          · exact hSB_neT0 h1
          · rcases mem_union.1 h2 with h2a | h2b
            · have := (hL2_c2 S_B h2a).1; omega
            · obtain ⟨f, hf, hprf⟩ := mem_image.1 h2b
              have := (hpr f hf).2.1; rw [hprf] at this; omega
        have hbig_5 := sup_card_le_big h.1 L6 (insert S_B F) (fun T hT => by
          rcases mem_insert.1 hT with rfl | hT'
          · exact ⟨by omega, ⟨src D (sem_bar P), rfl⟩⟩
          · exact hF_ok T hT')
        rw [card_insert_of_notMem hSB_notF, hF_card] at hbig_5
        have hmd := sup_master_disj L6 E hEexit C hCok hCdis
        omega
theorem elim_res2_adj_w3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (idx : Fin 157) (hI : ineligSet 14 D = hc_rep idx)
    (hge5 : 97 ≤ idx.val) (hc5 : (ineligSet 14 D).card = 5)
    (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (w1 w2 a1 a2 b1 b2 qa1 qa2 z k v iz ik : Fin 14)
    (hw1 : w1 ∈ eligSet 14 D) (hw2 : w2 ∈ eligSet 14 D)
    (ha1 : a1 ∈ ineligSet 14 D) (ha2 : a2 ∈ ineligSet 14 D)
    (hb1 : b1 ∈ ineligSet 14 D) (hb2 : b2 ∈ ineligSet 14 D)
    (hiz : iz ∈ ineligSet 14 D) (hik : ik ∈ ineligSet 14 D)
    (hw1n : w1 ∉ ineligSet 14 D) (hw2n : w2 ∉ ineligSet 14 D)
    (hz : z ∉ ineligSet 14 D) (hk : k ∉ ineligSet 14 D) (hv : v ∉ ineligSet 14 D)
    (hg : a1 ≠ 0 ∧ a2 ≠ 0 ∧ b1 ≠ 0 ∧ b2 ≠ 0 ∧ iz ≠ 0 ∧ ik ≠ 0 ∧
      w1 ≠ w2 ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
      w1 ≠ z ∧ w1 ≠ k ∧ w2 ≠ z ∧ w2 ≠ k ∧
      (g14_nbB w1).card = 3 ∧ (g14_nbB w2).card = 3 ∧
      hc_adjB a1 w1 = true ∧ hc_adjB a2 w1 = true ∧ hc_adjB w1 w2 = true ∧
      hc_adjB b1 w2 = true ∧ hc_adjB b2 w2 = true ∧
      hc_adjB a1 qa1 = true ∧ w1 ≠ qa1 ∧ hc_adjB w2 qa1 = false ∧
      hc_adjB a2 qa2 = true ∧ w1 ≠ qa2 ∧ hc_adjB w2 qa2 = false ∧
      hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧ hc_adjB z v = true ∧
      v ≠ k ∧ (g14_nbB k).card = 3 ∧ decide (v.val < 7) = decide (k.val < 7))
    (hq1 : ∀ t : Fin 14, (t = w2 ∨ t = z ∨ t = k) →
      ∃ q : Fin 14,
        (hc_adjB a1 q = true ∧ w1 ≠ q ∧ hc_adjB t q = false ∧ hc_adjB a1 t = false) ∨
        (hc_adjB a2 q = true ∧ w1 ≠ q ∧ hc_adjB t q = false ∧ hc_adjB a2 t = false))
    (hq2 : ∀ t : Fin 14, (t = w1 ∨ t = z ∨ t = k) →
      ∃ q : Fin 14,
        (hc_adjB b1 q = true ∧ w2 ≠ q ∧ hc_adjB t q = false ∧ hc_adjB b1 t = false) ∨
        (hc_adjB b2 q = true ∧ w2 ≠ q ∧ hc_adjB t q = false ∧ hc_adjB b2 t = false)) : False := by
  classical
  have hBgt := bplus_gt_p1_ge5 h hD h11 idx hI hge5
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hmin⟩ := exists_weakMinBranch14 h hD
  have hbr : PureBranch 14 D br := weak_to_pure br (weakMinBranch_pure hmin) h0I
  obtain ⟨pos, hpos⟩ := k4_assigned14 h hD
  have hR2 : (residualUnits 14 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  obtain ⟨ha10, ha20, hb10, hb20, hiz0, hik0, hw12, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12,
    hw1z, hw1k, hw2z, hw2k, hdw1, hdw2, ga1, ga2, gw12, gb1, gb2,
    gqa1, hqa1, gw2q1, gqa2, hqa2, gw2q2, giz, gik, gzk, gzv, hvk, hdk, hsvk⟩ := hg
  have gw21 : hc_adjB w2 w1 = true := (hc_adjB_iff _ _).2 (adj_symm ((hc_adjB_iff _ _).1 gw12))
  have hw1n' : 1 ≤ (ru D br w1).card := by
    have h3 := two_in_deg3 h hD hpos ha1 ha2 hw2n ⟨ha10, ha20, ha12, ga1, ga2, gw12⟩
    have hc := cc_le h hD br hbr w1; omega
  have hw2n' : 1 ≤ (ru D br w2).card := by
    have h3 := two_in_deg3 h hD hpos hb1 hb2 hw1n ⟨hb10, hb20, hb12, gb1, gb2, gw21⟩
    have hc := cc_le h hD br hbr w2; omega
  have hw1le : (ru D br w1).card ≤ 2 := (card_le_card (filter_subset _ _)).trans_eq hR2
  have hw2le : (ru D br w2).card ≤ 2 := (card_le_card (filter_subset _ _)).trans_eq hR2
  by_cases h2_2 : (ru D br w2).card = 2
  · have hw2R : ru D br w2 = residualUnits 14 D br :=
      eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    exact pe_co_blow5 h hD br hbr hpos w1 w2 a1 a2 qa1 qa2 b1 b2 w1
      hw1 ha1 ha2 hb1 hb2 hw1n
      ⟨ha10, ha20, hb10, hb20, hw12, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12,
        hdw1, ga1, ga2, gqa1, hqa1, gw2q1, gqa2, hqa2, gw2q2, gb1, gb2, gw21⟩
      hw1n' ((filter_subset _ _).trans hw2R.symm.subset) hw2le
  · have h2_1 : (ru D br w2).card = 1 := by omega
    by_cases h1_2 : (ru D br w1).card = 2
    · have hw1R : ru D br w1 = residualUnits 14 D br :=
        eq_of_subset_of_card_le (filter_subset _ _) (by omega)
      exact ru_sub_excl h hD hB0 br hbr hpos hb1 hb2 hw2 hw1n
        ⟨hb10, hb20, hdw2, hb12, gb1, gb2, gw21⟩ h2_1
        ((filter_subset _ _).trans hw1R.symm.subset) hw12.symm (hq2 w1 (Or.inl rfl))
    · have h1_1 : (ru D br w1).card = 1 := by omega
      obtain ⟨u1, hu1⟩ := card_eq_one.1 h1_1
      obtain ⟨u2, hu2⟩ := card_eq_one.1 h2_1
      have hu_ne : u1 ≠ u2 := fun hh =>
        ru_sub_excl h hD hB0 br hbr hpos ha1 ha2 hw1 hw2n
          ⟨ha10, ha20, hdw1, ha12, ga1, ga2, gw12⟩ h1_1
          (by rw [hu1, hu2, hh]) hw12 (hq1 w2 (Or.inl rfl))
      have hRu : residualUnits 14 D br = {u1, u2} := by
        symm
        refine eq_of_subset_of_card_le (fun u hu => ?_) (by rw [card_pair hu_ne, hR2])
        rw [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact (filter_subset _ _) (hu1 ▸ mem_singleton_self _)
        · exact (filter_subset _ _) (hu2 ▸ mem_singleton_self _)
      have hru_emp : ∀ t : Fin 14, (t = z ∨ t = k) → (sem_W 14 D t).card ≤ 2 := by
        intro t ht
        have ht1 : w1 ≠ t := ht.elim (fun h' => h' ▸ hw1z) (fun h' => h' ▸ hw1k)
        have ht2 : w2 ≠ t := ht.elim (fun h' => h' ▸ hw2z) (fun h' => h' ▸ hw2k)
        have hemp : ru D br t = ∅ := by
          apply eq_empty_iff_forall_notMem.2
          intro u hu
          have huR : u ∈ residualUnits 14 D br := (filter_subset _ _) hu
          rw [hRu, mem_insert, mem_singleton] at huR
          rcases huR with rfl | rfl
          · exact ru_sub_excl h hD hB0 br hbr hpos ha1 ha2 hw1 hw2n
              ⟨ha10, ha20, hdw1, ha12, ga1, ga2, gw12⟩ h1_1
              (by rw [hu1, singleton_subset_iff]; exact hu) ht1 (hq1 t (Or.inr ht))
          · exact ru_sub_excl h hD hB0 br hbr hpos hb1 hb2 hw2 hw1n
              ⟨hb10, hb20, hdw2, hb12, gb1, gb2, gw21⟩ h2_1
              (by rw [hu2, singleton_subset_iff]; exact hu) ht2 (hq2 t (Or.inr ht))
        have hc := cc_le h hD br hbr t
        rw [hemp, card_empty] at hc; omega
      exact pa_m1 h hD hpos z k v iz ik hiz hik hz hk hv
        ⟨giz, gik, gzk, gzv, hvk, hdk, hsvk, hiz0, hik0⟩
        (hru_emp z (Or.inl rfl)) (hru_emp k (Or.inr rfl))
theorem elim_102 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨102, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,1,2,10,11} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0,1,2,10,11} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_adj_w3 h hD h11 ⟨102, by decide⟩ hI (by decide) (by rw [hIeq]; decide) (mI hIeq) 4 13 10 11 1 2 0 3 3 12 7 11 2 (hE 4 (by decide)) (hE 13 (by decide)) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by decide +kernel) (by decide +kernel)
theorem elim_107 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨107, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,1,4,8,12} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0,1,4,8,12} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_adj_w3 h hD h11 ⟨107, by decide⟩ hI (by decide) (by rw [hIeq]; decide) (mI hIeq) 2 13 8 12 1 4 6 3 3 11 7 12 4 (hE 2 (by decide)) (hE 13 (by decide)) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by decide +kernel) (by decide +kernel)
theorem elim_res2_share_w3 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (idx : Fin 157) (hI : ineligSet 14 D = hc_rep idx)
    (hge5 : 97 ≤ idx.val) (hc5 : (ineligSet 14 D).card = 5)
    (h0I : (0 : Fin 14) ∈ ineligSet 14 D)
    (w1 w2 ish oa ob v1 v2 qa qb z k v iz ik : Fin 14)
    (hw1 : w1 ∈ eligSet 14 D) (hw2 : w2 ∈ eligSet 14 D)
    (hish : ish ∈ ineligSet 14 D) (hoa : oa ∈ ineligSet 14 D) (hob : ob ∈ ineligSet 14 D)
    (hiz : iz ∈ ineligSet 14 D) (hik : ik ∈ ineligSet 14 D)
    (hv1 : v1 ∉ ineligSet 14 D) (hv2 : v2 ∉ ineligSet 14 D)
    (hz : z ∉ ineligSet 14 D) (hk : k ∉ ineligSet 14 D) (hv : v ∉ ineligSet 14 D)
    (hg : ish ≠ 0 ∧ oa ≠ 0 ∧ ob ≠ 0 ∧ iz ≠ 0 ∧ ik ≠ 0 ∧
      w1 ≠ w2 ∧ ish ≠ oa ∧ ish ≠ ob ∧ oa ≠ ob ∧ v2 ≠ ob ∧
      w1 ≠ z ∧ w1 ≠ k ∧ w2 ≠ z ∧ w2 ≠ k ∧
      (g14_nbB w1).card = 3 ∧ (g14_nbB w2).card = 3 ∧
      hc_adjB ish w1 = true ∧ hc_adjB oa w1 = true ∧ hc_adjB w1 v1 = true ∧
      hc_adjB ish w2 = true ∧ hc_adjB ob w2 = true ∧ hc_adjB w2 v2 = true ∧
      hc_adjB oa qa = true ∧ w1 ≠ qa ∧ hc_adjB w2 qa = false ∧
      hc_adjB ob qb = true ∧ w2 ≠ qb ∧ hc_adjB w1 qb = false ∧
      hc_adjB ob w1 = false ∧
      hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧ hc_adjB z v = true ∧
      v ≠ k ∧ (g14_nbB k).card = 3 ∧ decide (v.val < 7) = decide (k.val < 7))
    (hq1 : ∀ t : Fin 14, (t = w2 ∨ t = z ∨ t = k) →
      ∃ q : Fin 14,
        (hc_adjB ish q = true ∧ w1 ≠ q ∧ hc_adjB t q = false ∧ hc_adjB ish t = false) ∨
        (hc_adjB oa q = true ∧ w1 ≠ q ∧ hc_adjB t q = false ∧ hc_adjB oa t = false))
    (hq2 : ∀ t : Fin 14, (t = w1 ∨ t = z ∨ t = k) →
      ∃ q : Fin 14,
        (hc_adjB ish q = true ∧ w2 ≠ q ∧ hc_adjB t q = false ∧ hc_adjB ish t = false) ∨
        (hc_adjB ob q = true ∧ w2 ≠ q ∧ hc_adjB t q = false ∧ hc_adjB ob t = false)) : False := by
  classical
  have hBgt := bplus_gt_p1_ge5 h hD h11 idx hI hge5
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hmin⟩ := exists_weakMinBranch14 h hD
  have hbr : PureBranch 14 D br := weak_to_pure br (weakMinBranch_pure hmin) h0I
  obtain ⟨pos, hpos⟩ := k4_assigned14 h hD
  have hR2 : (residualUnits 14 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  obtain ⟨h0sh, h0oa, h0ob, h0iz, h0ik, hw12, hshoa, hshob, hoaob, hv2ob,
    hw1z, hw1k, hw2z, hw2k, hdw1, hdw2, gsh1, goa1, gv1, gsh2, gob2, gv2,
    gqa, hqa, gw2qa, gqb, hqb, gw1qb, gnob1, giz, gik, gzk, gzv, hvk, hdk, hsvk⟩ := hg
  have hw1n : 1 ≤ (ru D br w1).card := by
    have h3 := two_in_deg3 h hD hpos hish hoa hv1 ⟨h0sh, h0oa, hshoa, gsh1, goa1, gv1⟩
    have hc := cc_le h hD br hbr w1; omega
  have hw2n : 1 ≤ (ru D br w2).card := by
    have h3 := two_in_deg3 h hD hpos hish hob hv2 ⟨h0sh, h0ob, hshob, gsh2, gob2, gv2⟩
    have hc := cc_le h hD br hbr w2; omega
  have hw1le : (ru D br w1).card ≤ 2 := (card_le_card (filter_subset _ _)).trans_eq hR2
  have hw2le : (ru D br w2).card ≤ 2 := (card_le_card (filter_subset _ _)).trans_eq hR2
  by_cases h1_2 : (ru D br w1).card = 2
  · have hw1R : ru D br w1 = residualUnits 14 D br :=
      eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    by_cases h2_2 : (ru D br w2).card = 2
    · have hw2R : ru D br w2 = residualUnits 14 D br :=
        eq_of_subset_of_card_le (filter_subset _ _) (by omega)
      have heq : ru D br w1 = ru D br w2 := hw1R.trans hw2R.symm
      obtain ⟨u, hu⟩ := card_pos.1 (by omega : 0 < (ru D br w1).card)
      have hres1 : ∀ u' ∈ residualUnits 14 D br, w1 ∈ supp 14 D u'.1 → w2 ∈ supp 14 D u'.1 := by
        intro u' hu' ha'; have hm : u' ∈ ru D br w1 := mem_filter.2 ⟨hu', ha'⟩
        rw [heq] at hm; exact (mem_filter.1 hm).2
      have hres2 : ∀ u' ∈ residualUnits 14 D br, w2 ∈ supp 14 D u'.1 → w1 ∈ supp 14 D u'.1 := by
        intro u' hu' hb'; have hm : u' ∈ ru D br w2 := mem_filter.2 ⟨hu', hb'⟩
        rw [← heq] at hm; exact (mem_filter.1 hm).2
      have hw : w1 ∈ supp 14 D u.1 ∧ w2 ∈ supp 14 D u.1 :=
        ⟨(mem_filter.1 hu).2, (mem_filter.1 (show u ∈ ru D br w2 from heq ▸ hu)).2⟩
      have hpoa_in_w2 := mem_W_of_pos hpos hoa h0oa
        (pe_co_g14 h hD br hbr hpos hoa hw1 hres1 hw ⟨h0oa, hdw1, goa1, gqa, hw12, hqa, gw2qa⟩)
      have hw1_in_pob := pe_co_g14 h hD br hbr hpos hob hw2 hres2 ⟨hw.2, hw.1⟩ ⟨h0ob, hdw2, gob2, gqb, hw12.symm, hqb, gw1qb⟩
      have hpsh_in_w2 := as_mem hpos hish h0sh ((hc_adjB_iff _ _).1 gsh2)
      have hpob_in_w2 := as_mem hpos hob h0ob ((hc_adjB_iff _ _).1 gob2)
      obtain ⟨ev2, hev2, hbev2, hfv2, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gv2)
      have hWw2_le4 : (sem_W 14 D w2).card ≤ 4 := by have := cc_le h hD br hbr w2; omega
      have hWw2 := pa_four hpob_in_w2 hpsh_in_w2 hpoa_in_w2 hev2
        (fun e => hshob.symm (hpos.2.2 _ hob _ hish e))
        (fun e => hoaob.symm (hpos.2.2 _ hob _ hoa e))
        (fun e => hv2 (hfv2 _ hob h0ob e.symm ▸ hob))
        (fun e => hshoa (hpos.2.2 _ hish _ hoa e))
        (fun e => hv2 (hfv2 _ hish h0sh e.symm ▸ hish))
        (fun e => hv2 (hfv2 _ hoa h0oa e.symm ▸ hoa)) hWw2_le4
      have hfull := full_g14 h hD hB0 hpos hob h0ob ((hc_adjB_iff _ _).1 gob2) (fun p hp hne1 hsub => by
        rcases hWw2 p hp with rfl | rfl | rfl | rfl
        · exact hne1 rfl
        · have hm : ish ∈ supp 14 D (src D (sem_bar (pos ish))) := by
            rw [show src D (sem_bar (pos ish)) = src D ((pos ish).1, !(pos ish).2) from rfl,
              (hpos.1 ish hish h0sh).2.2.2]; exact mem_singleton_self ish
          exact hshob (mem_singleton.1 (hsub hm))
        · have hm : oa ∈ supp 14 D (src D (sem_bar (pos oa))) := by
            rw [show src D (sem_bar (pos oa)) = src D ((pos oa).1, !(pos oa).2) from rfl,
              (hpos.1 oa hoa h0oa).2.2.2]; exact mem_singleton_self oa
          exact hoaob (mem_singleton.1 (hsub hm))
        · exact hv2ob (mem_singleton.1 (hsub (sem_mem_W.1 hbev2).2.1)))
      exact sem_adjB_false.1 gnob1 ((hfull w1).1 hw1_in_pob)
    · have h2_1 : (ru D br w2).card = 1 := by omega
      exact ru_sub_excl h hD hB0 br hbr hpos hish hob hw2 hv2
        ⟨h0sh, h0ob, hdw2, hshob, gsh2, gob2, gv2⟩ h2_1
        ((filter_subset _ _).trans hw1R.symm.subset) hw12.symm (hq2 w1 (Or.inl rfl))
  · have h1_1 : (ru D br w1).card = 1 := by omega
    by_cases h2_2 : (ru D br w2).card = 2
    · have hw2R : ru D br w2 = residualUnits 14 D br :=
        eq_of_subset_of_card_le (filter_subset _ _) (by omega)
      exact ru_sub_excl h hD hB0 br hbr hpos hish hoa hw1 hv1
        ⟨h0sh, h0oa, hdw1, hshoa, gsh1, goa1, gv1⟩ h1_1
        ((filter_subset _ _).trans hw2R.symm.subset) hw12 (hq1 w2 (Or.inl rfl))
    · have h2_1 : (ru D br w2).card = 1 := by omega
      obtain ⟨u1, hu1⟩ := card_eq_one.1 h1_1
      obtain ⟨u2, hu2⟩ := card_eq_one.1 h2_1
      have hu_ne : u1 ≠ u2 := fun hh =>
        ru_sub_excl h hD hB0 br hbr hpos hish hoa hw1 hv1
          ⟨h0sh, h0oa, hdw1, hshoa, gsh1, goa1, gv1⟩ h1_1
          (by rw [hu1, hu2, hh]) hw12 (hq1 w2 (Or.inl rfl))
      have hRu : residualUnits 14 D br = {u1, u2} := by
        symm
        refine eq_of_subset_of_card_le (fun u hu => ?_) (by rw [card_pair hu_ne, hR2])
        rw [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact (filter_subset _ _) (hu1 ▸ mem_singleton_self _)
        · exact (filter_subset _ _) (hu2 ▸ mem_singleton_self _)
      have hru_emp : ∀ t : Fin 14, (t = z ∨ t = k) → (sem_W 14 D t).card ≤ 2 := by
        intro t ht
        have ht1 : w1 ≠ t := ht.elim (fun h' => h' ▸ hw1z) (fun h' => h' ▸ hw1k)
        have ht2 : w2 ≠ t := ht.elim (fun h' => h' ▸ hw2z) (fun h' => h' ▸ hw2k)
        have hemp : ru D br t = ∅ := by
          apply eq_empty_iff_forall_notMem.2
          intro u hu
          have huR : u ∈ residualUnits 14 D br := (filter_subset _ _) hu
          rw [hRu, mem_insert, mem_singleton] at huR
          rcases huR with rfl | rfl
          · exact ru_sub_excl h hD hB0 br hbr hpos hish hoa hw1 hv1
              ⟨h0sh, h0oa, hdw1, hshoa, gsh1, goa1, gv1⟩ h1_1
              (by rw [hu1, singleton_subset_iff]; exact hu) ht1 (hq1 t (Or.inr ht))
          · exact ru_sub_excl h hD hB0 br hbr hpos hish hob hw2 hv2
              ⟨h0sh, h0ob, hdw2, hshob, gsh2, gob2, gv2⟩ h2_1
              (by rw [hu2, singleton_subset_iff]; exact hu) ht2 (hq2 t (Or.inr ht))
        have hc := cc_le h hD br hbr t
        rw [hemp, card_empty] at hc; omega
      exact pa_m1 h hD hpos z k v iz ik hiz hik hz hk hv
        ⟨giz, gik, gzk, gzv, hvk, hdk, hsvk, h0iz, h0ik⟩
        (hru_emp z (Or.inl rfl)) (hru_emp k (Or.inr rfl))
theorem elim_99 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨99, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,1,2,3,10} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0,1,2,3,10} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_share_w3 h hD h11 ⟨99, by decide⟩ hI (by decide) (by rw [hIeq]; decide) (mI hIeq) 12 13 2 3 1 5 4 11 9 4 11 13 10 3 (hE 12 (by decide)) (hE 13 (by decide)) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by decide +kernel) (by decide +kernel)
theorem elim_104 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨104, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,1,3,4,8} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0,1,3,4,8} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_share_w3 h hD h11 ⟨104, by decide⟩ hI (by decide) (by rw [hIeq]; decide) (mI hIeq) 11 13 4 3 1 6 2 12 9 2 12 13 8 3 (hE 11 (by decide)) (hE 13 (by decide)) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by decide +kernel) (by decide +kernel)
theorem elim_108 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨108, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,1,8,10,11} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0,1,8,10,11} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_share_w3 h hD h11 ⟨108, by decide⟩ hI (by decide) (by rw [hIeq]; decide) (mI hIeq) 4 6 11 10 8 13 9 0 2 2 13 12 8 1 (hE 4 (by decide)) (hE 6 (by decide)) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by decide +kernel) (by decide +kernel)
theorem elim_112 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨112, by decide⟩) : False := by
  have hIeq : ineligSet 14 D = {0,4,7,8,9} := by rw [hI]; decide +kernel
  have hE : ∀ x : Fin 14, x ∉ ({0,4,7,8,9} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  exact elim_res2_share_w3 h hD h11 ⟨112, by decide⟩ hI (by decide) (by rw [hIeq]; decide) (mI hIeq) 1 6 9 7 8 13 11 3 2 2 13 12 8 4 (hE 1 (by decide)) (hE 6 (by decide)) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (mI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (nI hIeq) (by decide) (by decide +kernel) (by decide +kernel)
theorem elim_111 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨111, by decide⟩) : False := by
  classical
  have hIeq : ineligSet 14 D = {0, 4, 5, 7, 8} := by rw [hI]; decide +kernel
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h4I : (4 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h5I : (5 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h7I : (7 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h8I : (8 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have hE : ∀ x : Fin 14, x ∉ ({0, 4, 5, 7, 8} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt := bplus_gt_p1_ge5 h hD h11 ⟨111, by decide⟩ hI (by decide)
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hc5 : (ineligSet 14 D).card = 5 := by rw [hIeq]; decide
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hminW⟩ := exists_weakMinBranch14 h hD
  have hmin : sem_MinBranch 14 D br := weakMin_to_min hminW h0I
  have hbr : PureBranch 14 D br := weak_to_pure br (weakMinBranch_pure hminW) h0I
  obtain ⟨pos, hpos⟩ := k4_assigned14 h hD
  have hR2 : (residualUnits 14 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  have h10n : 1 ≤ (ru D br 10).card := by
    have h3 := pa_card3 (as_mem0 hpos h0I)
      (as_mem hpos h4I (by decide) (by decide : Adj 4 10))
      (as_mem hpos h5I (by decide) (by decide : Adj 5 10))
      (fun e => (by decide : (0 : Fin 14) ≠ 4) (hpos.2.2 _ h0I _ h4I e))
      (fun e => (by decide : (0 : Fin 14) ≠ 5) (hpos.2.2 _ h0I _ h5I e))
      (fun e => (by decide : (4 : Fin 14) ≠ 5) (hpos.2.2 _ h4I _ h5I e))
    have hc := cc_le h hD br hbr 10; omega
  have hle2 : ∀ v : Fin 14, (ru D br v).card ≤ 2 := fun v =>
    (card_le_card (filter_subset _ _)).trans_eq hR2
  have hR_of2 : ∀ v : Fin 14, (ru D br v).card = 2 → ru D br v = residualUnits 14 D br := fun v hv =>
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  let hpush := r2_push h hD br hbr hpos
  let hne00 := r2_ne00 h hD br hbr hpos
  let hsame1 := r2_same1 h hD hB0 br hbr hpos
  let hom2_edges := r2_hom2_edges h hD br hbr hpos
  let hom2_full1 := r2_hom2_full1 h hD hB0 br hbr hpos
  let hom2_R_full := r2_hom2_R_full h hD hB0 br hbr hpos hR2
  let hR_blow5 := r2_blow5 h hD br hbr hpos hR2
  have h10_no_same : ∀ (x ix qx : Fin 14),
      ix ∈ ineligSet 14 D → x ∈ eligSet 14 D →
      (ix ≠ 0 ∧ (g14_nbB x).card = 3 ∧ hc_adjB ix x = true ∧ hc_adjB ix qx = true ∧
        x ≠ 10 ∧ x ≠ qx ∧ hc_adjB 10 qx = false ∧ ix ≠ 4 ∧ ix ≠ 5) →
      (ru D br 10).card = 1 → (ru D br x).Nonempty → ru D br x ⊆ ru D br 10 → False := by
    intro x ix qx hix hx hg h10_1 hxn hsub
    obtain ⟨hix0, hdx, gix, gqx, hx10, hxq, g10q, hix4, hix5⟩ := hg
    have hpx := mem_W_of_pos hpos hix hix0 (hpush x 10 ix qx hix hx ⟨hix0, hdx, gix, gqx, hx10, hxq, g10q⟩ hxn hsub)
    have h4 := pa_card4 (as_mem0 hpos h0I)
      (as_mem hpos h4I (by decide) (by decide : Adj 4 10))
      (as_mem hpos h5I (by decide) (by decide : Adj 5 10)) hpx
      (fun e => (by decide : (0 : Fin 14) ≠ 4) (hpos.2.2 _ h0I _ h4I e))
      (fun e => (by decide : (0 : Fin 14) ≠ 5) (hpos.2.2 _ h0I _ h5I e))
      (fun e => hix0.symm (hpos.2.2 _ h0I _ hix e))
      (fun e => (by decide : (4 : Fin 14) ≠ 5) (hpos.2.2 _ h4I _ h5I e))
      (fun e => hix4.symm (hpos.2.2 _ h4I _ hix e))
      (fun e => hix5.symm (hpos.2.2 _ h5I _ hix e))
    have hc := cc_le h hD br hbr 10; omega
  have h10_no_both : ∀ (x7 q7 x8 q8 : Fin 14),
      x7 ∈ eligSet 14 D → x8 ∈ eligSet 14 D →
      ((g14_nbB x7).card = 3 ∧ hc_adjB 7 x7 = true ∧ hc_adjB 7 q7 = true ∧
        x7 ≠ 10 ∧ x7 ≠ q7 ∧ hc_adjB 10 q7 = false ∧
       (g14_nbB x8).card = 3 ∧ hc_adjB 8 x8 = true ∧ hc_adjB 8 q8 = true ∧
        x8 ≠ 10 ∧ x8 ≠ q8 ∧ hc_adjB 10 q8 = false) →
      (ru D br 10).card = 2 → (ru D br x7).Nonempty → (ru D br x8).Nonempty → False := by
    intro x7 q7 x8 q8 hx7 hx8 hg h10_2 hx7n hx8n
    obtain ⟨hd7, g7, gq7, hx710, hxq7, g10q7, hd8, g8, gq8, hx810, hxq8, g10q8⟩ := hg
    have h10R := hR_of2 10 h10_2
    have hp7 := mem_W_of_pos hpos h7I (by decide) (hpush x7 10 7 q7 h7I hx7 ⟨by decide, hd7, g7, gq7, hx710, hxq7, g10q7⟩ hx7n
      ((filter_subset _ _).trans h10R.symm.subset))
    have hp8 := mem_W_of_pos hpos h8I (by decide) (hpush x8 10 8 q8 h8I hx8 ⟨by decide, hd8, g8, gq8, hx810, hxq8, g10q8⟩ hx8n
      ((filter_subset _ _).trans h10R.symm.subset))
    have h5 := pa_card5 (as_mem0 hpos h0I)
      (as_mem hpos h4I (by decide) (by decide : Adj 4 10))
      (as_mem hpos h5I (by decide) (by decide : Adj 5 10)) hp7 hp8
      (fun e => (by decide : (0 : Fin 14) ≠ 4) (hpos.2.2 _ h0I _ h4I e))
      (fun e => (by decide : (0 : Fin 14) ≠ 5) (hpos.2.2 _ h0I _ h5I e))
      (fun e => (by decide : (0 : Fin 14) ≠ 7) (hpos.2.2 _ h0I _ h7I e))
      (fun e => (by decide : (0 : Fin 14) ≠ 8) (hpos.2.2 _ h0I _ h8I e))
      (fun e => (by decide : (4 : Fin 14) ≠ 5) (hpos.2.2 _ h4I _ h5I e))
      (fun e => (by decide : (4 : Fin 14) ≠ 7) (hpos.2.2 _ h4I _ h7I e))
      (fun e => (by decide : (4 : Fin 14) ≠ 8) (hpos.2.2 _ h4I _ h8I e))
      (fun e => (by decide : (5 : Fin 14) ≠ 7) (hpos.2.2 _ h5I _ h7I e))
      (fun e => (by decide : (5 : Fin 14) ≠ 8) (hpos.2.2 _ h5I _ h8I e))
      (fun e => (by decide : (7 : Fin 14) ≠ 8) (hpos.2.2 _ h7I _ h8I e))
    have hc := cc_le h hD br hbr 10; omega
  have hRside_ne0 : ∀ (v iv x7 x8 n7 n8 q7 q8 : Fin 14),
      iv ∈ ineligSet 14 D → v ∉ ineligSet 14 D →
      x7 ∈ eligSet 14 D → x8 ∈ eligSet 14 D →
      x7 ∉ ineligSet 14 D → x8 ∉ ineligSet 14 D → n7 ∉ ineligSet 14 D → n8 ∉ ineligSet 14 D →
      (v ≠ n7 ∧ v ≠ n8 ∧ iv ≠ 0 ∧ (g14_nbB v).card = 3 ∧ (g14_nbB x7).card = 3 ∧ (g14_nbB x8).card = 3 ∧
        v ≠ 7 ∧ n7 ≠ 7 ∧ v ≠ 8 ∧ n8 ≠ 8 ∧ x7 ≠ x8 ∧ x7 ≠ 10 ∧ x8 ≠ 10 ∧ x7 ≠ q7 ∧ x8 ≠ q8 ∧
        hc_adjB iv v = true ∧ hc_adjB 7 x7 = true ∧ hc_adjB 8 x8 = true ∧
        hc_adjB x7 v = true ∧ hc_adjB x7 n7 = true ∧ hc_adjB x8 v = true ∧ hc_adjB x8 n8 = true ∧
        decide (v.val < 7) = decide (n7.val < 7) ∧ decide (v.val < 7) = decide (n8.val < 7) ∧
        hc_adjB 7 q7 = true ∧ hc_adjB 10 q7 = false ∧ hc_adjB x8 q7 = false ∧ hc_adjB 7 x8 = false ∧
        hc_adjB 8 q8 = true ∧ hc_adjB 10 q8 = false ∧ hc_adjB x7 q8 = false ∧ hc_adjB 8 x7 = false) →
      (ru D br v).Nonempty := by
    intro v iv x7 x8 n7 n8 q7 q8 hiv hv hx7 hx8 hx7' hx8' hn7 hn8 hg
    obtain ⟨hvn7, hvn8, hiv0, hdv, hd7, hd8, hv7, hn77, hv8, hn88, h78, hx710, hx810, hxq7, hxq8,
      giv, g7, g8, gx7v, gx7n, gx8v, gx8n, hsn7, hsn8, gq7, g10q7, gx8q7, gn78, gq8, g10q8, gx7q8, gn87⟩ := hg
    by_contra hve
    have hv0 : ru D br v = ∅ := not_nonempty_iff_eq_empty.1 hve
    have hx7n : (ru D br x7).Nonempty := by
      by_contra hc; exact hne00 x7 v n7 7 iv h7I hiv hx7' hv hn7
        ⟨g7, giv, gx7v, gx7n, hvn7.symm, hdv, hsn7.symm, by decide, hiv0⟩ (not_nonempty_iff_eq_empty.1 hc) hv0
    have hx8n : (ru D br x8).Nonempty := by
      by_contra hc; exact hne00 x8 v n8 8 iv h8I hiv hx8' hv hn8
        ⟨g8, giv, gx8v, gx8n, hvn8.symm, hdv, hsn8.symm, by decide, hiv0⟩ (not_nonempty_iff_eq_empty.1 hc) hv0
    have h10_1 : (ru D br 10).card = 1 := by
      have hne2 : (ru D br 10).card ≠ 2 := fun h2 =>
        h10_no_both x7 q7 x8 q8 hx7 hx8 ⟨hd7, g7, gq7, hx710, hxq7, g10q7, hd8, g8, gq8, hx810, hxq8, g10q8⟩
          h2 hx7n hx8n
      have := hle2 10; omega
    obtain ⟨ra, rb, hrab, hRpair⟩ := Finset.card_eq_two.1 hR2
    obtain ⟨u10, hu10⟩ := card_eq_one.1 h10_1
    have hu10R : u10 ∈ residualUnits 14 D br := (filter_subset _ _) (hu10 ▸ mem_singleton_self _)
    have hother : ∃ u' ∈ residualUnits 14 D br, u' ≠ u10 ∧ residualUnits 14 D br = {u10, u'} := by
      rw [hRpair, mem_insert, mem_singleton] at hu10R
      rcases hu10R with rfl | rfl
      · exact ⟨rb, by rw [hRpair]; simp, hrab.symm, hRpair⟩
      · exact ⟨ra, by rw [hRpair]; simp, hrab, by rw [hRpair, Finset.pair_comm]⟩
    obtain ⟨u', hu'R, hu'ne, hRu'⟩ := hother
    have hmem_u' : ∀ (x ix qx : Fin 14),
        ix ∈ ineligSet 14 D → x ∈ eligSet 14 D →
        (ix ≠ 0 ∧ (g14_nbB x).card = 3 ∧ hc_adjB ix x = true ∧ hc_adjB ix qx = true ∧
          x ≠ 10 ∧ x ≠ qx ∧ hc_adjB 10 qx = false ∧ ix ≠ 4 ∧ ix ≠ 5) →
        (ru D br x).Nonempty → u' ∈ ru D br x := by
      intro x ix qx hix hx hgx hxn
      obtain ⟨w, hw⟩ := hxn
      have hwR : w ∈ residualUnits 14 D br := (filter_subset _ _) hw
      rw [hRu', mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · by_contra hnu'
        have hsub : ru D br x ⊆ ru D br 10 := by
          intro z hz
          have hzR : z ∈ residualUnits 14 D br := (filter_subset _ _) hz
          rw [hRu', mem_insert, mem_singleton] at hzR
          rcases hzR with rfl | rfl
          · rw [hu10]; exact mem_singleton_self _
          · exact absurd hz hnu'
        exact h10_no_same x ix qx hix hx hgx h10_1 ⟨w, hw⟩ hsub
      · exact hw
    have hu'7 : u' ∈ ru D br x7 := hmem_u' x7 7 q7 h7I hx7
      ⟨by decide, hd7, g7, gq7, hx710, hxq7, g10q7, by decide, by decide⟩ hx7n
    have hu'8 : u' ∈ ru D br x8 := hmem_u' x8 8 q8 h8I hx8
      ⟨by decide, hd8, g8, gq8, hx810, hxq8, g10q8, by decide, by decide⟩ hx8n
    have hx7_2 : (ru D br x7).card = 2 := by
      have hne1 : (ru D br x7).card ≠ 1 := fun h1 => by
        have h7eq : ru D br x7 = {u'} := eq_singleton_iff_unique_mem.2 ⟨hu'7, fun z hz => by
          obtain ⟨a, ha⟩ := card_eq_one.1 h1
          exact (mem_singleton.1 (ha ▸ hz)).trans (mem_singleton.1 (ha ▸ hu'7)).symm⟩
        exact hom2_full1 x7 7 v iv n7 x8 q7 h7I hiv hx7 hx7' hv hn7
          ⟨hvn7, by decide, hiv0, hd7, hdv, hv7, hn77, h78, hxq7, g7, giv, gx7v, gx7n, hsn7, gq7, gx8q7, gn78⟩
          hv0 h1 (by rw [h7eq, singleton_subset_iff]; exact hu'8)
      have := hle2 x7; have := card_pos.2 hx7n; omega
    have hx8_2 : (ru D br x8).card = 2 := by
      have hne1 : (ru D br x8).card ≠ 1 := fun h1 => by
        have h8eq : ru D br x8 = {u'} := eq_singleton_iff_unique_mem.2 ⟨hu'8, fun z hz => by
          obtain ⟨a, ha⟩ := card_eq_one.1 h1
          exact (mem_singleton.1 (ha ▸ hz)).trans (mem_singleton.1 (ha ▸ hu'8)).symm⟩
        exact hom2_full1 x8 8 v iv n8 x7 q8 h8I hiv hx8 hx8' hv hn8
          ⟨hvn8, by decide, hiv0, hd8, hdv, hv8, hn88, h78.symm, hxq8, g8, giv, gx8v, gx8n, hsn8, gq8, gx7q8, gn87⟩
          hv0 h1 (by rw [h8eq, singleton_subset_iff]; exact hu'7)
      have := hle2 x8; have := card_pos.2 hx8n; omega
    exact hom2_R_full x7 7 v iv n7 x8 8 q8 x8 q7 h7I hiv h8I hx7 hx8 hx7' hv hn7
      ⟨hvn7, by decide, hiv0, by decide, hd7, hdv, hd8, by decide, hv7, hn77, h78.symm, hxq8, h78, hxq7,
        g7, giv, g8, gx7v, gx7n, hsn7, gq8, gx7q8, gq7, gx8q7, gn78⟩
      hv0 hx7_2 hx8n hx8_2
  have h9n : (ru D br 9).Nonempty := hRside_ne0 9 5 1 6 13 11 3 2 h5I (by rw [hIeq]; decide)
    (hE 1 (by decide)) (hE 6 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  have h11n : (ru D br 11).Nonempty := hRside_ne0 11 4 3 6 12 9 1 2 h4I (by rw [hIeq]; decide)
    (hE 3 (by decide)) (hE 6 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  have h12n : (ru D br 12).Nonempty := hRside_ne0 12 5 3 2 11 13 1 6 h5I (by rw [hIeq]; decide)
    (hE 3 (by decide)) (hE 2 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  have h13n : (ru D br 13).Nonempty := hRside_ne0 13 4 1 2 9 12 3 6 h4I (by rw [hIeq]; decide)
    (hE 1 (by decide)) (hE 2 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
    (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
  have hkill_if_L0 : ∀ (x ix r4 r5 n4 n5 : Fin 14),
      ix ∈ ineligSet 14 D → x ∉ ineligSet 14 D →
      r4 ∈ eligSet 14 D → r5 ∈ eligSet 14 D →
      r4 ∉ ineligSet 14 D → r5 ∉ ineligSet 14 D → n4 ∉ ineligSet 14 D → n5 ∉ ineligSet 14 D →
      (x ≠ n4 ∧ x ≠ n5 ∧ ix ≠ 0 ∧ (g14_nbB x).card = 3 ∧ (g14_nbB r4).card = 3 ∧ (g14_nbB r5).card = 3 ∧
        x ≠ 4 ∧ n4 ≠ 4 ∧ x ≠ 5 ∧ n5 ≠ 5 ∧ r4 ≠ r5 ∧ r4 ≠ 10 ∧ r5 ≠ 10 ∧
        hc_adjB ix x = true ∧ hc_adjB 4 r4 = true ∧ hc_adjB 5 r5 = true ∧
        hc_adjB r4 x = true ∧ hc_adjB r4 n4 = true ∧ hc_adjB r5 x = true ∧ hc_adjB r5 n5 = true ∧
        decide (x.val < 7) = decide (n4.val < 7) ∧ decide (x.val < 7) = decide (n5.val < 7) ∧
        hc_adjB r5 10 = false ∧ hc_adjB 4 r5 = false ∧ hc_adjB r4 10 = false ∧ hc_adjB 5 r4 = false ∧
        r4 ≠ 1 ∧ r4 ≠ 2 ∧ r4 ≠ 3 ∧ r4 ≠ 6 ∧ r5 ≠ 1 ∧ r5 ≠ 2 ∧ r5 ≠ 3 ∧ r5 ≠ 6) →
      (ru D br r4).Nonempty → (ru D br r5).Nonempty → ru D br x = ∅ → False := by
    intro x ix r4 r5 n4 n5 hix hx hr4 hr5 hr4' hr5' hn4 hn5 hg hr4n hr5n hx0
    obtain ⟨hxn4, hxn5, hix0, hdx, hd4, hd5, hx4, hn44, hx5, hn55, h45, h410, h510,
      gix, g4, g5, gr4x, gr4n, gr5x, gr5n, hsn4, hsn5, gr510, gn4r5, gr410, gn5r4,
      h41, h42, h43, h46, h51, h52, h53, h56⟩ := hg
    have h4_1 : (ru D br r4).card = 1 := by
      have hne2 : (ru D br r4).card ≠ 2 := fun h42' => by
        by_cases h52' : (ru D br r5).card = 2
        · exact hom2_R_full r4 4 x ix n4 r5 5 10 r5 10 h4I hix h5I hr4 hr5 hr4' hx hn4
            ⟨hxn4, by decide, hix0, by decide, hd4, hdx, hd5, by decide, hx4, hn44, h45.symm, h510, h45, h410,
              g4, gix, g5, gr4x, gr4n, hsn4, by decide, gr410, by decide, gr510, gn4r5⟩
            hx0 h42' hr5n h52'
        · have h5_1 : (ru D br r5).card = 1 := by have := hle2 r5; have := card_pos.2 hr5n; omega
          exact hom2_full1 r5 5 x ix n5 r4 10 h5I hix hr5 hr5' hx hn5
            ⟨hxn5, by decide, hix0, hd5, hdx, hx5, hn55, h45.symm, h510, g5, gix, gr5x, gr5n, hsn5, by decide, gr410, gn5r4⟩
            hx0 h5_1 ((filter_subset _ _).trans (hR_of2 r4 h42').symm.subset)
      have := hle2 r4; have := card_pos.2 hr4n; omega
    have h5_1 : (ru D br r5).card = 1 := by
      have hne2 : (ru D br r5).card ≠ 2 := fun h52' =>
        hom2_full1 r4 4 x ix n4 r5 10 h4I hix hr4 hr4' hx hn4
          ⟨hxn4, by decide, hix0, hd4, hdx, hx4, hn44, h45, h410, g4, gix, gr4x, gr4n, hsn4, by decide, gr510, gn4r5⟩
          hx0 h4_1 ((filter_subset _ _).trans (hR_of2 r5 h52').symm.subset)
      have := hle2 r5; have := card_pos.2 hr5n; omega
    obtain ⟨u4, hu4⟩ := card_eq_one.1 h4_1
    obtain ⟨u5, hu5⟩ := card_eq_one.1 h5_1
    have hu45 : u4 ≠ u5 := fun hh =>
      hom2_full1 r4 4 x ix n4 r5 10 h4I hix hr4 hr4' hx hn4
        ⟨hxn4, by decide, hix0, hd4, hdx, hx4, hn44, h45, h410, g4, gix, gr4x, gr4n, hsn4, by decide, gr510, gn4r5⟩
        hx0 h4_1 (by rw [hu4, hu5, hh])
    have hRu45 : residualUnits 14 D br = {u4, u5} := by
      symm
      refine eq_of_subset_of_card_le (fun u hu => ?_) (by rw [card_pair hu45, hR2])
      rw [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact (filter_subset _ _) (hu4 ▸ mem_singleton_self _)
      · exact (filter_subset _ _) (hu5 ▸ mem_singleton_self _)
    have hL0 : ∀ y : Fin 14, (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 6) → ru D br y = ∅ := by
      intro y hy
      have hy4 : r4 ≠ y := by rcases hy with rfl | rfl | rfl | rfl <;> assumption
      have hy5 : r5 ≠ y := by rcases hy with rfl | rfl | rfl | rfl <;> assumption
      have hy10 : hc_adjB y 10 = false := by rcases hy with rfl | rfl | rfl | rfl <;> decide
      have gn4y : hc_adjB 4 y = false := by rcases hy with rfl | rfl | rfl | rfl <;> decide
      have gn5y : hc_adjB 5 y = false := by rcases hy with rfl | rfl | rfl | rfl <;> decide
      apply eq_empty_iff_forall_notMem.2
      intro u hu
      have huR : u ∈ residualUnits 14 D br := (filter_subset _ _) hu
      rw [hRu45, mem_insert, mem_singleton] at huR
      rcases huR with rfl | rfl
      · exact hom2_full1 r4 4 x ix n4 y 10 h4I hix hr4 hr4' hx hn4
          ⟨hxn4, by decide, hix0, hd4, hdx, hx4, hn44, hy4, h410, g4, gix, gr4x, gr4n, hsn4, by decide, hy10, gn4y⟩
          hx0 h4_1 (by rw [hu4, singleton_subset_iff]; exact hu)
      · exact hom2_full1 r5 5 x ix n5 y 10 h5I hix hr5 hr5' hx hn5
          ⟨hxn5, by decide, hix0, hd5, hdx, hx5, hn55, hy5, h510, g5, gix, gr5x, gr5n, hsn5, by decide, hy10, gn5y⟩
          hx0 h5_1 (by rw [hu5, singleton_subset_iff]; exact hu)
    have h1_0 : ru D br 1 = ∅ := hL0 1 (by decide)
    have h2_0 : ru D br 2 = ∅ := hL0 2 (by decide)
    have h3_0 : ru D br 3 = ∅ := hL0 3 (by decide)
    have h6_0 : ru D br 6 = ∅ := hL0 6 (by decide)
    have h11_1 : (ru D br 11).card = 1 := by
      have hne2 : (ru D br 11).card ≠ 2 := fun h2 =>
        hom2_full1 r5 5 x ix n5 11 10 h5I hix hr5 hr5' hx hn5
          ⟨hxn5, by decide, hix0, hd5, hdx, hx5, hn55, by rintro rfl; exact (by decide : hc_adjB 5 11 = false) ▸ g5 |> Bool.noConfusion,
            h510, g5, gix, gr5x, gr5n, hsn5, by decide, by decide, by decide⟩
          hx0 h5_1 ((filter_subset _ _).trans (hR_of2 11 h2).symm.subset)
      have := hle2 11; have := card_pos.2 h11n; omega
    have h13_1 : (ru D br 13).card = 1 := by
      have hne2 : (ru D br 13).card ≠ 2 := fun h2 =>
        hom2_full1 r5 5 x ix n5 13 10 h5I hix hr5 hr5' hx hn5
          ⟨hxn5, by decide, hix0, hd5, hdx, hx5, hn55, by rintro rfl; exact (by decide : hc_adjB 5 13 = false) ▸ g5 |> Bool.noConfusion,
            h510, g5, gix, gr5x, gr5n, hsn5, by decide, by decide, by decide⟩
          hx0 h5_1 ((filter_subset _ _).trans (hR_of2 13 h2).symm.subset)
      have := hle2 13; have := card_pos.2 h13n; omega
    have h11_eq : ru D br 11 = {u4} := by
      obtain ⟨w, hw⟩ := card_eq_one.1 h11_1
      have hwR : w ∈ residualUnits 14 D br := (filter_subset _ _) (hw ▸ mem_singleton_self _)
      rw [hRu45, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact hw
      · exact absurd (hom2_full1 r5 5 x ix n5 11 10 h5I hix hr5 hr5' hx hn5
          ⟨hxn5, by decide, hix0, hd5, hdx, hx5, hn55, by rintro rfl; exact (by decide : hc_adjB 5 11 = false) ▸ g5 |> Bool.noConfusion,
            h510, g5, gix, gr5x, gr5n, hsn5, by decide, by decide, by decide⟩
          hx0 h5_1 (by rw [hu5, hw])) id
    have h13_eq : ru D br 13 = {u4} := by
      obtain ⟨w, hw⟩ := card_eq_one.1 h13_1
      have hwR : w ∈ residualUnits 14 D br := (filter_subset _ _) (hw ▸ mem_singleton_self _)
      rw [hRu45, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact hw
      · exact absurd (hom2_full1 r5 5 x ix n5 13 10 h5I hix hr5 hr5' hx hn5
          ⟨hxn5, by decide, hix0, hd5, hdx, hx5, hn55, by rintro rfl; exact (by decide : hc_adjB 5 13 = false) ▸ g5 |> Bool.noConfusion,
            h510, g5, gix, gr5x, gr5n, hsn5, by decide, by decide, by decide⟩
          hx0 h5_1 (by rw [hu5, hw])) id
    obtain ⟨e11_3, e11_6, he11_3, he11_6, h11ne, -, -, hf11_3, hf11_6⟩ :=
      hom2_edges 11 4 3 7 6 h4I h7I (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h3_0
    obtain ⟨e13_1, e13_2, he13_1, he13_2, h13ne, -, -, hf13_1, hf13_2⟩ :=
      hom2_edges 13 4 1 7 2 h4I h7I (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h1_0
    have hW11_3 : 3 ≤ (sem_W 14 D 11).card :=
      pa_card3 (as_mem hpos h4I (by decide) (by decide : Adj 4 11)) he11_3 he11_6
        (fun e => (by rw [hIeq]; decide : (3 : Fin 14) ∉ _) (hf11_3 4 h4I (by decide) e.symm ▸ h4I))
        (fun e => (by rw [hIeq]; decide : (6 : Fin 14) ∉ _) (hf11_6 4 h4I (by decide) e.symm ▸ h4I)) h11ne
    have hW13_3 : 3 ≤ (sem_W 14 D 13).card :=
      pa_card3 (as_mem hpos h4I (by decide) (by decide : Adj 4 13)) he13_1 he13_2
        (fun e => (by rw [hIeq]; decide : (1 : Fin 14) ∉ _) (hf13_1 4 h4I (by decide) e.symm ▸ h4I))
        (fun e => (by rw [hIeq]; decide : (2 : Fin 14) ∉ _) (hf13_2 4 h4I (by decide) e.symm ▸ h4I)) h13ne
    have hm11 : merges 14 D (carrierT 14 D {11}) = ∅ := card_eq_zero.1 (by have := cc_le h hD br hbr 11; omega)
    have hm13 : merges 14 D (carrierT 14 D {13}) = ∅ := card_eq_zero.1 (by have := cc_le h hD br hbr 13; omega)
    have hu4R : u4 ∈ residualUnits 14 D br := (filter_subset _ _) (hu4 ▸ mem_singleton_self _)
    obtain ⟨P, Q, hPQ1, hPQsat⟩ := gct_gen sem_g14_gr h (sem_g14_comp hD) br hmin hu4R
      ({11, 13} : Finset (Fin 14)) (by simp) (fun z hz => by
        rw [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · refine ⟨hm11, ru_mem (h11_eq ▸ mem_singleton_self _), fun u hu hzu => ?_⟩
          have hm : u ∈ ru D br 11 := mem_filter.2 ⟨hu, hzu⟩; rw [h11_eq, mem_singleton] at hm; exact hm
        · refine ⟨hm13, ru_mem (h13_eq ▸ mem_singleton_self _), fun u hu hzu => ?_⟩
          have hm : u ∈ ru D br 13 := mem_filter.2 ⟨hu, hzu⟩; rw [h13_eq, mem_singleton] at hm; exact hm)
    have hPQ : P ≠ Q := fun hh => hPQ1 (congrArg Prod.fst hh)
    have hW11_le3 : (sem_W 14 D 11).card ≤ 3 := by have := cc_le h hD br hbr 11; omega
    have hW13_le3 : (sem_W 14 D 13).card ≤ 3 := by have := cc_le h hD br hbr 13; omega
    have hc1 : (sem_W 14 D 1).card ≤ 2 := by have := cc_le h hD br hbr 1; rw [h1_0, card_empty] at this; omega
    have hc2 : (sem_W 14 D 2).card ≤ 2 := by have := cc_le h hD br hbr 2; rw [h2_0, card_empty] at this; omega
    have hc3 : (sem_W 14 D 3).card ≤ 2 := by have := cc_le h hD br hbr 3; rw [h3_0, card_empty] at this; omega
    have hc6 : (sem_W 14 D 6).card ≤ 2 := by have := cc_le h hD br hbr 6; rw [h6_0, card_empty] at this; omega
    exact elim_disj_ps_pair h hD hpos hPQ 11 13 4 4 3 6 1 2 7 8 7 8
      h4I h4I h7I h8I h7I h8I
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) hW11_le3 hW13_le3 hc3 hc6 hc1 hc2
      (hPQsat 11 (by simp)).1 (hPQsat 11 (by simp)).2 (hPQsat 13 (by simp)).1 (hPQsat 13 (by simp)).2
  have h1n : (ru D br 1).Nonempty := by
    by_contra hc; exact hkill_if_L0 1 7 13 9 2 6 h7I (by rw [hIeq]; decide) (hE 13 (by decide)) (hE 9 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      h13n h9n (not_nonempty_iff_eq_empty.1 hc)
  have h2n : (ru D br 2).Nonempty := by
    by_contra hc; exact hkill_if_L0 2 8 13 12 1 3 h8I (by rw [hIeq]; decide) (hE 13 (by decide)) (hE 12 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      h13n h12n (not_nonempty_iff_eq_empty.1 hc)
  have h3n : (ru D br 3).Nonempty := by
    by_contra hc; exact hkill_if_L0 3 7 11 12 6 2 h7I (by rw [hIeq]; decide) (hE 11 (by decide)) (hE 12 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      h11n h12n (not_nonempty_iff_eq_empty.1 hc)
  have h6n : (ru D br 6).Nonempty := by
    by_contra hc; exact hkill_if_L0 6 8 11 9 3 1 h8I (by rw [hIeq]; decide) (hE 11 (by decide)) (hE 9 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      h11n h9n (not_nonempty_iff_eq_empty.1 hc)
  have h9_1 : (ru D br 9).card = 1 := by
    have hne2 : (ru D br 9).card ≠ 2 := fun h2 =>
      hR_blow5 9 5 1 1 7 3 6 8 2 11 4 10 h5I h7I h8I h4I
        (hE 1 (by decide)) (hE 6 (by decide)) (hE 11 (by decide)) (by rw [hIeq]; decide) (by decide) h2 h1n h6n h11n
    have := hle2 9; have := card_pos.2 h9n; omega
  have h13_1 : (ru D br 13).card = 1 := by
    have hne2 : (ru D br 13).card ≠ 2 := fun h2 =>
      hR_blow5 13 4 1 1 7 3 2 8 6 9 5 10 h4I h7I h8I h5I
        (hE 1 (by decide)) (hE 2 (by decide)) (hE 9 (by decide)) (by rw [hIeq]; decide) (by decide) h2 h1n h2n h9n
    have := hle2 13; have := card_pos.2 h13n; omega
  obtain ⟨u13, hu13⟩ := card_eq_one.1 h13_1
  obtain ⟨u9, hu9⟩ := card_eq_one.1 h9_1
  have hu_ne : u13 ≠ u9 := fun hh =>
    hsame1 13 9 4 5 1 10 10 h4I h5I (hE 13 (by decide)) (hE 9 (by decide)) (by rw [hIeq]; decide)
      (by decide) h9_1 (by rw [hu13, hu9, hh])
  have hRu : residualUnits 14 D br = {u13, u9} := by
    symm
    refine eq_of_subset_of_card_le (fun u hu => ?_) (by rw [card_pair hu_ne, hR2])
    rw [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (filter_subset _ _) (hu13 ▸ mem_singleton_self _)
    · exact (filter_subset _ _) (hu9 ▸ mem_singleton_self _)
  have h1_2 : (ru D br 1).card = 2 := by
    have hne1 : (ru D br 1).card ≠ 1 := fun h1 => by
      obtain ⟨w, hw⟩ := card_eq_one.1 h1
      have hwR : w ∈ residualUnits 14 D br := (filter_subset _ _) (hw ▸ mem_singleton_self _)
      rw [hRu, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact hsame1 1 13 7 4 2 3 10 h7I h4I (hE 1 (by decide)) (hE 13 (by decide)) (by rw [hIeq]; decide)
          (by decide) h13_1 (by rw [hw, hu13])
      · exact hsame1 1 9 7 5 6 3 10 h7I h5I (hE 1 (by decide)) (hE 9 (by decide)) (by rw [hIeq]; decide)
          (by decide) h9_1 (by rw [hw, hu9])
    have := hle2 1; have := card_pos.2 h1n; omega
  exact hR_blow5 1 7 9 2 8 6 13 4 10 9 5 10 h7I h8I h4I h5I
    (hE 2 (by decide)) (hE 13 (by decide)) (hE 9 (by decide)) (by rw [hIeq]; decide) (by decide) h1_2 h2n h13n h9n
theorem elim_105 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h11 : totalSurplus 14 D ≤ 11) (hI : ineligSet 14 D = hc_rep ⟨105, by decide⟩) : False := by
  classical
  have hIeq : ineligSet 14 D = {0, 1, 3, 8, 10} := by rw [hI]; decide +kernel
  have h0I : (0 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h1I : (1 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h3I : (3 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h8I : (8 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have h10I : (10 : Fin 14) ∈ ineligSet 14 D := by rw [hIeq]; decide
  have hE : ∀ x : Fin 14, x ∉ ({0, 1, 3, 8, 10} : Finset (Fin 14)) → x ∈ eligSet 14 D := fun x hx => by
    by_contra hc; exact hx (hIeq ▸ sem_mem_inelig.2 hc)
  have hBgt := bplus_gt_p1_ge5 h hD h11 ⟨105, by decide⟩ hI (by decide)
  have hel := inelig_card_add 14 D
  have hts := totalSurplus_split 14 D
  have hc5 : (ineligSet 14 D).card = 5 := by rw [hIeq]; decide
  have hB0 : Bzero 14 D = 0 := by omega
  obtain ⟨br, hminW⟩ := exists_weakMinBranch14 h hD
  have hmin : sem_MinBranch 14 D br := weakMin_to_min hminW h0I
  have hbr : PureBranch 14 D br := weak_to_pure br (weakMinBranch_pure hminW) h0I
  obtain ⟨pos, hpos⟩ := k4_assigned14 h hD
  have hR2 : (residualUnits 14 D br).card = 2 := by have := card_residual h.1 br hbr; omega
  have hle2 : ∀ v : Fin 14, (ru D br v).card ≤ 2 := fun v =>
    (card_le_card (filter_subset _ _)).trans_eq hR2
  have hR_of2 : ∀ v : Fin 14, (ru D br v).card = 2 → ru D br v = residualUnits 14 D br := fun v hv =>
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  let hpush := r2_push h hD br hbr hpos
  let hne00 := r2_ne00 h hD br hbr hpos
  let hsame1 := r2_same1 h hD hB0 br hbr hpos
  let hom2_edges := r2_hom2_edges h hD br hbr hpos
  let hom2_full1 := r2_hom2_full1 h hD hB0 br hbr hpos
  let hom2_R_full := r2_hom2_R_full h hD hB0 br hbr hpos hR2
  let hR_blow5 := r2_blow5 h hD br hbr hpos hR2
  have hkill_if_L0 : ∀ (x ix r1 r3 n1 n3 : Fin 14),
      ix ∈ ineligSet 14 D → x ∉ ineligSet 14 D →
      r1 ∈ eligSet 14 D → r3 ∈ eligSet 14 D →
      r1 ∉ ineligSet 14 D → r3 ∉ ineligSet 14 D → n1 ∉ ineligSet 14 D → n3 ∉ ineligSet 14 D →
      (x ≠ n1 ∧ x ≠ n3 ∧ ix ≠ 0 ∧ (g14_nbB x).card = 3 ∧ (g14_nbB r1).card = 3 ∧ (g14_nbB r3).card = 3 ∧
        x ≠ 1 ∧ n1 ≠ 1 ∧ x ≠ 3 ∧ n3 ≠ 3 ∧ r1 ≠ r3 ∧ r1 ≠ 7 ∧ r3 ≠ 7 ∧
        hc_adjB ix x = true ∧ hc_adjB 1 r1 = true ∧ hc_adjB 3 r3 = true ∧
        hc_adjB r1 x = true ∧ hc_adjB r1 n1 = true ∧ hc_adjB r3 x = true ∧ hc_adjB r3 n3 = true ∧
        decide (x.val < 7) = decide (n1.val < 7) ∧ decide (x.val < 7) = decide (n3.val < 7) ∧
        hc_adjB r3 7 = false ∧ hc_adjB 1 r3 = false ∧ hc_adjB r1 7 = false ∧ hc_adjB 3 r1 = false ∧
        r1 ≠ 2 ∧ r1 ≠ 4 ∧ r1 ≠ 5 ∧ r1 ≠ 6 ∧ r3 ≠ 2 ∧ r3 ≠ 4 ∧ r3 ≠ 5 ∧ r3 ≠ 6) →
      ru D br x = ∅ → False := by
    intro x ix r1 r3 n1 n3 hix hx hr1 hr3 hr1' hr3' hn1 hn3 hg hx0
    obtain ⟨hxn1, hxn3, hix0, hdx, hd1, hd3, hx1, hn11, hx3, hn33, h13, h17, h37,
      gix, g1, g3, gr1x, gr1n, gr3x, gr3n, hsn1, hsn3, gr37, gn1r3, gr17, gn3r1,
      h12, h14, h15, h16, h32, h34, h35, h36⟩ := hg
    have hr1n : (ru D br r1).Nonempty := by
      by_contra hc; exact hne00 r1 x n1 1 ix h1I hix hr1' hx hn1
        ⟨g1, gix, gr1x, gr1n, hxn1.symm, hdx, hsn1.symm, by decide, hix0⟩ (not_nonempty_iff_eq_empty.1 hc) hx0
    have hr3n : (ru D br r3).Nonempty := by
      by_contra hc; exact hne00 r3 x n3 3 ix h3I hix hr3' hx hn3
        ⟨g3, gix, gr3x, gr3n, hxn3.symm, hdx, hsn3.symm, by decide, hix0⟩ (not_nonempty_iff_eq_empty.1 hc) hx0
    have h1_1 : (ru D br r1).card = 1 := by
      have hne2 : (ru D br r1).card ≠ 2 := fun h12' => by
        by_cases h32' : (ru D br r3).card = 2
        · exact hom2_R_full r1 1 x ix n1 r3 3 7 r3 7 h1I hix h3I hr1 hr3 hr1' hx hn1
            ⟨hxn1, by decide, hix0, by decide, hd1, hdx, hd3, by decide, hx1, hn11, h13.symm, h37, h13, h17,
              g1, gix, g3, gr1x, gr1n, hsn1, by decide, gr17, by decide, gr37, gn1r3⟩
            hx0 h12' hr3n h32'
        · have h3_1 : (ru D br r3).card = 1 := by have := hle2 r3; have := card_pos.2 hr3n; omega
          exact hom2_full1 r3 3 x ix n3 r1 7 h3I hix hr3 hr3' hx hn3
            ⟨hxn3, by decide, hix0, hd3, hdx, hx3, hn33, h13.symm, h37, g3, gix, gr3x, gr3n, hsn3, by decide, gr17, gn3r1⟩
            hx0 h3_1 ((filter_subset _ _).trans (hR_of2 r1 h12').symm.subset)
      have := hle2 r1; have := card_pos.2 hr1n; omega
    have h3_1 : (ru D br r3).card = 1 := by
      have hne2 : (ru D br r3).card ≠ 2 := fun h32' =>
        hom2_full1 r1 1 x ix n1 r3 7 h1I hix hr1 hr1' hx hn1
          ⟨hxn1, by decide, hix0, hd1, hdx, hx1, hn11, h13, h17, g1, gix, gr1x, gr1n, hsn1, by decide, gr37, gn1r3⟩
          hx0 h1_1 ((filter_subset _ _).trans (hR_of2 r3 h32').symm.subset)
      have := hle2 r3; have := card_pos.2 hr3n; omega
    obtain ⟨u1, hu1⟩ := card_eq_one.1 h1_1
    obtain ⟨u3, hu3⟩ := card_eq_one.1 h3_1
    have hu13 : u1 ≠ u3 := fun hh =>
      hom2_full1 r1 1 x ix n1 r3 7 h1I hix hr1 hr1' hx hn1
        ⟨hxn1, by decide, hix0, hd1, hdx, hx1, hn11, h13, h17, g1, gix, gr1x, gr1n, hsn1, by decide, gr37, gn1r3⟩
        hx0 h1_1 (by rw [hu1, hu3, hh])
    have hRu13 : residualUnits 14 D br = {u1, u3} := by
      symm
      refine eq_of_subset_of_card_le (fun u hu => ?_) (by rw [card_pair hu13, hR2])
      rw [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact (filter_subset _ _) (hu1 ▸ mem_singleton_self _)
      · exact (filter_subset _ _) (hu3 ▸ mem_singleton_self _)
    have hL0 : ∀ y : Fin 14, (y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 6) → ru D br y = ∅ := by
      intro y hy
      have hy1 : r1 ≠ y := by rcases hy with rfl | rfl | rfl | rfl <;> assumption
      have hy3 : r3 ≠ y := by rcases hy with rfl | rfl | rfl | rfl <;> assumption
      have hy7 : hc_adjB y 7 = false := by rcases hy with rfl | rfl | rfl | rfl <;> decide
      have gn1y : hc_adjB 1 y = false := by rcases hy with rfl | rfl | rfl | rfl <;> decide
      have gn3y : hc_adjB 3 y = false := by rcases hy with rfl | rfl | rfl | rfl <;> decide
      apply eq_empty_iff_forall_notMem.2
      intro u hu
      have huR : u ∈ residualUnits 14 D br := (filter_subset _ _) hu
      rw [hRu13, mem_insert, mem_singleton] at huR
      rcases huR with rfl | rfl
      · exact hom2_full1 r1 1 x ix n1 y 7 h1I hix hr1 hr1' hx hn1
          ⟨hxn1, by decide, hix0, hd1, hdx, hx1, hn11, hy1, h17, g1, gix, gr1x, gr1n, hsn1, by decide, hy7, gn1y⟩
          hx0 h1_1 (by rw [hu1, singleton_subset_iff]; exact hu)
      · exact hom2_full1 r3 3 x ix n3 y 7 h3I hix hr3 hr3' hx hn3
          ⟨hxn3, by decide, hix0, hd3, hdx, hx3, hn33, hy3, h37, g3, gix, gr3x, gr3n, hsn3, by decide, hy7, gn3y⟩
          hx0 h3_1 (by rw [hu3, singleton_subset_iff]; exact hu)
    have h2_0 : ru D br 2 = ∅ := hL0 2 (by decide)
    have h4_0 : ru D br 4 = ∅ := hL0 4 (by decide)
    have h5_0 : ru D br 5 = ∅ := hL0 5 (by decide)
    have h6_0 : ru D br 6 = ∅ := hL0 6 (by decide)
    have h9n : (ru D br 9).Nonempty := by
      by_contra hc; exact hne00 9 5 6 1 10 h1I h10I (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) (not_nonempty_iff_eq_empty.1 hc) h5_0
    have h13n : (ru D br 13).Nonempty := by
      by_contra hc; exact hne00 13 2 4 1 8 h1I h8I (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
        (by decide) (not_nonempty_iff_eq_empty.1 hc) h2_0
    have h9_1 : (ru D br 9).card = 1 := by
      have hne2 : (ru D br 9).card ≠ 2 := fun h2 =>
        hom2_full1 r3 3 x ix n3 9 7 h3I hix hr3 hr3' hx hn3
          ⟨hxn3, by decide, hix0, hd3, hdx, hx3, hn33, by rintro rfl; exact (by decide : hc_adjB 3 9 = false) ▸ g3 |> Bool.noConfusion,
            h37, g3, gix, gr3x, gr3n, hsn3, by decide, by decide, by decide⟩
          hx0 h3_1 ((filter_subset _ _).trans (hR_of2 9 h2).symm.subset)
      have := hle2 9; have := card_pos.2 h9n; omega
    have h13_1 : (ru D br 13).card = 1 := by
      have hne2 : (ru D br 13).card ≠ 2 := fun h2 =>
        hom2_full1 r3 3 x ix n3 13 7 h3I hix hr3 hr3' hx hn3
          ⟨hxn3, by decide, hix0, hd3, hdx, hx3, hn33, by rintro rfl; exact (by decide : hc_adjB 3 13 = false) ▸ g3 |> Bool.noConfusion,
            h37, g3, gix, gr3x, gr3n, hsn3, by decide, by decide, by decide⟩
          hx0 h3_1 ((filter_subset _ _).trans (hR_of2 13 h2).symm.subset)
      have := hle2 13; have := card_pos.2 h13n; omega
    have h9_eq : ru D br 9 = {u1} := by
      obtain ⟨w, hw⟩ := card_eq_one.1 h9_1
      have hwR : w ∈ residualUnits 14 D br := (filter_subset _ _) (hw ▸ mem_singleton_self _)
      rw [hRu13, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact hw
      · exact absurd (hom2_full1 r3 3 x ix n3 9 7 h3I hix hr3 hr3' hx hn3
          ⟨hxn3, by decide, hix0, hd3, hdx, hx3, hn33, by rintro rfl; exact (by decide : hc_adjB 3 9 = false) ▸ g3 |> Bool.noConfusion,
            h37, g3, gix, gr3x, gr3n, hsn3, by decide, by decide, by decide⟩
          hx0 h3_1 (by rw [hu3, hw])) id
    have h13_eq : ru D br 13 = {u1} := by
      obtain ⟨w, hw⟩ := card_eq_one.1 h13_1
      have hwR : w ∈ residualUnits 14 D br := (filter_subset _ _) (hw ▸ mem_singleton_self _)
      rw [hRu13, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact hw
      · exact absurd (hom2_full1 r3 3 x ix n3 13 7 h3I hix hr3 hr3' hx hn3
          ⟨hxn3, by decide, hix0, hd3, hdx, hx3, hn33, by rintro rfl; exact (by decide : hc_adjB 3 13 = false) ▸ g3 |> Bool.noConfusion,
            h37, g3, gix, gr3x, gr3n, hsn3, by decide, by decide, by decide⟩
          hx0 h3_1 (by rw [hu3, hw])) id
    obtain ⟨e9_5, e9_6, he9_5, he9_6, h9ne, -, -, hf9_5, hf9_6⟩ :=
      hom2_edges 9 1 5 10 6 h1I h10I (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h5_0
    obtain ⟨e13_2, e13_4, he13_2, he13_4, h13ne, -, -, hf13_2, hf13_4⟩ :=
      hom2_edges 13 1 2 8 4 h1I h8I (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h2_0
    have hW9_3 : 3 ≤ (sem_W 14 D 9).card :=
      pa_card3 (as_mem hpos h1I (by decide) (by decide : Adj 1 9)) he9_5 he9_6
        (fun e => (by rw [hIeq]; decide : (5 : Fin 14) ∉ _) (hf9_5 1 h1I (by decide) e.symm ▸ h1I))
        (fun e => (by rw [hIeq]; decide : (6 : Fin 14) ∉ _) (hf9_6 1 h1I (by decide) e.symm ▸ h1I)) h9ne
    have hW13_3 : 3 ≤ (sem_W 14 D 13).card :=
      pa_card3 (as_mem hpos h1I (by decide) (by decide : Adj 1 13)) he13_2 he13_4
        (fun e => (by rw [hIeq]; decide : (2 : Fin 14) ∉ _) (hf13_2 1 h1I (by decide) e.symm ▸ h1I))
        (fun e => (by rw [hIeq]; decide : (4 : Fin 14) ∉ _) (hf13_4 1 h1I (by decide) e.symm ▸ h1I)) h13ne
    have hm9 : merges 14 D (carrierT 14 D {9}) = ∅ := card_eq_zero.1 (by have := cc_le h hD br hbr 9; omega)
    have hm13 : merges 14 D (carrierT 14 D {13}) = ∅ := card_eq_zero.1 (by have := cc_le h hD br hbr 13; omega)
    have hu1R : u1 ∈ residualUnits 14 D br := (filter_subset _ _) (hu1 ▸ mem_singleton_self _)
    obtain ⟨P, Q, hPQ1, hPQsat⟩ := gct_gen sem_g14_gr h (sem_g14_comp hD) br hmin hu1R
      ({9, 13} : Finset (Fin 14)) (by simp) (fun z hz => by
        rw [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · refine ⟨hm9, ru_mem (h9_eq ▸ mem_singleton_self _), fun u hu hzu => ?_⟩
          have hm : u ∈ ru D br 9 := mem_filter.2 ⟨hu, hzu⟩; rw [h9_eq, mem_singleton] at hm; exact hm
        · refine ⟨hm13, ru_mem (h13_eq ▸ mem_singleton_self _), fun u hu hzu => ?_⟩
          have hm : u ∈ ru D br 13 := mem_filter.2 ⟨hu, hzu⟩; rw [h13_eq, mem_singleton] at hm; exact hm)
    have hPQ : P ≠ Q := fun hh => hPQ1 (congrArg Prod.fst hh)
    have hW9_le3 : (sem_W 14 D 9).card ≤ 3 := by have := cc_le h hD br hbr 9; omega
    have hW13_le3 : (sem_W 14 D 13).card ≤ 3 := by have := cc_le h hD br hbr 13; omega
    have hc2 : (sem_W 14 D 2).card ≤ 2 := by have := cc_le h hD br hbr 2; rw [h2_0, card_empty] at this; omega
    have hc4 : (sem_W 14 D 4).card ≤ 2 := by have := cc_le h hD br hbr 4; rw [h4_0, card_empty] at this; omega
    have hc5' : (sem_W 14 D 5).card ≤ 2 := by have := cc_le h hD br hbr 5; rw [h5_0, card_empty] at this; omega
    have hc6 : (sem_W 14 D 6).card ≤ 2 := by have := cc_le h hD br hbr 6; rw [h6_0, card_empty] at this; omega
    exact elim_disj_ps_pair h hD hpos hPQ 9 13 1 1 5 6 2 4 10 8 8 10
      h1I h1I h10I h8I h8I h10I
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) hW9_le3 hW13_le3 hc5' hc6 hc2 hc4
      (hPQsat 9 (by simp)).1 (hPQsat 9 (by simp)).2 (hPQsat 13 (by simp)).1 (hPQsat 13 (by simp)).2
  have h2n : (ru D br 2).Nonempty := by
    by_contra hc; exact hkill_if_L0 2 8 13 12 4 5 h8I (by rw [hIeq]; decide) (hE 13 (by decide)) (hE 12 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      (not_nonempty_iff_eq_empty.1 hc)
  have h4n : (ru D br 4).Nonempty := by
    by_contra hc; exact hkill_if_L0 4 10 13 11 2 6 h10I (by rw [hIeq]; decide) (hE 13 (by decide)) (hE 11 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      (not_nonempty_iff_eq_empty.1 hc)
  have h5n : (ru D br 5).Nonempty := by
    by_contra hc; exact hkill_if_L0 5 10 9 12 6 2 h10I (by rw [hIeq]; decide) (hE 9 (by decide)) (hE 12 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      (not_nonempty_iff_eq_empty.1 hc)
  have h6n : (ru D br 6).Nonempty := by
    by_contra hc; exact hkill_if_L0 6 8 9 11 5 4 h8I (by rw [hIeq]; decide) (hE 9 (by decide)) (hE 11 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide)
      (not_nonempty_iff_eq_empty.1 hc)
  have hkill_if_R0 : ∀ (r ir l8 l10 ol8 n8 n10 rA rB nA nB : Fin 14),
      ir ∈ ineligSet 14 D → r ∉ ineligSet 14 D →
      l8 ∈ eligSet 14 D → l10 ∈ eligSet 14 D → ol8 ∈ eligSet 14 D →
      l8 ∉ ineligSet 14 D → l10 ∉ ineligSet 14 D → n8 ∉ ineligSet 14 D → n10 ∉ ineligSet 14 D →
      rA ∈ eligSet 14 D → rB ∈ eligSet 14 D → nA ∉ ineligSet 14 D → nB ∉ ineligSet 14 D →
      (r ≠ n8 ∧ r ≠ n10 ∧ ir ≠ 0 ∧ (g14_nbB r).card = 3 ∧ (g14_nbB l8).card = 3 ∧ (g14_nbB l10).card = 3 ∧
        (g14_nbB ol8).card = 3 ∧ (g14_nbB rA).card = 3 ∧ (g14_nbB rB).card = 3 ∧
        r ≠ 8 ∧ n8 ≠ 8 ∧ r ≠ 10 ∧ n10 ≠ 10 ∧ l8 ≠ l10 ∧ l8 ≠ ol8 ∧ l10 ≠ 0 ∧
        l8 ≠ 4 ∧ l8 ≠ 5 ∧ ol8 ≠ 4 ∧ ol8 ≠ 5 ∧
        rA ≠ ol8 ∧ rB ≠ ol8 ∧ rA ≠ 7 ∧ rB ≠ 7 ∧ nA ≠ 1 ∧ nB ≠ 3) →
      (hc_adjB ir r = true ∧ hc_adjB 8 l8 = true ∧ hc_adjB 10 l10 = true ∧ hc_adjB 8 ol8 = true ∧
        hc_adjB l8 r = true ∧ hc_adjB l8 n8 = true ∧ hc_adjB l10 r = true ∧ hc_adjB l10 n10 = true ∧
        decide (r.val < 7) = decide (n8.val < 7) ∧ decide (r.val < 7) = decide (n10.val < 7) ∧
        hc_adjB 8 ol8 = true ∧ hc_adjB l10 ol8 = false ∧ hc_adjB 10 l8 = false ∧ hc_adjB 8 l10 = false ∧
        hc_adjB l8 0 = false ∧ hc_adjB ol8 0 = false ∧ hc_adjB n8 ol8 = false ∧
        hc_adjB 1 rA = true ∧ hc_adjB rA nA = true ∧ hc_adjB rA l8 = false ∧ hc_adjB 1 ol8 = false ∧ hc_adjB ol8 7 = false ∧
        hc_adjB 3 rB = true ∧ hc_adjB rB nB = true ∧ hc_adjB rB l8 = false ∧ hc_adjB 3 ol8 = false) →
      ((r = 9 ∨ r = 11 ∨ r = 12 ∨ r = 13) ∧ (n8 = 9 ∨ n8 = 11 ∨ n8 = 12 ∨ n8 = 13) ∧
       (rA = 9 ∨ rA = 11 ∨ rA = 12 ∨ rA = 13) ∧ (rB = 9 ∨ rB = 11 ∨ rB = 12 ∨ rB = 13) ∧
       (9 = r ∨ 9 = n8 ∨ 9 = rA ∨ 9 = rB) ∧ (11 = r ∨ 11 = n8 ∨ 11 = rA ∨ 11 = rB) ∧
       (12 = r ∨ 12 = n8 ∨ 12 = rA ∨ 12 = rB) ∧ (13 = r ∨ 13 = n8 ∨ 13 = rA ∨ 13 = rB)) →
      (ru D br l8).Nonempty → (ru D br l10).Nonempty → (ru D br ol8).Nonempty → ru D br r = ∅ → False := by
    intro r ir l8 l10 ol8 n8 n10 rA rB nA nB hir hr hl8 hl10 hol8 hl8' hl10' hn8 hn10 hrA hrB hnA hnB hg1 hg2 hg3 hl8n hl10n hol8n hr0
    obtain ⟨hrn8, hrn10, hir0, hdr, hdl8, hdl10, hdol8, hdrA, hdrB,
      hr8, hn88, hr10, hn1010, hl810, hl8o, hl100, hl84, hl85, hol84, hol85,
      hrAo, hrBo, hrA7, hrB7, hnA1, hnB3⟩ := hg1
    obtain ⟨gir, g8, g10, g8o, gl8r, gl8n, gl10r, gl10n, hsn8, hsn10,
      _, gl10o, gn10l8, gn8l10, gl80, gol80, gn8o,
      g1A, gAnA, gAl8, gn1o, go7, g3B, gBnB, gBl8, gn3o⟩ := hg2
    obtain ⟨-, hn8_in, hrA_in, hrB_in, h9_in, h11_in, h12_in, h13_in⟩ := hg3
    have hol8_cases : ol8 = 2 ∨ ol8 = 6 := by revert g8o; fin_cases ol8 <;> decide
    have hR4_not_l10 : ∀ z : Fin 14, (z = 9 ∨ z = 11 ∨ z = 12 ∨ z = 13) → l10 ≠ z := by
      intro z hz hh; rw [hh] at g10; rcases hz with rfl | rfl | rfl | rfl <;> (revert g10; decide)
    have hR4_n0 : ∀ z : Fin 14, (z = 9 ∨ z = 11 ∨ z = 12 ∨ z = 13) → hc_adjB z 0 = false := by
      rintro z (rfl | rfl | rfl | rfl) <;> decide
    have hR4_n10 : ∀ z : Fin 14, (z = 9 ∨ z = 11 ∨ z = 12 ∨ z = 13) → hc_adjB 10 z = false := by
      rintro z (rfl | rfl | rfl | rfl) <;> decide
    have hR4_n8 : ∀ z : Fin 14, (z = 9 ∨ z = 11 ∨ z = 12 ∨ z = 13) → hc_adjB 8 z = false := by
      rintro z (rfl | rfl | rfl | rfl) <;> decide
    have hl8_1 : (ru D br l8).card = 1 := by
      have hne2 : (ru D br l8).card ≠ 2 := fun h2 => by
        by_cases h10_2 : (ru D br l10).card = 2
        · exact hom2_R_full l8 8 r ir n8 l10 10 0 l10 ol8 h8I hir h10I hl8 hl10 hl8' hr hn8
            ⟨hrn8, by decide, hir0, by decide, hdl8, hdr, hdl10, by decide, hr8, hn88, hl810.symm, hl100, hl810, hl8o,
              g8, gir, g10, gl8r, gl8n, hsn8, by decide, gl80, g8o, gl10o, gn8l10⟩
            hr0 h2 hl10n h10_2
        · have h10_1 : (ru D br l10).card = 1 := by have := hle2 l10; have := card_pos.2 hl10n; omega
          exact hom2_full1 l10 10 r ir n10 l8 0 h10I hir hl10 hl10' hr hn10
            ⟨hrn10, by decide, hir0, hdl10, hdr, hr10, hn1010, hl810.symm, hl100, g10, gir, gl10r, gl10n, hsn10,
              by decide, gl80, gn10l8⟩
            hr0 h10_1 ((filter_subset _ _).trans (hR_of2 l8 h2).symm.subset)
      have := hle2 l8; have := card_pos.2 hl8n; omega
    have hl10_1 : (ru D br l10).card = 1 := by
      have hne2 : (ru D br l10).card ≠ 2 := fun h2 =>
        hom2_full1 l8 8 r ir n8 l10 ol8 h8I hir hl8 hl8' hr hn8
          ⟨hrn8, by decide, hir0, hdl8, hdr, hr8, hn88, hl810, hl8o, g8, gir, gl8r, gl8n, hsn8, g8o, gl10o, gn8l10⟩
          hr0 hl8_1 ((filter_subset _ _).trans (hR_of2 l10 h2).symm.subset)
      have := hle2 l10; have := card_pos.2 hl10n; omega
    obtain ⟨u8, hu8⟩ := card_eq_one.1 hl8_1
    obtain ⟨u10, hu10⟩ := card_eq_one.1 hl10_1
    have hu810 : u8 ≠ u10 := fun hh =>
      hom2_full1 l8 8 r ir n8 l10 ol8 h8I hir hl8 hl8' hr hn8
        ⟨hrn8, by decide, hir0, hdl8, hdr, hr8, hn88, hl810, hl8o, g8, gir, gl8r, gl8n, hsn8, g8o, gl10o, gn8l10⟩
        hr0 hl8_1 (by rw [hu8, hu10, hh])
    have hRu810 : residualUnits 14 D br = {u8, u10} := by
      symm
      refine eq_of_subset_of_card_le (fun u hu => ?_) (by rw [card_pair hu810, hR2])
      rw [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact (filter_subset _ _) (hu8 ▸ mem_singleton_self _)
      · exact (filter_subset _ _) (hu10 ▸ mem_singleton_self _)
    have hno_u10 : ∀ y : Fin 14, l10 ≠ y → hc_adjB y 0 = false → hc_adjB 10 y = false → u10 ∉ ru D br y := by
      intro y hne hy0 gn10y hy10
      exact hom2_full1 l10 10 r ir n10 y 0 h10I hir hl10 hl10' hr hn10
        ⟨hrn10, by decide, hir0, hdl10, hdr, hr10, hn1010, hne, hl100, g10, gir, gl10r, gl10n, hsn10,
          by decide, hy0, gn10y⟩
        hr0 hl10_1 (by rw [hu10, singleton_subset_iff]; exact hy10)
    have hno_u8 : ∀ y : Fin 14, l8 ≠ y → hc_adjB y ol8 = false → hc_adjB 8 y = false → u8 ∉ ru D br y := by
      intro y hne hyo gn8y hy8
      exact hom2_full1 l8 8 r ir n8 y ol8 h8I hir hl8 hl8' hr hn8
        ⟨hrn8, by decide, hir0, hdl8, hdr, hr8, hn88, hne, hl8o, g8, gir, gl8r, gl8n, hsn8, g8o, hyo, gn8y⟩
        hr0 hl8_1 (by rw [hu8, singleton_subset_iff]; exact hy8)
    have hol8_eq : ru D br ol8 = {u8} := by
      have hnu10 : u10 ∉ ru D br ol8 := hno_u10 ol8
        (fun hh => by rw [hh] at g10; rcases hol8_cases with rfl | rfl <;> (revert g10; decide))
        gol80 (by rcases hol8_cases with rfl | rfl <;> decide)
      obtain ⟨w, hw⟩ := hol8n
      have hwR := (filter_subset _ _) hw
      rw [hRu810, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact eq_singleton_iff_unique_mem.2 ⟨hw, fun z hz => by
          have hzR := (filter_subset _ _) hz
          rw [hRu810, mem_insert, mem_singleton] at hzR
          exact hzR.resolve_right (fun hh => hnu10 (hh ▸ hz))⟩
      · exact absurd hw hnu10
    have hn8_0 : ru D br n8 = ∅ := by
      apply eq_empty_iff_forall_notMem.2; intro u hu
      have huR := (filter_subset _ _) hu
      rw [hRu810, mem_insert, mem_singleton] at huR
      rcases huR with rfl | rfl
      · exact hno_u8 n8 (fun hh => by rw [← hh] at gl8n; exact (by decide : ∀ x : Fin 14, hc_adjB x x = false) _ ▸ gl8n |> Bool.noConfusion)
          gn8o (hR4_n8 n8 hn8_in) hu
      · exact hno_u10 n8 (hR4_not_l10 n8 hn8_in) (hR4_n0 n8 hn8_in) (hR4_n10 n8 hn8_in) hu
    have hrA_0 : ru D br rA = ∅ := by
      apply eq_empty_iff_forall_notMem.2; intro u hu
      have hnu10 : u10 ∉ ru D br rA := hno_u10 rA (hR4_not_l10 rA hrA_in) (hR4_n0 rA hrA_in) (hR4_n10 rA hrA_in)
      have huR := (filter_subset _ _) hu
      rw [hRu810, mem_insert, mem_singleton] at huR
      rcases huR with rfl | rfl
      · have hrA_eq : ru D br rA = {u} := eq_singleton_iff_unique_mem.2 ⟨hu, fun z hz => by
          have hzR := (filter_subset _ _) hz
          rw [hRu810, mem_insert, mem_singleton] at hzR
          exact hzR.resolve_right (fun hh => hnu10 (hh ▸ hz))⟩
        exact hsame1 ol8 rA 8 1 nA l8 7 h8I h1I hol8 hrA hnA
          ⟨by decide, by decide, hdol8, hdrA, by decide, hrAo.symm, hnA1, g8o, g1A, gAnA, g8, hl8o.symm, gAl8,
            by decide, hrA7, go7, gn1o⟩ (by rw [hrA_eq, card_singleton]) (hol8_eq.trans hrA_eq.symm)
      · exact hnu10 hu
    have hrB_0 : ru D br rB = ∅ := by
      apply eq_empty_iff_forall_notMem.2; intro u hu
      have hnu10 : u10 ∉ ru D br rB := hno_u10 rB (hR4_not_l10 rB hrB_in) (hR4_n0 rB hrB_in) (hR4_n10 rB hrB_in)
      have huR := (filter_subset _ _) hu
      rw [hRu810, mem_insert, mem_singleton] at huR
      rcases huR with rfl | rfl
      · have hrB_eq : ru D br rB = {u} := eq_singleton_iff_unique_mem.2 ⟨hu, fun z hz => by
          have hzR := (filter_subset _ _) hz
          rw [hRu810, mem_insert, mem_singleton] at hzR
          exact hzR.resolve_right (fun hh => hnu10 (hh ▸ hz))⟩
        exact hsame1 ol8 rB 8 3 nB l8 7 h8I h3I hol8 hrB hnB
          ⟨by decide, by decide, hdol8, hdrB, by decide, hrBo.symm, hnB3, g8o, g3B, gBnB, g8, hl8o.symm, gBl8,
            by decide, hrB7, go7, gn3o⟩ (by rw [hrB_eq, card_singleton]) (hol8_eq.trans hrB_eq.symm)
      · exact hnu10 hu
    have h9_0 : ru D br 9 = ∅ := by rcases h9_in with h | h | h | h <;> rwa [h]
    have h11_0 : ru D br 11 = ∅ := by rcases h11_in with h | h | h | h <;> rwa [h]
    have h12_0 : ru D br 12 = ∅ := by rcases h12_in with h | h | h | h <;> rwa [h]
    have h13_0 : ru D br 13 = ∅ := by rcases h13_in with h | h | h | h <;> rwa [h]
    have h4_eq : ru D br 4 = {u10} := by
      have hnu8 : u8 ∉ ru D br 4 := hno_u8 4 hl84 (by rcases hol8_cases with rfl | rfl <;> decide) (by decide)
      obtain ⟨w, hw⟩ := h4n
      have hwR := (filter_subset _ _) hw
      rw [hRu810, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact absurd hw hnu8
      · exact eq_singleton_iff_unique_mem.2 ⟨hw, fun z hz => by
          have hzR := (filter_subset _ _) hz
          rw [hRu810, mem_insert, mem_singleton] at hzR
          exact hzR.resolve_left (fun hh => hnu8 (hh ▸ hz))⟩
    have h5_eq : ru D br 5 = {u10} := by
      have hnu8 : u8 ∉ ru D br 5 := hno_u8 5 hl85 (by rcases hol8_cases with rfl | rfl <;> decide) (by decide)
      obtain ⟨w, hw⟩ := h5n
      have hwR := (filter_subset _ _) hw
      rw [hRu810, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact absurd hw hnu8
      · exact eq_singleton_iff_unique_mem.2 ⟨hw, fun z hz => by
          have hzR := (filter_subset _ _) hz
          rw [hRu810, mem_insert, mem_singleton] at hzR
          exact hzR.resolve_left (fun hh => hnu8 (hh ▸ hz))⟩
    obtain ⟨e4_11, e4_13, he4_11, he4_13, h4ne, -, -, hf4_11, hf4_13⟩ :=
      hom2_edges 4 10 11 3 13 h10I h3I (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h11_0
    obtain ⟨e5_9, e5_12, he5_9, he5_12, h5ne, -, -, hf5_9, hf5_12⟩ :=
      hom2_edges 5 10 9 1 12 h10I h1I (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by decide) h9_0
    have hW4_3 : 3 ≤ (sem_W 14 D 4).card :=
      pa_card3 (as_mem hpos h10I (by decide) (by decide : Adj 10 4)) he4_11 he4_13
        (fun e => (by rw [hIeq]; decide : (11 : Fin 14) ∉ _) (hf4_11 10 h10I (by decide) e.symm ▸ h10I))
        (fun e => (by rw [hIeq]; decide : (13 : Fin 14) ∉ _) (hf4_13 10 h10I (by decide) e.symm ▸ h10I)) h4ne
    have hW5_3 : 3 ≤ (sem_W 14 D 5).card :=
      pa_card3 (as_mem hpos h10I (by decide) (by decide : Adj 10 5)) he5_9 he5_12
        (fun e => (by rw [hIeq]; decide : (9 : Fin 14) ∉ _) (hf5_9 10 h10I (by decide) e.symm ▸ h10I))
        (fun e => (by rw [hIeq]; decide : (12 : Fin 14) ∉ _) (hf5_12 10 h10I (by decide) e.symm ▸ h10I)) h5ne
    have hm4 : merges 14 D (carrierT 14 D {4}) = ∅ := card_eq_zero.1 (by have := cc_le h hD br hbr 4; rw [h4_eq, card_singleton] at this; omega)
    have hm5 : merges 14 D (carrierT 14 D {5}) = ∅ := card_eq_zero.1 (by have := cc_le h hD br hbr 5; rw [h5_eq, card_singleton] at this; omega)
    have hu10R : u10 ∈ residualUnits 14 D br := (filter_subset _ _) (hu10 ▸ mem_singleton_self _)
    obtain ⟨P, Q, hPQ1, hPQsat⟩ := gct_gen sem_g14_gr h (sem_g14_comp hD) br hmin hu10R
      ({4, 5} : Finset (Fin 14)) (by simp) (fun z hz => by
        rw [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · refine ⟨hm4, ru_mem (h4_eq ▸ mem_singleton_self _), fun u hu hzu => ?_⟩
          have hm : u ∈ ru D br 4 := mem_filter.2 ⟨hu, hzu⟩; rw [h4_eq, mem_singleton] at hm; exact hm
        · refine ⟨hm5, ru_mem (h5_eq ▸ mem_singleton_self _), fun u hu hzu => ?_⟩
          have hm : u ∈ ru D br 5 := mem_filter.2 ⟨hu, hzu⟩; rw [h5_eq, mem_singleton] at hm; exact hm)
    have hPQ : P ≠ Q := fun hh => hPQ1 (congrArg Prod.fst hh)
    have hW4_le3 : (sem_W 14 D 4).card ≤ 3 := by have := cc_le h hD br hbr 4; rw [h4_eq, card_singleton] at this; omega
    have hW5_le3 : (sem_W 14 D 5).card ≤ 3 := by have := cc_le h hD br hbr 5; rw [h5_eq, card_singleton] at this; omega
    have hc9 : (sem_W 14 D 9).card ≤ 2 := by have := cc_le h hD br hbr 9; rw [h9_0, card_empty] at this; omega
    have hc11 : (sem_W 14 D 11).card ≤ 2 := by have := cc_le h hD br hbr 11; rw [h11_0, card_empty] at this; omega
    have hc12 : (sem_W 14 D 12).card ≤ 2 := by have := cc_le h hD br hbr 12; rw [h12_0, card_empty] at this; omega
    have hc13 : (sem_W 14 D 13).card ≤ 2 := by have := cc_le h hD br hbr 13; rw [h13_0, card_empty] at this; omega
    exact elim_disj_ps_pair h hD hpos hPQ 4 5 10 10 11 13 9 12 3 1 1 3
      h10I h10I h3I h1I h1I h3I
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) hW4_le3 hW5_le3 hc11 hc13 hc9 hc12
      (hPQsat 4 (by simp)).1 (hPQsat 4 (by simp)).2 (hPQsat 5 (by simp)).1 (hPQsat 5 (by simp)).2
  have h11n : (ru D br 11).Nonempty := by
    by_contra hc; exact hkill_if_R0 11 3 6 4 2 9 13 13 12 4 5
      h3I (by rw [hIeq]; decide) (hE 6 (by decide)) (hE 4 (by decide)) (hE 2 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (hE 13 (by decide)) (hE 12 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) (by decide) (by decide) h6n h4n h2n (not_nonempty_iff_eq_empty.1 hc)
  have h13n : (ru D br 13).Nonempty := by
    by_contra hc; exact hkill_if_R0 13 1 2 4 6 12 11 9 11 5 4
      h1I (by rw [hIeq]; decide) (hE 2 (by decide)) (hE 4 (by decide)) (hE 6 (by decide))
      (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (hE 9 (by decide)) (hE 11 (by decide)) (by rw [hIeq]; decide) (by rw [hIeq]; decide)
      (by decide) (by decide) (by decide) h2n h4n h6n (not_nonempty_iff_eq_empty.1 hc)
  have h11_1 : (ru D br 11).card = 1 := by
    have hne2 : (ru D br 11).card ≠ 2 := fun h2 =>
      hR_blow5 11 3 4 4 10 0 6 8 2 13 1 7 h3I h10I h8I h1I
        (hE 4 (by decide)) (hE 6 (by decide)) (hE 13 (by decide)) (by rw [hIeq]; decide) (by decide) h2 h4n h6n h13n
    have := hle2 11; have := card_pos.2 h11n; omega
  have h13_1 : (ru D br 13).card = 1 := by
    have hne2 : (ru D br 13).card ≠ 2 := fun h2 =>
      hR_blow5 13 1 4 4 10 0 2 8 6 11 3 7 h1I h10I h8I h3I
        (hE 4 (by decide)) (hE 2 (by decide)) (hE 11 (by decide)) (by rw [hIeq]; decide) (by decide) h2 h4n h2n h11n
    have := hle2 13; have := card_pos.2 h13n; omega
  obtain ⟨u13, hu13⟩ := card_eq_one.1 h13_1
  obtain ⟨u11, hu11⟩ := card_eq_one.1 h11_1
  have hu_ne : u13 ≠ u11 := fun hh =>
    hsame1 13 11 1 3 4 7 7 h1I h3I (hE 13 (by decide)) (hE 11 (by decide)) (by rw [hIeq]; decide)
      (by decide) h11_1 (by rw [hu13, hu11, hh])
  have hRu : residualUnits 14 D br = {u13, u11} := by
    symm
    refine eq_of_subset_of_card_le (fun u hu => ?_) (by rw [card_pair hu_ne, hR2])
    rw [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (filter_subset _ _) (hu13 ▸ mem_singleton_self _)
    · exact (filter_subset _ _) (hu11 ▸ mem_singleton_self _)
  have h4_2 : (ru D br 4).card = 2 := by
    have hne1 : (ru D br 4).card ≠ 1 := fun h1 => by
      obtain ⟨w, hw⟩ := card_eq_one.1 h1
      have hwR : w ∈ residualUnits 14 D br := (filter_subset _ _) (hw ▸ mem_singleton_self _)
      rw [hRu, mem_insert, mem_singleton] at hwR
      rcases hwR with rfl | rfl
      · exact hsame1 4 13 10 1 2 0 7 h10I h1I (hE 4 (by decide)) (hE 13 (by decide)) (by rw [hIeq]; decide)
          (by decide) h13_1 (by rw [hw, hu13])
      · exact hsame1 4 11 10 3 6 0 7 h10I h3I (hE 4 (by decide)) (hE 11 (by decide)) (by rw [hIeq]; decide)
          (by decide) h11_1 (by rw [hw, hu11])
    have := hle2 4; have := card_pos.2 h4n; omega
  exact hR_blow5 4 10 11 2 8 6 13 1 7 11 3 7 h10I h8I h1I h3I
    (hE 2 (by decide)) (hE 13 (by decide)) (hE 11 (by decide)) (by rw [hIeq]; decide) (by decide) h4_2 h2n h13n h11n
theorem g14_orbit_partition : ∀ idx : Fin 157,
    (hc_rep idx).card = 3 ∨
    (∃ k : Fin 21, no_i0_4_idx k = idx) ∨
    (∃ k : Fin 22, cnt_b1_R_idx k = idx) ∨
    (∃ k : Fin 46, cnt_b1_L_idx k = idx) ∨
    (∃ k : Fin 4, cnt_b2_R_idx k = idx) ∨
    (∃ k : Fin 6, cnt_b2_L_idx k = idx) ∨
    idx.val = 49 ∨ idx.val = 50 ∨ idx.val = 54 ∨ idx.val = 59 ∨ idx.val = 63 ∨ idx.val = 79 ∨ idx.val = 82 ∨
    idx.val = 99 ∨ idx.val = 102 ∨ idx.val = 104 ∨ idx.val = 105 ∨ idx.val = 107 ∨ idx.val = 108 ∨ idx.val = 111 ∨ idx.val = 112 := by
  decide +kernel
theorem g14_lb_25 (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ G14Edge x) (hsize : C.size ≤ 24) :
    False := by
  obtain ⟨D, h, hD, -, h11, -, hmem⟩ := g14_wlog_canon C hmono hC hsize
  obtain ⟨idx, hI⟩ := hc_rep_of_mem hmem
  have hI' : ineligSet 14 D = hc_rep idx := hI.symm
  have hts := totalSurplus_split 14 D
  have hel := inelig_card_add 14 D
  rcases g14_orbit_partition idx with
    hc3 | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ |
    h49 | h50 | h54 | h59 | h63 | h79 | h82 | h99 | h102 | h104 | h105 | h107 | h108 | h111 | h112
  · rw [← hI'] at hc3
    exact tight_le_all h hD (by omega) idx hI'
  · exact elim_no_i0_4 h hD h11 k hI'
  · exact elim_cnt_b1_R h hD h11 k hI'
  · exact elim_cnt_b1_L h hD h11 k hI'
  · exact elim_cnt_b2_R h hD h11 k hI'
  · exact elim_cnt_b2_L h hD h11 k hI'
  · exact elim_49 h hD h11 ((show idx = ⟨49, by decide⟩ from Fin.ext h49) ▸ hI')
  · exact elim_50 h hD h11 ((show idx = ⟨50, by decide⟩ from Fin.ext h50) ▸ hI')
  · exact elim_54 h hD h11 ((show idx = ⟨54, by decide⟩ from Fin.ext h54) ▸ hI')
  · exact elim_59 h hD h11 ((show idx = ⟨59, by decide⟩ from Fin.ext h59) ▸ hI')
  · exact elim_63 h hD h11 ((show idx = ⟨63, by decide⟩ from Fin.ext h63) ▸ hI')
  · exact elim_79 h hD h11 ((show idx = ⟨79, by decide⟩ from Fin.ext h79) ▸ hI')
  · exact elim_82 h hD h11 ((show idx = ⟨82, by decide⟩ from Fin.ext h82) ▸ hI')
  · exact elim_99 h hD h11 ((show idx = ⟨99, by decide⟩ from Fin.ext h99) ▸ hI')
  · exact elim_102 h hD h11 ((show idx = ⟨102, by decide⟩ from Fin.ext h102) ▸ hI')
  · exact elim_104 h hD h11 ((show idx = ⟨104, by decide⟩ from Fin.ext h104) ▸ hI')
  · exact elim_105 h hD h11 ((show idx = ⟨105, by decide⟩ from Fin.ext h105) ▸ hI')
  · exact elim_107 h hD h11 ((show idx = ⟨107, by decide⟩ from Fin.ext h107) ▸ hI')
  · exact elim_108 h hD h11 ((show idx = ⟨108, by decide⟩ from Fin.ext h108) ▸ hI')
  · exact elim_111 h hD h11 ((show idx = ⟨111, by decide⟩ from Fin.ext h111) ▸ hI')
  · exact elim_112 h hD h11 ((show idx = ⟨112, by decide⟩ from Fin.ext h112) ▸ hI')
end PEqualNP.Outside.L_meta_9772_aux
theorem PEqualNP.Outside.L_meta_9772 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 24 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hmono, hsize, hC⟩
  exact PEqualNP.Outside.L_meta_9772_aux.g14_lb_25 C hmono hC hsize
