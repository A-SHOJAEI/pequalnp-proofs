import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_8455.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_8455
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffe8ffffffffffecffe8fffffff8ffffffe8fefcfaf8eeeceae8ffffffffffffffe8ffffffffffecffe8fffffff8ffffffe8fefcfaf8eeeceae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 5 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 5 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 1000000000000000003
  (n*(n+971)) % 1000000000000000003
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 1000000000000000003
  (n*(n+971)) % 1000000000000000003
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv
theorem count_low {u} {m hints L : Nat} (hm : m < 512) (hp : properB (graphGoal m) = true)
    (ess : checkEssential (graphGoal m) (vars m) (graphPairs m hints) = true)
    (hle : L ≤ ((graphPairs m hints).map Prod.fst).toFinset.card - 1) :
    Lower u (varsX m) (graphGoal m) L := by
  simp only [varsX, hm, ite_true]
  intro p bank hr ha
  exact hle.trans (lower_count (proper_of _ hp) (graphPairs m hints) ess p bank hr ha)

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩

def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a p (kwProbe neg (field 4)) && kwWireB ws T b p (kwProbe neg (field 5)) &&
    kwWireB ws T a (kwProbe pos (field 6)) n && kwWireB ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {pos neg T ws k v} (h : kwWord pos neg T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)

def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (pos neg : Nat) (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => kwWord pos neg (targetOf g) (stateSet g k (a+j)) k (packedAt data (32*j) 32))
theorem mixedCut {pos neg g k a n data} (mode : g.mode=false) (h : kwTest pos neg g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord pos neg _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh

def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1

def eightInputs : List Sig := vars 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
def eightEdge (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7)

theorem eightTable : ∀ r : Row, bit r graph = eightEdge (sampleEight r) := by decide +kernel
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [← eightList, List.map_ofFn]
  rfl

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl
def neighbor8453 (i : Fin 8) : Nat := [1,0,0,0,1,2,3,3].getD i.val 0
def absentRow8453 (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< neighbor8453 i)
def presentRow8453 (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor8453 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 8, bit (absentRow8453 i) graph ≠ bit (presentRow8453 i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (absentRow8453 i) (eightInputs.getD j.val zero) =
      bit (presentRow8453 i) (eightInputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 8 C = eightEdge) (small : C.size ≤ 13) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 12 else 13) ∧ Live u graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((congrFun computes (sampleEight r)).trans (eightTable r).symm)
  have len : C.gates.length ≤ 13 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 12 else 13) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates eightInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (absentRow8453 i) (presentRow8453 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 13 → ¬Live false graph k eightInputs.toFinset)
    (s : ∀ k, k ≤ 12 → ¬Live true graph k eightInputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 eightEdge 13 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def g7Y : Array (Bits × Bits) := #[(0xd76bb5daed76bb5daed76bb5daed76bb5daed7,0x148a45229148a45229148a45229148a4522914),(0x6db6db6db6db6db6db6db6db6db6db6db6db6d,0xa150a8542a150a8542a150a8542a150a8542a1),(0xbadd6eb75badd6eb75badd6eb75badd6eb75ba,0x4a25128944a25128944a25128944a25128944a),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g7C : List ColumnInfo := []
def g7A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g7D3 (_ : Nat) : Nat := 0x7
def g7L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g7D3)
  | _ => emptyPacking
def g7I (_ _ : Nat) : Option (Nat × Nat) := none
def g7 : Forest := ⟨7,3,fun i => g7Y[i]?.getD (0,0),g7C,g7A,g7L,g7I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7P3_0 : block g7 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g7B3 : block g7 3 0 1=true := g7P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7T : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0 = true)
  · exact (rfl : block g7 1 0 0 = true)
  · exact (rfl : block g7 2 0 0 = true)
  · exact g7B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7G : graphValid g7 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low7 : Lower true (varsX 7) (graphGoal 7) 4 := lower_forest (g:=g7) (i:=0) (hints:=1) (before_sound [] baseKnown) g7G g7T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K7 := extendKnown [] 4 [(7,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[(0x9f379f379f379f379f379f379f379f379f379f,0x16911691169116911691169116911691169116),(0xe3e9e3e9e3e9e3e9e3e9e3e9e3e9e3e9e3e9e3,0xa142a142a142a142a142a142a142a142a142a1),(0x0,0x0),(0x1c161c161c161c161c161c161c161c161c161c,0x886e886e886e886e886e886e886e886e886e88),(0x60d860d860d860d860d860d860d860d860d860,0x50bd50bd50bd50bd50bd50bd50bd50bd50bd50),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[16,67]]
def g27D3 (_ : Nat) : Nat := 0xf
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g27D3)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 1=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=65537) (before_sound K7 V7) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K7 4 [(27,[]),(45,[84,33]),(54,[67,83,16,32]),(75,[100,84,49]),(77,[100,84,49,33]),(83,[100,65,81,16,48]),(86,[100,65,81,49,16,32]),(89,[97,81,33,48]),(90,[97,16,65,80,49,32]),(139,[116,100,84,49]),(141,[116,100,84,49,33]),(165,[116,100,81,16,33,48]),(166,[116,100,81,49,32]),(169,[113,65,100,81,33,48]),(172,[113,16,96,64,48,81,32]),(216,[116,67,49,96,81,32]),(232,[64,116,49,96,81,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V7 low27 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := plain_low (m:=15) (hints:=1) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=15) (cap:=4) (before_sound K27 V27) (8,0,7,0,4) (by decide +kernel) (by decide +kernel))
def K15 := extendKnown K27 5 [(15,[]),(23,[67,16]),(39,[83,67,32,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V27 low15 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 5 := plain_low (m:=93) (hints:=50724866) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=93) (cap:=4) (before_sound K15 V15) (4,0,89,0,4) (by decide +kernel) (by decide +kernel))
def K93 := extendKnown K15 5 [(93,[]),(94,[67,16]),(109,[66,84,98,32,48]),(118,[100,82,32,48,16]),(155,[116,66,98,33,16,48]),(171,[118,84,33]),(174,[118,83,67,32,16]),(182,[116,100,66,82,50,16]),(218,[116,64,99,80,32,16]),(236,[67,116,99,80,16]),(248,[96,64,66,114,80,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V15 low93 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low203 : Lower true (varsX 203) (graphGoal 203) 5 := plain_low (m:=203) (hints:=855638017) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=203) (cap:=4) (before_sound K93 V93) (64,0,139,0,4) (by decide +kernel) (by decide +kernel))
def K203 := extendKnown K93 5 [(203,[]),(205,[33]),(217,[65,33,96]),(233,[112,81,65,33,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V203 : Known true K203 := extend_ok (m:=203) V93 low203 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := plain_low (m:=31) (hints:=65537) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=31) (cap:=5) (before_sound K203 V203) (16,0,15,0,5) (by decide +kernel) (by decide +kernel))
def K31 := extendKnown K203 6 [(31,[]),(47,[84,33]),(55,[67,83,16,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V203 low31 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[(0x8eff396382b2e3bfce58e0acb8eff396382b2e,0x10081428202c0402050a080b010081428202c),(0x813647695dce204d91da57738813647695dce2,0xb4ca422914c82d32908a45320b4ca422914c82),(0x1c17e1ed91c40705f87b647101c17e1ed91c4,0xa313c946914028c4f251a4500a313c9469140),(0x7e0b829466619f82e0a5199867e0b829466619,0x525b0ab051601496c2ac14580525b0ab051601),(0x0,0x0),(0x0,0x0),(0x7000e59724411c003965c91047000e59724411,0x2da0f54fae810b683d53eba042da0f54fae810),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(4,0,75,0,4),(0,64,7,8,5),(64,0,15,0,5),(2,0,77,0,4),(8,64,7,0,4)]
def g79A : List (List Nat) := [[],[33]]
def g79D4 (_ : Nat) : Nat := 0x5bd4910
def g79D5 (_ : Nat) : Nat := 0x908400e140fd21fe10fd10
def g79H5 (_ : Nat) : Nat := 0x7000
def g79D6 (_ : Nat) : Nat := 0x28189f
def g79H6 (_ : Nat) : Nat := 0x4c00000000000000016800050b40000000c80
def g79L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g79D4)
  | 5 => (3,1,3,0,0,5,0,g79D5)
  | 6 => (1,0,3,0,0,0,0,g79D6)
  | _ => emptyPacking
def g79I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 5 0 1 g79H5
  | 6 => lookupWord 1 23 0 7 2 1 g79H6
  | _ => fun _ => none
def g79 : Forest := ⟨79,6,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : block g79 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : block g79 4 0 1=true := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_0 : block g79 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B5 : block g79 5 0 3=true := g79P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P6_0 : block g79 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B6 : block g79 6 0 1=true := g79P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
  · exact g79B5
  · exact g79B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 7 := lower_forest (g:=g79) (i:=0) (hints:=50331649) (before_sound K31 V31) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K31 7 [(79,[]),(87,[67,16]),(143,[118]),(167,[118,83,67,32,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V31 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[(0xc3406101ffe38680c203ffc70d018407ff8e1a,0x824b860133a104970c026742092e1804ce8412),(0x9540b37c28cf2a8166f8519e5502cdf0a33caa,0x514511e485e0a28a23c90bc14514479217828),(0x0,0x0),(0x42a341c7c71c8546838f8e390a8d071f1c7215,0x408429f6cc04810853ed98090210a7db301204),(0x3c1c9e7c152078393cf82a40f07279f05481e0,0x30012ee0b70060025dc16e00c004bb82dc0180),(0x0,0x0),(0x28bf1c8210fc517e390421f8a2fc720843f145,0x883ad00900fb1075a01201f620eb402403ec41),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(2,0,89,0,4),(1,0,90,0,4),(8,0,83,0,4),(16,0,75,0,4),(64,0,27,0,4)]
def g91A : List (List Nat) := [[],[49,100],[16,67],[16,64,48,99],[48,16,97,65],[48,97],[64,99],[64,97,49,48],[96,49,65,16],[96,65]]
def g91D4 (_ : Nat) : Nat := 0x5dd4530
def g91D5 (_ : Nat) : Nat := 0x1030fd30fd10
def g91H5 (_ : Nat) : Nat := 0x90
def g91D6 (_ : Nat) : Nat := 0x23440bf
def g91H6 (_ : Nat) : Nat := 0x40803400000002876792f9915c2b5fb800000008a0
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (2,1,3,0,0,3,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 8 0 4 g91H5
  | 6 => lookupWord 3 17 5 9 1 4 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : block g91 4 0 1=true := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 2=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=50397185) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(173,[118,84,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 6 := plain_low (m:=243) (hints:=1416691713) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=243) (cap:=5) (before_sound K91 V91) (0,32,83,128,5) (by decide +kernel) (by decide +kernel))
def K243 := extendKnown K91 6 [(243,[]),(245,[118,84,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V91 low243 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[(0x3d84b0003ffac7f30f612c000ffeb1fcc3d84b,0x2980a94aa54886a30a602a52a95221a8c2980a),(0x0,0x0),(0x5f487003c1fc39e4d7d21c00f07f0e7935f487,0x164054a452323944c5901529148c8e51316405),(0x6096807c3e03e618d825a01f0f80f986360968,0x400602954ab76018500180a552add806140060),(0xb8610f80000000072e1843e000000001cb8610,0x3860039dcee10a610e1800e773b84298438600),(0xc2c84003c004381830b21000f0010e060c2c84,0xc0880b5badcc4418302202d6eb7311060c0880),(0x87330ffc0001000fe1ccc3ff00004003f87330,0x87110c6231009186a1c443188c402461a87110),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(0,32,89,4,5),(32,0,93,0,5),(0,16,45,64,5),(16,0,109,0,5)]
def g125A : List (List Nat) := [[],[48,98,84]]
def g125D6 (_ : Nat) : Nat := 0xe413f
def g125L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g125D6)
  | _ => emptyPacking
def g125I (_ _ : Nat) : Option (Nat × Nat) := none
def g125 : Forest := ⟨125,6,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 1=true := g125P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact (rfl : block g125 5 0 0 = true)
  · exact g125B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 7 := lower_forest (g:=g125) (i:=0) (hints:=52822018) (before_sound K243 V243) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K243 7 [(125,[]),(126,[67,16]),(187,[114,33,97,48]),(190,[118,83,67,32,16]),(222,[117,50,66,96,16]),(238,[83,112,50,98,64,16]),(246,[82,100,114,32,48,16]),(250,[99,48,114,64,16]),(252,[98,82,48,66,112,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V243 low125 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[(0x1fc3f1ffc093f43530001fc3f1ffc093f4353,0x94a02b19540d1642115294a02b19540d164211),(0x0,0x0),(0xc5e43fe00fb424300000c5e43fe00fb4243,0x6b5cd4c6aa40e90042ad6b5cd4c6aa40e90042),(0x3ff3e1fc03c444359cf83ff3e1fc03c444359c,0x421c00a4020040310c08421c00a4020040310c),(0xc0010600003b9ca82007c0010600003b9ca820,0xce790628cc8a1cb80039ce790628cc8a1cb800),(0x0,0x0),(0xfe029860023b838c2407fe029860023b838c24,0x318299433131830420c6318299433131830420),(0x3608001e6607088f80003608001e6607088,0xbde37e13c1f620c2c0f7bde37e13c1f620c2c0),(0x0,0x0)]
def g221C : List ColumnInfo := [(4,0,217,0,5),(0,4,216,1,5),(5,0,216,0,4),(0,16,141,64,5),(16,0,205,0,5),(128,0,93,0,5),(80,0,141,0,4)]
def g221A : List (List Nat) := [[],[96,66]]
def g221D5 (_ : Nat) : Nat := 0x17e52
def g221D6 (_ : Nat) : Nat := 0x1ac6881ff
def g221H6 (_ : Nat) : Nat := 0x0
def g221L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g221D5)
  | 6 => (1,0,3,0,0,0,0,g221D6)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 0 1 g221H6
  | _ => fun _ => none
def g221 : Forest := ⟨221,6,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P5_0 : block g221 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B5 : block g221 5 0 1=true := g221P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 1=true := g221P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact g221B5
  · exact g221B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 7 := lower_forest (g:=g221) (i:=0) (hints:=856031234) (before_sound K125 V125) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K125 7 [(221,[]),(235,[118,84,33]),(249,[96,66,82,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V125 low221 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[(0xf23d7015d482ba89f5807f3de47ae02ba90575,0xe010000554002ad201004215c020000aa80055),(0x99217ba1a67641673079aa613242f7434cec8,0x80017b000264428a01119a010002f60004c88),(0xc6e08948a5dd49678efd64c38dc112914bba92,0x6e2c84880d101001624240a0dc5909101a202),(0x30adf3054000928802601518615be60a800125,0x1faff3722374902df66415ca3f5fe6e446e920),(0x4d4606a24a2004100806a0449a8c0d44944008,0x7746284a7e8082575b2ee45eee8c5094fd0104),(0x3d4888c12118016008788a407a911182423002,0xb91924a72108007fe95bdaf17232494e421000),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,16,45,0,4),(1,8,54,0,4),(8,0,55,0,6),(16,0,47,0,6),(0,32,27,4,5),(32,0,31,0,6),(9,0,54,0,4),(36,0,27,0,4)]
def g63A : List (List Nat) := [[],[33,84],[16,67],[16,32,67,83],[32,16,83,67],[32,83]]
def g63D4 (_ : Nat) : Nat := 0x49d7690630
def g63D5 (_ : Nat) : Nat := 0x930c0afd8940b758630d754630e790630
def g63H5 (_ : Nat) : Nat := 0x160000
def g63D6 (_ : Nat) : Nat := 0x2a19080da2d402edb0762407f4437a81de30
def g63H6 (_ : Nat) : Nat := 0x5440000230018a002048fc3e40100000000000060
def g63D7 (_ : Nat) : Nat := 0x2b5c61bf
def g63H7 (_ : Nat) : Nat := 0x3c000004b74b55006a401eeb8bc19000006880000f3003c20000901
def g63L : Nat → Packing
  | 4 => (1,3,3,0,0,0,0,g63D4)
  | 5 => (4,2,3,0,0,5,0,g63D5)
  | 6 => (3,1,3,0,0,6,0,g63D6)
  | 7 => (1,0,3,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 7 0 3 g63H5
  | 6 => lookupWord 2 17 5 9 2 3 g63H6
  | 7 => lookupWord 4 23 5 9 2 3 g63H7
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P4_0 : block g63 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B4 : block g63 4 0 1=true := g63P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 4=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_2 : block g63 6 2 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 3=true := (@block_merge g63 6 0 2 1 g63P6_0 g63P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 1=true := g63P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact g63B4
  · exact g63B5
  · exact g63B6
  · exact g63B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=2162689) (before_sound K221 V221) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K221 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V221 low63 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := plain_low (m:=111) (hints:=52428801) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=111) (cap:=7) (before_sound K63 V63) (32,0,79,0,7) (by decide +kernel) (by decide +kernel))
def K111 := extendKnown K63 8 [(111,[]),(119,[67,16]),(159,[118,84,33]),(183,[118,83,67,32,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := plain_low (m:=207) (hints:=855638017) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=207) (cap:=7) (before_sound K111 V111) (128,0,79,0,7) (by decide +kernel) (by decide +kernel))
def K207 := extendKnown K111 8 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V111 low207 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 8 := plain_low (m:=219) (hints:=855703553) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=219) (cap:=7) (before_sound K207 V207) (128,0,91,0,7) (by decide +kernel) (by decide +kernel))
def K219 := extendKnown K207 8 [(219,[]),(237,[118,84,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V207 low219 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[(0x15fd53701f21314071f82a4057f54dc07c84c5,0x10a000701f0101650a04e040428001c07c0405),(0x4be1ec09e045a4838e33ad512f87b027811692,0x43496001a040a098214015090d258006810282),(0x4c14bfbf460094400fc001813052fefd180251,0xac169f8e40981402d4b10082b05a7e39026050),(0x344800cba8e80b0c700c0238d120032ea3a02c,0xa558288980e0021094da063e9560a226038008),(0x8a0202049b1640b38003d6d6280808126c5902,0xa80682501a060004969be2f6a01a0940681800),(0x0,0x0),(0xe022418675da4a3c000450af80890619d76928,0x52a155266518482b692411014a855499946120),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(2,0,93,0,5),(1,0,94,0,5),(4,0,91,0,7),(8,0,87,0,7),(16,0,79,0,7),(0,64,7,24,6),(64,0,31,0,6)]
def g95A : List (List Nat) := [[],[16,67]]
def g95D5 (_ : Nat) : Nat := 0x4ef7258610
def g95D6 (_ : Nat) : Nat := 0x2044080104200ac85b400bf58610fbd8910bbd8910b758c10bb58810
def g95H6 (_ : Nat) : Nat := 0x140
def g95D7 (_ : Nat) : Nat := 0x196f2804756bca101d972e8407888807f843fa21fc10
def g95H7 (_ : Nat) : Nat := 0x6973000041c200f4000060
def g95D8 (_ : Nat) : Nat := 0x5d1a17f
def g95H8 (_ : Nat) : Nat := 0xc004e00000710000072
def g95L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g95D5)
  | 6 => (5,2,3,0,0,6,0,g95D6)
  | 7 => (3,1,3,0,0,7,0,g95D7)
  | 8 => (1,0,3,0,0,0,0,g95D8)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 0 1 g95H6
  | 7 => lookupWord 2 11 4 8 3 1 g95H7
  | 8 => lookupWord 1 11 0 7 2 1 g95H8
  | _ => fun _ => none
def g95 : Forest := ⟨95,8,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 1=true := g95P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_3 : block g95 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 5=true := (@block_merge g95 6 0 3 2 g95P6_0 g95P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 3=true := g95P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 1=true := g95P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=50397185) (before_sound K219 V219) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K219 9 [(95,[]),(175,[118,84,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V219 low95 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0xfffffdc900091012c00230fbdfb4c2700264,0x2b2b2b00004701446c007a20e0d394c271e060),(0xff00fff9d5b07a2d111e05e0931e35c08c18a4,0x444444060790022000180440130c2100881084),(0xffff00260d90477b03e483906ce1c208021e48,0x909090f9c000009913c781900c204208020a08),(0x0,0x0),(0x11223b007ec1b5c6b0c80091f266091,0x191919019021b0076827f031cc800835264001),(0x12207d85c24c20a04c04306a30d9850a,0x7070702303405424c286a4f021028b0190402),(0x464e0418e401580f0044580f226011,0xe6e6e640664e06188440090e3064514a002010),(0x820cfa080a9802404000b0034d98102,0xf8f8f88800cbb0a0a3901480010b8605c08100),(0x0,0x0)]
def g247C : List ColumnInfo := [(4,0,243,0,6),(1,0,246,0,7),(0,128,87,32,8),(2,0,245,0,6),(64,0,183,0,8),(0,64,167,16,8),(128,0,119,0,8),(80,0,167,0,7),(32,128,87,0,7)]
def g247A : List (List Nat) := [[],[33,84,118]]
def g247D6 (_ : Nat) : Nat := 0xc60fe121c83109fb805c910fe12148110
def g247D7 (_ : Nat) : Nat := 0x8200190200208000008200000208396dae818036ba6d9062ed969a89b1a59981755d514539211508f0d8843c01fd48510fec42885fd72442ffb9221fec8310fea43885fd72c42feb8043fe1c121ff6e090dff70486feb8443fe48110bfae510df970086eeb98437edc121
def g247H7 (_ : Nat) : Nat := 0x1a800000000680001880
def g247D8 (_ : Nat) : Nat := 0x2f5a5b0008c8b5e95c0c012312b5eb418024deb405b030918402d2adc61270a5184cc03fe21ff487fc21ffc43fd10
def g247H8 (_ : Nat) : Nat := 0x307000000028620c004c0000200000000c29d020684000000000000000f3c00515cc0000000000000a100000038000014d0ac0092ec200000d26000c1000000
def g247D9 (_ : Nat) : Nat := 0xcb0e22ff
def g247H9 (_ : Nat) : Nat := 0x58c193f4cc0049a29000000000
def g247L : Nat → Packing
  | 6 => (3,3,4,0,0,4,0,g247D6)
  | 7 => (17,2,4,0,0,8,0,g247D7)
  | 8 => (5,1,4,0,0,8,0,g247D8)
  | 9 => (1,0,4,0,0,0,0,g247D9)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 7 2 1 g247H7
  | 8 => lookupWord 6 47 6 10 5 1 g247H8
  | 9 => lookupWord 2 13 4 8 3 1 g247H9
  | _ => fun _ => none
def g247 : Forest := ⟨247,9,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 3=true := g247P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_3 : block g247 7 3 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 17=true := (@block_merge g247 7 0 3 14 g247P7_0 g247P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 5=true := g247P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 1=true := g247P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact g247B6
  · exact g247B7
  · exact g247B8
  · exact g247B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 10 := lower_forest (g:=g247) (i:=0) (hints:=1411448833) (before_sound K95 V95) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K95 10 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V95 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[(0x681a704149021c0385040f5ea29aa05e8908c,0x68bddc5f0840010b050402de4318901e80088),(0x80202401b014a4a52a34c5aa09b67233e10e,0x9130200a09701ca70c0210c01b4a367211e006),(0x0,0x0),(0xf07402200fe865561ed04a7241e218041778b0,0x181402200569014408201ad200c20004127030),(0xe0b9f21f404c828e12fb50000944d74d20702,0x2c0ed621540e4000a12da51400b44804420300),(0x181d0fb8c5712454601a2085404a0ab080041,0x17b9c2a7ad7717cd4685ae22c600a0e1000040),(0xeffadcffa708cbc4684cb0001124188e1ae20,0xc3e129dea8108eb84692400021080188a18c00),(0xf1007dda410fd2030049000a14c5529b0c4051,0xe0423d585000c002114801091805561a0c0001),(0x0,0x0)]
def g251C : List ColumnInfo := [(64,0,187,0,7),(2,0,249,0,7),(16,0,235,0,7),(0,32,91,128,8),(32,0,219,0,8),(1,0,250,0,7),(16,2,232,1,5),(8,0,243,0,6),(3,0,248,0,5),(160,0,91,0,7),(1,2,232,16,5),(0,16,169,66,6),(64,16,169,2,5),(19,0,232,0,4),(0,2,232,17,6),(18,0,233,0,5)]
def g251A : List (List Nat) := [[],[96,65]]
def g251D7 (_ : Nat) : Nat := 0x33040091080000074cc2d330b4cc2f1cb3609d22136484805fd75c86ffbaa437fdc950bfaeb907f930c82ffbaa417f5d520ff2a0905dd73c86fdb82437ddc530
def g251D8 (_ : Nat) : Nat := 0x526e7944b1f20152660a88ca414998aa0b8aca6470526a61625b4f308b2c2989c827412d472c4a02c530ab2729283d2662847b54f208c74a1705200ff4c7ff21ff487fd50ff4c3ff20ff483fd10
def g251H8 (_ : Nat) : Nat := 0x4160520000000219660011c13caa20009f942908c00
def g251D9 (_ : Nat) : Nat := 0x72084a23ff
def g251H9 (_ : Nat) : Nat := 0xcb3000b50000000002b300009a0056000000000000000000c427000000180e29e1000000003d0000000000000000000000
def g251L : Nat → Packing
  | 7 => (11,2,4,0,0,7,0,g251D7)
  | 8 => (8,1,4,0,0,9,0,g251D8)
  | 9 => (1,0,4,0,0,0,0,g251D9)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 17 5 9 4 1 g251H8
  | 9 => lookupWord 4 47 6 8 3 1 g251H9
  | _ => fun _ => none
def g251 : Forest := ⟨251,9,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_3 : block g251 7 3 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 11=true := (@block_merge g251 7 0 3 8 g251P7_0 g251P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 8=true := g251P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 1=true := g251P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact (rfl : block g251 6 0 0 = true)
  · exact g251B7
  · exact g251B8
  · exact g251B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 10 := lower_forest (g:=g251) (i:=0) (hints:=863043585) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 10 [(251,[]),(253,[118,84,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),(0x1fff881030c130fa4ad951308703f0c1,0x535b554a95210430c120aa004840208700f081),(0xfe03f810008803601a6d9c797c5810151,0x8c208a346896a90018971126958f9340f90050),(0x7c1f0000068efa3008102580426421bddd02c,0x38c630e1c3ea1d820049805c09024213d1c00c),(0x3e001fc01a10545c8dfc49a238ec42220482,0xa884a2a54a9a3bc00e9d54f98038cc00020400),(0xf8000fe000051068a74205e42080a538822b10,0x71ce71c38749106f826064c020002438020300),(0x3ff0000012ccef390c0001220f09f8389426,0x47394d1a3400c03d31000000728501e8281022),(0xffc00000006423003fc30e1006205a24446a08,0x86318e1c3814e2007d820b0306601804042800),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,7),(2,0,252,0,7),(0,2,232,20,6),(0,4,216,34,6),(8,0,246,0,7),(0,8,54,192,6),(16,0,238,0,7),(0,16,172,66,6),(32,0,222,0,7),(0,32,90,132,6),(64,0,190,0,7),(0,64,166,24,6),(128,0,126,0,7),(0,128,86,40,6)]
def g254A : List (List Nat) := [[],[66,115,101],[33,84,118],[33,81,99,65,116,67],[49,98,33,116,84,81],[49,114,100],[65,33,115,98,82,83],[65,98,83],[81,99,116],[81,114,67,50,49,97],[97,50,117],[97,66,83,50,33,114],[113,50,33,84,100,66],[113,82,67]]
def g254D7 (_ : Nat) : Nat := 0x17ddc540
def g254D8 (_ : Nat) : Nat := 0x1ac5a8e6290604242239ac5a928398602882439ac5a928398a4188203a613003fd40ff483fd10
def g254H8 (_ : Nat) : Nat := 0xc000
def g254D9 (_ : Nat) : Nat := 0x1950c8203ff
def g254H9 (_ : Nat) : Nat := 0xeb0000051b550000028c00409ce29988584a929c004334049262b4800000856a9a0d42ae8cc100000
def g254L : Nat → Packing
  | 7 => (1,2,4,0,0,0,0,g254D7)
  | 8 => (3,1,4,0,0,8,0,g254D8)
  | 9 => (1,0,4,0,0,0,0,g254D9)
  | _ => emptyPacking
def g254I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 0 8 0 4 g254H8
  | 9 => lookupWord 7 29 5 10 2 4 g254H9
  | _ => fun _ => none
def g254 : Forest := ⟨254,9,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P7_0 : block g254 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B7 : block g254 7 0 1=true := g254P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P8_0 : block g254 8 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B8 : block g254 8 0 3=true := g254P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P9_0 : block g254 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B9 : block g254 9 0 1=true := g254P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : checkedTables g254 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact (rfl : block g254 6 0 0 = true)
  · exact g254B7
  · exact g254B8
  · exact g254B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 10 := lower_forest (g:=g254) (i:=0) (hints:=857825568) (before_sound K251 V251) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K251 10 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V251 low254 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0x27581273269dc6c968aac64cd8043111725c80,0xfa5840120214c6004828400458043010305400),(0x80347a8016518db93a753dc222a188802aba50,0x2526410c6310bd22502cc220218880028a40),(0x1840800100c602442c3811b1ff2d76a804295,0x20880f0082002008381080680476a800091),(0x36cc857360a31242a40cb2a0e0b128c9d5040a,0x484836524a91852b3049ba0a0f04889c10002),(0xceb3e88c8b40291011145a84c80e2d1608a160,0xce92c98c12806b40910e5200cd0e2102082100),(0x680002a011001840450003115524222800005,0xf6d5276e01318bd50c5460f5f15a90053f8004),(0x5863851cc9223002cd20647e220d04fc05012a,0x30692410c94684294ca1245f02010674040028),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(1,8,54,64,5),(16,0,111,0,8),(8,0,119,0,8),(0,32,91,4,8),(64,0,63,0,8),(2,0,125,0,7),(1,0,126,0,7),(33,0,94,0,5),(32,0,95,0,9),(2,16,45,64,5),(4,32,91,0,7),(44,0,83,0,4),(37,0,90,0,4),(0,16,45,66,6),(50,0,77,0,4),(48,0,79,0,7),(36,0,91,0,7),(1,32,90,4,5),(2,32,89,4,5),(40,0,87,0,7),(96,0,31,0,6),(82,0,45,0,4),(34,0,93,0,5),(0,64,39,24,7),(24,64,39,0,5),(32,64,7,24,6),(8,32,83,4,5),(16,32,75,4,5),(64,32,27,4,5),(100,0,27,0,4),(0,8,54,65,6),(9,0,118,0,5),(8,64,39,16,6),(16,64,39,8,6),(38,0,89,0,4),(18,0,109,0,5),(65,8,54,0,4),(72,0,55,0,6),(52,0,75,0,4),(80,0,47,0,6),(41,0,86,0,4)]
def g127A : List (List Nat) := [[],[16,67]]
def g127D5 (_ : Nat) : Nat := 0x30a53e8d762097544316892e01755cd10
def g127D6 (_ : Nat) : Nat := 0x2c4040000018304001c170820000000000341040000004000000000000000000000000000002c4040e081a950a7936984aa3514873d1dce871371acd0652e968ae4f261248c43200f474371a0c45c2b14094441f0e0642c130582000abac8ca4b8c6199d8750e418c2ad924c2ae30845f662525c610abcc84a4b8c21b7161e0151843bc2e290a4108557e4d765d510cb7bb104baa2196d7620975442fc32518a408855b249755cd10cbdc02eab9a2117d98dce52442ed124bac80884de6625290110bb8c8ca520221768925d540442ee722baa80885dc64652501109f84c262a022156c925d773442abf26c32e12955de45845c252aba48b08b84a547f9650d7094aaf32140ae12964f5d18194a609bdc8303294c117d9894971982aeb23292e330657dcd81949608becc4a4b8c6195f73602525828ff2ca1ee2a864fe137158550cafc1ee2b02a187d76606529022fb31292e32055d646525c640cbbb8f00a8a8195d8750e528c2ad924c2ae3184dee418194960
def g127H6 (_ : Nat) : Nat := 0xf009c0b40
def g127D7 (j : Nat) : Nat := (if j<1 then 0x48c4744534324234023bd39c37b35a3393182f72df2c72a627325b23a2191ef1ce1a418316214a1320f60d50bd0a508406304b021000bf98098520bbf8458520df771585209fd8790520bed8290520bf980905209fd878c520afd868c520bed828c520bf9808c520ddd32dc530bdf8358120bef82501209ff825d210d7d7494a10d7d7394a10b7d8194a10bf78150a10d7d855c6109ff825c610d7e525c6109ff874c520d7f7154530b7f8054530bdf824c530ddf724c530f5e524c530f5d514c5309fd8798620bf98098620bbf84586209fd8790620df77198520bdf835d920bf7815d120bf4815d1209fd81dcd209ff815cd20aff8650d20bef814c920bf9809c5209fd8798520bdd8398520bed8298520bf98090620d7d7454110b7f8154110f797590110bf98290110f7a5290110bf78150110f795050110f797550110bfb8250110f7a5250110bbf8458610def7248110feb7248110fe93248110ff23148110ff13148110fe92148110ded865c810ddd7358810ded7258810d7d7394810ff13150110d7d7354610f7561546109fd8748610ded7248610bfb8250210f7a5250210df97148210fe92148210bdf835d910d7f765d510d7f7454110d7d75dcd109fd82dcd10d7d755cd109ff825cd10aff8650d10def825c910b7d8794910d7f7394910d7d7394910b7d8094910bdf8358110d7d765d510b7f8058550d7d635c252d7f7158150d7d835c252d7d645c252d7d7394a40b7d8194a40d7e525c640b7d8094940d7d73546409fd82dcd409fd81dcd40dbd43dc940d7d865c2529fd81dc940d7f7394940b7d8194a60b7d8194940d7d845c252d7d855c6609ff825c660d7e525c6609fd81dc960b7d81949609fd80dc532b7d80949609fd82dc560d7f7158550ddd43dc5329fd80dd132d7d64dc550d7d63dc550d7d43dc550d7d815c252d7e815c252b7d8098550d7d435c252d7e52dc560ddd435c630f3d4394940d7e525c6309fd81dc162f5d4354630d7d71546309fd8790630f9d43906309fd82dd130d7d855c6309fd81dc930d7f7494930d7d7494930b7d8194930b7d8094930ddf744c930bdf814c9309fd82dc530d7e52dc5309ff825d130dbf7350940bfb804c940d7e52dc540d7f7354540b7f80545409fc874c540b7f81541409ff825c6309ff825d230ddd435ca30d7d7494a30f5d4394a30b7d8194a30f9d4350a30d7f7154140d6f855c810fe12148110c7d7694810d6d729481097d879481097f815c25297d8794a60d3d7494a60a7f8650e529f7815d12097f875463097d8794a30d77715454097d8794a10b798094a10c7d765464097f8754640b7b8054610c7d7694a40d5d7394810b5f8358150b3f8458550b6c825d510b5d839855097e8798550a7f8650d5097d8794910b798094910d5f7394960b77815411097d8794a40 else 0x810c2c462820250420182020322820810c2018202c462820322820810c203118a081a8a08100308000248508120b202c100f90100c104628200000083030604100308860e2314102006101c8c505c8c505c8c504000c10162314101a14110c101820081e2314101914110c1010b06081c0708003060d0a020d04102020e2307050e900c25064a03040bc1800300000817904a0d86c80a8748080943a406000010210c10a860304044a040002083080c4a0b90085010780c20982030404000f90162306172018104424100c1008611430788c184c16104001424404c20d0400012c221702200c10000182020102c40588c20e06080184004b0285c208030436106410400c20182080185820406080b04080c10150416200420102000c404221208220e2016202031002120988100c1046282622602a402080184c4a184030404070410030804ba1020000000182020010030a86080416182041410400c0018003e404080184c404062260209217041b1286180e860b220d050c0c05e412b0609000f4842a18303a190a1d210c850f831008860808a183a450d0c1e2306172314102094030f8982040450c2d2a86102086860c2210430748a521a86212806090c2286829284a450d0c1d210a860f118a0b118a0b89c1e11430d85188b88c50608450588c5040808848308a18a01d228615210b0625080808a183fb4f9cf84f6cf54f3cf24f0cef4edced6ebeea6e8ee88e82e6ae5be43e2be1ce04dfedf8df2decddddcedb6da7d8fd77d71d59d41d29d23d0bcf3cdbccccabc93c7bc6cc66c4ec36c30c2ac12c03bf4beebdfbbeb9db85b64b5eb4fb2eb16afeaddad7ac8ac2aa1a89a7aa74a6ea56a3ea2fa20a089f99e19db9c39ab99397b96c96694592d91590f9098f18d98d38cd8a389488e8888708618528318198137e97e37cb7bc7a479577d76e75674772f7207086f96f36ed6de6c66b76a869969367b66365463c6246155fd5e55cd5be5a65a058858257c57657055855253a52b51c50d5074f84d74d14b94a1492)
def g127H7 (_ : Nat) : Nat := 0x24a41ef46e0ad04916116628da86a498a2ce78b1c909c6e88cecfd580225a1cc0032060100198144c9524569855685a1c00000000000cae06e259b620e8900052e00054d070000034ea1900000327e9f41e0038d6580002854826120145b89e52e14085001a08006000808302281800a3c401
def g127D8 (j : Nat) : Nat := (if j<1 then 0x2291320608218509000c0622c80a1d0891151185822818817030d01c410c88206247c172079801908704170281000c054a50062a1209410e1686061880417030210c80009062612092a190e86042480417080d021e8ac10c26125e0609421a14704108105c86000421e251063218002190824817040d010542001ec88a28105c04341722290878917c41e020d0581014a50285c10780904149b222824a8109c448054aa0868227120942150e861a0480417021ec88a4109225f210818280061f1ec4c10905d006c8243304271003081817209212005d006c818471307084118621c82009d00618821320874218681c82009d0061848231304a029161888217c881d009001e2be89e224a88321ce862216284f20f6834209a813201e7f81faa7db1f267be1ed27af1e7e7921e027771d867561d2a73d1cb671e1c3a7051be66e81b7a6d31b266ba1ac26a51a5e68819d2663195e64e191263b18b66201862613181e5f617a25d917365c016ba59b164657a15b255d153653a14b251b14164f4138a4c912e64ac126a48b11ee470117a45310f642a106a4010fae3de0f1a3b10e8e3900e0236b0d663480cda3230c4e3020bc22df0b462c00aba29d0a1e27609aa255090e232087220707ee1ec076a1c706de1a2064217d05ae1580522135048e10e03ea0e5033e0bc02aa099022e0780192057012603c00ba021003e0003fe98a41ff8c520ffa82907fe41483feb0a41ff98520ffae2907fe71483fea1a41ff58d20ffae6907fd428c3feba241ff5d920ffa83107fd61883ff30c41ff59220ffa80987fd414c3ff20a61ff50930ffc83187fd64483feb1021ff48110ffa60887fd40443feb0221ff4c910ffac4887fd72443ffb9221ff50d10ffac6887fd60483ffb9a21ff5d910ffeec887fd21843fea0c21ff58610ffa85087fd62843feb2421ff4c120ffa80907fd73443ff20c41ff4c940ffa62a07ff73503ffb9281df5d510bfae3307f920843fca04217fdc960efca4b077d51842ffb8ac17f5c610efac8a877e52843beb1aa17f5ca10bfae70877d43542feba421df58550efca5305fd72042feb9821fe48110bfee0b17fa20443beb1ca5fe50110efa87297fa40443bea8221df98550efca4885fd744cafeb9221f750d32bfee4885ff714caffb82657f5cd10bfae5305ff73442ffba2657fdc540efaa2a05fd71882feb9c417f5d220efaa0a077d504c3ee98a617f5d230f7a84a077e528c3bea8a617fdc530fba64985fd728c3bf292617fdc930bfae8985ff744c3eea1c61fb48520efac0a85fd718c2feb9c817f5ca40efca5205fd71903bea8c817fdc520efca4085ff73503dea1a817f5cd20bfee6905ff72502feba241df54630efca4a05ff74483f699241775cc10bdae4084fd76042beb84a56f5d260bbee6b04fd76902bfb8aa13fdd943 else 0x322008022850c0544488842068a208e2004362850c05488841068a1c54105e2104162870c4888420544068a2320308a284c80c058a10611220043408022881725888a132079087c2e286260643488883010d82272035049a2851744c842241d8a1c8c1a2004362861506041788418a1c5d22210801101a288271706888a1434047a0841e1f087c15210c08790471e1f4348010d181419210e220d060881727888a107418105d0d220e060840a0c05c84a0616220c7c14005830d0105c806185e220d0890141870b4348888302001c74105d0d22220c74a500c22112b2018154051844888301020009205c96220c41742248a90150f21080041744c8414224151d105d0f204484a22060516220c8c1824146178883411506051c98190d22220c04142491d06041743488883209c5c1a220c5881f008a1034062a404c81e421f10152221041a2860b4348020006183408003420d0841210c043454808c4c1c24a8685200c432080841860c090005064a501e5f2104182452105174ac8241a094042150e128680808849782c1094a058624432084904170403010210c8000905062d819d5c1a22286849781825085861d85941a21115e28717040d0102004a5006247c43210878186445845410086428a205c107808432024341904a416160068844578a2205410e161a1286808174a03c450c809c100c20605307c432078150818709050c064a5018848074145e122a408220905064a00501d8621951a0d115c797c841060915124115611a0d050882397c800091520225e120608012a1418a42454461605706888a265e120609421a1471704a00905820006c88a410d305c1034047808308b2128a4418c88a4100185c103404780b2018152940b17010dc41e0b068a8290282c162a0a4000617040d0110421fc80024848030152819407041703010d10c800421e28120a8024341b2228817041e02d081c80922120815290e860424817040d01028a009006247c172229087818717041e02c88a41092310021686070928188281f8500a006824a2210241720800060410c8090da00641211210001887212824881c4504385a08682221026052015290e821a08a0417010d101ec81f221321288000517010dc4820c054a06502a120542150e821a0880417010d05c84a1f205c104321042680021a08a0410c809a01f410d868)
def g127H8 (_ : Nat) : Nat := 0xddc76f800000300070f9c3bc83d2280010b34ae0000003f7940eab38003d7b83454aa50f50a000e5e000297c60f21540f400000000000000011ba34521f40000000000000000000a030003154679b2a80038e40b30003c8985b8206d1914400000000032d6cea000b33000000138f0000001d1c000fc960040000000000000000c80035bae80004a80007a9e7040000003d0072a01c8058000000f73000000302ac30e37800000000000000000000b700016a8001aa40000001c6e0000003306b76000000198c000000000199e93ca8b5204a63301b210000000000000d818002ae286294d6ab441b9c100066e5894000000000000079443812980000000005ae0a1a0000001904000846000000000161b1438001d0d0b4000000185e29f0000000c73e6cfa800034900000001ab00000000000003b1600000000010fe0000000000000c31d16000209b86863d000389765f72f00004ae0000000000000000350f04bb48000380d659b4c000548000000124400079a40000000000003c3200011f8003cc0000f5929256fa000955f58fcef46d00015d0000000e040868000000000000380a000000000000000754e0000001a264355e100000000000001412000000000253a0004d3800000000084b000211800082d8000000000000709400064e000000000170b126000000000023a61bb140000d13800000000003b2e28000000c0b5ac000003a000000000083c142555800047e00002a6f7a00000000000000000000000000a94b2e464000000000000000006a2cd856c68f6377ac400020e200000000000000000000000001f890b60000001291c29f829563c560bdc0d7851489b10d0cfe0a632221884f8a4e14000000000077664980003300000000001337e0000071f00000000006a34000000f4de85ced7e2e70fd89155e29742780014ca000e14ea8dd040000000002d10cc0e5f800000000000000000000004c28000000000c94bea4001418000000094a000c11e80b2f13ac00048d9ce6f6a1a2000000041ee08800000000000036340000000005951456000000000000000042d2587c21c8f0003141f2603b083800180800000071840010425cb80000014810003190001a92000000041884702c3088001c9900000000000000000000001e380002cd74f01095ab800000000000000017800000000000976986290217466800000002d800000000054f717200000c000100000c020001200800000000180000400000010240200002004020100000000008030000000002000020000100c0000803000000000500000000010000000c11000000080000000000000000000c0800400000010000001400004000080200c0100402004000000000000
def g127D9 (_ : Nat) : Nat := 0xb8389220c2a0182925c1c49106100a0143145c605882a0c2201892e1624101085100c49e3e1622091041500c5030b12441a080106242c443200c2a02431210b83020885089204c101083053c10509210a0a018806042d009210a00c48b0a1a2201504110005050c10521828211024205301a22090041501200c4a18248434000e10185892210013410810c608890610a0c34483088091b2103db72cd2982ac04a284ce718227a38c56052044003fd10ff843fd20ff883fd30ff8c3fd40ff043fd60ff983fd32ff58bfd43ff58ffe40df5437e52
def g127H9 (_ : Nat) : Nat := 0xb33803caf20000006898001a5ce17785de8e0008bf800000000011c0000000000000698c0018000000000001c230005c16c16078000000000000000000000000000000000cb60004388000001f4a00059d1e23818d3c80024a5e460007c3042641233820a526575dc12bcd2cd4000e0800010ba000000000170ac586b989454d7e6611de186c759430001a080006070004dc80000002c5982800005a127894f517884e0100004aa00003b800103200063e2de0001c09306800011be0c518487c000000c250001492000523885400000039092338c844119c000000122a0000000c69220e00800345e0055c5342fa520008b4800000175e0003e33a3bf7e7b8000000000000068526cb11702b8000000000ba9000000078d0007158c91833941d8b0484000000000000163783f0000001745e3178c8efa17c2019cf58780000000002d140000000000000000a0259f4000c4583d9d200000003c140e40000004a7d0adad6a36e40ac7e6e9e3e0005d02a4ee5e000789c4d87620000c9800110d00b4e2546ba76b203cf0000e800140000001b3e000000000161a000000000000000071cc000000000000148708500000f7cdb406f0eee2090d5763a0a0714c03423348000000000000000045ae0e00d80000000000000000001854000000387f86e8b880034cb044827094000100898441d40f41640004846c42f660000003d1224d292b92cd0e00052c8003ec600000039fc00106f000000165e00072679c80008221b0e0909100000003c54001b4e0002d4c000c31d0f00000014680000002e8800000000018be03018001a000100800010080400030180000000080002080180402010000c02000001400000101400040201006010301436000100c0a00000040200010000200008040000018000400048000001
def g127D10 (_ : Nat) : Nat := 0x84021202ff
def g127H10 (_ : Nat) : Nat := 0xabcab0022a00000f8400c3400c9800ab800003a21100b21c00000890000088cc300168002ac53c00002ca69fcc00000001c8f040030bce7400041800400000026d5140003084001004
def g127L : Nat → Packing
  | 5 => (2,5,6,0,0,3,0,g127D5)
  | 6 => (44,4,6,0,0,9,0,g127D6)
  | 7 => (194,3,6,0,0,12,0,g127D7)
  | 8 => (142,2,6,0,0,14,0,g127D8)
  | 9 => (17,1,6,0,0,11,0,g127D9)
  | 10 => (1,0,6,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 11 0 6 1 1 g127H6
  | 7 => lookupWord 19 73 7 11 6 1 g127H7
  | 8 => lookupWord 88 541 10 13 8 1 g127H8
  | 9 => lookupWord 69 359 9 13 8 1 g127H9
  | 10 => lookupWord 9 53 6 10 5 1 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 2=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 44=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 44=true := g127P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_31 : block g127 7 31 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_127 : block g127 7 127 67=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 194=true := (@block_merge g127 7 0 31 163 g127P7_0 (@block_merge g127 7 31 96 67 g127P7_31 g127P7_127))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_9 : block g127 8 9 80=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_89 : block g127 8 89 53=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 142=true := (@block_merge g127 8 0 9 133 g127P8_0 (@block_merge g127 8 9 80 53 g127P8_9 g127P8_89))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_2 : block g127 9 2 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 17=true := (@block_merge g127 9 0 2 15 g127P9_0 g127P9_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=52494337) (before_sound K254 V254) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K254 11 [(127,[]),(191,[118,84,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V254 low127 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[(0x9401e6015e469839832cbf1ec82129a80a5314,0xa00276803c0008288220831a482121a0021104),(0x95f0c1c70d15647b948bc8a00210068bf51268,0x517001018075205300c908000010060ba40228),(0x2d1200250035f421f275466c8064c315a0074,0x68d0832430257805d06546490ced810580050),(0x4a0c1f3082e88000205826d105ff1251e46903,0x800003c02e6a00000496480010a1051e44003),(0x2b2208ec21102384db8021883601e966818488,0xaa8408fc75808500db102288bf012860018400),(0x0,0x0),(0x691a030928a85b864800892d704ee30420a482,0x517b670308195a8f242489254044c304002080),(0x20418708008007420d2105225901050040801,0xb2fd7943d8085bf46392115b26b0048e1a8800),(0x0,0x0)]
def g223C : List ColumnInfo := [(0,4,216,3,6),(8,128,87,0,7),(16,0,207,0,8),(64,0,159,0,8),(0,128,87,8,8),(128,0,95,0,9),(2,0,221,0,7),(1,0,222,0,7),(130,0,93,0,5),(4,0,219,0,8),(136,0,87,0,7),(0,192,7,24,6),(64,128,23,8,6),(9,128,86,0,4),(18,0,205,0,5),(7,0,216,0,4),(2,4,216,1,5),(6,0,217,0,5),(5,0,218,0,5),(1,4,216,2,5),(2,16,141,64,5),(0,16,141,66,6),(140,0,83,0,4),(20,0,203,0,5),(68,0,155,0,5),(80,0,143,0,7),(192,0,31,0,6),(136,64,7,16,5),(1,128,86,8,5),(4,128,83,8,5),(80,128,7,8,5),(72,128,23,0,5),(137,0,86,0,4),(144,64,7,8,5),(3,4,216,0,4),(82,0,141,0,4),(88,128,7,0,4),(133,0,90,0,4)]
def g223A : List (List Nat) := [[]]
def g223D6 (_ : Nat) : Nat := 0xd08103410741040100100000000000000000070c1000000711c30800000000342040000000000b257ab152a651a813a9a4923d0e7f3e1d0e26e359a0ca622f970b256299409045210fc782f160a44c23100742a120783012060180156f9550f724423df30ba8e48856be51751c910c7743aca392211ef985d072442bcf22ba0e48847be61731c910af5c82e6392218ee8798c724438dacbb92a28853b656635c810bd8ca10098a217e192201314431df0bb92c0884fc2613150110f70b2c4310221ee26388620443dc2ca90a40887b898d2148110a6ecaf0cb98218bd855d2630431bb0ab9cc60866be137254510a7cc8502b84c74ef926057098e9f720c0ae131e3b98f825c241cd6a1f04b84831fb985c0704c71f6ebc0242b053b65e6350a20d7531f00a1441ba943e01428829db2f31c431053b64263dc910e7331ae310c41ae965602218835d4c6c04431053de457498d20e3ab2ee2a8a419e882e01734429df24ba4c68856be5175dc910ad7ca30bb92214ef90597724429db2b31ee4887395957188620
def g223D7 (j : Nat) : Nat := (if j<1 then 0xd7458110def7254110bf78154110efa6390110ff13190110def7250110bf78150110ef96050110efa6350110feb7250110fe87250110ff13150110ded75dc910def724c110fd5314c110ef96588110efa6388110ff13188110ef96548110efa6348110ff13148110ddd855cc10afd8598c10cfd7498c10dbd7454c10ddd7354c10cfd655c810cfe635c810ff12150110eed65dc910ded74dc910ded73dc910eee63dc910ded85dc910ded84dc910ded83dc910ded53dc910ded43dc910cfd655c910cfe635c910ded751c910eed651c910ded741c910ef56548510eee631c910e7d6554510bbf8454510def7254510def7250510def724c510bfb804c510fd5434c510fe7724c510fe4724c510ff3804c510ff0804c510ef56588510bf58388510ef66388510ded731c9109ff805ce21afd8598e21cfd7498e21afd8098e21ded744ca21cfd655c221cfe635c221aff80595219fd83dd1219ff835d121afd8598d21cff7498d21cfd7498d21cfe635ca40afd8098d21b7f8550d21def7350921eee6350921e7d6554521bbf8454521cfd65dc121cfe63dc121aff8050560cff7588560afd8488560cff7548560bfb80485509fd80dcd42afd8098d429fd80dd132dbd43dc1429ff805ce41afd8098e41cfe635ca41dbd435ca41cfe635c241dbd435c241cfe63dc1429fd80dcd41afd8098d419fd83dc941cfe63dc941dbf7350941aff80596219fd83dc141cfe63dc141cfe63dc5429fd80dd1319ff805d131bfb805c931bf8805c931bf78150931bf5819c131dfb709c131bef825c131bbd841c131bed821c131df9701c131ebe6350941bfb805c5309fd8790530bdd8390530fdb804c530fd8804c5309fd8788530bdd8388530bdf83501309ff835d220cfe815c263afd8598e20cfd7498e20b7f8550e20ded7350a20eee6350a209fe8788550cfd825c263cfd655c620cfe635c620e7d6554620bbf84546209ff874c6209fd874c620ddd734c620df5714c620eed6588620ded535c810bed8488620ded7388620eee6388620cfd845c263fad4350a20cfe635c6409ff874c6409fd81dcd429fd874c640ddd734c640df5714c6409fd81dcd40afd8098d409fd83dc940cfe63dc940dbd43dc940bbf8350940dbf7350940ebe6350940bef825c530bf9809c530ebd4158140cfd815c2639fc874c5409fe874c540ebe6350540bbf8350540cfe63dc540bfb804c940cff7158140cbd655d010cdf865cc10cdd655cc10cbd7498c10cdd7398c108fd8798c10fe22188110fe12148110ced655c810de57188620be980886209f7815d120beb8050a208fd8798e208fd8798e109ef825c6309ef825d1109ef825cd10cee635c810afb8048560ced65dc910cee63dc9109fb805cd219ee871c910be7814ca21cef72581109ef825c241a7f80595518fd8798e40 else (if j<2 then 0x103610100a000c0081082a81080a0409860b08188305e244030b84c486040810281026487420000d2128589130b84c4860402840402800300020004062b04200000161e0804c4c230c4000805080409080805080e08281010001218004028403118610004241e2e04222020705921c080e060480040281028382000020408730d830762418662b120e1b141bc28341c5a25150e8610114443860ba2a1c3092182307e28a0f20714362f098307830a10e2a1c308a1f8a1d678a130c2f59e1f168410181605c4a1c4058150e1e0715c5838959e284c3e2d042623160f0613038a0b84c161b10462b102a0d2b8a1f14261042834ae284c5a2d042ccf0f8b828304c605c648244100b9943873da9ea4f3a77f3b09c34d9667732c98ecc5e62330b982cbfe5e12d89604a7e4fd26692bc922485233912485641f1f78f8c7ae3a71bb8dac6be34119a8ca46162ff1798b0c56e287134897445a22110a87dc3d61df0e9871c35219d0c885cc28611306882cc12a06501a8013fcdfdafe77f0bf25f62fa27c9be11eeaf5d7a2bcb5e3cf0f7803bc5dc4ed375db9fdcf2e6172038e9c68e2570b381dbccdd76dfb6c1b30d806afb565aa6d4469f34e1a52d2368133cd9c8cde66332b993ec90640b1ed8d8c5d62bb121860c18604b00d7e8bee5f42f897b8bc45d62e99740b9a5ca2e39710b795b52d49698b3d5972ca1632b135822bb15a8ace55faa7950ca77538a9894a6a4451aa87542e9ff4fca7cd3a49ba4da26b932c97e4b324f125a91e48c24011d08d0460a2c9146879430a1490748194009fa4fa27b93c79e24ed07623a99cece4671d38b9bb4d986b43499a10cea66f32b9944c96645316980cbfa5e52e696d4b4c5972bb15c0ab055229d14d0a5c51f28393e09d24d1253923c90047a23a11948be4232010f3c74a3841b18cc061e2dc15d8a684f223d10987c83901a70c7859429a12308583a81a409f043812c042000b7f8550e10cfd655ca10cfe635ca10cfd655c610cfe635c610e7d6554610bbf84546109fd874c610ddd734c610df5714c610bfb804c610efa6350210ef96548210efa6348210aff8059520aff80595109fd83dd1109ff835d110def825cd10dec825cd109ff805cd10dfb805cd10afd8598d10cff7498d10cfd7498d10afd8098d10b7f8550d10cfd65dc9109fd83dc910cfe63dc910bbf845d5109fd83dd1209ff835d120afd8598d20cff7498d20cfd7498d20afd8098d20b7f8550d20def744c920cfd65dc520cfe63dc520e7d6554520bbf8454520df77154520eed6548520cfd7498e10aff8059710afd8598f10cfd7498f10afd8098f10cfd655cb10cfe635cb10ef56548710ef66348710aff8558310cfd7458310bf78154310ddd734c310fd5314c3109ff835d210afd8598e10eee6348520ef66348510aff8558110cf else 0x617081000424184821a4250a0c261709060c080500024402820a040000000c48204028405020409a0f143005078a18100a103c1c48202241c4838904002328200002014202810200043020010704002850608001d0828382040c16100021c1000000838200041040e41080a0408188305870706120e260e104d12151688102c1000002b890b13060a040d081a102140430c20a8b41080e410a120c2412003090612084016283420620c1782056246028b410807452086000130612085c10b3118a1c24161b0826102c46504c56084c462b0c3000610200109040a16260c1e241a10205128a103f1210501a5034a040a083090408482c4628404028589040c48200000004028405020400000000106060c0d0b12100c4058808149040838203c204050204000816230c0418100a1608101860c241618302040a040800201420008182f1218100a10000001210100a16078a16078a00a4880a040a08181e28581e28581e284c9061209101020140009100e8109880b))
def g223H7 (_ : Nat) : Nat := 0x7975ec9059a611ab07219526a63289a280846c8f000000028bd7c464b2eda0da80000071000258c769b11656800016900000003e714c8d000001b9abc8a8e3709d002a0f4bc500363f430235c00445821c700004529a18d
def g223D8 (j : Nat) : Nat := (if j<1 then 0xba0c081ea04c7f99fb07de9f3c7bb9ea879c9e447819dc07649d4c7439cd87289c647079bd06e09b3c6bd9ac86a69a4c68199b8664995464398e0628985460397c85e4975c5c796e05a2963c57d95a055c952453b94a0516941c4f393884d492fc4b19288492920c473918844c90f442790504008fb43df8f403be8ec43a18e483868dc43618d483428ccc3238c503068bd42e78b602c68adc2a18a20272898424d890022e887420f88001ee875c1c986d81a6867418985e016a856414b84d0128845c10583d80e8836c0c782e80a6825c08981d806a816c04d80f802e806c00b8000ffaa2907fd21543ff10aa1ff50520ffa62907fd50483fea0241ff4c120ffaa7887fd31487fea0a63ff54521ffa8690ffd53487fe98621ff54e21ffaa7087fd43843fe38263ff5c131ffce098fff704c7fea0a43ff50130ffa42987fe214c3fea0a61ff90530ffae2987fe714c3fea1261ff5c930ffaa7107fd43883fea1a41ff50630ffaa3107fd41883fe98c41ff48540ffa62a07fd32503ffb9281ffdcd40ffa63207fd53483feba261ff54510ffa82887fd43443fea9a21ff4c510ffae6887fd32507fea8221ff5d110ffa80887fd75443ffba263ff4c110ffaa6087fd51843ffb9263ff4c610ffa83087fd50c43feba263ff50931ffae498ff631442ffba241fd88510dfaca907ee21882feba241fd4c510bfee6905fd734837f31a41bf58110bfae3107ed428837f31821fe90110bfae9107f940442feb98217f5d010ff440886fe63882feb9c41fe48110dfaca087f521442feb8c217f5ca10ff281086fe63842feb9c217f5d210dfacb087f9208437eb2c41bf58310fea43887f531c42feb9621bf59510bfee8885fd720437f31e217f5cf10bfae9886fd65c42ffb9a21bf58120fda42905fd734437f31a217fdc910bfee2907ed32483f7b92217f5c910fd8e4885fd74442ffb9a83bf98d41bfee4a0fbd42506ffb82837f5d231bfae518dfd708c6ffba2637f5c221fba8698dff724c7ee992637fdc131dfacb10dfd74886feb9c43bf98e21fda6510dfd744c6ffb8aa57fdc152bfee6a16fe6350bdea1a857fdc542bfee0a15ff744cafeba2657f5c241bfee2995ff704cafeb94a37f5c251bfee4a8dff70546feb9c83bf98e41f7a8720dfd72907f6a1265bf98e40bfae5205fd71902ffb9a81bf98d40f7a86a05ff72503dea12817fdc540bfae7206fd60502feba4617f5ca30bfae3185fd744c2ffb9261f74c930bfee2985ff744c3dea0a817f5d121bfee690dfd73486ffba243bf98d21fda8490dff70487ee98a61bf50960dfc82b06fd415837e90ac17f5ca50bfae3285ff72542ffb8aa1bf59521dfc42b057d75042deba0215fdd543bbae6084fd7098e7ebacc77b5c8109feeab067d65546dfba2a36f5d250afaeb18def72442bebac813fdc165 else (if j<2 then 0xc50f20944d06243c5070fc51310142c0c5408248883150490b8382894a448786200c2c08542b144c01249c510c212122d052b141c4c40709c3c2cac50f8786203c2b14404c5c3c2cac50f87861d64280025085038571490900990e07c5418221282a266619121e088990ac5130049185714648841246990a092215c50e1d64381f1605085470b038115028ac5064913282c0c082604522840189090059421507c581200c2c082b144c511e2418a24c5014214140c2e0408562b15244c9011449c51b22182c0c5408881e062b2490b59c241448789862164381f1508562470b0302148907414a06260c2e0929121e261888b414ac58613182c002491641f16050854a181007c5830b18604c1b142e0e24799061707c541821e652a19121e0a24743142415c541891e645c2b148a08504c899c3170ac5221382478929650850541f160470b0389101307c58142152a670c2b14243e08401890b038115028a228910242c0e0454088a28404c91107c50b490018246f142e6440187991b13c5830b00492024006f142c8c60910990607414a1d2a266609121a1c7241986c54116670c442b1608184d2400a8459c3428a10131c2d2a261a660a1c799120ac50749101e642b1424504c1c71500090641994a1d2a261912661e087240741c519141a670c2b16084d2440813c5198749141a642803260b14507040913200699074a204e1a660907241c78a0009140615c5590742282c0e04540a2b144018001d24c030b8102150f098a1307282c002450920715648030b021510c581490027148924046c4c6030b8102150922202024005207156508548131007c5191419642b145c4d08547030b4102154ac50f202c0d0454092b1442241c4cb590ac542150f182e0e09282a19121e24959c542140610131f144f28444141310062007c5011b25670d08884e061d24859420f07858119248965181e150a0480f42490781131a64086c282f144018001d24b091b13990716646c420f142d240081b0a000907c50b992105650e19121e247430b4249811318846c1b241f1460e15cac31307c906c5242e060a2b245062014d9c21306c907c524730c2f082b251c70c0b59c20ac91844032b0c53081c1b1490b59012587142c6709052b26187210b1bcac98618846f284f27141c78121c28a10c9061f64404f0f0b2a1b161c9821bca13c9c5071c6a6407251c5d0eb3fccf1b3a8cdeb344cc7b2f0cb0b28cc95b228c7cb1ccc67b168c4ab0dcc23b060c10b01cbfdafd0beaaf7cbd5af28bbeaec4ba1ae50b82adb4b5fad48b42acccb23ac70b12ac14afdabc8adeab54ac9aaf0ab2aa8ca97aa18a7aa9b4a5da958a48a8fca35a8a0a14a81c9fda7c09e2a7549c9a6e09aaa66c989a5f096aa58c94fa50892ea46c909a3e08e2a34c8c3a2e08aaa274885a1c0860a14483 else 0x12030b420618004616100c2c1c78584030b004918380854312444509101515102c0c0224615020089111448244d0451f0b0645411511144428022468485150e0a42182c0d0802245244445430214182c7d150444520064107147c2c1915062461f074585030b411c901d111616110c0850981c5431b4249060a072607143d2480581c5070c1e041a2841502091010540a06284118513811082144d26045150e858110801a150a045c50f49208117150c6c801a046178502150913811f144801245a0461f074585030b418920901d111616110c085624a24444543021518381c0856062862385030b4200891c3a16100854422474445840a0006891c44244c34445021410591114244c1c60902150c2915100854507444584831b0a0682242c7d15044c51b152481142d0a248c1c186890e0714109111150c0a245070b1f454189152911143c2a241c188444522492014543911142440645440b038906071c892438315028906c507190889248c481c5421411143e2480190461f0745030b41820a8926142d088c1c18681c5491011111610281c18685840e0714061915100c2c181c6c51b150e24145e12140850244018881c5110049161a2c3c1f150450407590ac51242878914204b144c521d24659c241864344878923161d183590ac5421506138910262c881c1905286030b4102154ac50f12242c0c5408404c03150490b83824a86448789220c2e0a25043e181c8030b02150ac5104689072a11670f150a1c407830b824a8987861d67143c504c5590ac507421419671441081c5060b41c5c3c214c913064a072d64382b140024541d0818a1114c5071086491e0c2e092a1a261c7030b41021520064a89072853141c412451a0b59c241898786203f14184d245030b020ac50f09131410060730482b1524001c659c5134207141a0c2e092a261a1c70b0341150209134a0725642b140024541d0881a418959868718531441244c51a4159864389871e0c2e084d0726181c811c549061314822c50401c1905288110ac5134900061e250511661e186590ac50f421518442b1401241c187830b82894a448687202c0c085024401905289590e0a0009c5421506242d670a2505121a1c8030b4102154a))
def g223H8 (_ : Nat) : Nat := 0x1c2b5798000001a2d000281c0012f29220002113c4d185241c001cd5000022f846000000000000007a276f3b800145c00000014b4000000581155a000e142074001ab8000112d15f8c38718bd8d240f8459b420466c45529f86d8b784fb5b98f4deb08e00061dc001c0916dd950001a50251f0a800028fa612878e054c521e3af793800000072600008b000000000018a105a289c00069100000000004df00000005364480000000001e1300000009c3e6ce1600034fbc11e018003c6fab9f308000000276c4b80035f82bbf396323cc1058512590380c20c321b0c00ff842507ba30dfdc85717522b835ec0b4ff1475ba000170000005f0742264360001d04268f3dfcc82bf8410000001cac16591bac77a0011d6204001a1613c000354800092f3a58000000027000000000000000000000000002af80008ab0000af314141c075241800000025460e3192000000000000047100030d599c0000003088001701b3e6b97cda0000002a100000000000002934000000000000000000000021c5b00f35a21bc6d81581480000008da00041c00012b2e06d154001693a2b00019fa2d2632b97e03122192e800142870c00000000008120000003dcc66836383c75116cf237ca989ae0000001bd000000000060200002ec0439ba142e00000000009e0ee7000442f0698c6260d0f9cd5a73a66a0810afa0ba3c80000ea00053320fc000cdc0007b2800000040c80020c784126f0000001c7ec00db40000000425607f16d494212c98b52a0007726c24001d05b53d24353aae953dc89bc8e631334f364001caee232a02d3c4c4902c8400738023550003dd6eff95a800241c000358fbed106cd6b33fa640000000000000001e0ac1959240016d422cbc0f1458cc0000000df200000053e8d4a8baa77bb4c000a8d0004aa64a4020400000000100400011081800050000010000b01c00030080804040280000010280010000980c0400020000e0000004020001800000403824000100808000000010000602000160300800220e0000400020081004010180000070c80c1806000000006
def g223D9 (_ : Nat) : Nat := 0xbb225145870a50f0e18b082ecc5870a54926183962e2c3845254920183942ec800d161c294247872c20bb21a2c384425090e5a00c0619b842a487243431f089c9026c50728345320a549281c80818a4a2726299041ca0a1030b326e487202840c4e499361c817640078b0e14a123c3161018b042a2ca865210927243863c381370e10a92188061c09b865210a2124316547078a6618295243141e299043e510921890e2ccc2372a4862038b3308dca212431258307030cdc214251132cb860f14c829425113283071664da226386481c0998608549285013e1c599842a4902c3c58708a1394243141618b84064871c5c3842a48a6610115245ef1c976ce86c677bad1564a3136a4e4497b4e71a4afd5709e91a9e232c57c898d511214814800ff443fe10ffc43fd20ff883fd30ff8c3fd40ff903fd50ff943fd21ff043fd31ff8c7fd41ff907fd51ff947fd32ff50bfd52ff50ffd53ff886fd60bf98efd65
def g223H9 (_ : Nat) : Nat := 0x17c62ba01e59e8059f2b568c2b00000003a00006d3e45274001f2d3a40da0000016c3609a88000001e8f7b10d82ce000442024000000000000001e36000000861ef9b2326a0016c40000000000006160012c60018f213205200151e185ca04dc0000000018a4082d61b77596001e7e303383446f6fcbab955791b400105717493ce1f321799f6b21bef1938906d4e000000001e4a0000000008bc000b1400000000000041202c00000087c00024d30885bce44200006c8000da29466ecb3fcfc74400023fd5f09c000000000711670077740000000e222c0c33a38dabe0bd0e464eaf20291600000000000027236200177b4f66e7c1dc91c95ba978a19ad7eb0ad52b4c5180000001599b2000000000000a1024109a8d0e930ea001150a4828b15caee64e430a283558a7684ee8c9e9880015ae5b60000011317a670512e000000529548b1c0011700f4790772001f000be00145f27800165436d0638862980004a3742001ca8c04001d36000000001cb23678060fe0000000000014b800046c000000d0cf4a2e2469d9200000000000000000007a001e96000867712018d6923a4508de0013accfa2e0001eac001f2a00000000000000193578016438c000000000001e3500e0002cdb86000b8ec3df3a000f5a7278caa27b1a65c8b640c000000cd442e0014d626f3572aaf9d01572404000080a0b048000000010000000000080208008040805040080802000000402000000202008000800000080601020200200000042e010102c0e0300000020a000140c03040000400000001004038000a05
def g223D10 (_ : Nat) : Nat := 0xc8a18451237f
def g223H10 (_ : Nat) : Nat := 0xa93afefa6005c74a000048491a729cc0476af6ba58000000ee19eead290ea38ba0031f820b4645080019088040
def g223L : Nat → Packing
  | 6 => (47,4,6,0,0,9,0,g223D6)
  | 7 => (269,3,6,0,0,13,0,g223D7)
  | 8 => (220,2,6,0,0,14,0,g223D8)
  | 9 => (28,1,6,0,0,11,0,g223D9)
  | 10 => (1,0,6,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 15 61 6 10 6 0 g223H7
  | 8 => lookupWord 89 409 9 13 9 0 g223H8
  | 9 => lookupWord 73 331 9 12 8 0 g223H9
  | 10 => lookupWord 9 37 6 9 5 0 g223H10
  | _ => fun _ => none
def g223 : Forest := ⟨223,10,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 47=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 47=true := g223P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 29=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_29 : block g223 7 29 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_125 : block g223 7 125 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_221 : block g223 7 221 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 269=true := (@block_merge g223 7 0 125 144 (@block_merge g223 7 0 29 96 g223P7_0 g223P7_29) (@block_merge g223 7 125 96 48 g223P7_125 g223P7_221))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_15 : block g223 8 15 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_111 : block g223 8 111 40=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_151 : block g223 8 151 69=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 220=true := (@block_merge g223 8 0 111 109 (@block_merge g223 8 0 15 96 g223P8_0 g223P8_15) (@block_merge g223 8 111 40 69 g223P8_111 g223P8_151))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_3 : block g223 9 3 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 28=true := (@block_merge g223 9 0 3 25 g223P9_0 g223P9_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 1=true := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact (rfl : block g223 5 0 0 = true)
  · exact g223B6
  · exact g223B7
  · exact g223B8
  · exact g223B9
  · exact g223B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := lower_forest (g:=g223) (i:=0) (hints:=855703553) (before_sound K127 V127) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K127 11 [(223,[]),(239,[118,84,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V127 low223 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0x1262ad9ac9e501ee833c33d800001e021660,0x2d02620182c14500e08038134001e01e001240),(0xc0c482ae6020555002684c0fd9820e2185a860,0x804190aa00201040020a040899800621818820),(0x80460803f84f38f43de50170008603c0757408,0x500c0c047c0c20341d610160000600c0742408),(0x12b175500394808bd00b740021000ba1fe8380,0x12919d400100a08b0203440000820ba1e60180),(0x6d808010042402932014e924066cd859000803,0x6c940311058c0a972004e9a406245808000002),(0x25080802005288ac010cd3c98239250620401c,0x27a2006202528b88001c508982390104004004),(0x392011400412120884b802404e5cd0d8988083,0x81202080d032140085b8024048588050188001),(0xe090410010400425840829a31713426400114,0x8484018280540605840821235403402000010),(0x0,0x0)]
def g255C : List ColumnInfo := [(6,0,249,0,7),(1,0,254,0,10),(0,2,232,21,7),(8,0,247,0,10),(9,0,246,0,7),(3,0,252,0,7),(2,4,216,33,6),(5,0,250,0,7),(1,8,54,192,6),(0,8,54,193,7),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,4,216,35,7),(4,0,251,0,10),(10,0,245,0,6),(2,0,253,0,10),(4,2,232,17,6),(1,4,216,34,6),(1,2,232,20,6),(12,0,243,0,6),(7,0,248,0,5),(5,2,232,16,5)]
def g255A : List (List Nat) := [[],[33,84,118]]
def g255D8 (_ : Nat) : Nat := 0x346090800401c0c051008e3000642c08040027beb2d500cf9e4b9160d218fee81984c910ff04c93148110bf8e8d2148110bf868d2148110
def g255D9 (_ : Nat) : Nat := 0x3ec40c244100904b1edec1abec4250fb7b3047ed0dec0ceb0bea0a05a3d1c133a8144b44085ec0cea0a02edeba3d1c12bac17be8c24106ec0ceb0bea0a05edafd111c13003a9bc10460fb7b3049edeceb03c102eaafd127b437b033ac2fa82a8ebf0408ceb0f23edecd109c1201c0a8cba47ab05bc805edec0891eac16f2004428c20404630091eac1af1d8c0a47ab06bc6100706ea4205af6323b437b033ac2fa8280abf4704ced0dec0ceb0bea0ac3d10eaf33b7b3aabf0d4450761eb80eaaf02edecc3d12847b7b3a822bc187ed0dec0cea0ac30eeba16fd133b7b02027ae85bf448ed0dec0ceb0bea0a00a32bac004f3c3850709b183edecc11c004e8c273c38602edecebeaa3cfd1218407b7b3afaa028c3b3f4408cedecebeaa361cfd10227ac2fa828033f47b7b2858cbed0dec0cea0a04ebb1c12bb7b02412c4561edeca30eea02ebcfd12b3fb7b3afaa8f4470f00072e0542e3edecebea2eafaa2292a7926da5824aa3121da0a1f09df1cd9bc1b29a319598416a95114192c11c9030f18dc0d08c10b38a208887505d84803c8270178002fff24c0a61fdb904c530beec9a42984ff64b83442ff720c1a213ff9260d10dfdc8306884ff64f824437bf0498a613ff984c9109fecc264886f760d32442fef2498a21fd5324c510ff9c8262885fde4d21442feb2690a21ff131481109ffc9b04884ff643824c6fef22c12637fb9060931febc8a6498cff64b804c77ba65c02633fd90e0d21bfbc8b0690df7e49314c37ef22c1a433ff9060d21dfdc830690efe241834867fb27c02433fd92e0530bfdc8302985fee41834867f720c1a43fe12148110
def g255H9 (_ : Nat) : Nat := 0x220000000000200000000000a40021000000000000330000000000
def g255D10 (_ : Nat) : Nat := 0x484004f56b5ec76ec8704cdab762cd6ac2a309a8941a26eb57a95055e11889dbb20c334b230417507d6010d19e59646157870403541a256dd9af50525bc48404868c334a8525af6ec268f52f8344c20236ec05ae1ef4344adbb3580d4be1a12944117b766bd4be197a2489dab762cd6af52a008d0939e3a88240b02dbb35ea0a1c041c6be89a176ecd7a91c1df44907b3505dbae0afa24920a0b6ecd68c8ea83bcb0a4816dd9af52309077d130312dbb35ea0a1c0afa2597de275ea080f6ec82c4b1fb766a09ae1c1624ebd4036ec438e7d12401305840edd9af5239f44c01840edd9af5239f44a20536ecd5ae1a1df44a06204e1dbb35ea5f44a27840edd9af5435f44a05b766b0a008ea82bca8147b37526ff6b36525f85ac55951449e43d3f83b33603062b326021b1d617c1300e409804c000ffd214c3ff60d10ffd814c3ff60121ffd82443ff60131ffd32443ffe0131ffd824c7ffe0931ffd83486ff60910bff83442ffe0910ff531442ff60d10ff920443f74c530bff814c2ffe0121bfd83486ffe0d21bff804c7f74c931bff824c7fd48510
def g255H10 (_ : Nat) : Nat := 0x6092a2cf9b400000581c3843a4bda5f227364400022c0034d28d24821ac041ff26000002dc2219600000000000000494643c2402000c4415a82c9b0000000055de3b04b6ac0c11621f47f18793a0e8c815000000004cb94062a51c9e46241000a50000000c2001000083
def g255D11 (_ : Nat) : Nat := 0x2db2ba8386f44802db2baa18cf44912baafb6c0c1c4916db2bbe3a81449b4783c00ffa63ff487fe987fd10
def g255H11 (_ : Nat) : Nat := 0x203e09df73f5fd11340041727622cc00000a114a94d90e3b8600215f0b99003eac3ec105000b4a8900000001476580052fd800fa8141056180000001
def g255D12 (_ : Nat) : Nat := 0x1ac5a86f0c48ff
def g255H12 (_ : Nat) : Nat := 0xb725f800002e0000000620120000000000
def g255L : Nat → Packing
  | 8 => (5,4,5,0,0,7,0,g255D8)
  | 9 => (38,3,5,0,0,12,0,g255D9)
  | 10 => (26,2,5,0,0,12,0,g255D10)
  | 11 => (4,1,5,0,0,8,0,g255D11)
  | 12 => (1,0,5,0,0,0,0,g255D12)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 29 0 8 3 1 g255H9
  | 10 => lookupWord 16 67 7 11 6 1 g255H10
  | 11 => lookupWord 10 43 6 10 5 1 g255H11
  | 12 => lookupWord 2 23 5 7 2 1 g255H12
  | _ => fun _ => none
def g255 : Forest := ⟨255,12,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 5=true := g255P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_2 : block g255 9 2 35=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_37 : block g255 9 37 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 38=true := (@block_merge g255 9 0 2 36 g255P9_0 (@block_merge g255 9 2 35 1 g255P9_2 g255P9_37))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_15 : block g255 10 15 11=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 26=true := (@block_merge g255 10 0 15 11 g255P10_0 g255P10_15)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 4=true := g255P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 1=true := g255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact (rfl : block g255 6 0 0 = true)
  · exact (rfl : block g255 7 0 0 = true)
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 eightInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=12) (i:=0) (before_sound K223 V223) g255G g255T (by decide) (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0xff800fffffc0000000000000000ffe003fffff,0xaa1542a8550aa1542a8550aa1542a8550aa154),(0x7ff001ffc00000000000007ff001ffc007ff,0x11222444889112224448891122244488911222),(0x7ffffe00000000000003ff800001fffff800,0x40c8190320640c8190320640c8190320640c81),(0xff800000000007ff001ffc00000ffe00000000,0x580b01602c0580b01602c0580b01602c0580b),(0xffe000007ff00000000000,0x668cd19a334668cd19a334668cd19a334668cd),(0x3ff800000003ff80000000000000,0x1f03e07c0f81f03e07c0f81f03e07c0f81f03e),(0xfffffc0000000000000000,0x98730e61cc398730e61cc398730e61cc398730),(0x3fffff0000000000000000000000,0xe07c0f81f03e07c0f81f03e07c0f81f03e07c0),(0x0,0x0)]
def mo255C : List ColumnInfo := [(8,0,247,0,10),(2,16,173,64,8),(4,32,91,128,8),(32,0,223,0,11),(0,2,232,21,7),(1,0,254,0,10),(66,16,173,0,7),(0,4,216,35,7),(3,0,252,0,7),(2,0,253,0,10),(129,8,54,64,5),(8,64,167,16,8),(16,0,239,0,11),(2,4,216,33,6),(20,2,232,1,5),(0,128,87,40,9),(12,0,243,0,6),(64,16,173,2,8),(1,4,216,34,6),(1,8,54,192,6),(64,0,191,0,11),(10,0,245,0,6),(4,0,251,0,10),(128,0,127,0,11),(1,2,232,20,6),(16,64,167,8,8),(17,2,232,4,5),(132,32,91,0,7),(6,0,249,0,7),(39,0,216,0,4),(17,0,238,0,7),(0,8,54,193,7),(65,0,190,0,7),(0,16,173,66,9),(0,32,91,132,9),(0,64,167,24,9),(36,0,219,0,8),(136,0,119,0,8),(65,8,54,128,5),(8,128,87,32,8),(32,4,216,3,6),(128,32,91,4,8),(40,128,87,0,7),(32,128,87,8,8),(18,0,237,0,8),(9,0,246,0,7),(164,0,91,0,7),(33,4,216,2,5),(9,128,86,32,5),(192,8,54,1,5),(5,32,90,128,5),(5,0,250,0,7),(168,0,87,0,7),(129,32,90,4,5),(64,8,54,129,6),(12,32,83,128,5),(193,8,54,0,4),(3,4,216,32,5),(80,0,175,0,9),(10,16,165,64,5),(5,2,232,16,5),(4,2,232,17,6),(21,2,232,0,4),(35,4,216,0,4),(16,2,232,5,6),(19,0,236,0,5),(24,64,167,0,7),(0,192,7,56,7),(23,0,232,0,4),(10,64,165,16,5),(20,0,235,0,7),(128,8,54,65,6),(12,128,83,32,5),(68,0,187,0,7),(4,128,83,40,6),(72,0,183,0,8),(88,0,167,0,7),(1,128,86,40,6),(34,0,221,0,7),(38,0,217,0,5),(1,16,172,66,6),(1,64,166,24,6),(34,4,216,1,5),(8,192,7,48,6),(33,0,222,0,7),(32,192,7,24,6),(82,0,173,0,7),(134,32,89,0,4),(160,0,95,0,9),(37,0,218,0,5),(96,0,159,0,8),(192,0,63,0,8),(168,64,7,16,5),(73,0,182,0,5),(137,0,118,0,5),(7,0,248,0,5),(3,16,172,64,5),(6,16,169,64,5),(20,32,75,128,5),(8,32,83,132,6),(68,32,27,128,5),(8,16,165,66,6),(48,0,207,0,8),(144,0,111,0,8),(4,16,169,66,6),(6,32,89,128,5),(34,16,141,64,5),(130,0,125,0,7),(130,16,45,64,5),(9,64,166,16,5),(88,128,7,32,5),(89,0,166,0,4),(130,32,89,4,5),(16,192,7,40,6),(176,0,79,0,7),(129,0,126,0,7)]
def mo255A : List (List Nat) := [[],[33,84,118]]
def mo255D8 (j : Nat) : Nat := (if j<1 then 0xb004e0031040408007be5c04be0c501ef97f94804f831405765f65385b8245f97f94f83804f8c14014413e0c301d01c81b80601a14083e5fe0e07fe30579401301271110c14014268f78000e0c041a3c038300568b78c60612e5fc53258054460900d6010d416826804338c505005a8b1002901823050052060c02021e01be0c430fc82f14c8911e31c640603c0504411806600360678c6010f2a64ec9190b1e636c618ab1261ec3184b06606c017eafa5eebd178aee5d6ba172ae25beb716cad65a6b4166aca58eb1160abe576ae15aab255eab154aa6546a814ea9a52ea5148a8e516a2142a824fe9f13ca764e69c136a6a4aa93115a0a3d2720d99922e2558a393223a408738d217a2884987e0c61201982a02a001ff05c9324c540443fe0ba26498a40887fc1644c93148110ff82a89926290221bf85d1a3485204437f0b234690a40886fe15468d2148110fdc2ecb1a4290221f785d97248520443f70b1a42b0240885fe1b758d2148110dfc34e90ac090221bf8699214c120442ff0db14690a40885fe1b720d2148110bfc36c41a42902217f86d89848520442ff0d993090a40886fe172684904c940dfc2ead112098a21bf86dda2241314437f0b934448262886fe1b5688904c510dfc2a4d112098a21bf4545a3241215837d8bab4848262886fb172690904c510df62a4d212098a219fc5d4a94c5404433f8b995298a808867f0a95c93150110cfe2a654a62a02219fc548a94c5404433f89915298a80886fd153684904c940cfe32ed0920992819fc655a1241325037d8da34248264a06f9970690924c530deb264d2902b02619f665da3241215833eccab4648242b063f9706809850931c7f260d0130b12a3bb66d9a3241215835ecc3b4648242b06bd8b868c9048560df92e4d1904a0221bda5c9a5209404435f4b915099280886f69532898550110cfca6054a84a8a43bd95c9a5209314435e6c3346412e4886bcd8468c825c910d6db0cd2904b9221adb611a5209724435b6c1b4a412e4886dcd7668c825c910dadaecd2904b9221bd954ca2615314435b6c3144c2aa6886b6d842898554d10c7db2c5130a41a21adb60ca261553442fb0da90690a40884fe1ba4c92148110d5734cd2120c1a43aec691a1241834865ecd8152bb30610ebe1a26849060d21d7c170d1a42902211f96c0a95095148756cd33464830690e7b194684904c940adb36c5032690a61a5b61da5209724434e6c3b46412e48867e196688904c51087b974c3b2610ac1bf06cda2241314437e0d1264482628867b1a4648904c510df23489912098a215ec6d0a064d214423f8d915298a808851ddb72a19308560cdb32cd192090ac17f06cd214c1204427f0d8b4441a40886fc143688904c510 else 0x0)
def mo255D9 (j : Nat) : Nat := (if j<7 then (if j<3 then (if j<1 then 0x8220131d7765d3220131db76593220131dd76553220131de76513220131afe2819460d21ddd6557120131ded6517120131df96497120131ddd6556120131df96496120131cfe6189060d21cfe6109060d21afe2819660d21df36493220131e7b61c825c910bdb694825c910bf368c825c9108ff68c98589108ff68c98509108ff2a5844c910cf72a5834c9109fd6859220d10ef360d724c910ef360d624c910bfa688904c510bf9289854c510bed690924c510bfc680924c510b7d69c824c510bbd698824c510cfb261724c910bdb2898554d10adf6948360910cfe6199008530cdf6199520910cef61d9420910c7f65d8420910cbf6598420910cef65183209109fd6859320910cf761d9320910cf76199320910cf76119320910df56859320910c7f65d8320910cbf6598320910cdf6558320910cdf6558420910bde6948250110bf668c8250110afe2a13250110bfc6843250110dfc2a53150110ff44c93150110bfc68d2150110bdd694824c510bf568d214c110ff44c5704c110ff44c5604c110ff44c5404c1108ff6a58348110df564d3148110ff14c93148110bf968d2148110cf7661324c110bed690824c510bf568c824c510afd2a1424c510ff15c9324c510ff1589324c510dfc658904c510ff450c904c510bfc688904c510bbe6988250110ff44c8904c510cfd2a19348510dfc2819348510bdd69483485109fd6a53248510bfa2898550110bde6948350110b7e69c8250110dfc648904c510edd5518154430c7f61d9550430cbf6199550430cfb6a58250430cfb6558250430eeb6918250430e6f61d4250430cfd6518148430ecf6154250430eeb6094250430cfd6558150430eed5098150430c7f61d9448430cbf6199448430cdf61d9520910cfd6558148430eaf6194250430afe2a12158130bf668d2158130afe6a02158130bde6942158130bee6902158130bf668c2158130afd6a55460430ef96858254430cfd6559260430afd6949260430afd6909260430e5f61d5454430e9f6195454430cfb6a58254430edb6958254430edb5518254430edd6555460430cdf6558420d10afb2898520d10aef6909260d10afb2899560d10afb2898560d10afb2898561110cfb6189261510cfb61c9261510cfe6199008430cef6558448430cfd6558108430cf76199308430cfd6615148430e7d61d5148430ebd6195148430eed6115148430cef6199408430ef96095148430c7f61d9408430cbf6199408430cfd6518108430cef61d9408430bf868d2148110ab76989060c219f92a54254521add69492604309fc2a53150110cfc6059008430cbe6199008430bec690904c510cf564d8108430ced6518108430c6f61d9408430cdd6558108430abe6989360021cb76199308430ff04c93148110bf8688904c510caf6199408430aed6909260430 else (if j<2 then 0xeb76597660c10e7765d7660c10af76a57660c10eaf5d96561010aef69d6561010adf6989361410ff850d2148110ff858d2148110ff820d2148110ff860d2148110ff828d2148110ff868d2148110ff85512148110ff85912148110ff85d12148110ff84c93148110ff86512148110ff86912148110ff85d92148110ff86192148110ff86592148110ff86992148110ff82612148110ff86612148110ff82a12148110ff84c92148110ff85092148110ff85492148110ff85892148110ff85c92148110bfc68d2148110ff86112148110afe6989360021afe6a56360021afe69d6360021ebe6596360021ebe5d963600218ff684984c960cf7261534c960bde69481581308ff68898545608ff688984c5608ff68c9848560dbe6589048560bf668c9048560cef61d9408560cf76a19308560cf72a193085608ff68c9854560cbf6598320121cef6518320121d7d65d5120121dbd6595120121ded6515120121df564d5120121abf6989060c21af76a57660c21cfe6599360021eb76597660c21af76989060c21e9f5d98558c21cef65d8458c21eaf5d98458c21cf765d8358c21eb75d98358c21afe6a57660021af72a57660c21cdf61d9520530cdf61995205309f768d9220530cdf65582205308ff688985c5308ff6889854530be7690924c530cf761d9308560cf72a19348530df628193485309f76a53148530cef61d9408530cef6199408530cf76199308530cfb659820c810bee6908258130be7690824c530db76999308560df66819308560d9f6556308560daf6516308560db764d6308560cfe61d9008560dbe58d90085608ff684984c940cfd2615148540bfc684904c9408ff68c985c5408ff688985c5408ff68c98545408ff6889854540afd2a171545408ff688984c5408ff68c9848540dee650904c940aef6908260131cdf61d9520131cdf6199520131cbf6598520131cef61d9420131cef6159420131c7f65d8420131cf76119320121d7765d4320131dd765543201319f768d9220131cfb61d9220131cfb6199220131cfb6159220131cfb6119220131df368d9220131cdf65584201318ff68c98589518ff68098589518ff68c98509518ff6809850951cfe61c9060931cfe6189060931cfe6149060931cfe6109060931bfc2818258531cef61d94209319f768d90209318ff68098589318ff6809850931bf6281914c931bfc281825c531bed690825c5319fd2a5425c531df650c9060931abf6989060d21aef6909060d21cfe6409060d21ebe6989060d21cfe6589060d21eee6909060d21cfe6509060d21df350d9220131efc6849060d21bfc2818354521cfe281984c521cef61d9420121c7f65d8420121cbf6598420121cdf6558420121cf76199320121ef668c9060d21c7f65d8220131cbf6598220131cdf6558220131cef651 else 0x49060931dfe5909060931dfe5889060931dfe5509060931dfe5489060931dfe5d89060d21dfe5d09060d21dfe5909060d21dfe58c9060d21dfe5509060d21dfe50c9060d21ffa5c8904c940ffc5d4904c510ffc5c8904c510ffc548904c510ff654c904c940dfe65c904c940dfe654904c940fee2813250540ffc5449048560dfe65c9048560dfe6549048560fbe58c9048560efe61c9048560ffc5c93150110ff550d724c510cef65d844c810cef655844c810cfb655824c810eb7619534c810cfb659824c810cdf659854c810cf765d830c810cf765d8354810cf7661534c810edb615624c810cfb661624c810ef360d724c810ff84853048110ff84854048110cfb661724c810ef354d824c810eeb611724c810eeb6117254810cfb6598254810ef360d7254810ef360d624c810cef659844c810cfb65d8254810cfb65d824c810ff44c53048110cf7659830c810ff84856048110cbf619954c810cef65d840c810cf76598354810cf765d834c810eeb611624c810cef659840c810cf7659834c810cf7655834c810cef655840c810cfb65d820c810ee7611534c810cf7655830c810cf76598354c10e7725d8354c10cf765d8354c10ecf5958454c10ecf5d58454c10cef6598454c10e6f25d8454c10cef65d8454c10a7f6a09754c10eb75d98358c10cf765d8358c10eaf5d98458c10cef65d8458c10e9f5d98558c10cfb655820c810e775d9835cc10e6f5d9845cc10e5f5d9855cc10af76949260c10af76989260c10af769c9260c10adf6a0955c810cf76559260c10ed76556560c10eb75d96560c10af769d6560c10af76a56560c10ed76557560c10af76a57560c10cf765d9560c10cdf65d8558c10afb69c9360810cfb6599360810cfb65d9360810ebb5d96560810ebb6596560810afb6989360810afb69d6560810afb6949360810afb6a56560810afb6a57360810e7b65d7560810afb6a57560810cfb65d9560810e7b65d7660810ed75d58354c10e7b5d97360810edb2959760810afb6a56360810afb69d6360810ebb5d96360810afb6a55360810afb69d5360810e7b29d5360810ee76117354c10afb6995360810edb5d55360810edb5955360810ef364d5360810ef35cd5360810ed75958354c10afb6a57660810ff44c93148110e6f5d9845c810ecf255845c810e6f5d5845c810cf76a5835c810ff86893148110e775d9835c810ff450d3148110ed7255835c810e775d5835c810ef3689835c810e7b5d9825c810ff464d3148110edb255825c810e7729d9560c10cef65d8458810eaf5958458810cf76a58358810cf765d8358810eb75958358810ef36898358810cfb65d8258810dfc2a531481109fe2a53148110ebb5958258810cef65d8454810cef6598454810bfa6888348110bde6948348110cf76a58354810e7b5d5825c81)) else (if j<5 then (if j<4 then 0x10cff591984c910cff551984c910aff2a57460d21aff2a55460d21edf60d8554d10edf6058554530edf60d5354510edf60d5254110cff6558348110cff549984c110aff6949260d10aff6948260131cff6518220530cff6558320910aff2a57460d10cff2a5835c910aff2a56560d10cff2a58358910aff2a55460d10cff2a58354910cff595984c810cff5d5984c810cff6599360021def5cd9420931def5c19420931def5d59420131def5c99420131def5499420131eef595844c810eef5d5844c810dbf5499620131cff4c8985c5409ff688985d9319ff688985d131aff684984c9609ff6889859531aff688984c5609ff6889855131aff684984c9409ff680985d1319ff680985c9319ff68098595319ff68098589319ff68098551319ff6809854931cff608985d131cff600985d131cff600985c931cff6089859531cff6009859531cff6089858931cff6009858931cff548984c560cff544984c560cff6089855131cff6009855131cff6009854931cff640984c940cff5cc9850931cff5c09850931cff5d4984c540cff5cc984c540cff261724c540cff54c984c540cff548984c540cff4c8984c540cff6199320910cff6119320910def5d99408530def6199408530def58d9408530def5819408530def61d9408530def5cd9408530def5c19408530cff4c09858951cff4c09850951def4c19420931cff4c09850931cff6119320121ebf5d96360910ebf5d98258510ebf58d8258110aff69d6360910cff65d8258110cff5d99848110cff659824c110cff58d9848110aff6989360910aff6988360121aff69c8360910aff6988360910cff5519848430df75d99320121df76999320121df758d9320121def5cd9420121f3f5c97658521dbf5cd9620121ebf5518648430cff484984c960cff484984c560cff5cc9848540cff6199220530cff61d9220530df72619348530bfb68c825c910df75d99320910df769d9320910df75cd9320910df76999320910df758d9320910def5cd9420910ddf5d99520910ddf5cd9520910ddf58d9520910dbf5cd9620910f3f5c97658510d7f58d9720910cff4409858931cff5cc9858910cff5cc9850910cff58c984c910e7f5d97360810e7f65d7660810e7f5d9825c810ebf5d96360810aff69d6360810ebf5d96360021ebf6596360021dbf58d9008560aff69d6360021aff6a57660021cff61d9008560aff6a56360021cff6199008530dfb5d89261510dfb5909261510dfb58c9261510dfb5809261510dfb5d09261510dfb5cc9261510dfb5c09261510dfb50c9261510dfb4c09261510efb289835c910ff9209724c510efb618825c910efb610825c910efb60c825c910f7b5d8825c910efe5d09060d21efe5909060d21efe5509060d21dfe5d49060931dfe5d09060931dfe5c89060931dfe59 else 0xd99560810efb6557360810efb6556360810efb5d98254810efb5cd8254810efb58d8254810efb5d59360810efb5959360810efb5d5824c810efb595824c810fe75cd5350540ef76117354d10ef76117354c10fe754d3250540ef7611534c910df76554320931df76554320131ef7611534c810ef7591834c910ef7595834c910ef75d1834c910ef75d5834c910ef7551834c910bf72a1744c931bf72a5744c931df72a5325c531bf72a1544c931df75d19348530df75919348530df75519348530fd7615514c530fd7545534c530fe74c94150130ef7611324c110bf7694924c530bf7694824c530bf72a5744c530bf72a5724c530bf72a5654c530bf72a5624c530bf72a5544c530bf72a5524c530df72a53250130ef765d6560c10ef7595835cc10ef76597560c10ef7699835c810ef75d58358c10ef758d835c810ef75d58358810ef769d8358810ef75cd8358810ef76958358810ef754d8358810ef75d98354810ef769d8354810ef75cd8354810ef76998354810ef758d8354810ef75d59260c10ef75959260c10ef75d5834c810ef7595834c810fcf5d55350540fcf54d4154140fcf5494154140edf6198554d10edf6198554530f9f58d5254560eef61d4250530eef61d4250430eef5cd8458c21def5cd9408560ddf5cd9508560def5c19408560f6f5d57250540f6f5cd415c140f6f5c9415c140bef69d5350540bef69d5250540def65d4154140bef69d3250540eef61d4150130edf6195254110bef69c3250540f6f5cd425c140eef61d4250130eef5d58458c10eef5d58458810eef595845cc10eef5cd8458810eef58d845c810bef6953250540edf6118554530eef6154150130eef54d8458810f6f29d5350540dbf6556348560cff61d9448530cff65d8420d21cff61d9448430cff65d8420121ebf6156358110cff659854c110cff6598520d10cff6199520530edf5d58454d10edf6118554d10edf6115354110edf6115254110e7f5d5845c910e7f611735c110e7f611725c110cff65d8454d10cff65d8454910cff65d8454110cff65d844c910cff65d844c110cff65d8448110cff65d840c910cff65d8420d10cff65d8420910cff655844c910cff655844c110e7f25d8454d10cff6558448110cff6558420d10eef5d98454810eef58d8454810eef5cd8454810ebf5498650430cff6199520931cff6558420931cff61d9420530cff6159420530bef6943250540cff655840c910cff6199520910cff6558420910dbf6556308560cff61d9408530cff61d9408430cff5cc9854540cff6199520131cff6558420131edf5d58454c10e7f5d5845c810cff65d8454c10cff65d8454810cff65d844c810cff65d840c810cff655844c810e7f25d8454c10cff655840c810fcf2957250540edf255845c910edf255845c810cff5d1984c9) else (if j<6 then 0x110f7e5d57250110f7e5cd7050110f7e5c97050110bfe69d5350110bfe69d5250110bfe69d5050110bfe69d3250110dfe65d404c110dfe65d4048110bfe69c3250110bfe69c8350110bfe69c8250110bfe6953250110dfe655404c110f7e29d5350110dfe6554048110bfe6943250110bfe6948350110bfe6948250110fde2957250110efe60d6048110dfe64d6048110dfe64d4048110bfe68c8250110fbe5d96348110fbe5d96148110fbe58d6048110bfe69d6348110bfe69d6048110bfe6993048110bfe69c8348110bfe6988348110bfe6989848110bfe68c9848110bfe684904c940dfe5c19020931efe2a13250110efe6148350110efe5cd6360021efe65d6360021efe65d9660021dfe5cd9008560dfe69d9008560dfe5c19008560efe5d99360021efe6999360021efe64d6360021efe6599360021dfe68d9008560dfe5d99008530dfe6199008530dfe58d9008530dfe6999008530dfe5819008530ff62853258130ff62093158130ff64c88158130efe6148158130ffa2097250110ff95095148530ff920d4254521ff95d54248510ff95cd4248510ff9509215c110ff954d4248510ff9509214c110ff95d92148110ff95d12148110ff95912148110ff958d2148110ff95512148110ff950d2148110ff35c93250531ff35c9324c540ff5549614c530ff35c93250130feb5c95250540efb6117254910efb6117254810feb5c93250540efb611724c910bfd6948258531dfd6556120131efb611724c810fbd58d5148560efd6195148530bfd6988354521efd6195148430dfd6595120121dfd64d5120121ff55d5434c510ff550d524c510ff550d3154110ff5591324c510ff5595324c510ff55d1324c510ff55d5324c510ff5551324c510ff5591314c110ff5595314c110ff5589314c110ff55d1314c110ff55d5314c110ff55c9314c110ff5551314c110ff5549314c110dfd5919348510dfd5959348510dfd5d19348510dfd5d59348510dfd5519348510fdd615534c510fdd54d514c510fdd5493154110dfd6553148110bfd694924c510bfd694824c510bfd2a5654c510bfd2a5624c510bfd2a5744c510bfd2a5724c510bfd2a5544c510bfd2a5524c510dfd2a53154110f7d5d97348510f7d5d97248510f7d5cd215c110fbd5d96348510fbd5d96148510fbd58d2158110bfd69d6348510dfd65d2158110dfd659214c110bfd6989348510bfd6988348510dfd65d214c110bfd69c9348510bfd69c8348510dfb5d59220131dfb69d9220131dfb5c99220131dfb6959220131dfb5499220131efb6958250430efd5498150430efd5519260430efd5518148430efb5957360810efb5d56360810efb65d6360810efb58d825c810efb6597560810efb6597360810efb5d58258810efb5cd8258810efb6595360810efb54d8258810efb5 else 0xe193db03d683d153cc23c7a3c273bea3bad3b7b3b493b173acf3a713a0839b5396d392538c73874382137d93786372836ca3682364535fd35d6356d350f34dd34ab34793452342033d83390332732c93276321831ba3172311430d7307930312fe92fa12f642f062ea82e602e0d2da42d5c2d142cd72cb02c7e2c362c0f2bdd2ba02b6e2b262ad32a752a2d29e529be2976294428db287d283527f827dc279f276d26f926bc267f2658263125ff25cd2585251124b32460242323db23932340231922d1227e222b21f9219b213d20ea20a2207020331ff61fae1f711f3f1ef71ed01e9e1e771e501e341dd61da41d671d1f1cd71c9a1c681c201bf91bc71b7f1b4d1b051ad31aa11a591a1c19ea19b8197b1949191718da189d184a17f717a41746171416e2168f165d162b15d815a61553150014b8144f141213d513a31366132912ec12af125c121f11e21184112610e910ac10430ff00fb30f760f2e0ee60e930e4b0ded0da50d520d0a0cac0c4e0bf00b920b600b2e0af10a9e0a3509d7096e090508a7083e07ca074b0703068f062605a7052804bf044003c1034d02ce024f01d0016700e800740000ffc5452158130ffc5d53150110ffc5cd3150110ffc4c57050110ffc54d3150110ffc5493150110ffc4c55050110ffc6853250110ffc4c93150110ffc4c5404c110ffc5d52150110ffc5cd2150110ffc5c92150110ffc4857050110ffc54d2150110ffc5492150110ffc4855050110ffc4c92150110ffc485604c110ffc485704c110ffc485404c110ff65493158130ff65453158130ff64c97050130ff64c95158130ff65493258130ff64c57050130fde5496054140efe6117054110efe60d7050110fde6155158130fde5495158130fee5057050130fee5097050130bfe6952158130efe615604c110bfe6948158130efe611704c110bfe6948258130bfe6942158130efe6095050110efe609604c110ff668d2158130ff64c92158130ff64c52158130bfe68c9048560bfe6888158130bfe6848258130ffa5c95250110ffa5c93250110ffc5d93148110ffc5913148110ffc5953148110ffc58d3148110ffc6593148110ffc5893148110ffc4c56048110ffc5d13148110ffc5d53148110ffc5cd3148110ffc65d3148110ffc5c93148110ffa4c96048110ffc5513148110ffc50d3148110ffc54d3148110ffc6553148110ffc5493148110ffa4c94048110ffc64d3148110ffc4c93148110ffc4c53048110ffc5d92148110ffc5912148110ffc58d2148110ffc4856048110ffc5d12148110ffc5cd2148110ffa4856048110ffc50d2148110ffc4853048110ff65cd5350110ff654d3250110ff64c9704c110ff64c9604c110ff64c9404c110ff64c5704c110ff64c5604c110fde5d55350110fde6155350110fde54d5050110fde5495050))) else (if j<10 then (if j<8 then 0xd638d5d8d578d518d4b8d458d3f8d398d338d2d8d278d218d1b8d158d0f8d098d038cfd8cf78cf18ceb8ce58cdf8cd98cd38ccd8cc78cc18cbb8cb58caf8ca98ca38c9d8c978c918c8b8c858c7f8c798c738c6d8c678c618c5b8c558c4f8c498c438c3d8c378c318c2b8c258c1f8c198c138c0d8c078c018bfb8bf58bef8be98be38bdd8bd78bd18bcb8bc58bbf8bb98bb38bad8ba78ba18b9b8b958b8f8b898b838b7d8b778b718b6b8b658b5f8b598b538b4d8b478b418b3b8b358b2f8b298b238b1d8b178b118b0b8b058aff8af98af38aed8ae78ae18adb8ad58acf8ac98ac38abd8ab78ab18aab8aa58a9f8a998a938a8d8a878a818a7b8a758a6f8a698a638a5d8a578a518a4b8a458a3f8a398a338a2d8a278a218a1b8a158a0f8a098a0389fd89f789f189eb89e589df89d989d389cd89c789c189bb89b589af89a989a3899d89978991898b8985897f89798973896d89678961895b8955894f89498943893d89378931892b8925891f89198913890d8907890188fb88f588ef88e988e388dd88d788d188cb88c588bf88b988b388ad88a788a1889b8895888f88898883887d88778871886b8865885f88598853884d88478841883b8835882f88298823881d88178811880b880587ff87f987f387ed87e787e187db87d587cf87c987c387bd87b787b187ab87a5879f87998793878d87878781877b8775876f87698763875d87578751874b8745873f87398733872d87278721871b8715870f8709870386fd86f786f186eb86cf86a88655860d85a4855c850984b68463840583c88375834382fb825b8234820281af817d813580d7808f803c7fe97f8b7f387eae7e5b7dbb7d737d207cc27c647c277bd47b817b397ae67a937a4b79ed798f793c78de78a1786f781177c9776b771876c57667761475b67579751b74c87480742d73cf737c732972cb728e7251721471ab714d711b70bd708070226fcf6f9d6f6b6f236ee66e936e2a6dcc6d6e6d1b6ce96c8b6c436bfb6bbe6b816b2e6adb6a7d6a4069e26984691b68de6880684e681167d46797675a670766b4666c662465f26594653664e364b16448641663d96391636a631762c46271623461e16183613b60fe60ab606e60315fe95f8b5f2d5ef05ebe5e765e445e075dbf5d615d245cbb5c5d5be95b5f5b015aae5a5b59f25994594c58ee58a6583d57ea5755570256af565c561455c1558f552654c8546a540c538d532f52dc527e522051c25185514850ea50b8508650284fca4f614f244ee74e894e2b4dc24d644d064cbe4c8c4c4f4c074bd54b614b194adc4a9f4a414a0449bc4974492c48e44870481247bf476c474546dc467345ff45e3456f4532450b44d9447b441d43bf436c4345431342ec42a4427d424b422441b04173412b40f9407a40273fc93f813f233ef13ea93e6c3 else (if j<9 then 0xaa352940000505214ba94518a8a80296a0ae0c862ec0d8632392d22582b942001c82050c144b072080d3051241f97904069828b60e41a27f2ec86413051c48b17606c8d80496912c15ca1360e41a27f2ec844130060a402592920e50b0092d22582d8c2425c9790728580496912c16c612a5d4a2835434014b5057184325628c0d87b0092d22582b97241c83810e411c0797f29e0c09f8c280a9a3027e0fcbe01c04617c6616c12584f09c06c036830343794f2e68804627c17817c660032c501e080107cb806f29e0f465802444b0b64fe0fcbf9410320a4b78c6005b23697e0fcbc8164f20a4b78c601224b02b0100479700de53c1813d00488921649fc1f97f2820541505f18a58b5422b285f94a4fe5d41505f074014b16c9587ca1f2920982f8360125a4494a895250bf2949fcb881a0be32802962cd19cbf07e5f009a7c0585bc6180c125b23297e0fcbc8124f20982f8c92d224b0780e41c00d07be33cbf94f06480800b0102283bd01e5fca783027e30b697e5d91ca164ec17c1b0092d224a01182fca627f2e60b02f83c00658a94ad94a794a1949b9495948f94899483947d94779471946b9465945f94599453944d94479441943b9435942f94299423941d94179411940b940593ff93f993f393ed93e793e193db93d593cf93c993c393bd93b793b193ab93a5939f93999393938d93879381937b9375936f93699363935d93579351934b9345933f93399333932d93279321931b9315930f9309930392fd92f792f192eb92e592df92d992d392cd92c792c192bb92b592af92a992a3929d92979291928b9285927f92799273926d92679261925b9255924f92499243923d92379231922b9225921f92199213920d9207920191fb91f591ef91e991e391dd91d791d191cb91c591bf91b991b391ad91a791a1919b9195918f91899183917d91779171916b9165915f91599153914d91479141913b9135912f91299123911d91179111910b910590ff90f990f390ed90e790e190db90d590cf90c990c390bd90b790b190ab90a5909f90999093908d90879081907b9075906f90699063905d90579051904b9045903f90399033902d90279021901b9015900f900990038ffd8ff78ff18feb8fe58fdf8fd98fd38fcd8fc78fc18fbb8fb58faf8fa98fa38f9d8f978f918f8b8f858f7f8f798f738f6d8f678f618f5b8f558f4f8f498f438f3d8f378f318f2b8f258f1f8f198f138f0d8f078f018efb8ef58eef8ee98ee38edd8ed78ed18ecb8ec58ebf8eb98eb38ead8ea78ea18e9b8e958e8f8e898e838e7d8e778e718e6b8e658e5f8e598e538e4d8e478e418e3b8e358e2f8e298e238e1d8e178e118e0b8e058dff8df98df38ded8de78de18ddb8dd58dcf8dc98dc38dbd8db78db18dab8da58d9f8d998d938d8d8d878d818d7b8d758d6f8d698 else 0x113cbf94009e0ec6185180d09b50a1d97a4e029428965c0501aa54a145b2942c132851119d0b04d6528328519cbb83718a0242b060083b97602e5181383718a024291e5c02783a0de30c28d424050260a4a14068c2a55380e0c4da83d1e68b4b908184d882014420401e05c110030198182488b00a480f02e08801c0608d004029008c110482020b0028de53c1f8c02c11c50800cc208e05acbb2214e2816b28c8845880cc04797f29e0fc600dc030130495817cb9960800605003800d083c32c283c01c658301c020cb0650c6100832c222202c8225389a5fca78cd002a4cb0c08941827d2e02f4a601d186000014c5d81b236192580b489012418372ee31c003d60d2587318e51c1b8007a2997b2960e80d8052c3194b2f60e80d8052c304ab2e81aca002b06a5870800b64b06041ca38372e03a4b0c041cbb837180f5834961c08397602e500138392c380a01003a4b0865c21d9400560e80d8c52c419408765c01583a036314b1060ecb83db29406c62961cc1d97b29406c0296180460101c6584011a300760132c2923f2802002e011746619403e50c01961bcbf94f06004070a03b46406802201e08001746794802300e01065830140980d012110580a14e1a2704c22c307c404201e05c1181404400c1080c200502607c03440140981f83ef18280a04c0bc0d013700300802c8885388bc0a303d00c68404196140500801c658421e48c009460120206816028538709c1308b40c228b7180190303da0a338c01d41500881140778c01a04f400c50f008c232c240101a0281309e5fca783080c14438c01100f8c10ec145300110040821002a010252584d19e5c226010802e8c2166002209a330080e32c228b71900443d051546397a4ea0a828a0964a00092d285828051c25c9700125a50b0500a3a97528a8541d000014147066a5d4a2a1a00002828052144a81523414491324640b05114ba94542a0e80000a0a3c89923205828922640c9160a22975280014b2a1a0a014711301148d051012c9494320d8000060a384b92f28641b00000c147306e51c039701d258651ea5d51a94542a3280000a0a4a4b912c8e40b051490e94238017058a0d802e944162121d2982ccb1891708e94c16658c48a4874a60b32c62454178474a1963122997328000cb1a1c0a01475060a019500a0a2983f2e6082060514cb99431868b00196c0ae0c832e650c19a1c0065b02b8c2092c8c61f209828b232cbb27904c14551ea5d51a94542a3280000a0a4a8972ea8a80107a4f4147518e5c19527a0a298cb2f89cc160514c1d97b29632cb5011a55822f2fa0302844182579720de500178332c3f97f2960c0278c32c3004d2960e41f97c03a30cb11a5241f97c03a00cb0ca0fcbb8c7000124b3061dca2837002a64b040198bb03618c8d80496912e508802a3d4b)) else (if j<12 then (if j<11 then 0xb07e5e8101a50a2d83a37e5e8100650a358303546d428822c09f97c05e0f00f8cc2c617049460cc601601268cc28c645ca18bc2d824543f65ccce163462997306630d1e16c12615ca10e5d53a99a2ca8c5822a0c0b009546a146022e5e90aa7a2ca8c6506a300b009546a14672f487460a7a2ca8c630765cc659430069cc79a3c2d824a32865c01001c2c2001c01520c1b94718c9dcb48972e398372ee3185b96912e50708e0d81986088c1d27b2f42eca001b18a2490460500182101806c04c2700a48170460501080cc540900488200a5086078101561ec0dcbb23619c524b4890625783f1811c1b305149390b60a180524e42c09080b18a30f6072580b489012409162ec8d81c9602d2240490c5d81b236192580b4890124297506a8d46394a134147c1665843066581808605a230513ec64306227d88f1492d2246a014668586046802a1a16210013f4643606e5d86714600c9d87b2392d224a600c2d8cc96912280f02e0880190603c320ff2e01a41080201cf21f2fe0f8679401c04f210122c0a00303e05a008a700a381400600003a9b80207b829005c0b01f802130028c08fca01f00026e0088200a479400326e548805c03c06f0607a008c00fcb81f80c078572810809812623415808e08546627d2f82f4a002d066589306e51c632772d2146306e5dc6306616e5a428e652cbd8cb2c04e952851dca38364ee5a42c0119cbb96026caa034858023d94b2d419152851416b97706c1a428b41ac602a50a201aa0d63142880242383690a2033728e3242b2a408303372ee0d85b8c60d21502100cdcbb9471804c0c4857068109066e5dca38360d215808ec24050260a5214068c60ecbd94b2d419428c05c0a0030180580481f00a400f03e0fc2a606805c24702e0500180c02c024098e07e0dc0603b00a008ce51c1b27718e5d4b4851dcbb83616e318339452d214872ee51c601f52d2154100421cbb94706a5a42b061b4a185b2d82c1b0a631ca38372ee15938c11c1b0080c0781704400c1080c04005a059203c0b8220060780b406802450930a11c1b09a5cc2e2708e2001d2e6841e0828c0083e0e4284760ce304f2e04bc18c21166146f2e04bc190630a404654ee5d45b94604e0d80b8c30a4820f2fe0c0d050f1907cc290e5dc1b8c0a207c038041c0f79704de5009783808614872ee51c185060207c0380421c6797034c1a42b011bcbf94f061000278c80e6148d07e30c2e020502f97f29e0c0978c03e01c0210e0c26b80637216030c65eca583a03601428c652cbd83a03601428d65280d80436a14505ae5dc1b8c60c061ca4852023f9706de53c181ff186148a1765280d8c454a14632965c09583a03631428e088c1d27b2f42eca501b18a149b2f6500958350a804606742680853054a146a1204e8085350a289b04ca14301481942a else 0x1abb066a5cbe09c0a3383357650d3e09c0a329750429e84d0515ca1a7357827028be53c61a7b2f825c1e051ccb98334663304809c0a383330668cc66090138140290e5cd3999c13814532e6a4d199434263304e0520da19431e63304809c0a0148355e52c19a2f1804f04b97c0a4ca9957a0d84b05141999734663304809c0a0148064e5f04e0510ca032353827028a0a2c1832c13814535760cd4e09c0a2a94552a0a84d0514c19a331869f04e0500a383d52de5fca78301be307729a0d55aa7a134146a59e5153d097074146706a9e84d05114a283556a3d46509013414840a0f082797f29e0fc601320186837280c555d09a0a380e71804c8088a6f4bf9451fe30095097074149060e0e84d05134ba9b061426828ba0d55b9454f426828c0f01c80d0fca78c54fa5e84b83a0a3f94f1860ac1e0972f8147822a0d51aa7a13414028ea0e90a8ba13414552ea0d51a8ca12026828e0b541aa351804a84d0500a42835040bd4cd09a0a329405ea4684d051541aa3518a9e84d0500a380101c0550283d145080507a054198aa0e90a8b105426828c0b14a28f50142404d0500a411152ea8d4050901341402900df0080810e6005c0260004082114ba94518aa684d0519c1aa7a134144b2e66418609c0a2a1f357650c7e09c0a318331868ccb609013814029065c089a93578245822600d119631f82404e0500a4997318e50cb1a3c1202702900701980872ee51c1c0271804c831407043833208021cb882707009c601320c620521202041037203005c010259cbb94706e32009041c8489610500880c01700388740be5fca783209e3200b80240e033010e5dca101104e008774e5dc1c0270040460380cc04106707009c010120c0797f29e0c09f8c1884f97f0700bca38010e0ec8092815cbb94706e31c01041c0e0870664100438372e26dc6106728e001c1a0f1cbb83718a45c01041c84b97707009c638010e388772ee0dc6291700410707820bc18022020e4672ee51c1b8c202e00820fe0e00904010200812ce5dca38371821c1e882240439770600bca38010e4048148e5dca082644e31c0087200439707ae0c4138c70021c813625a0483d728e0c4138c70021dcb960164b797f29e0fc6087700409672ee51c1b8c700410732e60cc61a330185b04b9420cb9833466330b016c12024806660cd198cc2c05b0480920c018b33385b048ae5cd3999c2d824502e00c02442817a5983020211020f9041084203a5305989100b80c00001c12009104014801e05c1100301981a05820200781704400c066062160241012e300330b632060506dc8f8a6061382c11e28c0dcbb0002d2259390c5d81b236192580b489012430f60a00a4100102a40244f14240b80c02c07c85809096014832810ecbd02b07406c62852026d97a0560d032851ac1d02034a144) else (if j<13 then 0x383802150fb068043058a5141aaba12026828e0b14ba94553426828ca894bd0f546a5150a8ca134149904c8e55583612c14652ea0d51a8ca12026828f0094baa351942404d051d4a28351ea31cbd09a0a3aae528a3d46509013414029120814583612c145b2925253c91644c25828e0501430960a25976452a453b0960a301c12c41084d97b2820ac1a0220363100813024701ab004043b2f2a984b051287aaba46e0c41509a0a3d97954c2582892af41ca9b2ec25828ca5d462a350142404d0500a44a9b2f2af41b0960a3594928c8845c91612c147222a5d51a83a12026828ea514628f50142404d0500a4294506a3155d090134147078201048a724e22c859014020480c00d314ba83546a31ca509a0a381c41285acb81210560d01101b19246ca026b00720b92f23254b0960a32a5528a0d47b97a13414705aa5d51a8ca1202682805214a283a44a3d46509013414892922c1330960a291152ea0d51b94a13414752ea0d51a8ca12026828ea5d4a28c553426828ca914ba94544e0e84d051d4a28351ea31cbd09a0a3c8295409ac1b0960a3297528a8950a8c7074268290a5d462a352d42404d0500a4794f18a0b41d0972f4147528a3147a96a1202682805214a2a9505426828ae5d41509a0a211152ea8d4b50901341402914b3ca282a12e5e828c0b14a28f52d42404d0500a4794f180d64130932ec147546e5e90e8c14f426828ea0d462a352d42404d0500a4011546e5e90aa7a134147822a0d51a96a120268280521cba9954f426828aa5d4a2a2542a31c1d09a0a4522d0622dca28fa134147728a9d55a8fa134146052e52912a751f426828e65cca1a2342631c1e09c0a419730668cc6394c13814732860cc798c72f827028fe53c602f02529d8498360a419b06ce0f04e0514ca1a9305827028a65ec61a9357824505a688c619631f82404e0500a499731868ccb609013814029165cc1609c0a219431863ccb60901381402906a4d5d83c138145252a3151a96a120268280520ca18331e631cbe09c0a39940518270288e5cd5609c0a2197356664c59a9c12318333262f04e0514cb983346631ca609c0a383331e630c01a2c120270280524cb994344684c6383c13814832e630d1980c120270280520ca1833186af04809c0a3d8334f8270288650c618f30182404e0500a4 else 0x0))))
def mo255H9 (_ : Nat) : Nat := 0xa240000006290000002d3000000000000000000000000000000000000d50000000000f39000e2aa400000000006261d97d621a84443230e000642000000000000000422000000dca625000548000000000c2f000000328b1e553000c0f0113b3d5753d3545527b600682703e00000000000000000000091c000c3f000d2ea16d050000000000308d8023317746ed5000000815000418000000f0a000090000000000000d34000000a31e1300000000000054e000000000000a1000083c51d000000000000000000000000000000000000000000000000000000751000704000000f2000000064900000035a000f0100000000000000000000000000000000034700000000000092c000f38c19000000793000000000000b33109a3a00000000000000000091f135000000000114000000000000391f8f00000000000000000000014c000000000000136000000000000b4500000000000073b000000000f3700000072d64d14f000000f58a0b64bc03e0c5550000000005b83b70008cd000000a59000056000000000000000000602000000912000000000000000000b4a000000000341000000000000000d43bc852b21b000000a0d2b11077b20000000007080008ce000e21000000000000000001000040007000000400018000400000000200008000008018040001000000401000040002
def mo255D10 (j : Nat) : Nat := (if j<12 then (if j<6 then (if j<3 then (if j<1 then 0xab8a62a06ff609720437fb0e40a61ff55148540dfec29029877f5cd70502ffb2840a617fd9220530bfecba42a05ff655215037fb0440a617fd9348540df6c1064086ef5d5840437bb06990219fd8754810ddeb2b08086f760d730437bb06b1821bbd8458810deec1ae4086ef611530435fb0ca9821bed8258810ddec2264086f760d530433fb0eb1821bbd840c810deeb2b06084ff660320437db26c1021b7d855cc10cfec3a64086fb24d820435fb0c99021bed824c810df6b9b04086f760d620437dac6c1021bed5360810ddec22e6086f75d9830437bb2ac1821bdd7560c10df6c12e4086bf619720437bb24c1821bbd7661010dbec2ac4086bf619520435fb0cb9821bdd9760c10dee49306086ef611520437bb2cc1821b7d8558c10df6cbb04084ff661320437daecc1021bed9560810df6bab04086f760d520436fb0a99021bbd845c810df6b2b04086ef611630437db04a90219fd8758810df6cb304086fe5d9800877f326c0043bf89360021dfcb1b0010d7f65c825827f930a12c13fc984c9609fe4c2e2b04ff261515827f93098ac13fc9848560afecb842b05df65421582f7b2810ac17dd9308560deec1864084ff261625027f930992813fc985c5409fe4c2a2a04ff261315027f93090a8177d95205309fe4c2e2984ff261514c3faae298a61fd5614c5309fe4c242985f764d214c27fb3010a616fd9608530bfcc8042b04ff261625c79faecb92c33fc98589519fe4c284a8dfe241824c6f7b28412633fc98589319fe4c28498ff550d714c7faa64b8a63fd53258531afecb90098dbf658804c6efb2a402637bd9420131dfccb30010ef760d6308777b08b1843b7d8558c21cfec3ac610ef7241830877bb20c1843bdd7660c21bf6c910098eef5d984086fbb26402437bd9420121b7ecb10090cff66131487fca84a8a43bf89060d21bfc4830690ef765983086dfb2c4122177d9520910bdeca104885f764c824427f930b12213fc98509109fecc264884ff261324437bb06992213fd980c910bdeca064885fd64432442ff32019221fd5434c510fea99262885ef650214c2feb2690a21fe54248510ff898a80887fc485404427fb3098221fd5314c1109fecc240887f948520443fe26290221ff12148110cfe4930e086df5d9850436f926c2821afd865d410cfec3aca087fc24131442fbb2610a617f99008530fec992c0987f64c5604c35fb0caa061bf59560430dfaca302186fd551810c37eb24c0861bf49260430cfec3aa2186bf619510c377b08a8861bed8254430dfac0aa21857f65c82442efb2a41a217ec9261510bfcc8042186fd604210c2fbb26108617bd9408430d7ec30421867f61d410c37eb0290861bbd8448430d7ec3242184ff661210c37eb02a0861bed8250430dbec2a82186bf619410c27fb3010861fe12148110 else (if j<2 then 0x2ac0987f74c9604c3fba62b0261ff98558130ffcc12c0987fe209604c3ff2a4b0261fdd9348530bfecc282986ff61d414c2ffb2aa0a61bfd8550530fdea1282985ff655314c37fb0a98a617fd944c530feeb9a62987f758d314c3fbaa698a61fdd434c530fee99262987f7261314c3fbb2e98a61fdd724c530fee41262987f7609314c3fb92498a61fdd924c530feeaa262987f7591314c3fbae898a61fdd874c530feeca262987f7595314c3fbaea98a61fdd854c530feecaa62987f75d9314c3fbb0c98a61fdd324c560feec2262986ff65982043f7a84a0861bfd8150430dfecbb04086ff661210c3fbae6a9821bfd8648430bfeca242186ff60d530437fb0290861ff55148430dfec22a6086ff618210c3efacaa98217fd9408430ffcc0ac0985ff65953043bf92ea9821fbc9461910bfecc2ec886ff61d854437fb0cc2a21fec9261510bfecbaa6085ff66175442ffb30b2a217fd9759510f7ebb2ca886ff61d844437fb0ac2221bfd7561110fbebaaa6087fe205604c3ff2a2b0261ff92158130ffc10ac0986ff61d404c2ffb2aa0261bfd8550130fdea1a80987ef509404c3fba64a0261fbd4150130fee98a80987fe5c1404c37fb2ac0861bfd9460430dfec1282186ff5d9820437fb0aa08617fd9550430dfecab04086ff5d5820437fb0ea0861bfd6560810dfeaa302186ff64d820437fb04a8861f7d5454430dfeb9b04086ff58d820437fb0ca8861bfd5360810dfec9302186ff605510c37fb3099281bfc984c940bfecba64a05ff65532503f7b2899281fdd534c940fdea1a64a07fb5c932503f7a8499281ff8904c940bfecb864a05ff65432502ffb22192817fd974c540efeb92e2a05ff65d62042ffb2ea8a81f7d5354540fbea92a2a07fd5c551503f7aeaa0a81fbd7350540fdea9a82a07ef5c941503f7aa4a0a81fbd3250540fde19282a06ff26131502ffb20192817fd9308560f7eb1842b05ff64021583dfacab10217fd9720d40bfeca906a05ff64883502ffb2ea9a81dfc9754d40fbebaaa6a07f75cd53503f7aeaa1a81fbd7350d40fdea9a86a07ef54942502ffb2a412817fd9320940efebb2e4a07df25572503bfaeab9281fbd435c940bfecbaa4a06ff61952503f7a86a9281fed7254940fdebaa84a07ef5cd42503f7aa6a1281fbd7250940bfecb904a05ff654814c37fb0c40a61dfd725c140dfec2b08987ef50970503bfae2b8281bfd8260530dfec2302986ff615814c37fb0cc0a61fbd415c140dfec3b02987ef50d70503ff2a4b02817fd9550d30dfec2ac6986ff61950503f7a86a8281f7d5154140bfecc2a8987ef505505037fb0ab2261ff96054140dfec3b08987bf259844c37fb0aa1a61f7d5454530feecb262987df615514c2ffb2a98a81bfd8654530dfec1ae4085ff661514c37fb0ab0a61fdd324c540ff else 0xa2b05ff65521583dfb2c90ac1bfd8748560dfecc242b07fd545214c2ffb2a98ac1bfd8258810dfe4c262b05ff64d21583feaa298a43bfd8660121dfec230090eff60d804877f906c0243ff55160121bfecb10090eff61880486ffb2c99021bfd8420121bfec990090eff60c80487feaa2402437fd974c810dfecb30610dff654825837fb0ca9021bfd8454810dfec1aa4086ff58d800877fb26c0043bfd7660021dfecb30010eff5d9830877fb0ab1843efd7658c21dfec12a4085ff65d63087fdae4a9021bfd984c810dfe4830610eff641830877fb06b1843dfc9761531dfec330a98dff261654c77fb0ec2263bfd8561131dfebab0898dff261744c77fb0ab22637fc9855131dfec22e698eff615634c77fb08a9a63bfd8550d31feeb9a8698ff754d434c77fb04402637fd9020931feea190498eff610824c6ffb2e190217fd9520931dfec310498eff61c824c7fbb0ea1a63ff89060931feea1b0498eff611824c77fb0ac1263bfd8660931dfec3b0498ff75d5434c7fbb0aa1a637fd960c810bfec8104b8dff648805c6ffb2c41aa37fd9020d51fbeb22a6a8fdf58d53547efaa6a1aa3bfd840c810bfeca864087bf5d961547efaa6b0aa3efd6258551bfecb100a8dff64c80546ffb2ea9a837fc985d931ffab8aa2a0fdf54951507efaa6a8a837fd9754541ffaa92c2a0f7f5c971507f7ae4a1283dfc9754d41fdeb9a84a0fef5d5425077fb0ca9283dfd755c941fbe4aae4a0f7f5d972507fbae6a9a83f7d7554d41fdea9a84a0ffd209614c7feaa4b0a63bfd824c810dfec32a298fdf54d514c7efaa4a8a63fdd3254531ffab0aa298eff61d414c77fb0aa0a63fdd3250531ffab8a8298eff61d804c77fb0cc0263bfd8560131bfe4c2e498eff61132042ffb2440263fdd4320131dfec210098eff614804c77fb06990217fd9520131dfec230098eff61c804c7fbaa699021ff56160131ffab8b0098ff74c9804c77f904c0263bfd8260131feea1b0098eff618804c7fbb2c99263fdc984c931feea1a6498ff758d324c77fb0899263bfd8750931ff6b1264087fd609614c7fba86a9263bfd8454931dfec32a498dff261524c6ffb30a92637fc9858931feea1ae498eff611724c6ff930a1263ff58558531fee992c298eff615614c7fea84b8a63ff4825c531ffac12e298ffb5c932043fbb0c99263fdd325c531feec8a6498ff7551324c7fbac899263fdd744c931feec226498ff7651324c7fbaec99263ff5845c531feeb1262987f7549314c3fba8498a61fdd714c530feeb0a62986ff61172043fbaa298a61fdd414c530feec8262985ff661214c37fb3090a61dfd755c810dfec3242985ff651214c2ffb2690a61f7d5354530fbe4aae4087f74c5214c2ffb3010a61dfd765c810dfec3042985ff650214c2ffb2610a617fd9008530dfec)) else (if j<4 then 0x887fd50931443feaca90a21ff5434c510efebb2e6087fd64931443fe92498a21ff57548510ffac1262887fd20931443feae498a21ff5624c510ffaa9262887fd54d31443ff30aa0221ff98750110ff6b92a4886ff61d42443ff2a0a0221ff97050110ffa90a80887fd4c5404437fb06a1221bfd8250110bfecc2648877f5c970442ffb2eb1821bfc984c910bfecba64885ff659324437fb06a02217fd954c910dfec2a80886ff61d404437fb0899221ff97054110ffa90aa0886ff661324437fb0698221bfd844c110bfecc2a4885ff65d524437fb0a982217fd954c110bfecb2a4885ff65930442ffb2e98221bfd8654910ffc19280887fe5d540443ff264a0221ff95250110ffcb9280886ff61152443ff104a0221ff98250110ffca9a80887fe5cd40443ff106a0221ff98350110dfec1aa4887df61552443fea62b0221bfd825c510efeb92e2887bf58560443dfac4b02217fd9758510f7ebb2c2886ff615614437fb04b0221bfd8358510f7eb1ac0887fd4c5504437fb0ab0221bfd8258510bfecbac0887fd48570443dfac4b0a21ff5315c110bfecbaa28877f5c570442ffb2ca8a21bfd8654510dfec1aa2886ff60d60443efaa2a8221bfd834c910feec1a64886ff60d73043efaa4a8221f7d5354110dfec1aa0886ff61150443fbaa699221fed724c910dfec32a0886ff60d71443fdac499221ff5914c910bfecc064885ff65c32442ffb2c192217fd950c910dfec22e6086ff61032442ffb22192217fd900c910bfecbaa0887fd48560442ffb2ca8221bfd8558d21dfec1ac690eff615434877fb06a1a43bfd835c521bfecbac290fbf5d9614877fb0ab0a43bfd8358521f7eb12c290eff619514877fb06a8a43ff56154521ffac32a290ffd611514877fb06b1021ff5714c521fee9926290dff649314877fb0698a43bfd854c521bfecb26290dff65d31487feac8a8a43ff55150521dfec1a8290eff615414877fb0ea0a43ff54354521ffab1aa290ffd20d51487feb06a8a437fd954c810fee9910098ffd5c4804c7feac240263bfd9560831dfec830418eff619520c77fb08a9063bfd8254831dfecab0018eff649800c77faa4c0063fbc9461921bfecc2ec90eff61d844877fb0ac2243efd7658d21bfecbac690dff66163486ffb2041a43bfd8420d21bfecb10690eff241834877fb20c1a43bfd8559121dfeb230690eff5d1834877fb28c1a43bfd7660d21dfecb30690ffe241834877fb08c1a43bfd8660d21dfeaa30690dff64482583dfac6a92c1efd6254960bfecb2a4086ff26132582ffb2a992c1fdd534c960bfeca902b05ff64881582ffb2ea9021efd5258560f7eb1aa2b07df54d51583dfac4a8ac1f7d5254560ffab0a6290dff654215837fb0e10ac1ff89048560ffaa8a42b07bf58521583dfac490ac1efd6348560f7eb0a else (if j<5 then 0x5ff661724437fb0cc1221bfd8354d10bfeca904886ff5d1834437fb0ec1221bfd8320910dfec2ac6086ff249834437fb08412217fd9720d10bfec9904885ff65883443fba6498221bfd9260c10f7ebb2ca085ff65d650437fb0ab2221bfd9760c10ffa90a40887fd4c5204437fb2cc1821bfd7660c10f7eb2ac4886ff655830437fb0ec1a21bfd8660d10dfebab06086ff615834437fb28c1a21fec825c910bfecc2c4886ff61c824437facac1a21bfd7560d10f7ebb2c6086ff655834437fb08c1a21bfd7660d10dfecb306886ff61543442ffb2eb1221bfd9760d10ffcb0240886ff60930443dfb0cb12217fd9148110dfec2240886ff60d624437fb2cc1221dfc9754d10dfec3240885ff65920443ff28098221ff93048110ffcb8260886ff5d9824437fb28c1221bfd7460910ffa90a60886ff61582443ff30c902217fd9754d10ffcb0260886ff61182443ff32890221ff98448110dfec22a6887fe5d1204437fb06c1221ff97648110ffcb2240885ff65953443ff2a890221ff98348110fbeb2aa6887fe20d20443efaeaa9a21ff96348110fbec2aa6887fe50d204437f906c1221ff93148110dfeb2b06086ff64d82442ffb2298221bfc9360910dfeb1b048877f5d973442ffb30a9a21bfd4360910bfecc2e6885ff64883443ff130902217fd9720910dfec1ac6086ff610834437fb0a41a21ff92148110dfec1a40887fd4c5304437fb06b1a21ff99148110fee98a60886ff61563443ff2e290221ff99648110dfec22e6887bf5d963443ff2c290221bfd5460910bfecbac6885ff661634437fb06b9a21ff95148110ffca0a40886ff59182443feac490a21ff57248510ffaa8a62887fd50d21443feaa690a21ff5414c510ffab1a42887fe24131443feae690a21ff48348510ffa4c262886ff5d584043feb2e98a21ff5874c510ffa49a42887fd64d21443feb2c98a21ff55448510ffac3262887fd59121443feaec98a21ff5954c510ffac2a62887fd60d21443efaa6a8a21bfd8254510efeb9ae0886ff60d704437fb08b8221f7d5254510ffab8aa2886ff61d414437fb0aa0a21bfd8350510dfec1282887fd54921442ffb2c98a217fd954c510dfec2a62886ff60d314437fb0498a21fdd324c510ffac8242887fd4c921443feae298a21ff54248510ffab0a62885ff65d31443fea6498a21ff5904c510bfecba42886ff61d21442ffb2c90a21bfd8648510bfecaa42885ff64d214437fb0690a21bfd8248510ffab8a42887fd5d121443feaa290a21ff54148510ffa98a42887fd26121443feb2e90a21ff58748510ffacb242887fd61921443feaec90a21ff59548510ffac2a42887fd58521443feaea98a21ff58448510ffab2a62887fd65131443feb0898a21ff5744c510ffab2262887fd65121443feaa898a21ff5734c510ffab1a62 else 0xf5cd50443ffb0ea8221ffd7154110ffeb22a0887ff58d50443ffb0ca8221ffd6154110ffebaa86887ff5cd43443ffb0ea1a21ffd435c110ffea1aa4887ff61543443ffa86a8221ffd7550910ffeb9a84887ff50970443ffaa6a1221ffd7561110ffec22e6887ff61172443ffb08b8221ffd8454d10ffec22a4887ff61150443ffaeaa0a21ffd7350510ffeb9282887ff50570443ffaa6a0a21ffd5250510ffea0aa0887ff5d540443ffae6a0221ffd7250110ffea9a80887ff54940443ffaec99221ffd754c910ffeba264887ff5cd32443ffb0e99221ffd325c510ffe992e0887ff59532443ffac899221ffd634c910ffec3264887ff4c961443ffa64b0221ffd544c910ffea9a64887ff50d32443ffb0899221ffd3250510ffe99280887ff5d983443ffaeac1a21ffd7460d10ffec1ae6887ff60d72443ffb06b8221ffd6560d10ffeb2306887ff60d63443ffb06b1221ffd8358110ffeaa306887ff60d53443ffb06a9221ffd8354110ffec1a86887ff60d32443ffaec98a21ffd754c510ffeb9a62887ff5c931443ffa62b8221ffd654c510ffeb1a62887ff58931443ffa62b0221ffd534c510ffea9262887ff4c550443ffa6498a21ffd764c110ffebaa60887ff5d130443ffb2e98221ffd734c110ffeb9260887ff61d30443ffae298221ffd654c110ffeb2260887ff65930443ffac698221ffd624c110ffec3260887ff58530443ffaa898221ffd954c110ffea9a60887ff54930443ffb0a98221ffd514c110ffeca260887ff50d30443ffa8498221ffd844c110ffea0a60887ff64930443ffa6498221ffd914c110ffe98a60887ff5d982443ffaeac1221ffd7460910ffeb9b04887ff60970443ffacac1221ffd6460910ffeb1b04887ff60960443ffaa8c1221ffd5360910ffea1b04887ff60930443ffaec90a21ffd7548510ffeb9a42887ff48570443ffaca90a21ffd6348510ffe90ac0887ff54d21443ffa4298221ffd7648110ffeba240887ff59120443ffac690221ffd5448110ffea1a40887ff54881583ffae641281ffc9260530ffeb990498fff24532583ff92498a61ffc8250530ffebb104887ff58c82443ffae641221ffd7358c21ffeb9842b07ff08570583ffaec10a61ffd8608530ffeb1842987ff085604c3ffac6402a3ffd7520131ffeb910098fff548804c7ffaa4a0861ffd5448430ffebb10090fff58c80487ffacab9821ffd7558c10ffeb1ae4087ff5d562043ffae6b1021ffd5358810ffebb2a4087ff5cd52043ffac6a9021ffd754c810ffeb2a64087ff50d72443ffae498a81ffd5350d21ffeb928498fff54d43443ff28090221bfd835c910feeb9aa6885ff654834437fac8c1a217fd9620910dfec22e4886ff551834437fb24c1a21dfd755c910dfec3104887df255724437fb06a1a21dfd765c910efec3ae488))) else (if j<9 then (if j<7 then 0xd5414c3ffb0ea0a61ffd7350530ffeb9282987ff5c5414c3ffaa4b0261ffd8550530ffea9a82987ff549414c3ffaa2a0a61ffd7550130ffec3a80987ff5cd404c3ffae4a0261ffd7150130ffec2a80987ff54d404c3ffaa4a0261ffd5150130ffebab02987ff5d1814c3ffb04b0a61ffd815c530ffeb2b02987ff591814c3ffb04b8a61ffd8158530ffeaa302987ff609414c3ffb02a8a61ffd8250130ffec12a2987ff605414c3ffb02a0261ffd544c530ffea9262987ff545314c3ffa64a0261ffd424c530ffea0a62987ff4c5404c3ff930a8a61ffc8354940ffebaac890fff5d563487ffae6b1a43ffd8759121ffec3ac690fff58d71487ffac4b8a43ffd7558521ffeb9ac290fff5c961487ffaea90ac1ffd7348560ffecba42b07ff5c921583ffae290ac1ffd215c160ffebaa8690fff5cd43487ffb0ea1a43ffd5358521ffea9a42b07ff61564487ffb0ab1a43ffd9548560ffec2a8690fff58d51487ffaa290ac1ffd7550521ffeb9a8290fff5c941487ffaa490ac1ffd5350521ffea928290fff5d521503ffae690a81ffd7248540ffe90ae0a07ff54d21503ffaa490a81ffd2154140ffebb30690fff5d183487ffac8c1a43ffd8358d21ffec9a42b07ff55183487ffb06a1a43ffd764c521ffebaa6290fff5cd31487ffae498a43ffd3248560ffeb2a6290fff58d31487ffac498a43ffd3148560ffea9a6290fff54931487ffa6490a81ffd324c521ffebb242987ff5d1214c3ffac890a61ffd8648530ffeb1a42987ff659214c3ffae290a61ffd6148530ffe90ac0987ff551214c3ffb0890a61ffd4348530ffeca242987ff545214c3ffa8290a61ffd2150130ffecc242987ff64d214c3ffb0290a61ffd3148530ffebb30090fff5d180487ffac8c0243ffd6360121ffec8242b07ff55180487ffa86c0243ffd9048530ffe4c242b07ff261214c3ffacab9a21ffd8759510ffeb2ae2887ff59570443ffaeab2221ffd645cd10ffeb22e4887ff61d64443ffac8b8221ffd7558d10ffeb9ac6887ff58d72443ffb0eb1a21ffd635c510ffeb1ae0887ff5d562443ffae6b1221ffd8758910ffeb12e2887ff58970443ffb0cbaa21ffd865cd10ffec32e4887ff61970443ffaeab0a21ffd7358510ffeb92c2887ff58570443ffaeab0221ffd7358110ffeb92c0887ff61d60443ffae2b0221ffd545cd10ffec3aa8887ff55170443ffac8a9a21ffd6354d10ffea9ac4887ff61953443ffaa6b0a21ffd5358110ffebb2a4887ff5d152443ffae6a9221ffd8754910ffea92e2887ff54970443ffac8a9221ffd6354910ffec32a4887ff54961443ffaa4b0221ffd7661510ffec2ae8887ff61573443ffb0ab8221ffd8559110ffec2ac6887ff61560443ffaeca8a21ffd7354510ffea8ae0887ff58d51443ffaa2b0221ffd7654110ffeba2a0887f else (if j<8 then 0xec36501b150d7e86ba835ae1aba0d4fc6a2834ee1a690d29c690c345b1a180cfec678c339619a90cc88660232d619558c9b06464320c18e90c69c62f8315118908c3ec619630a518420c18c6066300817e48bea05ed22f52178e8bbdc5d8e2e92171a8b83c5bb42dc816d88b5a05a662d1716710b2f0590e2c4316070af64572a2b6f15980abd855642a7d151f0a7e853762981149e8a3e451562876141909fb84f5e2775139d89bdc4d7a2688132c098644bbe259612ab8946049bc249f1232890ac47d823b711b988d0c461222d4114d08958444221e710d4085b8426820fa105d881c840701ffe0fe487e283eb41f110f6b87a883cbc1e330eff076fc3b1e1d4b0e860737039581c770e238705c37c41b9e0db706cbc35ea1ac50d430695833fc19c90cca0657c325418fa0c6286218309818120be205e3c2e8c170c0b6b85a882ce416420b06857382b1e15500a88853ac296c147c0a260504827a6139e09b484cd025f412bb0940848f4240611c908c504540224010f50860041f020ac100807ec03e8c1ed20f34077f83b3c1d160e4206f00360c1a9c0d0a06658325818a40c2205f182ea416e80b3a058502b68152c0a5705070273c133409650498023ec1196089b0435820c40fee07b803c401d380e1e06da034d819700c4405e302cf815800a4c04e20254011b80868040401e000df0067002f9015d009ec046e020200df005e8026c00f20057001bc004200007ff26151583ffaeca9283ffd6354941ffea92e2a0fff54941583ffae6a8a83ffd5250960ffebb2a4a07ff5cd52503ffaa4b8a81ffd525c140ffeb1aa4a07ff58952503ffaa4b0281ffd7354540ffea8ae0a07ff5d950503ffac6a8281ffd7154140ffec2ac898fff615624c7ffac8a9263ffd8654931ffeb1aa498fff589524c7ffaa4b0a63ffd524c560ffeb1aa298fff589514c7ffaa298ac1ffd754c940ffecba64a07ff5cd32503ffa64b8a81ffd724c940ffe992e0a07ff5d5844c7ffb08b9263ffd8454931ffecaa64a07ff50d524c7ffaa699281ffd7550931ffeb9a8498fff4c951583ffaa6a1263ffd5250931ffe992a2a07ff5d5414c7ffae6a0a63ffd7250531ffea9264b07ff54d414c7ffaa4a0a63ffd524c940ffebaa62a07ff5cd31503ffa62b8281ffd534c540ffea9262a07ff4c550503ffaeac1263ffd7460931ffec12e498fff595824c7ffac8c1263ffd8258931ffeaa30498fff609524c7ffb2299281ffd544c931ffe992a298fff4c9414c7ffa6498a81ffd7560131ffeba30098fff5c9804c7ffacac0263ffd6460131ffeb130098fff551804c7ffaa4c0263ffd904c940ffe4c264a07ff615644c3ffb0ab0a61ffd845c530ffeb22a2987ff619514c3ffac6a8a61ffd6154530ffeb12a2987ff545604c3ffb08a8a61ffd4354530ffea12a2987ff5 else 0x22531528da942e4a01a4f11270a93414983a4b35254e928b492da48d5241e91e948d7a45fd22a8910b487a242c1211e905f4803a3f5d1f768f9f47b523cc11e1e8edf475f239c11c588dde46cfa35f91a6a8d0a466fa326d18f48c3645f922ecd16f28b3a4582a2b5515408a5c4516227dd137a898d44b3a24f111c888b44444a21150ff887c243c6a1d250e3286ee435521a110cb2861f42f5217110b3c8569429ca143909bc84b3423ca10c107ce83a841c620d71064482ed4157209e5047e822340f7206e5031c817240a3a045d01d880b2403220080ffd67fc03fc59fd80fe427ee23f4f1f9ccfc9a7e2c3efb9f758fb427d853eaa9f4bcf9fe7ccf3e549f1e4f8ba7c2d3dfe9eebcf6ea7b4f3d881eb94f5747a943d371e8a8f3fe79cf3ccd1e594f25678e23c609e258f0cc782c3bf91deb8ef06775d3b919db68ed40767a3b161d7f0ebc075a63abb1d52ce9fa74b93a2e1d010e7a8738139a39cc48e57e7299392a9c894e40871d938c59c594e24270f1385e1c280e0cc703137fb9bf80df566f9937af9bcbcddea6ebb37459b958dc386ddd36de1b644daae6d2236769b2e0d92e6c6c36281b06cd7c26ba735b69ad1cd64c6aec355e1aa44d4b86a2735009a744d338696c34969a3f4d19a68a7343b9a130d02e67f633e599ea8cf086759339719c34cdce66c6334b199d4cc6c661032f7996fccb32657332a69949cc9ee64a9324199124c846640c31ee18ed8c716637931a718c50c5b4629b314218900c3da61b830c1984d4c1c460b2303c18120c0445ff22fe617e84bed85f282f8397b20bd3a5e6d2f0f977bcbb7e5d8a2eaf974bcba085cc52e4097194b8605c0a2ded16e6cb6cc5b3b2d8096b30b5745a942d3716920b43059e82ce3966acb2f6595a2c9c96460b1ee58cc2c44160d4b04657ee2bda15dc0ae7657242b8195b88ad6e56962b2915838ab8055862ab2954c0aa1e54df2a5795198a81c53d429d494e34a6ce5341298b14baca56c5290293514898a40051cb28d014548a22650c528481416ca0424fd327b893cf09e0e4eb927499398c9c664e0826f3936dc9b224d6626a013404998e4c9c263893154984a4c0925ef12ea497104b44258512b7c957c4a702522927dc935c498d24a49243c91c848af24421213c905c480d23f391f048f22477a23a511c908dfc46dd236311a448cc2461d22fe117448b42456c22a09140889cc44b622431116c882e43f621ed10e8086d6433b216f10a40848e422120f890678829640fd2050101ac804e40011fd48fd307e103ea61f3b0f8dc7c043ddc1ece8f58c7a703d081e6c0f2b479043c481dff8eed877203b5b1d9d0ec1475a03aa51d3f8e978747a3a1c1cfb0e740735e398e1cb90e508724c38f61c6d0e21c70c2383b1c080dfa86f6a37851baf8dce46e3036f21b610da846c)) else (if j<10 then 0x4d1cf68e634725a38cd1c368e0346f5a374d1b768da346c5a35cd1ab68d434695a344d19f68ce34665a32cd19368c834635a314d18768c234605a2fcd17b68bc345d5a2e4d16f68b6345a5a2ccd16368b034575a2b4d15768aa34545a29cd14b68a434515a284d13f689e344e5a26cd1336898344b5a254d127689234485a23cd11b688c34455a224d10f688634425a20cd1036880343f5a1f4d0f7687a343c5a1dcd0eb687434395a1c4d0df686e34365a1acd0d3686834335a194d0c7686234305a17cd0bb685c342d5a164d0af6856342a5a14cd0a3685034275a134d097684a34245a11cd08b684434215a104d07f683e341e5a0ecd0736838341b5a0d4d067683234185a0bcd05b682c34155a0a4d04f682634125a08cd0436820340f5a074d037681a340c5a05cd02b681434095a044d01f680e34065a02cd013680834035a014d0076802340059ffccffb67fc33fd59fe4cfef67f633fa59fcccfe367f033f759fb4cfd767ea33f459f9ccfcb67e433f159f84cfbf67de33ee59f6ccfb367d833eb59f54cfa767d233e859f3ccf9b67cc33e559f24cf8f67c633d5d9e6ccf016768b3a719cf6ce286703b37499b08cd4f668d3336d9974cc99662d330e597f4cbcf65d732df99674caf66560b29f5947cc9f564d8b25f19298c91764673227990e6c84d6413b1fc98f84c79263bb31d418e40c6eb636531a2d8cb6c62662e7316798ae6c5576293b13c98952c45b621d3103d87b4c3aa61c230d3d862ac2ef6150b08d58428c1cb60cb30521823ac0f76059b01bd8074bfd85fcf2fcf17e2cbed25f44af9797c5cbdf45edfaf6157ad2bd395e822f3657948bc5b5e1aaf01577bebbaf5dc72ed8d7684bafe5d6c2ea8d74b4ba2a5ce92e6c572eeb94c5c702e2d5711eb8375c0b2df996f8ab78b5ba12dc856de2b6c65b282d86d6baeb5a75ac0ad5096a1ab4d85a4f2d1f56890b3ff59e52cea566cab34e5991acb556540b26b591b2c7b56370b188589d2c4156178b0965835ac0895ff8afcc57d32bdd95e96af1b57732bab15d20ae6a57222b8655bd2adaf56c22b5655a48acf95664ab2a15904ac61561dab02d57acab9755ac2ac155578aaa0553d2a929540ca9d154c42a539523ca8fd545a2a1c1504ea7e853d4a9d6d4e24a6bf53452992d4c18a5d752c7295c94a8ea51c5271292c948bea439520728f794770a38351a9a8ca145faa2c85144a893d4420a1e550e9a86dd4318a1525093a83f141aca0b550452817d40549ff54fd8a7ddd3ea29f2b4f7da7b413d2c9e5c4f1da78913bfc9dd34ed6a76093a909d184e652720538ca9c214df626f0537189b664da7a6c9135b69aab4d4526941342c99dc4cd8a65f1327a98fe4c672626530dc98394c0225f292f5297834ba725c792df096d24b35a59292c5c95e54ad5a56152abe952f4a8 else (if j<11 then 0x814c798086598289f9782f9460d8c802053004e3227e5e0be538304a00815962c2702f97e500889e0b60a05e3200658c0968342e82a5b940ff8c4010f06105a24d12d23a0a96e5c3fe310049c18416893282a5b9742f94a0d0049c01416892c3314b8ca339742f94a0d2706100416893794a5397a592742e8303b8c401052c4329f9420b831838c0230525b092c8229f9722f941838c20008c17092f8c82397e5096a0c1ac1709270bc9f8300b97e50012048225b8cc0089342742c0b49f83e5f94206824178c40296350b49f8300b97e500120482c178c25889342128794c9f9700882c1783c0096224c08c27e0f9748d27a0905e3100a5a89310f496aca5b94e0e8c4010b06105a24c48804e328c49f9742f94e0c1240105a58d49d0be5f9404b830050041689294b12d2349e96e5f8304b8c061004168934220852742f97e538301f8c01100416893404022a12b29649f9742f94e0e8c4010536ac0cf94a539749e8ce0d0b061004168936ac0a902a5927e5f94a310042c1841689354bab29649f97e0e8c4012306105a24c03c2349c22e5f940cc21204824178c40096224f00801e5f94e0f8c1b5475aa34d5176a8a35445aa1cd50b6a8435415aa04d4ff6a7e353e5a9ecd4f36a78353b5a9d4d4e76a7235385a9bcd4db6a6c35355a9a4d4cf6a6635325a98cd4c36a60352f5a974d4b76a5a352c5a95cd4ab6a5435295a944d49f6a4e35265a92cd4936a4835235a914d4876a4235205a8fcd47b6a3c351d5a8e4d46f6a36351a5a8ccd4636a3035175a8b4d4576a2a35145a89cd44b6a2435115a884d43f6a1e350e5a86cd4336a18350b5a854d4276a1235085a83cd41b6a0c35055a824d40f6a0635025a80cd4036a0034ff5a7f4d3f769fa34fc5a7dcd3eb69f434f95a7c4d3df69ee34f65a7acd3d369e834f35a794d3c769e234f05a77cd3bb69dc34ed5a764d3af69d634ea5a74cd3a369d034e75a734d39769ca34e45a71cd38b69c434e15a704d37f69be34de5a6ecd37369b834db5a6d4d36769b234d85a6bcd35b69ac34d55a6a4d34f69a634d25a68cd34369a034cf5a674d337699a34cc5a65cd32b699434c95a644d31f698e34c65a62cd313698834c35a614d307698234c05a5fcd2fb697c34bd5a5e4d2ef697634ba5a5ccd2e3697034b75a5b4d2d7696a34b45a59cd2cb696434b15a584d2bf695e34ae5a56cd2b3695834ab5a554d2a7695234a85a53cd29b694c34a55a524d28f694634a25a50cd2836940349f5a4f4d277693a349c5a4dcd26b693434995a4c4d25f692e34965a4acd253692834935a494d247692234905a47cd23b691c348d5a464d22f6916348a5a44cd223691034875a434d217690a34845a41cd20b690434815a404d1ff68fe347e5a3ecd1f368f8347b5a3d4d1e768f234785a3bcd1db68ec34755a3a else 0x2a83c30abe0d19e30a7a5b09241be5e06e308b00a9613b09244e0000506c0607402a5801c24a0c783e5f94a580ee301fc008501309303d05433e5c06e5082e0f0025801c24c08853e5c64e0e06e300bc0049a5b09300f08b9701b9418b83c0046a5801c24ca5d8c0182a0043e068702697e500111c530a83e0f1962809a538ce5f830d85302e060f1962c33e503be30530602a2170924150cf97e0c42e300b14c18217092c5426f97117940ef8c04f0006085c24c05433e5f8304f000188500709298062f9780b838078c85a09650aa140ae5e9440b834078c459092811a8ecba1797a5102e0e80459092d22492a3b2e85e5e944078ca0116424ca1443a5102e0d01e3027a0116424b04c4800b83e5f940060180985e3216824d65c3102826e5202e0e01e3216824b614311219765202e0e01e3216824b0cc450ef00e5f94e0c13e301821709318076d850459765202e0da785a092f8ce5c61e5069e0c1c2170927971a7830731601885c24810f83e5c611a4c2e301c217092812014a7e5c8be5102e0e01e308045a09358ca0c1b018020041a1c0a098310bc1ac5b97e538301f8c07e80013093f97e5383e3007a008501309258502b9765202e0e01e3216824a10f83e5c60208c2e3008c1496c24b288a4e5f941838c0230525b092b9701b9420b8328408c1496c24ae0f97e506020808e3096c24903c1608b971938381b8c12408a5a94c24d03c22e5c06e5062e0c011180902296a3309380f05c2305031088030840a0982f06b8c07e8001e96013094c0f08c2208797e538305848000390dc600428001408c252058314880a0983f0f8390f7092b8300f97e502129c8b2081ae30962030934012870529f9722f9420b8320096c24ce0f97e50a722c8206b8c2009628442878c29f9722f9420b830f48025b09340009f836300a018010fb0524090002702c380040a0983f0f839658c2b02c28705e5f9420b83c0096224b014386000a0982f0681304a96298c0580211040183970182f007052c0503b9701b94e0c01a31802405a3044e5f83100060059624220f41629f9722f94e0d01e308081509342d09c0b0e383e5f94004130fb8c814c03c230105f00397e5082e0d01e32052590938020045f0483306008e5f94e0f8c814c01409e0f97e503e0040ee3180280121c3d17f97e5082e0f8c258a10c2be520160827e320565a092b8c631806520106da78160965ca0a5a7e5e0100b8c602058249a5a834078c14ea741509a5c9a58434078c0a92741509a509e0f97e50010ed051140ee3013a00bc5c3102826e5082e0c81e3096224b23ca3e330ce5f94e0c8220496c00893005a503614f97e0c42e31962405a5045e5f832183614c0b359892e9648d4bb9a8949f97a0e8c40282414ce539765a2782d8303b8c80205283d6580402227e5e0be53836320)))) else (if j<18 then (if j<15 then (if j<13 then 0x41ba0105426972b8ca339414c2a40505a59092433e0da7e5d8be500180605e3180824ce328ce5f8302c530490141696424b43d230e007e328ce5f94e0c1340505a010939a50cd83e339404daa806056020965cc1142de328ce5f8304901416964269431cb0cf8ce5f8304e0181580825942c3365daae3397e5013806056020960cc4852ca9696e538304e8041509a5cb0b5960c430653838078c8160965cb65c316581f66f97e5201e32058258331d865982e51838078c8160965cae5294a0c9b01e80aab834078c41509a5cda0e8c1550114d05a5909a5c90c41fe3397e538304a0181596824b6019604594e0c3869e05825972a8ba001be5f8c4040241696426942c5642ea4a03974078c1541241696426833696157834078c02e8041509a5ca1799607c2de53838078c8160965cb0b430e0f97e5001805828178c65a0931214b2a4a0397e501241696426832c5d6581f0b797e0e01e3205825942ecb1511be5d01e3013a0105426942d9460c57600076ab838078c8160965cc03c230c422e5f9407f83e300740505a5909383360038651aae0e01e3205825972c59600070cf97e5201e3205825832dd8601a7e51838078c8160965caa902de328ce5f940490141696426833013e5101e301b00905a5909242ce5294a0e9b48680aab8304905a5909a5ce0cc576018be5d838078c81609650b046cba5b97e0c13a010542694290f01c33a88a4a0397e5101e310542683368c1550114d05a5909a5086000762f97e0e01e32058259429db0cd8069d9480b838078c85a0965cce3397e538380a0185980824962da700b83e5f940060180a16e3180824d72c3368f8ce5f8380a018598082594308f26c82e0c968660b0830524221c79711842a582001b05240f08853e5c37e0e9610820c14a1578381b8c14ca71ac20a24903f8c26e060988213820a24908b97e0e0614c0b95b1408289280f014221a79709b8381b8c0830507289370cc53832088114f052588924a40930bc0397c538c28881c1496224c0470bc0397c538328482c1496224b0e397c5082e0c81e3096224922ca7e0f97e5001406824178ca590930221c79712442a581e01b05240f0880505800122420df0ce5f94e0e8006a9607b05442201b941c38329c1ec1401a24a03f9701b941488207b0500689280f08b9701b94e0e8007801a24a03c22e5c69e0c1ca580607a89289be5c6de5081e302dc1489242114f940ab831b38c1ac2da24a08e2a024211ab97e5052e304e0b689319702794004470f8530a81a0f3052c096538ce5f830d85302c860f3052c0f08c3008821e5c61e5069e0c050b700072893c050c696028260bc1a04818a24a03c1708c3102826e5082e0c81e330025889380bc1453e5c82e0c81e3300258892f0bc039720b832078c25889c50a86f8381b8c14d27126961af09 else (if j<14 then 0x4625c80079830161128a01208f20f9720a1107a011e83652162aca723d061f9426ca7c070960f0523cc32483e508229f0923cc31d94a0caa814a7445011cae0b80ce50a720889c248f014c32c2445e9700d0ba001650d01814a40297650132aa05445012097e50aac24ab354a91d802090584601161660c9b0489641611804865c9b4161120a0119832098065c12844968048e0c8009d970148f8460123940078c00082224052a4a260ca65e2760d8c2460542d9680289289660f9404b0930cab29d96258320d97a5d94a5196a5989a241f4aa423516a0e97a00124449b659012716418ab29e05404660e836328c2588911c36208c65183a0d96a5847218865e97652946328c65a9607d832252a3197a5d83a0d8ca3196a581f650892e83a5e80a5911815011d94a5183a0d8ca3196a581f65c892d9420296444aa29e05404865e94909803561981a112097c5c942088101627244845e4c40909a25228162782c900f9742d16a590150c740194e5c13a58aa445804049c01092a50681482404725c94208812a4911b97a02964460540460e917031024268982e054a4930f9765142a591941911219725d94a5183a0d96a5989a241f908c1bc6807c816506e1917a5d14a520b40909a2522a322704cc230822a48611058259760d8c6581f14c0b060a22597e538ca24822a4707897800822a405818a2804913b974650b45a9648c098aa05282d06d2345294a0d0ca3080a5d0111caa048a7a5909415225f8c25802a24a90d87159170528c4080990a054a60b2a060fa010c970f80606844529440e832090ca3100a029701d0941496399482d832a58c8152765a00a24a20f9720806068565d9482c22632051a600a252a2b94c5b09508ab29e051d8ce5f83000960708901491284a25897250a220c69230301b481048890b4d0788320300858ab0148f81a01281e25f172030085805818a2804a65e276520b03583208016320501e00a24d0789720c058181a8047a2ea7e0f97e5001404824178ca010931d86019688582e518369e05825972c3107d22e328ce5f94e0c1240505a5909378ca3394155010a905a5909a0ca65d8b6001160d968859b60a0582594312207c2da3ca5a5b94e0d01e310542697341f0b6a332e96e5f834078c41509a50c0468ba0397e0d2104905a5909a50b0b683e328ce538304a9b40505a5909a5cd0b29748682a5aaae5f9404e8041509a0cd1729714c55a8a96aab974078c02e8041509a0cf01e8ba0397e0d01e310542694292c0b03848680e5f9404f8304905a5909369707e82a8a962ab97e5101e3105426833443b2e960ab834078c09e8041509a50c08521e52a7e5e8241783a0296424b7682d6599be5d838078c81609650b08ca7e5f940cc21404824178c20096424d0e007e3397e538304e0181580824be328ce501340 else 0xf601010a60d94a5083e5c8c602800f491601784594850036020065a1680509414d14ca765c82c2705192724501a50054720b62480d82de5d8ca50866592a82c90d82d4712765d836329421a0b283614c918469482d966248031032a683e512745a9643d09a26423000208812a491140c45f9404d02426894a6422400c5d94c0f1604d27244812496c5d02c0d16048912048a3027a5c82a0d02e509604a890f842814d22717c0f1624481183e0688681481160b864a9a0d2965f94a5b16a25272c400f797e5183e320001182814a65d9460c00658080108181490cc2c48882086ac25927e5f94e0c0da310042c18a2505483316c0f26d8001c96653838078c0e1a7826053c2c45c27a5d14a500c401020250b48983414e2a4910008220705014765d94631800cc0720a098149760580a00f88d802588265f9460e01e31a782605412509514a51032a6830310045a960250f65d0b41500cc5a0a0236320c602002589b6520120a09814f0206665e1765214100226588989e0b205836320060a054828e5f9401f838078c60209814a0cd174510c258524002849c1820a89414d230a946481c9c82c14703c330962326c076949665f94e0e01e301360209815108c3312e0f20a2201dcb25b97653838078c04d8082605494b12c03e5d1940116a580949d236510534330a997652238518c8302826c966a9838048204d80826054c40e5f94e0c04e320065a052514a5003e5d0ca30814003d01105224ce5d14e5383c31090070507c0729050dc48909010fb0c1c1e20f942aca785812227090148f908c07897e50132a4822270901642288b417976538304d11049012037c5d8304f942ab0910882240065283e5ca78151104d01244865c12e50aac24a7908805a9720b838151104901239710b83e50139081241701c243e2ca50948300b030339420096227090148f22ce2902425c27c5c0ce508025889c240522ca2381c25c9420c8b069011c1e20f0380096c580523e06804a458ab29c8f81a01188306ca32321101ca7c2705014a07880c00a225b1623c0581a012997402092a48228a068048c02092a48228a06804725f00c58ab018a91a09601964161180468258365905846011a0965d9660d05846011e0960d8065d05846011e0965d804161180468259760d05846011a090f18084601150fe5d23e5122e0c3e06801248029c8b20844142025c83231002042642f05250010e894650b148f25f1720f032330cc5026203002088141496225020c432089922f09c14720c960780523e118047e5c96009830161128a012097288a7e0e1107a011cb40d39429c822270923c05908ae50aa20b01c2597c1642288925f9429c82c24a2908725f9426f092ac422a47a519629d05846011a942a996414a7846011d97a50a7659838441320201258026d058448280)) else (if j<16 then 0x7c2705181c45e27a5d03a0d0b800164652302605342d25f1720e02c0c008581220405244a13497c5c94c5083c0c8cc3216402890152742c133c8965f148070c2a609208a249d0b2c4326ca7c2583c146224090b697a5283a300d204182b83e3096224470d8648e8306d11650ab29f09c14945c4340d0c2450ba5816a2492b02c25f1720c02c0c0025889014912858c3897c5c94c5083c0c8cc301f20881258890152742d00448f28f97e5082e0c81e3300258892d17426894a642a510281480983614c4281450980b0d85321a056247a5197631966260b0d87a519760d8c6598982c36212790a94015966251c82c80d82d65c9163211a512a6260b2905e5f94e0f8c060121c94e0c961a28911c911c2c4529440ca9a0d2745a9643c0990a05342d00082204052a4911c2c45d14a501f4080990a054a4a2271740b03458392049120972531423201c30a920804825830162782ca23d17a5d0ca339445a960260b48a2704cc25f1725083c0c96c581f206096300589c91284f45e0965183631962242702c1329148259760d8c6588909c0b04ca82597653146319660c8909c0b04cb65f176531460f0365b16204898258c09c0b04cf65e97c5d94a531460e83c0d8ca330c259162260909c0b04d3e0f8c6583307089024470d90529058259460d8c6581f09c53060a0b6058259765183632010480d0a8894142714cf4142702c811843c0b4722605e0f8c65a8911c3604c9224338242702c81804450f0982783e3196414470d818202d65d964142a21866e99760d9602c814145365090b583658274159721878159460d8c6588914c1321056518365847218181c2d8160965d8c219962240b4142a650c7620582594632016588909d0514cb81597631962242a0d813210582597631960a836060856e0902c270e058159760d8c6588914d9404c92245302e06098522594e0d96184472181320286039765383e300762e09814a2250203491207051917a5d14a5103a0c0045a96204044148935830a18065f94e0f8c01da7826052f97e5383e310001c044148154ab26e83c2705194b12d1709e9740e83400000591902523651053c97244838080001c81c14845e974529429c8b4328c45a96a0c1f42505200f45e974529440e834328c05881011004148938834af972081ac1464b02c45e974440045a96a0d2142505630d45c2740d0c2452340296a2505650b2502a4448b2a482c2705209724483008a1c009622705630aa519760d8c6598982c3620970a88c4448b20b0902705014a170aa20b0965f051b97e0c8b02d8c0f46a5f832308009c990f476529420d80a004026c765083e5d8ca3180a01060f490746320840109410c8c29c82c2409c14052697e508009c96100821ca9e5c8c2588b264821c08024a701499208625c8b2649b10976529460e836028 else (if j<17 then 0x16162125808460120985884609117a5c0342e800594340523416853083c508229cc323f051f1429cc326f0523c645283858ab29d1923f05444925f1426c42c14ab2a47c50a765c82908a2c14765c9b8460161621208749c0682c09a52060f070104565e94632064a98582c945e974529440e834328c0008201d0142505258f00f974310b4643d0607025972a7948052742f8c208a2c14b02714804a9e303c0f47258821483d1094453976328c42c010f418250345a564168543e011d174092995905a152280489583c0f4345c97a52838028c0f4182194a5183a0d8ca3196a581f215272d97a5d83a0d8ca3196a581f2150b2d8365e976529420d8ca3196a581f060c0ec9b14c15112c0b117a5d03a0c00059114858c42505349623f97e50a2e0c3e0cc450ec130f018c24850f5063027e5c420f80006906a1501299789d94109830f20041a85404a65c2a6520b0898c806090c8138001860e85010f45e974529440e834328c07d01058a722c80425054394e3000208092a4a260c852597a5d9460e8365a9607d06215012d9410d8c806090f12aa1404242a208aa09983c27051d94a5c94a0e8ca590b0d8182597a5283a329649c471c9642783e319611c3604c849e9742e94a0d01a31090f1962997a5d94a5183a0d8ca309607c85060043683a58474198c04c665c4342d8363006825060f200a1404321665d836310914d9404c8e0f8c258164240911c3604c965e97c5d94a5183a0c96405098242702d8c04cf8259760d8c2590909d9404c945103a0f9705a278251104c911903a0e0005a064168543e01289414c0222d1109b09c148a5197251836319682c36060907c3ba5d8c0a906a1501202445e974501f05a2a4450141685484c09117a5d0c42d1905a2a8243d4168548cd0eca48a845054525f97e538ca5885048a207c0428a2192062505302c151c3ba5e836302a41a8509d01241b05d14a0c168aa0944505a1627484c23f9728f9428b83004090f80e2a9465c946319682c36060895a97a52832468c14c0b0f03d824b45e8c4a65640905a160b48a092a170183e0e9723d0b2a4090383c1e97651836322711c181c0765c5306caac27051e0965c0b60d8c25853650132694a0c01a302714c3c0f609250960d8c11c3604c665c2a4188261456e99760e022585302d01614960e022590609d85199460c9611d0604c665383424474181318db56e0909c0b0e06a5d9460d966162700447202d8160965d8363012034862250514c0b341f0b6058259702d942058c80412034890f1050a90224860f830b59460d8c0043c09c530608928d665d9460d8c4443c14c0b060892d2c0b11140e8340280a5c16485094158c342d22409653972043ce302a060a0f0813581811836319611c364146e0f8ca5a8911c361b97e5383e3300c1407010810c8260ca else 0x52d9760e026021641a851c8023c3028c6d07f97e5069e0c61e301cc24853d838098c806098580a09a8525830241a46e85149410c8306c8c29cab01f09027052f97e0f8c058096145107c8b2583e5c890700528a1982c809117a5c0343091a310ba001650d2365109414f09117a5d11a5003402800592142505630d0882d0912322c1fa9080e5f94a0d01e30aa04a9642505483312e0f08c1f68dcb2179765202e0e01e318085a094797e5202e0e01e318085a0924230cc5b6003176c8565d9480b838078c69e16825010d80e5d9480b838078c62e16824b16c2380e0283080826050c4a72924090144a50ca3000405160590902505a152260d04a59729c99c58a3c24745e974529400d0ca3100a000742505258d20d292321129c1628c85c249156222a997c27051b97e5383e301f01d09414829c8b00801e5c13e5202e0e01e321620185824fe0f8c858470da09614745e9740e834328c058094168522c1f200d65f94e3082008182881f010965e9742c836328c65a9607c182a8381a2aa50151497a5183a0d96a5a066168549e012d97a5d94a508365a9607c18804a1621400d96859098452761605884b3ca9701815103a45c14801024a50580685488a3c806054305d148a916a5a0944505a1627484b45e4c40a0989d05a160b488945e974522745a96a0d1140413484b45e944a64c40a274168548a01800b6518365a014259702e8c04c965d94a519660c2702e01a3013299789d9482d8c806098002fa14042c850cc8fe5f94e0c1f0f8452083c0f4c630272643e4040e199789d94265830f29640482500b20c0223c8c2019725b09c14b60f94e3000258092a4850cca2299789d8363006825060f29642ca6520b60ca9632018243ca592729836599781a8c04c6e5f94e0f8c0629607c04228311d06630131597a5d94a5183a0c9640418010a65e97652946328c07c9620818010b65e9742d83a0d8ca310625818010b65c976529460e836328c25818010b7628c65a0609d85804765d960aa06a3013189709c83008a32311120096c27052ca3250832848c20a272586b24a3250a12322b89c6b214865397e300929e022142d28e222897250a12304e0258529c8b808aa5c808a602405858887a5e293310929e026162222c965e944a4cc29d02a15228048029174450348680a59094158c249709c9402ca22848c2009660f09c14c65e8c2648b46ca3c1529824965e8c4a65640a854888b824946c9922ca3c15028247e31942000b0262928e02214928c942848c8a44e80885202c2531429c820264223c85c14a288a10542702c381897c5300c5b052aca900482a656208a2c160119972a656208a2c16011c80288969588f2170580488519790980355858661122562aca723f05804660c8260197844392587c5082908aac14a21a0960c9b034968460))) else (if j<21 then (if j<19 then 0x402564168548a011d03402564ad05a150f80480728380d27653976300661602004b0101ca0e032ab9763006616022a832ad27006026001d1e8365d94e3202060281c970a89482c8c07c822a709c14a8250980400028260fe850f4965c53004090f00a4aa85219414c060243c8cd0b09a8525976518c001850708201c8e5f9401f83e320089e0b80585824b09117a5c0343091a31000592742505a1523382445e974469400d00059274258c41685484e45e97452944328c000094168520807320089e0b8041d141de0f8c8019689e0b80609242465d940898c8022782c398040d2e94e5f8322c0b0485128c07010aa5e9420f832338c200272145101c0430976529460e836028046c12804a20d97a5d94a5180a0185a1502804b25c992a8a3c145070a780016264092aca3217052b97e0c8ce32802145128c07010a2141c20044074a722c5f209980844a0101149709c83200992141c28c8028260bc1a07c0761404c249e5f94e0f8c6141f01c04203a45e9705100a021641601a15222dba0e99783e176501460e2280c8045901616053c67652238518388a0340516424a761605379765394e0d851410107c07010a16e038308029c8b814382397e0d8ce31851448b07c07010ae5f94e0f8c04a8001c04218c65e976529460e832308004807010c65197a5c9460e836328c2001201c04306665e0f85d9488e14404804250261605348f25c83208968660b0808402972aa898151942c726e89814824650b189710c8c4448b20b0902705014a09d2214c1010826182025e162a489c240528a4282ca20caa20842098560f9725802c500528a1982c923c97288838660b080725043230a720b0902705014982597a32432243c4161982c940397a58aa8151942c765f0cc51002a48228a0642c926e052091942c52270cc53002a43c208a28189c5c8bc0f0c801940043d0609290242a7172330cc5080c00962240528983204f08d032a59743211c510005a8949cbc8c06c5026c0206270760c83070ab4ac18e5f0cc5300208063297a0d8c226054650b060805a97a0c828151942c12210029e97a0e054650b1f976303c0611942c891c202a7172330cc5080c00820600528a063505e5f83630184650b04880710005919025234ae0549c9e5f14e0d0ce310002f0501c04298320c1cc53970070c0612a208a080972330cc50822a40528a0682cb45e9705103a0c824328c4028001d094149639224841514c0b09860809720c8c42c0581826208340e94e5e8cc300140818259465e9725183a0d8ca3180a00122d97a5d94a5183a0d8001280215012d97a5d94a5183a0d8ca30802141201c04342702d02809018045f600860e97a528ca01020a0710f97e0c8b02c162640928d94214b65c4308d838098c0186d825068581865285389710c838088c4448b01f090270 else (if j<20 then 0x4850c8068c07c162a8398243d815425b9418ca9038821927098068148b169705d14a5103a0d0ca3201402802580d060e02714c31162aca70f48f25e01034bc5f036309922c3c4247258434089922c39c24745c83c0c8c20300014990f494a70365e8cc588b266092129e5d0ca320140280a511606102824c43d17a5d2240c82a0d0ca329409900a009604818819145e9705103a0d0ca303d0120522e09308049f17c0f162648bc248a0c8ba510be5c01a3013a583f2aa053129e5d0ca3294402804581881902c24c45e9740e834328c80500a02942580d060d024834a70365c8025b16264a7c24b07294a0e970068c02a800489b814bc5f0322c3d2640d824742c0a2aa0529c525043c508cc30a7016012089c530c2ad0129c3c42472a7172308b01499208700f974310b0f4184647a0d14a5003e5d0ca32012003d060b0511740d0c458268188bc24902714c3300060a9404822117a5d14a5103a0d0ca301629c8b2030904ce2580e0e43d1114a50a740e834328c45a9607d09414803496c530cc00a920862019742f14c310004ca9208948d1422e94a0f974850c8068c04d16a583f824182a914469400f974028045a96404920c2702c3f208525e0b2a8a70e4500f9743116a5a090610b50d1928174529440e834328c0f404814a72c9489c3f22d060e4641439e5f94e0f8c04c1221c9e5f94e0c801009618a50949402f1420c02c0c8cc30092000523c963ccb12c9709f1720c02c0c09200052649634a40909709f172500bc508cc300920005288963c2505d1140e8300116a592142505630c45d1140c210f2801897c5c94c5083c0c8cc30042000540496424e29c8b20844e308025b09209410f142330c024a720880729720a8340a8ca5026a009604806814d2a7170248b26482184b4a50ca3000819028580482505a1522369445e97050a740e834328c85a0941413344c45e97a500c0020685905a1522804c4529440e83e5e1680609a310504cb05d14a5103a0d0ca321629d05060043083c0c8c203000588f26418010ac0d97a311b2648b824a3c1494a50ca320140280a5102061222917a5c1440e834328c8588b82505060043409c5f03c3180c03050343d24034321b4650b4168548e02824a00d14a53972021680b8c41418010b86f976318065216808010609a0d9763180062020a07a0d97651806160200428202d43d17a5d2240e834328c200364041222e9642505449745f14c0f0c800010f4182409c5f14c0f0cc140d0f4825f172531420f032330c2008504807010d45e974529440e834328c8051682505060043917a5d14a510ca300080502060042c97c5c83c0c8c8001626418010a03d172531420f032330c8001680418010d6ea8380e2be5d8000585808920d03a5397a010200418200c45e974529440e832021680505060043517 else 0x8c600010603d281c022058580660e026009600505630c40d94c53976330c603002580106082308c4321665d9460d80004180f4a85997a5d94a5183a0d8ca3080414010603d381c020404149615058599460d801001221c825a0565183600400603d21050121665d838098c60006048872c968159760d8c600060603d241c010088161660d9726d8c651800e0122590501904159765180100122087e5397600372584006082221665d8363180650010603d25d86520b6319629d051c96815976518360001630180f4a0219789d8c6588b4144501898019765183414010603d220565d9460c80630180f4802194465830059629d050ed8c29ba8160065e2760c806580141445630c414048599765183809800041221cb022058019789c0620196005050ed8c30a56500b29d836319604c829ccc04c3800060043e03850700826d8c601050188220cc65c276511960d8c6580104c802d234459429cab23f09c14880397e5383414400603d220029c8b0240e0f1961dd86518c6010520868159765183200400603d210529c8b04c09038086588021976520b60d8c2a839414a7280865e2760d8c0e5051148b018a0220065c8b6520b0f401630132a839414d2a8800019729c8b633946598304cba3194e5d8003a011007a319460d8003a01100725cae09143c530c2a8ab2a4911903a0c168192781601228c8312b26619e5f946030065a012c99865834a597e518065b16826012c1e4581a018446586078060fa05104645d038180e816011d1740c1a4028025a06a308e5f94e0e80a584003472584360d162aca70e70920834a48c844a728c96c2409c14052d0f48c02484160dd050e40d24082520bc50832330c2ae16024a70480523c0d3c0825e27c5c8380b038580922c1201499034e45d030fa06a305020972520bc508cc32002a40904c05208d03100a01168252981a0540983280c45a968192b49e0565c804117a5d03a0c0005911406052943c5197c32092a89b1c2f26e052084e5f94e0f8cc270507c072117a5d14a5103a0d0ca3116a581f424a722ce45e9740e8300116a59014449e5f94200631008218ae0b89410f142330c024a7014822d14a510c8068c00116824184a5022c972520bc508cc3200024132a4822c082a7170248b01499208825e27c5c83c0c96c580922c99289482f1420d29c0c8cc3096c580929cc09117a5c034301650e090f50b815193040a320c26619e52016019624407628c830998679460196804a0228c8319760c0e81a012008a320c65c998640ee5180804a0228c8300e81983e518065e01282445e974469400d00a0016406052c99020058040e6586a31976518360201100710008a320c65e06e519660e0128400228c8320660f9465a01268c2650b28405600441e8c65d9460c0e804401c2209117a5d234508ba5283)) else (if j<22 then 0x422e9448903a0d2143201a30800583904e090603d5e97a5283a329604e0529c8b200a05117a5d03a0d0ca3116a581f8260522cd65d9460d8c6000d0f5092589c5f14c0f0c4043c424712d29e5d0ca30008191601209815023033424090359460d8c405800f4a424398599760e026318003487282505d1140e8300116a5901826052d29c0d97c58a72646559970358363101601944243d285f1999783e1765223851016020042482414e020834a70325b16024a7014992b97e0c8ca00990f4605d14a5103a0d0ca3116a581f8260529cd1483d42482112c65d9460d01285800f486e83a65e0f85d940518388a036020025901414f021970f5832098c6000604896289b0f59460c826318065c12258a40e00653976330c200010603d281c0220585997651838098c04c0625905004e0700865d9460d8c04c9b41482290c8019765183200010603d241c010088161665c8260e026301304896414063f97e53830078c805050f404824a07004022058599460c016301326c12259053905814820dd801105f1f97e538320000101050f481601784594850036020065a16886098168c3a0065183414400603d1c8081597e5383a00400603d2482809801106117c1c1e16e5f94e0d804144004887259722d8363105018180f480700865d94600014158c208920205e5f836338ca00060603d29ba8161665d8380980258014158c2c8b200a701838160065d94414400603d1e0565397200400603d1c968159765183100180f480259742f14c31002a601208900d14a53974328c4028001205208b2010bc530cc58ab29f0920174510c4580a2a8a7c2484469440e83a5d00a0116a59012809c530cc00a90f601208825d43c530c2ab002ac0126c940d1695927816011b974011695a05805021d1740c3d95a05804645d030110095a05804729197650824898c60012258925f1720f0323200014990f6092897253142330c012002a58301601208c45e97452940020145b8c81418409833117a5d14a5103a0d0ca3116a581f29c8b41609201045e974529440e834328c002012580d06004383d804390360915976518360040414961c0865d9460d8c0f48204896259745d94c5183c0d8cc3080800010603d34081199760c02e518000412258a65f1722d83c0d8cc308080194814010603d3894c5083c0c8cc32000148f8043d2c0865d9460d8c29c8b20013259765183101050f4625043c50832330c858ab29d970148f8040d3914a5103a0d0ca3100a001643e0106197349710f1720e02c0c8c8588b650052640d824e45e9740e8343100a001682519061943097c5c94c508cc3080c000401601208c25f172531420f032330c40216016010600d824f05917a5d14a5103a0d0ca30808043d060043917a5d14a5103a0d0ca3100012808048241609259025d178599460d else (if j<23 then 0xc1f60a09814c65c976529460e83200400f4965197a5d83a0d8ca30804183d29d81619488e1411c226320c2018380596858a78260545836529420f976328c2003d279765394e0d961a10107c826e8320a974205e5f832308002e960109903496504360ca9121978160903a96285a65e0f85d8300d8c8310665a164248b414e76058652238518300d8c8860c65a16424a7414f4a597264a7c27051997e5f9460f8c6580207c863197a5d94a5183a0c8c2003d285b80e0c858314248b29d052797653836338c0f41f1c4ca5397030008191681601408a0208380b038580929c1201499034b65f94e0f8c6584a07c765c8260e024058c245116518085839426090f0f17d0f45e9748d14a512240c82a0d2143201a301f0009604a09061525b97e0c8b2643d1897c5c94c5083c0c8cc3080c000425901424e45e9740e8340280059014458c284943d17a5d2240e834328c05a060e6098148b3f97653836338c6000402c882f14c30aa65f0520870591710e9740e83432090611942e96650d0249710f1720e02c0e160489922d94c24d6310ca5e2726519a0f94a59012880402168259729d276508b42c8260e024058c804394243c4e0bc50a94a70365e01c3316824a72c2317c5b60e0365c9b6320c41994600318000725804425054f97e538363180010651c5f19d9705d0660e2280d808009640505341c01009a5e9420a8340801a301325812814e65294e5d80a00961008220960f20965d83630916003d24b40d09482f142330c024a7014822e27c5f0324511c3194c5a0922ca65e976529460e8360004a0096404b035090f90121c5259018259765183631800f490a917a5d1100116a5a834060528330210660e0260096404865e976529460e836328c2003d2833022168258365c9b63106651800343d424e6e99760e026009640470209789f170248b0149920890cc0865d946010120872583c8259765183632010f492530c2a48b418821a0920837406010158017c825e0bc530c29c8218330221682597209838098c4180d0f5093480a5f94e32802a4821c3302197651838098c41896404a09e9702e9420863a0d018068c01d0542580383365d9460d8c035010f509242d1699783e170d82200d8c830808059622d82826054797e53830138c600625f172531420f032330c201010f4b09c0b208634046517d80202317c4b65e0f85d942098388a036320c07c00418072580442505570c650abc588b29c8f418825f97e528025840208717c4c65e0f85d9460e2280d8c0301f00106259054051a5f94e0e801003d18962883729c8b200440200d2482404390f109258610f9400b83e300929c0523d97258b45e97050a740e834328c45a9607d094148038991110181609a0062ad9408b9763201816090dc965d9460d8c6000d0f509203c43d1729e9748d1 else 0xcc5321b25e0f6528343216404a26d1b25d83804a718830a84c65e9440e0c07e01408a25c1b1191760e010360949c920c2a13197a51228300004e01288c265014243e110606e9705d2345294a0d214328c058aa0e609814a7409702f14c30ab26c609f9702f94e30092000560c8229ba0e99783e176501460e2280c8065a16405053c43e5c02e0c0922c0565099258a06d1140e8340280a5c1640605286665e0f85d8300d062019685901414ce5f94e0f8c6581f188310f14c30a7208665c4308d8363006602050f60941a963043c530c29c8f26c645e974529440e8303116a581f816013283c3194858ab29c8f418825b942aca70383d1a97e5083e0c8009e961000d259425197a5d83a0d8ca3180a003d011063517a5d14a50a722d0ca3116a5a8382413349423080020a90240528983258a19d9488e1460e2280d0165a16424a7414d65c976529460e836328c602800f404319729c3d6508b009834058c8041f81609a58e12c144a50ca300040502a59224250560cd29f9722f94e0d01e301f0f19629976509960d016020582696249402cab23096020092000523ca2008f120a3e5f9420b831838c04c08c1496389709c8325808024800149924052581f09c0b209020e48e0f8c11c3665a09814725e8c0448b26cabc24708c8c844a72088fc2409c1405283a053974028045a0181502259460d8c6582d07ca7826052412208448149614a722c130fa05602961d9760d8c6582d07c8b82605245b80c8b830808583129e09814a20d2bc5c8b26482199711c36e5f94e31966)))))
def mo255H10 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xc80007200800000004993c96100003414f803000000004c52f12441383d62000028a864ee85e2e890f1da0888518839fe20eb0000000000000000617590a9f9fb610865795c1f0db9fc488862811330238000000059168000716f489c0000350e80005056855b0000290bfc8d901b998bf8c4d0620000595f9198e051610909fc00002020f8f4b1f8f0f605c1389ad97921e15816000019c0000000001067800000001920500988c535b3a978dd5600004d9f18afb9bf1925983d39a91495393d709328ff518ce0f3a97f505264026de380007c9135b1e928380eb1f9f9a08000000031a30000485560baf9fa9dbc684b090c696d00000000000030d000000000484f301c594139a2716379d180b880000db4f092804889693419d99980003d60411e914195df9972bdbf01c83431a2060000000000003118c05ef8e429f1d945000000000c1ee1d27c1c90fe8000000000003968000000000077a0b68029c939c8f9dc42cc233d7ec0dc799dd0cc8000398ef959000028abc9cdf590a9b5000049b18000185a800059a389a4800039cbc022a036592680300202400818006000010080040000000100000001000008000000020000040180200201c0780600a0040200600401c0000202600803804002010000060040200180200e0040000000a000008000060000000000a004038050080040580300a0000080d000000058000000080200100c0600000a0040000300300c00c0000100006c0280000000c0080100200403803010008008020020000400100c0880080000000c010050020040000002000c0400100000c00801000064030000000000000000602403801000028000010080000280100c0680301c004008000010080000000c00000c0003201000401003002010068010040040100000000001001000000000040280280001100001000803008008000000040080080201e0000080001001c0000e000004000000000000000700c0000500003a04800800004008020110320000c0000140000400400400800003038024000000100000080001a000020040000140000000003000001004004010070080040100001204002006006000010000020080580c0040000100103c02804001000030068100580040100b002000020000000040180000c00400000008000008070000480080001001c0000000a000010000000000200c00000007800008008000010000a80000400a0140280300e00005002000034000190000040280001601000000000000028000040340080500e04c030050000000200800801c0883a01000405805008004050010000080000000a000000000140140100200e0240100200e0000400600a00000004000004000000000080300a00402c0500002a000000000000040080400005c02000010004070060000080000a else 0x6800000005543d93508c885e7d40fb86f21e1a83be9326dcd888ae0a0798574e43892312ef8c2792c4082c924d179881fa9e04c81e4d300006c948000000078e87d12c59fe855f8d08187e818d91a797b0a0000d9c8db59fe90f81545a88c48a5620211e9682895df08ca64576943b9e66066a849eda12929d0c5dd3a8000000079ed7110000049f6800065f4800011bd48e6b9cc89d4d04e580f0000000000004838404b800058d880000000000000000000096cb06e00d5000000000000106b800011c4b02480003971ec8049ab4ca6d1d9318b20aeb98f4192ec188565390391448000000028fe0000000055b400000000000000004902000078e23854a1567094a936000061658000000001115997a84d80007cf7e108a07cc1b25045081750013d0b2064815b0000582000003958000000000000698c29a28000542c000000000000000000000000055b8000601d00001139000011a78000000028868000000038810000000035bd0563f831e1160000699f00000000000071924191316c61060000000040b7800029d140dab0f780006df8e89000007c7ec82fc9ff01d6794319828000412af9170000000078480000000065e68000699bf8418000713c00000000000000000000000000006c2e0000000039f60000282a486a51b5e5c3d1ec8000411d68cbf801f07290b4d89e8d370000214680001cef319eb5f1481059e98000094a10069d7d8012d0b128d58a03993a847f80bf7082218e682138e00000000000f100004511c5e719c6a13b41c3e060b1b965d428d4418580004804311b800000000000119a811ad15d91628000290778218870b0cd983098420000456145fa80000000000018b3300250d8201100007c58206580000000000010a2113d800045be800050af59bde180693fc0a5914b70beb8e568e5e893d0c9c1db0891d0ace8fd000000006dd5d184a07151c8800000001063d0da45ea8000519049b7a13889f54df6a040189b8000000000000000000000006110d50e000075b81c4300000000585d8000000000002906f48cf00c3565e84a80002027c42444e24c564c219995c85b91bb01c93db000006181a0680000582ce0a1916518f6d105d00508bbd8f331d7f0fb4899412d44acc16448c0a8b9c90a3967c889a54e78ca887af17d8061280600bc71a18dc4a122000000001161b40df15d000068bd7a044887000059895084712d800034e700005c8681af80007104192b7d6300000000483c0000000049cc0000000000000000711b2d698000484469fcfd13288c8000000068b3d05ff01a000011dc4404800000004599591840dea57c00002d15800041f01995000021b021be142b800010a348c709f4000001e7000050e78000000011f5800051d000000000000010bd80002041489995cbf0ea7da78000000020e) else (if j<3 then 0x201f68ed800078ab000060340000000000000000000030c00000217809b398b92493f8310000000075f2800060ac25c18000000000001973800000006c8d2c0809cf8000700f8000514bc9128000415a0032000061cd41f7000000000000000029508000702e800024902db2291de03ec8f749c54033e8c2800001b100000000000068ce7d58a07698a90000048445abfd51c86709a02d53800000000000183580000000000014270000000059c18000000031f1000000004113800000004900250f2d9769d6a9e8b0e38000410295120000000041ac80000c8480007838f029407f004300002de8183b10f180df41ea61bef1d3000000000000000004e4f5e4387b1483d100800000004142f0774cf7405028ad0000308d00000000000000000000000000003d508000000029dda8378000642861734454000034497901c1e2a4a9000054808042800010b18081e93c9183000065efa91e41dac06c90d10000000051b631475037440965f9a9aa19d86075ed7f000000000000293328eb9d660000795559b6d14051a50000184ff80de87830ddb5f85955f5800000319d486e8000387b90c130ed308900007125000050ae0000784c887f800038f0d06b2c51800001a17190c15700001c90f9889dd08158e9d5ac2f8000110359524c93000060b2906ae89f28a0acfa8c9680000000113400000543312c800000003516189e00000000309a0000000000001183e076004a709400000de8800000000000112600000000540d1d5e8000000000000d53409d80000000000049ec517780006058f8be0000285b50a8e0ba54863949097ce9fd000000000000000028a71c208000208d80004112153b0000241b098a0804800038fb800061fba9f9403db0f96808a1d5000040e4800009228140f0ee00000d968000000035eea9e831fdf945c1af00000000000044155160312709de800040ce80000000695cc9e20000786991c70000418a80000caa305708860133d9f3000000000000450000000000000011a7447f195480fc0000000031d38000000021c10120ec3211adc4e1990f8000582c00000000000024201157c8d3c43da8f89c228000017a34e3f02dd583408e3c598000010780000000000019a5f00930465d61bde2397e8000000014a180000000090a80000000003f80000000696b80007db8c87e990499b080000000582b8000093f000058cd70bb403cf1d2c896c8f43ddcd0965888a83280004ca1000049d709743dfa61d880dc94763885948f91d4000019bc911f60f520119d0f800000000000348e1136dc66fdb7800000000000291998e1193e80000000000000000000000000003cd20000000000000000781d80000000000048c38000214c145889b81568699e000000c7802f60f2a0d2b01991cb248b481c8000094ca976595e503 else (if j<4 then 0x928185996759a71eb74e930b21c1d29f4e07340130d46103a919b785815a1d09161ef94516d669135f05975e5f12f8000146ed0d77c0338707d56c89fa0aad582dd506c28b5582db5f18f80004152a97c10d7989768a6000000005201000049c468e3797e204c75cc341e799c51c29da2800041b8c8794d7c980ce17d5181000038aa65e564e69150086d00000000248258efc873d0cfa85a7026e1d080003c54a93bd8dd4856450b85901982095c5949d994e976f0c409ae08029111d5bd8000409530cb00005416b868800000000000017230646dc7000000000000000000000000209d015eb8e18000000008db800030333846a930c966bdf3216b79caf498800030ad9c03e5c860618000508a000049c229b2800039a98de90000201b11e4800041e7a49288c18000000000003835381ef0a3c94fed5700005c060934a0d331ef7c8f78c68000087201866025008bc1a8d2029803c4744456e008542215d8f8dfd04d1887907a7c99700a619f9dc32928c48741ead163a56480001834b90eb99a39930df9000049aab0c305b90000000000007883dc0a8df508a79825c5c0d94e0123d5e495ec0000097aa07559c6000000004db6a80b00000000000000006c1a8000000009dcf8fa8000657fbc55bdf0e8f5a0ec2548f1edc9440000000038c90000000000000000784959f7f8d6800000000000282b0000000008a2b87480002059a8270000509b49ba0000000000003dcb00000000401538bc80000205ed99c1977151994d00000000684eac0b09533ce8d57d00007146688081ffa475394e80003d67205e0c6a800020e9e0e70000249981e5f91c90d648a47c05b8d26567ad57854cd16e1812089879ba8000000031378000000040799866116a05526cd88c1be807f828086c68848000000030fdb8f009750000390ca9db800060e0b0e600000000000059ae840ed83e1dcd4819192f4594c9ad1956d10e0170b5b0985395c0480d494799e438d9107e791fa1e6e9ce0000218759ca518d0000316e8000616880000000000010ff89f09d5ff9df80000000000000000000693a000041b4000000000000000011e0800050a17191f9710000000058cc71302c1c0000000000005d2f847d60b7019960145914f17748c800000000311400000000000011de392e25f1995a80746119314f48b5d0e2900b80000000605f5921781589a6c1fa2098b40e602e717488b0e96679e3f8b501ac454f8000000005b29194405c00007953a95f4986d10d45ce19ee71d980000000015bc931c0bfd90b60b600000000449600002196e0a481df1880640f18c678e8e453659a887de9bc0839c826599cb86d80237847a00aa0d18000708b000025a800e90948000079b7503f0000011795b6088520fce0225d79ada971f200b02d80810db20485de609cb9b4800 else 0x7013a109800000000000685c800018eee1157d94000078ea8869140280001954181a8000000054e821230000182d20ef00de388e85db200759c0cc159a05088f889780f211b990d4e0534043a1314850e57be9f800000000111c01a64121e014e05d1095800000000000382ae83a3c8e89ab881e596a8040e2030000686000000000618091c980002960e800e1cf000039f3d0b8413e000010448000616d800009bf80004942314ab1bbe065507d000000000000388f000032018000000059f280007169e0178d3680001030697f8000410f15aa5871800049ebf1c78000000000000000607c08fa107881c31421000058830000403900000937000000000000000051c5884769e3085471648000706f80005578000058240000115101987148a1b358a680000000000000001170692b95c9d00e05be000000000000000000000000000000001901194df9a87115f9e55c73e051800000006010d54e800060578000000069dd000070630000217b8016f18dc1ce9127f0cf21eed1845de3396735ed2189c959a932a16235d968b4155f7c9a6852e1a4696fb92a4045c805b9056c72892)))
def mo255D11 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x3ff58d30ffd434c3ff0c940ffd64487ff55121ffd83487ff20d21ffd63487ff50d21ffd71487ff58521ffd51487ff50521ffd31487ff60121ffc80487ff5d821ffd21583ff0c810ffd74583ff55160ffd73583ff54d60ffc82583ff5c960ffd52583ff50960ffd32583ff20560ffd71583ff54560ffd41583ff4c560ffd63087ff60910ffc82443ff5c910ffd62443ff54910ffd42443ff4c910ffc32443ff5c510ffd61443ff54510ffd41443ff4c510ffd21443ff60530ffd60443ff54110ffd40443ff4c110ffd20443ff5d810ffd75043ff59410ffd73043ff58c10ffd53043ff5c810ffd62043ff54810ffd32043ff5c110ffc814c3ff5c530ffd614c3ff54530ffd414c3ff4c530ffd214c3ff08530ffd604c3ff50130ffd540c3ff54430ffd410c3ff48430ffd43443ff61d10ffd86443ff5d910ffd85443ff5d510ffd65443ff61110ffd74443ff59110ffd54443ff60d10ffc83443ff5cd10ffd63443ff54d10ffc210c3ff54d41ffd72507ff20971ffd62507ff54941ffd435c7ff5c541ffd635c7ff54541ffd545c7ff61d31ffd734c7ff61931ffd655c7ff5d931ffd854c7ff54d43ffd754c7ff59531ffd7350fff5d131ffd644c7ff55131ffd645c7ff5d951ffd74547ff59151ffc83547ff5cd51ffd71587ff58d51ffd72587ff54d61ffd73587ff50d51ffd625c7ff50951ffd71547ff5d561ffd61547ff20151ffd76507ff20171ffd75507ff59541ffd73507ff58d41ffd62547ff58531ffd7358fff54531ffd414c7ff55163ffd7458fff61131ffd7558fff5c531ffd76553ff54831ffd75593ff61921ffd655d3ff5d921ffd84487ff5d560ffc804c7ff60931ffd434c7ff4c931ffd7550fff50931ffd804c7ff58d31ffd524c7ff58931ffc824c7ff5c931ffd534c6ff61954efd64587ef21161bfd86546ff60c10bfd82042ff61110ff531443bf58961bfd87592ff61510fbd6450eff61d51fbd7450fef5d154ff521443bf21943bfd8650eff61d43bfd824437f5d171ff940442ff61543efd7658eff61c10bfd86043f758d43bfd87587bf5d961bfd85042ff61d63bfd84042ff60d10ff920442ff61131bfd85502ff61940bfd87503f750d31dfd765d3bf58960fdd324c7fd5c531efd63583fd58531bfd87583ef50d40bfd83086ff61021bfd86086ff61c31bfd860c6ff61431ff551486ff61031bfd820c6ff60031bfd86486ff60d21bfd84486ff60021bfd86442ff61d10f7d54546ff60430bfd840c2ff61830f7d53547fe58130fdd314c3fd5c551bfd87506ff61941efd61583ef50940bfd864c6ff61d31fbd41502ff61531fbd42507fe58140bfd85506ff61930bfd844c3fd58541bf980086f760c21bf5810c2fb60810bbd840c27f61c10bdd83042bf61830bbd84042ef61021afd86042df61410afd86086df61431 else (if j<2 then 0x2494a050a797c190b180b801205048072f94c1e320a89242e55ca63054a70dc0880b014239415e0c4e018492160290f2f83058061240251997c190c320b82a2490b65f0696088060a38302c0521e5f0619c602e01092c2c0521e505783c609e0109281397c18460a01448e17418145397ca6320002849409cb84729834b006124250e397c19091606809000028a72e11ca0080309242c09cbe0c1700218652905282816cbe0e0011460060a4850e397c1844848b1f2f940160c038c0b0248cbe50058300e302c09204f9705e53078c000148cbe530601c60141239332f94c189c1600008149156530601c609c0a09232f94c18071805048e232589f2f83c60000a40845997ca60c0a091c422ccbe5005830b02482b65f0601c602c0a0923298c0d8040405048e56cb80b0601c602c2c09245427cb82f2801c600004092a1a7618f61776151e139e1266100e0eb20c5a0b2208ca079204ce02be00adfee5fcd5fb55f98df735f5b5f339f1ddf039ee29ec61ea51e7d5e655e3fde211e001ddcddbbdd9d1d755d4d9d2a5d071ce61cce1ca89c831c645c3edc195bf85be4dbccdbb71b8f5b799b5f5b331b1d5b055aef9ad9dab45a9c5a7fda5c9a401a2159f759cb19a59982595cd940591d18fe58dd58c558a2187a58595838581517f897d557afd78ed770174a9729970896e556bfd69c967dd65cd637561895fe55d8d5b35590156cd549952f5512d4f414ce94ab548a546b94461425140413da13bb539c9370535853351311d2ee92d212b1128712619239d218d1f111c711aa919291641140d1269107d0eb50d110b25095d077105cd03e10164ff30fd44fb34f948f738f528f318f174ef88edc0eb8ce9c4e7fce634e3b8e13cde54dc20d980d7dcd638d470d260d02cceaccd2ccb88c954c7b0c4ecc390c1a4bf94be80bc70bb14b970b7a8b5e0b418b1c0b01cade8ac20a9eca890a65ca494a314a0989df89ba0994896cc9504926490e48e8c8ca08a2487f0859884a8839482a481487f5c7d707c147a947938782476c875b474a07368723070d46fe46eac6d2c6b646a2c68f46774666064bc633c622860cc5f945e145cb85b38597057f056705580546c537c5268517850404ec04d644c504b184a0448cc4704456043bc423c40e03f3c3e043c603a74388836e4351c33c031d430542ef82dc02bd42a5428d42778261c24c02388222c20f41f981e841ce01b601a4c18cc1794165c15001380122411100fd80ea00d680c540af809c008ac07740660052803f002dc01800003ff08560ffd70583ff5d940ffd75503ff59540ffc83503ff5cd40ffd63503ff54d40ffc82503ff5c940ffd62503ff54940ffd32503ff5d121ffd71503ff54540ffd31503ff48540ffd70503ff58140ffd50503ff61930ffd764c3ff61130ffd744c3ff59130ffd544c else 0x2a503783036314f16849f83400732e85030bc24078b00612608cb09644c2504833894e0a509c1601048cf2e45ca60c778c09c00001842c25113e5c17941880719830721414260d07c78960242524a1312c3b8b65f298342c144e0b0004c0309402c09010050a138289f2e0bca60f18004b42502c1ba285338a5a128582d0b28838609e008280a2020065f060942c140c3e4b00612609f2e0bca0c4038cc1a581c0a130683e3c428121291162d97c1c144e0b2604e125088480b00a894885828ab2f9441e32009684a002429160a53cbe0c0d8c05c012d09344e0b008240033cb9172882c18ef19004b0f612886d2e1741a160a53ca0ab078c13c012d093d2e01152590a138289f2e0bca20f1800414250028a72e0b0100460610f2f830580612390f2f830595a1230300a29cb867180b0142490788c442d0b65f298300e310005049a0f118886600cbe530601c62580a09340016cbe0c021182a32124814002705e5f2983c62020a50248797c1867180b4b42490b016282bc189c023803298c0b0a4050541c2490a14f2f8305c000238148794c609c05091c2e11ca0ab06278000480b847282a5386e0401200a160165f2983c64152c49bb2f83264000230580a43cbe0c17000090140b014239415e0c4f0000940f118884200cbe53078c82a5a1260300d9415e0c4e0184908c0665c0d94c180612405c280514e5c23948000802505c55830ce304f001c2c43ca0af0601c609c0a094b961621e5f0619c602c0a094a141438e5c3383034047060580a2bc1867182784930c4be0c338c05a9e1240005397ca007180202825065058120515e0c338c13c0090005b2e11ca60c420504a30a0788c44210b65f2983c62020b09302c09010072f94c1e312d0928281602e5c2394c1c000309280029088080305182d97c190c1601828e16088ac4e01828c8ccb81b298300c2470a0af06270340460b65f0696218641705202c09010072f94c1e312d09292e1729e505583c609e0048032f832186417051d2853cbe0c0d8c05c00800058122b0c89e0a38012997c1a00220182900f118172f940160c038c400581260000b9708e50058310a302c092c0a43cba5005830ce3016160496160282f282bc180718000494160289f2f830ce300009240a27cb82f288300e3000020496830186f2f94c600a2c40580a27cb847298310a3000092c441c0289f2e0bca60c038c002581268885a16cbe53078c1382c020042824d062500a43cbe0c338c05c5a12583c4622108172f94c1e31011684980002e5c2394c1c580309241e23198032f940160c038c428581268302d97c190c320b82a5212505b298c218ac4f054bc249060a72e06ca0080309204421040584f9705e53078c002240a68584f9708e53068c000040a50581227cba530619c60000a50252e29cbe531880014)) else (if j<4 then 0x68b65f078c4028d280682c250040a92e0b110052c828b65f298c512a9070584a22705c9c0597ca005028282e320096449c211625d2c8590cb20aaacb90b2883862010509441e2c0ca0d009742c86590538e5137838629d2d0948520121e510583366304e9635c24c429c72f830890916962b424a108905619404013756512910b21964172f9441c312d095098940625a2c858281b282ac189d0001849e805560d2c854b958023c0c024b25a5a2c858290c5583036304e80849a972720106964da14ac011e2081261990b050365055270da0803092f298c4b0390a53150684e3c0c012126a5c2e968b65318858282c541384988cc665f06964294c0c0b1e060090934b48582a500d8c1549c368284965b002588b16c602d0b05150187109352f9705e50038c4b0390a2a130683e3c41012128a5e282a429320a27cb82f28838600105013db0584b2160a53ca20f18278020a1269692c8522c1455974181b180b8020a1274512c4c8b652130c42c14162a09c04d33a5a2c851dc140d941560c4f0000c24e5d0e92d16429160a53cbe0c170000c24e332590a3b828ab2e06ca20e008200c24e1d25a2c858295706539380612596c069742c152806c60a94e1b81424d3380d0b050365054a70dc08030931743a404590a6a829572e9481a2e0401849e2900a9f2e8bca1ab18800113a126094068582957298c15200370284989786258ac858295402531e06012608c9c4b8b28d9685828ab2e948181b18808142512b03c468386154e28582a6f0706c614d4e9684a2562e25c2853861552c4242c15559741c1b180b4020a12a094290c4b4588485829570706c602d01093c9c4c4a2301916429aa0a2acb81b29034040803094846858286f0606c614e4e96849680802160a1b030fc049600c24b01a160a55ca007182a5386e040930465886258e28582a0e0d8c29a9d050938568c45c032f162b2160a554a0047902049e01ca1ab18292700a12858194144b2152f83089094e5684940121e50d98c1589cd70942c5cb07865b08590cb20a9738e51070c53a0a127a590a71cba0c224245a08ad092c1e2514aa92d1647a950b21964152e42ca60e188084a671cb867061126200ad0924928b4040318858286d2802030fe126e0e079746458ac858294c020b1e0601272591285058a898131c178c8665f28834b2160a2a008f104093b2f838b414ac011e060124a590a2acb865064c802080c812c96968b2160a191560c4f0003204ccba530696428280c1f1e060030930b09644c250b05419c7182780208c4b85f190cca25a2c858294c5401138f0300940b6170a2160a2a5386e040680962b112910b27cbc2f288380e32000d4b424f119612d0942c15070c29a9d050130879701231008517e0c0d8c4581e2c04849e5a42c1455270da080d0124461c2da01b6858 else (if j<5 then 0x4546cb42e5d2902c1c0718808b424fc18071880cbe50721d0d17d2d09300397ca20b0660c6014120882a5a126820360f21a0c028080653078c0b0152e9b1ca5a129020924311a0c050345a020197c6015283f030e52d094c10241588802a4404032f94c601506394b42500420c05034003a0197028187e011ca5a1278204e0b4180a06010065f298c028fc729684a103cbe5002a745a08898c4025a12610f291414a015583c625a2c97008f20a093c868c45c032f838b15928011e4141268ad0100cbe5318968b0fd06011e4141270220197c1c58ac011e41412509c16800065f2983c625a2c05008f20a093c2c830140d00048065f298c1c8143a012fa5812889f2e0bca0c52c2dc1e32000a1341512710d00204b0222d97c1e311694030161270ac02a2404032f94c625a2c3f418740b093d001a8065f06968b110120602c24c0489c160116a581116cbe53078c40016127858120200a020197ca60f18391e17c0a9684a00f118a422804b2530701c60e14f05849c0f21889b0964be510701c629e0b09352e2b11888228b4020f18964da52028282c2500782c52a54b25f298380e30268082c24e1388c22cb4b65d298380e30268082c24e4b8a816224b2ab2f9441c0718134041612783d28434186d36804baab0701c604a0a9684a04311808228b4065d2983c640425054b424f158894880cbe510701c604a0a96849a27058e00597ca04f078c094060a96849c431480500aa39a581116ca60f18a74b81612809c16051865cdb94c1a07182d82a24d168052c308b6531853154151258b4ac940a2312c6d8b65f06422982d0d0544a02d2702c44014b20a2d97ca631442a41c151280845a2c13ab12d16cbe5306a1212320a893c12014b0b62d97ca60f18000f89c1705449e2d0e09c160200c140b97ca60f19004b224f1382f2f944160d038c802591258512d16448985b09cbe0ca642029827460792c2d8b65f298344a048405345619110852ce644c9f2f0bca20d190041415015888030b41a5b2f941fe3201270c41512786442ac4b49f2f94c1a32010b0c415127008032785e5f298309630310082a24d041304e94460312c608b65f0680030060b0940879400e3100aac1a581c970d0f20b0938868c4022c1797c1e312c94030f20b093846082d8a500aa6da5a2d83c629d46974a01a0b0948038c4065f2896010fd061a1e41612683c86014145b298c53b612e8382c24d11b68105a4b8ad008b806312c9b4128d288303416129a001197c1a580c8c1e416125020ce29402a92c608b60d4e97032320b093d743a21a012c608b65f068b00a511905849e083325c5680304012c9b41019068c82c24f00e310197ca60d2c0e0d0f20b09314e8b00e5f2839c19831805400220b09381e081282c5201552952d16ca60f188047a5e0b094846082589d969 else 0x10c461185c032f14c1e31048182a5912725c2e968b22612553894c0a516c18944b45b06972101a0a503db0580ca012d0184a5f290c53a08e28382a05a0625a2d9738a0c84068294a7cbe0d00110f0060a403c3c2514aa94a968b653070980a3d2e4282a00c8b65f06710c9300d0524421e1525d2d0184e5f290c41289544241c150cba0b06110f2580305201e1e0d86506804bc061394c1c314e714dc1500605b2f83389080d0520421e1225c56198a29101008626e130680a59448382a61e13808430184e5f2983862580a42829c1c33a010a618281b281bc1a9e2c01849c6b402ab06968b25c0c3e828051261392e6a404012c9b04819063e828051270032f834b4580c3e8280512507034808065f0605031112c0144981914a0154734b07a2c97ca60d4f09809c40a803128968b65f0671210180a525c56198a151001e8020e18964dc260d014101514b2243e2dcbe0ca64282922d2da5a2c89188c2122a21414b13e5d286f4b0b7298344a04144246414e1699d2c308b6511281210a9190531743a4b1b62d97c1a25020b29a5119053842e6169992c8940c272f9441284544241a320a8c583e2d84e5f0627059320a5250989616c5b2f94c1a243e004089c168c82a01981e5c43944b4254e8b41200890535743a21a010a6182e5d298345c580309383866404010a698286f2e06ca00a2c01849f94cb80b0601428bc358c4001e2c04849c0200a9f2e8bca1a70661c6200390934461c2589c04a365a160b974a60c0d8c4045a12887098274a230188530c172e06ca60d011600c25121a014f00ca60f188582a5c36011e45812790c048c45c032f832b2160a94008f22c093d001c80653181642c1436010c00a2c09383900cbe0e0a56008f22c09282c27058090000cbe53078c42c14023c8b02500160c038c2fa003997ca0bc348503c580909400401cbe50d38330e3012160e21612683c462908a01b6854ba52058380e314f1684a0200e10c460285c032f83c648c0a0682a5912809c16a70165f280180a0a0b8c4025a12719c28968b15484068290660a25a2d972aa0c84068294254b45913092a908170524545c4b94c00554b22613974128954832102e0a890f2e82c1a58320b1041490d83d065544c27069b3894e0a588c40241584601425222613978a63216965115507054c19140b65f06712101a0a4a261397c1a584c532102e0a510f2f830c82c410544c50911a5a2d8c2a818a70544922310138570b8065f189641288aa83034151280522d97c19c42242829591251152d16cbe0f1826298181705449827118)))
def mo255H11 (j : Nat) : Nat := (if j<4 then (if j<2 then (if j<1 then 0x300000100000a00000000100900200c00100100b00000100100400000000400000100000000500100300100100500900000000d00000200400200200100e00000100100100200000000700000000400600300300a00000000800000100200600000300300000100200200700500200800000300900e00100200300000000100000501700100200000200000300100900000700c00000100000000000100300000800600200200100600000c00000800300800200700200700800100200400401c00100000200600600c00100200400600100101500100500000000200400200200200400002f00c00200000000000100400000900000300000000000000300400a00100700300000f00000000800000001000000200100400f00000000300000401100100300100200000800300000900300100c00100100802500700100100200300000100700000100700000200600300a00000600000200100100100b00400200000100000300400400100700000200800d00000000000200000400203c00000200500400300200300000100700100000000100000100000f00600100000000d00600200800901900a00100100200200000200000c00200200000200000300001300100600600000500000000000100300002700700000300100100200b00000200800200800000000202a00700300000600301300000000b00000901600b00000000001200000900f00000000700600000601400501300000100000802d00000100000100201001b03400000000100000600400100100200000100100500100000200100700100800000100000300300000500000000702d00000a00a00d00000600000100300401e00300100000400200300000000100000000400002400000000700000000100700800000100200000000d00200000300800100a01a00f00100000000100000000000501500b00300800002900900400000000c00100000100000001900000000101500000100000300000400800000100000700400500900100000000000000300000400000801300b01301600d00400301400e00000300000100700001400300000800800000f00000000400501a00700000100000500801301400800200e00000000700700000400100500000300000200400700000400000000a00700400300000700000001100202000000200a00000101100000000000000100100000600200600000500300700000000300e00300b02500000200200600200300000500400001300800401900600300101400600800200000100600201800000100500000200600300101000000000000200200000800a00500000100900300000000100200000700000000000300300800100600000100100900000101000600000000001200000100100e00200601300000400e002003000 else 0x3ad690000bdcd000000000000055b322a7cfa0000641d9cacdc9fb1426ca80000a0aff45f0000437d131cedb80000f58534544b541304b17f00005bfd000000002c10654eb0172317b5743148a4c408bfd1fd2558c4c0c50b80d3dc80d5996b63240269b1fd3ae35eb2c150fee3fa7a0361bb25703311a4484bea216ce9a753a8d077c24339c1356545d4ba0cc57834d66dab74b3f5b46005f41602a09a78f119719d699c221cd9e592d26373eca451710d70c5897cd0fdd02004732ed456821974f000e159eed2c483d9badf4538b523e3b958f1b40e8d4760bd05456473001e010f005683a70000a333f3c7f0ee09a6000014be0000581d0000000050180000e05070a5ed1d000082260000000000000000422311cdf132bbf7000000000000734e000000000000000000007c82000014cec147435cf24c000099ba4d41303000002b4855aed13cf4f313871508e4a20474f10400004292f52e0000550212e643c40000b2c7000000000000000000000000b95c000000005af3b4fe93b30000431d0000e4ae159a8942000000002d304163e11ab2be4d5da20f2937a07c9ab51d616dcbf5c3000000004caa0000f262000000000d180000b3cf000001580000ea7e000000000000e376fd57000000000000000000000000891a59601b317123000000000000a273f506c4a60000e5125391fb410000130bc21d0000421f000000002231d5b684af0000d43778f54238d3508a310389000000007d29322c0000e068f0270000000054d50000d3884a41000073a0f1bec00f0000a3230000000000000000000000000000000000000000ea5e000000009afc3afac4d10000b3d10000d0fd93a400000000000000000000ab960000000000000000335f196a52d09bb574eb00000ac00000000000000000f06e80d605acbb7285b27438b517557f3166cd28d1542085000064f80000542be0890000e11c752703a35d7454def2a304dbf4000000d0068230a86373b00000f19bdcd7fd9d22e00000000041900af43313d52f827d0000323c0000049e000020f2645ea08080a900003462000040ba0000c179b10895616ad600005955d557000000000000552500001552b156b5a4d2f863161a530000584f6aaec3b8000000000000451d00000000f087bdd300000000ad73434f00000000000099816b4b64e59136e5c10000000080e80000217a74b830c7032778e600000000000071f2d24600006414f3c14b710000a39c00007ab43d090000d36a98f0c1280d08000000000000e3c0319a000024b9524ed41be947fa957d5bc081438a03e400009562c1c4d30adc2aed02b55423eae053397600500000000000200b00000000c00200000000000100000001100200000003300602d00000000300d00500000000100c0000070000010010030000000010020) else (if j<3 then 0xf003dfc0f00002b7ee13aba44a0581b0f000042ba22ca129c505fb98c297758dbe28700000000000000004994e3280000f1402146000010f5736c0000627ef36d000000000000a00e000092630000000000009d26c0e7c2bc424fbc8694e9cd51e55f0000680e82efc074e1a369c4000044938ca000000000644aa444c40921a10000446e0000d1fe00000000000083990000107e432221d600008117256d24da817400000000c3ab1065308e830e0000000035c64143b55574c1ad3b000001ec928c0000000000000000ebb4000084f5000010830000e257000054619c508129000093ff03b71dac680c351c00000000d4072540d3103b94dda37d6f04bfc33dfd844baf24c2000019ab00000000000000004449750da4ad80bec173f31bf35a4dce0000add25b0e40d72131eaacc4aa6513128489c992b458f7a27a345bf8dab075b9c52cae8357aa75a152baa890a292d96b3b3a0698d4b5a16a80ad34e30fd58f9aa52d070a6db17792fdc59f60b399f3899bc37e1212c817f4ee3a5cb5d0012c0d67fcfdec7cb9b57b9970ce69f7b41884a5ba70708d04600000000034fc0000a28f0000805c0000000000000000b404746b000013c8000000000000b161835d14a8000000000000b4330d01000052e5a0a00067fa9ca02ef9ed05cdca52000051e889c33a7b227c7b55a32572fb42f2254a0000b15bbad2b31203c37590000012da0000e9f524940000519e138325340000d08200005dad8ccc0000000000000000523b0000d5269546b58300000000a48a1ce9d1e7749ab4cb8390fa2d32101192b251649d31113935dd0e63e6728000000000105d0000212245a783821213a591536e000010db00002d2af1418cde6038a10200003428754400006347a2c89d7b739e40422385000000000000000000001d21420301a71036844ca500b0f7725e0000911883edb3d800005453d1782393000011cf0000d020000000000000000075059aafdbfc00000000d573fd63000000003441c2aab1a5925b316fd24000000000ed1154bc40b660c9a20b828d14f9e431acc20000000023e700000261000083dc503caac4b34000000d760000a54d2c840000fc7e000000000000000000000000b46d0000bd3700000000000000000000bc29a2b000000000fa8f00000000ccf78bb8b47d000031680000847200000000000042b932760000655900000835544510ec9071255c34f2b2d361ba00000000d06100000000311f735300005d6a0000000065889d2cc5530000141a000000000000602f00002138f1fb00000000000014ea0000000078289b56915d000032d66d8f50cf000000001b4928e0549b20da3970000000004d17f2a942490000f392000032eb6a4828318046605700005524a1aa35cf0000000000009a71000000000000959cdb9f0000e4e else 0x70d8c1e3d42f000084ca8a76dc54846580f8906a74d4000000001cdf7228c099000000000000f0fc00005bfa30abb3d221c200000000453ba1c9509a0000c44f54c7b8e500004172aab3b45cba92000023fb00005cf912fa00000000a55d0b0550bc502d75c9632fd5d5000035a2fd2500006c41241e74975186b8d0db8f000030a425ab544bd2f17162b38ef98e0000841730d1e92f3cc32c530cbe120600004341fd715bd68001f850550ff29b443e1d586c88c17641da00000000426d00000000843b000000000000695a00008b3f0000c55a0d330000a58c00008d04f46f054f784a54466511609fd1a6c9b0b944000099b700000000922b000012b500000000720dd56e74e89dbd79e473acfd5073f3304493d6203500000000a3d06201c2aef1aba471b22fcd3f953171f1ca25ea45805a73d4e56c0c493925e9615905e0e930e69264d503f51fe4e458c3001c0000f1ed0000248bbd823931fc780000719c0000d15e8a69556874ab2450a16ec37a91f3000021bd0000000019650000000000002259783200002580203484699d540000da4b0000530c0b52c4d9c02b0000000010fa30a700000000da469b1d00007d66000000000000000061c0000004a90193d22d713b73d500002318cc878d8e309549f20000d0490000f1345aa70000345ac443f0974167c03ab073b0ea02b1783784fd000002b812db0000547011b193370000510a51db6c2100000af132ec0151000071de0000ecc0000000006434d54b0000000098ee000010d0bda0000000000000000000000000000000008a68334b930362e9000004a4000093bcbdc701e500000000fc9d00006c8f0ab8407d000019bf00006838143615b300000000000000000000b3344ab90000f48679c6042372affbec20370d00f4fb4ada00008268a0bf78c9e5847dbffc2b000020b581bff8fe13f8258de4a3000061c100008da9b3bb0000810605c4951bc0d50000130500002cf50000000000000000e8ecf5a000000ac5c188d11ed8073caf7abf000000000000000011b4000055b9a8de61646a21e07000000000518efa3f948711ac0000000010eb827f000000000000e5048d1ac2a86830942a02a53016000050120000818100002b9af4f40000295f1d2dd08b0000855e8bd70000725db3190000000000000000000031d4c4357113a2ffa0a81c01740b453e00007c6100008290000000000000b26ce3667bc551b9a20a557ef52b08339877910c8bd213d744cc90df0000dd190000e32900007ad352780000614e00001194000000000000fb1b00000000b5662a649a20ebad453fa26f0000a306f0d2d01d53450000c307c091052a0000e4e20d6c00000000f452a4b5208fac1394c91d5a78368aaa6982d1df000000003bfe1c1a917e144d4429629aa92ca0409135c32d94a054d)) else (if j<6 then (if j<5 then 0x8706d0000d447b4770000517d0000000061d540290000000000000000000000003ce3000093e1242c0db30000b38f000073eea5304b7d7a34b8bcfc1851104c8913656a65491b928e00dd998f1b79137ca23d7c7a95433c0e88cae4b12d390000d47699938c57084203af6ad5881ff814514c02b2d0519ac3290171e900008989000068e2fb7468bdc5633d200000b8ed000028d60000e5ba0000000012f472dd4086000000000000dcee046a73ef0000000091840d6b4b5145941597a33290ed35600000798433ec02d400000000435892ad133e0000db690000b1f0eba919161c264c3de22100000000c20700000000a24aa2df50ca000045350000000000000000000000000000101900001ba5d522f50ad43cb5d6daa9519f54b0e1bcbcb021f6613ed2220000f0250000b2e7194b5a903cec00005556ddcf0000b05ef26782347496653c0000ad136250b18038ce00000000000013957514000024ed6b44000030c6d2820000e3782b70ace181e6e2850000000073ada33beca1000000000000000048c22296000071498b8ecb629235b275000012b3229e442183c283b1b3b65007452db4dd443a3c005ad08ceb740a0000d93db2fc21b6b29398f2000083f40000000063f6e21e00000000ea4700000000dd65b3db0000c21100000000ccc5ca3a7430e464fb98630975ad00000000e1d3750c00000000298300007a4052f598e88c4865a6000078f300000b60607a0000b48559d1a00adbe800000000000000000000000000000000d377b17c3442d480537b02a451c60000000051210000c2e124c3b2e444017216442ea1c8bd0d000045518468b2586492c42df3d37031018593a2406fa5d3f114a2913d36000000007200000018d8a0e50000000000001063018c0000000094d3dc7b00003908805483caf4266922114dc425bb7548ef8d8d0000bab0757a00002509396e1245752c0000742000004490247ea1b742e210f4f4efe1e401ddd14b9598330d6467e1cbe01f41affad42ae0b10322774300548eeda8000083468a9a43f7510003cb112bb363ac2cd3dac5b1d3e84196000052ccc9c000000000d3c60000000000000000000000000000000051ee05c84501091db342db58da4e0bf40000809000004b09000031e20000fa4ce16b00003d1b8abc00006375e29dd38bc98b025a826e52088242b0b494b6c06481ae047c808805bc1829522e8923f06900000000f04f000090f9e80aa16022e80000b2f7e4a1692000000000ba97e41cd0e2000092ab0000000042fe428a00000000000000007b3efd9a0852b2810000608a0000000029fdb9eb0000399a00000d75d40fe3beebee000061c30000902c2011000003e2cc02000031b200000000f4cdf510f3aa1abdb1f54419b03943670000807200000000412d0000000000009499000 else 0x182e30000641f98c800000000d294e3520000f0c1a1ff031e00000000912efd4a0130b532c4d04528e2487c5a0000c943e33600006a770000c2650000000000001520000002bf0000057b0000b3e00919000000009af50000109c00000000d159f47a00004a37d2ac0000500c71c7bdc5b5770000000003fcc022ac9e0d0c0000000053c5000092c958c5921453e30000d01500006372000013fe0000c45d30deb51a5c06000018fa0000f1d002240000000094bd000000000000733ad02a1ad93acec537235b604d00000000526b432c6daa0000f060f3e523012002f29715d2a3614084f0e3dbe40000ed15000035aa00000000e40592a7a1982116000000009a3510f1000095be23490000f165387612690000c44e4cce416900d4249ce0a6da05000000000000000045a895070000029f0000c2b69c3ec5b08b18fb4f9aab000000005175791e407b0000f0a3a25cf53600000000000000000000000000008225b0760d12b9560000000002b7451e00000320bb7c00000000a23a000000000000a9aa0000733c0000eceda9981958816d4aff000004570000809200000000d3980000857679406b391c03a247928b25296c0504e14b4600000000b059da605ce2cbacf1a4315c0afd7451587fe80b114ab49f00006236c491000075bbc39703f9f422c921797f2bf6f5720000640d02d700000000000092320000a324000005ca0000ac81f9bb6299503300009308937ff403d3026013e5812a7ce5c0b9fa237950b7e21a5d48637400000000c03b0000000034750000000020149b770000aab1943f000011a0e909fc476d43e25fc0ef000000008028000000000000000018f4c2410000b9efd0aac978027400001227695d619109a54d2752dec04e8c2dd4ba00000145509601ad84810000b09e000000000000224d8094e94c6547000081b8c38d3aadf0f600005cd60000339ae2dcbafbb266001a3a1940dc0000f12ac3b2e2ee7ac2147f039de0ae3483710eb9683cb3293e3205c81a0c90b542000029f6000023cd00001cab019971156bc41d1cb045827189ce021774bba1fcb0cdfb0d9386438144592571c58e34f7e21b0000a973adca24ac0000c33f194f8c250593b3ce00007bf3d848ebcf82cd22bda859785899e05c23f2c0429560f3e9597b022ac8000094a779e90000e1d99da19bb3120e356b00000000d048f218e0520000dcc60000000000000000918a08081af0e59e02f0a439b90ca5b8f043d2cb0000da82000034d2f498028892d8448fb5cec8d300001cfc000069ac90c400007286000031cc0139e48215b50000000000009354cbff000000007a5933eb00000000216a0000f4ff000000000000a4584351000011fa000070c5556f434d45490000341300000000d0ac0000b1550000013300000000c44000000000000030c) else (if j<7 then 0x7986348443c990fb421593bf95c55dd443aee2d13298b1b02bb2e8fb136261098d4050c2059bbdbe354c997dd8be0000d0790000604a74120000dd0b814f0000618d0415d85360bb63a67289d3f2e1d1c5a913b5e8ff5d35b0f07b8c3406e3bd81caa4f1612661d895165348223f101b1bb6106683680000d09869f012f3720474c6c09d5360613f5478d1e00000600b00006d2f000000008d38c521800960004d05000000004809d40890e0f06c00b2383983846b2deba4dd3e9550c24b8c830000000043ba748d00000000000000007d1fbb8382c3841022c6750e3b3af1ea85393ae3603242c55c920000d124146c0000caba2996012f8803000092530000d0a100002144c364aba8000000000000c90d710d000000000000bd2e00000000e31f00000000000000001587000000000000e58a000000008c550000000031eb00000ab663e9004100000000c4e07b9b00000000ca9deb2c101000000000e5a3000000006bab1a9173a170b90000000000000000b4e6dd03fbd50000000028d50000307fa27931b300000000000000000000957d0000256900000000d0b1d424c04be105fd8100000183000000000000000061820000736f33431dcc31375cc7c10700002d2200002153000010d9d31a427b92d5a99700000c1f9db54582626000000000425200008ca3f06200003c4c04d70000839f0000000000000000d0ad000081f7000064890000cdaf4da7cb57fb08e1a900002992f33900000000e57c0000653a937113a90000000063708432b4b7847909067cf8e08c3bbb91dc296d5bd925bf7055c2a24394947b859519c7115ff541434400001321240c0000b06b0b9c41125c4600009283b15a1dae00006331091c000000000000000000004bc0d38c00009355dbfb653d1b731804faf600000000fd5f00001a731b0641250000ed53000042a6391f1d44000014fa0000d003e17b0000643d6847a18b00000a0700001359a270803fe18fd2720000f92d0dc4abbd75bdba6b1548c2cefa560427000000004a6c000072eab189edb759f491f99ac90000b9130000159252bb051594e7e26ac209000000000000632b22391026b90b6934eba20c594237056aeb00a2447078ea22d519fb6d0000112700000000a3dd00000b470000000053f06533b8f6658b73b4b5b7c03e80c0812095cbc10b94666338a5c2600dda96f3f111ce75670000211d0000f4952101f1f400000000b3f5f22000005ccd000045c7e9ec0000c0cce596e4d8000053a5000024b471c57256f1d283cca356a98a6411000091955197000000000000a8d9cccba5d10000436970e4291740b03233513d61b5109be1a8000000000000000000000000b34a50470000000000000000f8d1296c6c5842ed531469b2b0c3cbbe2315886421a2487483260000000000000b03eac else 0xd23e111b000084f6e255f008dbd3fd0a422991ef5ce7315700002db6000000009bb700000000002410b80000e05b5b4e0000704c0000720c04b292cf948c00001aea72a1033044ec00004b9e40cb000011870000000000000000d34c75643c22920211f8236b1bf55518000000000000d2f9bcc1000051e161d74579000050ff00000000000000004150d4dc5254f09382f65900798500007db4fcf1d586ace600000000000033dfd170e023259d72c2545509f1939b1d91ca1e84cf000068dfb93a53de00000463f5ccf39649add57565afc48870210000000014c8000000000000732a4dc1b33585a50000f3fd00000000d4c5038)))
def mo255D12 (_ : Nat) : Nat := 0x169794838c0509209e5c2e520e300014816099794838c00052050005a5e0c3024180414a004216099714838c0b052a5e500a0c06305824800059794838c1609209e5c2e520c06300024916059794838c0009225e520c06301424700161b059794038c02092830005058165e0c1a302c24b002a16051794838c270928505824165d0a520c300004b4c1609234b059714838c002c00586c241998165e500c300804d3a059714830c0b012000a85824199c145e520c309c04d002a4216095b051714838c273000595884b0165e520c3024bc857f2db560a153123f4307d4eb1ab2f8544910f31782643102f000ffa21ff0c3fe987fd40ffac1ff087fe90ffc31ffa63ff043fea8ffd61ffae3ff50ffeb1ffd54ffac9ff5d3febb7fd41
def mo255H12 (j : Nat) : Nat := (if j<1 then 0xc0ca2e4000c16400000000000000000000000000000000002e2900038a1133992600018a60000000b191c6e40040006a3c0000000aca0002c83b26405fa1fa51e73e00005249446ca7c0bcd49c0c60000a1ed04b71fb23d62463ca3269c65aeb0001256b03a0bb625400000014cbaa40000000384ad07009a01994cdd06ec7c5b782c300000009238516cc91851b4040000001a18b1016d11060000c3f02d7313c49400000007c78000e389813aba800092ce42300000007ab7f0dabb0000a37c0003356d2ccb348e780f68ef6170000a3490f90000000c1a505e4b5783b9b82ccc415de0b885b5036481a8ad306109328a4ff3044000eb194740003d2479f3408346646ff02400000006ce525bcdc0000511a812cac42c22f78ca48c350cf10852d1090f0282e98be0c10414aeaf0003c6a0001a660002a949346422f1240000001aef3014000b3d800044748a438e80006adc00000004300b64000000130900024aa0320873648ca2390f24b8547c42441200001052416924f8c900028280002a67a990000436f4e0445400000000000002e42ebd960913b40000000000000281900020c40000000000210d4940000000209c00010fd0000c7b50080003b8400000000000b30cd4b07440000126be00012fc00000000000000f488000e314000a9d0000f22c826b15000000000000000b21e2c88d0a0b426a992d4ea733c000000343400026594c10000000184100010af3cb189e33b8b16529f91c834c6ff52374b1e14d091e27c5176c80c8991e77086082ad332a000092b58baf109a9aa1c141ab308ce6aa1c9076c8be5a240be2d000100d000251300024610001c68448400000010e800000007b3d83ad1ae0f02375425000084ceb9de3b00000004453c270003c38eb48a27000000059536c4eb53c58738fabbb3694170002c6d000225f7c4cf037394000000000000026a2000363100006581468000000000000024620001714812ff12c21c000988928174a8ca50002c31641387f000000091d40391301210641bcfb0003c76f20400030d8000e3b000000034ca00024c7fa121100000000485104d900c000000000000034e4117489d0000000726c000000000040b00000378000000310f00016a7603f706000250b40f8ae85880e3dc8076b40000000000001008010080200400028010100804c010680000000000010000100000040040080000006004100540000000018030040001c00008050000200815008010080200c00008010080901800004030040600403044000240000402000010000e03405010080280d030000080100400000030140100402024050141e01c0000000008020001c004020100000c010000102c0d008030000002c000341a00c060000000000044080040208c0400800030010340100006020010300101005 else 0xdb42d0522dc00023afe320002a1100018650000498ec68088000132a000321f60d769e3c438ae93d0021683c0000ac800000000000000000000021d00004861430707a07b679219ec6052f9c77da0f48c191b2dab18dd12fbd40006a7705babed815a28f4d8e2dbce160a6a2173ead2b81e8e06e3dd043536400000004e9000252850fcc44000050a2b7382b0002c4e407c0006402e1360b942fa283afa42fc0001ac1262f01907214a4078e35b2bc5156ca9e2138bd11b2845c3cc000ca940000000000000270ec0dd88573f989700000566228305000000020a8000d3d7d1b9ca0807194e925f2af4713439a98314043209c42c7cc3ed1841f4ecb1bfb047f20885ad2d50800000000098ea70ca8c0f1702e2760001a6b0000000da1400000028d71b6000000022470)
def mo255D13 (_ : Nat) : Nat := 0xb9406304ff
def mo255H13 (_ : Nat) : Nat := 0x418000000000000d138e60420b2800000000b0cfe4c00dbc000000000000001f00002700007b40000000c00305000007a8a90026308b6874a49f0000647cdf940880b0ba9b430acf3000014010304020000d
def mo255L : Nat → Packing
  | 8 => (91,5,7,0,0,11,0,mo255D8)
  | 9 => (1037,4,7,0,0,16,0,mo255D9)
  | 10 => (1495,3,7,0,0,17,0,mo255D10)
  | 11 => (301,2,7,0,0,16,0,mo255D11)
  | 12 => (20,1,7,0,0,11,0,mo255D12)
  | 13 => (1,0,7,0,0,0,0,mo255D13)
  | _ => emptyPacking
def mo255I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 36 307 9 12 7 1 mo255H9
  | 10 => lookupWord 449 1949 11 16 11 1 mo255H10
  | 11 => lookupWord 725 3163 12 16 11 1 mo255H11
  | 12 => lookupWord 149 653 10 14 9 1 mo255H12
  | 13 => lookupWord 11 59 6 10 5 1 mo255H13
  | _ => fun _ => none
def mo255 : Forest := ⟨1279,13,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_0 : CutRow mo255 8 0 26 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_26 : CutRow mo255 8 26 65 := mixedCut (pos:=0x88028900c50240481203) (neg:=0x12891620e18462308c4541c) (data:=fun _ => 0x8720906462106054621060546210605462106065621060656210606503134150031241500421327103134160042132710312416003124160031841600313416004213271042132716010658762106075740172517401725162106075621060755401728147107075471070754710707506016760060167604803834106016760060167600601676006016570060165700601257006016570060217817512006045107220621025101602678172120070451072204510722045107220611525870312416161156587031241615120606004213262165125765721001030214120212100102121001016512576302141200421326230214120212100103031412021210010) rfl (by decide +kernel)
theorem mo255B8 : CutRow mo255 8 0 91 := (@joinRow mo255 8 0 26 65 mo255P8_0 mo255P8_26)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_0 : CutRow mo255 9 0 18 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_18 : CutRow mo255 9 18 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_114 : CutRow mo255 9 114 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_210 : CutRow mo255 9 210 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_306 : CutRow mo255 9 306 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_402 : CutRow mo255 9 402 45 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_447 : CutRow mo255 9 447 2 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_449 : CutRow mo255 9 449 96 := mixedCut (pos:=0x1288242800a03121402406) (neg:=0x1286248985843818b10541c) (data:=fun _ => 0x53104100531041005310410053104100531041005310410053104102806776320102131201021312010213185709930743089307470593028067783201021412010214185709930753029308530993031104021241361317431898074715980747159807461898074618980747159307431893074715930746189307471593074318930746189307431893019310410747059302410614185709930853099308530993075602930856099302410614124106141241061412410614124106141241061412410614124106141743189207431892074618920241361317431892074715920241361316907386224136131053104104231617274318920193104101931041074318920311040103110401031104010311040103110401071061253311040103110401060065341311040103110401020102130205021302080213020102130280677526001534134104090130145605201216213014560341040103410401034103010341040100201219220102130311030102010213020102130) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_545 : CutRow mo255 9 545 96 := mixedCut (pos:=0x14088241401224090180a03) (neg:=0x184911c185882a0e250c431) (data:=fun _ => 0x250341202503412025834120250341202503412025034120250341201093822121043010109382212104301021043010210430104343722143437221350470103504701035047010350470102104301021043010210430102104301021043010350430102104301021043010210430102104301021043010210430104343722143437221604363414003412091348442450371203763468545037120434372214343722120031120683527639231945243937221684527634343722192319452434372214343722145037120200391204343722120031120200341202003412043437221210430102104301043437221210430104313722121043010200311202003112043437221210430102104301021043010210430109134845245037120450371206836876345037120450371204343722160406341210430102104301021043010210430106043638121043010210430106043638131043010350470104003412021043010434302212104301021645010210150102104301021012010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_641 : CutRow mo255 9 641 96 := mixedCut (pos:=0x14088280909012048180a03) (neg:=0x1283862188c23115309221c) (data:=fun _ => 0x811093807230743172307431204031202040312020403120204031202040312064308221643082216430822164308221634081201030422110304221504363304343801020476120214300102143001021430010604761202047612070305481102012211030422110201221634081206340812063498120631081206340812010374221634081209104164263408120234031208140933023403120811093301020122163408120434380106340812072307481634081202146701021430010214300102143001023120010703454414343801050536330214300102143001043438010434380104343801021430010214290102142901021430010214300104343801021430010214300102142001021430010214300104343001021430010214300102143001021430010214300102340312023403120234031202143001021530010214300102143001021430010634081202143001050436330434300102047612021430010214300102340312021530010214300102340312010201221) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_737 : CutRow mo255 9 737 96 := mixedCut (pos:=0x50240900612032201205) (neg:=0xc461620e054c218a51221c) (data:=fun _ => 0x583584734605636146056371460563715835848346056371460963714605637146046371460563714605637146056371751541207535912058358483758591207535912058358483758591205835848375359120753591207585912075354120753591207515912064506381740858537408585364506381645063813035051030350580820817528208175231305070313050700440137104401381203021202010212020302120201021208350743183507431313050703130507031305070313050803130508031305080645063716450637164506381645063816130602030350510313050206450632130350510353050203530502064506321303505103035051030350510303505103035051064506321645063212870277564506321645063216450632164506321353050203530502064506321303505103530502035305020353050206530502035305020653050203530502035305020303505103530502035305020353050200440132135305020044013212030218020102180) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_833 : CutRow mo255 9 833 96 := mixedCut (pos:=0x110a0240141224031402403) (neg:=0x25182916118988380e184622a) (data:=fun _ => 0x5431467154314671070165820701657220032130200121305431467194083864070265720701657220012130070265822001213007016582070865820702658220012130200121302935a752863084412935a75229328752610130706171a070200321300451668120032130200321306101307061013070610130702003213020032130610130806101308061013080200321302003213061013070410343104103431003310671070165713510407035104060701065107080751008138483701065100813848302102182021791820216218202102182021021820813848370836680410343913013061050731381451346903610301035130680410343913610301030130610362050704103438102102173151040701510407002102173152640703230518314304361143043611430436114304361143043611430436114304361143043611430436114304361021021821430436114304361021021821430436114304361143043711430437114304371143043711430437102102173) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_929 : CutRow mo255 9 929 96 := mixedCut (pos:=0xc12501411048018901205) (neg:=0x31184c1309885494488e0621c) (data:=fun _ => 0x3451617179059230345161713451617134516171650a44413615789236157892790592303901507139015071285029101851237009510370120120810350191018512380120120811851237018512370120120811201208109510380185123800951038009510380095103800851038003501910095103806950a8206950a820790592316950a8306950a8307905924121102096650a444136157882361678823615788236157882361578823615788236157892361988823615788236157882361578823615788263517820361578827001323036157882361578823615788207103293361578823615788236157892345161713451617134576171361578923451617135034161071032933501416136157892120120614315618763517820635178201670149470053231700532311201206134516172345161723451617234516172700532416107145212012071120120711241207112032071120120710501417212012071345361821243207112012071120120711201206112012071) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_1025 : CutRow mo255 9 1025 12 := mixedCut (pos:=0x90184805242201203) (neg:=0xe0c43115251221c) (data:=fun _ => 0x714360870504646005046460752464600504646005046460050366600503666005036660050464600334517102012161) rfl (by decide +kernel)
theorem mo255B9 : CutRow mo255 9 0 1037 := (@joinRow mo255 9 0 449 588 (@joinRow mo255 9 0 210 239 (@joinRow mo255 9 0 18 192 mo255P9_0 (@joinRow mo255 9 18 96 96 mo255P9_18 mo255P9_114)) (@joinRow mo255 9 210 192 47 (@joinRow mo255 9 210 96 96 mo255P9_210 mo255P9_306) (@joinRow mo255 9 402 45 2 mo255P9_402 mo255P9_447))) (@joinRow mo255 9 449 288 300 (@joinRow mo255 9 449 96 192 mo255P9_449 (@joinRow mo255 9 545 96 96 mo255P9_545 mo255P9_641)) (@joinRow mo255 9 737 192 108 (@joinRow mo255 9 737 96 96 mo255P9_737 mo255P9_833) (@joinRow mo255 9 929 96 12 mo255P9_929 mo255P9_1025))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_0 : CutRow mo255 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1 : CutRow mo255 10 1 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_97 : CutRow mo255 10 97 91 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_188 : CutRow mo255 10 188 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_284 : CutRow mo255 10 284 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_380 : CutRow mo255 10 380 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_476 : CutRow mo255 10 476 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_572 : CutRow mo255 10 572 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_668 : CutRow mo255 10 668 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_764 : CutRow mo255 10 764 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_860 : CutRow mo255 10 860 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_956 : CutRow mo255 10 956 58 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1014 : CutRow mo255 10 1014 5 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1019 : CutRow mo255 10 1019 96 := mixedCut (pos:=0x1400324220a009028902406) (neg:=0x304c4616125122c4188e0541c) (data:=fun _ => 0x710815647108156458138141581381415873a141581381415813814158138141581381415815a1415813814158938141581381415813814158138141581381419301525258138141581381415813814158138141581381415813814158138141930152529303525258138141930152525813814158138141581381419301525278319430783194307831943078517430581381417831943078319430788194305813814178319430783194309301525258138141783194307831943078517430900172527831943078819430900172527831943090017252581381415873a14158938141581381415813814193035252083493202810302103310810283013205810814128301320033108107831943078819430785174301331081028349320581081411331081013310810133108105810814104301320211020217108156421102021033108105608576350104141501041410430132004301320317050216330643063506430501041410430132004301320043013202110202121102021) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1115 : CutRow mo255 10 1115 96 := mixedCut (pos:=0x880480d4024029409012) (neg:=0x1846218a5188c148984541c) (data:=fun _ => 0x163197302617204116718730162187302617204116718730163197302617204116218730261720411671873016718730261720411671873016718730167187301621873016718730167187305361345253013452530134525301345257037873570378735703787316718730163197305307345216718730167187301631973016718730261720411671873016718730167187301671873016319730167187305301345216718730167187301671873053613452530134522702716327027163270271632617204126172041269740412617204126172041261340412617204126172041268720412617204126172041841305752617204126172041261720418413057526172041280561632805616316718730167187301671873016319730167187302617204116718730167187301621873016718730261720411671873016718730167187301671873053013452261720415301345253613452530134521002126453013452535144525301345253024452530134521002126410021264) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1211 : CutRow mo255 10 1211 96 := mixedCut (pos:=0x11006500900a50091201203) (neg:=0x128c40e305849130988622a) (data:=fun _ => 0x787056522373046448078341788056527870565278725652787056522373046423730464497892632373046448078341485783414827834148078341480783414807834148098341787056524807834141731263787056527870565248078341417312637870565278705652480783414807834178705652787056522017213020172130201721302037213048078341201721309517913048078341480783414807834120405130201021302010213040013341201021302040513020102130201021304021334120302130206051302030213020302130203021304001334120102130204051302010213020102130400133412010213020405130201021304001334120102130204051302010213075704652400133414001334140013341400133414004634120405130201021304001334120102130203021302010213020102130201021304001334120102130201021302040513020102130201021304001334120102130203021302010213020102130400133412010213020102130) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1307 : CutRow mo255 10 1307 96 := mixedCut (pos:=0x605048491050242804806) (neg:=0xe18291308c588620e309282a) (data:=fun _ => 0x490676416760a9106760a9106760a9100860391008603910086039100860391009630820890360210860391008603910086039106760a9101763a8201763a8201763a820892380211763a8201763a8201763a8201763a8201763a820086039100860391009630820096308200860391008603910096308200963082008603910086039106760a9101763a8206760a910086039101763a8200963082009630820096308201603a0211763a820096308201763a8206760a9101763a82039634730397347303993273039634730397347303973473039634730396347305883173039634730400356414003564140035641400356414001564140035641586317305883173058631730396347304003564139634730397347304003564158631730397347302738657339634730588317303963473040035641396347303963473058631730588317305863173020302152473763635863173047376363400356414023564140435641400356414003564145341363203021522030215220102152) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1403 : CutRow mo255 10 1403 92 := mixedCut (pos:=0x110a0281204806028481203) (neg:=0x128c461244c4610e0e0622a) (data:=fun _ => 0x4018532043103010431030104360901040185320211020104315801051132320511323205113232030031421511323203053442130031421511323207134166330031421300314213009642140130320404353204013032040130320401303204043532040130320401853204013032040435320401853205203242152032421520324217938966379389663520324214013032040637320401303205203242140130320520324215113232051132320700142415113232051132320793896634013032040130320406373204315801040130320401303205203242151132320511323205203242151132320511323205203242152032421520324216234076452032421520324218435755252032421520324215203242152032421623407645203242152032421401303204013032040637320401303204013032040435320401303204013032052032421520324214310301040130320401303202110201021102010211020104013032021102010) rfl (by decide +kernel)
theorem mo255B10 : CutRow mo255 10 0 1495 := (@joinRow mo255 10 0 764 731 (@joinRow mo255 10 0 284 480 (@joinRow mo255 10 0 97 187 (@joinRow mo255 10 0 1 96 mo255P10_0 mo255P10_1) (@joinRow mo255 10 97 91 96 mo255P10_97 mo255P10_188)) (@joinRow mo255 10 284 192 288 (@joinRow mo255 10 284 96 96 mo255P10_284 mo255P10_380) (@joinRow mo255 10 476 96 192 mo255P10_476 (@joinRow mo255 10 572 96 96 mo255P10_572 mo255P10_668)))) (@joinRow mo255 10 764 255 476 (@joinRow mo255 10 764 192 63 (@joinRow mo255 10 764 96 96 mo255P10_764 mo255P10_860) (@joinRow mo255 10 956 58 5 mo255P10_956 mo255P10_1014)) (@joinRow mo255 10 1019 192 284 (@joinRow mo255 10 1019 96 96 mo255P10_1019 mo255P10_1115) (@joinRow mo255 10 1211 96 188 mo255P10_1211 (@joinRow mo255 10 1307 96 92 mo255P10_1307 mo255P10_1403)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_0 : CutRow mo255 11 0 14 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_14 : CutRow mo255 11 14 85 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_99 : CutRow mo255 11 99 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_195 : CutRow mo255 11 195 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_291 : CutRow mo255 11 291 10 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B11 : CutRow mo255 11 0 301 := (@joinRow mo255 11 0 99 202 (@joinRow mo255 11 0 14 85 mo255P11_0 mo255P11_14) (@joinRow mo255 11 99 96 106 mo255P11_99 (@joinRow mo255 11 195 96 10 mo255P11_195 mo255P11_291)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P12_0 : CutRow mo255 12 0 20 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B12 : CutRow mo255 12 0 20 := mo255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P13_0 : CutRow mo255 13 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B13 : CutRow mo255 13 0 1 := mo255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255T : mixedTables mo255 13 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo255 0 0)
  · exact (mixedEmpty mo255 1 0)
  · exact (mixedEmpty mo255 2 0)
  · exact (mixedEmpty mo255 3 0)
  · exact (mixedEmpty mo255 4 0)
  · exact (mixedEmpty mo255 5 0)
  · exact (mixedEmpty mo255 6 0)
  · exact (mixedEmpty mo255 7 0)
  · exact mo255B8
  · exact mo255B9
  · exact mo255B10
  · exact mo255B11
  · exact mo255B12
  · exact mo255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255G : graphValid mo255 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255R : Impossible false graph 13 eightInputs.toFinset := by
  rw [show graph = targetOf mo255 by decide +kernel]
  exact mixedRoot (g:=mo255) (top:=13) (i:=0) (before_sound K223 (known_down V223)) mo255G mo255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_8455

open PEqualNP.Outside.L_meta_8455 in
theorem PEqualNP.Outside.L_meta_8455 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7)) t → 14 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo255R g255R ⟨C,hf,by omega,heq⟩
