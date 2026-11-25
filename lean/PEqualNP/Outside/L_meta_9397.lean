import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_9397.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_9397
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
def graph : Sig := 0xfffffffffffffffffffefffefffefffefffffffffffffffffefefcfcfefefcfcfffefffefffefffeffeeffeeffeeffeefefefefefafafafaeeeeccccaaaa0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 6 && x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 6 &&& x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 6 &&& x 8)
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
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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

def nineInputs : List Sig := vars 511
def sampleNine (r : Row) (i : Fin 9) : Bool := bit r (nineInputs.getD i.val zero)
def nineEdge (x : Fin 9 → Bool) := (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 6 && x 8)
theorem nineTable : ∀ r : Row, bit r graph = nineEdge (sampleNine r) := by decide +kernel
theorem nineList : List.ofFn (fun i : Fin 9 => nineInputs.getD i.val zero) = nineInputs := rfl
theorem nineSampled (r : Row) : List.ofFn (sampleNine r) = nineInputs.map (bit r) := by
  rw [← nineList, List.map_ofFn]; rfl
theorem nineEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates nineInputs).getD i zero) =
      (C.wires (List.ofFn (sampleNine r))).getD i false := by
  rw [← b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), nineSampled]; rfl
def neighbor9 (i : Fin 9) : Nat := [4,5,6,7,0,1,0,0,1].getD i.val 0
def absentRow9 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor9 i)
def presentRow9 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor9 i))
set_option maxHeartbeats 1000000 in
theorem requiredInputs9 :
    (∀ i : Fin 9, bit (absentRow9 i) graph ≠ bit (presentRow9 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow9 i) (nineInputs.getD j.val zero) =
      bit (presentRow9 i) (nineInputs.getD j.val zero)) := by decide +kernel
theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = nineEdge) (small : C.size ≤ 13) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 12 else 13) ∧ Live u graph k nineInputs.toFinset := by
  have goalEq : (execute C.gates nineInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (nineEval C legal C.output r).trans ((congrFun computes (sampleNine r)).trans (nineTable r).symm)
  have len : C.gates.length ≤ 13 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 12 else 13) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false, fun _ => hn, ?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true, ite_false]; omega
    · refine ⟨true, by simp, ?_⟩
      push Not at hn
      obtain ⟨g, hg, hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq; exact absurd eq hx
      simp only [ite_true]; omega
  obtain ⟨u, mono, count⟩ := mode
  have out := get_rep (u:=u) (execute C.gates nineInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k, S, hk, run, sub⟩ := extract C.gates nineInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : nineInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ nineInputs) : ∃ i : Fin 9, nineInputs.getD i.val zero = a := by
    rw [← nineList] at ha; exact List.mem_ofFn.mp ha
  have eq : S = nineInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i, rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run nineInputs (nineInputs.getD i.val zero) sub (absentRow9 i) (presentRow9 i)
        (requiredInputs9.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := idx v hv
      apply requiredInputs9.2 i j
      rintro rfl; exact hn rfl
  exact ⟨u, k, hk.trans count, eq ▸ run⟩
theorem directSplit
    (m : ∀ k, k ≤ 13 → ¬Live false graph k nineInputs.toFinset)
    (s : ∀ k, k ≤ 12 → ¬Live true graph k nineInputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 nineEdge 13 := by
  rintro ⟨C, legal, small, computes⟩
  obtain ⟨mode, k, hk, run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low17 : Lower true (varsX 17) (graphGoal 17) 1 := count_low (m:=17) (hints:=4) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K17 := extendKnown [] 1 [(17,[]),(34,[84,16]),(65,[100,84]),(68,[100,84,32,16]),(129,[116,100,84]),(130,[116,100,84,16]),(136,[116,100,84,48,32,16]),(258,[132,116,100,84,16]),(260,[132,116,100,84,32,16]),(320,[132,64,112,100,80,48,32,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V17 : Known true K17 := extend_ok (m:=17) baseKnown low17 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low69 : Lower true (varsX 69) (graphGoal 69) 2 := count_low (m:=69) (hints:=1542) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K69 := extendKnown K17 2 [(69,[]),(81,[32,66,50,96]),(131,[118,33]),(137,[118,50]),(138,[118,50,16]),(145,[114,32,66,50,96]),(162,[114,32,82,66,50,96,16]),(193,[114,82,66,50,96]),(262,[134,118,16]),(290,[130,114,32,82,66,50,96,16]),(321,[130,114,82,66,50]),(322,[134,98,114,82,66,50,16]),(386,[32,128,114,82,66,50,96,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V69 : Known true K69 := extend_ok (m:=69) V17 low69 (by decide +kernel)
def g324Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0xd76bb5daed76bb5daed76bb5daed76bb5daed7,0x148a45229148a45229148a45229148a4522914),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x6db6db6db6db6db6db6db6db6db6db6db6db6d,0xa150a8542a150a8542a150a8542a150a8542a1),(0x0,0x0),(0xbadd6eb75badd6eb75badd6eb75badd6eb75ba,0x4a25128944a25128944a25128944a25128944a)]
def g324C : List ColumnInfo := []
def g324A : List (List Nat) := [[],[134],[98],[98,130],[130,98],[130]]
def g324D3 (_ : Nat) : Nat := 0x7
def g324L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g324D3)
  | _ => emptyPacking
def g324I (_ _ : Nat) : Option (Nat × Nat) := none
def g324 : Forest := ⟨324,3,fun i => g324Y[i]?.getD (0,0),g324C,g324A,g324L,g324I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g324P3_0 : block g324 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g324B3 : block g324 3 0 1=true := g324P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g324T : checkedTables g324 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g324 0 0 0 = true)
  · exact (rfl : block g324 1 0 0 = true)
  · exact (rfl : block g324 2 0 0 = true)
  · exact g324B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g324G : graphValid g324 (boundsBefore K69) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low324 : Lower true (varsX 324) (graphGoal 324) 4 := lower_forest (g:=g324) (i:=0) (hints:=8623490560) (before_sound K69 V69) g324G g324T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K324 := extendKnown K69 4 [(324,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V324 : Known true K324 := extend_ok (m:=324) V69 low324 (by decide +kernel)
def g85Y : Array (Bits × Bits) := #[(0xc7bf63dfb1efd8f7ec7bf63dfb1efd8f7ec7bf,0x1295094a84a54252a1295094a84a54252a1295),(0x0,0x0),(0x39c09ce04e702738139c09ce04e702738139c0,0xbb8c5dc62ee317718bb8c5dc62ee317718bb8c),(0x0,0x0),(0x418f20c79063c831e418f20c79063c831e418f,0xe50af2857942bca15e50af2857942bca15e50a),(0x0,0x0),(0xbe70df386f9c37ce1be70df386f9c37ce1be70,0x4460a2305118288c14460a2305118288c14460),(0x0,0x0),(0x0,0x0)]
def g85C : List ColumnInfo := []
def g85A : List (List Nat) := [[],[96,66]]
def g85D3 (_ : Nat) : Nat := 0xf
def g85L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g85D3)
  | _ => emptyPacking
def g85I (_ _ : Nat) : Option (Nat × Nat) := none
def g85 : Forest := ⟨85,3,fun i => g85Y[i]?.getD (0,0),g85C,g85A,g85L,g85I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P3_0 : block g85 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B3 : block g85 3 0 1=true := g85P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85T : checkedTables g85 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g85 0 0 0 = true)
  · exact (rfl : block g85 1 0 0 = true)
  · exact (rfl : block g85 2 0 0 = true)
  · exact g85B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85G : graphValid g85 (boundsBefore K324) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 4 := lower_forest (g:=g85) (i:=0) (hints:=1540) (before_sound K324 V324) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K324 4 [(85,[]),(147,[118,33]),(153,[118,50]),(163,[118,84,16,32]),(170,[118,84,50,16]),(195,[100,116,84,33]),(197,[116,84]),(201,[100,116,84,50]),(294,[134,118,84,16]),(323,[128,112,80,16,65,32]),(337,[132,116,66,82,50,96]),(354,[128,64,116,82,50,96,16]),(387,[100,134,116,84,16,32]),(390,[134,116,84,16]),(394,[100,134,116,84,50,16]),(449,[66,130,116,82,50,96]),(450,[98,130,116,82,50,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V324 low85 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low325 : Lower true (varsX 325) (graphGoal 325) 5 := plain_low (m:=325) (hints:=8589936134) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=325) (cap:=4) (before_sound K85 V85) (1,0,324,0,4) (by decide +kernel) (by decide +kernel))
def K325 := extendKnown K85 5 [(325,[]),(326,[134,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V325 : Known true K325 := extend_ok (m:=325) V85 low325 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 5 := plain_low (m:=155) (hints:=28788) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=155) (cap:=4) (before_sound K325 V325) (2,0,153,0,4) (by decide +kernel) (by decide +kernel))
def K155 := extendKnown K325 5 [(155,[]),(171,[84,16]),(203,[100,84]),(211,[99,83,65,112]),(213,[48,99,83,65,33,112]),(217,[99,49,67,81,33,112]),(395,[132,100,84,16]),(419,[48,128,49,96,83,113,64]),(422,[128,49,96,83,64,113,32]),(426,[131,16,99,67,80,113,32]),(465,[48,132,65,99,81,33,112]),(482,[48,67,16,132,99,80,113,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V325 low155 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 5 := plain_low (m:=179) (hints:=1048660) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=179) (cap:=4) (before_sound K155 V155) (32,0,147,0,4) (by decide +kernel) (by decide +kernel))
def K179 := extendKnown K155 5 [(179,[]),(199,[97,49,50,82,65,112]),(205,[16,97,49,83,65,33,112]),(227,[84,100,16]),(339,[128,112,96,80,64,16]),(355,[135,96,64]),(391,[16,128,96,48,50,82,113,64]),(398,[128,96,48,83,64,113,32]),(403,[133,101]),(457,[133,97,65,49,33,112]),(458,[16,80,133,96,64,48,113,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V155 low179 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low460 : Lower true (varsX 460) (graphGoal 460) 6 := plain_low (m:=460) (hints:=9428825600) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=460) (cap:=5) (before_sound K179 V179) (0,128,324,8,5) (by decide +kernel) (by decide +kernel))
def K460 := extendKnown K179 6 [(460,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V460 : Known true K460 := extend_ok (m:=460) V179 low460 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low327 : Lower true (varsX 327) (graphGoal 327) 6 := plain_low (m:=327) (hints:=4294968966) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=327) (cap:=5) (before_sound K460 V460) (2,0,325,0,5) (by decide +kernel) (by decide +kernel))
def K327 := extendKnown K460 6 [(327,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V327 : Known true K327 := extend_ok (m:=327) V460 low327 (by decide +kernel)
def g341Y : Array (Bits × Bits) := #[(0x580d960676dc2c06cb033b6e160365819db70b,0x4921168cc3c424908b4661e2124845a330f109),(0x0,0x0),(0xa0f079e58b0dd0783cf2c586e83c1e7962c374,0x23041c21eb0d11820e10f58688c107087ac344),(0x0,0x0),(0x1802a12370cc0c015091b8660600a848dc3303,0x16dea9733c080b6f54b99e0405b7aa5ccf0202),(0x0,0x0),(0x477f57388c33a3bfab9c4619d1dfd5ce230ce8,0x49081000412824840800209412420400104a0),(0x0,0x0),(0xa78328df03a253c1946f81d129e0ca37c0e894,0x806b22de10e04035916f0870201ac8b7843810)]
def g341C : List ColumnInfo := [(256,0,85,0,4),(0,16,324,1,5),(16,0,325,0,5),(4,0,337,0,4),(1,16,324,0,4)]
def g341A : List (List Nat) := [[],[130]]
def g341D4 (_ : Nat) : Nat := 0x4fd5131
def g341D5 (_ : Nat) : Nat := 0x60908400e140fd41ff31fd31
def g341H5 (_ : Nat) : Nat := 0x4800
def g341D6 (_ : Nat) : Nat := 0x20e09f
def g341H6 (_ : Nat) : Nat := 0x1af200038000004d0070000
def g341L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g341D4)
  | 5 => (3,1,3,0,0,5,0,g341D5)
  | 6 => (1,0,3,0,0,0,0,g341D6)
  | _ => emptyPacking
def g341I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 5 0 1 g341H5
  | 6 => lookupWord 1 17 0 7 2 1 g341H6
  | _ => fun _ => none
def g341 : Forest := ⟨341,6,fun i => g341Y[i]?.getD (0,0),g341C,g341A,g341L,g341I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P4_0 : block g341 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B4 : block g341 4 0 1=true := g341P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P5_0 : block g341 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B5 : block g341 5 0 3=true := g341P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P6_0 : block g341 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B6 : block g341 6 0 1=true := g341P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341T : checkedTables g341 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g341 0 0 0 = true)
  · exact (rfl : block g341 1 0 0 = true)
  · exact (rfl : block g341 2 0 0 = true)
  · exact (rfl : block g341 3 0 0 = true)
  · exact g341B4
  · exact g341B5
  · exact g341B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341G : graphValid g341 (boundsBefore K327) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low341 : Lower true (varsX 341) (graphGoal 341) 7 := lower_forest (g:=g341) (i:=0) (hints:=8589936132) (before_sound K327 V327) g341G g341T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K341 := extendKnown K327 7 [(341,[]),(358,[134,84,16]),(453,[116,84]),(454,[134,116,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V341 : Known true K341 := extend_ok (m:=341) V327 low341 (by decide +kernel)
def g451Y : Array (Bits × Bits) := #[(0xb140729817db6280e5302fb6c501ca605f6d8a,0x815c801c925902b9003924b20572007249640a),(0xc2a789679305854f12cf260b0a9e259e4c1615,0x8289444d83130512889b06260a2511360c4c14),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x1d1836116b363a306c22d66c7460d845acd8e8,0x1803566129863006acc2530c600d5984a618c0),(0x2260caef64cc44c195dec99889832bbd933113,0x20223ba26ca440447744d9488088ee89b29101),(0xcc9f0d00fc61993e1a01f8c3327c3403f18664,0x4414a992546888295324a8d11052a64951a220)]
def g451C : List ColumnInfo := [(128,0,323,0,4),(2,0,449,0,4),(1,0,450,0,4),(64,0,387,0,4),(256,0,195,0,4)]
def g451A : List (List Nat) := [[],[129,118],[16,134],[16,96,112,128],[96,135],[96,113,128,16],[112,97],[112,129,96,97],[128,16,97,118],[128,113]]
def g451D4 (_ : Nat) : Nat := 0x57d4d10
def g451D5 (_ : Nat) : Nat := 0x1a0fd20fd10
def g451H5 (_ : Nat) : Nat := 0x400000
def g451D6 (_ : Nat) : Nat := 0x20688bf
def g451H6 (_ : Nat) : Nat := 0x7840040002080000870000143d332c8b2a0000000000011c0000000000000000400
def g451L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g451D4)
  | 5 => (2,1,3,0,0,4,0,g451D5)
  | 6 => (1,0,3,0,0,0,0,g451D6)
  | _ => emptyPacking
def g451I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 8 0 4 g451H5
  | 6 => lookupWord 3 29 5 9 1 4 g451H6
  | _ => fun _ => none
def g451 : Forest := ⟨451,6,fun i => g451Y[i]?.getD (0,0),g451C,g451A,g451L,g451I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451P4_0 : block g451 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g451B4 : block g451 4 0 1=true := g451P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451P5_0 : block g451 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g451B5 : block g451 5 0 2=true := g451P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451P6_0 : block g451 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g451B6 : block g451 6 0 1=true := g451P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451T : checkedTables g451 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g451 0 0 0 = true)
  · exact (rfl : block g451 1 0 0 = true)
  · exact (rfl : block g451 2 0 0 = true)
  · exact (rfl : block g451 3 0 0 = true)
  · exact g451B4
  · exact g451B5
  · exact g451B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g451G : graphValid g451 (boundsBefore K341) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low451 : Lower true (varsX 451) (graphGoal 451) 7 := lower_forest (g:=g451) (i:=0) (hints:=4294967414) (before_sound K341 V341) g451G g451T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K451 := extendKnown K341 7 [(451,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V451 : Known true K451 := extend_ok (m:=451) V341 low451 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 6 := plain_low (m:=119) (hints:=1050196) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=119) (cap:=5) (before_sound K451 V451) (0,2,85,32,5) (by decide +kernel) (by decide +kernel))
def K119 := extendKnown K451 6 [(119,[]),(238,[101,84,116,33,16,48]),(311,[134,118,84,16]),(413,[101,134,117,33,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V451 low119 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[(0x3e1e60fce40ebe458b003e1e60fce40ebe458b,0x4a4740fba422a64109294a4740fba422a64109),(0xc1e1e1839a1031f85407c1e1e1839a1031f854,0xc625e187764030e80418c625e187764030e804),(0x0,0x0),(0x1f4001e14d8220f800001f4001e14d8220,0xdeea67dd21e00d9f007bdeea67dd21e00d9f00),(0x1a22b47e087e050300001a22b47e087e0503,0xb5b8b2045a8c580402d6b5b8b2045a8c580402),(0x1e24403980983d8140001e24403980983d814,0x39da0c30891b831010e739da0c30891b831010),(0x0,0x0),(0xfe059f4803f7c022e8fffe059f4803f7c022e8,0x2110180000154000e0842110180000154000e0),(0x0,0x0)]
def g187C : List ColumnInfo := [(17,0,170,0,4),(2,32,153,0,4),(8,0,179,0,5),(0,16,170,1,5),(32,0,155,0,5)]
def g187A : List (List Nat) := [[],[16,84]]
def g187D5 (_ : Nat) : Nat := 0x1ef52
def g187D6 (_ : Nat) : Nat := 0x468817f
def g187H6 (_ : Nat) : Nat := 0x12
def g187L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g187D5)
  | 6 => (1,0,3,0,0,0,0,g187D6)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 0 1 g187H6
  | _ => fun _ => none
def g187 : Forest := ⟨187,6,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 1=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 1=true := g187P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact g187B5
  · exact g187B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 7 := lower_forest (g:=g187) (i:=0) (hints:=1077332) (before_sound K119 V119) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K119 7 [(187,[]),(215,[97,49,50,82,65,112]),(221,[16,97,49,83,65,33,112]),(235,[84,100,16]),(411,[133,101]),(423,[16,128,96,50,82,113,64]),(430,[128,96,83,64,113,32]),(473,[133,67,97,33,112]),(490,[16,80,83,131,67,96,113,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V119 low187 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 6 := plain_low (m:=207) (hints:=30326) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=207) (cap:=5) (before_sound K187 V187) (8,0,199,0,5) (by decide +kernel) (by decide +kernel))
def K207 := extendKnown K187 6 [(207,[]),(243,[50,33,83,66,97,112]),(399,[134,16]),(435,[48,128,49,83,66,113,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V187 low207 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(0xe712c3e0f82a2e02dce2587c1f0545c05b9c4b,0xe700cc6318f886a29ce0198c631f10d4539c03),(0x7ca53c0007c5d9f10f94a78000f8bb3e21f294,0x548404a529619a710a908094a52c334e215210),(0x1948001f0010100c63290003e00202018c6520,0x19401d6b5ada0146432803ad6b5b4028c86500),(0x0,0x0),(0x0,0x0),(0xfa05000007c061f81f40a00000f80c3f03e814,0xaa013b5ad68465889540276b5ad08cb112a804),(0x64a401ff8187e1d20c94803ff030fc3a41929,0xa2294a50178192001445294a02f03240028),(0x81b0bfe000278007f03617fc0004f000fe06c2,0x303318c60600046006066318c0c0008c00c0),(0x0,0x0)]
def g231C : List ColumnInfo := [(0,4,163,64,5),(4,0,227,0,5),(32,0,199,0,5),(0,32,197,2,5)]
def g231A : List (List Nat) := [[],[112,97,82]]
def g231D6 (_ : Nat) : Nat := 0xe413f
def g231L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g231D6)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,6,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 1=true := g231P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact g231B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 7 := lower_forest (g:=g231) (i:=0) (hints:=1050198) (before_sound K207 V207) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K207 7 [(231,[]),(371,[135,66,50,96]),(407,[134,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V207 low231 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low343 : Lower true (varsX 343) (graphGoal 343) 8 := plain_low (m:=343) (hints:=4294968964) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=343) (cap:=7) (before_sound K231 V231) (2,0,341,0,7) (by decide +kernel) (by decide +kernel))
def K343 := extendKnown K231 8 [(343,[]),(359,[134,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V343 : Known true K343 := extend_ok (m:=343) V231 low343 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low459 : Lower true (varsX 459) (graphGoal 459) 8 := plain_low (m:=459) (hints:=4294996086) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=459) (cap:=7) (before_sound K343 V343) (8,0,451,0,7) (by decide +kernel) (by decide +kernel))
def K459 := extendKnown K343 8 [(459,[]),(467,[97,96,67,129,112]),(483,[16,128,83,67,113,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V459 : Known true K459 := extend_ok (m:=459) V343 low459 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low461 : Lower true (varsX 461) (graphGoal 461) 8 := plain_low (m:=461) (hints:=8589964806) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=461) (cap:=7) (before_sound K459 V459) (8,0,453,0,7) (by decide +kernel) (by decide +kernel))
def K461 := extendKnown K459 8 [(461,[]),(462,[134,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V461 : Known true K461 := extend_ok (m:=461) V459 low461 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low469 : Lower true (varsX 469) (graphGoal 469) 8 := plain_low (m:=469) (hints:=8589936132) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=469) (cap:=7) (before_sound K461 V461) (128,0,341,0,7) (by decide +kernel) (by decide +kernel))
def K469 := extendKnown K461 8 [(469,[]),(486,[134,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V469 : Known true K469 := extend_ok (m:=469) V461 low469 (by decide +kernel)
def g455Y : Array (Bits × Bits) := #[(0x98ac18ae72148e00018f08213158315ce4291c,0xd8ae9a2c4210840a4c314039b15d3458842108),(0x241ce2499ca21003e00d28a04839c49339442,0x279eec418482018c89102aa04f3dd88309040),(0xf313215bc8015087c0700107e62642b79002a1,0xf3936512c11540285813002be726ca25822a80),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xacb709c11ce0c2f8007f2655596e138239c185,0x4000c11cc002d1a2840ac400800182398005),(0x4489513e3dc0d000780196a08912a27c7b81a,0x25000113a1840965334e9d444a000227430812),(0x5f00623c2623307ff800e7d0be00c4784c4660,0xc041028222210060568d51018082050444420)]
def g455C : List ColumnInfo := [(64,0,391,0,5),(256,0,199,0,5),(4,0,451,0,7),(1,0,454,0,7),(2,0,453,0,7),(0,128,324,3,6),(128,0,327,0,6)]
def g455A : List (List Nat) := [[],[16,134]]
def g455D5 (_ : Nat) : Nat := 0x4ef7259653
def g455D6 (_ : Nat) : Nat := 0x20440800084006c85b2c0bf59653fbd8953bbd8953bb58853be58053
def g455H6 (_ : Nat) : Nat := 0xc0
def g455D7 (_ : Nat) : Nat := 0x19442b2cc85601acb1d946b2c0c8909807f94ffaa7fc53
def g455H7 (_ : Nat) : Nat := 0xe1b2a450d300f80002
def g455D8 (_ : Nat) : Nat := 0x5c9c17f
def g455H8 (_ : Nat) : Nat := 0xd800800000000000000c401880
def g455L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g455D5)
  | 6 => (5,2,3,0,0,6,0,g455D6)
  | 7 => (3,1,3,0,0,7,0,g455D7)
  | 8 => (1,0,3,0,0,0,0,g455D8)
  | _ => emptyPacking
def g455I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 0 1 g455H6
  | 7 => lookupWord 2 11 4 8 3 1 g455H7
  | 8 => lookupWord 1 17 0 7 2 1 g455H8
  | _ => fun _ => none
def g455 : Forest := ⟨455,8,fun i => g455Y[i]?.getD (0,0),g455C,g455A,g455L,g455I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P5_0 : block g455 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B5 : block g455 5 0 1=true := g455P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P6_0 : block g455 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P6_3 : block g455 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B6 : block g455 6 0 5=true := (@block_merge g455 6 0 3 2 g455P6_0 g455P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P7_0 : block g455 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B7 : block g455 7 0 3=true := g455P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P8_0 : block g455 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B8 : block g455 8 0 1=true := g455P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455T : checkedTables g455 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g455 0 0 0 = true)
  · exact (rfl : block g455 1 0 0 = true)
  · exact (rfl : block g455 2 0 0 = true)
  · exact (rfl : block g455 3 0 0 = true)
  · exact (rfl : block g455 4 0 0 = true)
  · exact g455B5
  · exact g455B6
  · exact g455B7
  · exact g455B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455G : graphValid g455 (boundsBefore K469) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low455 : Lower true (varsX 455) (graphGoal 455) 9 := lower_forest (g:=g455) (i:=0) (hints:=4294968950) (before_sound K469 V469) g455G g455T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K455 := extendKnown K469 9 [(455,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V455 : Known true K455 := extend_ok (m:=455) V469 low455 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 8 := plain_low (m:=223) (hints:=30324) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=223) (cap:=7) (before_sound K455 V455) (2,0,221,0,7) (by decide +kernel) (by decide +kernel))
def K223 := extendKnown K455 8 [(223,[]),(251,[49,67,82,97,112]),(431,[134,84,16]),(443,[48,128,49,50,67,82,113,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V455 low223 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 8 := plain_low (m:=239) (hints:=1078870) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=239) (cap:=7) (before_sound K223 V223) (8,0,231,0,7) (by decide +kernel) (by decide +kernel))
def K239 := extendKnown K223 8 [(239,[]),(247,[67,82,97,112]),(415,[134,84,16]),(439,[16,128,50,67,82,113,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g375Y : Array (Bits × Bits) := #[(0x3fc07c200602021023ed65b10217fc526505,0x51515120220200425022fdc5a1129372124401),(0xc0003f8040d3c900032184826e0199c2ad882a,0xc4c4c48800c149000621c5aa4c01b1d60d0022),(0x3fc00003ff282061be8c121c09fd60007802d0,0xc3c3c3840016010092a393fe88d8600079e240),(0x0,0x0),(0x7c8014130580038160564603bc526005,0xaeaeaedc84749b05809500205644448c402004),(0x3f8200178d082122089036280242ad800a,0x3b3b3b76081e848829422a5032a80a20a08008),(0x3fffc003ee0074be4c5c6e1588756401841550,0xc0c0c18108176000c44000000250401840110),(0x0,0x0),(0xc000000111e874dff2d0100a41889809021aa0,0x30303063ee2800cf6118000101020808021880)]
def g375C : List ColumnInfo := [(64,0,311,0,6),(4,0,371,0,7),(0,32,341,2,8),(32,0,343,0,8),(0,16,358,1,8),(16,0,359,0,8),(256,0,119,0,6),(17,0,358,0,7),(2,32,341,0,7)]
def g375A : List (List Nat) := [[],[16,84,134]]
def g375D6 (_ : Nat) : Nat := 0xc60e6d65d8b529ef825d952e6d6558952
def g375D7 (_ : Nat) : Nat := 0x8200190200208000008200000208200d967a6a301ae99662e59e9a89b1a59981755d514539211508f0d8843c01df59552efccaa95fd7654affbb2a5fbd8b52efacba95fd76d4afeb90cbfb1c965fdee4b2dff72596feb94cbfb58952bfaed32ded72196fcb80cb7bdc965
def g375H7 (_ : Nat) : Nat := 0x8400098
def g375D8 (_ : Nat) : Nat := 0x1820c4a773d2a500c1c4a77a549307129dc07a54a34c01c5cf4a926a003844a7727467998cc03fe65ff597fc65ffd4bfd52
def g375H8 (_ : Nat) : Nat := 0xa2c000000000385c20000000000000000006ae8400a074040052400b35f0000000030c0000053c0000000b861060f8e00246a28000000040000000009100
def g375D9 (_ : Nat) : Nat := 0x6830e2ff
def g375H9 (_ : Nat) : Nat := 0x33122858001d30c02e68800
def g375L : Nat → Packing
  | 6 => (3,3,4,0,0,4,0,g375D6)
  | 7 => (17,2,4,0,0,8,0,g375D7)
  | 8 => (5,1,4,0,0,8,0,g375D8)
  | 9 => (1,0,4,0,0,0,0,g375D9)
  | _ => emptyPacking
def g375I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 7 2 1 g375H7
  | 8 => lookupWord 6 47 6 10 5 1 g375H8
  | 9 => lookupWord 2 17 5 8 3 1 g375H9
  | _ => fun _ => none
def g375 : Forest := ⟨375,9,fun i => g375Y[i]?.getD (0,0),g375C,g375A,g375L,g375I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P6_0 : block g375 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B6 : block g375 6 0 3=true := g375P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P7_0 : block g375 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P7_3 : block g375 7 3 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B7 : block g375 7 0 17=true := (@block_merge g375 7 0 3 14 g375P7_0 g375P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P8_0 : block g375 8 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B8 : block g375 8 0 5=true := g375P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P9_0 : block g375 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B9 : block g375 9 0 1=true := g375P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375T : checkedTables g375 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g375 0 0 0 = true)
  · exact (rfl : block g375 1 0 0 = true)
  · exact (rfl : block g375 2 0 0 = true)
  · exact (rfl : block g375 3 0 0 = true)
  · exact (rfl : block g375 4 0 0 = true)
  · exact (rfl : block g375 5 0 0 = true)
  · exact g375B6
  · exact g375B7
  · exact g375B8
  · exact g375B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375G : graphValid g375 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low375 : Lower true (varsX 375) (graphGoal 375) 10 := lower_forest (g:=g375) (i:=0) (hints:=4296017492) (before_sound K239 V239) g375G g375T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K375 := extendKnown K239 10 [(375,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V375 : Known true K375 := extend_ok (m:=375) V239 low375 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low475 : Lower true (varsX 475) (graphGoal 475) 9 := plain_low (m:=475) (hints:=4294996084) (cap:=8) (by decide +kernel) (cut_root (u:=true) (m:=475) (cap:=8) (before_sound K375 V375) (16,0,459,0,8) (by decide +kernel) (by decide +kernel))
def K475 := extendKnown K375 9 [(475,[]),(491,[134,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V475 : Known true K475 := extend_ok (m:=475) V375 low475 (by decide +kernel)
def g477Y : Array (Bits × Bits) := #[(0x4a08aab0004260c03504846c3464bc3e79204b,0x2020180004420c0800480543024183a510049),(0x0,0x0),(0x477612004e95801f03736313da09400bc5f130,0x400022000034009b437beb109e294008c1b110),(0x92890205537a0f25c28a188683924660800a84,0xda9c06c85f726e2782ae11062a107620000280),(0x408102202042e000180104284433b434112003,0xf1d11a2cea8ac5207a7b57a8c653a58504ba02),(0x0,0x0),(0xad08d54afc0592d70a7530cc104003c1225540,0x1808d4057d01800410001088004002c1204400),(0x3081f89501b91d20e5c8fc81a39e0a48880a8c,0x2061f8378089111865506ea1818a0040880804),(0xa276455ab2801f0808024353488dc192468430,0xa2f709fa82ca7f600c80004341848916160020)]
def g477C : List ColumnInfo := [(256,0,221,0,7),(0,16,460,1,7),(0,8,341,128,8),(8,0,469,0,8),(1,16,460,0,6),(128,8,341,0,7),(16,0,461,0,8),(64,4,153,256,5),(4,0,473,0,7),(4,256,153,64,5),(64,256,153,4,5),(64,0,413,0,6),(0,4,153,320,6),(0,256,153,68,6),(68,256,153,0,4),(260,0,217,0,5)]
def g477A : List (List Nat) := [[],[130]]
def g477D6 (_ : Nat) : Nat := 0x309dd87d0630adf8650630
def g477D7 (_ : Nat) : Nat := 0x460900410500751f6cf2175133c84cd6a7423c02feb8683f758630fbe83187dd418c27fbb283775d230
def g477H7 (_ : Nat) : Nat := 0x8000019000000000
def g477D8 (_ : Nat) : Nat := 0x15381ec25a72253582164b4e4482ae25a724309036a862c969c8a0550a25a723920a96d29a4e44146556679130442b22605ab48de0b8429343e00ff587ff41ff507ff40ff503fd10f750fde30
def g477H8 (_ : Nat) : Nat := 0x1c400000001cc00005000ca952e6800800080
def g477D9 (_ : Nat) : Nat := 0xac64903ff
def g477H9 (_ : Nat) : Nat := 0xf000053ed5a4156a0cb0af9c800e0
def g477L : Nat → Packing
  | 6 => (2,3,4,0,0,3,0,g477D6)
  | 7 => (6,2,4,0,0,7,0,g477D7)
  | 8 => (8,1,4,0,0,9,0,g477D8)
  | 9 => (1,0,4,0,0,0,0,g477D9)
  | _ => emptyPacking
def g477I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 6 1 1 g477H7
  | 8 => lookupWord 2 17 5 8 3 1 g477H8
  | 9 => lookupWord 3 17 5 8 3 1 g477H9
  | _ => fun _ => none
def g477 : Forest := ⟨477,9,fun i => g477Y[i]?.getD (0,0),g477C,g477A,g477L,g477I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g477P6_0 : block g477 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g477B6 : block g477 6 0 2=true := g477P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g477P7_0 : block g477 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g477P7_2 : block g477 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g477B7 : block g477 7 0 6=true := (@block_merge g477 7 0 2 4 g477P7_0 g477P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g477P8_0 : block g477 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g477P8_2 : block g477 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g477B8 : block g477 8 0 8=true := (@block_merge g477 8 0 2 6 g477P8_0 g477P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g477P9_0 : block g477 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g477B9 : block g477 9 0 1=true := g477P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g477T : checkedTables g477 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g477 0 0 0 = true)
  · exact (rfl : block g477 1 0 0 = true)
  · exact (rfl : block g477 2 0 0 = true)
  · exact (rfl : block g477 3 0 0 = true)
  · exact (rfl : block g477 4 0 0 = true)
  · exact (rfl : block g477 5 0 0 = true)
  · exact g477B6
  · exact g477B7
  · exact g477B8
  · exact g477B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g477G : graphValid g477 (boundsBefore K475) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low477 : Lower true (varsX 477) (graphGoal 477) 10 := lower_forest (g:=g477) (i:=0) (hints:=8589964804) (before_sound K475 V475) g477G g477T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K477 := extendKnown K475 10 [(477,[]),(494,[134,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V477 : Known true K477 := extend_ok (m:=477) V475 low477 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low499 : Lower true (varsX 499) (graphGoal 499) 9 := plain_low (m:=499) (hints:=4296015956) (cap:=8) (by decide +kernel) (cut_root (u:=true) (m:=499) (cap:=8) (before_sound K477 V477) (16,0,483,0,8) (by decide +kernel) (by decide +kernel))
def K499 := extendKnown K477 9 [(499,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V499 : Known true K499 := extend_ok (m:=499) V477 low499 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low463 : Lower true (varsX 463) (graphGoal 463) 10 := plain_low (m:=463) (hints:=4294997622) (cap:=9) (by decide +kernel) (cut_root (u:=true) (m:=463) (cap:=9) (before_sound K499 V499) (8,0,455,0,9) (by decide +kernel) (by decide +kernel))
def K463 := extendKnown K499 10 [(463,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V463 : Known true K463 := extend_ok (m:=463) V499 low463 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low471 : Lower true (varsX 471) (graphGoal 471) 10 := plain_low (m:=471) (hints:=4294968948) (cap:=9) (by decide +kernel) (cut_root (u:=true) (m:=471) (cap:=9) (before_sound K463 V463) (16,0,455,0,9) (by decide +kernel) (by decide +kernel))
def K471 := extendKnown K463 10 [(471,[]),(487,[134,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V471 : Known true K471 := extend_ok (m:=471) V463 low471 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0x442104cf77ff010008518d80933ee4e3100669,0x640104cc670a01000050800010346443100621),(0x794641b0080c7fff00a0103e2c00db07696806,0x394640b08c0ccfa980a012a62510d101414802),(0x88d43270880380c0e5a0400140c71208809110,0x98503278ca03f0c8b160440b002e1200801100),(0x3198a0000000030371e2240000109d0060080,0x4b592009375f5330971207d400410dd8f40060),(0x20000037ff000008003c815f3ee0c0000069,0xbf4da1310f5f6fd9f233ec14f0a808ce7b848),(0xc808840430007ffb4208001e2e003b03602806,0xc408850431c03056420880581a002a02202004),(0x86c5788fc8008003cda44121e0c10008909310,0x286480300300e034c860120e0c10008008010),(0x339adf7000000004325ffa60008004340f4480,0xa09b0000000004200d6800008000240a0080),(0x0,0x0)]
def g255C : List ColumnInfo := [(0,4,187,64,8),(4,0,251,0,8),(16,0,239,0,8),(1,16,238,0,6),(128,8,119,0,6),(32,0,223,0,8),(0,32,221,2,8),(34,0,221,0,7),(8,0,247,0,8),(64,4,187,0,7)]
def g255A : List (List Nat) := [[],[112,97,82,67]]
def g255D6 (_ : Nat) : Nat := 0x139d98dce40
def g255D7 (_ : Nat) : Nat := 0x30bbd87903e7dce40
def g255H7 (_ : Nat) : Nat := 0x300
def g255D8 (_ : Nat) : Nat := 0x10d0480b9b62e38c07bdaa41ca3022bae01ff5c3df207dd30
def g255H8 (_ : Nat) : Nat := 0x378000
def g255D9 (_ : Nat) : Nat := 0x18d24a005c9ff
def g255H9 (_ : Nat) : Nat := 0xe8a8001f24390000000
def g255L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g255D6)
  | 7 => (2,2,4,0,0,3,0,g255D7)
  | 8 => (3,1,4,0,0,7,0,g255D8)
  | 9 => (1,0,4,0,0,0,0,g255D9)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 5 0 1 g255H7
  | 8 => lookupWord 1 5 0 6 1 1 g255H8
  | 9 => lookupWord 1 11 0 7 2 1 g255H9
  | _ => fun _ => none
def g255 : Forest := ⟨255,9,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P6_0 : block g255 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B6 : block g255 6 0 1=true := g255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 2=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_2 : block g255 8 2 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 3=true := (@block_merge g255 8 0 2 1 g255P8_0 g255P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 1=true := g255P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact g255B6
  · exact g255B7
  · exact g255B8
  · exact g255B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K471) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (varsX 255) (graphGoal 255) 10 := lower_forest (g:=g255) (i:=0) (hints:=1078868) (before_sound K471 V471) g255G g255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K255 := extendKnown K471 10 [(255,[]),(447,[134,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V255 : Known true K255 := extend_ok (m:=255) V471 low255 (by decide +kernel)
def g507Y : Array (Bits × Bits) := #[(0x463540801b558402881cf45bd419ce5400a8d1,0x403480a013058000001cc44b9401865000a051),(0x28408a29442a6ba1728445218488e37b8e542a,0x40238a29002407a1529444210488c21b045422),(0x0,0x0),(0x998a385030a0010ca42b0a2010620080400304,0xcfc36dd231ad011caa0c8421d78f0188c49910),(0x60102950855a4028091100a5419c400000891,0x9ec9765f4c7026d28181391468dc618b680e80),(0x3a84002884636088748000238000015888140a,0xba840502c7436808240000c6e07315c0880008),(0x40246506bf0052d149424c942b041800318040,0x710aac1252f558020a102a001800100000),(0x919a3a5060801a6f076baa4000622085426304,0x100810004000184205632a0000602004020204),(0x845885c7808811500164118c2b841222350020,0xa55804c4008880000160118c01040020210000)]
def g507C : List ColumnInfo := [(32,0,475,0,9),(0,32,473,2,8),(16,0,491,0,9),(1,16,490,0,7),(2,32,473,0,7),(8,176,320,3,3),(16,160,320,11,4),(48,11,0,448,2),(136,0,371,0,7),(0,80,170,257,6),(40,400,0,67,2),(0,16,490,1,8),(64,0,443,0,8),(40,208,0,259,2),(8,3,0,496,4),(0,8,371,128,8),(42,0,465,0,5),(9,16,482,0,5),(8,0,499,0,9),(128,8,371,0,7),(0,288,153,66,6),(34,0,473,0,7),(34,8,337,128,5),(0,176,320,11,4),(16,11,0,480,3),(320,0,187,0,7),(64,16,426,1,6),(32,400,0,75,3),(256,0,251,0,8),(337,0,170,0,4),(2,288,153,64,5),(1,24,354,128,5),(0,90,0,417,3),(1,80,170,256,5),(8,289,0,210,3),(48,192,0,267,3),(81,0,426,0,5),(129,24,354,0,4)]
def g507A : List (List Nat) := [[],[16,84,134]]
def g507D6 (_ : Nat) : Nat := 0x30ce366174d8a30ae36a36290630
def g507D7 (_ : Nat) : Nat := 0xc260f81c21000282001c0c101410303c009120800018cc582b8420341c662f84182810091c00a6508813cddad563301509949a350e5d270b43c18004fb66362442dd92cc12217ad9790520fc7b1483186e7616418c373b0d20c617cd91d8a30fc6ba6c5185fa6436244373b0ab246179f9759230dcec32e9185e7e59748c3b5ae9b12e1b6f85d8970adfcb2e8b86eb5d180d8b79b0bb14613cd98d8a30
def g507H7 (_ : Nat) : Nat := 0x3100002400000000e
def g507D8 (_ : Nat) : Nat := 0x8088a818c2022290ba98c110284069f1e1d80420208ba7a90b05061a1c4c14186382905072437263a0222a06020016041fa430080058107890d09062380218430022010587890c1f031781842c6458561082c8984ab8027063a0662249c1e10c909f8107042aaaa49c1e10ba4a82eab062c5c4a24169298c2eb399a489063048c6001e9298c3a2836338507a488460610dc1e90f0d843e14101b80863acc447a660218d33b9188907a4a63ccc66001e9298cb38007a5262cca24644e169098e3412b381a4063614bbd662b554ca5d3c26949c8cd0c1fd3cc74cda1993045acaa13923c40c700c514c22c3605107406c003f75c630fdd618c3fe58110fdd768c3fbd8950fbd64543ef5d160fed71482ffe1910bfd86443fb60910bff81597fbd8910fef625c2fbe0520fad74483f3d8a30fae41483e790630f9d648c3e75d230bdd868c36f5d170b7f855c2fb60362fcd53d8be759153bdf8654ef7e1563ebd64596f761630
def g507H8 (_ : Nat) : Nat := 0xcb40000000000000000053c00000000c185000009a94bf2800002019360972166710007380000000000000ae47f33400b800000000000060c00002e3518000000000310cb1a514400002a2c0800002e800192000004000c0000000000
def g507D9 (_ : Nat) : Nat := 0x6459580846098548994744403666103a478938506218494a8ea46d1c0260ce0490495a46518c800d0167040c083d1218079042a40ca9d726098148983aa419903205207547b37044c810a1d522e489826052075488572621804c1d52297949ea65d2f3c4ba1f03e003feb2ffd70ffac1ff543fe887dd63fbaa7fbd8bef187ed20
def g507H9 (_ : Nat) : Nat := 0x4647000d44005ac00000a5adc009ec003b40000000ce4000011822800000000000000000000000000000000000008359300000410009989b723d76c6aa000e40e102ff3d5614008040000000442d2b1cc0000005b9998266f003cbc0eddceb3e5300063dfd85000868000000013b1ed5800000680000000000000000000008340010000200020c1800000000
def g507D10 (_ : Nat) : Nat := 0x65c20c002483549ff
def g507H10 (_ : Nat) : Nat := 0x48c0000f859510006cb9c01765a246eec000002c34600408003882003d200698004000001
def g507L : Nat → Packing
  | 6 => (2,4,6,0,0,3,0,g507D6)
  | 7 => (19,3,6,0,0,9,0,g507D7)
  | 8 => (31,2,6,0,0,11,0,g507D8)
  | 9 => (10,1,6,0,0,10,0,g507D9)
  | 10 => (1,0,6,0,0,0,0,g507D10)
  | _ => emptyPacking
def g507I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 6 1 1 g507H7
  | 8 => lookupWord 10 67 7 10 5 1 g507H8
  | 9 => lookupWord 16 101 7 10 5 1 g507H9
  | 10 => lookupWord 6 29 5 9 4 1 g507H10
  | _ => fun _ => none
def g507 : Forest := ⟨507,10,fun i => g507Y[i]?.getD (0,0),g507C,g507A,g507L,g507I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P6_0 : block g507 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B6 : block g507 6 0 2=true := g507P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P7_0 : block g507 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P7_1 : block g507 7 1 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B7 : block g507 7 0 19=true := (@block_merge g507 7 0 1 18 g507P7_0 g507P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P8_0 : block g507 8 0 17=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P8_17 : block g507 8 17 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B8 : block g507 8 0 31=true := (@block_merge g507 8 0 17 14 g507P8_0 g507P8_17)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_0 : block g507 9 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_5 : block g507 9 5 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B9 : block g507 9 0 10=true := (@block_merge g507 9 0 5 5 g507P9_0 g507P9_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P10_0 : block g507 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B10 : block g507 10 0 1=true := g507P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507T : checkedTables g507 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g507 0 0 0 = true)
  · exact (rfl : block g507 1 0 0 = true)
  · exact (rfl : block g507 2 0 0 = true)
  · exact (rfl : block g507 3 0 0 = true)
  · exact (rfl : block g507 4 0 0 = true)
  · exact (rfl : block g507 5 0 0 = true)
  · exact g507B6
  · exact g507B7
  · exact g507B8
  · exact g507B9
  · exact g507B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507G : graphValid g507 (boundsBefore K255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low507 : Lower true (varsX 507) (graphGoal 507) 11 := lower_forest (g:=g507) (i:=0) (hints:=4296044628) (before_sound K255 V255) g507G g507T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K507 := extendKnown K255 11 [(507,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V507 : Known true K507 := extend_ok (m:=507) V255 low507 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low479 : Lower true (varsX 479) (graphGoal 479) 11 := plain_low (m:=479) (hints:=4294997620) (cap:=10) (by decide +kernel) (cut_root (u:=true) (m:=479) (cap:=10) (before_sound K507 V507) (2,0,477,0,10) (by decide +kernel) (by decide +kernel))
def K479 := extendKnown K507 11 [(479,[]),(495,[134,84,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V479 : Known true K479 := extend_ok (m:=479) V507 low479 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0x681a15df0964081654025c01d2a8c5ffb4020d,0x240211830d26080640020401d2284477840209),(0x18f05602468ac40083fda3d06d57103d4119b2,0x38110e02068244008245b7d06016101d4009a2),(0x8f05a8b0111137a9a2c2a02534102c0092e440,0x8d13b83a115d0ea080cea0e514313080964400),(0x0,0x0),(0x4810010c0204009845005e10028001ce940005,0xd9104a4ce20010b837fdfbba0880298850d184),(0xc012035003600001a8619086531021001092,0xc6718df105b06529a8402486c14060001010),(0x8625ac01b8003bee9a23890a6046020028c640,0x52a40600808071081a21090820460200208040),(0xb02a405000f8871000450240982cc000010128,0x8368c070405883100400000008008000010000),(0x10801a4a71100432810002f01082f124a2800,0x80184282000436010000201080d02082000)]
def g503C : List ColumnInfo := [(0,6,17,480,5),(0,22,0,481,4),(32,82,0,389,3),(4,0,499,0,9),(0,32,469,2,9),(64,0,439,0,8),(0,4,179,320,7),(16,160,324,3,6),(16,0,487,0,10),(128,0,375,0,10),(17,0,486,0,8),(32,0,471,0,10),(256,2,85,160,6),(1,16,486,0,8),(2,32,469,0,8),(0,2,85,416,7),(0,5,34,464,5),(32,257,0,214,4),(0,16,486,1,9),(4,289,0,210,3),(32,6,17,448,4),(64,4,179,256,6),(256,4,179,64,6),(0,82,0,421,4),(64,289,0,150,3),(256,0,247,0,8),(0,176,324,3,6),(272,0,231,0,7),(64,1,294,144,6),(68,0,435,0,6),(0,1,294,208,7),(16,66,0,421,4),(288,0,215,0,7),(34,144,324,1,5),(320,4,179,0,5),(260,0,243,0,6),(64,288,145,6,4),(21,0,482,0,5),(19,160,324,0,4),(64,5,34,400,4),(96,257,0,150,3),(0,289,0,214,4),(258,32,213,0,5),(16,1,294,192,6),(64,16,422,1,6),(81,0,422,0,5),(1,82,0,420,3),(324,0,179,0,5),(20,66,0,417,3),(17,160,324,2,5)]
def g503A : List (List Nat) := [[],[16,84,134]]
def g503D7 (_ : Nat) : Nat := 0x80108000000010c10001000000b1010000000107418050c0000b13c9007c8124d208d4521d08813a1c4dc6b34194ba552913c9849208f876381a8c8401d0d05c00e6be1f72905209eb6a77290520acfe958790520ae76a35290630be66807590630be36887590630ae76a07590630be3e897590630f47dd67590630ae76a27590630ce765d85906309f3e8997546309f3e8995dc630f535d57254a30cbbe1b925d5109f3e899754a30f535d772d4a30bd369772d4a30d7365f72d4a30cf366372d4a30ce766174d4a30be3e89755d230ae76a2755d230de5e91911d630cf3617925d630c5f2617554570cdbe5482601758fbaa48260175d67e5d7454a30e69e0a415c575
def g503D8 (j : Nat) : Nat := (if j<1 then 0x9da772046441633c9e58bc9000902fc8141cc4e5f242c150e05f904f2403c8a70005e4807901c3b1b430672f15c81c181187634200f0072f15c8282dc90a80397c8188bc9e582042296793cbc40bc922d3b9608142dc9c6f2f15c8182dc90072e0b8ae40f92e48079788148a59e4f2f100818441650a1f978ae40e452cf27978816894b0c7251429179659e4e20510313921fc6c6715c8220603e4833961c837208e48602e01c40a16c6f27978ae40c16e4857978ae40dc922f2e860817b67b4facbab3a9ba3b9ff99f9639278eb8d38bb83781f7bf7837236e76cf66f6335f75bb57f5434bf48346b4533633032a326722b1831230c303f002f7ef1eee2ea6e6ae52df2d26ca2c66be2bcab46b0aaaaa269c69ae97295a8d68767ce7b67566d25e25824fe47a41a3ba3362d627623a1da1560f6071fc9f69f51ef1e91e31e19dddd7dd65d29cc9cb1c75c5db25a7d96989d7d172965d5914353692e51d1050f60eb8decd20c30b1ca5096084c7806b45e84b03782ac1bc0cc002fbb2fa8c617df925c630deec2ae3185f7e55718c2fbb25b8c61bdd85dc630beecaee3185f7e45528c3f9ae4a9461f9d7454a30faebaaa5187d79d5528c37bb0aa9461bdd85dca30befcbaa5185f7647528c3f9ee5a9461f9d74d4a30faebaea5185f765f528c2fbf22b9461f9d745ca30eeebaae518777dd5728c37bb0ab94617df955ca30beec8ee5187775d7728c2fbb2ea9461aff8654910bf7c92ea886bfe1975443f7482a8241fba415c120fd6a9482907ebdca4148377b0b20a41bbf8590520ddec3c82906efe1e41482f7b2f20a41b7f85545209fecaf02907d75d7518c2fdb23b9241f9d5290630fcfa9483187e71d6418c3f3aeb20c61f9e7590630feab8aa3185f7e49518c3ebaeaa8c61f5e7554630deec2aa3185f765d518c2fbf2ea8c617dd92d4630bf7c8aa4905f764b758c37bb0bbac61fb9745c150ddec3ae8a86efe1d74542fdf24baaa1d7d75545709fe4c2a2b84ff657815c3afaeaa92e17dd91dd630ddfc2ae8b877b249755c3bdf24baae17ef925d570dbfc2aeab86fbdc980d4b77ae8c06a57dd91dd553df641300baefbe09805d7b7aeaba2e1f9e755d230beec90eb187e75d5748c37db21c12eb7df915d630fe6492eb187f3e49758c2fbb223ac617df925d630deec2aeb185f7646758c2fbb253ac617dd979d630beecaee51875b5d772d4b73b0aba46176d95dcb52becc80eb185f3e497554f37f0eba2a5bdb9360075edb20ae2baf5d545715d73df04b8aeb9ef82dc575d7bc3242886bde19714427df24c3aa53dd989d630eafbaceb184f7663518c27df24c3aa13ef9261f50be7c92eb184f7660758c31fb0cbaee17cd921d630dcec2c83185f5644758c376c82c0ee1d6d755c952fcab8c83184dfe55874833df0fb92413dd98d4a30 else 0x12c881014ba70603000a5d38221824b22045904b2090c1000a5d1286180442584c406254308860804b2205430486090c1a1839204884b098643040031384c962001cb1a86110a070d0a060a1410a04c008a112488092488090a9244068a0725880a060ea204030634084c10124c30992076193914280986170d2409642e4e0c0275102e1d101a5d3822212c861910961010504022d2e8818661a12491016418806231a1513241c0c1207018180a19180c03083b920e064425860349220282e48282e4b141e4b14150c3c131018942022212c481d4a901096a5480d0b9261a28449164200b2c309a4ca089644080218244e584050c12212c200860801d119650bc90ff2f90452f934e4508152ca179200e5f2070d914b3c9e58a22e4807978d1792)
def g503H8 (_ : Nat) : Nat := 0x3bbe2000000000000000ac000000012b001c0b8b78001a6aaaed00000000000000023a25e9d732a9b400020000e2001810005580079000ae000280000000000000000006d8000039000001060005e195ccea2a4801c18000068d16800c980063aa40049ef74f22b8012080800810180000c001
def g503D9 (j : Nat) : Nat := (if j<1 then 0x43224e1f05cb8d201724570d65387f2e3490519c94d06030fcbc84a1ece305b24543c1838032c782b20b22c94d03060e0fcb1e4ac82f24c138705f20447c9cb15161c17c81f27387f2f288b20703c9ce1fcbca22c8205b2454383c032c287b20190cc05c94d06030f0ecb4a1e2b2f2414180c782b21383ca16c9050f0ecb1e0ac843062f24880c5458387c332c287320c19c9050f0ecb1e0ac806432c8b26360c593a162b2091c0d26cb8e0c1b24147e340c183d3b2e28a16c9430e0f15cb8a23261466370e2b2059389190592c9151fcb8a1c24664b2454332e2870812c906c30f0ecb8a1c24a8147c2f2634180d383c6628c15c98d0f0ecb4306198a29132564032e17207c98d03160e0ccb198ac8285b2474572f207072fc94d0e0fcb1e4ac883281724307f2f220c58819c94e2f8ac88316208b260c74563b2d348c91d0c850f4ecb1e0ac8832c645b245430032c701b20ac92215161f0ccb198ac8292d67262b0d3861905c9cbc315c8ca1cce2b2e341c30722b0e3882c2bc945cbc30ace23262b0d3844b88c9228dc34e1c64170c84c73861d0619c905cbc8ca1cce28645b0c862b3860c1e19cec905cbc815c32858541a6726172f232b38aff97ef3efdf30f7d7af3d0de40f057713afdd58e9573d398dc70e156fb372db50d7d6ab34ada10ce565f323d8c0c356092f9d768b795a12c8d600add55d2a5d4e8a5151327dd3989954b9254d25090146922cd118865421208cff07c53cf1dbce907213791b3cd50675323185cbf05d92dd165cac8539287137c95847d22b10ec8203ed1e30e7c6f83551910bdc5b02ad147098c48021d0fd072c3401750ad04bc2180e906b02dc13807102b00ac000ffd71543ff54950ffd72543ffdc950ffd51543ff5d570ffd75543ffdd550ffd805d7ffdc550ffd51483ffe0970ffd725c3ff54970fff815c3ff5d510ffd52443ff54570ffd71483f7dd630ff970543f79d630fdc758c2ffe0550bff82543ef5d150bfd87542ffe1d50bfd81d43f75d630ff521443fd5c510bfd82442ff61510ff950483fe5c120fed21483ef90520bff81483fb54920fef72483f75ca30bfd85482ffe1520bfd87482ffe1d20fdd518c3f7d4630fdd718c3f7dc630fdd528c3f7d4a30bfd82d43f7dca30fbd74482ffe1d52bfd80d4aff60752bfd87d43ef5d352f7d75d4aff61f52fdd7554ff7dd553bfd801d6ff61d52bff805d77f5c575dff715d7fb20975fef825d6ffe0975bfd809d6ff60675bfd829d6ff61e75bfd821d7ef5d350ff970442ffe0570bff825c3ef5d170dfd755c37fdd570bff855c2ff60770bfd82dc3fbdcb52bfd85dc3df9d552bff8054bdf5d552fbd7454bf754d52bff8154bfb5c952dfd75dc3e75d230d7f759d6bfe1910bdd858c3e790630f9d7454ebf61875bed821d6bf61b70bf9801d6fbe0975 else 0xf1e2a4b888d4e29222234180c287060623888d430a1e1cb52d1222350c28785494b8d0f4e1e8a18172e490c78662872d198d431c8a18b4652d122234287082d5222431e4a18b4652e223538287882505444b928803152237210c7849206431e8a1418764a20287064b8dc84e1e149a26124a210c44332c70a26898492880e0fcb203d112e4a20287070f2a4b4e9288030029162917250d65385f2e288191cc9c80d15160c1ecb2967250d39172e282a2091a45c9434ecb8a590a882a340c193833272e288c98d0e0f4316cb8a212e360d3913262b208892d1cc98d06030f0ecb8a1e2c78b726340c3c3b2e2b2088b0c19cbc98d06034e0f8a291567250d385f2e28827268d43030cc9cb8ac828a046123440980033272e2b20c0c19071c058d43c90f8e1ecb8ac83830649a34180e383c7b272e2b20d22c9c80dcb83151c73272034332e0c58892c94e1615cb8ac822661634a7253a2a0c805048dc9830ccb8a20145b2418732e2b20844c9005915cb8ac82115672538072d0e282a20a1c16c98d830f0e1ecb8ac82c884b260c3c38732e2b20a051c16c98d0f0e83061ecb8ac837243c3a0c8b2e2b20859cbc943454e8a1d646b250d153b2e282a20a4517cb430159c94e8a2725145d0c05653b2e282a20b59c945434ecb8a1d6725153b2d0e282a20916c9430f060ecb058a2517250d6538072e28892c94e44228a831c5b24760c3f3b2c782b20a2d19120f0e1ec905cb4ac88330332c1724782b21383c9c92203150f0e2ecb058ac82c5a4967260d3a162b20923c90c30cb83161cc8272414383cc32e0c58287320bc9)
def g503H9 (_ : Nat) : Nat := 0x2daafa9157601e13450584c5c489444a973a623a672e2fa047bb4717000090c266e410007d2bb0533fe0afd000018327656879230af70000000008c232a113055db2000fed25f0008e3000000ac9000071000000000000004000fa4b4ae380000001728ab0000007d52c8000b9fc179e9c1c451654d742e791a5a561f69a03c865ec6a6f97c5ae000adb65ac07000357077375340b0a1afe0800000550b4bfd02dd9aa6000000d2052c1ca00000053993e0002165687b48c4f4f55b6a79aaf142426227094e690f95c046134a1ba1e000b2833706b0bd632db8d352fc94367a54b93b0000b511054d1ac129d6dcb6159e63519936d3f0008d7fad0000000008dc000a7892d00090e000a7d6f50cfe5edccb49de43e81ddf61e01e6e70dcd118865273162146212e200469d2f88b011b1d34e000000000f3d000f5075d62b453000000000000287d24e127265cb000c8fe6400000000060374cd6c5a896a29c073376306125c867d0df90a0800050101020d010e001700010c0301050010050d080009332b0100001205230b0c13000000030d2f0301080c001d01000515020f080000000003000d28
def g503D10 (_ : Nat) : Nat := 0x1233265c32a1644a3938b0a641c997221a29538a240c7490b2e195146644a3938e3248b49960c2c894727166511d2d242cb900e54e2c2849234b439630c8a9c5851b24e4b866454e24c8d45265c32a1454e28c8d5a7a5c3921454e28c85443529692725831538c32146a618721cb922871622485970c6ce1e4cb862a70bcbe9771d211ebd4d2ab28696630052007fe75ffaebff1d7ffa97fd52ffee1ff5c3ffa87fd50ffa41ff443eea9fde30
def g503H10 (_ : Nat) : Nat := 0xa693150000009ac4bf000a4bf637e52bcf98ae9000000e5600042200073da1a000000000000f610002d9a1e121000525f11daf737000000145000d0b290040000c3a000000f3500085f3abd4370ac58000000000a1099da81729708f8a833465a6b151000ee802bb0476a0000004c20003200001ce0360000e1000542616b8ba4700000000000000000070000089a0000007e424f52a45722841c426000000ae6000e2fddf8e3223dc68e70db000d9e266a1855e0000000008e2f442248050004bbf3edd58b6000d2c000000b4aaad63100000cd0f94900035d53bf09a12099239f4df4e1071b0d59c32d1b00000065468fc13802d67000ba90008171d8000000000ad1000000000f41603a5c33c000d5b2622bd00000074c000450eb5f1482e7482ba0000001cad52334c60130000b55264638000e53000000d0db5ad1911ff06a1dcc383f00000166874620e6d2000f2da270002020200000200010001010105000107030e0305010002000000010300030200010003020005000a040203000007010200
def g503D11 (_ : Nat) : Nat := 0x92c80ca386ff
def g503H11 (_ : Nat) : Nat := 0xda3b00146e400000b00000212005e44c97210061000003a801300011b2800190000001a7f2c8ba2d6c03dc0040000001
def g503L : Nat → Packing
  | 7 => (30,4,6,0,0,9,0,g503D7)
  | 8 => (126,3,6,0,0,12,0,g503D8)
  | 9 => (108,2,6,0,0,13,0,g503D9)
  | 10 => (13,1,6,0,0,10,0,g503D10)
  | 11 => (1,0,6,0,0,0,0,g503D11)
  | _ => emptyPacking
def g503I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 13 83 7 10 5 1 g503H8
  | 9 => lookupWord 63 241 8 12 7 1 g503H9
  | 10 => lookupWord 50 227 8 12 7 1 g503H10
  | 11 => lookupWord 7 41 6 9 4 1 g503H11
  | _ => fun _ => none
def g503 : Forest := ⟨503,11,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_0 : block g503 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_1 : block g503 7 1 29=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B7 : block g503 7 0 30=true := (@block_merge g503 7 0 1 29 g503P7_0 g503P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_0 : block g503 8 0 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_31 : block g503 8 31 95=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B8 : block g503 8 0 126=true := (@block_merge g503 8 0 31 95 g503P8_0 g503P8_31)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_0 : block g503 9 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_11 : block g503 9 11 78=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_89 : block g503 9 89 19=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B9 : block g503 9 0 108=true := (@block_merge g503 9 0 11 97 g503P9_0 (@block_merge g503 9 11 78 19 g503P9_11 g503P9_89))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_0 : block g503 10 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_2 : block g503 10 2 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B10 : block g503 10 0 13=true := (@block_merge g503 10 0 2 11 g503P10_0 g503P10_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : block g503 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B11 : block g503 11 0 1=true := g503P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503T : checkedTables g503 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0 = true)
  · exact (rfl : block g503 1 0 0 = true)
  · exact (rfl : block g503 2 0 0 = true)
  · exact (rfl : block g503 3 0 0 = true)
  · exact (rfl : block g503 4 0 0 = true)
  · exact (rfl : block g503 5 0 0 = true)
  · exact (rfl : block g503 6 0 0 = true)
  · exact g503B7
  · exact g503B8
  · exact g503B9
  · exact g503B10
  · exact g503B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : graphValid g503 (boundsBefore K479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low503 : Lower true (varsX 503) (graphGoal 503) 12 := lower_forest (g:=g503) (i:=0) (hints:=4296017492) (before_sound K479 V479) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K503 := extendKnown K479 12 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V503 : Known true K503 := extend_ok (m:=503) V479 low503 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 12 nineInputs.toFinset := by
  rw [show graph = graphGoal 511 by decide +kernel]
  exact cut_root (u:=true) (m:=511) (cap:=12) (before_sound K503 V503) (8,0,503,0,12) (by decide +kernel) (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0x7ff001ffc00000000000007ff001ffc007ff,0x8290520a4148290520a4148290520a41482905),(0xffe00000000ffe003ff800000003ff800,0x981302604c0981302604c0981302604c09813),(0xff800000000007ff00000000000ffe00000000,0x2784f09e13c2784f09e13c2784f09e13c2784f),(0x1ffc0000000000000000,0x9fb3f67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f),(0x1ffc0000000000000000000000007ff,0x7d6fadf5beb7d6fadf5beb7d6fadf5beb7d6fa),(0xffe0000000000000000000000003ff800,0xf67ecfd9fb3f67ecfd9fb3f67ecfd9fb3f67ec),(0xfffff000003ff80000000000000fffffc00000,0x580b01602c0580b01602c0580b01602c0580b0),(0x1ffffffff00000000000,0x604c0981302604c0981302604c0981302604c0),(0x3fffffffe0000000000000000000,0x80700e01c0380700e01c0380700e01c0380700)]
def mo511C : List ColumnInfo := [(0,8,375,128,11),(1,16,494,0,10),(17,0,494,0,10),(168,0,343,0,8),(160,8,343,0,8),(128,8,375,0,10),(48,0,463,0,10),(0,4,187,320,9),(8,0,503,0,12),(4,0,507,0,11),(2,32,477,0,10),(34,0,477,0,10),(0,32,477,2,11),(258,32,221,0,7),(144,8,359,0,8),(256,0,255,0,10),(256,4,187,64,8),(34,256,153,68,6),(72,1,294,144,6),(0,16,494,1,11),(0,9,294,208,7),(0,10,85,416,7),(16,0,495,0,11),(64,0,447,0,10),(264,2,85,160,6),(35,16,460,0,6),(64,4,187,256,8),(1,176,324,10,6),(320,4,187,0,7),(33,144,324,10,6),(36,256,153,66,6),(288,4,155,64,6),(288,0,223,0,8),(32,0,479,0,11),(100,0,411,0,7),(18,160,324,9,6),(272,64,170,5,6),(20,64,170,257,6),(0,80,170,261,7),(16,64,170,261,7),(152,0,359,0,8),(80,4,171,256,6),(80,0,431,0,8),(276,0,235,0,7),(48,128,324,11,7),(0,176,324,11,7),(272,0,239,0,8),(324,0,187,0,7),(81,0,430,0,7),(20,0,491,0,9),(66,32,413,0,6),(64,9,294,144,6),(0,288,153,70,7),(32,256,153,70,7),(32,144,324,11,7),(392,2,85,32,5),(3,176,324,8,5),(192,9,294,16,5),(38,256,153,64,5),(260,0,251,0,8),(17,64,170,260,6),(352,4,155,0,5),(256,10,85,160,6),(21,64,170,256,5),(260,80,170,1,5),(276,64,170,1,5),(162,8,341,0,7),(310,0,201,0,4),(336,4,171,0,5),(16,160,324,11,7),(64,288,153,6,6),(96,256,153,6,6),(145,8,358,0,7),(273,0,238,0,6),(4,288,153,66,6),(65,16,430,0,7),(102,256,153,0,4),(68,0,443,0,8),(5,16,490,0,7),(277,64,170,0,4),(117,0,394,0,4),(128,9,294,80,6),(68,288,153,2,5),(140,0,371,0,7),(66,288,153,4,5),(100,256,153,2,5),(2,176,324,9,6)]
def mo511A : List (List Nat) := [[],[16,84,134]]
def mo511D7 (_ : Nat) : Nat := 0x930c0f84698b2ec3304b1081d28d316e1b265982103e05baacbb0cc12c420748b5d5b86c99660840
def mo511D8 (_ : Nat) : Nat := 0xc09e021782d81580f8009e0be021302301d81580f800ac09e0217034c7bc2bc009e0be0217c4780b828631cf1411873c505d15d0a1146fc474287d19f11d16d0a27457428511bd19f10d0a2446fc474287d19f11d16d0a27c43c558087513f1150fa0da022b83647dc2dc00861ce0d91f7002246bc67c41875808b913f1190ee0ce02298278085e0be021782b81380f8009d15d0a15e8bc5772eb5d0b95712df5b8b656b2d35a0b35652c7588b055f2bb570ad5592af558aa5532a3540a754d297528a454728b510a154127f4f89e53b2734e09b5352674c89852f25b4b09552322b4387ecf61d13846b4cf18f3005aca814124c4447b0e1180294450690900e41500f000d6b5c76c4a865840d6b5716c4a865840e6b5b7659a121840e6b571659a121840e5b5cb65da121840e5b5b765da121840e5b5c165da121840d5b9c16dca464086e5b9c165da021840d5b9716dca464086e5b97165da021840e6b971659a021840ed4d8269d6214530eb4dc26a16214530eb4d626a18214530f52dc565d8258840f52d8265d7558840f62dc26597560840f62d756598258840f2ad976198258840d6ad716c8a865840e5adc165da221840e5ad7165da221840e6ad71659a221840d78d316e4a261840d72d756e4a261840ec5d8669d6214530ea5dc66a16214530ea5d626a18614530e95d8669d8214530cd5db869d6214530cb5db66c9a814530cb5dcb6a16214530cb5db66a18214530f23dc86597560840f23d756598660840f43dc565d8658840f43d8665d7558840f13dc565d8660840e53da86d59758840f13d8665d7560840e53da865d7558840d63db86c9965d440e63dca6597560840e63da86597558840eb4cc26d9a814530f62cc26e1965d440ed4cb269d8614530eb4cb26a18614530f52dc565ca261840f52cb265d865d440f62cb2659865d440fa4c516198258930fa2d756198258840cd55a76c48614530cb59a86c08614530cb55a86c48614530cd59a76c08614530cd4da76c88614530d695c36c4a865840cb4da86c88614530ad35c72d5a121974d539c56dca464086e539c565da021840b62dc22e1965d440b635c12e1965d440d52d976c8865d440d62d966c8865d440d535976c4865d440d635966c4865d440d539976c0865d440e52dc565da221840d2adb86c99660840e695966cda121840e595976cda121840e535c565da121840f0ad976198258840ad55c72d5a121930ab4dc22d9a814530ab59c02d9a814530d639966c0865d440
def mo511H8 (_ : Nat) : Nat := 0xcc06034020800000000
def mo511D9 (j : Nat) : Nat := (if j<1 then 0x61962103b5ecbb0cb08819ef6a19758840cf7b50cbac220677d9869c51483b5edc32cb8881daf619965c440ed7b64cb2e22076bd62659711033bed3b2c28a41d6f6c59760840eb7b04cbae22076bd82659711033deb8b5243081d6f6999760440eb7b0ccbb022075bd6265d81103b5edd32cc0881daf6e19660440ed7b4ccb3022076bd8665981103b5ed932cc0881daf5899660440cf7b2ed090c2076bcb865971103aded8b2e43081d6f219975c440ed790ccb2e22077ad9728986103d768830cc12c5b77588a764d10df72e2d010c206fb5b7684861037dab8b4243081fd36096214530fe5aeac12c4206fad7168886103daec330428a61f976196214530bebb70b10a2987e3d865d562103d9ec32eac1081bcf6a17558840fe9964c30a2987f2cb261975102fbcdb8a2c0241b7729d8664d10dabb4ec30a2985d79b714580482dbcdc0a2b024175e6dc5158120dabb4ec10a2985b79b8145804827aedd10c28a61ad76a08614530cbb94ecb3268855dcb764d92442facd810c28a61b5769c8614530be9b64430a2985dd8b764d80443b5ad8b2cc08817d56c48614530d6bb50c10a2986b5da8588514c3adacbb02b0881dad6598158440e97b2ec32c2206f54b5684864c36aed3ac428a619af6a19658440cb7b50cbac2207acd86609624c36b6d3ac428a41ad72d9a814530c6fb72d40a2906b79b06a0514831bed433028a4195f661a714520d6bb64d40a2986b5da8618514c31bed432c28a4195f69d9614520d6db50b10a2906b5db66a0514c3b1e5c32cba881d8f6e1965d440ec7b2cc330a20753d9761985103b1ed932cc2881d2f65d8658840cf732ed010c206f95b3684861033dacbb42430819af659a121840cb7b2ed090c2067ad9768886103a9edab2e43081d8f6c9965d440eb5b2e5130c2057adb928986103a9edab2ec30819af6a1a165840cd7b50d132c2056bdb12a196103b5659350cb0818bf2a58658580b5eb624b30cc05aedb225986603d56c32e8c12c5bcd2d5a121974cf713050328bb57b9b72919021bb56cb144c3081c6f65d8660840e57b2cc330420753d975d582103b1ecb2eac108196f6a19758840ea7b6acbac42066bda865962103b56d932cc1081d4f65d8558840ec7b2cc2ac420753d975d562103b1ecb2eab1081d6b65d8258840ed5b2cc12c4207aad866096210335edd32cc0881ebc6196160110ec7b70cb30a20763d9661975102b9edc90cba881d4f65c865d440ec7b2c432ea205f2db221975103a9ecbb0cba8817ce6c0865d440ea7b6acbb042066bdba6598210395edc32cc10817cd6c4865d440cd6b2cd090c2065b59768486102b5ad8950cb0815ab6c8a865840a97b6e5432c2065b9976808610335ccb3404308116f6e99721840cd5b2cd110c2064bda765886102adcdb948c810d96b65da221840 else (if j<2 then 0x50650d61a03305e04b8089a221a701f170d4198121b04e07b03614491ee8780f05118d389046e2e40836e0a3830c2e6a307f88c20619c2902bfc4026f16c1ac4b011e44f8804ac1a4d3011bc468960c269808a4a014697f11a26c53014026149455a26c53014036146050a43c428751741a808e4a01468ff11a2344b8aa024285521e2143a8ba0d40470544994878850f41a808e8a247f88d1124344d8a602448fd0be2344c90b14c0472500a347f88d1362a459856024e8fd1362ac2b011647c9a921e2243b06602382a91e89a4878890ec198091227c4487e0dc04550ba2bc4289d16096808f42b00812f10045080c8b5c2f88057a2a808d62745301d0a202d22c4bb4518f227a14705be2095e8ad16c06c790150a482c257a2980d8f203a14732fc5b456851114028f116274530150a3997e2da2b42884a014697f11a2344b8aa024285521e2143a8ba0d4047513e2012d06053404611a65fc4716d0a282af0ac1a47fa1921e33c4301f12532860d24247c97f19e2180f892415785c0c63fd0990f19e2300f8928c382a31fe2fc2e06f11804831e08fc4190f13804606123e4bf8b60de2248789201878b91fe1583788921e24851e08fc4290f13404605521e47f8bf0ac1bc43012147823f10a43c4d01181860fc2fe2cc3788c21e24865121e47c97f16c1bc430122490922a48491fa47891ca46c919a460916a454913a448910a43c90da43090aa424907a418904a40c901a4008fea3f48fba3e88f8a3dc8f5a3d08f2a3c48efa3b88eca3ac8e9a3a08e6a3948e3a3888e0a37c8dda3708daa3648d7a3588d4a34c8d1a3408cea3348cba3288c8a31c8c5a3108c2a3048bfa2f88bca2ec8b9a2e08b6a2d48b3a291892621786ba145837209f80d9ff97ec5f537ba9ea27969e287781d777515d087301c4c6f8db906d79b166ae1a5a68a19e0666193a637187e60817e35ec57695c596ce5a71649585d5cf55f152953b148e51193dd4d792df4a0522e47c519e45010ed42950683fa4f8b3d38ef03aa0e763910df1364cd4033e0cbb3148c0a2edcb592c18ab32954a02266495c24248ab21b881b1f4c78b1d647061a7464a18605c5164c535138849a11743e90e0030c0ab826608201aa058810402f005e0003bdacbb02b0881bdd2d5a121970bef36e28ac09077ad9760962103d76b830cc12c5bdb69d6214520debb6cd40a2986f5da8618514c37aed935028a61bd76a18214530debb50b10a298773d9761985103b9ecbb0ab1081dcf6e1965d440ee7b2cc32ea20773d965d582103b9ed932cba881dcf6597558840e77b2ec33042075bdb865d86103adedc32eb1081d6f61d9761840eb7b0ecbac42075bdb165d86103aded8b2eb1081d6f619975c440eb7ac4cbae22076bda861d96103b5ec3b2cc3081daf61da265840ed7b0ecb2c42076bd97 else 0xc1206f00f88c202c19e17c0ac48180243589516813808806f0e602c03e2384e10f2662c903c07701601f11c270d7933164e1c03780b00f88e1386bc998b26cbd89516813808a06d0e602c03e2384a10f2662c914206c50705e02281d144a2cc7f05e02358fe1565ac4a85e160538091a3f4bf0ad2c6140af0b029c04931fc1581301d43c00603628945a04b1fc04631fa8782f01138560230a04b85f931947824046a2d457885200a6809263f50f05e022597b12a2f82f01145058951622f82f011a4782304922e4578cf1126a48301284bc8f04722e457881352418093a2bc4025049a2e4e3011e47ba1e0bc044b1f6254588b409c04650ba2bc4026513a2c4e501201468af1009d44e8b539404891321f82f01128bf885174428d701180e8a2916e5f82f011982b1762de2384c8b635c04803cc0980f88e1207fc9c8b2282d17a2de2384a8ba35c048006c5d8b788e1322d8d70121cbb89917c17808b62545f05e022505a2de214581fe023003a2de228428ba21c047a2fe214581fa35c04671322f82f01101612bd15405c7901d0a3b89d1540742890b7c458915fa29808c0b7c458995f243453011d47b85f10e254868aa023f88d1324183301141849765123fc449060ce14892fc1a47b85e2ce00692eca18348ff19e224830170a4c2d91b2001548f60d62fc4490f12c04b05b2364048f92ec1ac5f88921e25809721e4bb2891fe218330170a402df11a0215b8ad1f404771ee2745685a022caff11e2c13b06b12c04715fe2098f8b04ec18c4b012094028f11a2344b8aa023d8af10092c5825c023788b1264303601149698d3000a8c7e06717e20c8789c025f85057e23c5826c0ce270091e2103811065c04))
def mo511H9 (_ : Nat) : Nat := 0x72001b000000c2e00092234c51a33cb06f360000003328373079b50006a3000d9c000219000a1c00000000000000000000000000053830900000000041480e61f000000000e0300000073b000000000d3d000000000c4100fd42a39b1e000b01a23111000d8159669b31d12900d94b8a1000418d94ab1e340a084514eec460a23a14043112522f01514993ee00330305a1339ad2c0000000006c2b98eb0d26993548850627000046000616108a2a683f3f80c243a4f22b00b921000e24f3572d3b2597f44347fb3604080d99baf00074af28000000000000cc3a10417cb6000a4d0000000000000003124b4000782000c33000902070500031a072700031326010001000101072509000100000f090d000901000000000002
def mo511D10 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x3efd8658910bff6a162442ffda221910fef61d86103fbda660440fef61981103fbd865c440fef60971103fbd8758840fef58981103fbd625c440fef21971103fdd8664d10ffb289864437bd9658440fed60561103fcca261930bf7688864c2fdda121930fd7619854c3bdd8660930fd7615824c2fdda858930fb7619624c3fcd8258930faf619611037bd9758440bef6a1611037bd965c440def659811037bd9760440feb60962103f3d7558840fcf61562103ebd8658840def659621037bd9758840bef6a1621037bd965c840fcf5d582103bbd8660840fd7615624c3f6d6214520df7661314837dd964c520ff358931483bf98760120fde5d580483f785160120ff64c5804837f99660110fde5d5604837dd9664d10fde14560483fd931581209ff6a5864427fda921910bfb68886442ff9a021910fbe5d960483ff16160110ff664d80443bf98660110bf76a1614c3edd8658530ff5605614c3f5d8614530fd7218514c377d9614520fd7588514c377d985d520ddf65975483f6d7558920def65982102f7da814520df764d9244377d9814520bdf69c51483f5d8214530fde5d580582feda225980bfd68496603faca261840ebf25986603beca261980def659861027fca95d980edf619856037bd9761840edf61975602efca664980ebf619626027fca958580ebf619616037bd9721840bfd684865c2ff9a021970def685961037bda265840def61d961037bda765840def6a1961037ed9724986dfb2899858377d9861560ddf66175583bf98760160efe61980583ef97660160fde61580582feda221970ffc585704437bd9760840dfb2499061bf3c865d440fcf619751037f9a764086dfe6859021b7bc9865176fcf61985103faca261974bef688865d2fbda121974def65976102dfda725980fcf5d56458bf3d855d162bef68486103ebd865d162fcf61975593e7d865d562def6617458bfad7460962ebb6198258b5bda465c86dee2919021ab7da814520bee281945dafb9a021974b6f69c865d2d7da714520b7729d93442fada221974bed684865d37d9a364086b6f69c861035bda165c40daf65886102fada221840daf659711035bd975c440bed68486102fb9a021840daf659811027bda95d8409ef6a4861035bd9760440daf6597610373d9761440dcf659851036bd9658840d6f65d6210373d965d440daf659721035bd975c840daf659821035bd9760840d6f65d761035bda865c40d6f69997102f5da814530d6f689971035bd9761c40d6f65c861036bca865840daf69d961036bd8765840daf689961035bd9758440daf659611036bda865840d6f65d86102ddda721930bf3688864c36bda165840bf5684864c2fd9a021930daf6598610353d9761440d8f6598510353d975d440ad76a0514c2d5da714530d8f6597510353da565c40 else 0x168a10c2b08f88a2f89404b10026e2023e2501182d0b897e2d06e2090e248f404a4a297a282310c2be228be25012a8f1038808f8940466142b0b788a2b8940470928fe149c114afe228ae25012a90a3c2c09a87e2f8541b88a25012c2d4a028a428fa5c27e2d06e2289404c4a997a1788a2b8940470a844a428fe2023a2501228fa5e9ca438808e8940480b0400af8be1506e228940490b5280ac41e2d06e22894049a3c4109f8808f89404765d8c0af8808f89804763c4109f8808f8980472818f22f89c1701198f65d9c6438808d898048a5e8c0af8808f8940470b68ca002ba5f8b41b88a4389a3d01302c631800ac2ae2f8581b886438963e01358f1038808f8980460a98c0af8808f89804763d900b026e2f8581b886260129280a28fa5e8a08c4109f88a2f89404ca3f85a168a10023e228be2501282c6258b09b8581b8811389804a0b428a278ba2c2741b88a7389404bc008f25f8b07490e24adc04921c8f25f8be33a1c1701218fe158a10023e218be260127a12408f25f8cc1701e2480c08fc1497e2f8ce8793e5890e24b0b289e2c26a2f8541b8827389404b4a02d0af88a2b894047e142b11788a2b8940470a388a2b89404522f89c1701108be2404c044a1788a2b8940450a38862b898045f93be48f90be3cf8dbe30f8abe24f87be18f84be0cf81be00f7ebdf4f7bbde8f78bddcf75bdd0f72bdc4f6fbdb8f6cbdacf69bda0f66bd94f63bd88f60bd7cf5dbd70f5abd64f57bd58f54bd10f38bc8cf08bbe0ee7bb48ec1baceea33a54e89b9e4e663942e3b3878dfc379add3b716db2b692d8f35d2d5f351cd36b498d15b40aced337ccceb302ca8b242c7b3182c48b0ccc1b300cbedaf2ebb12e50b812da4b58ad2ab37ac9cb0f2c04aee2b6cac82ad4aa72a5aa8629aea53a8e4a1ea8389f627789c126b8998a62a972a57e94a24be91f24088f423708c4229c88f21dc861a12682ca0487f79f887ca1ebe79c9e3077b9da27509cec7231c226f59b806d49af269f9a3267999a46589902626185660517d25d797305be16c05a2164657c15ae55614da52614244f1133c4b7127c48711a845710fc41d101e3ef8f683bf8ea838d0df23620d1e3370c903098bb22cd0ae82a48a3c277097c24c08e4226085620007b41cd86ae19b062016d853813384640fc03900ce82da0a10210067015004100cc027807000e0000ffe5c580583ff97158120ffe5c580483ff9865c110ffe58970443ff9825c110ffb609625c3fed625c520ff7619814c3fdd8260530ff7589814c3f7d8661570fdf615825c3f7d8558970fdf61975583f7d7560960fdf5d5625837fd9761910fbf619625c3efd8658570eff619825c2ffda858970dff661715837fd985c520dff659714837fd9758910bff688865c2ffda121970ffb289865c3fed8258910ff764d6244) else (if j<3 then 0xc241825f93c2cb0719380b090758506870603842d0ae320104b888409c2a0261412c2f93183a0e412e4f0b168a05489a2c9cc17011c3f0fa8b27305c04623c3e22c8ae309a24305c0496268ba8705c045074a2a2d8fa8705c04741516e228ba8510c04763d89a2c8ba8705c04745d16c268a46b01a14745a8a44301a14585d8a8421ac05851897e20404189a404643f0507716e230922c1f473012a8fa5f0aa5815c2c146170125104151745b88c268ba851ac04ac3f17c0b16e230906c8bc058529976268ba8705c04685e0f11a028061a8418a61490438511b02c078b11c3304890cb8511c46c0833e241225f01268b2bf88e2c27c1989c0470d30104011e2c350cc122034e202fc041114afe228926b8909b8b4190124070243802c1dc06851cadc0b886242fc0410a2880b4274a388a269ca2d0640585284a11b01a151ca286e1434c0b01e228925f8b0d410050b12b88c04100e850b4490038801c170c80fc0490ca8ae20114d0a607301a2c90b6974a28ce202ba4106a3d01614bd232123f16c230904b01c14925c8fc5901c23090530bc149e158ae23890918b0a6012185273882698909b8b81a01242a25d8f63188e2423e2e06805852d8f0a98809b8908f8b81a01614ae1424e21890a78909b8b81a01298862c35606890d0276148e1434c0b88e2c3505189c0490b505c0916e202f4268ac049029160d109a2b01a151c1c0f808100e01d614611a01e212611c33181764e0206838075851c2f06e028078824010e258a274823f16c0708c2f0504880dc2342d0ae320280685e2090b4414a02be2289a2d06405852a850d296e2011626811c2c65d2ba2b0163d01a1486268ac0685120f6584b85d886258b0518525850518a12d800c18906217e4d8b2d1a6242362c36a07051c2de21892bc90a2b011cafe2c2662701c14623ca2c1487c0589188f25d8be8705e2090e2701268f25e8809b8908f8b41901a14ac0b88e2497268381a2f86b0962985a04643d10c258aa1681182d2348023c97c198be2090e27012f0944285a0446252fa2b01a1454268a12a8544054410742e81a14583e1a84207605851b85e87960be07e3388e04883c23e2210e2581183083e17e2d86e2210e2480803dc6b17e1702c5b880748bc2701304009b8820423e24612f1323c97e2f8ce8705e2090e24b23c97e2c364178824389c04920c03c3f17c7310c0b16e201b22f09c04d04b0ac0a19c2f892178cc04921c8f25f8be33a1c1788c049e849023f0525f8ce2301e2490c20f61617e2f8ce8793e5a10e24b25c8f08f8824389c04763d97629880b40e62f8980490b28ca002b0ab8be1506e2290e268f404de148723c97e2f06e230122c2a3e8aa202ca168be2501268fa5e880b485a2f894048e170623fa124097e3388c0789283023c97e2f06e2090e2480ab85a else 0x19c2f026241804860bf000f0111385a2b88e2424a2c9a404823c2408c8b22b8ce209a2430128afe2c3c62705c04623ca221f05c0589188f25d8be8490e2705c048624af2428ac170118890fc9ac170114afa249062b05c0462408722f05c045a2490c1701108f2689021f05c046a2b8809424a2c9cc047a3e8ae228908e8b615012085a2b8809c89a2c9cc0480b2c225e8ae228826b89a2e85404b0aa8d25e8f08f85a2b88e2424a2c9c404da5e8ae228908e8b40585208f26890e2087c1b011e8fa258a61701148f2bf882428962b011f88a2490c1b0114afe209aa2426e2d064048a3c2d09d28e2289a2d0661501288526890e208722f06c0480a8972728808d06a149a4049a5e8962b01805851889e2025c189ac04623c90a258ac17011917e228ba851046b011d17a2916c2685a2d1ac04845a85a2d10c04545e85a2d1046b011a02c241d6141015858720280788c2610e4d8a241d8720280788c2610e4d8b261c80a01c2610e4d8562c80500f49838c2a028078841f0b2a1c6160280788c261ae4d8a258fc29966270b05285c0488701d80a01e230986b9362c98718a80a01c261ae4d8562c90170a05b8805409c2f01200f0170a05800e200905497c2c14e3301343bc170ac5b000630b04b8cc04a2b705c29010c3))
def mo511H10 (_ : Nat) : Nat := 0xea400000000000000000001e8d00000036c800000000000000000000000000000000000000049e000000000000085580bfea050c8a9759f76e510cbb32c850800094c21bead00000000000a940006127934001cadb41d88090e00062d5ecf47303b0002a440000000000002c100002240001cc0773000790c00168500000000000000000000001d55000226c000000000520000000021a8001026000e5c80022efb6315095586254a7b2cc1880a186b21eb16c87e00085bc92dc51f2d000287bc0dbb0e4e7a83c156b41a7c14728cc45000000000003190b29a12e8000faf00036da000ab500032b84ac000658743313e0000000000fb11480000001217ea4c94a8e0000000000000000000000028560000006ebdee2a260000000000000736800000104e619800354c4af435000000023aead800000000099670000000000000000000000ab4800000063000022a000000081e1911844e7a85b5d7c000a1c3cb587c000610b38e25c001e3e1b7452f846000929a904c1814c258000112cc8b3bd2ac4af1ca9ead09328fb47f0000000000000000000000000082aba691540000000000000000027a102cb0000a3600000002b53b2aed6d3ea1d713800000188200069ce549e051ba8003d29e0b0000000000000000703c000000000000000000072b000000106782f104800156600056d04fc00000010a9c08f51f1c38bb86e000000000944be01b47800000000000049dec8c0000000000000000fdc000146576f744a0da54bc75616e068000c61000000000000000000018b9d60000700c00020d00050540000002328000001072000000252a00000000000000000003190000249000286e4f600000049e4914000000495029a76b0000000000000000000190c0000000000000000c0480000000000000000d5c000f10d267d70c7cb25010800000072b91b8d18a5f0000a056340000000000000aa3b490001c8e000000000000000000021a542929d00000030f000000380000010760003975d6600000000000000000003288001d79ab82a4c03000000035f00000008070001e8fc292d950440000884160002d1c0000000001cc60000000002ce80002c899980016340000000000d4e000008060800804000100800040e0101000020201406010000000040080800010002c0004000040402000040200050000000000102e000180002000000400000000802010180c00040080000090280000020007c0801000000003048000000
def mo511D11 (j : Nat) : Nat := (if j<1 then 0xf0b028b627101045404d0dc08698bc28f319a1c46243901320452c4e207101182e16296271023808f85850080214080e09988c9c2f12625d182bc408f13011c601707808038b23e14498cd0e4f2d880e62500786c0a1c11e0462009b1023c4a04616225178513c1b109cc4c04a4625f178cd0c171090c4a3e025a30ac3642e203989809102206207189808c2d448bf17850be3343880d6260264c21f1781458a285c422b13012c49858286e051645623121c8096894589b19a182e21398980958515917108ac4c04742e211589808a2a4be171606c46240240b45f88456260230a3160642e2312011f0a0f0be2f19a1c9e5b1010c4971742e211589808c8bc4a860b01151e8ac4c16022e2f0ba1cb01c1e17c662302562743960785f10101c60491462c0d88c48046c5e140d88c48046bc42e95b8faddeb522c97afbeb8fac2ea63a8329bea59e919a29e83e9f9e73699f262596ce4f992ae4308ed63438bb228c888e18d83de08e80ddfce7dddf297b49e697801da0756dd167321c7a7045bcc6db1b0c6af9a5e681d9a765418f962898425fad78b5c896d459f560b571958154cd4ee525d4374ef13534b61293495d1ee45cd125426104a4038fae3dc8ef73aa4e6d3780d9234c8ced3234c512fe8ba32d78b102a9ca5928089ab24c08be220883d1f2c7861bc06b419e061816bc56114944b311283e10e0433c0c242bb09fc23a0744195058812f033c07800f0000ffec32c1ffd87583ffb2eb07ff66160ffeb0ae1ffd625c3ffb04b87ff21970ffe4b301ffd61603ffb22c07ff58980ffeb9301ffd82603ffb24c07ff5d980ffec3301ffd865c3ffac4887ff64910ffe43221ffd86443ffb2c887ff58520ffeb8a41ffd81483ffaecb07ff61d20ffeb0ac1ffd71583ffb02b07ff64560ffeb12c1ffd72583ffb04b07ff64960ffebb241ffd8758bffb0cbb7ff5d962ffe4c2edffd97603ffb0ec07ff65d86ffecb301ffd9061affb30905ff65d20feeb0a61fdc864c3fbb02987f758930feec12617fd96483fbb0c987ef58440fdeb8881fbd81103f7ac4207ef5c840fdec1081fbc86102ffb30bb7fe5c110bfec9221fec9261bfbb26885ff65c86bfecb2217fd97443ff2c0907ef5d840ff690a41fdd31483ef8a2905ff64886bfec810dfed62483fdae4907df5d520fbec2a41ff980482ffb2eb077f5d972bfecc2c1fbd645caffb30b15ff65d62fbec2ae1dfd765c3dfb0cb17ef5d964fbec2ac5f7d7558bf7ae8b17ef59162ff6c12c5f7d75603efb0ac06ff61980dfec3b017fd985c3ff300887ef61c40ffcc02c1dfd875dbf7b28bb7ef61840fde432e9fbd87593dfaecb07ef61964fbebaac1f7d85583f7b0cba7cf61440f9eba8817bd96103e7b0ab25ef65c40bfcc810df3d75593eb8a2987d761530bf6c910d5fd9721ab7b2e205af65840 else (if j<2 then 0x40704c146916c40be02890891854b868690280e21138b1a84028612478938145b10898489038382e0a348b621122f808402248b690481a05c788c8640a2d8884224210945c2e03054c2a070c9351f0f11a160b0a8145a0188448f2164cc6405447a5e17020a850718c80923882c2a2c8080424310b09632026054322f11a160a178540a2d00c422421091e42c238c80a88f85c0912141c6320240c89c858285c708a8b621161c0d404d8786e2e8a8145910c203c250a8b809a0d42c14708a8b6221209458720264591189c58744901428689272322c88048e03a1c80a14a42c151516c4226128b1206a025b08848f8786d15028b621101a44c25168580a03006a160a384540a2d8844c24488b23c0438823c61851c22a0501c462516142e0b16c409a162217c043448c20516440e2161d0e4050a1a2e0b16c4102161a17c05124946058828050390144904e8b220701d0e06a0285249a0f46259104c2aa04a48508162f89c2113090d22e163c13c14b17a4d110945888782742868ac406b12230d8b20a384869024462428381c0a8c8b6231247080e08440bf1635c08d04e85230a971a40a038844e2716350a16851a25b1011408bc70b858218bc2e3343880d404a0b040358b1b217100784c04a47a289e3c45e260b01211897c5e334290c4a3e0b01291a9747a282a8bc4c16024a411e971e62f19a144c1602525d0e4fc5e33428982c04902858358bc66871010809289458f319a14e6260b01251f85451044627c422f1301291e9745220588545e26024a5f0a8a218ac478845e260252411e2c4be144f8b8362113012d1e974e243102344c048166145641c5c1b108980922c462005697c5c1b1090c4a3e026020121b8287047811c24011c217270bc48e0585058350bc4042024617439617e3311811c250a81066178942e3202483027880483c2e850808f02503f0b0a810580e401c09b110bc4c04d0785c24161681d0b8885e2602580802140e62f0b8cd0e4f2d880d424d479044f8811e26023a2917880806a02343e2f1c8822a051642a2e13012e1f178e4430b028b6203a8b84a86026e144417c60af1007c0902d0b000618b05e1743890785f198808204f0be1719a1c40403501203a85c404035011a1f178e442051642a2a13012a0b164562039011b0a0200850398bc66872796c404212683c2c401362047898090090d8143423c08c2d81058138b058d30a26c668711890e404f0e62c6d05c406a1281201785d0e58201ac662213812810100d2140e23c08e8f16c5a1148086260a8a80944f1e6240a23808c09c2e872c2fc66202181251e172b0d90b880d62602483f2c2fc404115811e1f96839490b094560488843e2e26c5e334285c44250258685f8bc288b110940900fc2e872c100d6331181262f028b214a589c422a0248d05f170786 else 0x4162d8844c2c4c2f8086891823205164422612380e91e02850e1a8f1806e0488c4e2c3a14244851816211389c5852021c2a904847c3c468a8145b11084486a130580a2d0a401c908f2943c2e3c464320516c4421128b85c16029d200e481a25e2e4f464320516c4421128b85c060a90b5188f8b406110985c1424506f0a8c814050010c495316471983c2471246485828f022384540a2d8844c248e240e405169614708a8140712120a22c926c14a516c4404204c2092538145b11080e))
def mo511H11 (_ : Nat) : Nat := 0x1962836000b64a281cb408c1c6b9f9db0543c6ef8cd863f3f75e00038ae00021d3adb0a8000000000357e00028152e400000021fb96d0bca2ab5ae883fafcbdf6d800125c0005328002cc8000000037800081300000030a45bf104980800000000068050ed1547d38000473a85b65c063da20000004329f46b840005eb9c8600000022b38c77db06d4da7618000b5bfdb800000024539740010690000b33131d7c369cde32120006a05a1bf300000000002674adc13742fb177fad7070a4ad04adfce1800000162e0000000000000dba4041c47ac20000000000000ec8b814f5f2732a50003121bca8574e77763bcc0cbc27c000a4a0004338001045d180000001022e518000361c88befaa5800144e56691ac700000000106651f6a6000000000186d000111000021211380004bf62db0208edd64000000071700e0008697b000000006a0b11a811bbdd1591c5d026675001770a165a92cd99572a2b83654231494b85c24bb73ab2c09d44cbb21080fac5d510a5414d59f01a272e78f367213f254e42680c7278405f61169b8b5215eb7f599d981bbca6f43348de6d76d06a7e5c20707b3526222540ce36770d2577a4d7d0006937d23614754a1f610787840f98f54c3d9056b56484f268dcbb3085d88ee0955e54c777a471e98875464494b0632891350805e580000000006a4e104000000924add744bed700b96e669140d916000199fe166c40000305c7b36c8001778000a278001631550000000000000093bb0f2890c35581bf60ce0e62312222c000000d3a6ab54ea1c8960f66804c00000036328d85cdb588000142000098df6730b7340007210000d7e0002278001c59000286b0ff4d5e9f59f38695b8863e2c0ec7f2b000394532a41e000294dbabc1511f495a76e84b6ad1acf51c34433d714354906a1ed78729752c651456c9b8c8b81c0a30c017e9bb5a6f0914f40f255352d38f5d6849ca1c77c0000000806110101400000305004000080c0a0602080040c0001402010185800080000024000080c0402078100c79060102a0a118041a000700c0a0309800080615000000300000000905804140509800020a00000000003800000302800000a0004c8e330401418040007c160a0080804090202426010201c0001010101c06
def mo511D12 (_ : Nat) : Nat := 0x242e16865a2632207204a0c130085a196890f178c881081343c5c304e20222686582c14e204d0f171c100ca19688080b05093881383cbc5e162e86581e32202604c170f8502168b8ca18889012c5821222e32862414049300f178502168b8ca1888901303c5c70421408581e2e3286202404e0f17850a02160038880b898c01362e328416222404717858b8ca188890122162c1a22240468b8ca18905011a4f430784d3173288474750af0f01641b01b000ffd86ffc86ffd76ffd72ffd62ffd80ffd70ffd60ffd20ffd10fbd74fbd64fbc40fdd30
def mo511H12 (_ : Nat) : Nat := 0x12aee60e9d74bd700029b0000001905454000001d52b78000003aa8000000e1c000000700003599c973740000000000004bc08c00349000000390afec00001c174000000000000000000000000001f09430db684d930518002f980000000000000000028706185e15c10c132d4db63ebfc4017ce8e7a43cccc8800000310000000080c0000000000000021a209dfc93885aabe3c6900597b0f202d125014002615d440032380005900001680248b400217d458000b248d31200f4634000000000000001caf0661480000022797bc000002da4002075acd46000138d2c6c7c000000001ff8000002e49211b199fcc19cdfb67dec00000000000000000000000000255c000002959e74000000000001d280000009c400000045c0000036eec7addc00166733c0480000000000001808c400094c00000258810c4a0003dd8000000000000000b540010ca82000000000328aed40000035380000029ae154000000000000000d940018b1ec0000001cfc000000000de4000000000134000000002a4ef380010100021d6e8fb9c0019100000000000000000000000000008e8001abe114000000000000003f10000000003270000000000000000000000dc88d5085b6ae9470c00000394286c000000000000000b44987ba000183adead3c4a87900000000980018500000000000000034b8000c80000000837e6800159c000003e50a2c0000000013e4000000000002c280025cedf400000000000243eb365b800000271e66edd00000004407a651c003d6c1f063396000358e0ec000000000000000002844000bb80000000000000033b40000002a19fa6b0000ce0001c0a4a7d2c0000000000000000025bc0027228fb164003b426d80202040000c010000002000201408000180000000500c0203010000400058000802028100001008040403000040005000000e09000080800000040203008100601040000000018040000
def mo511D13 (_ : Nat) : Nat := 0x51684b091820091ff
def mo511H13 (_ : Nat) : Nat := 0x6a9479999e500000400050c2c00d10000000d861000002d00557e400e864c0000d4c5c2da45c86e46e7140040000040
def mo511L : Nat → Packing
  | 7 => (4,6,7,0,0,5,0,mo511D7)
  | 8 => (81,5,7,0,0,11,0,mo511D8)
  | 9 => (186,4,7,0,0,14,0,mo511D9)
  | 10 => (226,3,7,0,0,14,0,mo511D10)
  | 11 => (128,2,7,0,0,14,0,mo511D11)
  | 12 => (14,1,7,0,0,11,0,mo511D12)
  | 13 => (1,0,7,0,0,0,0,mo511D13)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 11 0 7 2 1 mo511H8
  | 9 => lookupWord 36 163 8 12 7 1 mo511H9
  | 10 => lookupWord 83 499 9 13 8 1 mo511H10
  | 11 => lookupWord 112 431 9 13 8 1 mo511H11
  | 12 => lookupWord 66 419 9 12 7 1 mo511H12
  | 13 => lookupWord 8 37 6 9 4 1 mo511H13
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,13,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P7_0 : CutRow mo511 7 0 4 := mixedCut (pos:=0x1048820a048811) (neg:=0x7816ad0b40f) (data:=fun _ => 0x53021060120120604332406012012060) rfl (by decide +kernel)
theorem mo511B7 : CutRow mo511 7 0 4 := mo511P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_0 : CutRow mo511 8 0 27 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_27 : CutRow mo511 8 27 54 := mixedCut (pos:=0x2090241089114008a048841) (neg:=0x129780b4f1b00f2d0b40f) (data:=fun _ => 0x120123601201236012012370120123707002137070021370700213707002137670021376700213767002137612012376280286719708267197082671506253705002537012012370120123701301207012012360700213707002137012012370428140304281403028028671471876714708767128028671280286719708268197082671970826714281437042014370506253705002537050625370506253605002537050025370120123801201237012012370471876614281436028028671470876715062537050025370420143701301307012012070) rfl (by decide +kernel)
theorem mo511B8 : CutRow mo511 8 0 81 := (@joinRow mo511 8 0 27 54 mo511P8_0 mo511P8_27)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : CutRow mo511 9 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_12 : CutRow mo511 9 12 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_108 : CutRow mo511 9 108 2 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_110 : CutRow mo511 9 110 76 := mixedCut (pos:=0x1110481089044408d010241) (neg:=0x1e07816879680f9c6c2525a) (data:=fun _ => 0x74410861434950408641576043405040434950808641576123103040231030404340604043406040434060402310204043405040937581509375815093758150937581509375815023102050231020504340505023102050434050505045038050450380504503805045038021102370214023804140537041405380434050802310207043405050234020508641577121102380214023804140538041405380434060505045038050450380414053804140505050450380504503805045038021402380211023802140238021402380414053804140538043405050414053805045038050450380414053802310204043406080434060501404508441405040414050404340603041405030414050402310304043406090434060404140509021102040414050402310303021102030) rfl (by decide +kernel)
theorem mo511B9 : CutRow mo511 9 0 186 := (@joinRow mo511 9 0 108 78 (@joinRow mo511 9 0 12 96 mo511P9_0 mo511P9_12) (@joinRow mo511 9 108 2 76 mo511P9_108 mo511P9_110))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : CutRow mo511 10 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_7 : CutRow mo511 10 7 55 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_62 : CutRow mo511 10 62 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_158 : CutRow mo511 10 158 23 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_181 : CutRow mo511 10 181 2 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_183 : CutRow mo511 10 183 43 := mixedCut (pos:=0x822210411a02048841) (neg:=0xf02d9c3c03db094ad0b40f) (data:=fun _ => 0x70131514520529645205296436340854110509541105095140620505402526034317050140150501401505034364050140620501406205064869260648692606486926034314060140620a0343640903436406014062060340170605402527014015060140150601406206014062060343640501401505014015050140150a01401506014015060323140503201405032314050323140501201205012012050120120501201205012012050) rfl (by decide +kernel)
theorem mo511B10 : CutRow mo511 10 0 226 := (@joinRow mo511 10 0 158 68 (@joinRow mo511 10 0 7 151 mo511P10_0 (@joinRow mo511 10 7 55 96 mo511P10_7 mo511P10_62)) (@joinRow mo511 10 158 23 45 mo511P10_158 (@joinRow mo511 10 181 2 43 mo511P10_181 mo511P10_183)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : CutRow mo511 11 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_2 : CutRow mo511 11 2 11 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_13 : CutRow mo511 11 13 69 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_82 : CutRow mo511 11 82 46 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B11 : CutRow mo511 11 0 128 := (@joinRow mo511 11 0 13 115 (@joinRow mo511 11 0 2 11 mo511P11_0 mo511P11_2) (@joinRow mo511 11 13 69 46 mo511P11_13 mo511P11_82))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : CutRow mo511 12 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_4 : CutRow mo511 12 4 10 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : CutRow mo511 12 0 14 := (@joinRow mo511 12 0 4 10 mo511P12_0 mo511P12_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : CutRow mo511 13 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : CutRow mo511 13 0 1 := mo511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511T : mixedTables mo511 13 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo511 0 0)
  · exact (mixedEmpty mo511 1 0)
  · exact (mixedEmpty mo511 2 0)
  · exact (mixedEmpty mo511 3 0)
  · exact (mixedEmpty mo511 4 0)
  · exact (mixedEmpty mo511 5 0)
  · exact (mixedEmpty mo511 6 0)
  · exact mo511B7
  · exact mo511B8
  · exact mo511B9
  · exact mo511B10
  · exact mo511B11
  · exact mo511B12
  · exact mo511B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511G : graphValid mo511 (boundsBefore K503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 13 nineInputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact mixedRoot (g:=mo511) (top:=13) (i:=0) (before_sound K503 (known_down V503)) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_9397

open PEqualNP.Outside.L_meta_9397 in
theorem PEqualNP.Outside.L_meta_9397 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 6 && x 8)) t → 14 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C, hf, hsize, heq⟩ := hs
  exact directSplit mo511R g511R ⟨C, hf, by omega, heq⟩
