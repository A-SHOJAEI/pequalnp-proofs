import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_8397.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_8397
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
def graph : Sig := 0xffffffffffeeffecffffffffffeaffe8ffffffffffeeeeecffeeeeecffeaeae8ffffffffffeeffecffffffffffeaffe8ffffffffffeeeeecffeeeeecffeaeae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7)
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 4) ||| (x 3 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7)
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 4) ||| (x 3 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7)
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
def eightEdge (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7)

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
def neighbor8453 (i : Fin 8) : Nat := [1,0,0,0,0,1,1,3].getD i.val 0
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
def K7 := extendKnown [] 4 [(7,[]),(25,[66,49]),(98,[98,81,66,16,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[(0x9f379f379f379f379f379f379f379f379f379f,0x16911691169116911691169116911691169116),(0xe3e9e3e9e3e9e3e9e3e9e3e9e3e9e3e9e3e9e3,0xa142a142a142a142a142a142a142a142a142a1),(0x0,0x0),(0x1c161c161c161c161c161c161c161c161c161c,0x886e886e886e886e886e886e886e886e886e88),(0x0,0x0),(0x60d860d860d860d860d860d860d860d860d860,0x50bd50bd50bd50bd50bd50bd50bd50bd50bd50),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[16,83]]
def g43D3 (_ : Nat) : Nat := 0xf
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g43D3)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B3 : block g43 3 0 1=true := g43P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=1048577) (before_sound K7 V7) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K7 4 [(43,[]),(51,[67]),(75,[101]),(83,[101,67]),(139,[117,101,49]),(141,[117,101,49,33]),(163,[117,81,97,65,16,48]),(166,[117,81,97,65,49,16,32]),(169,[113,97,65,33,48]),(170,[113,16,96,81,64,49,32]),(184,[113,49,48,96,65,32]),(232,[80,81,113,96,65,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V7 low43 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := plain_low (m:=15) (hints:=1) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=15) (cap:=4) (before_sound K43 V43) (8,0,7,0,4) (by decide +kernel) (by decide +kernel))
def K15 := extendKnown K43 5 [(15,[]),(23,[67]),(27,[66,49]),(29,[33,50,65]),(39,[83,67,16]),(71,[99,83,67,16]),(99,[98,81,66,16,48]),(102,[33,97,82,50,16,64]),(153,[115,99,50,48,82,64,16]),(226,[50,32,112,99,82,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V43 low15 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low121 : Lower true (varsX 121) (graphGoal 121) 6 := plain_low (m:=121) (hints:=90177539) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=121) (cap:=5) (before_sound K15 V15) (0,32,25,64,5) (by decide +kernel) (by decide +kernel))
def K121 := extendKnown K15 6 [(121,[]),(122,[100,83,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V121 : Known true K121 := extend_ok (m:=121) V15 low121 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 5 := plain_low (m:=173) (hints:=812646402) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=173) (cap:=4) (before_sound K121 V121) (4,0,169,0,4) (by decide +kernel) (by decide +kernel))
def K173 := extendKnown K121 5 [(173,[]),(174,[83,16]),(179,[117,66,33,49]),(186,[80,115,64,32,16]),(203,[82,101,114,33,16,48]),(233,[83,117,99,48,64,32]),(248,[83,117,50,48,98,64,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V121 low173 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 6 := plain_low (m:=47) (hints:=1048577) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=47) (cap:=5) (before_sound K173 V173) (32,0,15,0,5) (by decide +kernel) (by decide +kernel))
def K47 := extendKnown K173 6 [(47,[]),(55,[67]),(79,[101]),(87,[101,67]),(155,[117,101,66,49]),(157,[117,101,33,50,65]),(227,[82,81,114,97,66,16,48]),(230,[81,113,98,50,16,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V173 low47 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[(0x70fdeeb5e209b87ef75af104dc3f7bad78826e,0x510010056200a8800802b1005440040158802a),(0xbc0d30ea1bb05e0698750dd82f034c3a86ec17,0x285128f80cf01428947c06780a144a3e033c05),(0x0,0x0),(0x333431d8d578199a18ec6abc0ccd0c76355e0,0x6c502d885150362816c428a81b140b6214540),(0x43c2ad0a6c6e21e15685363710f0ab429b1b88,0x3aad2218ea001d56910c75000eab48863a80),(0x8c02924351b046014921a8d82300a490d46c11,0x87ae9707f30043d74b83f98021eba5c1fcc010),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(16,0,43,0,4),(0,32,25,2,5),(32,0,27,0,5),(8,0,51,0,4),(2,32,25,0,4)]
def g59A : List (List Nat) := [[],[67]]
def g59D4 (_ : Nat) : Nat := 0x57d4d20
def g59D5 (_ : Nat) : Nat := 0x60908400e140fd32fe20fd20
def g59H5 (_ : Nat) : Nat := 0x3c0
def g59D6 (_ : Nat) : Nat := 0x20e09f
def g59H6 (_ : Nat) : Nat := 0x6c0000000000006a0000000000000001600000000000000000900000000001280
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 5 0 1 g59H5
  | 6 => lookupWord 1 37 0 7 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 3=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=1048577) (before_sound K47 V47) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K47 7 [(59,[]),(91,[101]),(107,[100,83,16]),(115,[67,84,99,16]),(143,[117,101,66,49]),(167,[117,81,97,33,66,16,48]),(185,[113,97,33,48]),(234,[65,16,116,81,96,49,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V47 low59 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[(0xc3406101ffe38680c203ffc70d018407ff8e1a,0x824b860133a104970c026742092e1804ce8412),(0x9540b37c28cf2a8166f8519e5502cdf0a33caa,0x514511e485e0a28a23c90bc14514479217828),(0x0,0x0),(0x42a341c7c71c8546838f8e390a8d071f1c7215,0x408429f6cc04810853ed98090210a7db301204),(0x0,0x0),(0x3c1c9e7c152078393cf82a40f07279f05481e0,0x30012ee0b70060025dc16e00c004bb82dc0180),(0x0,0x0),(0x28bf1c8210fc517e390421f8a2fc720843f145,0x883ad00900fb1075a01201f620eb402403ec41),(0x0,0x0)]
def g171C : List ColumnInfo := [(2,0,169,0,4),(1,0,170,0,4),(8,0,163,0,4),(32,0,139,0,4),(128,0,43,0,4)]
def g171A : List (List Nat) := [[],[49,117],[16,83],[16,80,48,115],[48,16,113,81],[48,113],[80,115],[80,113,49,48],[112,49,81,16],[112,81]]
def g171D4 (_ : Nat) : Nat := 0x5dd4530
def g171D5 (_ : Nat) : Nat := 0x1030fd30fd10
def g171H5 (_ : Nat) : Nat := 0x800000
def g171D6 (_ : Nat) : Nat := 0x23440bf
def g171H6 (_ : Nat) : Nat := 0x394003071b4583d5800000e028020227000000000000000
def g171L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g171D4)
  | 5 => (2,1,3,0,0,3,0,g171D5)
  | 6 => (1,0,3,0,0,0,0,g171D6)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 8 0 4 g171H5
  | 6 => lookupWord 3 23 5 9 1 4 g171H6
  | _ => fun _ => none
def g171 : Forest := ⟨171,6,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 1=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P5_0 : block g171 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B5 : block g171 5 0 2=true := g171P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P6_0 : block g171 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B6 : block g171 6 0 1=true := g171P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact g171B4
  · exact g171B5
  · exact g171B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=806354945) (before_sound K59 V59) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K59 7 [(171,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V59 low171 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[(0xefbf00189adef7df7e003135bdefbefc00626b,0x18e1000000000031c2000000000063),(0x2873fe156013e050e7fc2ac027c0a1cff8558,0x18e71e60060ac031ce3cc00c1580639c798018),(0x518fbc1c441c80a31f7838883901463ef0711,0xa518e187c0143d4a31c30f80287a9463861f00),(0xd1e0c477292609a3c188ee524c13478311dca4,0x81f254d501185103e4a9aa0230a207c9535404),(0x3c44ec2e21b8007889d85c437000f113b0b886,0x3c0dab2a2006a2781b5654400d44f036aca880),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(4,0,27,0,5),(8,0,23,0,5),(16,0,15,0,5),(2,0,29,0,5),(6,0,25,0,4),(24,0,7,0,4)]
def g31A : List (List Nat) := [[],[67],[33],[33,67],[49,66],[49,66,33],[65,50,33],[65,50]]
def g31D4 (_ : Nat) : Nat := 0x31826d62141318fd91538426f6254d10
def g31D5 (_ : Nat) : Nat := 0x218022002040100200218050040db4e6c278b10910c02fea098df14131bfa9c217d53842fea6885f54d10f7a9221f531443ec20885bd4910
def g31H5 (_ : Nat) : Nat := 0x489c150690000000608000000
def g31D6 (_ : Nat) : Nat := 0x4581314850c4214312c580fd31fe10fd10
def g31H6 (_ : Nat) : Nat := 0x908000000000480030100125ac1807700000000000000004a800d044240000400a65c0020600000000194c100000140001
def g31D7 (_ : Nat) : Nat := 0x162218df
def g31H7 (_ : Nat) : Nat := 0xb800000000000002a2000000000ee000000400151e400890000060000020400000000080000072000a6000000
def g31L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g31D4)
  | 5 => (10,2,3,0,0,7,0,g31D5)
  | 6 => (3,1,3,0,0,6,0,g31D6)
  | 7 => (1,0,3,0,0,0,0,g31D7)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 9 2 3 g31H5
  | 6 => lookupWord 5 37 6 11 4 3 g31H6
  | 7 => lookupWord 4 37 6 9 2 3 g31H7
  | _ => fun _ => none
def g31 : Forest := ⟨31,7,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B4 : block g31 4 0 3=true := g31P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_1 : block g31 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 10=true := (@block_merge g31 5 0 1 9 g31P5_0 g31P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 3=true := g31P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P7_0 : block g31 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B7 : block g31 7 0 1=true := g31P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
  · exact g31B5
  · exact g31B6
  · exact g31B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 8 := lower_forest (g:=g31) (i:=0) (hints:=1) (before_sound K171 V171) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K171 8 [(31,[]),(103,[100,83,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V171 low31 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 7 := plain_low (m:=125) (hints:=90177538) (cap:=6) (by decide +kernel) (cut_root (u:=true) (m:=125) (cap:=6) (before_sound K31 V31) (4,0,121,0,6) (by decide +kernel) (by decide +kernel))
def K125 := extendKnown K31 7 [(125,[]),(126,[100,83,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V31 low125 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),(0x7fc47003c1f2b3fc1ff11c00f07cacff07fc47,0x794054a5129033a81e50152944a40cea079405),(0x8fc0300001e20cfd23f00c000078833f48fc03,0x86802b5aed6a8c5521a00ad6bb5aa315486802),(0xe0cb807c3e014f00f832e01f0f8053c03e0cb8,0xe0c1818c46201518b8306063118805462e0c18),(0x130280003e004f02c4c0a0000f8013c0b13028,0x13020e73b9c56a6244c0839cee715a98913020),(0x30344f83c01cb003cc0d13e0f0072c00f30344,0x240318cc668002c00900c63319a000b00240),(0x0,0x0),(0xcc390ffc000d0003330e43ff00034000ccc390,0xc180c633199408503060318cc66502140c180),(0x0,0x0)]
def g190C : List ColumnInfo := [(4,0,186,0,5),(0,4,184,2,5),(16,0,174,0,5),(0,16,166,8,5)]
def g190A : List (List Nat) := [[],[49,66,117]]
def g190D6 (_ : Nat) : Nat := 0xe413f
def g190L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g190D6)
  | _ => emptyPacking
def g190I (_ _ : Nat) : Option (Nat × Nat) := none
def g190 : Forest := ⟨190,6,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P6_0 : block g190 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B6 : block g190 6 0 1=true := g190P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : checkedTables g190 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g190 0 0 0 = true)
  · exact (rfl : block g190 1 0 0 = true)
  · exact (rfl : block g190 2 0 0 = true)
  · exact (rfl : block g190 3 0 0 = true)
  · exact (rfl : block g190 4 0 0 = true)
  · exact (rfl : block g190 5 0 0 = true)
  · exact g190B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 7 := lower_forest (g:=g190) (i:=0) (hints:=806568224) (before_sound K125 V125) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K125 7 [(190,[]),(237,[100,83,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V125 low190 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 8 := plain_low (m:=183) (hints:=1343225857) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=183) (cap:=7) (before_sound K190 V190) (16,0,167,0,7) (by decide +kernel) (by decide +kernel))
def K183 := extendKnown K190 8 [(183,[]),(189,[117,66,49]),(207,[100,67,83,16]),(219,[116,100,66,32,50,80,16]),(238,[81,98,113,66,16,48]),(243,[116,98,50,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V190 low183 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 8 := plain_low (m:=249) (hints:=895483907) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=249) (cap:=7) (before_sound K183 V183) (64,0,185,0,7) (by decide +kernel) (by decide +kernel))
def K249 := extendKnown K183 8 [(249,[]),(250,[100,83,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V183 low249 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := plain_low (m:=63) (hints:=1048577) (cap:=8) (by decide +kernel) (cut_root (u:=true) (m:=63) (cap:=8) (before_sound K249 V249) (32,0,31,0,8) (by decide +kernel) (by decide +kernel))
def K63 := extendKnown K249 9 [(63,[]),(95,[101]),(111,[100,83,16]),(119,[67,84,99,16]),(159,[117,101,66,49]),(231,[82,81,114,97,66,16,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V249 low63 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[(0x8d8901675640001ffc8ccc6d9ab1b1202ceac8,0x8880164124024e0010e2045120111002c8248),(0x6d06ba98c3a07f807efd3870000da0d7531874,0x1506929840a1800480801c380042a0d2530814),(0x0,0x0),(0x947066da141800638010808e7e728e0cdb4283,0x846022920416c91c283010ba68708c04524082),(0x51fdc5190058007c00014703c4ca3fb8a3200b,0x7317dc0900091203d2014f00858e62fb812001),(0x4a272f662987838003e23380210944e5ecc530,0x48212d6209021c29182662870d090425ac4120),(0x22c0d0a4a827fc00011303d0b124581a149504,0xa2d84004a00463d261190140f2b45b08009400),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(64,0,59,0,7),(32,0,91,0,7),(1,0,122,0,6),(16,0,107,0,7),(2,0,121,0,6),(16,8,98,1,5),(2,32,25,64,5),(2,64,25,32,5),(1,8,98,16,5),(1,16,98,8,5),(34,64,25,0,4),(0,32,25,66,6),(0,8,98,17,6),(8,0,115,0,7),(25,0,98,0,4),(96,0,27,0,5),(0,64,25,34,6),(24,0,99,0,5),(0,16,98,9,6),(64,32,25,2,5)]
def g123A : List (List Nat) := [[],[101],[67],[67,101],[16,83,100],[16,83,100,67],[16,99,84,67],[16,99,84]]
def g123D5 (_ : Nat) : Nat := 0x317dd76350520
def g123D6 (_ : Nat) : Nat := 0x1841028018943809faed20c41b7553634836fb1c82906df6350520
def g123H6 (_ : Nat) : Nat := 0x20000
def g123D7 (_ : Nat) : Nat := 0x488a19a20f200908810104407a18620e090c68c1458a410c420005810b3410e244070c1010c404ed0c085c18668984286c214263043632d5569a42dd2b2411646000ff55132ff55220ff90620ff55120ff90520ff50520bf58620bf586109f59640b7d8d20bb58810
def g123H7 (_ : Nat) : Nat := 0x29361e500002c28291800400000
def g123D8 (_ : Nat) : Nat := 0x102200458cd188444821349180309b531821c3b414c920608840b1208453422033848213452022408492071840888ed8078462480842804010cd20626d0842f8598b44c9f8c04512001fd42fe997f903fa81fe20fe907f843fa21fc10
def g123H8 (_ : Nat) : Nat := 0xb0f026f4c081cc001cb00098e613c5000f9319da0000000855c1f005c00080000053140400506240a14a32a4118000
def g123D9 (_ : Nat) : Nat := 0x46d13f
def g123H9 (_ : Nat) : Nat := 0x48f460000000008a00000000000000542001614000000000000014300000000000000000ab000000000001630012e02280000000000000000001c080000000000000604390002a400000000000000000000000000030abc6f2d40c00580000000002d5e4600000000000000000000000000000028800000000000c1dc2000000000000004100004300000000000014001
def g123L : Nat → Packing
  | 5 => (1,4,5,0,0,0,0,g123D5)
  | 6 => (4,3,5,0,0,6,0,g123D6)
  | 7 => (11,2,5,0,0,9,0,g123D7)
  | 8 => (9,1,5,0,0,9,0,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 7 0 3 g123H6
  | 7 => lookupWord 2 11 4 9 2 3 g123H7
  | 8 => lookupWord 7 31 5 11 4 3 g123H8
  | 9 => lookupWord 8 107 7 11 4 3 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 1=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 4=true := g123P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_3 : block g123 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_5 : block g123 7 5 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 11=true := (@block_merge g123 7 0 3 8 g123P7_0 (@block_merge g123 7 3 2 6 g123P7_3 g123P7_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 9=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : block g123 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B9 : block g123 9 0 1=true := g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=17825793) (before_sound K63 V63) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K63 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V63 low123 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[(0x15fd53701f21314071f82a4057f54dc07c84c5,0x10a000701f0101650a04e040428001c07c0405),(0x4be1ec09e045a4838e33ad512f87b027811692,0x43496001a040a098214015090d258006810282),(0x4c14bfbf460094400fc001813052fefd180251,0xac169f8e40981402d4b10082b05a7e39026050),(0x344800cba8e80b0c700c0238d120032ea3a02c,0xa558288980e0021094da063e9560a226038008),(0x0,0x0),(0x8a0202049b1640b38003d6d6280808126c5902,0xa80682501a060004969be2f6a01a0940681800),(0x0,0x0),(0xe022418675da4a3c000450af80890619d76928,0x52a155266518482b692411014a855499946120),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,5),(1,0,174,0,5),(4,0,171,0,7),(8,0,167,0,7),(32,0,143,0,7),(0,128,7,40,6),(128,0,47,0,6)]
def g175A : List (List Nat) := [[],[16,83]]
def g175D5 (_ : Nat) : Nat := 0x4ef7258610
def g175D6 (_ : Nat) : Nat := 0x2044080104200ac85b400bf58610fbd8910bbd8910b758c10bb58810
def g175H6 (_ : Nat) : Nat := 0xa
def g175D7 (_ : Nat) : Nat := 0x196f2804756bca101d972e8407888807f843fa21fc10
def g175H7 (_ : Nat) : Nat := 0x7200a3f000e4298100000001
def g175D8 (_ : Nat) : Nat := 0x5d1a17f
def g175H8 (_ : Nat) : Nat := 0x13800000000788400069
def g175L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g175D5)
  | 6 => (5,2,3,0,0,6,0,g175D6)
  | 7 => (3,1,3,0,0,7,0,g175D7)
  | 8 => (1,0,3,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 0 1 g175H6
  | 7 => lookupWord 2 11 4 8 3 1 g175H7
  | 8 => lookupWord 1 11 0 7 2 1 g175H8
  | _ => fun _ => none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 1=true := g175P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_3 : block g175 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 5=true := (@block_merge g175 6 0 3 2 g175P6_0 g175P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 3=true := g175P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 1=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=806354945) (before_sound K123 V123) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K123 9 [(175,[]),(187,[117,66,49]),(235,[81,98,113,66,16,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V123 low175 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 9 := plain_low (m:=253) (hints:=895483906) (cap:=8) (by decide +kernel) (cut_root (u:=true) (m:=253) (cap:=8) (before_sound K175 V175) (4,0,249,0,8) (by decide +kernel) (by decide +kernel))
def K253 := extendKnown K175 9 [(253,[]),(254,[100,83,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V175 low253 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 10 := plain_low (m:=223) (hints:=822083585) (cap:=9) (by decide +kernel) (cut_root (u:=true) (m:=223) (cap:=9) (before_sound K253 V253) (64,0,159,0,9) (by decide +kernel) (by decide +kernel))
def K223 := extendKnown K253 10 [(223,[]),(247,[100,83,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V253 low223 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0x5c081cf1e2d58fc4602a0d016f00c9438d6121,0x1010203838000000d000300c101884121),(0x6343234faea246080c44f0001a2c2abc7060c6,0x80040080884040000405000580c288c502086),(0xbcb7844000004004686ea100056217ae810045,0xb6bf94529100403f6bbea23504621622039840),(0x8098d680007119a293910277e4997c24541918,0x8188160808701c22c341826364882c24440808),(0x4d0c834510cb04033901e7698b194c0501838,0x3677c834558c20513492509c983512c8101010),(0xd735340c112a207b8405529822cbc003aa8680,0x77311c04033b907c9e1403902283c003a08200),(0x806403221d48633381a104c8904621110a8602,0x80ce832354406b8301a92c6e815001100a0400),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(4,0,123,0,10),(16,0,111,0,9),(1,0,126,0,7),(2,0,125,0,7),(32,0,95,0,9),(0,84,0,43,3),(64,0,63,0,9),(8,0,119,0,9),(1,8,102,16,6),(2,32,29,64,6),(4,32,25,66,6),(1,16,102,8,6),(6,0,121,0,6),(2,64,29,32,6),(9,16,102,0,5),(36,0,91,0,7),(24,0,103,0,8),(0,8,102,17,7),(16,8,102,1,6),(0,16,102,9,7),(8,16,102,1,6),(12,0,115,0,7),(5,0,122,0,6),(4,8,98,17,6),(0,32,29,66,7),(96,0,31,0,8),(34,64,29,0,5),(0,76,0,51,3),(40,0,87,0,6),(0,64,29,34,7),(5,8,98,16,5),(64,32,29,2,6)]
def g127A : List (List Nat) := [[],[101],[67],[67,101],[16,83,100],[16,83,100,67],[16,99,84,67],[16,99,84]]
def g127D5 (_ : Nat) : Nat := 0x142bed985e5183dc910
def g127D6 (_ : Nat) : Nat := 0xc801000000000000000000000f04186807a74645e58524c46403a342e28221c161000a2fe9975e11304423e7a9dc88154110c6b6179460f724431af85e5183dc910aeae9183e03724428efa65d7825cd10a2fe9975e11734430bf86e51735461087be8998dce518429afa25d7844c110c6bdd192205504c30bd96dd08154130c6bdd392602514c21efa26637194530a79688815c5508c21efa26628794630a3be9995e09718c28efa6617825c630979688915d5718c23cfa2662518c130
def g127H6 (_ : Nat) : Nat := 0x0
def g127D7 (j : Nat) : Nat := (if j<1 then 0xa3de3a234232a2ee2b225223a2221c21aa16e1320f609603601dfe1fa5f69f2decde49e31dd1db9d7dd41ce1ca5c45bc1b3db01aa1a65a059c99b19999398fd89d8618257e97897717356f969965d6215e55cd5915314f54dd4c54654294113d53bd3813453092f12b527923d19517d11d1050c908d051039020fe4f84f6cf30f18eb8e58e40de0dc8d8cd50d38cfccc0c60c24aecab0a74a5ca44a089cc9b497893c8dc87c7d47747146906305f45dc5584f84bc4804203302882282101b012c060002fd724b9aa0885eee517354110df3b9102a82213f697205504437cee5c0aa08867b2637254110d76c36e5282215ec9854f72442bdf30a9ee48867b61583dc910cf7c2b07b92215ed91e0f724433df0bc1ee48863fe197354610df4c1f01b9221beb83e0372442bd92ea9ee48857be5d53dc910bd7ca2e7b92217eb9060f72442f5f28c1ee4884fb64b8754d10cf6baf04b9a219ef75e097344337aebc22e68866fdd7845cd10df5c930f884215bf945cd51843fc703c06e48877ae1f8244010ef5cbf0488021deb92e1d10042bdd30b92200867be5f8244010ee6b9f04880219ef87e09100433df25c3a200867be49819c010ff1b92a108221fe372dc210443fc721b9420885f9e497584110df44c6e4a82216f7965461044377708a8260886ebe13724c110cdebaf08982219bf75e1130442bdf24baa608853fe59754c110cf7cc6e5182219ee87dca30442bdf24bac608853fe59758c1108ffcc2eb18221fe3724c550443fc723b92a0885bde597584110af7c930f28a615bf9461e514c33e902b8aa11867de057154230af7c92e2a84613ed92205508c25fb2c40aa1184fbe4980946308ffcbb0128c619ef9261e518c2bdf24c3ca31847f6628794630cf6c8704b8c619ef90e09718c23fb31b8ca29867be57825c630cf6c2f04b8c619ef85e09718c2bef22c2ae31857be49855c630a7fcb30ab8c619ef829c5718c33daebc12e31867be5f825c630afa48aeab8c612ff96616718c27db2440aeb184bf658815d630cf6c910e98aa19ed95e09718c2b7f28b9ca30867be4987946109f7c930f28c219ef9260773842dbf2ca8c60984fbe4980946109eecc4a318261bcf92606304c3a7ee8a8aa0984fb6488154130cdfba102a82612fd96205504c33df24c0ee6a866fdd38154130cdfba700a8a61cbf86dd1514c27df24c04a29863fe1b73546108fecc6e728c219bf74602514c23dd30b92200867ae4b87440108f6c910e98aa19cd73e09100423df24c0ee6a857aa6172440109f5c930f884219eb87e09100423df24c0ce00847be4987946108f7c9303b9c215af945cf7244335f09b9260884f3e49818c130df1c0f01b92211ef9261e518c2b5f28c1ee48862fe1b7454530c76c36e528221ae986dca504427cb2440aa08875a5d78244010 else 0xd203a406170808084836006808208000c867080d0026406820c809c1480901000a074009201d0022000040f53b98301cce00808103a60541200ac00a0ac0138205030c41038107600640830ac00b820410001000b0180250022ab0058006880d00163300203420e84141a9c25383a7074e0810804c0890b40080025022100010006081c7040e080010000095410b021300800082000f7304000013003e0040002e095022100030400042027339020001a40800003c1040e083c10605660b82084c25268141c23209211c1040008002981e08200001900302b005027005c4f0c2212220ac0169e22158207020e07020ac0081e6d240c3f0c0820282050623900941202692496481bcde1d271c42468020105600ac08b4407e60600f48e016c0820)
def g127H7 (_ : Nat) : Nat := 0x60f705b0b39100063100000000030600000000000088010e000712000000000000000c0c00a000f0351000028e000000000000000102000c13e0d000000b11d07000000000000000130304000d00b01000000000000309708043081000100
def g127D8 (j : Nat) : Nat := (if j<1 then 0x70040df2c1cdc9a18f0438c01f35870d381701027f207c94e05c038b84fc81f25870d381301423f207c861c205c043cf3587081700c10f207c205c0304847305f08101f0103a13c211cfc0043f713b2dd78ea974739edcd8e5972738cdc08ded6f1373db80dad6d1364db08d756ad352da78d1968533dd9d0cd966732dd950c9564331dd8c8c5161f30bd848c15605301d7f8bed5e52efd760b8d5bf2d8d6a8b4159f2cbd650b155832b9d5b0abd54929fd4e8a6552d294d480a21503277d3709954b5252d258909479236d1808a5443217d06080d3ef1eccf307713a31cbce106e53631accd20661323188cc085e92e916dcb185752a9149ca084dd259122c8f0451215100c7b03b11c50dac6903251850bac588299135091c4401fd0ef06fc3281650a1049c2100e5063026c0f005d021007c000dff7394610dfd754c110bfd8794610fef724c110fed73dc910ff9504c110fef7284110fbf7454530fde518c130f7d5154130bfc8154130bff8154130ff65184110fde514c530bff8054530fef83dc910fdd518c130bfc8754d10bff8754d10bfe878c110fed83dc910dff758c110dfd758c110dfd755cd10dfd7394610dff75dcd10fef728c110fef73dc910ff9508c110dfd7354610dff7354610dff754c110bfd8094610dff755cd10fef80dc910ff55184110dfd855c630dff855c630dfe715c630ffb7354110fef825c630dfe8794630bff855c630bfd859c630bfc815d630bff815d630dff8744010fef8244010fef7254110fef7294110dfd755c630bfd8094530dff7194530fdd8394530ff77584110fbf7494530dfd8794530ff97354110ff57584110dfd7154230bfc8154230bff8154230bfd8094630fed53dc910dfd8794630dfe8794530feb7254110bf48154110bf78154110def7254110ff131541109fe878c110def728c110bbf844c110def724c110feb7294110fe77284110ff37084110ff150841109fd819c0109ff8744010ddd7344010bef8244010ded7244010dfb8744010def7284110def825c6309fc874c5509fd8794630feb8244010dbf7494530dbf7454530dbf7454130bdd818c1309fd81dce10def825c610bef825c6309fd8794610aff86546109fd811c153bf987c4210bbf845cd109fd81dcd50bef825cd10def7294110afd8694110def73dc910def80dc910ded73dc910ded53dc910feb80dc910def83dc910ded83dc910de97284010d797584010dce735c810dcd735c8108fd86dd630d9d745cc109ed821c5509dd831c550d9e745cc109fb8744010d797544010de972440108fd861c550af986941109ef825cd109bf845cd10af986942109ed829c2109ef825c6109bf845ce109bf845d5309ef825c63097d85dcc109bd84dcc109ed82dcc109dd879cc10d5e759cc10d5e755cc10d5d755cc108fd86dd610 else 0x23508883a00a4148061a050c744086b40c290ce9c322508704088107041a08887530805821010c0d3360e38c1d084c044229820e224048584c26088838a060410e01e0b209820e2219ad033a408cd82170040487c010121f0015386c290ce9d40403120c53868c814e1b30c12508893b05010824e221920c13888881054e1d033a406880410c088e53208b4c083018e088c508841480618e50d0062c8540862330d010488cc30c9c02320c700740041523384064104100c830113320c064c422822400604484520485c0060419020636260e3c1c1108113481a04d535244c10c3049401e08883900800381e086120a0874388881c82801d21c1230b3b0070eccc03418e0c022063810c384c0442280e2240064850e0104e388418e140242486048010882c173491227305840101d2700e6662137349c0317c5d0c453dcd244b0137213cce0cf4811c3c048e830c025853f00110414d1b4913063761054e505d3e36219f0040f1d07103761054e3cd5cc4d23041c5c410c041171104286848584700af216c81211c030584068481f00c1a1216100605c0393a8b3868485818170138d1b891383178f110704c058b06848584018130101bcc13c817c211ce0605c05d35245c4301046c4c1c115cdc8c1a18f0436c83625870f00004049373cda1c3c0000548078e53046c4c1418a24278f0fc14173490448909e3c3f05cc15210178ea7c1734810388f04801083a0c3009614fc0044737270f3c5c43046c4c14196c1cdc9a1058e309808883dcd27001903f838e7bc013063ece863f062010c13c01a16102f372199870040db20d896003c000114e2257372580f040b35171107734904c040e9ca33352058470048114cc9ac892e0ce3690426a4b0a5b3a40b21d0126a2a9acc92c89ce0903653cb33830b224a1b3a413409a928623326b224b81ad033a4129acc92c8c2ce9c914048b73058484780101f39212b1cc1611e00407cfc050b04fcf238708101d012102dcc1613c204074048ed26870e3f0010e161211f3c80407c0478066cf370f381e211b207c3c01188330847c81f201700e1bcc161211e007cfc048486f30584780101f3f014181bcc161211e0c00407ce5f80eacf0f3f001e2107a72134817c211cfc04fc8bb0737258708411f22661cdc9c0103859e84f08473f00e2dcc161211e1c20406c0570f3f346f244c5c441b04117f2274fcdc9c01104409dcf352)
def g127H8 (_ : Nat) : Nat := 0xa1e0000c14480480000001c034000000000000000c3480000000000102dd867f0800000000000000000000000000010ba00000000000000082000000000e0e381c8d20f02460f2000000000000000206cc2600000000000000060750000000301800000000000000000000000c5e000000009001c1080007823000000002126859000140a8000007fb26f6043031800072a60000ca90000000140dc00000000000d1f60aa882e000000000000000000001b80000000000000000000000e0d16160000000000000000000000090faf102c1fe028d0f961140002c4c000000018358000a04200000000000603e0003c2f0000000000000000000f062000000000000000e20483780170001840000078020000000000000000000c1c000000000000000102200000000011b81c903b00000001c208000f03985d400049430000a02d925082900000003c1300000000f90340b000078eeb932139000000000000000721800000001c1a0000000000000000000c0c400000000000000171a713980000000e138000000010d40000000000000000000000361974bf417c0000000709b9068812c44dfa929940000707390b40002829800000000000000000000000000494800058bfc1dc000000098900000000680100016154000000000000000000000070c20000000000000000000000600a0000000000000000000000000000000000e1b40000000f0320000000000002cd4030000382c80aec0f000000000001193400030040000000000000000001e1fa832000000006140c360000000000000000000000000000000000000000000000000d066000200c2852e04025a580a587b8cbfa1588ad80000001810c21180000000f9440000000e4e83064000204bf8a1a5a05092e772300804a81f0000826c00000000000c8b08128000285c90a9c5dc0000000000121e80000836000000000007c120000000000048780001603e51000000000d0940168000f8d6418040a80005074811d009a838000000000000000000180f509c0805000000000005866f03b012203a104f00000003624984900000002d210000000000000000000000000000007832703c00010077808226200000000000000085ac000000090440000000000000000000000000092540000000000000000000b09000028a205a94018027530260440005418203400028035807c0ca000041784560000000103b382b000020d40000000000000000000000018040202000040200008140401008100000000000000008000007010040000000040002000080402000080000000040000000180603000100200070000201018000002008040001
def g127D9 (_ : Nat) : Nat := 0x10639a04e5260120c934e4588c02410e2c439c02410c3448b11801821f00e12e52508e208304471ac00dc824942396388e006e5202a11c91b984e4609f008206e61390730c020838c1ce01220639804b949423822304006e5202a11c8422e0a7111dca4c00ca079b260a11c10f986e413828470440b10e7324c39f00212546890638d122c4600608b34e520b11804822336417844671a27003045c688398601036080c2c8812339cd804a4a00a390c30e0b22048c986c64826203609f0022c31d08045890e23861c00819ae44e1119f00c3458911c0103cf8090d905881a24182c049a16e5209c2233e0250001a2c488e184103293871a2c4e1c00819218689c8c30a7118091a27ce46187002064b949c04e7c031d31e736461853e0105063a10c7907918614e0b01874c791d9b230c380415e720b11c0167c0479e083364c39c734241b9cc905e1119f01624683c82f088cf809380ece6a1863e08820a0767350c382247044a60c2c470c3822090450e076734461853e01008b0f86cc4162300304487c364588c026202241d9cd11861c02086180c891029323c2ce6c39f009240930e47802b39b0e7c00e21a2c470c380c89044097399250c31f002243e1722c460120881a26847c00c10e74c79079b250c11c115873e61b9048b11801032ce98f39b230c29f0080459d31e736461853e00450d1624470040f3e024989c2233e07208873423e0120861a27c83cd930101049d31e7203c03a39074c79cd9300e10401f23b364c11c410241b9cc928618f80414e5250c02440de48e6c9808021fc92271f364c0208c29c8e61b9048b060b0167cee1ce9a20b11804822f0e7cc372091620182405f9e19b261ce8079944bc658328a92647e636917689c442219508c8204025f96f7f7963bb9d36e6b71db7f5b9ad7a68cb3a5948c5f60d2f39712b4457fab3d506a294eea67d2d0915468221107e7f33d01d6ce2c6d835799a8c125cb2c31520a224c5239107c7a638e1a80c805b629d12f88843aa1a50b704c01ba08a01b8003fea8c21ff54210ffaeb087ff10843fea8261ff54530ffca2987ff73443feb9a21ff54d10ffaa1187fe518c3ff28c21ff5c630ffce3187fd50443fe88021ff94110ffc20887fd30443fe98aa1ff5d630ffee6a87fe30442ff38421fe94210ff420085fe70043fca8421fb5c810fbae6085fd73043ef39821fe54110bfee6885ff73042feb9a21fd84110fdee4887fa50443fd884217fdc153bf8e0a9efd76942feb9ca17f9c650bfae3285ff73543bea9aa17fdc550bf8e2a877e50542ffbac617f5d610bfce3185fd718c2feb8c217f5ce10bfee7087f910042ffbac217f5d630fba62985fc714c2ffb8a61efdd130bfaea985ff754c3ef182616fdd130bbae6084fd76942f6b90217bdc910
def g127H9 (_ : Nat) : Nat := 0x9839a10112a9e2400014043c00800000000002c81d40290e9207070f183178b621ed01400000001050c081297512b00000ea6384e331d808aa2b024fd4e0714120e80005268f9e113a446ec0640001b3280006509506b846144200012a380005e1b503d51fc0003955e83d2034000016f48b04604000487e0000000000000000001e5e44350056f2e00001b0f886532ed41dcf46800f1267a2114a48000000180800003c800001c02be3860520001c0bc0000000f8d7d2394430000000100264a7f68500000000000748280c00000c2d00000000487921e8000006ee9480007622f2e3908c0088000a00911fba2e8000000000000002e560cdad8130aa1063000000012103c8660bf615503e80000000504e00a300000000000b230000d0720001406000000000002c374849000061500000000102a99e54210182b31b80ac8a66c1282a785a91024824404b0a0f145517860420002239a167410fa9100003a7f6101722ed12000022ba2c86232f8830001212fb22082658440002416bc6de0a2b57643f800000ae19bde3a2044c2d66192538905b000192200000000308c058c0000000000000004287989f07e00000002a76a42c644ec238000000000000007172000180a6528800058bc423710dd221c0a741a5728000030584049c0bb06ce48c21e0000081d609800000000000483e000282080000000000183840672abce1b4000000000000000000548d806759cc00062898cf4000000041013c04000088e0000a4ce000084734781cb7002f8219889420f513b43378484068b215cc34c2c7034c1c480d9e1aa866622881f584a20e5e067c341921c0f4817163d0000000000014ad000000000000440800090b20003a02624820ec00000000885142a601f73fc42660300135c13803c00000000000615e32fda9c80000000b05c0000240800000000000000000000000000221c96d00003a0000010050000000221a8a1a00000000000000000000000000000094f4000000078360000c889745142438d840e041eac44000061ac0005140e0c3849ac186e3d40ea016050fbc6f88a8f21c000783a22ae00000004e7488b20003e930000303e82210ae0c46c076017b80180000000d0e4c010000f105604ce3cc932000001cc8b26835f0de00200003006601cf50c000000000004117e24f079000168f5145e84f000000000000000e836ba2e031000024e7c61e0b48023c91441f202ef02aa8950d3ccbbd08b7899752600b00800090301c100201014000002808060800004000705000060802800060100808120302004040d0781002000000814030080000020002400010080810060003c020200000000502024100005018040a0080c00010580400000302408000080c0e0a1a020000c0000406090000000040400008000180c0001
def g127D10 (_ : Nat) : Nat := 0x191108092068676442c8809089c199848678092399a44078021f93a69101e0208e619e690b220089e709a486780718404786798d9092c880308fd25a2650266240c000ff54ffe50ff543fe30ff4c3fe10ff443fc10
def g127H10 (_ : Nat) : Nat := 0x240740340000000000000141b78640000002f32000280f7896a1f5ca8000090440e0c0c0000002907000222002e86210000000702322e24d400080c80000000000ed0c5030000c1958dc000a04c0006004000000000028aee3200000000002a0d428a000183c0005101d32c0a2c15108f88dd05cc457074430000000000000000000000081c00000000000000000000212700014c70000000000000000005420002c4884a60bed105025000188c2110000502d402000101e409f72928e1a2a0000000d2fc00040a6c3580c6849d10bc120003b262ae8000701043928f40000000c090003a27e0ae03e370151d000003b0001e4200000000000000a21800000034942088000951400002b400000000000000c3600000000003e2242e00009310495c0e8000445400000014210001203982c000000082e0003ea87300020e83b0b40c96c37000000000004c90000000000274110cd01f000280cb8d800000000000000000fcac000b8e8000000000084cfc1050f00000001c18000000000024470000cc3509812b0000000000122900584a850b000000020c5aae1a26f21cc05b440000809253600000006890000b2f4000304400090fc838d924000f02800310bd0060320c43d0a8b3688a000054a8000000000000000000001727000222f806a919105144684fca1500000000002243ed08000b0f612500000007a8bd1a649800000d10b00003140c0b400015040000000000143ec1c00004000b0080000020000400010002c08000000c0000020200401018100205010001400008000002000180001000040002000040000020000004010080001
def g127D11 (_ : Nat) : Nat := 0xcc0c409c03ff
def g127H11 (_ : Nat) : Nat := 0xe9000000000000031000000000000001c00e18000000000000000000000073c000000015c00000000000078800814000000000000003e30000000000003ee0000000000fcc0067f65000000000000000001010000000000000c2ed00025000000000000000000000000024d49b0e70c0080000000002b6d300000000000000000000000014000
def g127L : Nat → Packing
  | 5 => (1,6,5,0,0,0,0,g127D5)
  | 6 => (20,5,5,0,0,8,0,g127D6)
  | 7 => (130,4,5,0,0,12,0,g127D7)
  | 8 => (143,3,5,0,0,13,0,g127D8)
  | 9 => (74,2,5,0,0,13,0,g127D9)
  | 10 => (8,1,5,0,0,9,0,g127D10)
  | 11 => (1,0,5,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 7 0 3 g127H6
  | 7 => lookupWord 8 59 6 12 5 3 g127H7
  | 8 => lookupWord 64 479 9 15 8 3 g127H8
  | 9 => lookupWord 107 479 9 15 8 3 g127H9
  | 10 => lookupWord 56 307 9 14 7 3 g127H10
  | 11 => lookupWord 8 107 7 10 3 3 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 1=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 20=true := g127P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_22 : block g127 7 22 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_118 : block g127 7 118 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 130=true := (@block_merge g127 7 0 22 108 g127P7_0 (@block_merge g127 7 22 96 12 g127P7_22 g127P7_118))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_30 : block g127 8 30 47=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_77 : block g127 8 77 66=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 143=true := (@block_merge g127 8 0 30 113 g127P8_0 (@block_merge g127 8 30 47 66 g127P8_30 g127P8_77))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_5 : block g127 9 5 45=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_50 : block g127 9 50 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 74=true := (@block_merge g127 9 0 5 69 g127P9_0 (@block_merge g127 9 5 45 24 g127P9_5 g127P9_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 8=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11_0 : block g127 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B11 : block g127 11 0 1=true := g127P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
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
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=17825793) (before_sound K223 V223) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K223 12 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V223 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[(0x5e4ab00c91aa02826fb4bbec39d0a18280a33,0x12800820d9010600180818000823),(0x4341c2f63441c0143b0df8a088a214c1c461b0,0x42001184044101000b0276a088801481c40190),(0x321941fc954040141020000e5b6fae61806281,0xb4594479b1044cf7502000197367a262137200),(0xbcbe144922bf3fe986140640004032a2deac40,0x20100041220837a003240600884212a2ca2440),(0xfa197800cba40ec2c8c2051004b47420368042,0xda8b7eb6d9a40842c802601124a56545348000),(0x7000200220084e0ae904b1017400c91c41110c,0x3039a0636388fedaa09481055100480c010008),(0x0,0x0),(0x88020c9900431103500800c93458c19e01140c,0xcb064c9c9c770005504910ea26188110001004),(0x0,0x0)]
def g191C : List ColumnInfo := [(1,0,190,0,7),(16,0,175,0,9),(2,32,29,128,6),(8,0,183,0,8),(12,0,179,0,5),(4,0,187,0,9),(0,4,184,3,6),(0,16,166,9,6),(2,0,189,0,8),(9,16,166,0,4),(7,0,184,0,4),(32,0,159,0,9),(128,0,63,0,9),(3,4,184,0,4),(8,128,23,32,6)]
def g191A : List (List Nat) := [[],[49,66,117]]
def g191D6 (_ : Nat) : Nat := 0xf624c3023f730b80e098e6be13825cd10ad7ca2e7b92215af9460f72442fc324402628866be13724c110
def g191D7 (_ : Nat) : Nat := 0x1441040814c162cc208c4202080001020f5040000000821c0860a205e2101001f0e3ddd0bca89b95887b6e68625c564927130d00def724c110ff0804c510ff3804c510fe7724c510ded83dc910ded73dc910dfb805cd109ff805cd10fd5314c110bfb805cd10bbf845cd10df9701c131bed821c131bef825c131dfb709c131bf5819c1319fd879c131def825cd109ef825cd109bf845ce10
def g191H7 (_ : Nat) : Nat := 0xc00000d40000e1a3f2650000
def g191D8 (_ : Nat) : Nat := 0x6406002894a92238736122a901804a26ea48942254a4903786765eb8c7411e764e3ad000fe769e250be19d9656a4e240be159e3dc1411e625004769ea40de778c19d03c14ff3c0d230cae24c7b1a44e0cc18001ffdc131ffce098ffd704c7fe38263ff5cd10ffa60885ff704c6feb9c217fdcd10bfae6887ef72443fa98a217bdc910
def g191H8 (_ : Nat) : Nat := 0x502cc00000002320000af14a10000000342a2c00b1acd003ce0000000000a2400a4400e4193a100081d62000e6ccc000000002131002e710c00b0400003d200000d938f000000000001000040001
def g191D9 (_ : Nat) : Nat := 0x39b88ea81c7c8eea040eae6e33a8104575c03fd31ff843fd10
def g191H9 (_ : Nat) : Nat := 0x5359c5400d18024000003911600000000069943c5440000800000000414014c00004
def g191D10 (_ : Nat) : Nat := 0x19626b037f
def g191H10 (_ : Nat) : Nat := 0x2a89c2be00000000000
def g191L : Nat → Packing
  | 6 => (6,4,4,0,0,5,0,g191D6)
  | 7 => (20,3,4,0,0,8,0,g191D7)
  | 8 => (13,2,4,0,0,10,0,g191D8)
  | 9 => (3,1,4,0,0,7,0,g191D9)
  | 10 => (1,0,4,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 11 4 8 3 1 g191H7
  | 8 => lookupWord 9 59 6 10 5 1 g191H8
  | 9 => lookupWord 4 29 5 9 4 1 g191H9
  | 10 => lookupWord 1 11 0 7 2 1 g191H10
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : block g191 6 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B6 : block g191 6 0 6=true := g191P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_2 : block g191 7 2 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 20=true := (@block_merge g191 7 0 2 18 g191P7_0 g191P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_1 : block g191 8 1 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_7 : block g191 8 7 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 13=true := (@block_merge g191 8 0 1 12 g191P8_0 (@block_merge g191 8 1 6 6 g191P8_1 g191P8_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 3=true := g191P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 1=true := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact g191B6
  · exact g191B7
  · exact g191B8
  · exact g191B9
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=806354945) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[]),(239,[100,83,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[(0x190665060080c6534f744e580458734ca8a8a2,0x51002002894244c20554085004086304a82022),(0x826082d1285024247c146ecbda0380215451a8,0x8601021020902224c809460ac8030021540188),(0x0,0x0),(0x6480402c41a9c96280e9802c15b48a7355a015,0x4811295090a000c0a8002c10b48071148011),(0xb986250244000b11038bb286014e7d0e500816,0x82b6465004010b190a03b383a3431c8a400804),(0x25918a0be16108c001211b3a08486eeaa4740,0x481028c8028c03011201a1000486cea04440),(0x91329e51124a3080300631247e931911281608,0x51b62443126c108034e4300437f03910081200),(0x54292628a72d0178a000481008204490870041,0xd7b72652272d517c3200cc5048084000030000),(0x0,0x0)]
def g251C : List ColumnInfo := [(2,0,249,0,8),(64,0,187,0,9),(16,0,235,0,9),(1,0,250,0,8),(0,32,25,194,7),(1,8,98,144,6),(67,0,184,0,4),(3,0,248,0,5),(8,0,243,0,8),(32,0,219,0,8),(128,0,123,0,10),(34,64,153,0,5),(66,0,185,0,7),(96,0,155,0,6),(64,32,25,130,6),(0,64,153,34,7),(2,64,153,32,6),(32,64,153,2,6),(0,16,226,9,7),(24,0,227,0,6),(1,16,226,8,6),(9,16,226,0,5),(0,8,98,145,7),(16,8,98,129,6),(2,32,25,192,6),(19,0,232,0,4),(17,8,98,128,5),(17,0,234,0,7),(8,16,226,1,6),(129,8,98,16,5),(40,128,83,0,4),(72,0,179,0,5),(136,0,115,0,7),(98,0,153,0,5),(25,0,226,0,5),(128,8,98,17,6),(128,32,25,66,6),(65,0,186,0,5),(80,0,171,0,7),(130,0,121,0,6),(66,32,25,128,5),(130,32,25,64,5),(192,32,25,2,5),(144,8,98,1,5)]
def g251A : List (List Nat) := [[],[16,83,100]]
def g251D6 (_ : Nat) : Nat := 0x2d2baa28a725a422a11f9e1c9b199816951392108f0d8c0a8907860483018025eba95c87250110a57e9574e0d7244315f85e4d7250610a75e8554e0d72843d15545cd5150420f0d5d95454541083d16545ce5150420f0d5da5494541083535979525150420a5daa0855c54108295ea82157350420c1fa617621541082977a566171d0420e4d612545c65108295fa55d38348110e47612545ce51083475766465494420c5d61d919525108383d766125494420e4d615845517108393785612545c420b4d693859517108317598e16545c42095de9591a117108374b954c9414c120dd2e5632506304829d7a16177350120c57a5f851cd41482d55a19537394520e4761254dce51482d55a19517394420
def g251D7 (j : Nat) : Nat := (if j<1 then 0x6545c420aefc9ae4a0c211fd98dd6724433beebc1ae4886775d7835c910cefba706b92219de74e0d724433bae9c1ae48847fe61741c910abfcaae83922157f955d232442aff2aba2648872f5d95450420ef5b94e4a02217db935c940443bd2e439280887f81c92150110abfcaae99022157f955d1204433beebc1a40886775d78348110cefba706902219dd74e0d204437b706a8240885f6e4d7254110cefc2ae6a0841d5f855cd410833bb0ab9a82107572157350420ecf2a2e6a0841d9d545cd410832ff0ab8a821067de157150420ebbc2ae2a08419f5855c541083ae90ab8a821065fe157250610edaaa2e2a08415f597945410839eaed28a82107cd9525150420eeab9ca2a0841cf57654541083e6aa8a8a82107755cd5150420afbc8aa8b94219de54e0d728433baa9c1ae508577e4d72d0610edb2a2e2a08415f591a1171882aff2ac22e31057de45845c620cbec3ca928c41b3d8495251882eeb232a4a31057764654dcd20aeec84a9b9a415df9155373482bbf20aa6e690677a1e541cd20cefb9b01a0a415f7915537148367b092a4a2905dd6465494520ceec26e728a41d5e54dce51482bbd2e39ca290677dcd8094520eaeaa6e6a8a415de971cd514833bb0bb9e829076755373d0520aef4b8e7a0a419de8755073482bf3212a6e09967edd3804c950dbd2a700992a15f7915d632502bef22baa64a067edd7804c940cfcbaf0099281dce545ca328c3b9aa8b9465186f6951808ca30decaa301194613f79161540c82aff2ac22e31857de45845c630ceec3c6528c61dcd728ca518c2fb321194a3186cf6125494530bbac8ca928a617d791551314c2bef22aa2e3906cf6125494720bbac8ca928e417e79155121c82beb23422e318677dcf8150120ecfb9e82a0241d9f7350540483bb6e6a8280907f2952328c120fe4aa46518241fca3294630483f9464a8c60907f28cb418c120fe5194831824177b95506304833bb0bb9a80907f2951324c120fe4aa26498241fc93294530483f9264a8a60907f24cb414c120fe4994829824177b9550530483f9264a0a609063f5d98195020c7ebb702aa0415dd9195173082bef2ac22e2107f28c9418c120aefc8aa8b98419df73602414833bf0bb9a8290757e177350520cbfc2ae6a0a415de971cd414836bf0a39a82906dbe163250520db7c2a64a0a415de971ce41482fcf22aa24290677e137354120eaf2a6e6a82419df73e0550483abee6a8aa09067761773d0120cefb9f00a0a419df7360740483b3ee6a0e80904fde458550120cefc2ee6a02418dd865cc410832bb0ab98821043f658874c550c3ebb70aa08418f976600410832bf0ab9a8210657e177350520cecb9b002084157795611710833e2e2c00821053d658845c4208f7cc2e43922157595211710832ef0ab8a821043f6617610420 else 0xe21029001500110084080000014104c102020241054104085042024104003c0ee2b0901382c00703d88080904100003c10201000a001304100c104c104000c104000c90403041000e010200112240ee2b82400604100e288903b82180d04100000001c1040c0c1000904103000405101c0c1d08100001810681074104050410005041504100050688080806880682054123c2904190410380b4138ae085904190410340c02d04e2b821a41040018004023d41080a0400281000000000000000f078207820400000140040000000024120c105083080000049800800000303040028100000003030408040000028100090019041000000000c081500100004c5208000131482c081b041000000b0410000141040d04102820682040400140c140c10240040000038204052683a20350149a0e881006201622400a83a202018801e400f03040704c9c0c20180508c901f030e830549a202ac0abaaa0a90a80a66a60a5aa54a4ea3ea24a1ea0e9fe9e49de9ce9c897c96295c94c94694093092091a9149048f48ee8de8ce8c88c28b28ac8a689689088087a86085a8187d67d07c07ba7b47ae7a87a279278c77c77677076075a74a74473472471470e7087026f26e26d26cc6bc6b66b06a069068a68466a65a64a63a6206106005c85b85a856655655054a53a53451a50a5044f44ee4e84e24dc4d64d04ca4c44be4ae49e48e48848247c47646646045a45444e44843842840e4084023fc3e23dc3d63d03ca3ba3b43a439e39839238c38637636636035a35434433e33832831831230c3063002fa2f42e42d42ce2c82ae2a82a228827826826225c25625024023a23422e21e2182082021f21e21dc1cc1bc1ac1a619619018a18417e16e1681441161101000e60cc0c60a209208206804e02a01a000eaf2a2e7288419f5845c651083aeca8b8ca21071f5d95454420eaeaa2e6a8841d75545c5510831faecc2e821072f5d954d0420ceec2ae7a0841d9d545cf410833eb30b8e821057d646845c420edaaa2e3a08418fd76612410833bb08b9c821067d6117190420c7ebb70aa0841c7d76e15410831faecc2a82104dfa608550420abecb90aa0841c7d762154108397aed2a2821067d61571d0420abfcab08b88415f59195171082bef22aa2e21057d653855c420afacad08b8841bdb8350120443aef2ac22e21075d255845c420cfbc2b08b88419f58561171082beb312a2e2106776117394420edac24a8b88415f79855171082beb30aa2e21075d615545c420edb422a8b8841db584551710831faecc24a21065f61e5494420e3ebb4a928841b3d8495251082eeb232a4a21075de1)
def g251H7 (_ : Nat) : Nat := 0x14e000000000000000000003820000066000a30016519e0000000292007240000000000004b625b900018a004a1aa8000000000604000bc00000a680e7341de1fb3d2c0000689ed3ad69da94b800c8dbb4c000040800000180060c081
def g251D8 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xd325c740dfd32dc550dfe32dc550ffa3254140ff93254140f7e544c950dff744c950f7e548c950dff748c950fdf7390520dfd845c630dfe545c630f7e5494530dfd32dc540dfe32dc540dfd758cb40bfd8195230dfd7294630bff8155230fde3294630bfd8195130bff8155130fde544c930fdd544c930fdd548ca30bfd8494530dfd545c630dfd73d0720dfd7294620f7d5454620dfd7254620bfd85d0620fbd54d0620dfd54dc532dfd72d0620dfd71d0620dfe54dc532dfd7290620bfd8095132bfd8195132bfd8494620bfd8195120dfe545c632bfd8095120bff8155120bff8055120dfe54dcd20dfd54dcd20fde54dcd20fdd54dcd20dfe325c740dfe545cd20dfd545cd20dfe545ca30dfe545c232bfd80d0720fee5448720fed5448720bff8454320f7e5454320bff8154320dfd54dc132f7d5154320bfd85d0320bfd81d0320bff8550320bfd8550320bff8150320fbf4150320dfe54dc132ff95050320bfd8195220bff8155220dfe545ca20dfd545ca20dfe845c620dfd845c620dfe545c620dfd545c620dfd758c940f7e5494620dff758c940faf4290910bf581909109fd87909109fe87909109fc87549109ff87549109ff874c740bf581949109fd87949109fd87c87409fe8794910ded721c910ded72c8740bdf835c910fad42c87409fd81dcd40bbd81d0d409ff87509109fc8750d52bdf8348110cff7654d42ff12150110ff13150110fbb42501109fd81dcd509fc8750d509fd81dc9509fd81dc940fbb43501109fc8750950aff8650950fb874501109fe8790950bf581d0110dbf74d0110ff13154110bfb804c950bf781541109fc874c5509ff815cf40bbf8150f409ff815cb40bbf8150b40bf980109109fd87109109fe8710910aff86509109fc8750910bf78150110ddd7394420cfd76944209fd8794420df5545c420df6545c420df4845c420df5845c420df6845c420df7845c420df5855c420df7855c420dde325c630ddd545cc20dde545cc20df57194420cfd7655020cfd7695020ddf7350120ddf73d0120ddf7354120ddf7350520ddf7390520ddf73d05209fd8794620ddf73545209fd8790620ddf7394520dde54dcd20ddd54dcd209fd87946309fc8754940bfb804c940bf78155210bf98010420ddd7310420b7f85506109fe8794940def729c910cfd76104209fd8710420df571504209fc874c540bbd81d0940ddd73504209fc8748540b7f8550420cfd7650420df57190420ddd7390420cfd76904209fd8790420df571d0420ddd73d0420cfd76d0420cfd7654420df57154420ddd73544209fe87c85409df835d1208ff865d1328ff865d2328ff865d1209de871cd208ff865d2429df835d5209f7815d5409df835c9109df835ca10fca328c1208ff865d320b798590110bd9808ca30dcd728ca30fc9324c120 else 0x40b07ea8f7e1e4e3b4073c8e191b8435ac68a0cbd18ba30f06000ba016802ba45448a5613ec263448908c4111020e83f6078c0e7c1bc035586660c0c16bc2b5052509d21200222041107740d8c19802d90528093c10501c50312053409180e7013201980198000bff8154120f7e5454120bff8454120fef4148520fed5448520fee5448520fef41c8520fed54c8520fde541cd20bff8050520fed3250520fee3250520fdc7350520dfd7350520fdf7350520dff7350520bfd8090520fed3290520fee54c8520ff9544c120ffa544c120ff9418c120ffa418c120ffb418c120ff9518c120ffa518c120ff9548c120f7d5154120ff95050120fbd4150120fbf4150120bff8150120bfd8550120bff8550120fbd41d0120bfd81d0120bfd85d0120ffa548c120dff7354520f7d5454520bfd8094520fed3294520fee3294520fdc7394520dfd7394520fdf7394520fee3290520f7e5494520bfd8494520dfd54dc520dfe54dc520fed544c920fee544c920fed548c920fee548c920fdd541cd20dff7394520fdc7390520dfd7390520ff94048110dff7390520bfd8490520bfd80d0520dff71d0520fed32d0520fee32d0520fdf7354520dfd73d0520fdf73d0520dff73d0520fbd54d0520bfd85d0520fed3254520fee3254520fdc7354520dfd7354520fdc73d0520ffa3254110ff97254110ffa7254110ff97354110dfd744c910dff744c910dfd754c910dff754c910ffa514c120dff748c910dfd758c910dff758c910bfd8710910bff8750910bfd8790910bff8754910bfd8794910dfd741c910dfd748c910ff95048110dfd7448110dff7448110dfd7548110dff7548110ff940c8110ff950c8110dfd74c8110dff74c8110ff93254110dff75c8110ff93250110ffa3250110ff87250110ff97250110ffa7250110ffb7250110ff97350110ffb7350110dfd75c8110bff8550420bfd8490420dfd71d0420fbd54d0420bfd85d0420f7d5454420f7e5494420bfd8494420dfd745c910dfe545c420dfd845c420dfe845c420bff8155020bfd8195020ff9414c120ffa414c120ffb414c120ff9514c120dfd545c420dfe745c910dff745c910dfd755c910dff755c910dff749c910dfd759c910dff759c910dfd755cd10dfd7250610f7f8550420dfd545ca10dfe545ca10ff55150420ff65150420dfd7150420fbd5450420fbe5450420f7c8550420bfd8550420dfd72d0610fdd3294530fdd3254530fde544c530fdd544c530fde548ca30dfd754c940bfd8195320bfd8095320bff8155320bff8055320dfe545cf20dfd545cf20dfd754cb40fed32d0720fed544cb20dfe545c720dfd545c720dff754c940bfd8494720f7e5494720dfd7394720dfd545ca30fed3294720bfd8094720f7d5454720dfd7354720fed3254720fee544cb20dfe845c630df) else (if j<3 then 0xd04a29853001e6f06104050488372b021104863049b03e2080506c25caa0d300b49a020d1050439509cde209e44c1c009090081c0b000249008e5504a2e1200c05c18aa0a0d32841402d2507404415ca0083c0e1201124800041a20ba4f2a948fa08240e404dd091008419a0f008581014e546c304148ac03e504430326c3741e550292834411ca0503c02120101430403c1dca84813059b8060f10550537425050292834411ca2601c129b4410106426f954ca4d0106881d36a0a65250740440e0403a6c0408e513292404195caa081e929ba122010832537caa0d268083440ea0a0a6e934041a20750525374c41a206e501d084ca4d05374244021065a6f9549a620d10303c03ca0a8605e503b8204a485b1014c192230770409490b620299b24480e8406336288c1dc1025242fc202e0c90972b8216c406f06388e23c18485f84051f9411a605b1014c18e040850713cacde0c7c60502d83e560060972b181681e0068185f95c110480e0c7080b83182bca22524361002e0080ba0f95c1240a162472b828314441b4b72b822ca4f944b27ca4e8c9b0931f25de4b44947924d243a47b48d591572206427482d90191fd23f2c7d68f7d1e763c7477f8ebd1d3e38e46e08d7f1a56331462f8bf917922dd45998b1515822a445278a0d1372259449188bd10d2212c40487c70f0a1d9c3a4872b0e1a1b7434d86470c0a16c42b78509096a1214233844907ea0ecc1af831d05fe0af414f8281047e083c0e6818b024a034403e803afff1fedbfba7f0efdbdfa2bf2d7e2afbf5f72becd7d6afa75f353e407c2cf7b1ee5bda17b12f5c5ea3bd1d79f8f349e58bc9078baf0a9e003be8777cee75dbe3b2e759ceab5d2fba117374e61dc9838f47170e25dc3b38166f90dec1bbeb76e6ebedc8db7836d86d4ada35b43b65d6caed8b5afd35a36af2d53da7c34aa68eed0819e4b384665acc0d97132d36564ca45945b258646ec8598f631d46366c6498b8b16b62cac511891b0f961b0c349858b0996102c181828b0396066c0b58062ff45fb8beed7c42f435e44bbbd76baeb65d06b989720ae3b5c46b8096f0adae5b08b5696a5ad335a24b40d67a2cee59acb2f964eac6a5892b0a1603abef579cae915c1ab62565eac3957b2acc5544a9e15272a1b53f4a7654d7a98552c8a50d491290a51d2a321453a8985100a15941aa8024fb09eb93c6a76c4e849c6137726d64d589a51330a6374c1a97b12e5a5aa4b1295c529f252f4a2e92dd22ba40947408d0117022a444be88450f3a17e42cc8461069a085405c7fc8fc91f3b3dc87ac4f319e1e3bb27608e9e9ce6390c714cdfe1bb7371a6cfcd741aa334ce68d0d0099a13294645cc60188430485fa0bbf97282da25a0cb1f15f92b325508a75948b28684f749c3132f25b04adc9349224239a45d889890da2106 else (if j<4 then 0xa400683c3078310418341e030c1a8f081a0f0986180b02504201012400c1c0107861500208101614241341861209841101a240820382c10c1080e0b83c0226082c084188100b03704801704080b06170910830b83c2442102a1664c0840b05604185c04120c1c1204860f06840e0b02430a05c12185810830d1c0a3c80140422018188890740c3808402c08818a140784c8620301e4081880d078203028202c1c241c08818816041020620142c088188058184130a0248621040a10401c038083c5068430680101c1604c084078360418100e090c12c103860e0780430783420b83c2402400b00042e080b958ac0e08905c2494707802b95812907000080186016442b940a078042a5c0c1108e50281e0101120b81800020885f2814040484804082b04282572814040484804052b0428250581014e502e363728a41ca0820060b1f940a020242a5c085048e5028161513940a0202404482e4300008a096060285ca4784412480b8000a472b83482b05307801c0bca08870ac48422248e50281e010205810128d9256a100f94110c0dca0503c021201014ac182215ca0502c01420a80f0211242f81c4c20a456e540f004c72cd43a0c4450180394150c02e88052394100c8543014610e0724f2822180ab587e502b02040485810128d93ca0b02016008d9107e502808090900b02050b13ca0503c02080900a08050b1407e5044301517940a0900816000883888487639820b423030b1f94050c8604e502824020580302442394078d958160040144924c6d2c1881924a3801c3005a084028c21b94530a603022f2a3656a082c51281012100b02029ca8dc30ae50281e010485810128d92142b14a370917940a008202402888142c494a2256018121237289e110182400154197090572814152e02ca2372814012480806482e00010512c3b81c1454ad0b2260f004f28140f008480418029109c081e36560c02e07ca2137caa4d068083440ea0a4a6e8283a0220703f2808094d80811412020ca03f2992c18db0a1008819207e5325831b6142011032794c10301d84140401593032b94c16481e36c284022064f29820764c6d85080440c9e50180ec98db0a10088193ca64819831b6142011032794c903b0636c284022064f2991030e361be532580c181c2088df2980c164c0e10381f9484a4d0536882020c9505253742a050506034412a04dd02834941a2070bd0525084b5039549819217e550525084b5029303242e92e55261096a050606485c25410b4239540a4c0c90905e1016e55329303a012120bf2a83080b502074927940404d0536020b1010648482fcaa4c202d4c81d049e502898010226c04162020ca0905f95498405a8303a012120bf2910166032506c1242e12e53242c88603050648101341e505811822020c9e5028240204158160008 else 0x1080e082c08141c89c140c4089060382818a180b100347c00801a382d000c3016091e08542cc90f04080b0682a085414104160ad0430204817411104160ad0440b8128212210b820b020309949041a382c140818102c18105024425838103020604884b0702041e0cc11020629051f04c122210305705030c3009c140c40c4270416040b820b0208103141c4984e0a06285704105704080b080f06e08381020c078488421030416082c080c26524106172114904205681080b08220900034105681080b0a172114904260810204704183c1a400c1c0107870206040c0818102160a84170910830ad021016104412000680a10540a205c24420c2c040a907042e082c0841880902048205040a082a16a60818090243410542d49102e12210782041e0dc10682050408542d4c0c1e0c082a16a487010d0503a093d84060a8b41278180a25049e410d881209a043098480818481e130c2612078702211491096142e08082e0f0900840b82020a82c20286020a86020284020a840260c0c20b8110212010a81a10540a22068416040815404028425082c080c2a808050844001424081424085811031100050040c449c04281a000a0081889380050380068281c0092444000c58011092c20a8b00249100a24000a140088490d89006105030b02206183b140f40c24098280100b04628838108824098200140404900306824318a40a3f0500201a08c503c120ec1400820034180fc5225098280138a4483b0500142208c54041e8902608004b040849a10589030381e04203059233043c070c080764860d08023150107c240982401410046281e09076090044098214088452442585810302041a0f0481080c1183009a11202c287a84103c83420b12050fd08200820f028204001e410910840b0102b41410a410702f118a848130500241e0d81200407058130210820c05e29028f84c1304482f144140a3e1304c1114102026924014820d05813148147e0a0048381604c5105028fc1400905e2315090260a003884118a4083e1204c140090c058128210261244068804361281868f2040c300240f09a020628401c080c2c0841860d080210020202c104c24090c240f0986120784c30000703c02183c1a400c261207c0c40881010180130900030783420994820b02106190010783020000201c12184826104826105c24020e024127a2508294d27012093d12841ca48381861109011070314ae83082e084186820ad0210161412c103860e078043002413082e12010617078203080380701078a1c001202c2034218340090304241b08259b4007080610080120d840f0684130902430a80104080b0)))
def g251H8 (_ : Nat) : Nat := 0x2f029b0000000000a2d9064167c1a000c4ee14386400012d800000000000000000006330000001006caf95be2c00000000000000000481000432000000000054d400000000018984bb24e638800316600000000028b1e25000000000000064a00021012a900052630eca0461109de0f5e7000008aac3e00088d993cb2a000000000351e0001c800019090529470000151d2a908c1154c7a9f00000020c8000bc7800352200000000000000000000001878000c2161bc000000000000151600093a8b3914338e61cb2f32eb649e4e0234000c7e699800000000000000000000000000003c98000b1b3936f30005f158947d214b88438000000000f3658f80006ca000000382c6a370cb220001f570004b10281e1800068fca5971ec058000001260000297b077a12a2274a68cfabe0000000000000eb0f023186c5675590e0000000000009c001542f10000287400000000031070140000ab000000000071ac8cd47bf2b80004b80000005b080000000000000000c850000000000000003cab712c000d0f531f496e650001230688000365800000000000000000004a71500000000000000000103800069f800343a00000031a800000000038b800000024f0000ce60000000aef21d489c0be31893296000000000010ae000000006fa78553000000000060781680000000001000000000000520952a000000000000000001448d00000000000001d9bc3003a0d76732e06d0d8001a68000e3c91a0002000849daabe8a0000003248000e2400000004fe0007a18000000524a4b800000000045a84c8d74000d18da68000000000000000000000000000000008d10000000b1d0cb800000000000000000000000000003d8000000040f52b40000000000000443bb50001ead43500032280000005a580018a800012a800000073e0000000d62802767e0bf9480000a38002c8efbc004aafc00000000000000000000007ad00002860000001459aa218cc839c4341a000000000000041180028940000000001490000000000298b4b200069b5820000000768400000031480020c5ec100049c80008b623e4ae4000000e528000234000395f1a588000000020540003690000000000000000017c8c2b960005c7000000035e80000000000000333415c133235481d92e7d00001b8ca6b1fc20f4840000c00008020080000c010000300c0000802018000000700002020020040200000000000100800800000000000000001000020040400c0900002008030000001400004020100100003000000040000001008060040101400008000000102c0401802000000200000400
def g251D9 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xa8e4a1c4637f06ee8dba1b3635d06ac8d3a1a1633a06628caa190e31b06288c2a18162fb05e48b9a16e62d405968b0e15de2b505568a8e14ce291050e89f6139e26804bc89521266243047488d211462220432883a101e1fc03e287920ee61d5039487060dae1ac034286620c6618202f285c20b3615d02a8852a0a1e13f027084c2093611d022a8432081e0fc01e4839e06f60d40194830605ae0b0014a826e048e08500f881ce034e05d00aa812e021603a006680ae012601c0028803a00360001ff8c940ffaa4a07fe52503fe39281ffdc940ffaa6a07fe51483ffb9a81ff54520ffe82907fe41483fea0a41ff50950ffe80907fd40483ff90e81ff4c740ffaa1907fe32d03ff2a041ff55020ffa62a87fe51083fe992a1ff8c950ffaa0907ff41c83fea8e41ff94720ffe81907fd40c83feaa641ff95320ffca9107fd54883fea8a61ff94530ffaa8987fd32503ff28c41ff94630ffaa3107ff41883ff20c41ff55230ffca9187fe54483feaa241ff54140ffa42a07ff21503fe98a81ff95130ffe83087fd41843ffb9a21ff95232ffae6887fd53443ffb9221ff9c910ffae4887fd5350bfe39221ff95132ffaa4887fe42443fea1221ff10910ffc64887fd32443fea8221ff50d52ffe80887fd40443ff90221ff48110ffca4887fc41083ffb9aa1ff50420ffc82107fd43543ff2a421ff55210ffee4a87ff41083ff212a1ff4cb40ff8e4a87fd544cbfea88417f5c910ff260905fd75082feba0417f5c620bfaeb105fd72883fd282217f5c420ff2a0887fa40442feba441fe50110bfae3087f950842ffb8a41fb4c920ff281087ee32482feb94217fdcd10fde42907dc73482feb9a417f5c810bfae6887df73482ffb92217fdcd20bfae9087fa30482febac217f5d120bfee8905fd75482ffbaa41fb48520bfae9195fd718cafeb84657fdd532bfaea995ff744cafeba2657fdc532bfee0995fd74943dea1e817f5c650bfee8a877e54542ffb9aa1df54d50bfee4a877d52542ffb8aa1f74c930bfae7a05fd72942feba4a57f5ce52bfae3295fd7094affba2a57fdcd52efaa6a95ff7154affb82a57f5d642bfaeb195fd7390bf6a94857f5c642bfae1216ff7650affb9a85fb94942fdaa4a15ff7050afeb98857f5c042bfae9215fd718c3dfa1a81ef50d40bfee4a07bf42503dea12817f5d740bfee2a07fa50502febaa817f5d440bfae4205fd744c2feb88817f5d630bfae9185fd754c2feb9461f78ca30ff2a0a07ed21c82feb96817f5c720fda65907bd42d02feb9e417fdcd40bfae9905fd75902febae417f5d240bfae5205fd71903fca8481f74c530bfeeaa05fd71d02f6b90213f5d810bbae6085ee72043d7a14853fdd942fe621087bb40902bebac813f5da409faec1057d75082fab88416f9d020bece2105dd73082deba04177dcd20 else 0x80c50140729266c420c904ca0b1c8c1b831c985f28446c420c704ca0b8c17c20583202050700728466d2158420cb121608ca0b9b830c40248b2b052049586e0c800ca11c1091c1b8323282e305459200c7ca111cc208188c1c4f282c205230603ca0b111cc2080c4024102e332a04550c711ca811ac21688188c245f282d0a20585230815ca115b429688100c244b282c6b085a203100904ca0b8c15c281054324380f290412247308204130b1aca41119b8208104c244f28a304122420516c908ca411cc20b4c1c0f282f04730820610090f28c189ca041543205d28386014517ca28c10489421688145b2f283873082d306010bca898417054c203f28a30624570810150ca1300ca11c1094208145b280307284424550c71800ca11c10917c2080528183c101c272932087015000ccc11518ca111b831c145f28386c620c70f28c1048917c2ca0583286304570b2844160c808141c09ca0e9b485618832c4858232904266c420c9121608cac10b9b831840282f28443b08541530812160804000d89ca9b10832c582329046f084130240caca11c10915164803203c07287060486e0c8cac111c215054009032458232904460841300c908ca0ec10582180320582328444130986e0c9cac11c1648031b2b05220c401ca0ec20b4c1823293308701500700ca11c10917c20583243c102729330870150091314cac1081b831f284704570824160c8131200cac1081b83203f28a070606e0c70f01ca1c18c2080583245823290412246f08400ca12ca41119b08108320582304246f0b2844600ca28c10489151648ca0324232b046c60142c0c8030bca41118984c215054c2f2930706d005120816044189ca9b108328482058132a6e0c2d00916150cc11b00c203ca242c609c330414546f080c0128c1b0cc1051c0003ca202033046c0f08032880908cac111c21c180524a8aca4a220748f0624686014cca0cc105151bc21c0c272b0447085414609ca8904c21505100320a8a4a3085414600c820c11bc208031b282c446f08200c7c11b08c203ca18272847046f08200c80cc11b03c208ca1c6f2b04200c5ca28c11bc208031c485f06232a0c68b31150a28644d68941116a1f243ae86710b0a12a41d6830104ca07240be8121010a0023fa67e70fc29f5a3e6e7c60f789ebe3d167960f1a9e0e3bb676b0ebe9d4e3a4673d0e609c9e38e67110e0c9bea37866e40dae9b2635d66b00d4c9a7a34b668c0d0499e633866660cba9952325663f0c64989e30de6100c0897e22f5e5e00baa972a2df65b50b4c965e2c6e5840af495ae2b165550a9294fa29a65280a40944e286e50509fc93c227364d909a4932225fe4b30950927e24ae48808fc91d2234646008aa912221fe4380858909220e64130816900e1fce3f007ca8f761e8e3c9077e8ee21d763a6073) else (if j<3 then 0x20a0cb0f49890e164cca9b838829060444605925032a6e0e20b04164c4940ca9b838824341127285d22210201060a0cc0e0fca4817884080414982833054390852085902012729060e20d150d044914428216408041ca83883804252016203b286c2c0ca4181428215ca0b051825060427282c54607418115ca0b1b181c4b29205e21020105266caca9b4948880c188300266e23282c30620c008ca491815061b8380205f290201250e0d060a20acac11915141b8380232a285599042e0e008ca4918c21506058380272843052460781c14560e00bca10c1184942c20715058380309b2a282e005c560c4438a16ca49181e0003061583802c4f285a210201250e0d0608b07ca8a42821505410b83802c1d0607280060542d120e00b0741814282ca150b05188380301f2a28002c0c5545260e00bca8a81891a14481b83802b2a2a06248851586e0e00a410148880005ca0b1b03802f2a282e005c560c44389ca8a074888000b1b051851490380381c2522200060172b042d246c0e00eca8a81891b054803802606245417286d200e00907ca8a4100150b838027290532044460520a6c1525020e20eca151c8114111b102106042c24120a6c032901260e20d100904829bca4c494083882c072815205e206c0c382caca9b882810490c8380243728266c1522204110320e00cca15c2811105101f29060444620a6c0125020e20cca1548810b172a0488510202246c81601ca11151018344c1127285a210201050e0e08dca491128829b4c8388243c10240856305c166c5a0f2a00d02cac11c17881843290445306f08200c9ca0ec1181bc2080320183c101c2729306e2059000cc10ca41114c1bc2168803285403045b286c200c80b0eca15511b0c058024183c101c27293305006f08200cd06ca0b51c210030c80242c472857046c60160090f011804491bc21688ca032c03282f07080c620080b09151b050c1803ca0028603b28405415446f080c3200c0f090416ca4c1540208b045823286e0c71011ca15c11bc2031805802c5f045023286e0c702ca8c151603801c3c241230706e0f2a0091018164cca15401f04545b2a206e0c72200cac11688121b8324330458546f08000f2890f04098c1c121b83ca80280b04562328160c70f0904038c17051683ca802c5f2b04485a206e0c808ca1bc218050e0380240b2b04705e2061608ca1bc20c110380243c04085c6328160c8010f159b88ca18832048090414466e2328420ca121641119b88ca1083240040602133285c150090f01ca1a08189b1c3c10242329306900817c114ca081b431c8b28466e085a204130910ca1116144c188b283a2058626c71800ca0ec104491688149b2c3c24104b293089008131400cac188161b2328446f08600c6cac1111518091b832023286c142c0c603ca119b18831 else 0x2046a00532a246c714421c820e05ca41830b282438572a0c2c61609ca0e15181b085728381460617880e66ca41830b2055243a25085208205905032a0e20e1514ca0e1b1818543d243a25085208593329060e20e15184111814214821640ca49838838541108520820593125032a0e20d0b1541118104144282164049ca83883c045108720b28140c382ca41401505ca491b0388250500541729246e200c9ca0b891513282c56246c5ca491b400541c28803272a046a0052246c7ca0f0e829b400c414983882c343f282411260a6d0031060e20dca150b1b0c17292444620a6d05020e20aca8922408014811b232a246a0052046c749401505ca411b880324172906044508520901260e20c0fca49890e4214824c41838833292624390852081505020e20cca411b400549038821046d001729270a200c90dca04491442824080418388303b29085209020125060e20b0e0f1640804149ca9b83882c341124590201072a6e0e20b0fca49890e4817884c9b2b2926243849205e2105026cb0d12ca04491748884080419b3204890200532a246c849890e164140ca9b83882926243b29205e2105))
def g251H9 (j : Nat) : Nat := (if j<1 then 0x92075114b6c0005a9d4844dac0000001cbc0002d26b43800093349496c74000a4ae4b672ddb3beb8801898a002a54a40000000000a00fe6a00021701cb6f6f000145dc4ca293e28f952b05c000abd2c7eeb5b168000000050ea58214c5163000000033d1c9301a80000002ad3000000000012ba00007329be7c743ab7d509b03efd000225e2145ea30000000693c00000025350000c320000000000000014faa7d60360de000000000000000001c1ea16000010d4000ad1800073d4000a2f9536e06ad08d4e213a1a3800000000000000000bbac000000106b0000000948bcc3a5bd5662c3d4870000000bbb4c46000285f0000000000040600039213196b625b9400072e40000000000c44c000426c0000000000000270d000000000000000003f4eca7cf26000150700008200c960a20001c245098000598f2235427aa200000006bdcd27b45ecd76564000d1c4000ecc000000038682c240004ae0000000321f01b800086020e500000009b8c14a0000ceb4961804add80005226095729c15630cf082000000093a8000bdd312a90550119d049285263831506c000c3dc0007d99f10000316d4c2f295553faacd03c85043b0000716400000010eda0fa90ab385d7c1c8a226f455d6c12bd50f035ace783e8cdba0055043ba0ef18cf6b4361cc86680724bfbaa800eab9dea483d84600000abcc5fa022da62d16000000000000000000000eb80000b10c00000024e2abb80005aec00021270d4610b02fe2c8000000000000000000000c21602c00000012b40000000c520e290000000c550000fa3c0009abccaded3d17655ae8e03c70c7000000000003af800004637c058f93d62773403049d204e101ec81b3100034a63258c7dd2a6f3c65966ff70538b5951ab7759b949a9a2342e30f1372b00b85571daab90c13571000000014dfd7333ca3677496cf8354c2550000000eaad35a63694ba52392c500008fc49282525dbaf7851068b1657cc7a1554480a0294d000000000000000454400055def7973ef0a00002085a285579c51ec57f8d400000024c50000000000000065cb0400123ee47db22e6000357400028b882a141641500000048b3eb110000000305c010081a000000080100005004000240604c020180100404004000340100808000130000800400000060000d00402008000140f004000000103c0100002000000e0000000c04403004020000004007004060040c01017000000240000004008000000100c19000010300000802004090100700c010440302403008000000300c01034030340605c000200000404000020080106c01010090140900800000020040c000070000000c0302c030040002c01010030080100000014000000200003004040000100000008060180001806008000000101400000000300c00400080020000b else 0x18102c288c24a10000000000000000000000000000000055008d5000014200028acd22acbdf230000000289f0000000601defc000375c4020000edfaf54923c00010c0000b32800000006eccb3f259000051d00004d2b47b0fd000000000024fe61fff1a0000000000258100e72a600013330000894d0ee40000014520000000042c1750001e7c1390d2c63459410000c91000186fccb8b7df46d5693333957dd74539b169f7f711f81fc40b4aa0003a50650e0ae519d533337c53b444172164630b4000000000000002dec000000000000000000001c2c2a58000b537845dc0ec29437194bf33cd7a243188df0d8064aad445b10df061a1380c910a12fa51e2c3f731e862d31207b9cb3b4462422b10027ce6c89f42763c60eecc01e1cf2736d70003964f58a2b3fb48000a377d5800000000584000000000062c3d5a0003a5b0000000000095c0000000c4902f00000923913391a21340000ba74d30000000000000074528566178b8124fca8500028cbd578d7f147e8e800000009a80000d4b80000002694fb44825d13dd5d2d44c5ce40000020650f0adb7105740df11460f2a193bd8bb24b703493fc09945153231418000d38dea5b219c83000014e0000000d5ec9305290000bdd5b808248c8b0000000b53000061b442d000200570f413c551156e00038ce73cc000b08d519758235ba365cb3000253d0000000000290d0000000cd54000000102b76120e90b71112a5a8c723d284a500000000001d2f725d43821b3f7af32370200032fb93070c6736101dd9900005ce7053a5f59340003f69000304a4222d78847304b00030ab0003b0cbb85479a1f3069e56fd204d588751971ab7c278d67c301477)
def g251D10 (_ : Nat) : Nat := 0x488192a09b06008126c44a1908a850600a02241009504dc2100ca12080152d2a09b100ca1202096946c40320480392a09b100c8122004a8268e1b0648910025410a7010324d8801288c18414a890658800a2541126cc032408994320821014a9b840c01a2004a8224d8b0640910045ca226c6032449b11285c22a14601065892600a4a820841636509012a082106c70108403950448b2a48200a0403950449a3014b00a2103112a0892a60a1208588072809134146162408b840c44a22546142440b4d280912a6c61404d8800a21150a62509066665c33736c0d43a0b3023dc287c6e09a22ff558981149e4322514790a60b4003fd10ff843fc20ff483fe20ffc83fd30ff8c3fc40ff503fc10ffd03fd50ff943fd32ff8cbfc42ff50bfe42ff54bfe52ff54ffe40
def g251H10 (_ : Nat) : Nat := 0x616c001a2341d70aa05e266e57cead914e582067ea11a1467a3aeb112de87034e3647d0f0b8acf6dc22e9bade405b89c3722780baacdfa800053bb00c000d9d727aafa3a253959c49540000440006b55ebbac3d2e52d8c60847d5fa9a605df11e0a3029c7144e94d2062c62b3a32b383754a4ae0090000c9000000000000000007d79e20000e1900028e400000089d81a33528510934e4c8482621aa7a7dedb38ecdbe7114356768d380020232a0329418cae78d100026ba0fa2606d1f293dbef0e5d86916244000000000107e00005bb6505a800000000000016cf2cf80000000000002a10000eb200000028d6000000013400000004c800000069555800035903478264640f4a6dcd656591d20235e5a0003907a330003cd59921b60000223ca762cd158f6d54e4a300298a6104000821ea63e1f7c3000000119917f40e5743574000a6d800000073d84b49fe004c72b49512a9a59ce011007f57b83265dfcb605ae49c2d537a4c3914636f019876aa18103a5c06f6a900025a08820001130e695123891512194a696b18040a7b884ad3c2a699337400042bbefed4da6ed3c2e9311c07bc1ecb6a51ee13ee28f6b9b3a5eb1e4943d22479803a2042fc1c8b073f7f420d569e00001050599edc5b1c99786f155996719d8b90002cc40000bc4720cc80010250005e5d8e8bc900000022bf6ada3f0000000e8b000000398327c010daa800140b56033361afb3cb3633169b00002da80000000004ef2ca8129bc263d3235b624e13cd90240009920002975b30959d2379cc000085b499ad4000ac670efef74680004540001985aac0003b80000000707800293b9b29ee01000017810005059cbe0006d10000000000c463b8c00040100040f8ef80004dd80028d400026b7374000f1ef0a91c6496fd820f026c90d63690200000604090040405010040005010701800000002e1500004000000008040602008000e00008141d038080200008280c050483014100181c00030180c24010000c06000002008000a0101a07190403a1b0281804010284410010401c0000148200076000100e13060001600040b010000001418030180c0806
def g251D11 (_ : Nat) : Nat := 0x140841ff
def g251H11 (_ : Nat) : Nat := 0x907d30000082c0083e8a28288d89e42d4008480073a6e6c40050d90237d5bd000433a784673616d682484000006afa8ea72d00302fcaaa0032371c6f502d40c146000b00008000f148100043
def g251L : Nat → Packing
  | 6 => (31,5,6,0,0,8,0,g251D6)
  | 7 => (208,4,6,0,0,12,0,g251D7)
  | 8 => (389,3,6,0,0,15,0,g251D8)
  | 9 => (229,2,6,0,0,15,0,g251D9)
  | 10 => (23,1,6,0,0,11,0,g251D10)
  | 11 => (1,0,6,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 11 67 7 10 5 1 g251H7
  | 8 => lookupWord 85 521 10 13 8 1 g251H8
  | 9 => lookupWord 185 809 10 14 9 1 g251H9
  | 10 => lookupWord 106 409 9 13 8 1 g251H10
  | 11 => lookupWord 13 53 6 10 5 1 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 31=true := g251P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_15 : block g251 7 15 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_111 : block g251 7 111 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_207 : block g251 7 207 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 208=true := (@block_merge g251 7 0 111 97 (@block_merge g251 7 0 15 96 g251P7_0 g251P7_15) (@block_merge g251 7 111 96 1 g251P7_111 g251P7_207))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_16 : block g251 8 16 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_112 : block g251 8 112 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_123 : block g251 8 123 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_219 : block g251 8 219 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_315 : block g251 8 315 74=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 389=true := (@block_merge g251 8 0 123 266 (@block_merge g251 8 0 16 107 g251P8_0 (@block_merge g251 8 16 96 11 g251P8_16 g251P8_112)) (@block_merge g251 8 123 96 170 g251P8_123 (@block_merge g251 8 219 96 74 g251P8_219 g251P8_315)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 18=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_18 : block g251 9 18 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_114 : block g251 9 114 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_137 : block g251 9 137 92=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 229=true := (@block_merge g251 9 0 114 115 (@block_merge g251 9 0 18 96 g251P9_0 g251P9_18) (@block_merge g251 9 114 23 92 g251P9_114 g251P9_137))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 23=true := g251P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 1=true := g251P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=823132161) (before_sound K191 V191) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K191 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V191 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 eightInputs.toFinset := by
  rw [show graph = graphGoal 255 by decide +kernel]
  exact cut_root (u:=true) (m:=255) (cap:=12) (before_sound K251 V251) (4,0,251,0,12) (by decide +kernel) (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0xffff00ffff000000000000ffff00ffff,0x42424242424242424242424242424242424242),(0xffff000000ff00ff000000ffff000000ff00ff,0x21212121212121212121212121212121212121),(0xffff000000000000000000ffff00,0x9c9c9c9c9c9c9c9c9c9c9c9c9c9c9c9c9c9c9c),(0xff00ff00000000ff000000ff00ff000000,0x15151515151515151515151515151515151515),(0xffff000000000000000000ffff00000000,0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8),(0xff000000000000ff00ff00ff000000000000,0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e),(0xff000000000000000000ffff00000000000000,0xd0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0),(0xffff000000000000000000,0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0),(0x0,0x0)]
def mo255C : List ColumnInfo := [(8,0,247,0,10),(24,0,231,0,9),(32,0,223,0,10),(96,0,159,0,9),(12,0,243,0,8),(128,0,127,0,12),(64,0,191,0,11),(2,4,248,1,6),(4,0,251,0,12),(136,0,119,0,9),(2,0,253,0,9),(18,0,237,0,7),(9,16,230,0,6),(1,8,102,144,7),(98,0,157,0,6),(5,0,250,0,8),(6,0,249,0,8),(21,0,234,0,7),(70,0,185,0,7),(32,128,87,8,7),(130,0,125,0,7),(129,0,126,0,7),(2,32,29,192,7),(16,0,239,0,11),(1,0,254,0,9),(72,128,23,32,6),(40,128,87,0,6),(8,128,87,32,7),(72,0,183,0,8),(2,64,157,32,7),(7,0,248,0,5),(34,64,157,0,6),(67,4,184,0,4),(66,32,29,128,6),(32,64,157,2,7),(64,32,29,130,7),(19,4,232,0,4),(17,8,102,128,6),(0,8,102,145,8),(0,64,157,34,8),(3,4,248,0,5),(65,4,184,2,5),(38,64,153,0,5),(8,16,230,1,7),(66,0,189,0,8),(0,16,230,9,8),(0,128,87,40,8),(5,8,98,144,6),(1,16,230,8,7),(5,16,226,8,6),(160,0,95,0,9),(0,4,248,3,7),(0,32,29,194,8),(66,4,184,1,5),(68,0,187,0,9),(6,32,25,192,6),(16,8,102,129,7),(17,0,238,0,8),(65,16,166,8,5),(24,128,71,32,6),(73,16,166,0,4),(18,64,141,32,5),(16,64,141,34,6),(48,0,207,0,8),(80,0,175,0,9),(88,0,167,0,7),(18,4,232,1,5),(65,0,190,0,7),(184,0,71,0,5),(13,16,226,0,5),(104,128,23,0,5),(56,128,71,0,5),(16,128,71,40,7),(112,0,143,0,7),(50,64,141,0,4),(25,0,230,0,6),(130,32,29,64,6),(88,128,7,32,5)]
def mo255A : List (List Nat) := [[],[16,83,100]]
def mo255D7 (_ : Nat) : Nat := 0x930c0ba65c059582585510c2e8d701656116154430e275a065995595810c361d6c1875956154430
def mo255D8 (j : Nat) : Nat := (if j<1 then 0x39f8c3322a8060887771b5645500c110dfa15098aa0982219fc69991540304433f84c34249aa0886ee9b66888358150f6d2a2c12c0a8061cfa6159258030443d74b0b04b02a01873e986649500c110cfd280d1122a8261ed958582545500c3d72db304b0aa2187ae5516096158030fe32caa1aa2a0261fc654543541404c3d9ca8b08b02a01879795161d6054030fd32caa1ac2a0261fa658543581404c337ca034c48aa0987b35616115154030f56aa2c22c2b0061add699a5605500c3cbab0b0ea8aa0186af5a56998158030f1eaa2c3ac2b0061be669943541404c37ccd3286a8a80986f99656913150130f7330ca1a8098221be6585a44c5404c3dccc2a86a02608873b985651600c110e3f30acbac018221eae58584581500c3c7cb0b0eb02a01873b986651500c110e3f30ccbaa018221be6545a44c5404c3f4c53286a8a8098776951649500c110cfd34cc92a018221dce5459454030443abca8b2ea80608867b9a6651500c110cbf34ccbaa0182218fe440a8651315427f45c34449aa0887a75966556560430f4eb4ab2b02b0861cdd659a5605500c3d3ad32cac0aa2187375966055154030f4e96cd2b02a8061e9d29981545500c397ad332cc0aa01872f5956056158030a7eb6cc2b2218221cbd2d9856443044357ad014ccab021872f5902598154430c7daa6d1130a0ac18fb591a2261315431f6d23444c262a867ad406889850550c7db645432898aa18fb681a2261315439e6d1b444c262a863edb26a48320550cf9a86d1122a82619eb50da2245505031f6c234448aa09867ac846889154130f4dac2b2b04a8861cdb65982545500c3d3653304a8aa01872ed616598254030a7db6cc2b2418221cbb2d985648304425f6da942cb3041872ed902598254430cdba86d3122a82619af50da624550503d1eb0acac22a218733d966115154030f4794cc22a2a8061caf58596611500c3c3eb0b0eb2aa218717d9661d5154030d4faa0d412ca8861e1f29987545500c387eb0b0ecb2a01853bdb6615940c110c3fb4ccbb0a182218bf611a6245504c297e5d32cc28608862fd906a09654430e5796cc2b2818221c3f299976143044395ec812cc22a21870fd9061c9654430cd7908d3122a8261be628543541404c3fc828a8298a80985e75b05956154430c5db2cd110640aa18f364da220c815421f6dd106c9102a863cda3688984c5508f5b6454a82a82810fb6c8a86513154315ed330848aa01861ed876889154030c75b08d1122a80618bb69982245500c21f6d9152c0aa01852f5b62458154030a7cb6448b02a80614bd6d8a9605500c33f0d0b40c90a68860fd876989154030f4cacac12c2a8861e8d59584585510c3c3ac3acab0aa218727596655656043097d36050b2ac10612bb6d8a1655820c25b6da942cb3041853e5b22a58154030 else 0x203002c2f8580d0070c00000000000021320f20b20720050001d61be143586f85f880dc2661be203586f85f880f807a206283e0118ae880f61be1780462ba20502704da9a933a644c29792da584aa94927a4c49291921a4047a8e91ba344628b915a2844a8890fa1c43285909a1041a82903a044027f8fd9f83ea7c8f79ec3d2798f19e03ba768eb9d43a2738e59c838a708df9bc3726d8d99b035a6a8d39a4342678cd99832a648c798c312618c19802fa5e8bb9742e25b8b59682ca588af95c2b2558a995029a528a39442824f89d93826a4c89792c2524989192023a4688b9142224388590820a408798de1b63606a8d219e330648c614a288468780c61381c824006001fe4595414c5404c3fc8b0a8298a80987f91515053150130ff22c2a1aa2a0261bf86c5a224d504437e8d3262a8260886fb1a65055050110cfe32cd2262a8221edc6d581581500c3db8b0302a8aa01873f185645600c110f5e36cc0ac0a8061ebc54181585600c)
def mo255H8 (_ : Nat) : Nat := 0x253ba200000
def mo255D9 (j : Nat) : Nat := (if j<4 then (if j<2 then (if j<1 then 0x9161940f9e5915358150f9e5516358150ff44c5504c110bbe2a16358150bfa6888358150fe650d404c110bfa68893581508ff2a1944c550c7f65d860c110ff458d3154110cfd615910c110cbf659850c110cef619940c110cfb688984c550cef615940c110cf768c984c550afb688984c550cfb619920c110cfb615920c1109fb6889850550cfb50d9220550cbf6594320550cfd619910c110cfb20d9220550c7f65d850c110cfd6598154030edd6958154030e5f61d5154030e9f6195154030ecf6115154030edb6095154030edd6055154030e7e61d6054030eee6116054030efa6096054030cfd6598154430cfb6a19214d109fb2a19214d10dfa6819214d10bfa6889358110bfc6849358110ef96096154430eed6116154430f9d5956154430e7d61d6154430edd5958154430ebd2598154430efc6056054030e3f61d6158030e9f6156158030eaf6116158030ebb6096158030ebd6056158030cfe6059014430c7f61d9654030cef6598454030cfb6099014430cef6119014430cfb6a58214430cfb6598254030cbf6199014430c7f61d9014430c7f61c91540309bf6989154030cef61091540309fb6889154030cfb60891540308ff2a58154030cfd2458154030cfd2a58154030cdf6159014430abf6a09654430fec5914154110ebd2999560430bfa6889354110dfc6594154110bfc6849354110c7f61d9654430ebd5958158430e3f61c9654430ebb6998258430cfb6a58258430afd6a56560430eaf5958458430e3f61d6558430edd6556560430fdc54d4154110ebd6596560430ebb5958258430cfd6599560430fbc58d4158110edb5958254430edb6958254430ebb2598254430cfb6598254430cfb6a58254430ecf5958454430ebd6998158030a7f69c9560430cef6598454430abf6989560430bfc6913154110aef6909560430afb6889560430e5f61d6554430eaf2598454430cf360d9214c10ceb6119214c10c7b61d9214c1087f2a58754c10a7b6889361c10a6f6909361c10a5f6949361c10adb6889161430af36889560c10c7e61d9014430fcc5514154110cbe6199014430cde61590144308fb6a45360810cee6119014430cfa60990144308fb688985056087f69c9850560cfc6059014430fd454d3154110f875915458d53a3f6989361c10fac5914158110f9658d535815087f6a58714430c6f61d9414430caf61994144308ef6a58414430c6f65d8414430f8e59154581508fb688984c550caf6598414430c7761d9314430cb761993144308fb6889850550cbb6598214430ce76119314430af968895604308fb6a58214430c7b65d8214430ceb6518214430aed6909560430abd6989560430a7d69c9560430be66913150130cf364d8214430fe45053150130a5f69c9161430a9f6989161430acf6909161430cd76159314430 else 0xd7f4c19720550eef6598454430e7f6598754430eef5458458030e7f5458758030eef5858454430e7f5858754430eef6418454430e7f6418754430eef5458454030e7f54587540309ff69491619409ff6949161930bf7694814c530cff6558120530bf7684854c530cff2a5854c110cff65543205609ff69491581409ff6949158130eef6148458530eef6608454530eef6148454530eef5948460530eef6048458530eef6048454530fb72594354530fcf2115154130faf5948458530faf2116158130def6588454530def6588454130eef618944c110eef614944c110faf2588454530dfb4419220d50dfb595920c110dfb615920c110dfb545920c110def595940c110d7f595970c110dbf615960c110def615940c110d7f615970c1109ff2a53154110def545940c110d7f545970c110cff6959120163cff6149858d10edf6556560430edf5958154430edf6958154030edf6055154030ebf6596560430ebf5958158430aff6a56560430cff6598154430cff6598154030cff615910c110ebf2999560430ebf2598154430aff2a58154030cff2159850d10ebf2998520d10efd2458154030bfe2855050130efb2458254030df750c9154130def50c9154140cff6109154130def2109154130eef2458454030e7f2458754030fde5456054030efe615600c110fbe5856054030efe619500c110fde545500c110bfe699500c110fdd5855154030fbd5456158030dfb0c19220550f9f5856554430ddf6595154030f9f2995154030dbf5859654030aff699850c110ebf299850c110dbf6409654430dbf0c19620550ffc5053158150ffc50531541109fb688915414097f69c9158140cfb65591608309bf69891541409df694915814097f69c9154140cfb6599160830ff44c5604c1109fe6809154d409fb68891581409ef2a541541408ff2a5864c5408ff2a5854c540cfb6599560830afb2859660830fe65053150130fec5056050110fe650d5150130fe650d6150130fe65954350130fec5055050110fe650d5050130fe650d60501309fb6889154130beb68895505409bf698915413097f69c91541309fb68891581309df694915813097f69c9158130bf3688954c530cef6548420530cef65884205309fe6809155130afb6a5656083097f69c9155130afb2859560830afb6888320550d7e65d600c110dde655600c110dee651600c110dfa649600c110dfc645600c110d7e65d500c110dbe659500c110dee651500c110dfa649500c110cf764c8320550dfc645500c110cdf619950c1108ff6a48320550afb6888360550ddb6959220d50cfb6559360810cfb6199220d50afb6889361950cfb50d9220560cdf6554320560afb68883605608ff6849854d60cfb6159220d60dbb6999220d60cfb6459060853cbf658832055097f69c916154097f69c) else (if j<3 then 0x16354110efe6056054030dfe645500c110efe6148358110efe6188354110ff5215314c110dfe6588354110efd6959660430efd6558158430efd6999560430efd6599560430efd6958158430efd6958158030efd6819560430efd6598154430efd6998154430efd5858154430efd5458158030efd6418154430efd6598154030efd6998154030efd5858154030efd6a58154030efd6958154030efd5458154030efe2618454110efe2618354110dfd595910c110dfd615910c110dfd695910c110dfd545910c110dfe2609354110efd2a58154030dfb6999220d50dfb5819220d50dfb6859220d50dfb6889850550efb688984c550dfb50d9220550dfb5019220550dfb4c19220550efb6558258430efb6598254430efb6998254430efb5858254430efb5458258030efb6a58254430efb6958254430efb6418254430efb6598254030efb5858254030efb6458254030efb5458254030efb5959160830efb6858254430efb5954360810efb595824c010efb545824c010fd75954354530fd750d5154130fd75453154130fb75954358530fb7595614c530faf5954358540fb750d6158130fb75853158130faf50d6158140faf5854158140df76594354130df76593154130def6594354140def6594154140cff619944c550df76594354530edf6115154130ebf5958458530ebf6116158130cff6598454530cff6598454130fe75954350130df7595944c530fe7594844c530edf6998550c10ef75958350c10ef7595834c010def595944c540ebf6958650c10eef5958450c10aff6998550d10aff6998550c10ef7619434c110ef7619314c110eef6194350110eef6194150110cff6199850d10cff619944c110cff6598454110cff2615350560fe75854350130df7651614c530fe7211614c530dbf5859654140aff6998550110eef6558458430e7f6558758430ef7615434c110ef7615314c110eef6154350110eef6154150110cff6159850d10cff615944c110cff6598354110cff595984c110cff619914c110cff615914c110cff6599560430ebf2998550d10eef6189460d10ebf2998550110eef6149460d10dbf50d9620550dbf5019620550d7f5019720550eef6598454030e7f6598754030eef5858454030e7f5858754030ebf6458654030eef6458454030e7f64587540309ff6819120d509ff2a1944c550bef2a54154140bbf2a16358150cff261644c550cff690984c550aff2a13158150cff680984c550eef595844c010fe75454350130ddf6595154130ddf5959520530f9f2995154130edf699854c010edf595854c010ef7545834c010dbf5859654130dbf5959620530ebf695864c010ebf595864c010aff699854c1109ff6999520530aff699854c010cff545984c110ebf299854c110eef545844c010e7f545874c010dbf4c1962055 else 0xbf7a7e64fc01f5c3e7b7c3af7d9ecc3d4579faf2d5e313c3077baee55da6baef750ce875cda396c725ee39dc5538627034df75bcab74d6df4dac9b24b5b46ad8d4bda6e349f68c4d0699e9339566b0cc4196f32c264dec8718ea31ad62f6c52588630c460ccc0a57eb2f785e76bb7573a2e165b86b595678aca95896afb55d2ab5d562aaadd5322a06533aa555486a8d05110a0d53f127a54ed09cad361264e4c22977d2c6254f4a3a93ad246a45b483c8f2d1c7235146288b5d14d225243bc85d508620b940cc8020fcf9f413ddc7a6cf241df53b44753ce789c9e38966f88dc79b5d36146adcd379a27337c65acc9198f1312660a8c0197dc2f6a5e0cbae17352e065b18b4f96782c3456c4aa9952c29de5270a1993e027304ce897392c024f048688de115321ea41d880c0faf1e603b4872f0e211b86356867e0c9318542f5c5c78b2615bc2a5851689e5133a24d0470888310601f743ca87160d8619c030905a90aac140c247843c07d20e5819c02cf04b6084c0e0016d021e02980298000ffc5855150130ffc54d4158110ffc60d4158110ffc58d4154110ffc60d4154110ffc5913154110ffc6194154110ffc6113154110ffc5056054110ffc2a54154110ffc2a53154110ffc2614154110ffc2613154110fde5955150130fde5455050130ff5595414c530ff5585414c530fde5456054130fbe5956150130fbe5856050130bfe6995050130bfe6995150130ff65953150130fee5954150130efe619404c110efe6118358110ff65853150130fee5854150130efe615404c110efe6154358110efe6158458110efe6156050110efe6158358110efe615604c110fed595414c540fbe5856054140fbe5856054130efe6118354110efe6194354110efe6198454110efe6195050110efe6198354110efe619504c110ff650d6054130ff64c56054130fee50d6054140fee5056054140efe6116054130bfe6913158150efe6116054110efe60d6054110fee2116054130ff65453150130fee5454150130fbe2995150130fde6115354110fde5518354110ff5595314c110ff5619314c110ff5585314c110ff5615314c110fde545504c110fbe6116358110fbe5918358110fed5954150110fed6194150110fbe5856050110fed6154150110fbe585604c110dfe6594354110dfe6598454110bfe6995050110dfe6598354110bfe699504c110ff650d604c110ff64c5604c110fee50d6050110fee5056050110bfe6a14358110dfe651604c110dfd6594154110dfe645604c110fee2918358110fee251604c110ff650d504c110ff64c5504c110fee50d5050110fee5055050110bfe6a14354110dfe651504c110bfe6913154110bfe6909854110dfe645504c110fee2918354110bfe68c9854110fee251504c110dfe2a58354110dfd4419120d50bfe2a)) else (if j<6 then (if j<5 then 0xd3380570c181f2e6000a788240fa83f0a030c0f881811023f0a097cbf881bc4109164a0d41501a000794512c2641c82601e201848a1c15b18f0b2098078803b2288f0aa0d41500f100c1450eaca80a835054000f28a1c11023f0a030c0f881b8168084305821785052e221282881a5a83a03e154150003ca28721320e41101f10036450f09bc2c82203e5fc401d914470207b05bc282971103005e392541f855054068001e5143901f0b20e4178801b228703d863c2983f0c60b00f97c00e20af0aa0d41501a00079450eac941a82a034000f28a1c18f85506a0a800305143830c31e14c1f86305803c41060c0f618f0a60b00f97c01e20936407b0c183f0c60b00f97c01e20a15a8e493785f0de20605fe1541a82202035450e0ad56a39071e17c37881c0cf86c03e5f0078802c6288043863c2e01f2f803c40163144c34f0a6b3007880606287469e1441901f10036450f36be6d4cda39b3b365e6c8cd8b9b0b35fe6bccd739adb359e6b0cd5b9aab353e6a4cd439a7b34de698cd2b9a4b347e68ccd139a1b341e680ccfb99eb33be674cce399bb335e668cccb998b32fe65cccb3995b329e650cc9b992b323e644cc8398fb31de638cc6b98cb317e62ccc53989b311e620cc3b986b30be614cc23983b305e608cc0b980b2ffe5fccbf397db2f9e5f0cbdb97ab2f3e5e4cbc3977b2ede5d8cbab974b2e7e5cccb93971b2e1e5c0cb7b96eb2dbe5b4cb6396bb2d5e5a8cb4b968b2cfe59ccb33965b2c9e590cb1b962b2c3e584cb0395fb2bde578caeb95cb2b7e56ccad3959b2b1e560cabb956b2abe554caa3953b2a5e548ca8b950b29fe53cca7394db299e530ca5b94ab293e524ca43947b28de518ca2b944b287e50cca13941b281e500c9fb93eb27be4f4c9e393bb275e4e8c9cb938b26fe4dcc9b3935b269e4d0c99b932b263e4c4c98392fb25de4b8c96b92cb257e4acc953929b251e4a0c93b926b24be494c923923b245e488c90b920b23fe47cc8f391db239e470c8db91ab233e464c8c3917b22de458c8ab914b227e44cc893911b221e440c87b90eb21be434c86390bb215e428c84b908b20fe41cc833905b209e410c81b902b203e404c8038ffb1fde3f8c7eb8fcb1f7e3ecc7d38f9b1f1e3e0c7bb8f6b1ebe3d4c7a38f3b1e5e3c8c78b8f0b1dfe3bcc7738edb1d9e3b0c75b8eab1d3e3a4c7438e7b1cde398c72b8e4b1c7e38cc7138e1b1c1e380c6fb8deb1bbe374c6e38dbb1b5e368c6cb8d8b1afe35cc6b38d5b1a9e350c69b8d2b1a3e344c6838cfb19de338c66b8ccb197e32cc6538c9b191e320c63b8c6b18be314c6238c3b185e308c60b8c0b17fe2fcc5f38bdb179e2f0c5db8bab173e2e4c5c38b7b16de2d8c5ab8b4b167e2ccc5678a6b133223cc45287d30eb21acc32785d50a8a132c23e83ab0586097c0c680fd0105ff1 else 0x102cc09c00ee1482d0650345d40000f10401ef0ae1a80a97a00003c4288260c018a03403c4785190c018603e2184b851980b00f11e140f8ac050c018601e23c28c83dc4218030c05807851d0c018044c0580788f0a3b09b0cc058078817c2b01b0cc03c40be1407d86602c005f0aa1680a97a00003c42880304f8560b20d834820052058bc80000578590221241c821415084903200404107f4302983a604c00e07f43181301e205f0a0d641d8613c2c83b0de20430c49d1a785e03e23807082184c83b0de204a0049dc3785f102f85a03e5e8078870d4607f0b61980b00f102b09030c058002017c2b01601e20108ac040c7856000805031e1580b000402818f0a08d80b00040301e115e1641f86904c07cbb00f105309b0cc064bb00001e224448a2680897f0ae1a80000f10a214513e1641c82602c000f48a1d80f859072098001e9143a8550ca5c0003321e062c4116204478570d4054bd00000a289f0b20980f97601e200ec8a21c2c83904c058001e914382e9580ac06f88905228704fe140b701f1022b800e0b40dcac01be224148a1c4878503a05b8088ae003a0f0372b01580d905228705c09c0c02d03de214408a200d8ac056037c4282114381b0400ac0681e5040607f0a20fc3301f2ec03c40169144b01f2fe208e78530cc607506e180678813c2e01f2f803c4386c303828c05e1610c16302600703aa9fc2a83b2fe206f0a0840b181301e20661202580c97600003c44880304a8350c01bc2934505e207603e5fc4309b0cc606f0ba080390f1142a820674054bd0000043c8f0a61700997c00003c41880304f85f10a0c3613e22418761bc2f880c06025b2fe204f0a60fc40601fc2a830fc298370de20470403012d97f102807f0ae183f0a0d487874101ad01f2f403c2b86a304033009e1542d0152f400000182542a860674054bd0000043c8f11e15c306063c2d01a00080541260cc1601c0007b0c0f40400f8550b400007885100609307e14c1601c0007b0c0e034d3785302e5fc40de14c1f86305803c4030c30478530660b00e0003d8607f10c26c30740680788f0ae1a8c0c03985785907e1a4100cb10400e615e1641f86904032c41004e4200e61520fc3482019620981805806e8102ba000a788200d184033e180ae18303e5cc00147105981033e180ae18300053c4100580d815f0c607cb980029e20906f863c2821f0d807cbe00710058c51603b05785307e18c100c710430903d22a41f86904c07cbb00f105021f0a033c3788140ec8af0b20980f97601e20802d22bc2883f0cc07cbb00f10480ec15e14c1f863040334410c040f48af0b20fc3482601e20903d22bc2c83f0d20980f976004f03067e1421e81017900702610f40f88017900603d20fc378560320980797f104821f0de1412f97f103286a69e17c400c53a301) else (if j<7 then 0xcbe06018094472f808cb81613c2f05159c1b01090e0022b8b93c5f03016e05e204503b1cc100701e18ac407e1782e02e01e20457172501f85e102281e0a2b383717c05e204503b1fc2b8600e03c4f0b6180680cf102f851590d300f881143236f0bc084503c17c400c0161f8500a0d001025f100200ed4027c280504e0189a7880100ac1f8182bc2b8600e03c4036013c2d860578045b18ad104aad4720e3c2f86f103297f0b61806788140083924c0314bd86f11e1480020e49300c52fe16c1788b0c48ad24d25fc2f887063297048033c408a5c4bf85b0de20068d6194bf85f100e85159c1a1a602e2e240457852005c2b86018ac4070d301717f1022bc2902b383434c05e204503b1c0b71712022bc283c181a717f1022bc283c1b4360602dc0bc408a076380ef0b0e20688a1bc283df10a094500c1d42a8207de21c300c1bc28ac17fa5fc408a1bc2d8632e00003a0f031a2080282b3830bfc05e20450aed2e49820366b015e0101b03cc5688241981b8420301598082d80b0c1341944820502a03c40de1410a81501e205a0de1540820501e206a0de14102815002820f0b61940a80f10338503d40940a80f10378503ea0540788140f502f0aa0540788180f502f0a03d40a801bc281d303e200b502300381ea05e1540a80f103102f0ac1640b17900003c40a327c280504e018c081701a02bc40003100080c1aa2342e86d2e002118d204427854468585304603c2812022040078e623c2b9770c8585f0ba1bcbb8883a2b81f0ae09cbc0a0743581f0b65ec420a0743288d0ba5c0042217837880880b00c0a621c2f0672e0010e8d2044222243a20450541027f0b607c4016a056007c73e1b41788015c5e158f8e741f88d0dc5e158cb00060250c60f850180944f0a0340678813c28c1f10084118ba1bc2981301086118c65c8bf85e0bc1b8100df104686052604c041f1413806f0be200448101a3b8520b40940d17500003c410a0dc378504be205f0ac158348162f200007882083785a0aa068ba80001e2051132048bf8560ac0a40000f104785f0dc0bcbe8082d034790245fc2b0560d2000078823c281df0c097cbf8802c0280682629c4786e05e1612c0d1bc2b0581ec0a40b179000008f0ac158340f902c5e4000021c4681d2fe1610c161a0842c469e16053811916434f0be21055811bc2b056052058bc80001e20806fe140eb8 else 0x0)))
def mo255H9 (_ : Nat) : Nat := 0x24a4e2100059cc0000007118000000000c9f00034fa8559110000000263d1d8120505c0b319806a917003e06816000000071200010ac820f25a9f800000000018f5ca36750006228000a5943218e9c29249a418003cefc618343a03d080000000001c7e0000000003502c3e1128001c88e01000786c44e4670000000001e1022eb14c00164cb3968d3c1e000d0171d211a00000071e742e46bb32e21609a22a22f0000001219000000000140c3020000001d7e000212991845702f8220001e4540031538b7487d23681405383c00000030f4000c1be8180c147c80e51e00d520700a8001887c5c00048bc05a000a34800000026fd3820c0001c39c1459b7c5d01d0000000000000b0469c64f697f327c0d98ed82c63151b342600020b391c000a125136999c1dc1ea193c6000124211a821a481e4e818ba3ac22838005707f0a0f41515b1bb4ffe4100044f40000000002168000a09000000000128900064520300000c0002010506010100040005030f0800000000010900000402110400020002060008020000040b0014000c000301000d0015
def mo255D10 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then 0xec3286085ef650304433fb0ea18213fd9850c10bf6c90a6086f760c5304377b08298219fd8714c109fecc2c6084ff660530437bb06a98217f5910c110ddec22a60867f61d530433fb28c38213fd9854c10deec1ac6086ef611630436fb0ab1821afd8658c10cfec3ac6085fb648304435fb0cb1a813fd98595409fecc062286fd605311437bb06988a13fd984c450dfac0a82286ef611411427f930a8a61bdd8350c50ddec2286284ff66143143ef2a6b02a1ef96358150fbcaa2c0a87be59160543ebaa698aa13fc984c5509fecc282284ff650814c27fb2a40a61bbc8420530dde42302986df615544c27fb30aa261afd86591309fecc2c8986ef614844c36fb0aa9a81bf59560430dde4a30a986ef251864c3f6a8298a817bd944c540ddec2a82a06ef619415027fb2640a813fd9520540ddec3108985df65481582bfb2e40ac16fd9650d60f6eb1aa6b04ff26153582fdb2441ac1ebd64551609fecc2caa1fcf551415427fb22402a73fd9620153faeaa2c6a9fb75916354e7fb22402c73fd95201639fec8102b1cff6548158fd7ac8aa2c7bed90608539fe4c282a84ff64c815427fb2840aa17ed9220550beec9902a85ef65081542dfb2c40aa15fd9720550bbecaa86a85ef65081582fdb2441aa1f3d6455150f5eb2282b04ff261415827fb2640ac13fd94205609feca902b05fb64881582fbb2640ac1f5d6354d50d7ec32c01867f61d600c2ff32028861bed8214430beec98a2186ef610510c2f7b28288619fd87144309fecc0a2186bf619610c37db04a8861bbd8454430dbec2aa2186bf619510c33fb0ea88613fd9854430dfac0ac2186fb609610c377b08b0861b7d8558430dfac0aa2187be58d60443df2c8b0221bf985581109fecc286885fe64053442fdb2429a213fd9814d109fe4c2a6884ff661534427fb30b1a21b7d85580309fecc2c8886fd605500c37db04a8061bbd8454030dbec2aa0186bf619500c33fb0ea8061bf58158030df6c12c0186ef611600c377928c1a21b7d8559430d7ec32ca184ff261414c27fb30b2861b7c9161430dbec8b0a186df659850c35fb22c3061afd9561830ddeb2b08187ee505404c3f3a86a02613fd9854130feaa0a62987e7211314c2fbb2898a61bdd854c530deec3262984ff261314c27fb30b2a61fd93150130cfec3ac2184ff661610c37db22c10619fd8759430dfab2b02186fd255810c37db0488021bed9660830df6b2b04186fb655820c37eb2cc08613fd906043097ecb102a87e650d404c277b2840aa13dd93205509f6c9102a847f65c8058e7b93098a611fd9720550cdec3b08084ef2614150373b08c18211fd9720560daec2b06084df654815823fb2e40a813bd94205609eec9902b04fb648815833db0ec1021bad8460810d6ec33060867761d8304379b06c1021abd8661010 else 0x8aa0187df54d50443fea82a8221bfd8654030ffc41aa0887bf585600c37fb02b0061ff96054110ffc4c2a0886ff615600c3ff30ca8221ff98454110bfec80a2187fe59150443ff126a8221ff98354110bfecb2a0186ff619430437fa8640aa17fc9850550dfec3282a87ef59141543efaa6a0aa1bfc984c550bfeca262a87f758d31543dfac8b02a1f7d5458150f7eb1ac0a87df54d60543ff126b02a1ff88358150fdeb2a82a07ef25541503f7a86b0a81fbd6550d40bfe48aa6a06ff619535037fb0ab1a81bfd8560c10ffca1ac0a85ff245865037fb02988a1bfd8150450dfea1b02286ff64d811437fb28c08a1ff93158150ffca0ac0a85ff24585502ffb2640ac17fd9420560dfe41b02b05ff655435837fb06a8021f7d5454d60f7eb22a6b06ff20c81542ffb2241ac1bfd8520d60bfeca906b06ff619300437fb22c00a7bfd854c010bfec8900a9eff60d10043dfaa8b1ac1bfd8550c10bfec9902a85ff650815437f906c0aa1bfd8650d50bfecb286a87df591535437fb06b0021efd6458d50bfe4c2c6a85ff644835437fb0c41aa17fd9620d50dfe49b0ca87bf58d415837fa8640ac1f7d5458d50bfecb2a0a06ff61950503f7a86a82817fc9154140feea1aa2987ef50550503ff2c0a82817fc9161930bfe48b0a987fe54030442ffb2242a61ff9600c110dfeb2b08987ef594844c2ffb2218221fbd4158140dfec0902985ff654814c2ffb2a182217fd9620530dfec2860887bf595614c37f90ac0a61bfd8454530dfec22c2985ff245534c2ff922aa261bfd8655130fde422c2987f750d614c37fb0c18221bfd8559130feeb2a86987f7205314c3f7aa6a0a81fbc8454530dfec3262a06ff61531503fbaa898a61fdd644c530ffcb0260887ef50531503fbaca98a61bfd8558140fee42a62987ef50d60503ff2a0982217fc9158140fee4aa62986ff619414c3f7ac6a0a81bfd8550530ffca0260887bf58560502ffb2c18221bdd8354010df6c9b04086df61530042dfb2c18221b7d8554010ddec2260086f760d300437dac8c10219fd8744010ddec22a0086ef61110043faa629822177d950c110df6c1260086f760d600437db04b00219fd874c010ff8a0ac08867f61d5004377b08b0021bed8254010df6b1b04086bf61960042bfb2e18221afd8654010cfec3ac0086fb50d820435fb0c98021bec5360810df6a9b04086df61560042ff32ca82213fd984c110dfcc32a0886f7591830437bb28c1821f795454110dee4ab06086f7655830437bb2cc1821bdd8560c10ddec2306087de54d504437bb0688021afd8660c10ff8a0aa0887ed505404433fb0ec18219fc9361c10ff898aa0886ef611640433fb0eb20213fd9859010ddec9b08086ef6558404377b2cc20219fd9361c10df6c1b04086f760d4304377b08a1821b7d8550c10d7) else (if j<3 then 0xa0987ff595844c3ffb08b0a61ffd8454530ffeb2a82987ff585414c3ffaa2b0261ffd6550130ffeb0a80987ff545404c3ffacac0a61ffd8158530ffec82a2987ff595314c3ffac298a61ffd5154130ffe4c2a2987ff20d60543ffacaa1a21ffd8650d10ffec22c6887ff61984443ffb08a9a21ffd4358110ffeaa2c0887ff61160443ffa82b0221ffd5358110ffeb2a80887ff61940443ffac2a0221ffd8550d10ffeb2306887ff61983443ffb0aa0221ffd8358110ffec2ac6887ff61583443ffb08c1a21ffd8558110ffea1aa0887ff59150443ffb08a8221ffd4154110ffeb1aa0887ff60d50443ffb0ca8221ffd6054110ffeb2a60887ff61930443ffac298221ffd604c110ffec2a60887ff54530443ffaa098221ffc9560d10ffe49aa0887ff26153443ff930a8221ffc8550d10ffec2906887ff21530443ff906a8221ffd6520530ffe482a2987ff50c81543ff922a8281ffc9154130ffecaac2187ff659510c3ffac2a8861ffd5158030ffec82a2187ff659500c3ffac2a8061ffd9154030ffea8aa0187ff59430443ffb0a18221ffd510c110ffe48aa0187ff59543043ffaca98021ffd514c010ffeb22a6887ff54d41583ffaa8b1a21ffd3154110ffe98ac0a87ff58d41543ffac898aa17fd954c110ffca8280886ff61930442ffb2c982217fc984c110dfec2a60887f7585314c37fb0ab0261bfd8458130fde422c0987f750d604c2ff922b0261efd6158130fee98ac0985ff659504c37fb0ca8261bfd8454130fde422a0987f750d504c37fb2cc0861f7d5154130fee98aa0987fe581504c2ffb2228261fdd314c110ffcb0280987fe541404c3ff2caa0261ff96150130ffca8a80985ff64530443fba8698221fbc944c110bfeca260885ff245504c2ffb3029a21fdd6354d10dfec22a6887df55150442ff930a9a217fd9854d10f7eb22c6886ff611634437fb0ab1a217fc9858d10feea0a62986ff61483442ffb2a41a21bfd8620d10bfecb106886ff591834437fb06a8221bfc9560d10dfec2306887ef251834437fb0ac1a217fd9858d10ffca0ac0887fe50d60443ff2a6b0221ff88358110ffcc1ac0887fe24d60443ff2a8b02217fd9654110ffcc22c0887fe615604437fb08a8221bfd8358110f7eb22c0886ff611604437fb0ab0221bfd8550d10bfecaa86886ff61943442ffb2ca1a21bfd8654110bfecc286885ff64053443dfac6b0221ff96354110ffab0aa2186ff605510c3ff286a8221ff94154110fbeb2aa2187fe4c550443df92ca88617fd9654430bfec98a0886ff619834437fb02b0861bfd8650110f7eb2ac2185ff655404437fb0aa0221fbd4350110fdea0a80887fe581404437facac0861bfc9560430dfecab02185ff65940442ffb30b2221bfc9561110dfec3308887fe581500c3efaa2a8061bfd8154030bfe4 else (if j<4 then 0x8cca8c7e8c508bfa8b908b448aee8a7089f289b0895a891888c2887688168798874286f686aa864a85fe85b2855c850684b0846483f08390833082ee82ac824c81f681b48168813080d0808e80427fec7f8c7f2c7ed67e9e7e487dde7d9c7d327cf07ca47c447be47ba27b567b147ad27a867a3a79da7970790678ba7864782277cc774e770276ac7660761e75dc7586753a74d0748e742473e27396732272d6728a725271e871a67164712270d6709470346ff26f7e6f3c6ee66eae6e6c6dee6d986d566d146cbe6c546bfe6bbc6b666b106ac46a786a2269cc6976691668d46888683c67d2674066a4664465ee6584650664a6645a641863e0638a633462ac6256620061be6186611260bc607a60425ff65fbe5f365ed65e805e0c5dc05d4c5cf65c645c185bc25b4e5aee5a8e5a3859d85982592c58b8586c580257ca576a5700568c561855b8555854ee548e542e53ce5378530e52ae523a51d05170511a50c4505050044f9a4f4e4ef84eac4e6a4e1e4dc84d724d084cb24c664bf24b924b3c4ae64a7249fe49a8495c48fc48ba4864481847cc4780470c46c0466a461445be455e450844a84452440643ba436e431842cc426c420241a2414240ec408c40363fd63f6c3f203eb63e423e003dbe3d7c3d1c3cbc3c5c3bf23b923b503af03a863a1239c6397a393838ec38b4382237c23758370236a23656361435aa3568352634c63484341a33b0336e332232d6326232023198314230ec308230222fe02f8a2f482ee82ea62e502e0e2d902d442d0c2cd42c6a2c002ba02b362b082ac62a3e29de2974291e28d2287c283027d0278e272e26ba2678263625cc256c250c24ac243823ce2396234a22ea2280223421e82192214620e6207c20301fc61f661f101ec41e5a1e041d901d301cda1c981c1a1bce1b8c1b401af41a941a2a19de1988191418aa1840180817a8173e16e8169c163215c8156814fe14a8145c141013c4135a130e12ae1258120c11c01174113210f010ae104410020fb60f6a0f000eb40e400de00d940d340ce80c740c280bd20b680afe0a9e0a5209e80988091408c8087c082607d00770071006a6063c05d20568050804a8043e03e80388033202dc02860208019e013e00ca00560000ffec2a86b07ff50d81583ffb30b0a81ffd9558140ffec8ac0a07ff64d61503ffaa6b0a81ffd6560d40ffec1ac2a07ff59581503ffb20b0a81ffd8650d50ffecb2a0a07ff50d60543ffa82b02a1ffd654c540ffeb0aa0a07ff50d81543ffb22a8281ffc9850550ffe4c262a87ff655614c3ffb28b0a61ffd9858530ffec9ac2987ff641614c3ffb2ab0261ffd9158130ffeaa2c2987ff615614c3ffaa6b0a61ffd6454530ffeca2a2987ff58d514c3ffb30a8a61ffd9354530ffea9aa2987ff659504c3ffac2a8261ffd6054130ffec8a else 0x6078078560e00e2218180ce178600700e2060378625f85e2039180a20f8620901e5f88e140d860a0e386e140c65f881839e1b8865f85035391c18e1b88e1597035391c0a05b864d1820e397e2385034a02b8507438e200d2b0700b850b3860981880797e200a800b05f8520e820e397c038807490ae390e385e1a97e207a0b884268661501400204609e142240500e201d46076181e60b850d407807978000f860b42585a0d014038846078638560d828079780388201e8638560f8660a01e5e00e20a03a82e140c0e40d0b016061882807e158660e01e5e0003e182604a238560e01802181d83e1435e1982807978000f860a08218e158660e01e5e00e20903802e142c058188079780388028b0582ce1702e5f880287004394980ce1786e207c0816e142c0302be200a230205b850b025e5f88028805810e142ce1988c0b9702890b815c0c39e5c1cc038806090980ce142ce183906397e200a28160ec140b386c0b9706f88028a058140e42ce180d0301802b882839e142ce180d06201e200a85ca0e40d033850b3860600ae209c0c3be5c2e05843e200ac1890340c0b386e14390639702b88280ee5c34e1443e200ac18804c2e0b0160e701e200ac5c9c0f850580c10f8802b062303e141609797e200ac188c0f97043850584302b0620160500f0b3860340c0e7970600aa20c0e40fe142ce180d0301802a88282c0340ce14390639702b8824160500d0302ce18390639702b882c0d0300fe142ce18390639702a882c2c0e7850340c0600ae208b486b480b47ab474b46eb468b462b45cb456b450b44ab444b43eb438b432b42cb426b420b41ab414b40eb408b402b3fcb3f6b3f0b3eab3e4b3deb3d8b3d2b3ccb3c6b3c0b3bab3b4b3aeb3a8b3a2b39cb396b390b38ab384b37eb378b372b36cb366b360b35ab354b34eb348b342b33cb336b330b32ab324b31eb318b312b30cb306b300b2fab2f4b2eeb2e8b2e2b2dcb2d6b2d0b2cab2c4b2beb2b8b2b2b2acb2a6b2a0b29ab294b28eb288b282b27cb276b270b26ab264b25eb258b252b24cb246b240b23ab234b22eb228b222b21cb216b210b20ab204b1feb1f8b1f2b1ecb1e6b1e0b1dab1d4b1ceb1c8b1c2b1bcb1b6b1b0b1aab1a4b144b0eeb098b060b028afdcafa4af58aee4ae52ae10adc4ad3cacc8ac86ac44ac02abc0ab60aac4aa6eaa0ea9cca976a934a8f2a8b0a83ca7f0a790a744a6f8a6b6a66aa61ea5bea568a4fea4b2a43ea3d4a360a31ea2d2a25ea226a1e4a18ea142a0d8a05a9ffa9fa49f589ef89eac9e609e1e9dc89d729d089cc69c3e9bfc9ba69b649b0e9ab89a6c9a2099ca9956990a98be9872981c97e49798972e96ec9696964a95f49580953e950694b0946e941893a49362930292b69256920a91be914a90d6908a900c8fc08f748eec8e968e548df48d808d34))) else (if j<8 then (if j<6 then 0xd039c078802b17200be144a60f88a5c0d8e4803b850743ae5c2310f880b3062b030744de5c2110f880b306278508881e201d8e4601b850940de5f8807d1d2044e5c0da038810c662029e161fc0c81e5c8010c90180c0c38807c391818e1483a0901c03880748033850843005839182009f8508416c0839e5c0dc0388060c40f85c041dc03880607e1421e20258345e141fe202527450d38507f030e79707300e2018280ae143460839e5c1cc0388060ae1416c0c41e5c1cc03880289063850d1821079707300e200a281fe200c4744e1603e1a021140c1827063860282605802e143d0338802e3937030e385e1b02e5c0de200a2418e142ce1b0265c2b60788028a0dc90e1421e1b970588a238508425e5f880588a1c0be142103030e20162288088ace1797e2016228711c4c08786e5c1ae20162289e14232078805a39180ce141dc0c2110f880b30625888844521385e1b0220797202162c0ce1430e20210e46e200c07c300743918180d00a09b8510e81e200b900ae17030343809843e200ac189e1430c0d970ad81e200ac18900103e5f850d043e200ac18904890e141dc0c3ae5c2110c2cc18bc0c0de141d08443e5f880b3062825e23850840d178540397e2022074181d0910e86a0d01e5d00e2018241e22b8520f8620b01e5f00e20ae1683a09014001ea287e148320901e200d2287e2101e1683a090007a8a238520c82c03880c08a1f8842585a0e824050007a8a278806808e1483209014001e228ae142240500e201d4607a1a8341386a0988e1501401182a86a0f86a0901e1500e21182686e142340500e201646080738540500e201f4607a1a8342786a098540500e21182806e142340500e2016460808c2046018e1686a0d01e5d00e20b01283a0a86e1501400204609a0b88a1901e150008118238540500e2021460608a86a0d1806385e1a8240797403883397e141f0740d603881f8507d9707581e20601b8507f970862ce20700b85e180d207888e470338520f8620881e5c80e2090a0040ab9720045e14832080c2b972038520c82e200c1c181100a1181609788034801817e1423e1834a0838e5f88034b05f8508a830e39709a80e222c282110f85a1901e5d00e2023060ae14220af888e45a0f8506386a0901e5d00e209a0c0f41386a0901e5d00e14182a8340786a0900e2385060840397e238508c1606074708607d01e5d00e2022e14182a8342786a0901e5d00e2185060a10f85a1818a0d01e5d00e20903d0410f85a1a834079740018290110f85a1a834038806080ff85e180d207884e47e168640500e20164607e148340500e201d460709c34e143de18180338802e012b8520d0140388075181f850878680797803880598a2586e142380600e20168608e158680600e20168607e142280600e201d8607e142280600e201d8 else (if j<7 then 0xe2091140ee1583e1982032882212e1b8503016e5c0da20810c0ca038507439e5c230602ce20be1483a0b970752ce20700b854b00d86081e5c80e210a280208b85e5c214b3881dc00e183e14300b039e20860826e162c82839e207e142165c1660788180ee1583e1982033881d86e141660838e5c0de20860b850e00d8e7970b388200d033850b3860e418e5c0ae20ae142ce180d0301802b882397e14210580d603881c0c03a82e140d0e42c05818e5f882c2ce140d03039e5c1802b88243060785e1816a0997e20825c1709385e180c2078820160502ce180d03039e5c1802b882c16067862141586181e5d80053882e82e1b850341660797e208a0b850ac2c20439e207b0048a0e820302ca0439e209e14220b2810e7881982e162c8282b60039e20861b850582b82839e207e142b60c2c82839e2078b01382848e5c0de20703f850b3860340c0e7970600aa20ba0826e152c42839e2070b7854b10a206800e788200de152ce1a81a0039e2084b00de150aa06800e7882306c0881e142007880e2018240d4b04742a81a0039e20809802e152c42881a0039e2091140ec2b8520f862080c200ee1683e1a82033881c0ee1683e1a82033881c2e03a83e1a82033881f8508939e5c26a002ce20802b8520f862080ce20700a86e1416a0838e5c0de2090801ec0b85e1818207972038828390af86a1b8505a8203788241404f86a180c05b9703788262c04e0a0c01b60439e208e152ce1834a0838e5c0de209a0b850e00d4e7970b38820390ae83a0b85036800b388240e08f97a5f850740da002ce20ae1422e5c0da002ce2070501ba0e8203397036800b3882b06c080fe142007881e5c80620182f8508a01e201d4e46e16400af88075391b8540d02e200c22860302be150340b9703680e209e1503e19020e397e200d4609e1503e19020e397e200d4609030380c00de150340839a07882b8540f864082b207880e518278503b86a0b88030609881e1503e1902e203946090b78540f8640881a03880e518282602b8540f8640881a03880e5182c22e140d60421603881c23e140d6041f603881d9708b8508581e2063019708f8507d81e2070978508416034509c180b40a0002105b02a0002e1425e200d3b8540f864082ba07880e5182402e142ce18304e42de200a404ae142c0d00ce5f00e200a23850f7860e40c4e78802d012682e178603788405391e97e1423e20168e4602b8508f860d282a5f88036392a97e1422e201d8e46a5f8508b8807639198302f8660b88a5f8503639278508e01e20164e466198386385e19828079780388299702c23e1834a0b88e140d4e4a65f8508b88075391b85e182503001a03881c180b785e1b88035391c0ae1416e19346082b807880c0392c0ae141d60c2b807880c0392402e142ce18260e580e200ac5cae142c0 else 0xf850846e208106385084161986e1681e2202a00161f97e2103e14220846e1603a1981e5f8800d800749a16880941f0301d183b0e7856082d09997e220a8183a2d17e2288e140c0846e15860e080e208a8e7172002e23850301f1686e200de14394046e17052b3068082d09700e208222b1730010980ca1b888638565c8a1b8822b85030391b85c5d86097880e46a1a8302f880708ae143820ace180ca080be200d22b850e0a07902e141f05a81a038820260ff8820f8503064181de142108281a0388202609f85807888220a60c809a01e203d60e97e14705b852048008388060710f85a0a86e208a0303923852b18265f880e20022882181d0d3882088ae140c201e40b85204800841606388248605b882b3850306e150607c34a0788a00709c2cc5f8882883e147e168560e86a5f88a203840182282612c0e08906a1834009018038802b85860e0982712c2ce168508d02a09018038802a86860f2b30680b88c200d22b8580492b0bf09b880308ae1697203fe140205d08a210a2b038030a0f8260328340600e22aca19978638530010980ca0b88a1a18e1597278509c21a0508082801d0842ac00e385030609b8860f85a5c52b18660b88623850e00d203961b85401882282503080980ca184ae1a8240600e200b65e18e14d21902a0825e200ae140c2106a182505b8802b85030861838e208ae140c1838e21c0e140c142c803850868261a978280c037882c39a0825e1786e200c4e480982c0338860f851806e178803021140c60f8860b850e00d1f85e203a0e501150205a00e141fa18b420a978280c037883785c082d09788c208a2183c240e60f8800182e1438034802c86e1502a08174228802838030b0e7856098822825030702d06a188205d08a200a0e385030b25f85c1706c080c09788223906027e170560821c080dc03882290ac5cee1705204806181fe20703039e14210639705b882182e1412e1811035810418003e882c0c4b38603680e143906388249c41b8507c812001de201826800e797e142306016e208a092c4280da0039e1418e209a08264b10ae143906388201160f850302c60439a2086148503a82030390342c05818e20b0e680e142106016e20703a82e140c0e40d0b016063882b86e1425e5f88141a083850848120016e2018240fa092c4280da03850e418620a10c1da0e82e143908418e5c2ce20b03e80e141da0c39e5c210602c620b1192c4280da01850e418e2090ea830c01de168660597e20904c15a0039e5d850841805b882839a038507683084180b388240fa0039e5f850841805988241260f8503397035800b2882680e1439e5c220602ce208c1b022242007881e5c80e2018292ca0039e5c22e141805b88240d05680076830e797084180b3882c1183c0de162c8298160039a20aa092c4280da03850e418)) else (if j<9 then 0xd20c82063882f85a15820868203197a5d86203882c23e168640500081181f85a158640821a083840280e220aa5cc09f8505b01e230020c702b85c1421a5c0ce207e16854181fa18342083840280e220aa5cde1705c1b020343920788238509018033888606e1421a0986a020aa5c25e20909c34e158360a01e5e00e202c860be158360a018001e860761b85e1982807978038805a1828c010385c141f033881f850301fe204e1583e1b880e42b0c1822385a158208682a5c2560280e20a08b8508d86c0788c007860180d01fc0788c0385201e0888ae1a82407974038805b85060c06f852b01d0582bc040de23002088a3080e142109788034665d1709286e140c60788210140388e158607c60781ae141f0598160388201809f8508701c00201c2708c43e15014002c080182785c148665e97c5d80a030007c21e20ce1483e1b976001a05b882385a19014038820c211c82e179707d80087881c24e141f618b42098065f88278520c82c07000788a1dc0e158007c2165f881c8280b850841660580e208e141f618b420997037882027e143461b01e208ac00803785a07884b1860e470ee2c0d0390b78509b8860602828b03681a5f8800818e1421058902f8540d00a0297e22180749c200ce141f0c0211a88097850840c058607786c0b880000ae1425034921b0600997e220ae140d23080978507c0d084630040e140ce201f0e47e140ce20210e452001ce142503580e201f274940385097880840d1b85a182360580e201f1e8608b8560580e202108c80b6390b38509700e2183860902f8560f886098885c2b0c090b439e1682e228686101202de178860e0117852b0340b7880948a804806802e140042288428ac0940c2b854210a904250306e142ce180d03039e5f8802818282208e86e1788604622b85a0f88903170ac7e1503e190203397e200d4609e1503e190203281e203946090378580d81e20391b97e160303388036181f8580c0ce203986068199707f88e14211a06e158007d97e20211f852b3888e48ac5c2b1c1de170303797e202110c2c24852088007430e202110d970b0ae168560697e228807580c1822284301b8520788060211c800e797e238508418058825f8503025e2021194010117e1788a200c07c8e141b0840c6042be21026001680a183388223852041f10c1d1f8540e81e2280a23060748e170620480e21030847a080de212ce14391b880338580e01800620b86e21024280de1439201ae5f850840ce200d1f85a1682030390342c05818e20a2fd85095880301f1a8100482e1b85e21020350a0e4ae5f88e1421034161981e23850843065c161f85a168660697e228805902600232c2740d86e178842a811cc110481e2018e141f1c2562385030211480e141da0c39e5f88084180b0a25c0c09788e141f18c1e5f8880 else (if j<10 then 0x5c200c0941f0849118446150625c0c0942120bf4fe1cc200c0941f084805b0802818034510e868180d06052711c0f4970302507c7301400940c07c502897e14212d025e20709102e141fa1882a020aa5c25e20b09c2c61902086820ad17a5c260038882b85380a25f8507c25e2062081ae142c05881e2074181fa18342082b45e9709800e220ae14d098ac029820580c65f8861918e14b01917e2385094211b8540901e210a0e86e203c0300d65f851a86e203ae143965c60580cc5c26e208a21b850f092b01809c8601982087020c31749b882290ae14f06282a1b8822b850940d202b25f1720c00e208a4b385240245f88e142507c641a8600997e200d42b852286e200c03597e146a1b88037850e5971b8561a01800208606060340081fc1830c5d26e210ae14b06286e208ae14250347e148380986c5c0c037884b090310a20c0de23850e4702b02e1b8509788860785f85e203c030251a17e158561b88030251cad49b8580697e21831c394980ce158280697e218624394980c61a01a5f88e148e170521b0603482c0881203882b06c080de143965f881c8180386c18bfc080b03597e17882f85c1486c180d20b0202881e20a2b3060d2020331709b882088ae14be14812008320b881886e17050941f087881c1a41a8600b8500108a220a0940c2f850840ce203917850900d08016e206e148625c25298212d3882097e17050302507f881c1c01b8540a824228882825030a07105a140608d17a5c26003888601f338505a833049c02818a1b8825820e197e1b88e140c4e48e158607e81e2016a007e141e068812001808416e209e1421a05880802ca007e1586204800601fe2078143880b887000c1906a180245e0ae1425e208e1583e183fe2038035822185a1586a180c60825a0881e20ae1786034bf207881b85a158607e860d08203197a5c2620388378525c252981fe206a1a0665f8507e8360788201d08686e1581e2060808665f8507c21037882286077850842060580e208e142160a8665c0de207e141fa181d60580e20732486e158007c2165f882083203000281de1586a0b97e212c2f8508582a198065f881f8521b976001f087881d06a180282b85033881d02a0917a1a0ae1425e208e141f033880e45e1502a0a868280ce2074028007c21e148360b97e222c290607c34e1788a04607844e14810602105b8820276190208785e22811cc110785c14810601fe20800822402800878561a82e5f884b0be178603482207881b8520c82e200c1480e141f0940d603880b08e159707c21037881b850882320d86c0700e20808a86e1786a0901e5d00e200a460b8081f05b8560788180a80997e142105a8260788243407701e2300e15861c0a80b8508416a0b97603882434c0788c038561b181f8509c34c0788c00181f85c140c4000a0e4 else 0x301401128))))
def mo255H10 (j : Nat) : Nat := (if j<1 then 0x490270ea8add212c0006218f24726f40000000000000030f18000012e000000000000000e77b0ce41409362e7e1424510c330e000000000000000000188bd9e5000184ea46a000000000000000000058e370980000000000000000005600307e00000000000233600000000000538400038498000000000000002195e444e2044c28cce40b3f5b01170000046e65b26b5a05bd346000070282210001c59800028550001c01000030b3000048350f58000b976665e49c8000e1b445baac092110000271eaf28000000000010ce8000637ec53c0000000d0e3409fc458df9b1fcb8a5085b97270ac000000019e66a8e0000000000090ca239c000000000000001e3b54275b360849ec300ec0afb24d66bc706c000000038b29df800008460716189ed10800000006d73718e00026a04dbc702a00004a770400001a1b40078d5000007634000000000000000b1a48f600000637cbfc838b33133582ef0000b81647fe8b7a183b9e20000000201b099a40ba8fd0913803c8533d1ae0f84c66276000038a2000000006bd30e17af600030381149104667c4037e170c2b8046b083b8c69402d59ec196e1c133fe718000118ed42a605b660160a000140348d699b5a426a07383c31a6301c0000000707913c232d271680000000000285ea431b15a816302971c0037800000000000d2b1042800019aa00000000000300600000000000393f0000000000069ee0000e068000403690ce00036c20000000124ecc250000605a00000000000000000000000000000000000004937000000024c660a7a8a200000000000000105a85030000000000000007088000062af6a600000000000382f80000000a27024d41810000815c00000000001c4abd19c817000000000007a26000000000000000000000000006826a28e000000001ae0000c73e05a69500000000147289cdd1e2a1ec000000079d70665f12dd8800a00400000002000008000080040080700400000003008000010060000080200100801c0380300a00c000070000040080100200800000000000028070080000280101c0080100100600002800000000000000020000080000a00000801002004020070040000080a00001c000010040040000000200000000004004000000160180000300000000008002000008030020000100000000400004002008000000120140080000200801000000008000000000000280000201000000008008000070000080080300400801000000008008050000100080200c0000100300400c01004004004010010000080000f00000c0000801400000806016010030000000080100100000c0080c002004000020000200080100000801006000020000060080240080000202400002000000050060100180100000400003002000004008030020100100600000000001 else (if j<2 then 0xf01d7e15105080300001a70782080007327a2bc00069a8c43a0002672b1b39446353c00040890000000343f99d7000044e3426603e103b584c00028cad24e83b508729f433c540ac00061a4000182c7471800020b4000388a8000c3a3d3b5aa699d50000674f02ea09a00000003103906681989044000309922a800000000000000000000001134000000000000000621192354fc9e06c8ce000000000000000000000000000000477d6f00000f196880001aa06a0001e650000516b7a8600038967d2000008408c4700000000e7f400000000000e26c00068fdc187a3a68a9112d60c5408409f0000000000000005978f278000000071b9f18aa5f288900000001a47060798f440dca37c00049038c54c2d40b980000000000106900000000000000000000000000000019da00015860839115d000000002f56d4422e2e10f00914c6d10143980000000385094f80000000028203728060000145172f70142842425200018abf1f68376086800001b0000000000000000000182c8804000000000000000722a00000218000698ab1c8000110608bb000000020640000f41000000000000a9c7c86e05411360000e4510771a2c2089c6d98a420dd341df3ef81d000031fea209515a9fc0000e79c00000000000000000000e2b1b3a528000223800000000000000000016064c4880007b30000000000000000a3080000000000000026bff60140c642dcc534d2a72c8d67503f0000a45ec21f83e68fa02c675096c671422c6de0b34958000f1ac0000c580809000125340004001204144100000000a44ee843ac9e9240000000250f0000b86eb74d2c7000048a9c3ec0000cdf0000e70f4f000000001683cc8f421c000000004d0000099c980cc44e80000000e41441a00000000000200fe106b0d3c3f000000ac5bf404c800039b20001f3a000000000000e826823508a438908eb4dc784f1029d6eaceb28c9000000018ee0000e33d885c000285e121ee5a3c980000a440a47c0000000000000000002569db0b57a58ba8000a3d2105c51b0000f2f4876e04879ed6324000087bb128c31e000000000000000030391a000082ac0000000000014480002439d203000126bf4c471efc14b269fca5800000000000880515540c000025058000000000000000000046200004e50000530146100000000000057f943b4a059027758708ea098000000000000000b232e21790a00000000000000000008c3400018d4a0a3614922e1c35800000000000441a8f3000193f20d09943000183604e43109bb2c17fc00010ba0001258946ae58f6adb409000000000000a75000000000001036c0002e17a28bc6fbe75519a000082fd8f871c98245c80a8c5d604011fe56c00078105b7be3366fb8000000003d400058640001535f0ba00007c6fb65ef173c32000162e else 0x36b1418629cee5ec00038072a7a459ded0605393eaa6dd426c9d9000000000000000f0c2000000069cef359724c0000000012ac5f48088000db040000000256400000000000000042bc0000000383cab3400018018000932000018999120c2b3e7a80e900000000000043a00000000000084b49e4bc2c8235cf439460001e8a541cf12103ee43c0c2700008374000000079609c3ea4c6c2e39101128000000000007202e45800068e00000552800071447884c0dc00079fe000000000000000000000012490000106326d000050a9008a00032b9717e9016000040c09960000046c0b6a87d282c45d8677a4e20a9000024028000d05e00000a9e0aa624cc34d0570000000000000000000c3440731c461d805433139800019a5b182000000020bc0000147000049890000000000078de000000026a770f2000043100000000819c60a40000000000000018f600000000e0a80000000f16c0003f140000f3560003c4f8000d3e482fb03468a051a231598fdb8d76a920000cbbd89282b4d2ba2a8800000008095801000000000001c11657501de0000000192e43bb0028d18000000000003ac1d0d00000d8ac00059f3027b64bf0bc80009077a1dd0678000f07a0003c283911000000000000000c90ca609ca8ea2db0f5a1d4ea31c46cc700000000000000000003c2380009beca0028e8010da38a63a151cf1cbb092a82800041910000487d428c632524b6894cb4d961b4640000000000011f317f4000046000000000d0b095))
def mo255D11 (j : Nat) : Nat := (if j<1 then 0xc361419881c8c970b87c0785066207240080186c283310391c2c02c28b30d02cbe20144a1b2e22c2887103001041fc28941a80c407490161b0a01006203038283e83c2a180200c406090105c141fc28972f00c4074a090441e2c056147218441204c280f0c0200e5c00461b0a1800e5c01881c09864461402000c0f8600e1401880c0c09c32140200c406071602873850c62060e6140200c40606160290a390c6206c36140200c406061602b0a39cbe206d08f39fccb72dfca6b204c5df132c3b7096c122fe8be8ef67bbfaeb0b942e02b68ad4bb41ac8bb11abe6ae86b4aabceaaea982a09a6ee952a4128bfa1a28119ec676c9c3269198c65da957e5119356487900e3888cc62e38a56247879e190850a0d981e603d7f2df6b7c75ec67951e0f774dd5873bdc987129bbd6dbdaeb69e5a3467759a164758b461518065ebd7585bbd6b3594d5fc567152a534d461504d3c54d052e14a4d24e47dd1a045250e0424904d3ffcfc33d44f0c3b40e6738acdc235d0d1d333cc6f303cbb82d60aef2a3ca38278499325148f722808401f807891d587081a7c65117e85911554507130846b10bc3d80e4c33c0b7028508dc1f206b417104b00f002d007800f0000ffc504c3ff54130ffd604c3ff4c530ffd414c3ff54530ffd614c3ff20530ffd814c3ff54d30ffd634c3ff55130ffd644c3ff61940ffd654c3ff21530ffd10043ff61930ffd50503ff58140ffd31503ff58540ffd81503ff54d40ffd63503ff60d40ffd65503ff61540ffd844c3ff4c010ffd50043ff58010ffd43043ff14c10ffd53043ff58c10ffd83043ff59010ffc30443ff4c110ffd40443ff14110ffd50443ff50130ffd43443ff14d10ffd53443ff58d10ffc83443ff60d10ffd64443ff61110ffd500c3ff58030ffc510c3ff54430ffd610c3ff59430ffd60443ff20d50ffd83543ff55150ffd64543ff61150ffd86543ff50560ffc81583ff61530ffd43583ff54d60ffc83583ff58d50ffd54583ff61160ffd85583ff59543ffc8054fff60153ffd6354fff59153ffd8454fff60163ffd8158fff55163ffd8558fff60d60ffd43143ff50550ffd41143ff4c550ffc81543ff60550ffd60543ff4c450ffd43543ff0c450ffd81583ff54d50bfd8650eff61543bfc81502ff60053bfd83443fe58110bfc8054ffe54110fbd43502ff60c50fdd6354f7f61c10bfd84043ef61010bfd81142ff60c10fdd83042ff20163bfc8158eff61540fed82043bf59163bfd84143f750d30f7d53543df55150bfc814c3ef21130bfd844c2ff61950fdd314c2ff20560bfd854c3fe50130bfd86502ff61430fbd41503bf59160bfd84442ff20550ff960543bf58d60bfd810c2ff61830bfd864c2fb60810bed8214efd60430bed820c2ef610309fd870c2ef61010afd860c27f61c10b7d850c2f760c10 else (if j<2 then 0x970c6202c6e181825806152f881c9102c361503881c8c81cba030a83416201840690c820125d000a108630a1612e201a727038824b87c3185430941a80c40b0dc306903974061441880612824be19018512e201a43003e83c2a1819881c9082c32004985066207240d10786414072f00c461430510f0a8641c072f00c40609c4615068280c003c8a210c1f1a20f0c82c2c0601888c1627410871086c2c0600208c158541c0601888c0c80104010c1fc2a0c73970c6205860840585c34090397406202c525d01851189710160690970ba030a03066202c39258040400845803816150c0cc40e4c40614460cc4058723a030a86cbe202c30e8860b832012e0a0fc0f0a0cc40e4d0fe143b031d65c4243c40b20c5a0d2e16c320b11851c0349138ea0d03c2a071039208c430d25c5822108590018c280c4b88069f850fc0d0397406208642703897108b00702400630a8612e201a71247e80160884216c280c19881c9880c288819880e8e474000d0597c2c1b101d21938541a0a0300c40c4600094358510e1869020665f100d4c1c970b08f0c34810e32f88c2834b0e0b30a03810072e00c4034a108b18038c280f100c202d8511e1869024be201a4e14450320e5e0d00c4074906e14450320e5c3900c4074585924838501e201830370a03411072e1c806203a525d0185110960d880e90c906e1607868120501881cc60a05c190097050842d02c28331039330b03c34081881c40e6304c192e0a1085a04800c6144b88069802c28870d97c4059144219018511e1b2f880b10860310d0100110b30b021ce5c3188109c25c2c0f0d020665f100d8c143481e1a058540e2072403b0b0381620188a1d01970ee144443c4418584a5c0018c280c4b880b03490f90431854180601880e920a10e1905000c6146917c4034bc28b02c3980e201517201585018080388060e020be19018512e201a421b2f850f8b31030020602c2e1a0439cb83601880c18024165f0a210b620716e1b0a01c40e46050310000c280c0439136203058870a0312e201a3058282cc30341839cb863100a2c2f85160284a811ce2081ce1459860683031880512000761406021ce20304008580c050030a39130631050341985166187218cbe201450030b031ce5c3900c40609036142d0320e5c3900c4028a0002843861a20b0b170662072583f0a2cc30341839cb86014507c801cc280c0300c40749c280f0c0212a0710390c1201130330d854be207240004386406144b880690970b8870d85066207240030a2c0b0332f00c402891f898198600c012f85c40e4a01098960ac30060185c40e4a0002807854340b2f880e9386c2897100d160797c285887880541880b8284386414030a3412e201a58e4700cc2e180300c410000507d07858b8331039241421c320805851a00401880c1700 else 0x310786410360188c28e430500800838b85b0c820603601851ce2030745c862c4320c180d8061473880c18828102b0d88c28041a42082f86c461418391d0c1f1a20c1917134041418c2e190597806210138b0420c8b89a0218c2a190797806215878742cacc4614188a1d0497c36230a38068e024185b0c82c4614020d24382c4320f11850083481f8d10617c320b1185060e4a602190788c2830723e150c83c40ac7230322e26808b30a834165e01882c7e83c320b11850603480720b0a0c1c83458160c620a4b8750c83c4614700d222e83c32084b01c461472182887854320c4b01c40e43048e50585c36204b391c5a271c8844a0a41c070a868be22726a0b0d851262056391c7234418030b86416204b392883854320f10259c8e4bc2e185a01406222e39245a25164070a838be22724a0f0b864162056391c960cc36230a97068e48414b2140d406230a390c12801ce5f0a210c6202c407d01850ea0c739710863102c2c1b85964290280c40e48076150786416201838284385128302d97c403490fe144a0ccb8350188161385166181a0c1ce5c318805141fc28305881c40e478340b0a200f2072e80c4060a0020a049705618180d4061473880c1b02c325f0a2412a0473880c1439c2e5c1a0c41a0b1018240480800284385c320873))
def mo255H11 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x38acc4f2000000014e859300000252109a80000bfc00000001da6c09041ac4cf802400000003327800039e0291c0000000c3dff208518f949045a480c00008eb0000c51191198fe918e63b153f81720000000032400000001a0c42eb9e2531ab83d42f3f9ba81f36808903800092b0a1740000c91000000034ef80000001d39800070cb4a9bd77e528a9650000000090680000001c83c00000007b83373c000000000000002cfa0000881e000000000000001f840000000000000000000000000016658000000000000000e02326700000000000793350e200000002d060000000325c800000000000000388400000000e850000000000000006a5300000001416787d00000000000000000000000d1c6df7c336032b9190000a208000000040ba0000c0bbcce80003142842d212800000000000000000090880000e5abdca63ab269000025b7913c0000c73c9f56ca7983dc0c80000000000000000000001417c0000190cbd12731c300dd6f10e000067a025b72da9473c01000000000001c5f618a13fc000000000000001e4f0000000000000003060524dc9ee0000000500132d200018fc151dd3a5c67100c285c0064000140d80000000000000038e8a093999f296b66600000001061800000000000000024fe43e0000000000000000002c920000000085d4000085e000000002d90186000000000000000304078b00000000d4d80000000697134fb374c00000005c740000000514e000021c8aa45612aa42e6f00cd000000000000a9f782fc051485d13ab56d0000000393500000000000000000000001a7e8848c0570000000222e91d36b98000010000000140000100400c0000400000000804000000000000000100080000000800006000000000010040080280200600000000002000030010020000000300000c0000100801000803006038018050000280000000000000001008004000000000000380100a00c008000020180080000200000001004004058000000140200000000c030020000480080000801000800000020018050020040000000000001001004000000000000000000000200402001006008000010000040300900003401000004008000000000040000200000401000006008008010060000200000001001803000004018000000040300200400800002000000008000040140100400400c00000006000008000000000280800400000000004000000020000080000000201400807006000020020020100180100002c000030020000100000200c010000020000100500400002003000000050000040300000900a0040100000200c00002000010010000040040300100800400007000000048000040040080000400c0000101201400006004000010000000000180100a00000000 else 0x390e00014884000156900002232c7fb94f0000a2272c1b0b2938486ffc131988ab40d8c12647896fad800000000000d046e9180002a2c0000d3b80003d7733ac636b08c8000000186f49058000dc26000000000000000040873bb99ef46c8913314f229a33283b64289945b15e903b8a98000000008580d00000406a955c00045a8aa4851fa46f80003b78000000064f982cc663c3385a780000b7c092a80c6547c00000000000935c0000000050b000103b8000000080e60000000000044f7822f4f80000000000009153a2f391e016887d8000a1b10324000006a00000000000016b0000a4780000000520600022964c290001a23af19d892602e00000000000000172d1c80800000000000000000072a0000000061ca000000030ee80000000c7f7464390000000000000000000000001e93380febbc00000000000b0220000000000004c4d4000003d2f00000000000327300004012efe0000000000000000000000000000000000189975800005914c4820000000000001a248c1f05f8f6c805d1b3ca37025aade94490e43ce30000093b83d7cbb3aa000000000000b1fa96ac2fb000000000001e008000000000020ab6d090000f6b801580000000000152551eb000109828298000531202a800000005c4c000228a0000f3668530000423bf44a0000000000060060000000000023c2b6780000000eca80000cc588bcca300002c58f99250427305c22857a00000000000000000000000ade800000000000000000000000001d08800000000000000000000018271293d257202a73540000000c4ba00000000000824bf5e400010ab90e8224fc4f800094d2f9240007208e996c2f4853800000000000000000000000000000000092b7736800000007a6e000124215b4000000000000000000104700001d91d330368a09c18b3000000000000000e0fce43df1a8000cc76000284a0d22fa05e4e80000000000000000000000a2f800038778000000079bc000000000000000000000000014308488a9620000e71b87d34c58b9d91780000000b4bc0001c8680000001745400029aa3284000009b00000b88e9b800015a419d4000000000000000810c0000000000000010b811a8a24e0000000366a0000055c00000e0c11a58b8e6cc17ab4ed21e4000251b52dcc1b10f72460d3c6000000000005a4179c6cc28000025e0000000709052ed01d40002cd700000000000797b0000486c000000000000000000000000000000000753ce10183a60af4265609446ec00030cd0000000022f8000227200002cd800091c9e47c0000000135f67500000000019e000000000000001e6010d485c3321800000000000e0c8000000000000001a9080000000000000018ee00000001356381c39ffd3700000d3c8000705b5538000387f00000000) else (if j<3 then 0x180680001239c0d312f10a00000813a00000000000000000000000000c3c12160000213fc89546060ad31470144586cc1fba1c000000000000000000000000000000fb1b40f0000015d24a80000325210a0000641c00000000001c65400000000000a20bd126a6d9044639510480000000441400035a50000000090c11ad911ee504000000000ac000000000000001602291e897d0000000292f8000526e000000000000001547800061ab0000e8400000000cb3a0002f0d786e000000000000000000062fc0004814425c83380000000000000020050000000000000002809000007b66b779210000677b01cf9f10001a800000180e0001d3b290ec0b80cb80000abf0000000000000007a61b3ed2481622f663c1146070000101ea3f600020038000011000000003a34c480c8a000000000000e3c40000000a133104400001e60000479000038fc00004608c5200000000000246dfa3f01c6c63b032e5178c9ce20fce0de7a5cea0000000595f1c784074000393b739c0002451d123a09ec76400060e6fcd3f76000000000001e19c00000000001e8880006e5f0000e35f8006012c0692813a6e7de4ac8221a309e804613b6f60ad3e304b000000032c568d47212000000000000000d40d2fc40060000157c00000004920000000000002326f348000000000000000000000000000001030800052b9f0980000000000000028208000000000034b3d16f0001819a02800004158000000000000001c2ec00079f3d0f00000000000013d200000000000000000000001268000032548d8a9b9c09a000146ef8f8638e000000000007c46d23a01ed9f76c0bd67f109a9681257989cc9479fcb23aa034e5ebce9000107010263977000143794d60000946a00000001e590001404dadc4428408000034540000000043040000000000021c00000000000185b00000000832831e0c4d8e370001c3886f03e1102340003329500b0000000000060290000000000000000000146400025780000f3080005917f4d761dc000000000018204000000000000002c1f403372a4e90fed8b12954a129eb0fcd0b4db6640aa2a601eaa15db85c000606f0000000000000000000000000009518368c86409519c5c2240000000000000000001d2900000000000000000000001591000058b00000283a45c800000000002a666113b08e00000007918525805501330000f8b844980000000f09c00000000000000023722cb754600000001ce180000000000000000007347b5480001e610000235acc8ba26000152fc000614b515200000000000000000000000000814c6850000000000000000000217e00000000000000000002030d054c4d34b28932c9a7a4b126288ce68b08b70000a10bc290000a34c00000000000c4b8e61c000000069c00002cb56263 else 0x163400000000e9f40001d2b71cbc0a9969e91d0000043c0000000513e000000014623db6642a000000000000001935a4e8800004c807600000000506f273593780000000000000000000000000000060f350db446c0006212000184880000000000000000000000a34a00000000000000018700000000804e60580000000000065800000000000176d5cf100000000000000000005bfe00000001d76000015ad91b9a58828636c3c69c20c9364c6318692a2ef076c5cdc8b7961434483d0cd80000280648f00000000c3080003c7bf27124b4000000028d9a39f85d3ca69886434382954d38110629597480007ceb18c3c5e62b53cd4da4746daedd518dd0c5a9fae710000315a4041b04000080f8a9df43dd4f5000164b400061e8e44132c00000000012b95edce480000000b0acc4280001b0a0419f28c83af03e000331f800051402794000000002f0f7bc00000000ba20001cc1800089ca889c00029329131c814000149ab1e400001390000000000030b2000000000000066342799b0c79c00000000000231400075c9000000000001ce400000003d3a38e15b1c018fcdb800013880001225f915c1d40001878521a496645fd4f9605b0001225f01b00003c1400000000000837c00010cb8000736bd8253259a488457f3bc4ebc8b60000000000000009a2200000000000f0b2000128429ecac1ae4200000000ccbc000144d3955140360140006876e2c6000000000007060000000064c7148a87680006638000157e800000000001681b85ade36000000000006855000000000000000000109c3d2480000000000))
def mo255D12 (_ : Nat) : Nat := 0x204283018b80c40e8202390a0c072e011048180c2c3014b8044110a070c04032e0110442c30080440a000d0a072f103018042c3014bc40f0a06047310303014300c28bc41c8e042e030b0d2e0110443428080440c0c04010b0d2f10303010b801605429c8c44157c5553243cf8374be28c84184460ac007fd64ffac7ff54ffe29ffd43ffac1ff543fe287fd40ffa61ff0c3fe887fc10
def mo255H12 (_ : Nat) : Nat := 0x18cc99e85b222e9b0c90001823000000385156d71000008ee000000000000000011600000000000000003076000901e26104f712e2e007c5254880004d99aa96800000087cddf820000000c9a000db559b744ce96148d9cbc54000000482800000000000026f40000066990000e170000002e35c020004e34000e06708800000000000000008920000000800000000000211a83000000020f4888000247ba1a4e00008b484c34ca0002127dd6094a3cc027d096c000032f80030e600031898396c541410d017af1769400021e05154190003d3400167400000000000000003a1c000000cbc8000000000000314fc8132a3378c88412c71242e52ea6800000010da920456c9475be87400000000020d09410000000000f330000000001f76631e0574f20003cae9f20910130000000000000c31514842da810000000001a1e01bb410000e0800024f24d5c105ae3cc452a000abf800080b49300000000000003cb11502c27700000000001111000364c000c1b00000af2e6000b8980000000002b9303c001b2b00029eb4af532d4180000000000000001c8a00000010e000144754179068ba000519353000125800071a767026b5068003a4e000427c99acc2a7b346c47a71c84e000000000088b90080000000000006070000a5a44485ec00107ec17a8c1025937c1a490800000048a8000b0b04b42caa13c5c000fa4800000172d8afba39c3a27d0000dc6e00000000002c000000000794000000031480000016760000001a2e00008f8e41c6600023a8000000a6000000000000000000000000000000000287df51000381f84a0004be000000000001f9232cb7e519b430d4c876398262d6ccd8699e3fe95712e0901800100501000000a0000c0001020100004010000000000000202018040004000000203000040005010040001048000200008100002030040200000600003018040601010040804050000006000000004
def mo255D13 (_ : Nat) : Nat := 0x2862e204ff
def mo255H13 (_ : Nat) : Nat := 0x5b80000d40000000d80480000002151dc00059f5400000000000000071ad0000000000840016c012c45001ec0349001d7e5007040004103000
def mo255L : Nat → Packing
  | 7 => (4,6,7,0,0,5,0,mo255D7)
  | 8 => (143,5,7,0,0,11,0,mo255D8)
  | 9 => (571,4,7,0,0,15,0,mo255D9)
  | 10 => (640,3,7,0,0,16,0,mo255D10)
  | 11 => (154,2,7,0,0,14,0,mo255D11)
  | 12 => (13,1,7,0,0,10,0,mo255D12)
  | 13 => (1,0,7,0,0,0,0,mo255D13)
  | _ => emptyPacking
def mo255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 7 0 7 2 1 mo255H8
  | 9 => lookupWord 50 223 8 13 8 1 mo255H9
  | 10 => lookupWord 240 1213 11 15 10 1 mo255H10
  | 11 => lookupWord 299 1733 11 15 10 1 mo255H11
  | 12 => lookupWord 73 383 9 13 8 1 mo255H12
  | 13 => lookupWord 7 47 6 9 4 1 mo255H13
  | _ => fun _ => none
def mo255 : Forest := ⟨1279,13,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P7_0 : CutRow mo255 7 0 4 := mixedCut (pos:=0x180a03) (neg:=0xb0420a) (data:=fun _ => 0x10021265012012510120126101201251) rfl (by decide +kernel)
theorem mo255B7 : CutRow mo255 7 0 4 := mo255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_0 : CutRow mo255 8 0 24 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_24 : CutRow mo255 8 24 96 := mixedCut (pos:=0x44a0300608411048180a03) (neg:=0x24868c1260b0420a) (data:=fun _ => 0x322101870120128721102060100212761201205062210151923101519231015112043050623101513221018101201281012012610120128101201281012012710120126162210161120120600221016112013060022101611201206012012060120120605221016152210161120130601201306002210161120120500661046206610482601604760661046306610487066104835813675406610472201201102012011001201261201201100120127101201261012012710130426101304271211020702110206021102060211020602312017024126170241261701502427115024281150242712412617024126180231201702415617023120170231201702012016010021271100212711003426121102010211020102110201021102010231201202415612020120120100212211002122110034221201201201002122110021221100212211003422121102010211020102312012021102010211020102110201021102010211020102110201023120120322101610221015001201271) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_120 : CutRow mo255 8 120 23 := mixedCut (pos:=0x254088300602222210180a03) (neg:=0x305243416130420a) (data:=fun _ => 0x231015002310150023101502110308506510561096018749a05184196054851422101504221015021103076323101603231015021102076065105620760137306510582065105821641356224120175120130602313017612012060) rfl (by decide +kernel)
theorem mo255B8 : CutRow mo255 8 0 143 := (@joinRow mo255 8 0 24 119 mo255P8_0 (@joinRow mo255 8 24 96 23 mo255P8_24 mo255P8_120))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_0 : CutRow mo255 9 0 51 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_51 : CutRow mo255 9 51 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_147 : CutRow mo255 9 147 76 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_223 : CutRow mo255 9 223 2 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_225 : CutRow mo255 9 225 96 := mixedCut (pos:=0x88048883011210180a03) (neg:=0xd1244c10b04580a) (data:=fun _ => 0x273101202130101021301010273101202731012010012221100122212130101021301010100132211001322120310120203101202130101021301010100132211001322121356010213010102031012021301010203101202130101027310120243651202731012021204010213010102130101021301010212040102130101021301010100132212120401010042221213010101001322121304010213010102130101048062532503504305035043050350430503504805035044050350440503504805035044048062543503504805035044020310120213010102031012020310120513614405136144020310120203101202031012020310120513614402031012020310120203101201301222121301010213010103110228172130181130122812731012024365120273101202731012013012221130122216243017112031080321301811203408005530483055304930110329101103281130122812031012010013221100132211004222121301010213010102130101010012221) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_321 : CutRow mo255 9 321 96 := mixedCut (pos:=0xa0440602242048180a03) (neg:=0x6a0d1244c608b0420a) (data:=fun _ => 0x231201802312018021102010100212213830178521304010201201202135701010043221383017851004322183051753100212213830178610021221830517638605677321102010100212212130401010043221211020101002122110021221201201202012012023120120201201202012012020165120231201202312012021102010231201202110401020140120211570102017512021104010211040101006122123120120100432212012012020120120100432212115601021304010213040102110201020120120211560102016512021102010211020101002122121102010211040102110201020120120211020102110401021156010211020101002322110023221100232211002122110021221100432211004322110021221100212211002122110021221140232211402322110021221251251202512512014023221140232212312012010021221100212212110201010021221231201202312012020120120100432212130201023120120231201202110201021102010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_417 : CutRow mo255 9 417 96 := mixedCut (pos:=0x894088301083011018240c05) (neg:=0x249824c1a0b0420a) (data:=fun _ => 0x37105a832950188537105a839205185235610473350162729206185237105a839206185237105a8392051852950638623501629292061862350162929205186273015a302950189573015a3092061852350162823501628292061862350162823501627273015a3073051640295018957305164092061852052132720521327295063862730516503501628235016272730516507305164035016292480355323505628205312483356104830101237001014370375016843561049310504370105043801010237013120010131200103020118110102370101023801312001013120010302011811010238030201181304051813040518130201181302011813020118103031110030211105316043053160430531604305316043035610493602051815013243003021181501324300602519114126090060251810602518106025181105043101010231010102310131200800302118110102310101023101010231003021181030451810302118103021181531304305313043012120070) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_513 : CutRow mo255 9 513 58 := mixedCut (pos:=0x180444203014221804a811003) (neg:=0x6a130682c49304420a) (data:=fun _ => 0x76104097746153610401337174427361040133717452656204013371043105722303115104415361045145620a2018840a201884670140706004171070140610701406109761067167026070600627106004171067014080074106710741067167016080040133720741067107410671670140806701407067015070673150806701407067014080701536108751068187410681040133726701607067017070673170806701607067016080600417103220119560041710230311526004171024035162600517106004171060041710074106710741067167014070043105730401337202201185) rfl (by decide +kernel)
theorem mo255B9 : CutRow mo255 9 0 571 := (@joinRow mo255 9 0 225 346 (@joinRow mo255 9 0 147 78 (@joinRow mo255 9 0 51 96 mo255P9_0 mo255P9_51) (@joinRow mo255 9 147 76 2 mo255P9_147 mo255P9_223)) (@joinRow mo255 9 225 192 154 (@joinRow mo255 9 225 96 96 mo255P9_225 mo255P9_321) (@joinRow mo255 9 417 96 58 mo255P9_417 mo255P9_513)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_0 : CutRow mo255 10 0 24 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_24 : CutRow mo255 10 24 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_120 : CutRow mo255 10 120 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_216 : CutRow mo255 10 216 45 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_261 : CutRow mo255 10 261 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_357 : CutRow mo255 10 357 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_453 : CutRow mo255 10 453 56 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_509 : CutRow mo255 10 509 7 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_516 : CutRow mo255 10 516 96 := mixedCut (pos:=0x894060440602203210240c05) (neg:=0x6a0d09892608b0420a) (data:=fun _ => 0x1030541010305410103054101010241010102410101024101010241010102410101024100402112104053121040211210402112110102410103054101010241014120020141200200402112104021121040531210402112110102410103054101010241014120020141200200402112110102410040211219604677384013a5164140540641042306414054084013a51522616435206164392041773520616439204177384013a519204177384013a51641042306410423084013a51520416436414054064104230641042305206164384031361525636435206164392041773520736435204164352061643520616439203177384013a519203177384013a5184013a5192031773840313616410423057063643641405405206164384031361641405408403136157063643141200201212002003023121030231210302312110305410101024101412002004021121101024100402112104053121040211210402112164140540641405406414054003023121121200201212002012120020) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_612 : CutRow mo255 10 612 28 := mixedCut (pos:=0x502201218088180a03) (neg:=0x6a24868c116130420a) (data:=fun _ => 0x10031221100212212146701010031221100212212146701021467010211650102146701021165010214670101003122110031221100312217506167320156120100242211003122110031221411355304115334021402010214020102140201021402010214020101003122110021221) rfl (by decide +kernel)
theorem mo255B10 : CutRow mo255 10 0 640 := (@joinRow mo255 10 0 357 283 (@joinRow mo255 10 0 120 237 (@joinRow mo255 10 0 24 96 mo255P10_0 mo255P10_24) (@joinRow mo255 10 120 96 141 mo255P10_120 (@joinRow mo255 10 216 45 96 mo255P10_216 mo255P10_261))) (@joinRow mo255 10 357 152 131 (@joinRow mo255 10 357 96 56 mo255P10_357 mo255P10_453) (@joinRow mo255 10 509 7 124 mo255P10_509 (@joinRow mo255 10 516 96 28 mo255P10_516 mo255P10_612))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_0 : CutRow mo255 11 0 11 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_11 : CutRow mo255 11 11 45 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_56 : CutRow mo255 11 56 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_152 : CutRow mo255 11 152 2 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B11 : CutRow mo255 11 0 154 := (@joinRow mo255 11 0 56 98 (@joinRow mo255 11 0 11 45 mo255P11_0 mo255P11_11) (@joinRow mo255 11 56 96 2 mo255P11_56 mo255P11_152))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P12_0 : CutRow mo255 12 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B12 : CutRow mo255 12 0 13 := mo255P12_0
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
  · exact mo255B7
  · exact mo255B8
  · exact mo255B9
  · exact mo255B10
  · exact mo255B11
  · exact mo255B12
  · exact mo255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255G : graphValid mo255 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255R : Impossible false graph 13 eightInputs.toFinset := by
  rw [show graph = targetOf mo255 by decide +kernel]
  exact mixedRoot (g:=mo255) (top:=13) (i:=0) (before_sound K251 (known_down V251)) mo255G mo255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_8397

open PEqualNP.Outside.L_meta_8397 in
theorem PEqualNP.Outside.L_meta_8397 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7)) t → 14 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo255R g255R ⟨C,hf,by omega,heq⟩
