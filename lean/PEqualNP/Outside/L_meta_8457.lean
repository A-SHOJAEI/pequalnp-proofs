import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_8457.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_8457
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
def graph : Sig := 0xffffffffffffffe8ffffffe8ffffeae8ffffffffffecffe8ffffffe8eeeceae8ffffffffffffffe8ffffffe8ffffeae8ffffffffffecffe8ffffffe8eeeceae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 5 && x 6)
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 5) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6)
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 5) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6)
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
def eightEdge (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 5 && x 6)

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
def neighbor8453 (i : Fin 8) : Nat := [1,0,0,0,1,3,3,4].getD i.val 0
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
def K7 := extendKnown [] 4 [(7,[]),(104,[33,97,82,65,48])]
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
def K27 := extendKnown K7 4 [(27,[]),(43,[84,49]),(45,[84,49,33]),(51,[65,81,16,48]),(54,[65,81,49,16,32]),(57,[81,33,48]),(58,[16,65,80,49,32]),(75,[100,84,49]),(77,[100,84,49,33]),(114,[65,64,97,80,49,32]),(147,[116,100,65,81,16,48]),(150,[116,100,65,81,49,16,32]),(184,[116,64,65,96,81,32]),(240,[67,64,65,115,96,81,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V7 low27 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := plain_low (m:=15) (hints:=1) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=15) (cap:=4) (before_sound K27 V27) (8,0,7,0,4) (by decide +kernel) (by decide +kernel))
def K15 := extendKnown K27 5 [(15,[]),(23,[67,16]),(105,[33,97,82,65,48]),(120,[48,49,98,81,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V27 low15 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 5 := plain_low (m:=61) (hints:=3473410) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=61) (cap:=4) (before_sound K15 V15) (4,0,57,0,4) (by decide +kernel) (by decide +kernel))
def K61 := extendKnown K15 5 [(61,[]),(62,[67,16]),(91,[100,66,82,33,16,48]),(115,[67,99,16,32]),(118,[67,99,16]),(155,[116,100,84,33,49]),(185,[116,67,84,48,96,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V15 low61 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 6 := plain_low (m:=103) (hints:=90177537) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=103) (cap:=5) (before_sound K61 V61) (0,32,7,64,5) (by decide +kernel) (by decide +kernel))
def K103 := extendKnown K61 6 [(103,[]),(110,[98,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V61 low103 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 5 := plain_low (m:=179) (hints:=1078001665) (cap:=4) (by decide +kernel) (cut_root (u:=true) (m:=179) (cap:=4) (before_sound K103 V103) (128,0,51,0,4) (by decide +kernel) (by decide +kernel))
def K179 := extendKnown K103 5 [(179,[]),(182,[32]),(186,[48,81,32]),(242,[96,48,81,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V103 low179 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := plain_low (m:=31) (hints:=65537) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=31) (cap:=5) (before_sound K179 V179) (16,0,15,0,5) (by decide +kernel) (by decide +kernel))
def K31 := extendKnown K179 6 [(31,[]),(121,[98,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V179 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[(0x8eff396382b2e3bfce58e0acb8eff396382b2e,0x10081428202c0402050a080b010081428202c),(0x813647695dce204d91da57738813647695dce2,0xb4ca422914c82d32908a45320b4ca422914c82),(0x1c17e1ed91c40705f87b647101c17e1ed91c4,0xa313c946914028c4f251a4500a313c9469140),(0x7e0b829466619f82e0a5199867e0b829466619,0x525b0ab051601496c2ac14580525b0ab051601),(0x0,0x0),(0x7000e59724411c003965c91047000e59724411,0x2da0f54fae810b683d53eba042da0f54fae810),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(4,0,43,0,4),(0,32,7,8,5),(32,0,15,0,5),(2,0,45,0,4),(8,32,7,0,4)]
def g47A : List (List Nat) := [[],[33]]
def g47D4 (_ : Nat) : Nat := 0x5bd4910
def g47D5 (_ : Nat) : Nat := 0x908400e140fd21fe10fd10
def g47H5 (_ : Nat) : Nat := 0xa
def g47D6 (_ : Nat) : Nat := 0x28189f
def g47H6 (_ : Nat) : Nat := 0x19000005400000000000000018800060d4000
def g47L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g47D4)
  | 5 => (3,1,3,0,0,5,0,g47D5)
  | 6 => (1,0,3,0,0,0,0,g47D6)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 5 0 1 g47H5
  | 6 => lookupWord 1 23 0 7 2 1 g47H6
  | _ => fun _ => none
def g47 : Forest := ⟨47,6,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4_0 : block g47 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B4 : block g47 4 0 1=true := g47P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_0 : block g47 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 3=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 1=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 7 := lower_forest (g:=g47) (i:=0) (hints:=3145729) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 7 [(47,[]),(55,[67,16]),(79,[101]),(107,[98,66,81,48]),(109,[33,97,82,65,48]),(122,[48,49,98,81,64]),(151,[117,101,67,16]),(248,[82,80,48,49,114,97,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[(0xc3406101ffe38680c203ffc70d018407ff8e1a,0x824b860133a104970c026742092e1804ce8412),(0x9540b37c28cf2a8166f8519e5502cdf0a33caa,0x514511e485e0a28a23c90bc14514479217828),(0x0,0x0),(0x42a341c7c71c8546838f8e390a8d071f1c7215,0x408429f6cc04810853ed98090210a7db301204),(0x3c1c9e7c152078393cf82a40f07279f05481e0,0x30012ee0b70060025dc16e00c004bb82dc0180),(0x28bf1c8210fc517e390421f8a2fc720843f145,0x883ad00900fb1075a01201f620eb402403ec41),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(2,0,57,0,4),(1,0,58,0,4),(8,0,51,0,4),(16,0,43,0,4),(32,0,27,0,4)]
def g59A : List (List Nat) := [[],[49,84],[16,67],[16,64,48,83],[48,16,81,65],[48,81],[64,83],[64,81,49,48],[80,49,65,16],[80,65]]
def g59D4 (_ : Nat) : Nat := 0x5dd4530
def g59D5 (_ : Nat) : Nat := 0x1030fd30fd10
def g59H5 (_ : Nat) : Nat := 0xf000
def g59D6 (_ : Nat) : Nat := 0x23440bf
def g59H6 (_ : Nat) : Nat := 0xa700284000010c0000f5b9a80ca000000047006140000308000
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (2,1,3,0,0,3,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 8 0 4 g59H5
  | 6 => lookupWord 3 23 5 9 1 4 g59H6
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
theorem g59P5_0 : block g59 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 2=true := g59P5_0
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
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=3211265) (before_sound K47 V47) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K47 7 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V47 low59 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 6 := plain_low (m:=221) (hints:=1124532226) (cap:=5) (by decide +kernel) (cut_root (u:=true) (m:=221) (cap:=5) (before_sound K59 V59) (0,16,77,128,5) (by decide +kernel) (by decide +kernel))
def K221 := extendKnown K59 6 [(221,[]),(222,[118,67,16]),(245,[98,48,83,114,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V59 low221 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[(0xfdc470001ff9637e3f711c0007fe58df8fdc47,0xb94054a5288861562e5015294a2218558b9405),(0x0,0x0),(0x6d80300001f00efd1b600c00007c03bf46d803,0x44802b5ad7730ea911200ad6b5dcc3aa444802),(0x124d4003fe0f7c00c4935000ff83df003124d4,0x2050318c6751800c08140c6319d4600302050),(0xf0328ffc00008183fc0ca3ff00002060ff0328,0xf022018c6224200fbc08806318890803ef0220),(0x8e29807fe0069d80238a601ff801a76008e298,0xc088c63198a85b003022318c662a16c00c088),(0x0,0x0),(0x3d20f8000000003c0f483e000000000f03d20,0x3d00e739dc0d24040f4039ce7703490103d00),(0x0,0x0)]
def g189C : List ColumnInfo := [(4,0,185,0,5),(0,4,184,1,5),(128,0,61,0,5),(0,128,45,16,5)]
def g189A : List (List Nat) := [[],[64,114,83]]
def g189D6 (_ : Nat) : Nat := 0xe413f
def g189L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g189D6)
  | _ => emptyPacking
def g189I (_ _ : Nat) : Option (Nat × Nat) := none
def g189 : Forest := ⟨189,6,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 1=true := g189P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact g189B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 7 := lower_forest (g:=g189) (i:=0) (hints:=1077215234) (before_sound K221 V221) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K221 7 [(189,[]),(219,[98,33,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V221 low189 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),(0x1f8eeaffc187f034b0001f8eeaffc187f034b,0x94a0c285ac585902095294a0c285ac58590209),(0x96ce8f813ef02430000096ce8f813ef0243,0x6b593d6a5083a60042ad6b593d6a5083a60042),(0x3e026050042970b030003e026050042970b030,0xce7a6049191c70f02039ce7a6049191c70f020),(0xc1f7930703c6906d8cffc1f7930703c6906d8c,0x42180902000480650408421809020004806504),(0xfe0414d0042f0c9c3007fe0414d0042f0c9c30,0x318416b0e6230c0810c6318416b0e6230c0810),(0x0,0x0),(0x7810003e083e084f80007810003e083e084,0xbde7e4947be00392c0f7bde7e4947be00392c0),(0x0,0x0)]
def g190C : List ColumnInfo := [(4,0,186,0,5),(0,4,184,2,5),(6,0,184,0,4),(0,8,150,32,5),(8,0,182,0,5),(128,0,62,0,5),(40,0,150,0,4)]
def g190A : List (List Nat) := [[],[81,50]]
def g190D5 (_ : Nat) : Nat := 0x17e53
def g190D6 (_ : Nat) : Nat := 0x1ac6881ff
def g190H6 (_ : Nat) : Nat := 0x300
def g190L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g190D5)
  | 6 => (1,0,3,0,0,0,0,g190D6)
  | _ => emptyPacking
def g190I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 0 1 g190H6
  | _ => fun _ => none
def g190 : Forest := ⟨190,6,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P5_0 : block g190 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B5 : block g190 5 0 1=true := g190P5_0
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
  · exact g190B5
  · exact g190B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 7 := lower_forest (g:=g190) (i:=0) (hints:=1076973856) (before_sound K189 V189) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K189 7 [(190,[]),(243,[99,32]),(246,[99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V189 low190 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := plain_low (m:=95) (hints:=50397185) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=95) (cap:=7) (before_sound K190 V190) (16,0,79,0,7) (by decide +kernel) (by decide +kernel))
def K95 := extendKnown K190 8 [(95,[]),(125,[98,81,48]),(159,[118,67,16]),(249,[98,48,49,114,81,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V190 low95 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 8 := plain_low (m:=119) (hints:=88145921) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=119) (cap:=7) (before_sound K95 V95) (64,0,55,0,7) (by decide +kernel) (by decide +kernel))
def K119 := extendKnown K95 8 [(119,[]),(126,[98,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V95 low119 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 8 := plain_low (m:=183) (hints:=1078001665) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=183) (cap:=7) (before_sound K119 V119) (128,0,55,0,7) (by decide +kernel) (by decide +kernel))
def K183 := extendKnown K119 8 [(183,[]),(250,[98,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V119 low183 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 8 := plain_low (m:=187) (hints:=1076953089) (cap:=7) (by decide +kernel) (cut_root (u:=true) (m:=187) (cap:=7) (before_sound K183 V183) (128,0,59,0,7) (by decide +kernel) (by decide +kernel))
def K187 := extendKnown K183 8 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[(0x15fd53701f21314071f82a4057f54dc07c84c5,0x10a000701f0101650a04e040428001c07c0405),(0x4be1ec09e045a4838e33ad512f87b027811692,0x43496001a040a098214015090d258006810282),(0x4c14bfbf460094400fc001813052fefd180251,0xac169f8e40981402d4b10082b05a7e39026050),(0x344800cba8e80b0c700c0238d120032ea3a02c,0xa558288980e0021094da063e9560a226038008),(0x8a0202049b1640b38003d6d6280808126c5902,0xa80682501a060004969be2f6a01a0940681800),(0xe022418675da4a3c000450af80890619d76928,0x52a155266518482b692411014a855499946120),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,5),(1,0,62,0,5),(4,0,59,0,7),(8,0,55,0,7),(16,0,47,0,7),(0,32,7,24,6),(32,0,31,0,6)]
def g63A : List (List Nat) := [[],[16,67]]
def g63D5 (_ : Nat) : Nat := 0x4ef7258610
def g63D6 (_ : Nat) : Nat := 0x2044080104200ac85b400bf58610fbd8910bbd8910b758c10bb58810
def g63H6 (_ : Nat) : Nat := 0x5800
def g63D7 (_ : Nat) : Nat := 0x196f2804756bca101d972e8407888807f843fa21fc10
def g63H7 (_ : Nat) : Nat := 0xf9030000e100000052908430
def g63D8 (_ : Nat) : Nat := 0x5d1a17f
def g63H8 (_ : Nat) : Nat := 0x1980000024000002a800
def g63L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g63D5)
  | 6 => (5,2,3,0,0,6,0,g63D6)
  | 7 => (3,1,3,0,0,7,0,g63D7)
  | 8 => (1,0,3,0,0,0,0,g63D8)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 0 1 g63H6
  | 7 => lookupWord 2 11 4 8 3 1 g63H7
  | 8 => lookupWord 1 11 0 7 2 1 g63H8
  | _ => fun _ => none
def g63 : Forest := ⟨63,8,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 1=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_3 : block g63 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 5=true := (@block_merge g63 6 0 3 2 g63P6_0 g63P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 3=true := g63P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 1=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
  · exact g63B6
  · exact g63B7
  · exact g63B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=3211265) (before_sound K187 V187) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K187 9 [(63,[]),(123,[98,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V187 low63 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[(0x61d500e6ce20001e7f518ceef02c3aa01cd9c4,0x14400e40c2024418021d02a600028801c8184),(0x5a92ef5a0a1800018e42081d7a0b525deb4143,0x5092c30a0216caaa704a00551a0a1258614042),(0xba67ac9840380001f00027828b374cf5930807,0xae293c10400911140e90278085f5c527820801),(0xe128531985c07ffe019fb06001dc250a6330b8,0x6828031880c18220121000c4034d0500631018),(0x0,0x0),(0x850356e6318781e000ec53110550a06adcc630,0x830354e211021c06a408d51a1c10606a9c4220),(0x4e8a1253047fe0000226331c4809d1424a608,0x14d4a805200461d948232221e0a29a9500a400),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(64,0,47,0,7),(32,0,79,0,7),(2,0,109,0,7),(1,0,110,0,6),(1,2,104,4,5),(0,4,104,3,6),(4,0,107,0,7),(104,0,7,0,4),(0,2,104,5,6),(0,32,7,72,6),(8,0,103,0,6),(3,4,104,0,4),(96,0,15,0,5),(0,64,7,40,6),(4,2,104,1,5),(8,32,7,64,5),(8,64,7,32,5),(1,4,104,2,5),(6,0,105,0,5),(32,64,7,8,5)]
def g111A : List (List Nat) := [[],[101],[33],[33,101],[48,81,98],[48,81,98,33],[48,97,82,33],[48,97,82]]
def g111D5 (_ : Nat) : Nat := 0x29be1543d8910
def g111D6 (_ : Nat) : Nat := 0x1841018018943809faed21c21bb553624437721ec4886ed43d8910
def g111H6 (_ : Nat) : Nat := 0x8
def g111D7 (_ : Nat) : Nat := 0xa349218428c1a0d08828184346218c20b1518108144880e8230a442101e2818c34009023b3420640dcc10783c4308203c503cc305c1842438436a30d72a849dfcce481806000ff55121ff55210ff90e10ff55110ff90d10ff50d10bf58e30bf58e109f59640bd58430bbd8910
def g111H7 (_ : Nat) : Nat := 0xe00011560000030c000022002c4c10000000
def g111D8 (_ : Nat) : Nat := 0x581304f12608848a8211051880890061601133c38891a04cf44488702144440f2838899a04213ca4448890011854203e108428388d3492a084e0c220b2a084610e0c227cdaab74fa04c6390f001fd41fe90ff903fa81fe30fe987f0c3fc21fd10
def g111H8 (_ : Nat) : Nat := 0x2c2000000424e3a8500158400000406c2a03800000001808000000000000000000000000001a08000000000000000020000000000000003a080000000000008000000002e60004600000000011800000000da60b24960c001d0ce7b2a080000018080
def g111D9 (_ : Nat) : Nat := 0x4c213f
def g111H9 (_ : Nat) : Nat := 0x106a2800000c012b728001a81832a11c2807e3000001623410004080000000000000000347330002aa800001b10000b88806148b000c0f65400000406003b0000087001040082
def g111L : Nat → Packing
  | 5 => (1,4,5,0,0,0,0,g111D5)
  | 6 => (4,3,5,0,0,6,0,g111D6)
  | 7 => (11,2,5,0,0,9,0,g111D7)
  | 8 => (9,1,5,0,0,9,0,g111D8)
  | 9 => (1,0,5,0,0,0,0,g111D9)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 7 0 3 g111H6
  | 7 => lookupWord 2 17 5 9 2 3 g111H7
  | 8 => lookupWord 7 67 7 11 4 3 g111H8
  | 9 => lookupWord 8 47 6 11 4 3 g111H9
  | _ => fun _ => none
def g111 : Forest := ⟨111,9,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 1=true := g111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 4=true := g111P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_3 : block g111 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_5 : block g111 7 5 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 11=true := (@block_merge g111 7 0 3 8 g111P7_0 (@block_merge g111 7 3 2 6 g111P7_3 g111P7_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8_0 : block g111 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B8 : block g111 8 0 9=true := g111P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P9_0 : block g111 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B9 : block g111 9 0 1=true := g111P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
  · exact g111B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 10 := lower_forest (g:=g111) (i:=0) (hints:=53477377) (before_sound K63 V63) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K63 10 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[(0xffff7f91c1fc65017d03981559fc80189170,0x2222228080e004440150030001186480109050),(0xff00ff8282c24edf0abc187c8aa60240821d84,0x4848487f000021130a2d883802820240820504),(0xffff007f024032120a0010e49f7dfc0e2004b0,0x95959500240c0aa0e40274c49c65980e2560a0),(0x415398029f543e3826a800193ea6049,0x1919194411198029c4a3aca45a8001316a4001),(0x80789e038864800e030482077c158a06,0x7070780b98202886582560364108534048802),(0x0,0x0),(0x164260402f006e003e0012303e26009,0xe6e6e6216c2604063204404ba1032a82802008),(0x106c1c81409c0805010060403d158202,0xf8f8f818441d815098582110006c5049510200),(0x0,0x0)]
def g223C : List ColumnInfo := [(2,0,221,0,6),(1,0,222,0,6),(64,0,159,0,8),(0,64,151,8,8),(128,0,95,0,8),(0,128,79,16,8),(4,0,219,0,7),(8,64,151,0,7),(144,0,79,0,7)]
def g223A : List (List Nat) := [[],[16,67,118]]
def g223D6 (_ : Nat) : Nat := 0xc609ee871c910fe22188110fe12148110
def g223D7 (_ : Nat) : Nat := 0xc08c08000000c080083a82000303ae99e4080369ae59899e5a6a08bbda58d8175695d45392108fcf0d88448017f5c810ff240887fa20443f6392217f5c910bfee4887f920842feb8c217f5ca10fda42905ff71483f710c417f5c620fdee4885ed72042f7b9221775cc10
def g223H7 (_ : Nat) : Nat := 0x10401c00
def g223D8 (_ : Nat) : Nat := 0xbce58052a6093845c14aca6131579c8d5c00241ab794f010118ad2f391820271e3d84cc03fe20ff483fe10ff443fc10
def g223H8 (_ : Nat) : Nat := 0x8d13fc300140ebf50003840000080800001aed24000030e0000000385c2ec6429cc0022000000001c1001880000000000000000030700000000003003
def g223D9 (_ : Nat) : Nat := 0xa50ec2ff
def g223H9 (_ : Nat) : Nat := 0xe200000084c0b32afb5c00e10040
def g223L : Nat → Packing
  | 6 => (3,3,4,0,0,4,0,g223D6)
  | 7 => (17,2,4,0,0,8,0,g223D7)
  | 8 => (5,1,4,0,0,8,0,g223D8)
  | 9 => (1,0,4,0,0,0,0,g223D9)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 7 2 1 g223H7
  | 8 => lookupWord 6 47 6 10 5 1 g223H8
  | 9 => lookupWord 2 13 4 8 3 1 g223H9
  | _ => fun _ => none
def g223 : Forest := ⟨223,9,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 3=true := g223P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_3 : block g223 7 3 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 17=true := (@block_merge g223 7 0 3 14 g223P7_0 g223P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 5=true := g223P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 1=true := g223P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 9 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 10 := lower_forest (g:=g223) (i:=0) (hints:=1124139009) (before_sound K111 V111) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K111 10 [(223,[]),(253,[98,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V111 low223 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0x2500a2b6204940cfd7e2da39c303c23b5c512,0x810002010040800ff6a2d2094003c23a04502),(0x710bfa0f770d95b2fca17440c001005846d940,0x802a640f674094800081004040010048449800),(0x4341f0040589611e001e1baf1cb03890d30c12,0x57c591d088b9635e0014128f0af44190130010),(0x0,0x0),(0xbece0060987008a10280d21ce14d47a5b010e5,0x1a44100010360820000050a4a00403a4b00045),(0x8dbc05902182e24b4143a04c22e6906b08228c,0x85aaa0d06308c00b5446a15a06e0900b080088),(0x407005b508a2665421e94040029a884e082208,0x4255452f88b326f4a9b94801311a0a44002200),(0x40001e08c70190002008610490ae784200021,0x45a18df3ae40714d6f5f8f50490be4104d6420),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,1,240,4,5),(0,64,151,32,8),(64,0,183,0,8),(128,0,119,0,8),(96,0,151,0,7),(4,0,243,0,7),(0,128,103,16,7),(1,0,246,0,7),(16,128,103,0,6),(0,1,240,6,6),(4,1,240,2,5),(7,0,240,0,4),(2,0,245,0,6),(0,4,240,3,6),(5,0,242,0,5),(2,4,240,1,5)]
def g247A : List (List Nat) := [[],[32]]
def g247D6 (_ : Nat) : Nat := 0x308fd8798f10cee63dc910
def g247D7 (_ : Nat) : Nat := 0x9c1183086065074202d33cb1005c13a13648037f31a417f5cf10dfcc7886fe634427eb8cc77bdc910
def g247H7 (_ : Nat) : Nat := 0x4c
def g247D8 (_ : Nat) : Nat := 0x656d18849c82be7441c03d0889ca2a01d2551c89ca202b4e92e889ca2c524e4d1689ca25029272e88adc41d10f05c6a648dd6ae3d8f84800ff8c7fd31ff4c3fd20ffc43fd10bf98efd61
def g247H8 (_ : Nat) : Nat := 0x107241008445b38aeb0000000000
def g247D9 (_ : Nat) : Nat := 0x2690ae37f
def g247H9 (_ : Nat) : Nat := 0x11004200002e80504acd2313d5e880219c02
def g247L : Nat → Packing
  | 6 => (2,3,4,0,0,3,0,g247D6)
  | 7 => (6,2,4,0,0,7,0,g247D7)
  | 8 => (8,1,4,0,0,9,0,g247D8)
  | 9 => (1,0,4,0,0,0,0,g247D9)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 6 1 1 g247H7
  | 8 => lookupWord 2 13 4 8 3 1 g247H8
  | 9 => lookupWord 3 17 5 8 3 1 g247H9
  | _ => fun _ => none
def g247 : Forest := ⟨247,9,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 2=true := g247P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_2 : block g247 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 6=true := (@block_merge g247 7 0 2 4 g247P7_0 g247P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_2 : block g247 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 8=true := (@block_merge g247 8 0 2 6 g247P8_0 g247P8_2)
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
theorem g247G : graphValid g247 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 10 := lower_forest (g:=g247) (i:=0) (hints:=1161887745) (before_sound K223 V223) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K223 10 [(247,[]),(254,[98,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V223 low247 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[(0x670a20eac47a06993950f5320281161f7061a,0x243003065003810882140a032008112156020a),(0x8605ad450d31544dd83abc8c52100e6a084ea0,0x100c6c400e5004455800848812100c4a000c80),(0x814104438030ba3449af213f6004c612ec00b2,0xc3c310a181243ab005ab61344487e210a80030),(0xd9381098224602921f2012c01873ce8d11810c,0xd94210f92ac444301d60104859728688018004),(0x29865ba051884d002052d0608f9c3190d27841,0x80001b811a149000012534201003090d24041),(0x78ac06141688ba9244004c94b447d90c00a144,0x24bd2e06841ab283e08c0c94a4054904002100),(0x0,0x0),(0xc10250a06008014e2241a02109c82090021001,0xd5d37647e408b2de2e61a0a19ae800672c9000),(0x0,0x0)]
def g191C : List ColumnInfo := [(0,4,184,3,6),(16,128,47,0,7),(8,0,183,0,8),(32,0,159,0,8),(0,128,47,16,8),(128,0,63,0,9),(2,0,189,0,7),(1,0,190,0,7),(32,8,150,1,5),(129,0,62,0,5),(4,0,187,0,8),(128,32,7,24,6),(32,128,15,16,6),(18,128,45,0,4),(1,8,150,32,5),(7,0,184,0,4),(6,0,185,0,5),(5,0,186,0,5),(1,4,184,2,5),(0,8,150,33,6),(2,4,184,1,5),(12,0,179,0,5),(148,0,43,0,4),(36,0,155,0,5),(40,0,151,0,7),(160,0,31,0,6),(144,32,7,8,5),(2,128,45,16,5),(0,160,7,24,6),(4,128,43,16,5),(40,128,7,16,5),(9,0,182,0,5),(48,128,15,0,5),(136,32,7,16,5),(3,4,184,0,4),(33,8,150,0,4),(152,32,7,0,4),(134,0,57,0,4)]
def g191A : List (List Nat) := [[]]
def g191D6 (_ : Nat) : Nat := 0x34107410440040000000000d08100000001c470c2038204001c3040000000000000000000b257ab152a651a813a9a4ba512289409e4ec73381b4d46732170b256299409a401e8d4642f13890421e0d8602a120783012060180156f9550f724423df30ba8e488573e4d751c910c7743aca392211ef985d072442bcf22ba0e48863ba1e641c9108f7cc2e6392215eb905cc724431df0bb92c28853b656645c810ce7c1ee4a82217d19320540442fc32440a80884fc2613150110f70b2c4310221ee26488620443dc2ca90a40887b89912148110a5ecaf0cba0218bd855d2640429bb2b322e60871b5977254110a7ac8d00b8cc94ef92601719929ef22c02e33253b65e644ca21d733270299443bc543e05328871f4c9c02e690e9e59780485508fbcc2e238a818ee64e09718c339a87c12e31853b64664dc910e72b2ae310c41ce6645c6218835d2cac0443106ba9918088620c7bc2ee2b0a419e482e05744431dcc9c12e688573e4d75dc910ae7c9b0bb92214ef91597724429db2b326e4884bb6626488620
def g191D7 (j : Nat) : Nat := (if j<1 then 0xf8354110def7254110def7250110bf78150110fb94350110feb7250110fe87250110ff38150110ff08150110fb94150110ff23150110ff13150110cfe64dc910ff12150110def724c110ef96588110bf98488110efa6488110ef96548110efa6448110ff13148110dbd855d010afd8599010dbd7455010cfe645cc10ddd545cc10cfd655c810cfe645c810ff22150110ded75dc910eed65dc910ded74dc910eee64dc910ded73dc910ded85dc910ded84dc910ded54dc910ded83dc910ded43dc910cfd655c910cfe645c910ded751c910eed651c910ded741c910ef56548510ded731c910aff8558510cfd7358510def7254510bfb8054510def7250510ef6648c510def724c510ef5614c510bfb804c510ef6644c510fe7724c510fe4724c510ef56588510ef66488510eee641c910aff8159521afd8599121afd81991219fd84dcd21cfe64dcd219ff845cd21cfe645cd219fd80dd132b7f8550d21def7350921cfd65dc121cfe64dc121e7d6588550fb77150540ddf7388550e7d6548550ddf7348550bfb80485509fd81dcd40bf7815c940bf4815c940bfb804c940df7719c540bf9809c540bef825c5409fd81dcd42bed821c540df5711c5409fd81dd132cfe64dc132ddd43dc532bf5819c141bef825c141bf7815c141cfe64dc532cfe645ca31cfe645c2319fd80dd131afd81991319fd84dc931cfe64dc931ddd43dc931bf78150931cfe645c221ddf744c931ede644c931dbf7450531cfe64dc131cfd61dc131afd8199132afd85992219ff845ce21cfe645ce21b7f8550e21ded744ca21eee644ca21fcd434ca21cfd655c221bdf844c931bdd831c5409fd84dc530cfe64dc530cff7158530ddf744c530ede644c530edd614c530aff81596209ff815d220afd8599220afd8199220cfe645ce20ded7350a20cfe805c664ddf744c930cfe645c620aff8558620cfd825c664cfd73586209ff87546209fd8750620dbd7450620eed6588620bed8488620eee6488620ded7388620ded545c810aff8159520cfd835c664cfd655c620fb471505409fe878c5409fd878c540bbd848c540bf9808c540cfd805c6649ff874c5409fc874c5409fe87885409fd8788540bbd8488540bf980885409ff815d230ede644c930cfe645ca30afd8199230ddd435ca30cfe64dc930cfe645c630ddd435c6309fd84dc9309fd8750630dbd74506309fd81dd130afd81991309ff815d130ced655c810fe22188110fe12148110cbd655d010cdd655cc10cbd74990108fd8799010cde645cc10cbf865d0109f7815d120be98088620de57188620cf77158520beb8050a208fd87993109ef825c6309ef825d1109ef825cd10cee645c810cee64dc910a7f81595509ee871c9109fb805cd21cef7258510be7814ca218fd87992218fd87992319ef825c241ced65dc910 else (if j<2 then 0x810202626118620006078a10100a10000107060e0c0c178a0c08050b140e281000618702000c502ca0e8400140810100a000c0041080000018ac10800e078201881a080805080805080e080416506c2028102038181400100805080805000600040008100a1428103040b0c102140b0c102014202014000a100e41080a0408002014262b078507830a110841d0dc5141fc5071004628378507830a0861b060cc4838c09a2218305d150c1b118b068388c5624183a0f142087148c18508dc50e82084a83c50a080b02a183cc71787820a41c6e2d042ac714281b118b078308c562040b20c603e28502ac714281d16821052b1c5e1d0824302c0a86c50805cc2183c0f160c1b0784c461893bf9dccece75b39e9c7ce026f53749a54cee6593149874c226052f39694ac653328a93dc9b24a924e91b489e4312128fd47d23dd1d68e846e23651ac8cec63a2ff1708b0c52627512b892c47e1fd0e687043221850bc85b42c215508082fc14209503280d402dfd4fdb7e63ed1f38f8d7bf3dbded2f5a7a13cf1e5af2778c3c49e06efd7773b7dda0ec1754b9b5c98e4671738a1c44e136fdb7b1b96dbc6d6b655afad656ab34d5a5ed2968d34519f8ced673b33d96ec9f64831e18e4c6c62a30f185ac1e607b0017e2beb5f2af7d7b2bc15ddae8d728b7c5bb2d9d6c2b5b598ac89602ae9571ab2d566a9b538a9894b8a4d51aa89941c9ff4f3a7853809b14cca6292f69754b7a53929093049524492068fd47ba3a11a08ca46222f912887c43b215509e84040b20410147f23ed1f50f9c7c83dc9ea8f127713b11d4ce9a7473979ca4e4671437e1bd8dbc6bd3529a7cd3269334699d4cde65732898e4c426092fd17acba65bb2c895e4ab054929d1488a2650d27f13bc9d24da26592cc91247122c914c8764081ea8eac6f033c18d8be85a02af14b89d84aa24610e07ec37e1a70c3057028812308583a81a4096036012c054000afd8199210cfe645ce10cfd655ca10cfe645ca10cfd655c610cfe645c610aff8558610cfd7358610bfb80546109fd8750610dbd7450610df97150210fb94150210ef96548210afd8599120bdf835d510aff8159510def825d110dec825d1109ff815d110df7815d110afd8599110afd81991109fd84dcd10cfe64dcd109ff845cd10cfe645cd10b7f8550d10cfd65dc9109fd84dc910efa6448210afd81991209fd84dcd20cfe64dcd209ff845cd20cfe645cd20b7f8550d20def744c920eee644c920cfd65dc520cfe64dc520aff8558520df77154520eed6548520eee6448520afd8599210bdf8354120afd85993109ff845cf10cfe645cf10b7f8550f10cfd655cb10cfe645cb10ef6644c710ef56548710ef66448710e7d6554310bdf8354310dbd7450310bf78150310aff8159610e7d6554120ef66448510e7d6554110bd else 0x218100002140c281830200004028001421041008207208400006281055078a180283c50c0805081e0e281c50204028400140814281c50200158210000100a10005020400107060e0b1016203060407440a0e0c1c10000620c1618140810185c20400000000650942838985c241c30282040c16150b1414281a162a0e1e281a10344a2840fc5040e06820d04102820818821000e04009020428102140c28185020e058a0d08188305807058a1807452086031582100010010bb0828502166231438502150586c2098ac1098ac109840b118ac30c00184080c462850a040c541820a2282a2d102058345a0840018a838413c5050206840d08185030a0400000008050800281028382020504041810000c913054a11880d16894a0f050708001e082000282c0f142c0f14014a1002080050703c508040e078a132810281020188c3010644078b8108880c08100001000141800402840311861008100085021320840000031060bc5080502040617098a0c0))
def g191H7 (_ : Nat) : Nat := 0xcc00000006aa0000000001af801a0000000000000080e52003960000000000000000000035000000000041e00000000000004400000a4b8f2e000007314de9a0000000001888882603c6142e002ac002ce002a5450004300000000007d7f180090ac000001b6800002dc000000000000001e8410007ca006b200001ea001c7000000000048a00000000c8000000000141800c98000000000000ee934544d800180000810004080000000001
def g191D8 (j : Nat) : Nat := (if j<1 then 0xba06080c9ffc7f19f987d49f1c7b99eb879c9e1c7779d8874e9cfc7319c8870e9bfc6ed9b706ca9afc6af9a8069099f4669994063e98b4621985060497c45dd97285bc96ac59b963057c95ac55b953053c94bc51d944050093c44e193384be92c44a1925048491dc465913844090ac41b90383fe8fac3d78f203ba8ebc39d8e283768da43538d103328c9c3158c202f48b8c2d38b102ba8a9c29b8a20274898c2558920238889c21387f81f0877c1cd86f01aa866418585e016c858c14b84f812c848410b83e00e683640c582e00a8827408981f006e816c04d810802e808400f8000ffa81887fd30c43fea1c43ff4c940ffaa910fff71503feaa421ff9c540ffa8298ffd31503fe38a81ff50931ffaa3087ff724c7fea0c21ff55120ffaa2907fd75443ffba263ff5c540ffa82907fd31483fe90aa1ff88550ffaa0907fd40483fe98241ffdcd40ffae6a07fd50c43fea0a43ff54521ffaa9887fd43487fea1e21ffdc940ffaa890ffd43483feb9281ff4c521ffa83187fd51883fea8a21ff8c540ffa62887fd424c3fea8221ff50620ffaa9107fd30443ff20a61ff50530ffc42987fd54043fe90a61ff50130ffa80887fd32507fea0a21ff5c941ffae6887fe70507feaa221ff5cd41ffa86887fd21503feba221ff88540ffae0a0dfd748837eb0a41bf99120dfcc9105ff71482feba241fb4c920fda85105fd718837eb0c417fdcd20bfee8906fd65482feb9a41fb88620bfae7105ff73442feb9a217fdc910fdee4885fd72443f639221bf58510fec62887f531443fa98e21fd48510ff480887f940443fd10221fe48110dfaca085fd740437f320217f5cc10bfae4087f621443f690a41bf59710bfae9886fe64c42feb9e217f5cb10dfacb107f521c437eb2c21bf99110dfcc9085fd73842feb94217f5c610dfac3087f940843fc90421bf59510bfee8885fd74442feba4217fdc941f7a84a0dff70506feba463bf99231bfae518dfd708c6ffba2637f5d131fda6510fdd434c6ffb9263f74c931dfac298dff704c77eb2c437f5d221dfcc910dfd738877f322637fdc552bfee0a95ff7350affb8a857fdc142bfee8995fd744cb7f32265f750d32bfee6a0dff714caffb8265bf4c961bfae528dfd70946ffb92a37fdc151bfae720dfd72906feb8483fb50932bfee6a07bd43502ffb9281ef50940bfee2a07bd41502feba461bf99230fba87185fd719037eb0c617fdd130bfae8986fe644c2ffb9261f74c930bfee2986fd614c2feb8c617f5ca30fba62986fd65486ffba2437f5d121dfcc890dff73486feb9a43fb50921dfac290dff70486feb94a17f5c650bfee4a85ff71542feb84437f5ca40bfae7204ff71596eeb98213f5d6649fae33257f7550edeba0215f5d410afaeb18def72442efb9aa19f59550bdae4085dd739467fbaac35f5d640 else (if j<2 then 0x84850b58c28a4186871c2e0e0a29061e187830b828a4186871d607c04002b15084c1c91101c51302144a0007240c2c0714083c28384850181cc830b82ca4114068720362c3848181f1504811c5144a121629610d061e186030b41c502130f1c2c0c4c08288b15043490b03020e0a12c50741240c2c084f16044801289c5011a22144a180c2f14084c2888348050a14980d07411c71062a620a1e187981001c5064a121e600714283a085018813000ac59841071c0028931506603878458c5c34286121c901b1504603869801c5c382144a12231450621928386149841ca8782061e6004020b172838719415887438a861c0c2f14084c341d06289830b4182878a861d6007141908386418a44988687821c705c501e0c2c61712061c0b838a1d61081b16043860b03c51302812212202c0f144c08884802051e28b9806c5411507182c0e28501b1506084c48a9841448687828a1d0c931506283860a00c58158420e1e605407170e088a28509981501c5220e82141225630d0a0489285071cc510074a00182a6068501851a981c12830b004a20680400281c72602e0c9000ac581580e074213260714401d28006030bc502130f0a8114062a63170e0904504870a0006c5815842132090071560385030b81c502134a142004392b14688860b03130222c5ca078124384850041c37146880a1206c59807411d0629121a621e08741241887102c0c082b160438481c90f419887821428001b1506607e1e089000a0641132498878225040629121a621e0889801c5144a00184f1489286048698010a2213c51f1e2889141906621e0889801c5c30a0f82120726604407170e0850001d28a121406c5180e19630905121a1d0e288030b41c502130f07202c0c4c085315044880b8382414486878a21600714410a1a283885801c54213148a0712262d071418504862514418a0f17144b084041a0198021406c51c00074a2c28726048681c61a98141c830b4a0020280070688c5030b01c5021312478a06282c0e07144c081d285091f06c58113580742206406630b291861f13c1c31206ca07c5242c3005630b2861b1cc301c2ca461e082e07283850d0ed8c21207ca06c52468841b281f1461ac18214ca061b60504b0f070a1b161c9211c831aca87182d04632a1c51000c1c30ec20706c524846b0453281860b250c0158c2ca86220487084b2b141c7ceab374cc7b2d8ca6b274c91b228c80b1dcc63b158c48b104c35b0b0c1cb04cc07aff0bf2afa4bdbaf30bc0aeccba9ae80b94ae1cb7badb8b60ad4cb3facd8b2cac7cb11ac20afcabbcadfab38ac0aaccaa5aa68a8caa0ca75a9b0a5ca924a3fa8c8a20a844a03a7d89eea7849d5a7309bca6c49a5a65898aa5dc969a558944a4ec925a45890aa3d48e7a3688caa2ec8aba290892a214871a17884ca0ec82 else 0x4445850106071a16107c18381c62406444585844302138a28561214083828481c8200645030b418a1c1b141e044200b074541160714183451302411212140838481c5431a424a0607012459111428501864544030b07061828084c345410d0706142c811504400114544030b061d0889288c401454402131607143d2834511451441100044083840010030b8207188d100c2e08012870b0342008a15111444040228613020a121207150838481431f132416102d088c181c645100a14411515102c0c02286200645030b41189111150c084c624064445858443020e260715284840b204541109111150c0838681c511004a16184c08022840d074541821515100c2c0228645440b038a07061c1a12150c6805081c813028ac50706184c7d1114284860b428a2306071835145106285200b0745418a1a287c183841f0645021341184c7d150441f45440213124a1c801d140c2d04060a289001002131111147c044e0864144450f018a0607205614084c2852047450f8a410d071b144001285a046224a1f0f150c6a04341c60b2045418a150c4c9204424444543028a0e1c421214284854445224a0d151612140401281c7c50f4a810d142c0c083a281b15041c90f8206418a14182e0d040609121a1e289830b824144868a87231453044440b0341c5130206128a1429631508381c485078b41c58714140c2c07140850391a281ca830b82418a14196007143d084c6030b41c502130f1d056112190e1e2875801c5144212131f161d183581f06c542138a07216007143d084c65801000a421fc50e13240c2c0714084c50012890ac3c1c5c20f8786203c07144c085040008c3c1c5c20f87861e0c2e0a283d04521c18958c50f0e1415631449081838658c51242060e1b143818492858b0f0607c5410e12222c88181f1504610c5140e864a183f141c51285190b4158c28a8786202f170f083b28481d0418a831c41828a87861d607c071400284c19081ca1001c5134a00c2070624471438184a1d287070fc50e121418650629610e1a1c70b03c513020a144106260c2d060a2a1a1c75801c5000a064213204007144c0928001880b58c24144868a87231441281))
def g191H8 (_ : Nat) : Nat := 0xc1c00000008aa57062e90a54a10000003ca9087e485298dd8075101c210000c1f0000001dbf6ea47400000012d10000000000000677e81c00007a0007a4704600035b6a806160000000000000849000236c00044b00000025edb00710d2238ff45f816ebec5528a70004278000000000000000086e0000000000000a6f00010b724f0000000df800032800000000647669054000000b6362ec000a5c77fd9af9ac00000000005f4000c5a0000000c01f02800000000000000034bda2200590fb160c533015391937c17173f907cfacabb6500030e26830000000000000000000000123f278fbd0000000d2b80028fc29a0004350000000c0b00000000000000001db0000d15a4314e6000052000084dc5a38321d8945a9d77c3a080000cb97080000010326357342cc10cc24b206c000000038000310a0000000000db4443000000000000022613e7c940006336028d25c440000000dcc8b1d5180000000000000000000000981b252978881d83c98a49a0008080a180123042040002c34a1286042b000162e0004b4ecd80003148000001c27000000115a000d230000001824000215908b0c5684f8818304145151a3817ba9703c19664ca0000000000000000216000000000000073c8000000000504fdfc0000003ae096600020c80039cba3000000000018c81240000000000000000000150151980000006f341880000000000000000001cb50004ae4000e0c41aba670e948cc1b3a70000000000229558e000b6c800147a0000000000001c5500061b40018110000000000000a67000000000042880034b18b7e0eea7f9d700d0318000000000307791c0004dc13c800003800000000031a543421442c800107c0000003876cfd000000392baf79128c231e08007308c168f7068e07e0e8000842461301b5896d504680000000000000000001e4075f800315c6c363382a10e582f47729df1dbe3c81bd23edc6804c44c9765d2000a85493b9140004348bd4001ed704c59bd517c8007130e4001cdd0003abc0000000004b24000000d49f40a99e000e0f000297c0000005b04000000000000000004010040005058000201008080000000140a0700808020c0080404010300800020400000070080000010300000020000414040080400010081c0000008080403060180002000042801018200003008000002018440009000180200000300001018000000
def g191D9 (_ : Nat) : Nat := 0xbb029145870610f0e18b17161c1843a5120c1ca082ec45870614a28183962c0580d161c184287872c5868b0ca411d085072899f0d14c4105283921a28f824a518041c90d1619a030a507201868b0c7422528d010e5863868c4a0e306384a51a301c71602c078b0e0c2143c316105d80f161c125085062c18b03160c3043854a2508386382078a6074104525062a28d0e6a1818528313143c334047c229283141421c0e6a0988528314142073504c422928314543078a620821488914583450f0cd0184291122c31c0e68c22243850c90398020a50e242a0161c098852880f14c4105287062029c860614a0c39c860614a1409885284eb9c435ee6ac3d766ca556a0734e4e4497ece39a12fd5629950c9cd2f450c7f0c010412c11000ff443fe10ffc43fd20ff883fd30ff8c3fd40ff903fd50ff943fd21ff887fc10ff8c7fd41ff907fd51ff947fd32ff50bfd52ff50ffd54ff4c6fd61bf992fd65
def g191H9 (_ : Nat) : Nat := 0x12600006f55c0001711b7acf2c44d4001aa800198357a0008e8944001fb4001c96d60b94000000000000000072f5e8070d6039bacc9ae94848a2e137486ad20004420016a5e7874800000120e91278a00000138c001f569782e5cf0fa10eb76af6600133256d9aa08f592338000001f03689baf264e66b72159a22452a0c4282a1480941b9a000001ab40000000001a40ee00000000000171b2d0af502426c0000d80006200000010c624103a000001ca6000000000000000f4dcac591728ac9d16f88b35a56f9e0000006bf5642c1f7fcddfb0001552001876000000001c2c00194aa2a000a33d9d8b010a00071400000000046313b24d2dec746b80000010aace0000000001511e6b342001c020000012b6000000a09598271e5e2b2fa200070deff7060142e3e51369b76001a8a575e8c61978f0da90000000000000000000000000045de31b2333000055becb720001268000c9200061ad2a00000151805a76332414fc9c4e7a900000018cc0858a2986000001351e7c000d8030fc7f446000000f7deba00101eb960016360000000012fde4aa10a82d3f2128f2844000000b1e0000000015a88bc000001a16000000000f3c24f40adb287a7089472ec63c000000861cfbcf86c2000234da6001098000000000d8505825400009ec3f755e046f630401d22756fd2ceae71cf2e010200802070202404030000c0000010000002010000c00000082000000001e00008140202018000c07010041201018080c06028140a0b008000c0100014000000814000d008140200060000c00098200600
def g191D10 (_ : Nat) : Nat := 0xc0a18211437f
def g191H10 (_ : Nat) : Nat := 0x8679672000025963f5a25e04c0000084ee0000000008875a6c00da3829f00000033a6993000000000006080083005280152e78000000006240000004340002081002080
def g191L : Nat → Packing
  | 6 => (47,4,6,0,0,9,0,g191D6)
  | 7 => (269,3,6,0,0,13,0,g191D7)
  | 8 => (220,2,6,0,0,14,0,g191D8)
  | 9 => (28,1,6,0,0,11,0,g191D9)
  | 10 => (1,0,6,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 15 127 7 10 6 0 g191H7
  | 8 => lookupWord 89 479 9 13 9 0 g191H8
  | 9 => lookupWord 73 331 9 12 8 0 g191H9
  | 10 => lookupWord 9 59 6 9 5 0 g191H10
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : block g191 6 0 47=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B6 : block g191 6 0 47=true := g191P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 29=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_29 : block g191 7 29 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_125 : block g191 7 125 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_221 : block g191 7 221 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 269=true := (@block_merge g191 7 0 125 144 (@block_merge g191 7 0 29 96 g191P7_0 g191P7_29) (@block_merge g191 7 125 96 48 g191P7_125 g191P7_221))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_15 : block g191 8 15 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_111 : block g191 8 111 40=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_151 : block g191 8 151 69=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 220=true := (@block_merge g191 8 0 111 109 (@block_merge g191 8 0 15 96 g191P8_0 g191P8_15) (@block_merge g191 8 111 40 69 g191P8_111 g191P8_151))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_3 : block g191 9 3 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 28=true := (@block_merge g191 9 0 3 25 g191P9_0 g191P9_3)
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
theorem g191G : graphValid g191 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1076953089) (before_sound K247 V247) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K247 11 [(191,[]),(251,[98,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V247 low191 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0x56099221800a279e0f98838c0631d54a68c4c2,0x320500012b8102860788008406215108680482),(0x61004030815649c79155200a531e1ad596440d,0xc0a00298505221008054000a511c02d4144009),(0x1f099201001000701a67a730406bed0b90004e,0x958b160000808701823bf7188c2ac23800044),(0x884225cc48a82609648846bdb8c40090949990,0x800610e402a24198041421920c00090948110),(0x30c570162544cc45c0208880200122244e2021,0x3b5df1470524dccd6020e984202100000a2000),(0xc0b40c1e3e21902000a21873850c30eb693320,0x80a00010285103021a820062800c306b601220),(0x1a7a39c056815020600a54427fd00d14210a10,0x335990c11684d020651c14005f12cf04010800),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(9,0,118,0,5),(2,0,125,0,8),(1,0,126,0,8),(32,0,95,0,8),(8,0,119,0,8),(64,0,63,0,9),(4,0,123,0,9),(16,0,111,0,10),(0,32,7,88,7),(40,64,23,0,5),(72,0,55,0,7),(96,0,31,0,6),(64,32,7,24,6),(0,64,23,40,7),(8,32,7,80,6),(8,64,23,32,6),(32,64,23,8,6),(0,4,120,3,7),(6,0,121,0,6),(1,2,104,20,6),(73,0,54,0,4),(5,0,122,0,7),(1,4,120,2,6),(18,0,109,0,7),(104,0,23,0,5),(34,16,77,0,4),(0,2,104,21,7),(7,0,120,0,5),(4,2,104,17,6),(16,2,104,5,6),(16,32,7,72,6),(2,4,120,1,6),(5,2,104,16,5),(72,32,7,16,5),(13,0,114,0,4),(17,2,104,4,5),(66,0,61,0,5),(80,32,7,8,5),(12,0,115,0,5),(16,4,104,3,6),(68,0,59,0,7),(24,0,103,0,6),(24,32,7,64,5),(20,2,104,1,5),(3,4,120,0,5)]
def g127A : List (List Nat) := [[],[48,81,98]]
def g127D6 (_ : Nat) : Nat := 0x2d2baa28a725a422a11f9e1c9b199816951392108f0d8c0a890786048301803c4e6598d535c81093baa49654d72042ccda3996635c810d1b6566598d72043c1d655d16354c10f079957498d5304345d979966354c10a37aa0865cd530428bea82197454c10a37e99985cf5304385d859957398c10b2768e655d26304383d859957498c10c3761d9399663043c4d6558d535c810e17e198599573042c5da5e1a655cc10c3766386995730424dfa664e855cc10bb8e995348520442ee3a654e2188110a3be9985dc9304428efa661772cc110a73e8d86dc9504430ee87e59531c910b3368e6598f7244346d9599663dc91097cea5711c5504c28efa65d7825c530a73e8d65e09718c385d86615655cc10
def g127D7 (j : Nat) : Nat := (if j<1 then 0xd2148110ff131c4310221d5e655cd53043abacab9aa60857765e6354c10f2f32cc6a9821d9d7498d53043cbacab1aa6087675d16354c10af6c9ccab90215ef9359572042bdb2b31ae40873b996635c810cdec2ae9318215ed96d4d72043adacba9ae40857b656535c810af7cb2a6b9021cef9654d72042bdb2ca9ae40873b259535c810eb732aa6b9021d6d6554d72043b9cc6a9ae40877358d535c810e76b2ac6b9021cbe655d2630433bb0ab9cc6087379957398c10e5eb2ae8b1821cdd655cd6304337b0cba6a60874f59574d4c10ceecc2e7a98219dd865cf53043abacab9ea60866f6157494c10e6e432e6a98212fe98219530429fb2e432a60866fe197454c10e5fc32e8a98219bd865d1530439790cba2a60874f9957454c10e9eb2ae8a98218ff865cd530433bf0cb9aa608737e197354c10ceec32e6a98219dd855ce53042bdb2f31c43107799957188620ef2b2ae310c41de6635c6218837d4cac0443106fa5958088620df531b0110c41a7d8599663482dbb2732cc6905f3e4d654c920aefc9acab9e219ee65e0973442dbb2732cc7885f5e4d654c7109efc9b0ca86212ff9661730c42bbb2742ae70853fe59855ce10aefc9b0ab9c218fd87996638434fb0b32cc7085b764e6598e10aefc9acbb9a21a7d8599663c433f6ebc0242b06be9978048560aefc9aed10aa15df935d9215433f6edc0242a867e5db8048550aefc9acab8c619ee65e09718c33dacbc12e31847f663769c530cf7bb704b8a615df93615738833deebc12e29867b9d7825c530cf6baf04b8a611ff985d4714c29ff2cba8e2985fae497158130ef9b8ce2a82617eb925c5504c3be2e238aa0987f41c53154130aeec9d0ab9c414ff96615738833daedc12e29867ba1d651c910cf743cc6392219ee8758c724433dd0fa98e48867ba1e531c910cf743aa6392216ef9654c72442faf26b2a62885bde595388510b7bcb2a690a219ef85dc9604433dd0f328e48867be0f7258110e76b1ee4b02219ed86dcb504433db07b96a08875b54f72d41109efc9b0ca82219ef86dc9504433db0db92a08867be0f7254110eb7a9ee4a8221d6d53dc950442bf32132ee090f3b9977258110ef5b92c0a8221a7d8599663442dbb2732cc68857be4973d4d10af6c9ccbb92215ed9099772442bdf26b2ee48857be4165dc910af6cacc7b9221cee6598f72442bdb2131ee48873b59563dc910cf6b2f04b9a215ef9054f724439df2ca9ee48857be5953dc910af6c84a7b92215ed90d4f72443adacba9ee48853fe59535c910af6cb6a7b92215ad9414d720429db2c29ae40857a640535c8108deca10e992c11bd985d0530429df2ca9ee488637e197354c10cdcba300298218bf865d1530433b2e6c00a608537e59855cc10aceca10ab98214dd96215730423ef30b88e29853be59535c810 else 0x314010800341004100000c50403141e181000314100030c100c5040c0202040830338741386180f0308303b87e18631415141e181000014506450643070604000000001c50706040001214420000485109c5040235450945234291410300942387e185914102c0a02508e1f861a45040000000000314100c504000c504c504c504c504c3040000c220250c150c88080014504001450681040d0330302387c13861c0d60420145040014505450400145a042004100545080000000000000c0810041000030204001c1000704000002010082040c2082d181000045840800184040000704001c5040c081d1410304040520101c100000000002c5040c081c181c1814081000510100003860405101000408100c140819141e181e181910100000000000c304000c504000000000c3c0b010cc430f02c044c040008050e81080a081911810a810400070204c3c08230c00c083050130b02c042ac0aa6aa0a90a80a7aa74a6ea5ea58a48a38a32a2ca1ca16a10a009fa9ea9d098e94c93c92c91c91691090a8fa8ea8da8ca8c48be8b88b28ac8a689688688087a86085a85483a82a82480a7f07e07a879875674674073a73472e72872271c70c7066f66f06ea6da6ca6ba6aa69a69468e67466464a64463e62e6286226126025b659c59658658057a56a55a55454e53452450a5044fe4f84f24ec4e64e04da4d44c44b44ae4a84a249248c47c47646646045a45444443e42e4144043fe3f83de3d83d23c23bc3b63a63a039a38a38437436435e34e34833832832231c31631030a3042fe2ee2e82d82c82b82a82a229c28c28628027a26a26425424e2482382282182081f81e81d81d21cc1c61c01ba1b41ae19e19819218217c17617016a16415e13a10c0f20ec0d20cc0bc0a209208207205803401a000adfc9acaba0215dd93a15730429ff2cc2ae60857764e655cc10aefc9acab98215dd95e1973042bbb2d42ae608577e59855cc10e6fcb30ab9821cdc96615730433bf0cc2ae6084bfe5985cc110aeecc4cab9821cdf8699573043abb0b32ae608577e61655cc10aeecc2cab9821cdd8659573043abd0ab2ae608757615655cc10c7ec3ccb31821a7d8599663042dbb2732cc608677619855cc10cf6c2ee5982212ff96615304433df0db92608867b61b724c110cf7c2ee4982219ed85dc930443bd6e4b02608877adc9504c110b7dcb2a710221fe26588620443fc2cb10c408856f64e655d010ff0b1c4310221fe35388620443fc4a710c40887f854e2188110b7dcb2a690221fe26548520443fc2ca90a40887f898d2148110ff0b1a4290221fe35348520443fc4a690a40887f854)
def g127H7 (_ : Nat) : Nat := 0xb35c4aa90cb200045bab974000000062c0092800408000009305146d45dc748ce56300e3e993171bf7941e5cc934000e6b950014710c70ca0c0141000041
def g127D8 (j : Nat) : Nat := (if j<3 then (if j<1 then 0xe65dc121dfd65dc121fdd6354c10fde6354c10dff7588560efe6588560dff7388560dff7548560f7d65d4c10dff7348560dfd7354c10f7d6554c10f7e6554c10efc8654c10bfd8654c10eff8654c10dfd7688750dfd7388750dfd7648750dfd7348750bff8654c10bfd8594c10dfd73d4c10efe6548560ffa5388110dfd655ce20dfe655ce20dfd855ce20dfe855ce20bff8359620bfd8399620ff92154130ff97254130ff95388110ffa6548110ff87154130ff97154130ffa7154130ffb7154130ff96548110ffa6348110ffa2154130fed6348520fee6548520fed654c920fee654c920efe6598d20bfd8598d20dfd655cd20dfe655cd20dfe655c620bfd8399520ffa6388110ff96388110fee6388620ffb5388110fed6588620fee6588620dfe635c620dfd655c620bff8359520bfd8714530dff7548530dff7588530ff97258130bff8359410ffa7158130ff97158130ffa2158130dff7688530dfd855cc10dff7648530fed6548520bfd8399410dfe855cc10ff95348110ffa5348110ffb5348110ff96348110ffb7254130dfe655cc10ff92158130dbd7414c10bf98014c109fd8714c10dee655c810ddc855cc10ded655c810dde855cc10def724c110ddf855cc10ddd865cc10dee635c810ddf865cc10ded635c810def535c810dee535c810ddd855cc10ddd7358c10dbd7458c10def72cc110dbd74d4c10def7254110ddd73d4c109fd8794c10dbd7494c10ddd7394c10dec535c810aff8654c10dbe655d010dbd7498c10dbd7454c10ddd7354c10dbd655d0109fd8798c10ddd655cc10dde655cc10ddd7398c109fd83dc5509fe87985509fc8758550b7d83d45509fe878c5509fc874c550bfb8048550bdf8359630df7719c530f775194530df5711c5309fe87985309fd8798530bdd83985309ff87585309fc8758530ded535c8109fd8794530bdd8394530bef825c5309fc8754961dbf74589519fd83dc9609fc87549609fc874c9609fd83dc5609fe87945609fc8754560bbf84545609fc874c9509ff835cb50b7f8354b509ff874cb509ff835c750b7f83547509fd878c750df5718c750f75518c7509fd83dc950b7d83d4950bfb8048560def72d4110def7258110ded53dc910dee53dc910def53dc910ded63dc910dee63dc910ded65dc910dee65dc9109fd8794e109fd8798e10ded73886209fd8798e20fd93154130f7b5154130fd932541309fe87945309fc8754530bbf84545309fe87145309fd8714530bf98014530bdf8358130fd93258130d7f75d4130bdd83d41309ff8754530f787554130bdf8354130f7b52541309bf845d6519bf845d6219bf845d5219ee871c910fe22188110af98694130de571886209df835d950be980886209ef825cd109ef825d5109bf845d5109ef825d910fe121481109bf845d7109ef825c630 else (if j<2 then 0x3e707a28f091dac3a2071d0de31b4e35886858cb418ba30185d78b5816022aa852989ea131425a448908c410ec20c43e407710e461ae833186030b7c16082a304ef090c119421483e4073e0d8c18f02d9055e098411701f2037e05e809f00f9017a02280228000f7d65d4e10bfd86d4e10efd6558e10efe6598e10bfd8598e10ffa6588110dfd655ce10dfe655ce10fee6348520dfe855ce10bff8359610bfd8399610ff9504c310ff9604c310bff854c310bfd864c310bff864c310dfd855ce10bff854c110dfd655cd10dfe655cd10dfd65dcd10dfe65dcd10bff8059510bff8359510bfd8099510dfd73d4e10bfd854c110ff9604c110dfe535c610dff535c610dfd635c610dfe635c610dfd655c610dfe655c610ff9504c110bfd8399510dfd635cb10dfe635cb10dfd655cb10dfe655cb10bfd80d4f10efd6558f10bfd8098f10efe6598f10bfd85cc310dfd655cf10dfe655cf10bff8059710bff8359710bfd8099710bfd8399710ff96588110bff8654110bfd8598f10ff96054310f7f5354310bff8354310bfd8654310bff8654310bfd83d4310bfd86d4310efd6358310dff535cb10efe6558310bff8558310ff75348710ff56348710ff66348710ff56548710ff66548710ff5654c710ff6654c710bff8358310ff56388510ff66388510ff56588510ff66588510ff7534c510ff5654c510ff6654c510ff7538c510bfd8598d10ff6658c510fed531c910fee531c910fef531c910fed631c910fee631c910fed651c910fee651c910ff5658c510bfd8654110f7d53d4110bfd83d4110bfd86d4110bff8354110efd6358110bff8358110efe6558110ff75388510ff55348510ff65348510ff75348510ff56348510ff66348510ff56548510ff66548510ff55388510ff65388510bff8558110dfd53dc910dfe53dc910dff53dc910dfd63dc910dfe63dc910dfd65dc910dfe65dc910bff8054d10f7f5354110bfd8594d10bfd80d4d10dfd73d4d10dff73d4d10f7d65d4d10bfd86d4d10efd6558d10bfd8098d10efe6598d10bfd8094d10dfd535c910dfe535c910dff535c910dfd635c910dfe635c910dfd655c910dfe655c910f7d5354110fee65dc910bfd85cc110bff864c110bfd864c110fed53dc910fee53dc910fef53dc910fed63dc910fee63dc910fed65dc910ff96054110bfd86d4c10dff7688550dfd7688550dff7388550dff7648550dfd7648550dff7348550ffa2158150ff92158150dfe655c630dfd655c630efd6558c10dfd765c930dfd655cc10dfd769c530dff759c530dff765c530dfd765c530dff755c530dfe755c530dfd755c530dfd751c530efe6598c10bfd8598c10bfd8798530bff8758530bfd8794530bff8754530dff769c530dfe655ce21dfe655c221bfd8399521bfd8099521dfe65dcd21dfd65dcd21df else 0xa0890887194c3e3a0434c44112110e3178ec44086904c324221c61f1d021a652098a484438c3e3b15021a6220890e04587c76231434814112110e71d88810d30d04c52494050471c0e444a818340141160801d178e444a81834014115c7a0a0830400e8a44e386803864112020271c402109b681c400021c70708090436d100f1171c400e0b3187068178e070317c1c04208049058340bc7038440c1307120911882025a109230584200a43e381c04062f81082012817c70386c0c5f208041250249a100100f8e040da08be41281f838a96a8bc7108e0e09d141e16630c0e8aa6a0443280c00e3c54b40901210a043241a05e381c261103004b40e24162209838300454b4218171c6000438e0e21b184038778b100704f8d011c3c0c076570d01184e0c076570c1ac08e11e28682b82e3e0474084f8bc7101e1be383827840af1880d1078bc7410a0ea2e0f8f95c10c1c417178e4114234aa204f05c7c08e110603b05c7c08c1d0603b2b8263e047088401f82e3e0460d85535c5e38a1e098301d95e3404708e2b09c70d40a823cc9898ef315a623cc1d981d2fda5eacbb497272dca59fcb27961f2bba566caac951729865204a0d93d9272e4d54977929b24b248148cf913921ca42448158fe91f2a3cbc76d8e991cae38546e98d911ae634c46928cd1191e313460e8bc9170e2d145938ac114fe293c50689a712a623fc4558869102a1f4c3c8873d0e621c9437a86e90dba1ab434786290c1616dc2cc857b0a7213dc25a84850886104c1e8837d06760be41528275046608540d7817f0256035c038800aff49fd43f997f02fd81fa8bf427e42fc49f81beeb7d82fa39f2dbe3a7c20f799ee2bd9b7ae2f541e933cf37992f27de43bc78789cf0d9e0abc0677caef11dd1bb8276c2ed01d8fbafe75baeacdd403a56746ae82dcec39ae7308e545c9838f4713ae1cdc2038166fd8df09bd5376e6e52dbfdb6ab67e6ca8d861af735e86ba0d675ac2b5526a2cd3f9a61346b68a6d0eda11b40b680acf919e633ab6714cda59a8b330661ecae19353237641ac78d8d831626294c45d86030696048bf357bb2f4c5e56bc297792ea45c88b88d7012de15b92b6a16c3ad665a8ab449678acbe594cb25d6322c31580eafbd5f02bad5706add15b2ab3b5634ac5157e2adb5562aa4153c2a575490a8e55152a24543ca7d14ee29bb5346a6094b0a92e519ca291438a847504ca0153f227d54eea9d5139e27094df49bad365268e4cda98112d2254449fe927d228a3f147348d0d171a29e448e882d0e32181425482e1039a01c3f9c7ddcf8b9eae3cae77b8ec71d2e39c07224e1d9bc036d26c00d549a4933c06600c8718ae30e460fcbf897be2f165d60b7c16e02cee585cae0155729ee52a4a2013f2275a4d5899192cc24fc48788e3915e220e42e483590141fb0)) else (if j<4 then 0x42c1090430db1858210c90131208130a0c0c188c5140a685818802cc612020c0410a8448902102a11810600442a1020220b0c1811068144060680618442a1419029a0e0c0a08183020001f021043420201610472a840c360908241104061c00d183a29348a15630a0b070060a0d818230e84c315452684c2825149a1b630505828802cc6103801a306c50c8003090441a1c0410783003050680c1d8742618a04001861c198a14188c5140a6858303060608c60b060c0682088c5618c928284c34bd169544a30582682a1809025e1420030771c09864a8030250141bc7000440c4301a090254578ec462b0e05011d8a140071d8c160084d87022a2a1561f1d88c58140486280187c763c558d0100c08a0e516869180a6b8f448112140030f8f1563404030225861462f1d8f156340403022a2ac3e3b158902808ec3003178f15634040302262ac3e3b2a05011a2ac5e3b118702808f156531187c781404762b0c01c78ab1a02018112004412a8745e3d1d2b464080504625e874a4ad1904811c394aa1f1d23014d512044a5e8b44a1a568c8240901ca2a4689014d50f8f02268a00a1f1e8e95a320402822810002511287c74a8190201411697a55128695a32080481249400019138f474ad19020141161508b1595c76204d870280940d0640c11c78261b2b82c095176231587156340a02425e8745a22568c82012049a2a5e89434ad19048122868da280c0044e3d1d2b4640805046c5d86c462c558d020140490002007c7a29112a064080504580186c5e3c558d0100c0890030d8bc763c558d0100c08a002208943a2f1d2b46408050458340a01e381c22068404c3450840811030401888019040345e399c703884081103004b410a294512d00821c7070c0d02f1c1c1b141a05e381c22060704c82904f09462d0b950760a8a4814be410a04f042e178f8720e18be432860b08505026102007c703818bf0a0210403452c1003e381c36062f9041f452b07c72887c020207d1442482007c70384c2206009681f452c1003e381c2206009681f452a2a1562b1187c7814048068178e070d818be4100838905f1ca21f20804042124101ce2f1ca213c16107e381c42040f880058508131fb450a8b10170a0801f1c0e1a008462a48840985e386803152410030403c4dc70d0042d0a8a940801f1c0e1103614261a278e071081022060810403852417c7038840811030401848244b1fc3442025ac108480681434010b71c1d15201a0501f1c0e1a008462a494621c72d4560630278e1a0085a2a301403c7038440d1009868928c40b4020440c6e381c12900d8a8d0800c83c7020702640401dc72d1043e8841900d028238e070d0042315268c5a010438e0e1b8e5209e130b462d0e1ca2a478f4480a6a8702243891a1f1e89014d51604487022c56230f8e1a40 else (if j<5 then 0xb44070404200241820483020805840c0681430904602182000030c160ec1060f0600a0a0d148613088a1308260181061a00c0830980604180d8a000c36448261840402e0c1830340d02c1850402c8818300a0d0f0c010d060e0d02d0986170c1a00a0840400c8819170c1a0088450de1a021314360483004342838340383080d0d02a0c206c09060086850402e0c183034038308430de1a021314181a07e1840684414184822040c101105860c0880c30d00504190c10d0050418013040048a202016440c180d0286010d040b0700508206802820c1e0c00870604184381e1a04284010010c8a1308060e81070307068030214881a00c08481830030210260e008684058340218281a4481080e0880c341832041c14200581080001228840008822048c060a0f0d006042c1810e118a306120c0c18107068881a2204440d181a81060e0d04080861834606820d06d8a186d88810d081b0d30c30d86994186d88810d081a0d841b0d30c3440244c30680302143786083786008684068201786101d03c30680228341444c3408507c170c1a008a0c41e1a0424181833142091460c1c18183021228c183830306058b0608384628c184081160b86810a1c043142246143811230603070448c20281a1123081c08918305820224610060c089184c3004341838078681081a0406c8b86170c1a00a0840400c88861006080b0c0834340bc30843c305860d0043c303860d00430886d8a186c22040c1c1101860d0882830d844081820220b0c181101861bc340830d86987061034080d9170c286c8904c309860d00430d06e0cc51036c48320434286c34c383081b0d32a0c206d89064086850d06e0c19151b08c320602302c02850680c1d87826189068300346103808420468c28701c11a3080c088360420442484810811090505229350688630c52494148a4d41a20706068070610100b4241842182c140d41a230f04c3120d228448c202c1a03041118a31141a13008800928c10348b460d10450cd1820700e8c410d0ac50410e8c1a208cc581040c4183b0f04c30c1000c141a830461c098624360f08260f08360e08260e080060340a1830061030220f0c221241060c0283430402c20600c84182016420c8a0a04a151b038461f0c48248a8546c0e1187c3100808005054614860c4151840e03c23461020110420a04282c060e42a370f04c310110905450400e8644148a0b048210a8dc3c130c4830120822a151b8782618904e060608c3c130c3860028506c0c1187826189228301381818230f04c3120b068068c207023460c1a1105861109040c06a160608c3c130c40240245c28400608c38130c502089430ca28281070640a6830402c2060340a180d8a000c100001860b076083078300505068a928184c3821208615630ac5830506060843242100 else 0x2c10102c1a020c86)))
def g127H8 (_ : Nat) : Nat := 0x85011b2bca0e0003332491e3e51bf117c5d8211c88000000e2061f4000c9eb4f800000000000000000000000000001c52e2700038f4000759000000000124a9a38000000000000087cc19a0d00029fc51de96a882a6340b514b384b2fcd513523418e8000812000000302214000034d0466b210000000000000000000185800045288d0000000b5c0000594ea0ed010c2cc8ebf83cd16c10e0000002d600004780005208000000f18d8540000002d0800243b545b270001d4200081c800000000055580012bc000fa30000000267b2e1a640000000000000000c620002d9119a02d00000009580000005d9cd480000005063c40cb172442720a3676e9d80026cd76dd400aba8e506373a0003f45055000000304a00065f20849774aac0200004a94b5467400348908a144bcdf98367e204791452488c962443a0b13a824ec2cb80e24b3bd61dee71c7bb4a29b299e0c954212bc807d5664ab2f6573a26e11f1b410bba9205708800176500061e80016280003acfc8fac70007918000000e4d9024a668900005ebc001c6eb079166d07aa39b428694c3857e9b712680261035d44e72786506601d8046a01bf0cd179737cc200039a486c0000000002b5400000048ac00163c0b08002d100000000002b892c6726ca98ccb42f000000386e00011750fc94585a69d79580014b6061b10e774000409c6ac001a2a20be0f8000000339887b87091500068c80018c8805800341cbb6303423c8e2c24000000174e000000626b103a66d5680008c00000000002877e757267b14001c52a5382a190d45f0000000000000000085a0042932580000000000820993ef73c53000425c0000000549330000000135a2dc168050480800020400806030000800020001c0208000280a07000000a02030100000030082001008000019008080406000280800010100602008080200018000e020100402000700006010080414020280004060000c0400010040001000000200
def g127D9 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xf1fd83f447d50f731e903c9477d0ed71d583a347330e3f1c2837c46e50d971ad034c46870cef19a832946410c63187030645f70bbf17382db45a10b1315d82b0454f0a7714a028a44ff09d3135026344b1093b122823a445d088b10c020c440307e70f801e743bf07570e581c0436906a30cf01944315060f0bd817142d905930ad014d428704f309a012a4241045b086810141e903a306f00d3419502ff05b00aa413f025f047808140f701bf033005f40ad013b022803b406700ab0118019401d001f0000ff8e2987fe614c3feb0a61ff94530ffaa2987fc514c3ff10a61ff48530ffee4a87ff504c3fea8261ff99620ffacb107fe63883ff32a41ff59520ffcc6907fd604c3feb12a1ff4c950ffee2a87fc71543ff30aa1ff58550ffc62a87fd31543feb8a61ff48550ffac0a87fe658c3feb2c61ffdc930ffae4987ff714c3ff38a61ff88550ffac6887ff53443ff29a21ff54d10ffac0887ff50443fea8221ffcc110ffac6907fe65043feb2821ff98c10ffac6087ff53043ff29821ff54c10ff8a6087fd30443ff32e21ff59710ffcc7887fd63c43ffa9e21ff58310ffea1887fd50c43ff31a21ff4c310ffccb087fd65843ff31c21ff58e10ffea7087fe53843ff32a21ff59510ffe61887fe21583ff28ac1ff48560ff8e2b07fd62547ffb8ac1ff4c960ffaa4b07ff72583fea8ac1ff99621ffc63a87fe21d43fe90ea1ff59521ffac4987fe65487fe996a1ff54961fea63887ed21482feb8c217f5db10bfaeb887f521c42febaa437f5cf10fecc2a8ff561546ffb82a37f5ce10bfae428dfd70146febac217f5da10bfaed10dfd75886febb2437fdd921bfae710dfd72c42feb84437fdd521bfae728dfd75946febb4a37fdc161ff440887f920442febb0217f5d410fda64905ff72586feb98217fdcd61bfeeab0dfd70986feb94c37f5ce61bfaeb30efd62586ffbb2217f5d910bfeea885fd75442ffb92a37fdcd10bfae6887bf74547fa90a21fd58651bfae528dff72443f7b92217f5c910fd8e4887f631443fa98a21fd88510bfae128ff9508c3fcb04617f5c630bfae6905fd73d42feb96a17f5d630bfaed185fd71142feb98a17f5d850ff2c0a877d52d43fd302a17f5db50efaa3a877d51543bfa8aa17f5da50bfee2a85fd75943bea92a1dfd4950bfee4a85fd73942ffb9aa17f5d950bfeeca87f960942feb8ca17f5c750bfee690dff70486febacc17f5d520bfaec907ee21882feb8c417f5ce60bfae7105fd71982ffbaac17f5d620bfaed105fd710c3fca8261bf99560bfae7185ff714c37eb0ac17fdc560bfee4985ff72583fd30261fe58130ff4a0985ff735837eb12c1f6cc230b7ee8a8ded72042deba0617b5c830bbae6085f6710c2ef398216f5d250eeea328d7d75042bf3a8213f5d810beae2184fd76942f7b92216f5d010 else 0x11c6c13146844551a0b1e04ac51b1ac71582811c3c386929131c6e087f18a020f0e014a44c713821cc62c731458071c56091880d21c58308c71b421fc6012c3c406f144f1c3a105718a0e0c0f1b1350c70a8415c62e2a131c6c690457180890d08034ac71f4411158228440468231c26560880410c503c71f11158224044f1c3a105718300891a01c70a8415c610022443140f1c6c6904571808ac510c71b134415c60302286805171c3d2857180c08a0510c7214ac61b14431c597c80380c5608a21100cc71b134a15c624446805140f1c3e56089c52010c7031395c65a412804587c0c331c3a57196904b1b0ec52010c71395c65a412c680514220f1c57183c08a0d21c5831cc608c7131a412c6807140c5718431c3808a131c0cc70e15821c0f157c8038431c560890d21c71f0e11158220071c4c571884087111a010321c70e958224104468042d171c3a5608a11011a084583c70f9582288514420e231c6c4d285718b21c508831b1a4115c6c7022c131470400f1f184c6904a0d0308114a44c71b8124484c13171c56186a04910c715c60e021834147f1c3844560881a0110c70f4a28158227171e09044c5c71f1a4186021c3c04431c284c57188408a140d0800034ac71f1344860230262b1c6c690457180890210c70e9582180433144f1c3a180881a014510c70f4a8602242b14686f1c10571808904030221c5c70e84c62408584c150f1c3e5608909031bc71315c60a0e04022c340c200a2a131c73184c6904c01161f0510c70f95c65a412c20262b1c731a144c6904a0d03088ac71f841115822820271c7e284456088210c1b50c70a138415c62808503c85431c2a131890921101bc5c70e138415c62c44683c0440871c2a5608a281cc7100f15821c2b144c386f1c57188252a212b231dc5830e20c61a8134571408071c509290ac5130e1b0415c6022c542b144c387f1c10089c51501c602c718042b14571c100b1880ac51502c601c71c94a8846c4c3857180890301c510c7130e1fc6248714540b18071c70310c51502c601c7202440540b18071c71a1b0ac515c70402c625143c371c6c4c38571808a111cc582c781185f14540b18051c790251ed23a747088d85199230b45c88b051432253444087b50df219342c084c507f20df41788285043206b408880b500b1fe33f807e54fb91f473e387bc4f671e9f3cf87904f031dcf3b2075a4ea11d1b39e07314e4b1c5f38687034ded1bab36e86ce4d891ae3356069f4d251a1733e06734cd3196b32886454c7318bb31206184c1d18032f905e84bbf17632e805c94b7d16d72d505a04b2d162f2c0857c4ae715a32ad854e4a8314e329785264a3d1457286850349f713c727304df49ad132725e84b1494d126f249048848ff11d3235846148b1113f223843d4867109f20e0415481b100) else (if j<3 then 0x281350c403b1d15121a560a04a431021c74a86958281251614403b1c11110e1a560a04c0f03084a4443c7869582812d1614240c2011110f1e1a560a04d454a85100ec7441686951343828139150c6c4f1d10540a0490cc74484461686434582812c2c210f1d121114591a1a0a04c43830ec7454616861344828130350e0c3b1d185a1929160a04c0e458510c744461686438281310f1d104c5517180a04945c74413154302812115104c550f1f180a0491b430e8345461686011a44c7828139150f1d1c4c55100a0490c0d448445431ac79582812c2c210d1211146b1e560a04b43830e45441ac795828128350e0c39286b1e560a04a4585100e44431ac79582812c2129110c6b1e560a0491b0c44844616861a4345c78281346c2c210d121114591a186b1e0a04e4a43c7131544c60281260f1c82105906145480510c71b82211a0c6d12131c4e145481a05c7100f1b18a31e1c86107c82084030a01c720c685100f13210e0c3f1d06048058842854b05c713411c81101521271d04807e1458403c5490516461f86c71302102128331d12110d0a09161a04ac709831b12171c821059060c548851b134484c75a41831528482c210d1211171c6a050a0a18d83c78716812068450f21828430483112131c6a050d0a091618c09c7418120168315231e1c86107c820840309014a44c71f1395c6206f171c4455690471b04c51a15c6c701204514431c3e57180480d051f13c70e95c60124484f171c04551870d0513c70e95861a812434200d29131c7c4e571804b10c7214a1fc6188516220f1c704f1880d21c583c720081355c61a8130503420000d29131c68540a04c120410c503c716551146012c1314400f1c6d087f1804a0d050e08431a15c70281283d14412b1c68540a04920451095c70f4a8601243414831c3a561804813451095c70f4a861a81286c42571c3d2a186a0490d08034ac720441c0124484413171c55180481cc516c715428601206c331c3a56186a0480221c5c70e441fc601244714400f1c384f180490c02450883c70f4a1fc6012c20262b1c82144d57186a04bc5c71f1381461b171c7c7206691870f45104a1502c601c724331438540b18071c84a44c7151f821870271c5a2845186a049140d0800034ac5441501c602c734443c40871c2883186a04a1085c70e20c61a812020262a171c6d087f1804a1209c7168a114601203c0884431c29107f1804a10c70e8a1fc6011c8041571c3c291a6a049111a45100f9582c781244419144c403e560b1e04a050d1b0e9582c7812018704c303a560b1e0491c21c50883c7165511461a8130340c206929106e560b1e04b0d08031b4a44061c139582c78134711c30384f186a0481bc51a01c715461c431c85287f1861221c50883c716551146012c73146844560b1e04806c51bc713828 else 0x1a430e19c7040214841b28010e0f1e1c286d14860a10b004383c7872013450f2182843000131c6c85220a1080020c721130e828420031e1c1024086d410e0a10b8583c787201641841526160c6c4f1d690610549411f20160cc70e1520031e1c10245506044c39410e1008e0003044181132143c78415023030351211150f1c4d06061a08c0b0843448445c71341818682310e0c3915131c4d06061a08b11c74484454313418195282c44210f1d1211144d060654c43830ec7451144134181952d0c3c2906044d40871e105408c1c81681082c7211d06048058871c3854801200cc70e1318680c331c386c6031b8382c7211859187e184c420b1c8490321c70e1b1480871c384c50fc50e43c71b46200013828432146d12104e0f1c548050341138110c72115022b1e5604843d0c2a0880bc7951341810e480a82290c3b1d047c8058521054ac522c7411f201615828428050c3b1c8052104c80fc5430e19c713001b82842e14821059060f1c5481b0d430e834616861a4a45c78281386c3914421511185a18690f1e0a04e1b084a43461686011a44c7828134246d14421421110c591a186b1e0a04f43441b1345c71581022515106c4d0f1c540a04945441b1343c715810225290c6c044f1d10540a04a1143830ec74a134181952834331d1029150e1a560a04b0b0d030843c7440a4586958))
def g127H9 (j : Nat) : Nat := (if j<1 then 0x9b48000000000080140254cc88580000000117f8fda358cfa43848ba112e55041cb29e88bd73d0000000833c0c900022d80001c6e0000000d55809b0003c497d0b0ec9150000000000000000000002c83a4587020003c80003800081d80000003958e32ace9000303c00000000000000a2b00000001575c0127180003c3f4c157042417d443050046722f7839dd1cd80000acd0000c860002401e4df03944a66d90001432414800020ec3400003330a441e9658ea8db4187eff410a4a0d464add04f5f790000f5a00000002e11f3a000000000000009c3b0b81cd3cb0904f90b9138000cc040000000000000000000000000001557234806b54a8a840dc003db18e22b22ee82a0cd53170a36170000306200000003294000d3d5038a395d7c0003f71000374543a04b9a29ab332c740001d500000003c09339c0008d4c000314f44c000000022a000000014a2157710885ab8203410000503e4680002843937748c00000003388152cb8609af8611214be20a351429470000766d530000b59a0bea3dc000bb40000a3b74df845c00064ff2af0002f1b00000000001535000349500009000303c8dec180000000ac70002b4172b400060b64ea000049e74780000001d84352c75baa404f1e0980002b90059f16cc8782cbd64e23a49332fc000000142f284695441df98100028f90000000f12b89cf03000022140000000000c05d8fe00004980001adc00000000003565cdb7d2fa1be2140000000c94c0009b47d270000f6c43ffd25241c0eee1e5489d5b9f1f3c0fc978103c6043700006430000187b746e44f2e0a56934cc069e8b000201cc4e090d9043ceb00023368000b8033120d084cc00080b8000236882200028d9b46956bab7ec880000000b31b4b17c280000000c18c0f9436aadf50295220abe29c00000014e05c7287bcc2ed4d708d2cb2445c7f00028c33df3b570b3e1241afa287cb240005144000d60c000000000031c4b1e00cd971ea381120000f810000000551400034acc34ca7fd6d934f86c201d06600030449169cb60003835ba8000021f4000b2916da1d9e8a900000002284000640c0008bb7d78000054a00000000000000000400000000050440000c0200002000020040000404008040040000c03004020240201c0000001000000080401c070080409806000010000004c070040001c00018000340100407008050040001c01024000000200805008030040200c0600800050000000200802010010000200000008000000501c070380000c0f0040003401018010000400c0400c140040c014120002100c000140900c03034020300100c0400001004010000100404004010340100c22028000080000c02000010280301006010010040000c000000700004000090200003c030140201c0800c02060020000f02004 else 0x3b5195cc000111654252440000003b0d0001c190001f2355da11581f90d485780000003906000000084d8000000303a00000002c9c000c3ec0005bd800083bf2b810a486795d34c13194000e121295657f540e32077543d0aaeb5a70b70003526022bcce038d8cc0054299002bcf031362f91207737484b4c5b5054b34bf597d6250000006f41e4107d510000475315b2a2cce185e652480b58d14275b280009589c570000000fc1ee1520c0a7f307552883c84c2f480000960800041a582c0000eef0000c28320a760703401251a800003f3d55b5ff831358696f15df69863ced4e3b4ef82b54c53b0001308000000000000000000000e4760ae000000000000000000000000297200036830000efb0000000a35e2c4000000034e4000f020c47a1cc000c0acf52e1720ded1750af484000001d38f80983cf600012920000000942800025188551dd992e29e491b7a4f2f714e847a28dd4e40003a9b0000ebd0de80000000000c2f40005a1411cb27f10fa43a6abfcfc93c0058000831f2326a5274e0002d4f000000064c40000003021458327a000080300038060001cb50000d67a4b369cf5efc84b009e8100016eaa46047800000000003e170000000f0de901000000000014b452a954304c816cc39a12dcc01968eb0251f64880007a5c000000000000000004da40000001c240000000d24801f4c808990000000db04d5cedaeb58d5640004ad167e9d640000000c4f3cc4e61cdc946d51f1715f5e74cd6190000ba750cb000117e5bf800014c389d748ca80d047890187f90984f9b3cd34400000034d52ca40005afdd340002a4fdce64700000ade0000c8f758eb1a956ed7ab60389632f19140000000)
def g127D10 (_ : Nat) : Nat := 0x1840cb0d458e54101281848a6a395040480610fc58e54101201848b1c0a03e541120c2458e0499f0c0890a0c5450c0498e371cac60808e06280c58e10a822018a8e04d932b18202282108b1c09336563030458442062838e38a822428309163862b18101282018a0e3892a0880624085211c51504483131c09b2628ac60a08b06482138b1ca863404a06122c72a1808e10145071c49b3f18094110828a0e38e4118d012c22105141c73638fc60258312082908e290463404b0624282211cd8a3f180960c481501484714b0a9414221026c98e2b181c7046673c6b7ded956da0b31e3dc287c6e5dacb145829d51f1f233e5307c8a60b4003fd10ff843ff10ff483fe20ff0c3fd30ff8c3fc50ff543fc10ffd43fd60ff983fd21ff887fc51ff547fe51ff587fe61ff58bfe50
def g127H10 (_ : Nat) : Nat := 0x72454fc2a792c0000cbc000a28800105840e0000003c1f0ca0338000cc6e39000485e9a606465ae4d6387036de0cad000000000021688454623acaaae43434e50fa12a99c204e6692b0aae00000000017a1069363f32fc46a96e1d1e04000b1582c80beefff5a76a0925c3a00023080000009e11e100031b4e6fb4694f8001c8e42abceb8af45dbc480000000000005345020809d3fe0710280119e95307c42034a62a93fc1b8ba7265358000ed788e7f500019d1000000367704100000035382a60b3c3780001e043be387f1529b9691ac311800000000037b800055b7f5d8cc00018a5f100000001a68001269ca85bd038c8b80a5d3b0001554ca283c811c55b2b38169761dbe0000004a8512e000000000000000066ab0f7164000e29e36d4309bf700d61f173fbe8300ac733acd8b4d79ca7c5e5bb6439aa96fe883e2d0a3457412d6263678360959bec2a511343068f627e13162e963238b90bdd9dd56b0b980254428371b0eb45245c5119d0e9dad1552642ea7bd60f4c31b925d5735a696ba75aeb453ee3e51b9f418caef3ba993e983c28c2d83e5d6aa8c0004c9e14968375619b68ece72d5ec7ce48000313a0000004f2f92408b0001c0e54080c7523ec8b58e68c49fe4748be3b3d211e2978b47542400817ea83d22421bc7040700000037c65a1e8d000336600061b9af919f871c12e997c7e000cda0000e7200000070cc000fa282048f2806f7e46838c889a06c036cc4c80a8c3e3dc2f4502eccb3e80016f7620f47f92d448280ad18a7b02b04e14a0000001c5fb24000141680a0af0001026000b13000000000000020180002dc88bc95876ac08913e1cf433c74c1ae9c2f6200000059ea904b11821510d0dc6e02575c9c0000004db23740005b00000000000000000000002000002800020001472030d80c680d0304404040484802030201402011000824090180000000480402010081400005000c000001800700c1002006000201400000005402010498814030008050030501002250000402060d81400160582422090181008020084c1c03038101200070084608000100000
def g127D11 (_ : Nat) : Nat := 0xa38c1ff
def g127H11 (_ : Nat) : Nat := 0x7306e81042a385300000218520000000007002e2d9216da0e743df675000cd30a001c84340081620f242d144105a8ec2d7439cc005ac000012ff2f00d053275723aa5a8535800012401c1080
def g127L : Nat → Packing
  | 6 => (31,5,6,0,0,8,0,g127D6)
  | 7 => (208,4,6,0,0,12,0,g127D7)
  | 8 => (389,3,6,0,0,15,0,g127D8)
  | 9 => (228,2,6,0,0,15,0,g127D9)
  | 10 => (23,1,6,0,0,11,0,g127D10)
  | 11 => (1,0,6,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 11 43 6 10 5 1 g127H7
  | 8 => lookupWord 85 383 9 13 8 1 g127H8
  | 9 => lookupWord 185 809 10 14 9 1 g127H9
  | 10 => lookupWord 106 401 9 13 8 1 g127H10
  | 11 => lookupWord 13 53 6 10 5 1 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 31=true := g127P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_15 : block g127 7 15 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_111 : block g127 7 111 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_207 : block g127 7 207 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 208=true := (@block_merge g127 7 0 111 97 (@block_merge g127 7 0 15 96 g127P7_0 g127P7_15) (@block_merge g127 7 111 96 1 g127P7_111 g127P7_207))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_16 : block g127 8 16 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_112 : block g127 8 112 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_123 : block g127 8 123 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_219 : block g127 8 219 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_315 : block g127 8 315 74=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 389=true := (@block_merge g127 8 0 123 266 (@block_merge g127 8 0 16 107 g127P8_0 (@block_merge g127 8 16 96 11 g127P8_16 g127P8_112)) (@block_merge g127 8 123 96 170 g127P8_123 (@block_merge g127 8 219 96 74 g127P8_219 g127P8_315)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_17 : block g127 9 17 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_113 : block g127 9 113 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_136 : block g127 9 136 92=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 228=true := (@block_merge g127 9 0 113 115 (@block_merge g127 9 0 17 96 g127P9_0 g127P9_17) (@block_merge g127 9 113 23 92 g127P9_113 g127P9_136))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 23=true := g127P10_0
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
  · exact (rfl : block g127 5 0 0 = true)
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=53542913) (before_sound K191 V191) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K191 12 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V191 low127 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 eightInputs.toFinset := by
  rw [show graph = graphGoal 255 by decide +kernel]
  exact cut_root (u:=true) (m:=255) (cap:=12) (before_sound K127 V127) (128,0,127,0,12) (by decide +kernel) (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0xff800fffffc0000000000000000ffe003fffff,0x91122244488911222444889112224448891122),(0x7ff001ffc00000000000007ff001ffc007ff,0x24248490921242484909212424849092124248),(0x7ffffe0000000000000000000001fffff800,0x4ac9592b2564ac9592b2564ac9592b2564ac95),(0xff80000000000000ffe003ff800ffe00000000,0xc8190320640c8190320640c8190320640c819),(0x3ff800001ffc007ff00000000000,0x380700e01c0380700e01c0380700e01c03807),(0x7ff001fffff80000000000000,0x700e01c0380700e01c0380700e01c0380700e0),(0x7ffffe0000000000000000000,0x83706e0dc1b83706e0dc1b83706e0dc1b83706),(0x3ff8000000000000000000000000,0xfc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8),(0x0,0x0)]
def mo255C : List ColumnInfo := [(1,0,254,0,10),(2,0,253,0,10),(128,0,127,0,12),(0,64,151,40,9),(64,0,191,0,11),(34,16,77,128,5),(7,0,248,0,7),(8,1,240,6,6),(16,128,111,0,10),(2,16,77,160,6),(1,8,150,96,6),(10,0,245,0,6),(4,0,251,0,11),(1,4,248,2,8),(8,0,247,0,10),(8,64,151,32,8),(0,128,111,16,11),(32,0,223,0,10),(0,4,248,3,9),(40,64,151,0,7),(32,64,151,8,8),(64,160,7,24,6),(72,160,7,16,5),(3,4,248,0,7),(65,8,150,32,5),(6,0,249,0,8),(9,0,246,0,7),(128,2,104,21,7),(129,2,104,20,6),(0,160,7,88,7),(32,8,150,65,6),(64,8,150,33,6),(0,8,150,97,7),(0,16,77,162,7),(2,4,248,1,8),(18,128,109,0,7),(136,32,7,80,6),(32,16,77,130,6),(104,0,151,0,7),(9,64,150,32,5),(96,8,150,1,5),(48,128,79,0,7),(145,2,104,4,5),(1,130,104,20,6),(144,2,104,5,6),(97,8,150,0,4),(17,128,110,0,6),(0,130,104,21,7),(148,2,104,1,5),(33,8,150,64,5),(152,0,103,0,6),(24,160,7,64,5),(2,1,240,12,6),(208,0,47,0,7),(0,1,240,14,7),(80,160,7,8,5),(10,1,240,4,5),(144,32,7,72,6),(12,0,243,0,7),(88,160,7,0,4),(66,0,189,0,7),(8,128,103,16,7),(32,128,79,16,8),(2,128,109,16,8),(132,2,104,17,6),(133,2,104,16,5),(72,0,183,0,8),(41,64,150,0,4),(96,0,159,0,8),(178,0,77,0,4),(4,130,104,17,6),(12,1,240,2,5),(19,132,104,0,4),(65,0,190,0,7),(56,192,7,0,4),(36,0,219,0,7),(149,2,104,0,4),(5,0,250,0,8),(8,160,7,80,6),(14,1,240,0,4),(4,1,240,10,6),(6,1,240,8,5),(15,0,240,0,4),(68,0,187,0,8),(34,0,221,0,6),(145,4,104,2,5),(12,64,147,32,5),(148,0,107,0,7),(5,130,104,16,5),(9,4,240,2,5)]
def mo255A : List (List Nat) := [[],[48,81,98]]
def mo255D8 (_ : Nat) : Nat := 0x584583f82e01e0014e10e0fe0b8078005806f820050fa23e0901c3e88f824070fe0801ea21018400a0096888061002fa20027e0a018500be88009f8280615c0dc11c49c31845805c39c026209f82113a810d453e0aa04361370e71270c6116019880152005b018e2320046139886170d60d613e0ac06c005a90c06e82d0ff84d0ed0df8cd0026764e69c136a6a4ce99130a5e4b69612aa5249e93124a464869011ea3a46e8d118a2e4568a112a2243e8710c9f83ae708d69982fa588a09201ce3485e88a0de1681c8006fd1b668c9150110dfa36ad1922a0221bf4595a3245404437e8b1b4648a80887f915350d2150110dfa2a6d1922a0221ff054d4348520443fe0b1aa690a40887f895350c8250110fec2caa9a4290221fb85956448520443f70b2ac690a40887fa1645512148110ff42c8a1a4290221fe85514348520442ff0db2a890a40885fe1b650d2148110bfc36aa1a4290221e976116558d530432de4c148cbaa2985fe1b654d2148110fbc2eab2a4290221bf8595a2245404433f8b295298a80887de17558d2148110dfc2c6d1122a02219fc58ca94c540443d2ec12cab1aa6087de17554d2148110dfc2a6d1122a02219fc2a5534c540443f705b2a690a4088725d966556560c10f49acab1aa6c1021be850da2245404433f0cab4448a808867e1966889150110df2346a1922a0221be46d1a3245404433e8cab4648a808867d19668c9150110c379305232ea8a618e76919320c8154316ed332641902a861bc982919754560a37968c3b26402a386f260a461d62547d0eb2b08b1aa608513db52a5845c430
def mo255D9 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x5360810afb6994360810afb6954360810eeb5914360810ef354d4360810eeb5915460810af76995460c10ee76515460c10ee75915460c10cef6a58458c10e6f5d58458c10eaf5958458c10e775d58358c10eb75958358c10abf6a09654c10cef6a58454c10cef6598454c10eaf2598454c10e6f5d58454c10cef6616450c10ee768d8454c10cf76598354c10eb72598354c10e775d58354c10ed75958354c10f975956354c10ee76116354c108ff6a58414c10cef6518414c10cef6a58414c10cfe6119014c10cef6598450c10cef6558450c10ecf5958454c10ded50c91609408ff68c9854940cdf6199520540cbf65985205409ef6919320540cf76199320540cf76159320540de76919320540cbf6598320540cdf6558320540daf6594320540dcf6554320540bf668c8154140cfb6199220540cfb6159220540cfb60d9220540deb50d92205408ff68c98585408ff68c9854540eeb5514360810dee50d90145408ff2a5854c540bfc28582541409fe2a53254140bee6909154140bbe6988154140de764d43205408ff6909854961c7f2618758951b6f2918758951c7f61d93201518ff69098549608ff690984c9608ff6909854560c7f2619754560b6f2919754560c7f26171545608ff690984c950c7f261754c950cfd60c91609408ff6a48320550abf6988320550aef6908320550cf764c8320550afd68483205508ff6909858550c7f69c984c5508ff690984c550cfd684984c550c7f261714c550bee6809150d40cfd6189160940cfd6149160940af728d8620550f765c53154130fe5591434c510fe5551434c510fe654d4350110fea50c8250110cef6614314540dfc6549150110bfc68c9150110fec50c9150110fec50d3150110ef66113154130ff44c5604c110ff44c5504c110ff85952148110ff85912148110ff85512148110ff858d2148110ff854d2148110ff850d2148110cef6599561010aef6a56561010eaf6596561010fec50d2150110bfa6888154140bee6913154140fe650d3154140afd28592611308ff69098585308ff6909854530c7f2619754530b6f29197545308ff2a58454530c7f26171545308ff6a58414530dfc6589150110f765d53254130cfe2a58454130bf668c9154130cef6518414530cfe6119014530a6f2918760951fcc5454154140bf8688904c510afa6805360810af96845360810aeb6905360810b6d2918758551abb6985360810a6f2918760151a6f2918720151acf6909361410a9f6989361410fd45453154130c6f2a5845c430cf660d9014c10bf468c9150110ab76989560c108ef6a58414c10ae76909560c10f785d52148110cdd6159114c10ced6119114c10cde6159014c10fe450d3150110bec690904c510b4f29197545509fc2a53150110bf86889150110cee6119014c10e6d685845c430 else (if j<2 then 0xebf5956460910ebf5956360910aff6995460910aff6995360910aff6994360910aff6954360910cff6598454c10fee5954150110fee5954350110ffc5953148110f7e5d56548110ffc5952150110ffc5953150110ffa5948250110ffc5949150110eef6556561010eef5958455010f7d5d56548510f7d595714c510ff9594824c510f7b5d56548520e7f5d56560910e7f595835c510dfb5959220540cff594984c540efb5955460810fee58d4150110fee58d4350110ffc58d3148110f7e5d56348110ffc58d2150110ffc58d3150110ffa58c8250110ffc58c9150110eef6958458c10eef5518458c10f7d5d56348510f7d58d714c510ff958c824c510f7b5d56348520e7f5d56360910e7f60d635c510dfb58d9220540cff58c984c540efb5516360810ef758d5360810ef754d4360810eef5915460810eef5914360810eef5514360810edf5955360810ebf5956460810ebf5956360810aff6995460810aff6995360810e7f5d56560810aff6994360810e7f5d56360810aff6985360810aff6954360810aff6905360810efb5949261110efb2898458d10fee54d4150110ffc54d3148110f7e5d55348110ffc54d2150110ffa54c8250110ffc54c9150110eef6958454c10eef5518454c10f7d5d55348510f5f54d7554110f9f2995354110f3f595635c510b7f699535c510e7f5d55360810dbf2999550d10d7f655754c1109ff2a54354110efb5515360810efb6a15320910efb6156520910efb6156320910efb6155320910efb5958420910efb6116320910efb6115320910efb5958320910efb60d6320910efb60d5320910fbe2995348110fbe2995350110feb5915420910feb5914320910feb5514320910fbd2995348510fbb5956420910fbb5956320910bfb6995420910bfb6995320910f7b5d56520910bfb6994320910f7b5d56320910ebf2995360810bfb6954320910f3f299535c510fbb2995320910ebf2598454c10dfd5949160940dfd58c9160940fee54d4350110bfe6809550d10bbf6989550d10bdf2959650d10df76959320540ffc54d3150110cef6599361010cef6559361010e775d56560c10ed76556560c10eaf5958459010cef6598455010eb76596560c10af76a56560c10cf76559460c10eb72999560c10e776557560c10cf76599560c10eb75956460c10af76989560c10af76909560c10e776597560c10ee76516460c10af76a55460c10af76a56460c10cef6615450c10cf76598350c10cf76558350c10ee75918350c10ee75518350c10cf76615350c10ee76115350c10aef6905360810afe6805360810e7b5d56560810ebb5956460810afb6995460810e6f5d56561010e7b5d56360810ebb5956360810afb6995360810ebb2995360810e7b5d55360810edb5955360810ef358d5360810afb6985360810afb690 else 0x454c8a3913b225e448c88b910b21fe43cc87390db219e430c85b90ab213e424c843907b20de418c82b904b207e40cc813901b201e400c7fb8feb1fbe3f4c7e38fbb1f5e3e8c7cb8f8b1efe3dcc7b38f5b1e9e3d0c79b8f2b1e3e3c4c7838efb1dde3b8c76b8ecb1d7e3acc7538e9b1d1e3a0c73b8e6b1cbe394c7238e3b1c5e388c70b8e0b1bfe37cc6f38ddb1b9e370c6db8dab1b3e364c6c38d7b1ade358c6ab8d4b1a7e34cc6938d1b1a1e340c67b8ceb19be334c6638cbb195e328c64b8c8b18fe31cc6338c5b189e310c61b8c2b183e304c6038bfb17de2f8c5eb8bcb177e2ecc5d38b9b171e2e0c5bb8b6b16be2d4c5a38b3b165e2c8c58b8b0b15fe2bcc5738aaf146a26ec49588b110f21ffc3b7869d0c1a159c24a83ef063a0a8c0e880ff0109ffd3f9c7e50fafdf3bbe037b1ef4f1e643c4977ecee35d9d3af274fce881ce1397a7238e2cdc2ab80d6f5edd71b79b6ab6cdcd815ac8b5286968d1dda1d33f266fcccd9971b285644ec77d8c0b118615ec0ed7eeaf7f5e16bb39748ae285b7eb58568cacc65912b05559f2ad554c2a7b54b7292651bca1d541127e54f669d5538126d04d26990130725d14afc9481266a48548a690011d6a365463a8afd13ba23a43e486d50c1a15c426a840d068a09440ae7fb8fc81f323da87a04f1c9ddb3aa273cce4a9c3737706d68d681a8834126704cc2191b317a6150c0097cf2f245dd8ba796fc2d9459dcb2295f22b8055e0a9294c728e850589dc1365260e4afc930921923b846508ab912521a441a47ef8f761e043a387128da61ae834b06720c9118a830305cc0b5015e42a2450a89ac12b223c0454081e0f6a1d0437186380bb4161c28f04b5088210101bd0311052408fc0eb018e027603cc03f8000ff658d5348110ff654d4348110fde5955348110fde5955350110fdd5955348510fbe5956448110fbd5956448510fbe5956348110fbe5956350110fbd5956348510fbb5956448520fbb5956348520fee5915448110fee5914348110fee5514348110bfe6995448110bfe6994348110bfe6954348110ef76116354c10df75959320540df76999320540df758d9320540bfe6908158130f7e5d52154130f7e5d5504c120f7e5d5504c110bfe6908154130ef75955460c10ef76595460c10ef75518358c10ef76555460c10ef75518354c10fed5915448510feb5915448520fed5914348510feb5914348520fed5514348510feb5514348520cff2a58458930cff2a58458530bfd6995448510bfb6995448520bfd6994348510bfb6994348520bfd6954348510ebf5958458d10edf5958454c10ebf5958458c10cff6199420530cff6159420530cff690984c550def5519420530d7f2619754530bfe6995348110bfe6995350110eef5915460910eef5914360910eef5514360910bfd699534851)) else (if j<4 then 0x23c148181a0db46100ac8982a011e080900c31c039408110006033f046388a60dd0384700100cfc169022783740e11c004284a280cfc102250263a8890a048982ad11e08c700ec1ba3308e002fc141301985c1a8017110508c27e11c400807f85fc602b07ba041f70030026130660330b82a181583d4260abc478251c85fc6013e005a034080710758880c3782c1e0cc5118115c1391e10e3a4082181a0db4612e09c270871c08606c81d184690073e088a60dd0263b08e00260040e81e6880e388f183b8431023c1808238479880540c0500b2202511018160601807203f04a44512811f4478200f018405c02803e8800c48bc60e01fc100580c202e510028c702c82fe30703ce220b82a1049d84055e080308f184708f0560abc100681a3c0600d231c2388f04e3a4911019c8b88f04e3a493841e03006918e11c478271d248880c01a46391711e0a493842203006918e11c47829243c0600d231c239171124bc111e0811993709807000de08ca18f32463300e000004782322650c7e01c003406511e0a06d8c148ce083240e002981180020806705c0e0b85184417054278403da23c1181b180d87f0504c0661706a005c440f0004f8200401011e1301985c148017100680018c0d8231261884500d8861cc009f09c13c670cc2e070c4700c26090a0060101701201804400d88064000a4068110920c422006c420e4004f8200400c0229102204806281003620bd11e0803c061148a94f08e220bd8c1bc1784f180d2c401e180f611c280cfc11a23023f82a0744940a911581c91711e09894811b47015f0807788988c2fa371170128152a406fe100bf8c1a1782df086480568e859e208f0806b0978232864700f8831c481cf0846f097823286470078831c561932984b00f8432263b00782274218802b84f47840f183e19307848c8e01f1063b00782274618802a093036801b0a60102de100ef11c0dc0746f8c311a00c049e131118f31d807c6600f044824307077c462231d807c6600f045024055e23c1013f0805fc61009017513a1fe120be8250501b40d0ea1be30445003c0d782929247c4322603e30800a0bbc268800c48bc60e60c0d191f1188b00f8cc01e089f094894a29151d407c6500f04481a353e1311194323807c6600f04549280de11c8b88141201c43b06fc4782129e109148e601e30c039e109178292924647300f18482443a06bc4782129e119148e603e30b054a2016f8405905fc60f0bc16f8405402b4700621be309c026200a824c0dc006f096381709205905fc60e01bc219205d01f440c06991f84645e0a4a49191cc07c614a080e02ea27a4287f84a1b43a8078c2e4b4c96392bb255e4a8c94b928b24fe49cc933925b249e490c91b922b243e484c90391fb23de478c8eb91cb237e46cc8d3919b231e460c8bb916b22be else (if j<5 then 0x800001460ac2191328648c66010036230014047c148f91007980b001d41384522a514928ca0200744500294102050824d4928ca02007445000005f8270824d4408fa03400711ca47c108f52847544501a00481103f24c0f301d10c007f044740c301510c006c33e0b01604c24644c7601c01a30ac0864704782c2463b00e8c220cd8471064f00c01c010008322650c7e01b118006032608c7e01003623000002111d84326652c66018038020013064c8b88b0865300c01c004191f0463cca601c00301932860cc4782c03800001064fc4782015805c26001e09584326650c8b88c030070012613c118f031807000ce10ca782c038005032644c478230663b00e00708481930984bc119432263b00e007105019304645c2194c02006c4600240c982012610c9e010036230000029c2782327807000a06002e01b118005f04620c9b84c0380060346080499231980400d88c00000a3220240f188c038006013e09c2188329807000fe0948e84528a4946501a004123523a114a68ca030068010a47c128f529406800da1148b88529a3280c01a0040a65230808ea94507e0a80d002449f88f040619178c6026118012a0810a8452648d4928ca03400001408fc1294524a3280d00000478252602a9178ca02e128011a1149923528a461168ca030068015613c1493602c00504a48c0c501a002a94506a23c1292519406800002449820f11e0a9178ca02e128013a1049b88845a3280c01a00428403fe0847d01a00318443bc40c1f82e03c007f05252c23016002804f04a5148a8e01948a80d00b105782a04a0d42503a08a4408a8e01ca4946512a1940400d000006213f04a53c229151d48bc6501a004b04035e0a4a49191cc31913017105782522e114a29251940400c88a005282042a1281a9251940400c88a00000bf0406147b84a034006601e0812c8100fa3060060100e811e11e0a0bc0d0004f827040ec1138c12b2047f0424c1158c5022800f04096408802dc8f08013e081a406902400b709c2004f8280d2047f040160348113c1022b18a04498a0eec278204563140a391c51782126a0440762881cf825022e08070017c178c3446047704e478438e0120d206c8121c1384e10e3804c0d9023b84723c23c103481a378200b0364089e08498120180f0478001c1d80cc2e0061602e0003991311e0802e01c003100829e0a488a29023003009c200080e0240301511c23c118100f630068dc23c10ba02f6305611850198393446046f0424fc61a23022f8200a8194089e0a09c170ec421342e1840c266230b88059c4406900278282705e0680017c141381f05e068be0a0980cc2f05000b8806a0009426c398930c422806c4015238278ce19804c470002b84c84268390920c422006c47042002388f0584c1d41781a3c1342e8074658841a3384723c else 0xe1005040cbc1007e180c45065e0b8603100a2c32f056138600a012302ef04e100503815c200a09c2782327807000a64411f8204b807000c0a2c238832963300c01c01000930807fc1027c038006f04a5148a8fa03222800fe0947a9251940400c88a000009034880ca183f05807000e650c1988f04648c6601c00000903e07b00d88c00281ef10083c1622f19805c260025c2028b10889c66014036430012e10ca782c03800532209cca601b118006322623c118c3078070038420c201af04650c898cc458070038829c2191b10651c660140364300126100f98804f807000c608c200932463300801b11)))
def mo255H9 (_ : Nat) : Nat := 0x32600356a2b037404160000000000070c000003c410500000157f1ed12a6b92800e618838811c2a6c2a53799e5241383800a4524515000543a0fd206890001993c1865dca24a9a372dbb3ca000f1d80af5f1200000347800d2e02c0060d43e0004e80000c091002c90c06100050000080
def mo255D10 (j : Nat) : Nat := (if j<6 then (if j<3 then (if j<1 then 0xc48aa0a06ff59182043ff302a8281bed6460810df6b1b04086fb551820437dacac1021bdd8350c10dfcc2a80886df615430437daa6c1021bbd8450c10cfebab04086f7655830437bb2cc18219fd7560c10ddec22a8087f54c530443bf2ea90221ff13148110cfecbb0a086df659850436fb28c2821b7d9361410df629b040867f615750436fb0ab2821b7d8555010d7ec32a8086ef6598404377b2ac2021bbd6561010ddec9b08086df615640427fb30aa021bbd8459010dbe49b0a086bf619430427fb30a1821fb94350110ff441280885fe64053042feb2229821ff09150110fdca0a80886ef61053043fe262a0221ff12150110dee4ab06084ff660530437bb06a9821bbd8454c10dbec2aa6084ff661530437bb06b1821bbd8458c10dbec2ac6086f7551830437bac8c1821bdd9460c10deeb2b06084ff661304433fb06b88a13fd9850450ddec2282286fd605411427fb30988a1bdd834c450dfac0a62285fb64883502fe922c12813fc98549409fe4c264a05bf65881502efb2a40a817dd9320540bf6c9102a04ff261614c33faeac1a41f795154140fdca12a0a07de54950503f7286a82817f9900c540bdeca062a04ff26161502f7b2898a813fc984c540fdaa8a82a05fe64051502f7b2828a813fd9814540dbec2aa2a04ff261515027fb3018a816fd9620d50bee49b0ca84ff261515839fae2b0ac13fc984c9609fe4c2a4b067f615754873fb0cb88a1f755254541cfec3900a8e7f61d80547eeaa4b0aa3df58758551efab8ac2a8e7f61d825467f930a92c3fb54254541fbca8ac0a877e5c560543ef2a4b02a1f75514c5509fe4c262a87dd54541543eeac2a8aa17bd9420d50ebecbaa2a875f5d5515427f930b0aa19fd865c5509fe4c264a875f5d552542feb2241aa17ed9220d50ebeb8aa2a84ff661434427fb30a9a21bec9260d10cfebab06884ff661544437d924c22219fd855d510d7ec32821877b5d521483bdaea99241bed4360810cfec2aea906fd605410c37db04a0861bbd8450430fdca0aa0a06fb249854427fb30a8221df57548510ff848262887f920931443faa8698a21df5754c510dfac2a628867f5d5824433fb06b8a219fd855c510cfec32e2886fb60c824437db0841221ded7520910df6c2904886fb61882443beae298a213fc98545309fecc0a2985fe640514c3fb264b0261df97158130efcbaaa0986fe611504c3ef2a4a8261fd93254130efcb8aa0987de545504c3fb262a8261bbd9161030dfacab02186fd651810c36fb0aa08619fd865c430dfac0aa2186fb609510c377b08a88619fd855c4309fecc2a2184ff661410c2b7928c3aa39ed7560810cfac0ae21867b609710c337b08b88619bd7561010cbec2ae21865f65d850433baeac18218fd865c430cfacbb021865f615750431fb0cba821fe12148110 else (if j<2 then 0x9ae2887fe58d40443bfaeaa82417fd9654120ffa4aa62887bf58d60483ff326a0221efd6458120ffca9a80886ff619815037fb0a99281fbd8350940fdeb2a84a07ef61542503f7b0ca1281bfd8358c10fdea1ac4a06ff61562503feaa2a0ac1fbd4360940fdec3282a06ff615825037fb0cc1281fbd9050d40fde48a86a07ef64543503f7b24a1a81fbc9850d40efebaa42b05ff65483502ffb2c41a81bfc8560d40dfec1b04a077f5d481542ffb2628a81bfc9854560bfecb0a2a07f754d43043f7a86a8a81dfd9754560fbeaa2a2b07ef50d615037fb0ab0a81dfd7154560dfec2b02a07ef50c815037fb0640a81efd6558c10bfec9902a06ff614815037fb08b18217fd9520540dfec3102a05ff65541582ffb2c40a81fbd4360540dfec1b02a077f5d563043f7aa8a1821dfd714c550dfec20a6086ff26131543f7ac8a18217fd9120d50bfe4c2c4a86ff61941542ff930a0aa17fc9850950dfec3284a86ff61583502ff930992a17fd9550c10efebaa64a877f5c561542ffb2ca18217fc9858550dfec3102a86ff20c815437fb0640aa17fd9320550dfec2102a85ff650815437fb30a1821bfd8660d40bfecc2caa05ff64c85502ffb2c42a81bfc9161540dfec330aa05ff65953043df92ca9821efd6448560efebaaa6086ff60d411437fb0c90aa1bfd8650450dfec22a6087fe48560543ff282b02a1bfd8354c10dfec1a86087fe20560543ff284b02a1fdd6354c10fbea8ac0a877f5c560543bfaea90aa1f7d6554c10bfecc2a29877f5c5614c37fb08b0a61bfc5360810bfec9900a8eff61562507feac4a8a83bfd5360810dfeb1b04086ff55182042ffb2caa243fed6550921efe42ae29877f615714c3bfb0cb8a61bfd8420530bfeca102987ef59154487f7a8628a817fd9520530dfec3102987fb249814c37fb08c0a61dfd815c530ffca12c0987fe205604c3ff302b0261fbd4350110ffcc12c0987fe611604c3bfae2b0261bfd8458130dfec22429877f5d5214c2ff930b12a3bfc9854530bfecaa829877f61d62546ffb30a0a617fd9655010dfec20a2985ff650514c2ffb3028a61dfd7154530dfec22a29877f65d514c37fa86c1021ff55150530ffcc32a0a07fe58150503f7a82a8281fbd4354140dfec2902987ef50560503f7a86b0281bfd8558140fdea1a42a06ff615215037fb0c90a81ff98354140dfeca306085ff65431502ffb2c18a81bfd6460c10dfeaa306086ff615315037facac10217fd9420560fdec1a82a07ef59541503f7b0aa0a81bfd6560c10dfec2b02986ff619814c37fb08b1261bfd8460930dfec3304986ff245844c37fb22c2261bfd9261130ffc90aa0a07fe4c550503bfacab8a43fbd6455010ffcb0aa0a07fe20550502ffb2ca8281ff98254140ffcb12a0a06ff655830437fb2cc1821ff93254140ff else 0x60907ff58d30483ffaa898241ffd434c120ffecb2a8887ff59554443ffaa8b1a21ffd5458110ffec9aa8887ff64154443ffb30a9a21ffd8559510ffec2ac6887ff64553443ffacaa8a21ffd6354510ffea9aa2887ff59550443ffac8a8221ffd6354110ffeaa2a0887ff65543443ffb20a1a21ffd6561110ffec22c6887ff61153443ffacaa0a21ffd6350510ffea9a82887ff59540443ffac6a0221ffd6560d10ffec1ac6887ff64153443ffaca98a21ffd634c510ffea9aa0887ff59530443ffac898221ffd634c110ffeaa260887ff54d30443ffa8698221ffd6520540ffe4aa86907ff215414c3ffacaaa021ffd5458c10ffeaa2a6087ff54d40443ffac6a1a21ffd4354110ffeb2a86887ff50d60443ff92aa1a21ffd9650d10bfecb2a8907bf595644837facac2241efd6458110efebaaca906ff60d60443dfac6b0221ff5314c110ffcb0260887fe541304437fb0aa0861ff9404c110dfec3282187fe59520443ff2c890221ff95448110dfec22c0887fe541404437fb06a1a41fbd5450d20fdeb2286907fd59521443feac890a21ff55448510bfecb286907ef591544837fb30a1a41bfd5460d20dfeb2306906ff59583483feaa690a21ff54348510dfec2ac0887fe58d20443bfaeab0221ff56348510dfec1aa0887fe4c9504c3efaa6a8221ff94254130ffcc12a0987fd4c550443ff308a8261ff96054110ffa98ac0887bf59564043ff130a82617fd9550110ffca0ac0987df545504c3bfae2a8261bfd8454130efebaaa0987fe485604c2ffb2ca0221ff95348110ffca1a40887fe65940443ff2c0a0221dfd7559410ffca8280987fe581404c2ffb2ca8221fbd4150130ffc48aa09877f5d5504437fb08a82217fd9550130ffc90aa0986ff59584043ff262a8261ff94154130ffc40aa0987fe605504c3f7a86a0261bfd844c110dfeb2b08886ff60d43443bfaeab2a217fd964c110dfeb2b04886ff591824437faa8c1221fed544c920ffca8260907fe581304837faa6c1221bfd4360910ff6b2904887fb59082442ffb2898241fed5420910ff6b1904886ff58d824437fb06b1a21bfd8458d10dfec2a60887bf59563443bfaeab1a21bfd9850d10bfecaa608877f5d5304437faa8c1a21efd6559110dfeb2b06886ff25583442ffb2ca1a217fd9550d10fdeb22a8887ef59143442ffb2caa221fbd5450d10bfeca260886ff59183443fda8690a41fed6348520ff6aa242907fe59540443fdac890a41fed6548520dfec1a60887fd59531443bfaea98241ff5544c510ffab1a62887fd50d31443ff32aa0221dfd635c520efeb2ae2907fb50d32483fdac899241fed654c920ffab2262885ff65930483ff2a0a0241fbd4350120ff6a9904887fb50c82442ffb2aa02417fd9650120ffcb02a09077f59571443bfaeab0241dfd635c510efea)) else (if j<4 then 0xe5d1db11d191c6d1bd51b651acd19f9196118c9181d1721168915c9151d14ad1401132d1281115d10b10fc90f1d0e5d0d750c150b410a45097108b107dd06a505d1051104790369029501fd013d00e0ffd0ff38feb4fdccfc94fbe8fac4fa40f994f898f828f790f694f5acf528f440f3bcf2e8f1b0f0dcf058efe8ef64ee54ed80ecacec28eb40ea44e970e84ce73ce6b8e5f8e4e8e3d8e32ce294e210e1b4e130e084dfd8dedcde08dd70dc88dbf0db08da84d974d864d740d658d5d4d550d4a4d434d360d2a0d1b8d10cd024cf78cee0cde4cd60cca0cbcccb0cca88ca04c958c8d4c7ecc754c6d0c64cc564c440c3e4c310c23cc1b8c0e4c024bf28be40bd58bc34bb88bac8ba08b970b888b778b6e0b5f8b524b4b4b41cb370b29cb1c8b0b8afd0aec0ad60acc8abb8ab48aa9ca93ca87ca794a684a5c4a540a480a3fca33ca27ca1f8a174a0dca0589fc09f289e409d589cac9c289b2c9a44999898d897b496e095e494fc94149340926c91c090ec90048ee08e208d608c8c8ba48aa88a2489a08908885c879c86f0861c8534844c838c82e08248816080787fa47ebc7e247d787c7c7b587aac799c78a078087720763875a075087420738872f071f470d06ffc6f146e406d6c6c706b746ac869e068f868386764665465806470637462b461e060f8604c5f8c5ecc5df85d105c3c5b545abc5a24597858cc5848576056a055f4550c542453645268515850844fc44ef04df44d5c4c604b644ab84a0c496048dc4808475c46b04618456c447043ec434042a84210413c40903fbc3f603edc3e303d983c743bf03b943ae83a6439cc393438b037c8373036ac36143590349433e83300322c319430d430282f402ea82e102d142c682b802a982988287827b826f8267425a0253024ac24142354228021ac20c4202c1f6c1eac1e281d7c1cbc1c101b3c1a7c19e4194c188c17f4175c16b015dc1508145c1338123c116810800f700ed80e040d1c0bf80b380a64097c08bc0810076406cc05e40538047803cc0320027401c8011c00700001ffd4158150ffec22c4987ff611614c3ffb08a8a61ffd8650930ffec3282987ff505604c3ffac8c0a61ffd8550530ffea0aa0987ff261514c3ffb2caa243ffd5448560ffec9aa890fff64154487ffacaa8a43ffd6448550ffeaa242a87ff59582503ffaca99281ffd6560540ffeb2a62a07ff59583503ffacaa0a43ffd6548540ffeb2a42a87ff595214c3ffac890a61ffd5448530ffeb2a80987ff65954483ffacaaa241ffd5458120ffec9aa8907ff64154483ffacaa8a41ffd6354520ffeb2aa0907ff59150483ffaa8a8241ffd6550d20ffecb286907ff50d60483ffb2aa1a41ffd4354120ffec8286907ff59541483ffac6a0a41ffd6550120ffeb1a80907ff59531483ffac6a8241ffd654c120ffeb22 else (if j<5 then 0x9b281600dc16004837c2618c400d47045c61008426127110b8380d70503600506dc1027c41280314440e00486dc1027c414440f183d080ff040982fc43183d090202e1a426c441e03718483c21848c4027877183823c17090986628f183867c4027c20480be1cc6102801dc203dc10261202fc4318541d08f080b86909b102700dc615c202e098660e048037184070000680703dc4705c202e098480e00dc61cc10550985707f080e3030741bc6400632009c1fc2059c441b07401c614c13220d80d07f08c441b07401c61751827c15041cd0287f094421c86f18801a8a5034421c86f18800f4802687f081671086a1c80718509b4870942224878480e71087200585d48048098380370487f0948a1c86f18801c87f08035034421c86f188012080088783a0df108721bc6200500408a1fc203740d108721bc6200582dc26224403a20f180de024c250cf08c8b1100c00c1100321fc221b4421c80718421fc204540d1087200389c89d2087f08035028721bc62005847c232311403c6400c1100350287f094421c86f1880120b708c444500f19003044323c2444c4403c6400c1108a00d40d108721bc6200400d07f0906b1107401c6100b7094424480f1880504402948d1091203c620141104900dc1709c40ba2eda2e1a2d5a2c9a2bda2b1a2a5a299a28da281a275a269a25da251a245a239a22da221a215a209a1fda1f1a1e5a1d9a1cda1c1a1b5a1a9a19da191a185a179a16da161a155a149a13da131a125a119a10da101a0f5a0e9a0dda0d1a0c5a0b9a0ada0a1a095a089a07da071a065a059a04da041a035a029a01da011a0059ff99fed9fe19fd59fc99fbd9fb19fa59f999f8d9f819f759f699f5d9f519f459f399f2d9f219f159f099efd9ef19ee59ed99ecd9ec19eb59ea99e9d9e919e859e799e6d9e619e559e499e3d9e319d719cd99c699be59b399a7999e198f99861976596e195f9957594c99431938593019205915990358f898ef18e6d8dc18ced8c2d8acd89f9894d888d87cd86e585fd853d8441839582d5823d817d810d80617ff17f457e5d7ded7d7d7ca97be97b797acd7a3579d9794178a977fd7715767d75bd749973c5732d729571fd717970f570356f616e796da56cd16c4d6b8d6ae169f968e96865672d665965496461637962a561bd605d5f895eb55e1d5d355c4d5b515a915a21599d58b557b956f9567555dd554554ad53d952dd516950bd50254f514e7d4dd14d4d4c514bcd4b0d4a39495147f1471d465d45754429439142a94211417940e13ff93f4d3eb53d913d353cc53c193b6d3ad53a5139b9390d386137dd371d36c1363d35cd357134ed347d33f933893319326d3211315130a52fbd2f252e652db92d212c892c052b3129e5292528a127e1274926c525b5254524992415239122e521e920ed20051f591 else 0xb8017c105c49928036005171840e10570417077c2072036005171840e105f040285dc200c40e103f04177080281a40e103827c442e1e035c140d801102126c8c1ac46191160040281982e1500dc60dc121012877c20734882ed101ac617c106e0a70819e100bb44c61204705c201a4986627f184704198484991fc26105111c40f185f0449a11c2718478664714440e0058020e9264a42e1e05d0360048001521016f080551d0b8390313780180183bc2000008250bd034771817059801b040541df08c882e1c83803718509049929c21238414440f18489049929c27044880c511038014010904981c4a70848e100314440e0060038402bc104903600380600877c207348c2e160101740d80184982384709c1718478664714440e00602827f18418664700f80100e8a3c611d420721b6004021c142e0e09209c0d80110a3110794440e003093c10260bf1007d1d4601b801424f040bf1009a1e06e00421c4a70848d1086a45809088d1087d0286f18800e204461bf098402ec6b1844290082dc203b88b110360346f1940194602ac40490350030808ef040bf1009d1ec6114202ac442747881c60f0202ac442747845c60f4702bc203b88b110bd1b116025079c102fc4026878458091c12110d877c20734882ec6b18506e0980dc6090202ac44260371835088ef040bf1009d1ec6100b826150381200dc60e080080070400c2619c2e070380887103600702e1b8381980dc60c1b82603718270827f181991e4700f80110082ac404903600340142028c4049036003f050b87815027036003a1c8a51087c0d800c0870509849c40740bd1d4601b8017067080a3101241b800fc211e1991c20f183045c211e1991c06e00382ac409c51103800c08851c2041475100622e0e20dc1600600806126160488370580102585e147081051c1671003705801702126c8b110642e15c0cc160050180ad101220dc16003897c20361d00f4400dc16004a088612944048835058010215048a5220e5034421c86f18801700708c8b1106c45800e49b22c440106c45800f0c832c8c2416f08c401500b1d00704621c4a70848d1086a4580114103651d2287f094421a87201c6174129b48a1fc22240e5034421c80174105489d2287f084403940a1c86f18801a91801c10681df094882e840720e00dc61a1d02bc203b4885803705801207129c212206245c6059001303708c8b1106d18305e16f080551c167100321bc61417f081600d470ac405bc205418718341c49b1015d1c23718381c17926c882e16038037184c1dc2322c444580c1b4630580140da23c231c0351100c4541600521c0af080eb220dd1003445416005a188a51087c45416003b2217f08c7059c400dc16004b23c2036c700ec400dc16004f08c885ec440d800c17b1dc23221600dc1600432217b1cc))) else (if j<9 then (if j<7 then 0x38470403b180b81a406e17211c11260b8cc203c0ff05c2322107111171900c00612647f04c2328107111171900c00585d04704c24281982ec61048e11c11290a06606b44c0930c832c8c22c4011c131d0730909403005187304c212203854c602ec0e100e150c832c8b1d09308c9b28c4403007046328c8c3309309c401500b1d007045812d4b1d09433c2322c4403007045b0709308c743216f1100c01c1141cd22147089151080f188070450101bf081982e1600dc6101d8720b7094424480f18807045032c270909327c401500b1d007045a06118494891016f080551c91203c6201c11d07708c8b110940346400c112c204021f1111403c6401c112c8b2810309c444500f1900704503c0ef0849b22c444500f19003045a061184254d1dc252291203c6201c1181585bc2054037183708c8b1023445460c23708c7061c4045460fc2048c444500f19003044048c2073c444500f1900704482a1231111403c6401c110c202bc2073c444500f19007045024c87090932900f10c7323007045a1c4a7080e9234424480f1880504584942073c424480f1880704482a1251091203c6201c11009d1091203c6201c10ec8b1c11b08c9b2911403c6401c1161088ac7047c232311403c6401c11611b1c16b26c8c4500f190070453221185bc2014c744500f190070458774424480f1880704382a1251091203c6201c1100ad2211d1d425274a24480f188070463200b0660ef10c7f081144500f18c7401c11c09a454401e80f188070440060e822147081051d4424480f18807046f040285419f0803b1d0b9101640dc61815511c200e03059808f880280d7044a123c464447603c617880281512848f1020a4447601c617c205c03d1003245c60e15708029108d80dc60f48708910454a51c80f1948a01c117447081531c1602fc60e1500dc208f4401ac60ec8035c4329c204511403c632300704602001929c20340924447203c612208a01c11dc250810127c424480f188070450474201549f0948a4480f18807045d080af081cf1091203c6201c1140202bc2073c424480f1880704502b4a522105074271091203c6201c1196104742522055274724480f188070460760b71091203c6201c110d483404b23c2444c4403c6401c1160d32221b28c2444c4403c6401c116c8851c2444c4403c6401c1120d30614309c444500f190070450221791fc2058477100301891203c64006f088222888d100331c86f188014010368981c8a70888d100350286f18801a1483851a29c21108880d40a1bc6200603651a29c22234421a807184808888588a00dc451c86f188015c20540e7048a2220371086f1880168a70888859c421a80718470449827c2610470660be004f082a80f84103c101b8051848061df0825d238402e5101b80140183a2b7081d6100bd1d4601 else (if j<8 then 0x7050931c20c02c8c0146160d02c1571846838400e200a70470449a1d4742e805004a1620047c16104982e34320cb0902022c4411c101d09403005186c320cb2308b11047040730909403005186c320cb0902022c4011c131d0742500c01461c0c9044a4224780344618419018016c2510c74031141a321f440a487328c88cc2709c642f440688993a47190bd101a2262b0907b2219b11c1400c641a1a144204848b11c104e0d01c03130e853c11278730844059866004a1625091481270370548d0241204203419f11c614440800898485d20c47050031906d028991c203c15f11c100c1b0ec13094232348b194642e40b105606c60a4c6718515101a0c0d426c4509c141ec602e0692c8427427040041e06f18d1302542742311c141ec602e1a03849118605403c0d000d09d08c47050782e3508c1323c6302c441e0f914240909b1003400320488d234241e80d02c4055c606c583282222c470428c1a3e08c440d46227068c187100a8800982e305688207c2055c4225c603980048583441109821198642f00d104d848002264e9c2031109c2e2105c203c467190bd03441361b144103a479244660200d1180000506cc470509c0d488c54852c403c84704099284880c57081b711c1718511024a1224c3542608c4211466185103900426271802d2081a094222486518154001997c2608c4211c66190b8398042612170c832c2408c8c22c40100770509403005187110c86098602e898660e110470448b1c87f181b84a1a1242211c1126c65198601a1a1342070840381a00d000e19705420734641b40a101500f00174830821812c47041131906d0307400899b48d081c2100e068030e19704471260691f40a1015718039602411c112680d024a02bc606c541a8470427c0c2a098470427c0d4641a38328121e00e1146229069048c11c170819f182a84a1a05453040f83c10034c4445c6403001449826481088a608471198614400072409a610840411c4661851001c112840960d06ac103e473084991ec4445c6403001a0d053c13040e92604b5247708c883cc4445c6403002282508122194642e150f0c83208b08c4411c131d0742500c01461ac47050a00d078a40c00c2322c64101a05440461740300308c705a5131906c444dc101a201c1072890300308c7042c642f0405448880e91e47704147111171900c00583a48b094203cc4511c13194642e1a2266908c4511c13194642e1a22648a6447050bc01098cc2508c8d22c4111c142e1b1242311447050ba26321fc20662a511c10401a20c4f05c203cc6718c0d105606c4f080f511c122e1b0d847042781a0331833090a066c602e150383b08c744544619030dc102a44126c2603800e17704c602e1b838498f043204a072000700281ad1303c61708e10c2011c111c47c1a1a7181b16c212 else 0x150f0cb10c84034640089c1a410807e10470aa1c8543f04470aa4a054292686c1b46054843223b094232348e11c111c4606d0b95c241bc62228a310120e24127847044880c408e1bf10897180e0278202a418822010479198614400704419224098098720c00b80d11800f485090a145460550006616138271986402c46000ac26461900b100a82628645151815401c112616101e411c1219460020a9270012854094661800b110002b09914130942122c751c10b18155190b903844587400478140470402c0d4090c211ec886784401c104104069031648e20127044792980e00411dc11061c85d84070031024b04c21280ee110007004c11035025a46018462102a88d23c101d42014865189120280310886e17611c2067c61441ce004094c1006c886f844001c0130406903502609202411c1119864020a80089940411fc614400704c212840924720141508129454605803a105036c1504c2508c8d22473194642e40e111606c79220b31049d084a51980c03801448826121100f70402e0380120e50982426c409c030e91a09c152947218112441520348a00c41a81f09888560081c157190b8385042c2077c112780e00389dc2623c611e1511c0e600482e5106e098811f054121c865190b8034422900068879a49719440220006e198e0b944088001b86630af08d10c2011c121d0bc1a87d18583ac1504c25084891cc6518c0d03840421506c7f080b9454642619848069041012420260e926101244660200d118000070490bd18c4027068c1e519860020ac00c442641044887647b084a1244660200d118018497194206e098b48073c131906d02898ec820019f048984506d0288b1d08c006520c207212044c641b40c230022658160b2261980c120cc13090a31012044c641b40c230016c47044106e030663705c203d4404210245c62028014c230541108c8d22473194630340e10108541b1fc15094891c07f1804e101086c511dc11262a922150dc111e2a922150bc1129c26101220c3108c1504c751cc6518c0d024a06e1086c683a4a111c111e4911980e0000140e927c470405645c6602c26005311464008a21f068d4203a4992848b111151980c0380160984741209420384722944222032006228c2211c121d035190021f0694a2089c150487d1c86518868034420688a0075080ef0549a46070148651891202803106d09c14260680cc60d02704c1426c73180bc281b934212647a1144704102194624480a00471a82508047044783c102194624480a00471b4206fc142606f18d1302406f4270509b180b81a3b080a929c1603800c1b826034002509023110980d000dc261d0351900228c441a41080ee21c111e0c60380104270812055c4119c642e0e1370993a64341e31084519861440e40109941e2248651815401098ec840904)) else (if j<10 then 0x86ac8c22c4011c131d073091141a5852c240808b1004704c741d1141a8018c2311c1126470630041b111248f040380c068a49b09c111e0301a340c0330902022c4411c101d1141a5c0c033090232308b100401dc14450698c1836c2311c131d032014612c8b1cc205903310310848b11c141a1b40c3b08c705903201463103b060db22c4704c240c3884c8c22c4411c101cc244506940212684511c1040865188bc030011e609021704815080aa2348840072194622e0dc02c440003a4072094204849a3a1500c4123847044a618479063c0d21123466190092700128c414817080f510108408622fc6054503a42111c16180386d03114261815926c440c3052c2408c41264703cc64190b8548018489298611e41d10308904704144190ba0247a004b2047f0816710030970b838c8940310448928466180091e0010744162500dc11098203a49c1c4911986036008141b0014422c21090e853c16184405849928504219704c2127861101611e480c4112908919860024790600510591c4885219704479288a6088ec1d861101606203a042123860541b311030e1a80849b18164190ba02c4200479700308c8b11c141b110f00322c4704c241b110f00308c4704c741b110e1b05dc123ac231cc642e8da03441700322c4704c730906c444400c2311c131d06c443a09422234885684511c12194624480c001b1dc111c4785a2508c441a49c0c2c1cc23104991c1885418106112647b11c1308c601443084786205054470603c10c200e24202150cc8b0900d1103619110ec231d00d110320186444470447863c20150041b1111c112647c0106c443126c2311c111c47c0106c4449264785418084441bc111e4a40c3511c100e0301a2911c100f03080db08c9b11c140c3308c88590331029094470403c1b030d8670447929030ac27044980c068a0eb08c76190351111600431049e19030881b220ab098640d444458012c22280ee190351111600406c17704c886ec23190ba3680d105f094741a4a3118640c3928c211106f044711f8640c4c1cc811e00b2216038201106f044712847e19030f04308c880e24202150ec47044a11f8640c306c17704c223ac642e8da034414c230541108c8d22c751c10b194642e40e111606c807481209424101242f4641a4d18c2119c104b0b8c1085d04308c7519c10730b92c1308c7043464110b8f4631c4670412c2e30084991e84511c104086518912028011c68641770449c2e282a29c11c11270bc004a10c86180b86e0e226311d427041280f0b8c40c00c8b1cc64101a054430541309421238431d47043461190b98c15044232348e10c751c109181b42e611cc1308c8814c621ac0c101500e591dc111f0781083066c09080305c204b040148bf1815600198586705c204b04014800668b90477044781e86866 else (if j<11 then 0x50442618050e0342386054038a6240d4111f8605a3092034084791d86054039019321c111c8be1816062029283065c130986014048e269044a4224790380d104180186164892847e0344107860e2240408b094431d0740306a018644466184a31047c0d000c620894231049b2140e024a4018616021261511e034003704471298600e47c0d0011425221581403854030e49b081b7058600c4781a4123c16180300e068c1192951923c221dc621b4407340a00641d42522c400f460540690a1085c15048701c8651886803443088a200740c03308c4704c74454610c8b10c730818445460ec2310c706111518320488d23423100380c1b10c260888d1003b19864021501a520942011c111e0f0409121a491c4885219704479288a6088ec1c18e024409803e18884219704c2127809102611f86150300cc2311c131d06d184704c140cc8b1cc231106d184c0c03704c1308c731106d18489a411224a11e40e034400041e185b084243a14f0449e02440984a6185f05c203d44042102029121a4852c2408c4011c11264703d1141a80181a8080470449c448011e408849b08c4411c144447a004c0c03308c470506d183c0c03704c1308c8b1106d1848081b926034002c0c03322c4704c244546118631049c0d000b0300cc8b11c130906d1842094202215a11447040386c0340058261982e873182f058600f03400283507422c13090a066c602e069448c1cc203cc406dc12400b93420561500e030a48c1cc1709c60681983c41081b7058600c4981a39261511e0308488724a11f80d11800fc2123c4704870a01a0e4251003e181506d03400406c0d50902704c13180bb1109838583a08e0809854034003c1d08d098209d09b1003400482281209420668651906a0340b101506d001c09d198641b40e0215928c44005427427050781a033183d1186129c111f034003c0c03308c4705115183b08c8b1018445460d04322038908085433234430803b19864021501a483b42310499294660300e0100144422341509820674661806868151748d10c270487d198601a1a0545128c2111c111d8606c47c0d001582622440381a00c3069089290a0661201ad13024f094761815928c440d00100ea0942022c4111c100e1b00d00160710442608121198641a40e03440541b1b08f042781a0331834460183ac1f04c231d0705ac64191140300510786c0002619b180b89c8784887141b03507423c13044a3090a3180b8660e1ac804821869c10000d01bc6344c09648c1cc203cc4704903180b8680e1607609888158641b809101500e50368250888d22c4111c101c0306c5890227050103ac231c1441cc64190b83680d101b2008810825084783c102194622e151462089425198640249929003105128447058611e1b40c388808b08c4411c131d0744506a005 else 0x4980d44504c2619008000392c208503))))
def mo255H10 (j : Nat) : Nat := (if j<1 then 0x76de00000a7000193f3a7aced558400000010eff35c000000290b0000000000016c000315900035356bee42b32951468308372a1572dac328000d28000064ac439000094d53b0000f1500004c748c90001aef41000000000000234c00000000000003c7b106454858840000000c6400030b8e8740000000d4761bbd71000000000000000000000518551690c1d230002c920001a3c0002d1a000353e00000000000531b2b34fd0000000000000032dc0000003284d3000002ce400042f000000000000d248a2000391c0000c4e0002488e9288e95bea43be92c4cf1015079b444000000287c516ec6600000000000000a000000000242c000249d000009368e8000a02f83eb4841589dd3cc8a311c38ec7f244e0210da350036b000109b00000003344000833a407b46544a1136c5c407c00035ad0e8d8140000002437d287f3282ec0000001ef9cb4085f00000000000018a2e40000002af8215d9497961cba84100009057060d05aa041507f6fd4c8c114260000f3ce8e20000000000000053dd926f2330123374000000374a000000000000000000e43f1666450003e06000117000034c30001d0fc51588170abb1384a9474246d955cd2e0f83a74115012047d3cf70e5000000005296ecb22400071580000000000fc99cb180d8000b4dd76e133748aa3ad876000288b941c00000000000001d3091880450000000000000000028317588000801b7161b2d4f600000004482a18f5769560000000000000000000000000000e25000000005650000000eca6e1bf1a80000000000c40c15eb548000c0fc00065d7ec6f49c8bf0026b3c813c00022bc00000000000002a2d0001118016b13ac10400000000002854000000180300019020002144000142e0000000000000052d3500c2c8000b43554e00006eb35b70c6000101df0bc0005012f15c5a04f0c850000000000054400000002af2e12c000f49400000000000126cfc621000072dbd1ecca08a3203c000850c00000004d600000000000000000000078d0c2da540972142b47ab57e53600000000001046000284212b703d0bcc4aee3ed13b000044ced0095c0000000000000084d00000000000000000000000000000000000000033c650e000000040d4000000000000000000000000018020100200804004000280600400050000000100003008000200000c000100000416010000040000401004010000101806000010000600803028010140600005020010000101808008070000300c190080a010000200000000010010000002402018030040300c000040002c00004030001a004040000a000020080000005000000000100c02000010000000003028010080100400008050280201800008090080b00809024000040900006000000040501403010090080400007004000180000402 else 0x3625e14796a0000827edb549034f44d9a59f4f5139c8a84cd7c5870e880d000000091e1469000000002a8000f87814c000000000000000000000000388d00504b56379c97304c000000083cf99dce122034f2300916fddb0000a47c000f4250d0000000052a7ac94bb4829f5ba0fa4354d1342140004097d7408e400000000000000000a2478650000000000000000005660000000441bc9c51b5517114cc21e35352d74a506f6316207e0ca4e46278000427c00091cf9730000428e900f3af30581e5110edf443000000038cc23abcc791c400024f1905d55d11d152c000619c12f00000000003834d09009645820be0000000d491b73b3980000003052cbfa96300008a60177f52d05c0003420000921e89a0000000940400000004e0c08f822937385000000000001d3961df52c000214f51b1f6494e31144d20336f92495ae509f3f432c80a0000000c1f8000337f153000146bb2c00003aac000120d0431c4b6f00000f20ed4c0000000000000000082080000000000421b833000000000014632c47cf42c95b3b000281a00000005071b500000ce331c80000000000c449564617a0d245500000000c0e42f50103c920b391a2c2031c22c89488000b2578f9836c00044b80000000c8f285faca6888000f3fbc0c0000928000007f0000000000000000028ff3bda88ef11c000000000000000005d4400000000000002d51000000000000000000cee456d569000000051d401be290000bb580000000000d3600000001af1000000064cf89962ac00000000267)
def mo255D11 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xd3bf26fa4cfe98592dfa5684a22930d22423bb46c88ba5129a1fc432684f105c20583fde7dd0f8e9eb43cde7818ed31d613a147284e251c0e37806e10d969ac434da687ccdf9983324663c0c55985d2fc45e50b9116e62cc45808ad5955429fa52bca279401279c4e6c9b4132c25bc49f890f11d92304446484610351faa3dd478a8ec71cce38406cf0d501a16331863c0c3c17b82e145928ae0151228a44e4895711dc225c42907f20f481d1036d867b0c6c17a02bb053109a211a020883cc06b40be8151825e043207080ba012f01c202280228000ffd31143ff61940ffd85443ff61540ffc85503ff59540ffd83503ff58950ffd86443ff60940ffd62503ff54940ffd30483ff4c940ffd81503ff20540ffc83503ff54950ffd63443ff50950ffd32543ff60550ffc81543ff58550ffd51543ff50450ffd41543ff4c550ffd21543ff58150ffd54443ff59110ffd84443ff59510ffd83443ff14530ffd414c3ff48530ffd604c3ff4c520ffd504c3ff50520ffd61503ff54520ffd61483ff50d20ffd63483ff54430ffd410c3ff55120ffd64483ff50130ffd51503ff14540ffd40483ff4c540ffc31503ff48540ffd60503ff54140ffd514c3ff61130ffd60483ff60930ffd624c3ff50930ffd814c3ff20530ffd614c3ff54120ffd64487ff59521ffd60443ff54110ffd80507ff50110ffd51507ff58541ffd52507ff58941ffd82507ff60d41ffd30443ff61541ffd86507ff55121ffd65483ff14c10ffd53043ff58c10ffd52587ff50961ffd54043ff20151ffd64043ff61151ffd82547ff58951ffd42547ff58551ffd65043ff60151ffc80587ff50c10ffc83543ff60d50ffd54543ff59150ffd84543ff59550ffd53443ff50d10ffd86543ff48560ffd41583ff54560ffc81583ff4c960ffd42583ff54510ffd61443ff55160ffd41487ff54521ffd52583ff58521ffd41443ff60950ffd31442ff60c10bfd83483fd48510fed324837f5c520ff531442ff60d10bfd86443fe50110bfd840437f5c510bfd82443fb20910fed214837f5d410bfd85042ff61810bfd84443fe48110bfd854437f5d510bfd844837f5d550bfd86543bf58560dfd71583bf58960efd645837f5d560dfd71487fb50921bfd844877f5d521bfd85486ff61921ff551507df54950bfd85506ff61941bfd80146ff60851bfd84147fd58551dfd715477f61d51dfd71587bf58961efd645877f5d561dfd625c6ff61942fbd42506ff60810bfd85482ff61920dfd710c2ff60430bfd820c2ff61030ff9504c3fe58130dfd714c2ff61130ff950503ef50540dfd75483df54550ff960542ff61850bfd84142ff60c50bfd82142ff60450dfd71142ff61940bfd85503ef50d40dfd71543ef50940b7d85042ef61030afd86042ef61010bed820c2fd60430bdd83042fb60810 else 0xec22204401c600304561218880308a0030441d84c408a020d4660a00560b09880340050060b09880688a00385308914448a038c80101001e106e0e0b0cf102200e3001823429881103c038c00608801844900ec20302e1b4401b0500300d82c2620448c180604040dc1c16198302e1d1501b050038290ec2246191717a220d002804110761110010688a00487603840884f1814444009070042911c4633040f801200c105c282a0781a0044461d138a05e07044401a0050330417c40501e0d80118c0a2201f0016038c4404e00288b0888030045c2220022206c046010441d8444034450120290ec2246182f802220d012809821b8382c33c403445012b041406e201e22808f820a0ef08911cc20838c25180cc10dc2c33c405d440d8017820100c1c16c224424000ec20838c0dc04f01000290807907181b809382c2047101403200458c00940ec10530811c4034248c009402c20a4281144018458c00948402608602a099071844382d848887510061163002505b09110ea20838c0dc04988c3a26068041228888788b18013019820a05f100f114048440501e4cc60b2023c0110132c6305f011d228e49c202e8f114048010002908078886c110047840405d1a8c11404a0883b0988090051800c11204c10dc1c1619e201a228015820a6201a0f11400787e100c814443a1b8c801210c26081e06c40381b8c001411c26081e22c4038248c00143308e13040f15019100e06e3000603823821984f082448e221d8c2d0804c104d298807c3b184c47090e0ba200d001c061109007090ec622305002b04141de11230819e3080008c55840b820398203400a0a44a1d8448c3202584441a00580401821b85866171501a0052102b82c404d1f8c1c038208e201e0dc60008010a41c14c2045102a03037180033058809a381b8c000e0ec10530811c4088248c001410c161023880a019020dc6000b8a6122288032061b8c80120184630298207c007018382c1200e112224c6423050030000e0783411844763305002a1c16c24442e1d4401a004820ab84466082f001f0988110071800c10e13c26081e06070371800242614c4088038c00608811e104401c600304393709820788b100e001006c26081f8806838018c270988110071800c10e120ce131001006087aa1d5206a1e53b8a6c34b2e92cd20ba37b457687ed094a0693f527b5cf1d9d7b399a6eccd5599eb32e661f4bf097332c7a548ca1f935b2512457480f8f711cae373467d8be1161e28f44be88630f6a1b442f6851b07ba0ac40d480c4fee9f893e8e7c26f685ea0bcd878baeff5db3bae374e2e791cc23924719ae125be2b7536e0adab9b07b5706a20d29da1ab3e766d8cc0d93b31e962eec45d857303c5fa6bcd174f2e235b3eb46d66b2c6457c0ad0555eaa5d53d6a62d483a89e50469f9) else (if j<3 then 0x38c1b400f48a13048e49a53100d03000a488a30982c40802f0e06c00a0d14f1108c105c260d80121a2ba09225988e11108c0605e1c0d801c0f488a30888c1438408c0b8d85406801c9007e1304270006b10065120600606911820b84c54068010074760b0891c40340c00242419c120922374724d290c1620e00844441a02884888190ea3a249348e22181b41c03048483405148a13048e49a53110c03000a0a0740e8ec1611238886018005e09228e11e104a8c0b8700d08401888c201e182ac10180044091c3bc20e523080e018458c0d804d81011228e49c20388f1163002588f05020a238803bc224610390ba3445013c4653c1409080448a3880938405d1e22809f8248a38478412c2036174688a0266092384840711c40c608e02503c3491c20db048ec44300c002f048e1de10729184070818c11c04cc12451c93840711e40c608e0258483382410503aa94743b0891860b20088834051091103a8e8924d2388861060283c12120d004121100a6092984114891d01c6246006c4108130ea4f05844882b112280e3200744006944885b04844702b112280e320076082f8809c3c45011cae8288a221d131805e1e8c11404cc1208281d04aa51d8448a224501c6400e48050022b0d05b081d888ab10220e4051b8c4023824100d22374721126944448a038c801c820e057088812103181b8094240ae103b111662036174688a02614e2040c105f10134788a02515d0488870ef0839888c02e8d4608a027012201c16620268f1163036012e20030ea0d088ec10b7112280e32006a302a2c120190030ab11820a0181f0146e3101042f048207a44662dc20291c88914071900392014c20001a4fc60451e334701e006a1308810e94718131c8906d002d048180e131814440920048d50411808df188809c00941204a38c0aa20483680120440c043b8c1c84e004019081d44423090c8b86f049383400d03609040f488ce2384474322e2c4441a007a11021d28e3072131b400988c13050e89c53100640a30000d801aa32488f048201c46090e89c502e1c4401a0084100888c105c54130340094862304140303e00a2c6206085a2211820ba30260f06c0092495d05118243a2688460302f0f06c00e480bd1d8448c30580611400a422445e8e49a52182c0308a0058a7048202035528180e302a8809c00d412451d8411220360600929017a3b089116620441b03004b026082f8809836003a445e8e49a5059881106c0c012d049147612181b4401845002902220a8e4480d800e9117e111d0c16018450024061a08e111d88110071800c11611c26091d8806c304500240d82c26201a8c1b098247620000d114008c200510061140060703f09824705c5406c6120308e10108e0605c5406c1400b040302e141503c0d82801382156102e881601b18400c460 else 0x440262a8a4440d884743719002d228e499210308422511f8cc10d8aa2a801e2f47611222c034007c1238764840e112233c64206c5515400ec12530855c6021222a801203222381a2a6220602918423f1982420e60086084a91c21211d8c1b420aa2a8018530ae082f88098360042445e8e49a505806801091c2238aa0784233041780145348a38aa934a423041780141447154778448c2304390bc00b0d2470836c123b100d03000a07a4708554742001820bc00ac1247088e03a302e2a03422005e08002ec20140c8184118207c2308002aa38662a80140c0be1022141c8901b0024064248859268ec44322e1b41e090906801e574143877841cc45180c0ba89100d801d848242304330ba30260d80148c0a8e44806800c900a61001821b8586788032890300351015c105c541303400800243081d0a0e448068012820e28d1d14c2222220640c371900354623c1208290e1de1222171c8711006801f848242304330b89038131c01a00613e1d82c2447100640a30000d801884020540d01c4037198209800b14e0904140eaa51d0ec22461917162220d00406b824100d22374724d290c8b8b106844441a008a0923844701c3688034009019103a8e49a47110c8b86d07824241a007a445f84470b00d001d201ec104f109448819448180161a11e09040f51a4623848705c388803400f2cc470851c46080d0e46036005a10083603407100dc660826002d2258c22389988208184500281c11c2411103340c04483806e330413001e8248a3b088820818450026040348c211c934a05c540616400c481611d844893310012081845003122584724d284cc41040c2280161226e09040f488ce23848923a1901262220d004424424885a249347622184180a0f04848340104844108141543c48220e6221d0dc6400e412461f8411071028887437190030244dc1208281d54a3a250ec22461901262220d0048244dc12092237474492694864049883422220d00481e911b06a238444018550e06e3304003a04148423877844885c722a030b2006921270e4a612118248819448180182e48e111c0744037040600150207a4611844705f182a16400b2424e2384846080c8f19a394481801a2a88e121c4f840370406801491470d9260640c0610844a0a91e0dc66080080511c361de107291840a80c0dc660800706b09044460866170989054068019824103d2228c24381a8144080a))
def mo255H11 (j : Nat) : Nat := (if j<1 then 0xf828ecde0000e85b1157c31a18d68c062d79f508ea1831afd10eadb7199c0450b11ee4db032daab448a5b46a5340000000609e00010bd7a4418da00004c980d6d3940002f0080000001e0ba69079cff3b40000010a23b0000000390f800024d5180e8ab800043c00003892782b0001875c000000093080000000000000013a1cd3c7816b9db04e62de40f1d398981cce7511bbb44a5840000a088329699000000000000000021f800009f80003842e91033c49563eb5800000000000ccc165de45987614ad41bc000168e12a4000071e400036c800000caa0002d1060e5b9a3710286d48c9338400000002e4a000065740001d5149a4000347c0000000000014b58066a33d54c6a2600000000631592ad5af1b6e67f40000000e3b945000003e6100000003900088a585bf88f4283923a4ca82e701c0000fcb6000330c8000e0e8388000061ffe19de1e2141f54b0001e9011458252c9aa0002299800073f258ac000103ef46e68a40007d9f914008040007a179b3bea132f701b12350e41b019800034a80003ca4800000000000000224e00000000cfa18fc0000000122f0000000000000003a60a2e1c1cc844094300000003511e5fe0000000144d2e30635264080003c1a34e471828f4b84c0000c3d8000000022780001d39ce3442148945c928681000000000002801347fd7afa6b00ee5211d3bc0000000b2fc867d8d63a71d2f099ffec78000745000035348000db4e04888aa0000cb4978b400059c422660002d3e71b7e087225c00021ef428d307c000000000000000000422f0000c1d80005a430000676f54408af0000000010000000040000501a00401801012000000000060000180a00a0140080300c040088050000040100001c080058000020040000700c0000280100000c0080900e018028140000100500400a000000060360340180700401c04000000000020010040180080200000001000002000010020140080080300c004018040020940080300c0000100000600c000010160200380500200c02013000000000000000480080000c0000380301a000010080020000000000a0000080101c0080500b0000100100800000801802000024048010020000180001001c0100000e00c03002000054020010160000200400203400801002018010010020040180505c0000700e0020880000000400c038000080000080500a01800001000004100090060000180100005c008350000540802d0140000280000000401814000004000070000040080000202c0000901e0240180400004400001004010038050060000b800002004010020000380080305604c000000020080700500c00000800000000028070080000200300000402800000018030000000000000000001c0281e00001800001012008008030080000200100200c00000 else (if j<2 then 0xf5c36a171d01c1f392fea1206578db431f6e8e428300000000a2100001c9ad895f97c00034d80000549105c05b20001a6280006dd3000062dc00000000001a45f8e8501d0000000101cee445348f616f3980000001c05400000000000c9776812836000046890cad96ec30a0000000788b304cf66800000007c26d3e20727805ccf345d40006a6b0000a63c0006846f418026cecf00005c9cb7ef0b6724778e206d503d6918b1f341920248000000080b400000000000643de8c1e24311b03b4f427057328a632805e000073be00020c01562f18400024c30000000000000005e3d0000000000015cf4202000340d86318302657084a223da15949852fc9e0442b000006d280009083f0890adfa1c81cda0c785d000032246245a6d12104ad184c40000000410c837cca80000cb7fc4f9ed47962001a00008380000000000000004c5f1c3c00000000000000180f00000000f433449ecf2e80901cee272f0d6060221da86cb14c415baa800018088000717d54524f68000fc6600015264e2239e8000385eca81000108f329a80006206160faaad88c70c7540cee08000022c3894000416f0001224c00045151b66942000000000001e93fcf389b0f4e80000000000000000000000000063e186710aae03db4276096c1a80000000e76453d3055e294e1abe021e1521a8814c4f464420068000000031760001f282235819d041436800006688015200026e9121500000000aa2d8008240f62c0004a4b0000000000010194b98000280f000000000003121000054b1c093ae280000000a0804a3f8d3534bb0c12bba209149507ddcc39a5f00012530c951e640000233000000000b141474000763e60b0b98c43dac181a6d95d6533c98d21fa254c000485600000003aec80000000000000000000001e74400056024409295f4fd21fc9219c060000000000000000000107e0000c7b1c58ea66701fe4c88f2000000000002d3780000000000000000000000a6ec0000000539637440006d0d120a000330ec04042d35924d13401c51c7452e52b0000000000000005e41a2e40002143b4330000000000000000000a49800041f10001a967cb38000000000000004dfc141a000000079e6000000000001651b3c6f7d8cde800058e6e19e877808e000123fc13a8000e016c1888228000000086dbf2a1dd062ace04e23178d9b269471c00000002256819681468470000e508000209200000000000000000018379825b9bae0e4e8c9520d5b9bacae2d202ffe00304e0002a0e0000000000000000000000167792b0212ce38d691a531dd9cd1815394000204200000003eb380dd00000000083800000000002d1881bf0000b3c140200004cdbb6ebd22b10d0001d0480000000104426476a95a7f6177e2576f9e054ca2fa265870e56672cc08778824061e38780d else 0x91eee4b6d268000000123b000000000000c07db2c3446000026b811280003cdcf39ae4e980639a1104eb2d499750140001b056d1992bf43ce0b26a5af00e81378093996000002c800039a0fb8009a05363177cc55765d88d08aa7cd7f94bcc489d32ada43f8e94222dd223ea1a702816d000027040000000318e00000c1cc1de26a81f1a04805235190893ad741380001028c00011ebfaa7b7a2ed829638054c8b80000000000000024ac81280000000000000000001e7340002182000148cd4d3e03a0000387c000726202bc64ec000000010d600026b50000000063d6115d5ec532400024fdf249146da2080002e7e331691e40000000210000014e06121214a01dc690800001b7c5ccd3b8000740a55f04b400005238982feda8000943cb0780000000e058970800061c8c05200000004d4793a8000072cecd40001b8f2f3a8671434c000080415a63bc880c2c6c006f215060fef178000e39347aa6d62a0632f7a0bf4eed54ee3180001a12a8e9a13ca164d287a7e6829c4bd0b8c990000049218985919a20051d2735712e20d1e8d4c69419b70db58e5852611fab90a5d028214b6b0e298a1f307e5e94f2590852e24eb8ce9c3044da20cd519f8050a8b559230d9600c0fc00eb71670716d37214898d8e1788d5f00c4cae482c000728972f3b886b1b3090fb5b068e4568000c2740002c9ec8023020b63811178831a24000161e800081300001942917c0001488749b80002188000007a78320000000304380000001777240b89520000489c50971f2c43069c045ae081d14cf56a2bb11d66b92430ee7eba7b381da51142d48c8ec30286acdc313fe47c07d9c7d78d7dcc541ffcd68c9e780f2174d1a1e855157f8ec00038b6000124db0072a1140eac08c4ccf0a781603172868688f736636f97034598e373f7c80f0800000000003e712a5b011219bd82759be0000e6a8000000000000000000389d00000000000000000016684000787de2c000000000000000099dc05faa0f922aa7fb3133627a89d8668a081632f2264288000691dc3aa0000545368ad4a6000086aa1b238d3f94c070101ab3a4d8d68d7e05b10d20002afa80f0b4ec000000039513b7a166c00000003c9e2344000410bcc9000000003d87e40e68ea93e8000d0880000000457eb31cf0e36dd960df22984a54a72941000060ee8b568960000c3880000000c85e00000000000000000000000000b88600000000000f504743c84f800024bc0000000000000000000000686e000105978f76db100000003d0a1a0200000000e279879d311c12b0be8000000163a3e1df669a213a2b80007a8000008370d07414))
def mo255D12 (_ : Nat) : Nat := 0x110e84880c178206002444483a12203006081800a1084820f06880e0d8c0028440612203a3208008110e0184088c82002042122208504418363000a0e018411888c820020420a122088063000811120e84880c008206012a080844388c0210223004a10848882141106228c01284038020a10462230049110e1300820414880f8c012e0808455c3a10040020305c88c110e1314880c0100820417223044384c041052203e320800b84088c01128c4c28d9099f038a688bf9542523f86b8a80ea108098007fd10ffa41ff0c3fe987fd40ff8a1ff543fe087fd21ffa83ff147fea8ffd61ffa85ff58bfeb05fd71
def mo255H12 (_ : Nat) : Nat := 0x1f5195200029a137fa3666ff0bf2aa00010f000043b2107f29598f430cc000000000055799600019c670f08b9ceba1450025e5484c6b95e8b1830a9b9942000390c36ab1a9824cec775ea13ec6ebc6c769db99cd32e7ccbb8003530b3af3f985dd730a245488b132b271f815c0ca78000e4d80028a120724580000000000000002123574c92e0ac0000000003a9ea7e000fbd812f926000245423443e2810004d21d34000a3ee0a6c9a00033d39768ae000359520388800078c90e04734b5e0976200000001d0000000000000000000000000003b5800000095080018915350007a740013b30e28000000000f8a0ccc3542b8000682d6d80000000002c0d421ad1dc6952502f00041ec0003d0b5d70fc00000002cd008001885cd87deac55ad2d31513344ff320005730000000d1421512a616d000000335e0000000000001fd2aa0202312bcac0005138000864000306800126a0006432efc0000000000000e965d6694c00000000072ad4660000000000f2c00000008b799ce8891968c0d2e0000004999c2a000112f85800000014e68eb2d055c23c800000052c5978002b034d783431189666ca000564f4a3c89993ca9a641819d90d0300000008930003cbd1570001128000000a5180020df249f61ba400000000002ca00000000000000000f70627b33c000000f08046d8f000086152b70dc0c965f923cda2cc080dff3756836000062c0d8b037f4f170c17c29f705715a2c9a04000000000140d00079000000000001cd000111e05b5aef81dc3ead21a0c88fbd78ade9848482726db0001b280000001a94000000ed280000008a8d1a2cba4e00000000000001e74498016c00a000120fd54001791e6589b6745e0f895a2c68384ae42e42310630659858000000000c294280000a1d21eaf2eae40009d30dcf63f02600079a633e85aac59c5511c51d0000000000750000615400087e000721dda7e4396468d8b65fa745e5624000d82f411006c23c7760c704ec07ecd09b19140014d4d30688c000000139fb55182022f620002b7000025b80000000630006a501000000000200018100601010100200048100001008000206008000c00000280202068100600060101003000000008020140e00000580400000000200028100007000081a030301408010000400000200800030180c0008000702a130200406050b0280001008100608080000805010080000000040008
def mo255D13 (_ : Nat) : Nat := 0x10410304ff
def mo255H13 (_ : Nat) : Nat := 0x3e7ca20a00181543cf9912b73006520005000013ab0386e020eaa5140088f8d0032f513ec81fa9d24000000092c00c08b087043040004
def mo255L : Nat → Packing
  | 8 => (49,5,7,0,0,11,0,mo255D8)
  | 9 => (374,4,7,0,0,15,0,mo255D9)
  | 10 => (653,3,7,0,0,16,0,mo255D10)
  | 11 => (216,2,7,0,0,15,0,mo255D11)
  | 12 => (17,1,7,0,0,11,0,mo255D12)
  | 13 => (1,0,7,0,0,0,0,mo255D13)
  | _ => emptyPacking
def mo255I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 17 71 7 11 6 1 mo255H9
  | 10 => lookupWord 156 797 10 14 9 1 mo255H10
  | 11 => lookupWord 315 1373 11 15 10 1 mo255H11
  | 12 => lookupWord 106 467 9 13 8 1 mo255H12
  | 13 => lookupWord 9 41 6 10 5 1 mo255H13
  | _ => fun _ => none
def mo255 : Forest := ⟨1279,13,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_0 : CutRow mo255 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_1 : CutRow mo255 8 1 16 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_17 : CutRow mo255 8 17 32 := mixedCut (pos:=0x60240140c90180a01203) (neg:=0x8c60950a2a40e289428a) (data:=fun _ => 0x7653607525134075765360757653607545038054255340757053618470536174201021750201215007356140073561400735614007356140073561400735615007356150073561505153062056103010073561500735614007356150845173320735614007356150243103322653615002012150523141502431033202012150) rfl (by decide +kernel)
theorem mo255B8 : CutRow mo255 8 0 49 := (@joinRow mo255 8 0 1 48 mo255P8_0 (@joinRow mo255 8 1 16 32 mo255P8_1 mo255P8_17))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_0 : CutRow mo255 9 0 30 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_30 : CutRow mo255 9 30 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_126 : CutRow mo255 9 126 72 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_198 : CutRow mo255 9 198 6 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_204 : CutRow mo255 9 204 96 := mixedCut (pos:=0xc090180485003031201205) (neg:=0x118c16129144a145150a21c) (data:=fun _ => 0x311030203110302054135120981487434713467220102120301304103043941020102120981487543110307002012162020121624803966202012162420121619804873242317171020121613110302031103020241371205604374347134672201021203013041030439410201021205804375431103070201021802010219020102130201021302010213050406130201021302010213020102130201021302010213020102130201021302010213020102130201021303013041030130410453451724803966245345172453451714534517135046161311030203110302054435120743146417431464124137130541351305040613054135130541351308431464131103070611304105413512024137120544351206113041061130410611304106113041061130410611304104534517245345172541351208471868174514681544351205413512024137120541351205413512054135120241371202413712050406130541351205443513054435120311030202010212020102120) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_300 : CutRow mo255 9 300 74 := mixedCut (pos:=0xc12481806028019201205) (neg:=0xc24630542a245150a21c) (data:=fun _ => 0x2010218620102196343541723435417243534120020121624313412002012162020121622313812020102120201021200201216202012162020121620201217202012172020121729110302020102180201021802010218009310380793078307930783053315830093103809310302093103020931030209310302093103020431341202010212079307896201021207930789620102120901303109013031043134120201021202313812020102120431341209013031091103020911030209013031090130310931040209013031090537310020121720201217290130310901303109013031043134120901303109013031090130310901303109013031090130310911030200201216202012162370378620201216232012161671565323431417102012161) rfl (by decide +kernel)
theorem mo255B9 : CutRow mo255 9 0 374 := (@joinRow mo255 9 0 198 176 (@joinRow mo255 9 0 30 168 mo255P9_0 (@joinRow mo255 9 30 96 72 mo255P9_30 mo255P9_126)) (@joinRow mo255 9 198 6 170 mo255P9_198 (@joinRow mo255 9 204 96 74 mo255P9_204 mo255P9_300)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_0 : CutRow mo255 10 0 14 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_14 : CutRow mo255 10 14 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_110 : CutRow mo255 10 110 87 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_197 : CutRow mo255 10 197 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_293 : CutRow mo255 10 293 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_389 : CutRow mo255 10 389 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_485 : CutRow mo255 10 485 59 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_544 : CutRow mo255 10 544 7 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_551 : CutRow mo255 10 551 96 := mixedCut (pos:=0x12030091805048018240c05) (neg:=0x311488c6130544a12a228a21c) (data:=fun _ => 0x32011211012031010120310032011211310202040103230815097414010323040103230401032309170a741815097414010323069146854032011216914685403201121401032304010323091208741912087419170a7418150974103201121401032304010323083504741401032304010323040103230401032309120874193706741835047414010323040103230912087414010323091208741401032304010323040103230401032304010323091208741912087419120874193706741912087418350474191208741531252305312523043127230835147415312523083514741534252305312523043127230534252305312523043127230534252308321474193716741832147418351474145410665454106655312523043127230534252305312523043127230534252306914685469046854531252304312723053425230691468545704285483214741832147419371674183214741835147418321474145410665401032304010323010120310121020201210202012102020) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_647 : CutRow mo255 10 647 6 := mixedCut (pos:=0x180a03) (neg:=0x228a21c) (data:=fun _ => 0x102012212112001020102120201021202112001021120010) rfl (by decide +kernel)
theorem mo255B10 : CutRow mo255 10 0 653 := (@joinRow mo255 10 0 389 264 (@joinRow mo255 10 0 110 279 (@joinRow mo255 10 0 14 96 mo255P10_0 mo255P10_14) (@joinRow mo255 10 110 87 192 mo255P10_110 (@joinRow mo255 10 197 96 96 mo255P10_197 mo255P10_293))) (@joinRow mo255 10 389 155 109 (@joinRow mo255 10 389 96 59 mo255P10_389 mo255P10_485) (@joinRow mo255 10 544 7 102 mo255P10_544 (@joinRow mo255 10 551 96 6 mo255P10_551 mo255P10_647))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_0 : CutRow mo255 11 0 8 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_8 : CutRow mo255 11 8 79 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_87 : CutRow mo255 11 87 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_183 : CutRow mo255 11 183 33 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B11 : CutRow mo255 11 0 216 := (@joinRow mo255 11 0 87 129 (@joinRow mo255 11 0 8 79 mo255P11_0 mo255P11_8) (@joinRow mo255 11 87 96 33 mo255P11_87 mo255P11_183))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P12_0 : CutRow mo255 12 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P12_1 : CutRow mo255 12 1 16 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B12 : CutRow mo255 12 0 17 := (@joinRow mo255 12 0 1 16 mo255P12_0 mo255P12_1)
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
theorem mo255G : graphValid mo255 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255R : Impossible false graph 13 eightInputs.toFinset := by
  rw [show graph = targetOf mo255 by decide +kernel]
  exact mixedRoot (g:=mo255) (top:=13) (i:=0) (before_sound K127 (known_down V127)) mo255G mo255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_8457

open PEqualNP.Outside.L_meta_8457 in
theorem PEqualNP.Outside.L_meta_8457 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 5 && x 6)) t → 14 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo255R g255R ⟨C,hf,by omega,heq⟩
