import Mathlib.LinearAlgebra.Matrix.Adjugate
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_818_aux

def step {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool) (x : Option (Fin s)) :
    Option (Fin s) :=
  x.bind (fun i => n i (p i))

abbrev Good {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool) : Prop :=
  ∀ i : Fin s, (step n p)^[s] (some i) = none

lemma iterate_step_none {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool) :
    ∀ k : ℕ, (step n p)^[k] none = none := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma iterate_step_eq_none_of_le {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool)
    {k m : ℕ} (hkm : k ≤ m) {x : Option (Fin s)} (hx : (step n p)^[k] x = none) :
    (step n p)^[m] x = none := by
  have hm : m = (m - k) + k := by omega
  rw [hm, Function.iterate_add_apply, hx]
  exact iterate_step_none n p (m - k)

lemma iterate_step_ne_none_of_le {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool)
    {k m : ℕ} (hkm : k ≤ m) {x : Option (Fin s)} (hx : (step n p)^[m] x ≠ none) :
    (step n p)^[k] x ≠ none := by
  intro hk
  exact hx (iterate_step_eq_none_of_le n p hkm hk)

lemma exists_simple_cycle_of_not_good {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (p : Fin s → Bool) (hbad : ¬ Good n p) :
    ∃ (L : ℕ) (hL0 : 0 < L) (_ : L ≤ s) (cyc : Fin L → Fin s),
      Function.Injective cyc ∧
      ∀ k : Fin L, n (cyc k) (p (cyc k)) = some (cyc ⟨(k.val + 1) % L, Nat.mod_lt _ hL0⟩) := by
  classical
  have hi0 : ∃ i₀ : Fin s, (step n p)^[s] (some i₀) ≠ none := by
    by_contra h
    push Not at h
    exact hbad h
  rcases hi0 with ⟨i₀, hi₀⟩
  have hne : ∀ k : Fin (s + 1), (step n p)^[k.val] (some i₀) ≠ none := by
    intro k
    exact iterate_step_ne_none_of_le n p (Nat.lt_succ_iff.mp k.isLt) hi₀
  let seq : Fin (s + 1) → Fin s := fun k =>
    ((step n p)^[k.val] (some i₀)).get (Option.isSome_iff_ne_none.mpr (hne k))
  have hseq : ∀ k : Fin (s + 1), (step n p)^[k.val] (some i₀) = some (seq k) := by
    intro k
    exact (Option.some_get (Option.isSome_iff_ne_none.mpr (hne k))).symm
  have hseq_step : ∀ k : ℕ, ∀ hk : k < s,
      n (seq ⟨k, by omega⟩) (p (seq ⟨k, by omega⟩)) = some (seq ⟨k + 1, by omega⟩) := by
    intro k hk
    have h1 : (step n p)^[k + 1] (some i₀) = step n p ((step n p)^[k] (some i₀)) :=
      Function.iterate_succ_apply' (step n p) k (some i₀)
    rw [hseq ⟨k + 1, by omega⟩, hseq ⟨k, by omega⟩] at h1
    exact h1.symm
  have hex : ∃ b : ℕ, ∃ hb : b ≤ s, ∃ a : ℕ, ∃ ha : a < b,
      seq ⟨a, by omega⟩ = seq ⟨b, by omega⟩ := by
    have hlt : Fintype.card (Fin s) < Fintype.card (Fin (s + 1)) := by simp
    rcases Fintype.exists_ne_map_eq_of_card_lt seq hlt with ⟨x, y, hxy, hEq⟩
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with hlt' | hgt'
    · exact ⟨y.val, Nat.lt_succ_iff.mp y.isLt, x.val, hlt', hEq⟩
    · exact ⟨x.val, Nat.lt_succ_iff.mp x.isLt, y.val, hgt', hEq.symm⟩
  let b := Nat.find hex
  have hb_spec := Nat.find_spec hex
  rcases hb_spec with ⟨hbs, a, hab, hseq_ab⟩
  have hb_min : ∀ b' < b, ¬ (∃ hb' : b' ≤ s, ∃ a' : ℕ, ∃ ha' : a' < b',
      seq ⟨a', by omega⟩ = seq ⟨b', by omega⟩) := fun b' hb' => Nat.find_min hex hb'
  let L := b - a
  have hL0 : 0 < L := by omega
  have hLs : L ≤ s := by omega
  let cyc : Fin L → Fin s := fun k => seq ⟨a + k.val, by omega⟩
  refine ⟨L, hL0, hLs, cyc, ?_, ?_⟩
  · intro x y hxy
    by_contra hne_xy
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne_xy) with hlt' | hgt'
    · exact hb_min (a + y.val) (by omega) ⟨by omega, a + x.val, by omega, hxy⟩
    · exact hb_min (a + x.val) (by omega) ⟨by omega, a + y.val, by omega, hxy.symm⟩
  · intro k
    have hstep_k := hseq_step (a + k.val) (by omega)
    by_cases hlast : k.val + 1 < L
    · have hmod : (k.val + 1) % L = k.val + 1 := Nat.mod_eq_of_lt hlast
      have hidx : (⟨a + (k.val + 1) % L, by omega⟩ : Fin (s + 1)) =
          ⟨a + k.val + 1, by omega⟩ := by
        apply Fin.ext
        dsimp
        omega
      dsimp [cyc]
      rw [hidx]
      exact hstep_k
    · have hmod : (k.val + 1) % L = 0 := by
        have hk1 : k.val + 1 = L := by omega
        rw [hk1, Nat.mod_self]
      have hidx0 : (⟨a + (k.val + 1) % L, by omega⟩ : Fin (s + 1)) =
          ⟨a, by omega⟩ := by
        apply Fin.ext
        dsimp
        omega
      have hidxb : (⟨a + k.val + 1, by omega⟩ : Fin (s + 1)) =
          ⟨b, by omega⟩ := by
        apply Fin.ext
        dsimp
        omega
      dsimp [cyc]
      rw [hidx0, hseq_ab, ← hidxb]
      exact hstep_k

lemma not_good_of_cycle {s L : ℕ} (hL0 : 0 < L)
    (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool)
    (cyc : Fin L → Fin s)
    (hcyc : ∀ k : Fin L, n (cyc k) (p (cyc k)) = some (cyc ⟨(k.val + 1) % L, Nat.mod_lt _ hL0⟩)) :
    ¬ Good n p := by
  have hiter : ∀ m : ℕ,
      (step n p)^[m] (some (cyc ⟨0, hL0⟩)) = some (cyc ⟨m % L, Nat.mod_lt m hL0⟩) := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      change n (cyc ⟨m % L, Nat.mod_lt m hL0⟩) (p (cyc ⟨m % L, Nat.mod_lt m hL0⟩)) = _
      rw [hcyc ⟨m % L, Nat.mod_lt m hL0⟩]
      congr 2
      apply Fin.ext
      dsimp
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  intro hgood
  have h1 := hgood (cyc ⟨0, hL0⟩)
  rw [hiter s] at h1
  exact Option.some_ne_none _ h1

def shiftPerm {L : ℕ} (hL0 : 0 < L) : Equiv.Perm (Fin L) where
  toFun k := ⟨(k.val + 1) % L, Nat.mod_lt _ hL0⟩
  invFun k := ⟨(k.val + L - 1) % L, Nat.mod_lt _ hL0⟩
  left_inv k := by
    apply Fin.ext
    dsimp
    by_cases hk : k.val + 1 < L
    · rw [Nat.mod_eq_of_lt hk]
      have h1 : k.val + 1 + L - 1 = k.val + L := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
    · have hk1 : k.val + 1 = L := by omega
      rw [hk1, Nat.mod_self]
      have h1 : 0 + L - 1 = k.val := by omega
      rw [h1, Nat.mod_eq_of_lt k.isLt]
  right_inv k := by
    apply Fin.ext
    dsimp
    by_cases hk : k.val = 0
    · rw [hk]
      have h1 : 0 + L - 1 = L - 1 := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega : L - 1 < L)]
      have h2 : L - 1 + 1 = L := by omega
      rw [h2, Nat.mod_self]
    · have h1 : (k.val + L - 1) % L = k.val - 1 := by
        have h2 : k.val + L - 1 = (k.val - 1) + L := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : k.val - 1 < L)]
      rw [h1]
      have h3 : k.val - 1 + 1 = k.val := by omega
      rw [h3, Nat.mod_eq_of_lt k.isLt]

lemma iterate_shiftPerm {L : ℕ} (hL0 : 0 < L) :
    ∀ (m : ℕ) (k : Fin L),
      (shiftPerm hL0 : Fin L → Fin L)^[m] k = ⟨(k.val + m) % L, Nat.mod_lt _ hL0⟩ := by
  intro m
  induction m with
  | zero =>
    intro k
    apply Fin.ext
    simp [Nat.mod_eq_of_lt k.isLt]
  | succ m ih =>
    intro k
    rw [Function.iterate_succ_apply', ih k]
    apply Fin.ext
    change ((k.val + m) % L + 1) % L = (k.val + (m + 1)) % L
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

lemma iterate_conj_perm {α β : Type*} (e : α ≃ β) (f : Equiv.Perm α) :
    ∀ (m : ℕ) (x : β),
      ((e.symm.trans (f.trans e) : Equiv.Perm β) : β → β)^[m] x =
      e ((f : α → α)^[m] (e.symm x)) := by
  intro m
  induction m with
  | zero =>
    intro x
    simp
  | succ m ih =>
    intro x
    rw [Function.iterate_succ_apply', ih x, Function.iterate_succ_apply']
    simp

lemma unique_bad_iff_ring {s : ℕ} (hs : 0 < s) (n : Fin s → Bool → Option (Fin s)) :
    (∃ c : Fin s → Bool, ¬ Good n c ∧ ∀ p : Fin s → Bool, ¬ Good n p → p = c) ↔
    ∃ (perm : Equiv.Perm (Fin s)) (c : Fin s → Bool),
      (∀ i, n i (c i) = some (perm i) ∧ n i (!(c i)) = none) ∧
      ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j := by
  constructor
  · rintro ⟨c, hc_bad, hc_uniq⟩
    rcases exists_simple_cycle_of_not_good n c hc_bad with
      ⟨L, hL0, hLs, cyc, hcyc_inj, hcyc_step⟩
    have hcyc_surj : Function.Surjective cyc := by
      intro j
      by_contra hnot
      push Not at hnot
      let p := Function.update c j (!(c j))
      have hp_ne : p ≠ c := by
        intro hEq
        have h1 : p j = c j := congrFun hEq j
        simp [p] at h1
      have hp_bad : ¬ Good n p := by
        apply not_good_of_cycle hL0 n p cyc
        intro k
        have hne : cyc k ≠ j := hnot k
        have hpk : p (cyc k) = c (cyc k) := Function.update_of_ne hne (!(c j)) c
        rw [hpk]
        exact hcyc_step k
      exact hp_ne (hc_uniq p hp_bad)
    let e : Fin L ≃ Fin s := Equiv.ofBijective cyc ⟨hcyc_inj, hcyc_surj⟩
    have hL_eq : L = s := by
      have hc := Fintype.card_congr e
      simpa using hc
    let perm : Equiv.Perm (Fin s) := e.symm.trans ((shiftPerm hL0).trans e)
    have hperm_step : ∀ i : Fin s, n i (c i) = some (perm i) := by
      intro i
      have hk := hcyc_step (e.symm i)
      have hek : cyc (e.symm i) = i := e.apply_symm_apply i
      rw [hek] at hk
      rw [hk]
      rfl
    have hperm_trans : ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j := by
      intro i j
      let a := (e.symm i).val
      let b := (e.symm j).val
      let k := (b + L - a) % L
      have hk_lt : k < s := by
        rw [← hL_eq]
        exact Nat.mod_lt _ hL0
      refine ⟨k, hk_lt, ?_⟩
      rw [iterate_conj_perm e (shiftPerm hL0) k i, iterate_shiftPerm hL0 k (e.symm i)]
      have hmod : (a + k) % L = b := by
        have ha : a < L := (e.symm i).isLt
        have hb : b < L := (e.symm j).isLt
        dsimp [k]
        by_cases hab : a ≤ b
        · have h1 : (b + L - a) % L = b - a := by
            have h2 : b + L - a = (b - a) + L := by omega
            rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [h1]
          have h3 : a + (b - a) = b := by omega
          rw [h3, Nat.mod_eq_of_lt hb]
        · have h1 : (b + L - a) % L = b + L - a := Nat.mod_eq_of_lt (by omega)
          rw [h1]
          have h2 : a + (b + L - a) = b + L := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
      have hfin : (⟨(a + k) % L, Nat.mod_lt _ hL0⟩ : Fin L) = e.symm j := by
        apply Fin.ext
        exact hmod
      rw [hfin]
      exact e.apply_symm_apply j
    refine ⟨perm, c, ?_, hperm_trans⟩
    intro i
    refine ⟨hperm_step i, ?_⟩
    by_contra hne_none
    rcases Option.ne_none_iff_exists'.mp hne_none with ⟨y, hy⟩
    rcases hperm_trans y i with ⟨r, hr_lt, hr_eq⟩
    let p := Function.update c i (!(c i))
    have hp_ne : p ≠ c := by
      intro hEq
      have h1 : p i = c i := congrFun hEq i
      simp [p] at h1
    let cyc' : Fin (r + 1) → Fin s := fun t =>
      if t.val = 0 then i else (perm : Fin s → Fin s)^[t.val - 1] y
    have hcyc'_bad : ¬ Good n p := by
      apply not_good_of_cycle (Nat.succ_pos r) n p cyc'
      intro t
      by_cases ht0 : t.val = 0
      · have hct : cyc' t = i := by
          dsimp [cyc']
          simp only [ht0, ite_true]
        rw [hct]
        have hpi : p i = !(c i) := Function.update_self i (!(c i)) c
        rw [hpi, hy]
        congr 1
        by_cases hr0 : r = 0
        · subst hr0
          have hmod : (t.val + 1) % (0 + 1) = 0 := Nat.mod_one _
          dsimp [cyc']
          simp only [hmod, ite_true]
          simpa using hr_eq
        · have hmod : (t.val + 1) % (r + 1) = 1 := by
            rw [ht0]
            exact Nat.mod_eq_of_lt (by omega)
          simp only [cyc', hmod, one_ne_zero, ite_false, Nat.sub_self, Function.iterate_zero,
            id_eq]
      · have hct : cyc' t = (perm : Fin s → Fin s)^[t.val - 1] y := by
          dsimp [cyc']
          simp only [ht0, ite_false]
        rw [hct]
        have hne_i : (perm : Fin s → Fin s)^[t.val - 1] y ≠ i := by
          intro hEq
          rw [← hr_eq] at hEq
          rw [iterate_conj_perm e (shiftPerm hL0), iterate_conj_perm e (shiftPerm hL0)] at hEq
          have hEq1 := e.injective hEq
          rw [iterate_shiftPerm hL0, iterate_shiftPerm hL0] at hEq1
          have hval : ((e.symm y).val + (t.val - 1)) % L = ((e.symm y).val + r) % L :=
            congrArg Fin.val hEq1
          have hu : (e.symm y).val < L := (e.symm y).isLt
          have hm1 : t.val - 1 < r := by omega
          have hrL : r < L := by omega
          have hmod1 : ((e.symm y).val + (t.val - 1)) % L =
              if (e.symm y).val + (t.val - 1) < L then (e.symm y).val + (t.val - 1)
              else (e.symm y).val + (t.val - 1) - L := by
            split_ifs with hlt
            · exact Nat.mod_eq_of_lt hlt
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          have hmod2 : ((e.symm y).val + r) % L =
              if (e.symm y).val + r < L then (e.symm y).val + r
              else (e.symm y).val + r - L := by
            split_ifs with hlt
            · exact Nat.mod_eq_of_lt hlt
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [hmod1, hmod2] at hval
          split_ifs at hval <;> omega
        have hpt : p ((perm : Fin s → Fin s)^[t.val - 1] y) =
            c ((perm : Fin s → Fin s)^[t.val - 1] y) :=
          Function.update_of_ne hne_i (!(c i)) c
        rw [hpt, hperm_step]
        congr 1
        by_cases hlast : t.val + 1 < r + 1
        · have hmod : (t.val + 1) % (r + 1) = t.val + 1 := Nat.mod_eq_of_lt hlast
          simp only [cyc', hmod, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
          have hidx : t.val + 1 - 1 = (t.val - 1) + 1 := by omega
          rw [hidx, Function.iterate_succ_apply']
        · have htr : t.val = r := by omega
          have hmod : (t.val + 1) % (r + 1) = 0 := by
            rw [htr, Nat.mod_self]
          dsimp [cyc']
          simp only [hmod, ite_true]
          have hidx : (t.val - 1).succ = r := by omega
          rw [← Function.iterate_succ_apply' (perm : Fin s → Fin s) (t.val - 1) y, hidx, hr_eq]
    exact hp_ne (hc_uniq p hcyc'_bad)
  · rintro ⟨perm, c, hstep, htrans⟩
    refine ⟨c, ?_, ?_⟩
    · have hiter_c : ∀ m i, (step n c)^[m] (some i) = some ((perm : Fin s → Fin s)^[m] i) := by
        intro m
        induction m with
        | zero =>
          intro i
          rfl
        | succ m ih =>
          intro i
          rw [Function.iterate_succ_apply', ih i, Function.iterate_succ_apply']
          exact (hstep _).1
      intro hgood
      have h0 := hgood ⟨0, hs⟩
      rw [hiter_c s ⟨0, hs⟩] at h0
      exact Option.some_ne_none _ h0
    · intro p hp_bad
      by_contra hne
      rcases Function.ne_iff.mp hne with ⟨j, hj⟩
      have hpj_eq : p j = !(c j) := by
        cases h1 : p j <;> cases h2 : c j <;> simp_all
      have hnj : n j (p j) = none := by
        rw [hpj_eq]
        exact (hstep j).2
      apply hp_bad
      intro i
      have horb : ∀ m : ℕ, (step n p)^[m] (some i) = none ∨
          (step n p)^[m] (some i) = some ((perm : Fin s → Fin s)^[m] i) := by
        intro m
        induction m with
        | zero =>
          exact Or.inr rfl
        | succ m ih =>
          rcases ih with hnone | hsome
          · left
            rw [Function.iterate_succ_apply', hnone]
            rfl
          · rw [Function.iterate_succ_apply', hsome]
            by_cases hpc : p ((perm : Fin s → Fin s)^[m] i) = c ((perm : Fin s → Fin s)^[m] i)
            · right
              change n _ (p _) = _
              rw [hpc, (hstep _).1, Function.iterate_succ_apply']
            · left
              have hnot : p ((perm : Fin s → Fin s)^[m] i) = !(c ((perm : Fin s → Fin s)^[m] i)) := by
                cases h1 : p ((perm : Fin s → Fin s)^[m] i) <;>
                cases h2 : c ((perm : Fin s → Fin s)^[m] i) <;> simp_all
              change n _ (p _) = none
              rw [hnot]
              exact (hstep _).2
      rcases htrans i j with ⟨k, hk_lt, hk_eq⟩
      have hk1 : (step n p)^[k + 1] (some i) = none := by
        rcases horb k with hnone | hsome
        · rw [Function.iterate_succ_apply', hnone]
          rfl
        · rw [Function.iterate_succ_apply', hsome, hk_eq]
          exact hnj
      exact iterate_step_eq_none_of_le n p (Nat.succ_le_of_lt hk_lt) hk1

def rowVec {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (i : Fin s) (b : Bool) (j : Fin s) : ℤ :=
  (if j = i then 1 else 0) - (if n i b = some j then 1 else 0)

def matM {s : ℕ} (n : Fin s → Bool → Option (Fin s)) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j => rowVec n i false j + rowVec n i true j

def matA {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool) :
    Matrix (Fin s) (Fin s) ℤ :=
  fun i j => rowVec n i (p i) j

def matS {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (S : Finset (Fin s)) (p₀ : Fin s → Bool) :
    Matrix (Fin s) (Fin s) ℤ :=
  fun i j => if i ∈ S then rowVec n i false j + rowVec n i true j else rowVec n i (p₀ i) j

lemma det_matS {s : ℕ} (n : Fin s → Bool → Option (Fin s)) :
    ∀ (S : Finset (Fin s)) (p₀ : Fin s → Bool),
      (matS n S p₀).det =
      ∑ p ∈ (Finset.univ : Finset (Fin s → Bool)).filter (fun p => ∀ i, i ∉ S → p i = p₀ i),
        (matA n p).det := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro p₀
    have hmat : matS n ∅ p₀ = matA n p₀ := by
      ext i j
      simp [matS, matA]
    have hfilt :
        (Finset.univ : Finset (Fin s → Bool)).filter (fun p => ∀ i, i ∉ (∅ : Finset (Fin s)) → p i = p₀ i) =
        {p₀} := by
      ext p
      simp [funext_iff]
    rw [hmat, hfilt, Finset.sum_singleton]
  | insert a S ha ih =>
    intro p₀
    have hupd_sum : matS n (insert a S) p₀ =
        (matS n S p₀).updateRow a (rowVec n a false + rowVec n a true) := by
      ext i j
      by_cases hia : i = a
      · subst hia
        simp [matS]
      · simp [matS, hia]
    have hupd_bit : ∀ b : Bool,
        (matS n S p₀).updateRow a (rowVec n a b) = matS n S (Function.update p₀ a b) := by
      intro b
      ext i j
      by_cases hia : i = a
      · subst hia
        simp [matS, ha]
      · simp [matS, hia]
    rw [hupd_sum, Matrix.det_updateRow_add, hupd_bit false, hupd_bit true, ih, ih]
    let S0 := (Finset.univ : Finset (Fin s → Bool)).filter
      (fun p => ∀ i, i ∉ S → p i = Function.update p₀ a false i)
    let S1 := (Finset.univ : Finset (Fin s → Bool)).filter
      (fun p => ∀ i, i ∉ S → p i = Function.update p₀ a true i)
    let Sfull := (Finset.univ : Finset (Fin s → Bool)).filter
      (fun p => ∀ i, i ∉ insert a S → p i = p₀ i)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro p hp0 hp1
      simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hp0 hp1
      have h0 := hp0 a ha
      have h1 := hp1 a ha
      simp at h0 h1
      rw [h0] at h1
      exact Bool.false_ne_true h1
    have hunion : S0 ∪ S1 = Sfull := by
      ext p
      simp only [S0, S1, Sfull, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (h0 | h1) i hi
        · have hiS : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
          have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a S)
          simpa [Function.update_of_ne hia] using h0 i hiS
        · have hiS : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
          have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a S)
          simpa [Function.update_of_ne hia] using h1 i hiS
      · intro h
        cases hpa : p a
        · left
          intro i hiS
          by_cases hia : i = a
          · subst hia
            simp [hpa]
          · rw [Function.update_of_ne hia]
            exact h i (by simp [hia, hiS])
        · right
          intro i hiS
          by_cases hia : i = a
          · subst hia
            simp [hpa]
          · rw [Function.update_of_ne hia]
            exact h i (by simp [hia, hiS])
    rw [← Finset.sum_union hdisj, hunion]

lemma det_matM_eq_sum {s : ℕ} (n : Fin s → Bool → Option (Fin s)) :
    (matM n).det = ∑ p : Fin s → Bool, (matA n p).det := by
  have h1 := det_matS n Finset.univ (fun _ => false)
  have hM : matS n Finset.univ (fun _ => false) = matM n := by
    ext i j
    simp [matS, matM]
  have hF : (Finset.univ : Finset (Fin s → Bool)).filter
      (fun p => ∀ i, i ∉ (Finset.univ : Finset (Fin s)) → p i = false) = Finset.univ := by
    ext p
    simp
  rw [hM, hF] at h1
  exact h1

lemma det_matA_of_not_good {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool)
    (hbad : ¬ Good n p) : (matA n p).det = 0 := by
  classical
  rcases exists_simple_cycle_of_not_good n p hbad with
    ⟨L, hL0, _, cyc, hcyc_inj, hcyc_step⟩
  let Cyc : Finset (Fin s) := Finset.univ.image cyc
  let w : Fin s → ℤ := fun i => if i ∈ Cyc then 1 else 0
  have hwA : Matrix.vecMul w (matA n p) = 0 := by
    ext j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    have hsum1 : ∑ i : Fin s, w i * matA n p i j =
        ∑ i ∈ Cyc, matA n p i j := by
      have hfilt : Finset.univ.filter (fun i => i ∈ Cyc) = Cyc := by
        ext i
        simp
      calc
        ∑ i : Fin s, w i * matA n p i j
            = ∑ i : Fin s, if i ∈ Cyc then matA n p i j else 0 := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ Cyc <;> simp [w, hi]
        _ = ∑ i ∈ Finset.univ.filter (fun i => i ∈ Cyc), matA n p i j := by
                rw [Finset.sum_filter]
        _ = ∑ i ∈ Cyc, matA n p i j := by rw [hfilt]
    rw [hsum1]
    simp only [matA, rowVec, Finset.sum_sub_distrib]
    have himg1 : (∑ i ∈ Cyc, if j = i then (1 : ℤ) else 0) =
        ∑ k : Fin L, if j = cyc k then (1 : ℤ) else 0 := by
      dsimp [Cyc]
      rw [Finset.sum_image (fun x _ y _ h => hcyc_inj h)]
    have himg2 : (∑ i ∈ Cyc, if n i (p i) = some j then (1 : ℤ) else 0) =
        ∑ k : Fin L, if j = cyc (shiftPerm hL0 k) then (1 : ℤ) else 0 := by
      dsimp [Cyc]
      rw [Finset.sum_image (fun x _ y _ h => hcyc_inj h)]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hcyc_step k]
      change (if some (cyc (shiftPerm hL0 k)) = some j then (1 : ℤ) else 0) = _
      simp [eq_comm]
    rw [himg1, himg2]
    have hshift : (∑ k : Fin L, if j = cyc (shiftPerm hL0 k) then (1 : ℤ) else 0) =
        ∑ k : Fin L, if j = cyc k then (1 : ℤ) else 0 :=
      Equiv.sum_comp (shiftPerm hL0) (fun k => if j = cyc k then (1 : ℤ) else 0)
    rw [hshift, sub_self]
  have hmul : Matrix.vecMul w (matA n p * (matA n p).adjugate) = 0 := by
    rw [← Matrix.vecMul_vecMul, hwA, Matrix.zero_vecMul]
  rw [Matrix.mul_adjugate] at hmul
  let u := cyc ⟨0, hL0⟩
  have hu : u ∈ Cyc := Finset.mem_image.mpr ⟨⟨0, hL0⟩, Finset.mem_univ _, rfl⟩
  have hval := congrFun hmul u
  simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, Matrix.one_apply, Pi.zero_apply] at hval
  have hsum : (∑ i : Fin s, w i * ((matA n p).det • if i = u then (1 : ℤ) else 0)) =
      (matA n p).det := by
    rw [Finset.sum_eq_single u]
    · simp [w, hu]
    · intro i _ hiu
      simp [hiu]
    · intro h
      exact False.elim (h (Finset.mem_univ u))
  rw [hsum] at hval
  exact hval

lemma det_matA_of_good {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool)
    (hgood : Good n p) : (matA n p).det = 1 := by
  classical
  have hex : ∀ i : Fin s, ∃ k : ℕ, (step n p)^[k] (some i) = none := fun i => ⟨s, hgood i⟩
  let depth : Fin s → ℕ := fun i => Nat.find (hex i)
  have hdepth_spec : ∀ i, (step n p)^[depth i] (some i) = none := fun i =>
    Nat.find_spec (hex i)
  have hdepth_pos : ∀ i, 0 < depth i := by
    intro i
    by_contra h0
    have hd0 : depth i = 0 := by omega
    have h1 := hdepth_spec i
    rw [hd0] at h1
    exact Option.some_ne_none i h1
  have hdepth_lt : ∀ i j, n i (p i) = some j → depth j < depth i := by
    intro i j hij
    have hpos := hdepth_pos i
    have h1 := hdepth_spec i
    have hEq : depth i = (depth i - 1) + 1 := by omega
    rw [hEq, Function.iterate_succ_apply] at h1
    change (step n p)^[depth i - 1] (n i (p i)) = none at h1
    rw [hij] at h1
    have hle : depth j ≤ depth i - 1 := Nat.find_min' (hex j) h1
    omega
  have hno_self : ∀ i, n i (p i) ≠ some i := by
    intro i hi
    have hlt := hdepth_lt i i hi
    omega
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin s))]
  · simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, id_eq]
    refine Finset.prod_eq_one ?_
    intro i _
    simp [matA, rowVec, hno_self i]
  · intro σ _ hσ1
    suffices hprod : (∏ i : Fin s, matA n p (σ i) i) = 0 by
      simp [hprod]
    by_contra hne0
    have hterm : ∀ i : Fin s, matA n p (σ i) i ≠ 0 := by
      intro i hi
      exact hne0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin s)), depth i ≤ depth (σ i) := by
      intro i _
      have hi := hterm i
      by_cases hEq : i = σ i
      · exact le_of_eq (congrArg depth hEq)
      · have hstep_i : n (σ i) (p (σ i)) = some i := by
          by_contra hns
          apply hi
          simp [matA, rowVec, hEq, hns]
        exact le_of_lt (hdepth_lt (σ i) i hstep_i)
    have hsum_eq : ∑ i : Fin s, depth i = ∑ i : Fin s, depth (σ i) :=
      (Equiv.sum_comp σ depth).symm
    have heq_depth : ∀ i ∈ (Finset.univ : Finset (Fin s)), depth i = depth (σ i) :=
      (Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq
    have hσ_eq : σ = 1 := by
      apply Equiv.ext
      intro i
      by_contra hne_i
      have hEq : i ≠ σ i := Ne.symm hne_i
      have hstep_i : n (σ i) (p (σ i)) = some i := by
        by_contra hns
        apply hterm i
        simp [matA, rowVec, hEq, hns]
      have hlt := hdepth_lt (σ i) i hstep_i
      have heqd := heq_depth i (Finset.mem_univ i)
      omega
    exact hσ1 hσ_eq
  · intro h
    exact False.elim (h (Finset.mem_univ 1))

lemma det_matM_eq_card {s : ℕ} (n : Fin s → Bool → Option (Fin s)) :
    (matM n).det =
    (((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
      ∀ i : Fin s, (step n p)^[s] (some i) = none)).card : ℤ) := by
  rw [det_matM_eq_sum]
  calc
    (∑ p : Fin s → Bool, (matA n p).det)
        = ∑ p : Fin s → Bool, if Good n p then (1 : ℤ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro p _
            by_cases hp : Good n p
            · simp [hp, det_matA_of_good n p hp]
            · simp [hp, det_matA_of_not_good n p hp]
    _ = (((Finset.univ : Finset (Fin s → Bool)).filter (fun p => Good n p)).card : ℤ) := by
            simp [Finset.sum_boole]
    _ = (((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          ∀ i : Fin s, (step n p)^[s] (some i) = none)).card : ℤ) := by
            rfl

lemma sum_rowVec_mul {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (v : Fin s → ℝ)
    (i : Fin s) (b : Bool) :
    (∑ j : Fin s, ((rowVec n i b j : ℤ) : ℝ) * v j) = v i - (n i b).elim (0 : ℝ) v := by
  have hsplit : ∀ j : Fin s, ((rowVec n i b j : ℤ) : ℝ) * v j =
      (if j = i then v j else 0) - (if n i b = some j then v j else 0) := by
    intro j
    dsimp [rowVec]
    simp only [Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul, ite_mul,
      one_mul, zero_mul]
  simp_rw [hsplit, Finset.sum_sub_distrib]
  have hs1 : (∑ j : Fin s, if j = i then v j else 0) = v i := by
    simp
  have hs2 : (∑ j : Fin s, if n i b = some j then v j else 0) = (n i b).elim (0 : ℝ) v := by
    cases hnb : n i b with
    | none => simp
    | some k =>
      simp only [Option.elim_some, Option.some.injEq]
      have hcomm : (∑ j : Fin s, if k = j then v j else 0) =
          ∑ j : Fin s, if j = k then v j else 0 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simp [eq_comm]
      rw [hcomm]
      simp
  rw [hs1, hs2]

lemma option_elim_split {α : Type*} (o : Option α) (a : ℤ) (v : α → ℝ) :
    o.elim (a : ℝ) v = ((o.elim a (fun _ => 0) : ℤ) : ℝ) + o.elim (0 : ℝ) v := by
  cases o with
  | none => simp
  | some x => simp

lemma denom_clear {s : ℕ} (n : Fin s → Bool → Option (Fin s))
    (g : Fin s → Bool → ℤ) (v : Fin s → ℝ)
    (hv : ∀ i, 2 * v i = ∑ b : Bool, (n i b).elim (g i b : ℝ) v) :
    ∀ i, ∃ z : ℤ, ((matM n).det : ℝ) * v i = z := by
  let M := matM n
  let rhs : Fin s → ℤ := fun i => ∑ b : Bool, (n i b).elim (g i b) (fun _ => 0)
  have hMeq : ∀ i : Fin s, (∑ j : Fin s, ((M i j : ℤ) : ℝ) * v j) = (rhs i : ℝ) := by
    intro i
    have hsum : (∑ j : Fin s, ((M i j : ℤ) : ℝ) * v j) =
        (∑ j : Fin s, ((rowVec n i false j : ℤ) : ℝ) * v j) +
        (∑ j : Fin s, ((rowVec n i true j : ℤ) : ℝ) * v j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [M, matM, add_mul]
    rw [hsum, sum_rowVec_mul, sum_rowVec_mul]
    have hvi := hv i
    rw [Fintype.sum_bool] at hvi
    rw [option_elim_split (n i true) (g i true) v,
        option_elim_split (n i false) (g i false) v] at hvi
    have hrhs : (rhs i : ℝ) =
        (((n i true).elim (g i true) (fun _ => 0) : ℤ) : ℝ) +
        (((n i false).elim (g i false) (fun _ => 0) : ℤ) : ℝ) := by
      change ((∑ b : Bool, (n i b).elim (g i b) (fun _ => 0) : ℤ) : ℝ) = _
      rw [Fintype.sum_bool, Int.cast_add]
    linarith
  let zvec : Fin s → ℤ := M.adjugate.mulVec rhs
  intro i
  refine ⟨zvec i, ?_⟩
  have h1 : (∑ k : Fin s, ((M.adjugate i k : ℤ) : ℝ) * (rhs k : ℝ)) = (zvec i : ℝ) := by
    dsimp [zvec, Matrix.mulVec, dotProduct]
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Int.cast_mul]
  rw [← h1]
  have h2 : (∑ k : Fin s, ((M.adjugate i k : ℤ) : ℝ) * (rhs k : ℝ)) =
      ∑ j : Fin s, (((M.adjugate * M) i j : ℤ) : ℝ) * v j := by
    calc
      (∑ k : Fin s, ((M.adjugate i k : ℤ) : ℝ) * (rhs k : ℝ))
          = ∑ k : Fin s, ((M.adjugate i k : ℤ) : ℝ) *
              (∑ j : Fin s, ((M k j : ℤ) : ℝ) * v j) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [hMeq k]
      _ = ∑ k : Fin s, ∑ j : Fin s, ((M.adjugate i k : ℤ) : ℝ) *
              (((M k j : ℤ) : ℝ) * v j) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [Finset.mul_sum]
      _ = ∑ j : Fin s, ∑ k : Fin s, ((M.adjugate i k : ℤ) : ℝ) *
              (((M k j : ℤ) : ℝ) * v j) := Finset.sum_comm
      _ = ∑ j : Fin s, (((M.adjugate * M) i j : ℤ) : ℝ) * v j := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.sum_mul, mul_assoc]
  rw [h2, Matrix.adjugate_mul]
  rw [Finset.sum_eq_single i]
  · simp [M]
  · intro j _ hji
    simp [Ne.symm hji]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

end PEqualNP.Outside.L_lib_818_aux

theorem PEqualNP.Outside.L_lib_818 : (∀ s : ℕ, 0 < s → ∀ n : Fin s → Bool → Option (Fin s),
  let step := fun (p : Fin s → Bool) (x : Option (Fin s)) => x.bind (fun i => n i (p i))
  let F := ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
    ∀ i : Fin s, (step p)^[s] (some i) = none)).card
  let ring := ∃ (perm : Equiv.Perm (Fin s)) (c : Fin s → Bool),
    (∀ i, n i (c i) = some (perm i) ∧ n i (!(c i)) = none) ∧
    ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j
  0 < F → F ≤ 2^s ∧ (F+1 = 2^s ↔ ring) ∧
    ∀ (g : Fin s → Bool → ℤ) (v : Fin s → ℝ),
      (∀ i, 2*v i = ∑ b : Bool, (n i b).elim (g i b : ℝ) v) →
      ∀ i, ∃ z : ℤ, (F : ℝ)*v i = z) := by
  intro s hs n step F ring _
  have hcard_univ : (Finset.univ : Finset (Fin s → Bool)).card = 2 ^ s := by
    simp
  have hF_le : F ≤ 2 ^ s := by
    calc
      F ≤ (Finset.univ : Finset (Fin s → Bool)).card := Finset.card_filter_le _ _
      _ = 2 ^ s := hcard_univ
  refine ⟨hF_le, ?_, ?_⟩
  · have hgood_eq :
        ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          ∀ i : Fin s, (step p)^[s] (some i) = none)) =
        ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          PEqualNP.Outside.L_lib_818_aux.Good n p)) := by
      rfl
    have hsplit : F +
        ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          ¬ PEqualNP.Outside.L_lib_818_aux.Good n p)).card = 2 ^ s := by
      calc
        F + ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
            ¬ PEqualNP.Outside.L_lib_818_aux.Good n p)).card
            = (Finset.univ : Finset (Fin s → Bool)).card := by
                dsimp only [F]
                rw [hgood_eq]
                have hdisj : Disjoint
                    ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
                      PEqualNP.Outside.L_lib_818_aux.Good n p))
                    ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
                      ¬ PEqualNP.Outside.L_lib_818_aux.Good n p)) := by
                  rw [Finset.disjoint_left]
                  intro p hp1 hp2
                  exact (Finset.mem_filter.mp hp2).2 (Finset.mem_filter.mp hp1).2
                have hunion :
                    ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
                      PEqualNP.Outside.L_lib_818_aux.Good n p)) ∪
                    ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
                      ¬ PEqualNP.Outside.L_lib_818_aux.Good n p)) = Finset.univ := by
                  ext p
                  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
                    iff_true]
                  exact em _
                rw [← Finset.card_union_of_disjoint hdisj, hunion]
        _ = 2 ^ s := hcard_univ
    have h1 : F + 1 = 2 ^ s ↔
        ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          ¬ PEqualNP.Outside.L_lib_818_aux.Good n p)).card = 1 := by
      omega
    rw [h1, Finset.card_eq_one]
    have h2 : (∃ c : Fin s → Bool,
        (Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          ¬ PEqualNP.Outside.L_lib_818_aux.Good n p) = {c}) ↔
        (∃ c : Fin s → Bool, ¬ PEqualNP.Outside.L_lib_818_aux.Good n c ∧
          ∀ p : Fin s → Bool, ¬ PEqualNP.Outside.L_lib_818_aux.Good n p → p = c) := by
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨c, ?_, ?_⟩
        · have hmem : c ∈ (Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
              ¬ PEqualNP.Outside.L_lib_818_aux.Good n p) := by
            rw [hc]
            exact Finset.mem_singleton_self c
          exact (Finset.mem_filter.mp hmem).2
        · intro p hp
          have hmem : p ∈ ({c} : Finset (Fin s → Bool)) := by
            rw [← hc]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
          exact Finset.mem_singleton.mp hmem
      · rintro ⟨c, hc_bad, hc_uniq⟩
        refine ⟨c, ?_⟩
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨hc_uniq p, fun hp => hp ▸ hc_bad⟩
    rw [h2]
    exact PEqualNP.Outside.L_lib_818_aux.unique_bad_iff_ring hs n
  · intro g v hv i
    have hdet := PEqualNP.Outside.L_lib_818_aux.det_matM_eq_card n
    have hclear := PEqualNP.Outside.L_lib_818_aux.denom_clear n g v hv i
    rcases hclear with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hdet_real : ((PEqualNP.Outside.L_lib_818_aux.matM n).det : ℝ) = (F : ℝ) := by
      have h1 : ((PEqualNP.Outside.L_lib_818_aux.matM n).det : ℝ) = (((F : ℤ) : ℝ)) := by
        exact_mod_cast hdet
      simpa using h1
    rw [← hdet_real]
    exact hz
