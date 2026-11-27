import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_287_aux

open PEqualNP.ProofComplexity

abbrev BaseV := Fin 4
abbrev Edge := Fin 6
abbrev BigV := Fin 4 ⊕ (Fin 6 × ℕ)

def src : Edge → BaseV × Bool :=
  ![(0, true), (2, true), (0, false), (0, false), (1, false), (1, false)]

def dst : Edge → BaseV × Bool :=
  ![(1, false), (3, false), (2, true), (3, true), (2, true), (3, true)]

def baseClause (e : Edge) : Clause BaseV :=
  {((src e).1, !(src e).2), ((dst e).1, (dst e).2)}

def baseF : Set (Clause BaseV) := Set.range baseClause

theorem baseClause_injective : Function.Injective baseClause := by
  decide

def lit (t : ℕ) (e : Edge) (j : ℕ) : Literal BigV :=
  if j = 0 then ((Sum.inl (src e).1 : BigV), (src e).2)
  else if j = t then ((Sum.inl (dst e).1 : BigV), (dst e).2)
  else ((Sum.inr (e, j) : BigV), true)

theorem lit_zero (t : ℕ) (e : Edge) :
    lit t e 0 = ((Sum.inl (src e).1 : BigV), (src e).2) := by
  simp [lit]

theorem lit_end {t : ℕ} (ht : 0 < t) (e : Edge) :
    lit t e t = ((Sum.inl (dst e).1 : BigV), (dst e).2) := by
  simp [lit, show t ≠ 0 by omega]

theorem lit_mid {t j : ℕ} (h0 : j ≠ 0) (ht : j ≠ t) (e : Edge) :
    lit t e j = ((Sum.inr (e, j) : BigV), true) := by
  simp [lit, h0, ht]

def step (t : ℕ) (e : Edge) (j : ℕ) : Clause BigV :=
  {((lit t e j).1, !(lit t e j).2), lit t e (j + 1)}

def big (t : ℕ) : Set (Clause BigV) :=
  {C | ∃ e j, j < t ∧ C = step t e j}

def liftClause (C : Clause BaseV) : Clause BigV :=
  C.image (fun l => (Sum.inl l.1, l.2))

theorem liftClause_baseClause (e : Edge) :
    liftClause (baseClause e) =
      {((Sum.inl (src e).1 : BigV), !(src e).2), ((Sum.inl (dst e).1 : BigV), (dst e).2)} := by
  simp [liftClause, baseClause]

theorem step_one (e : Edge) : step 1 e 0 = liftClause (baseClause e) := by
  rw [liftClause_baseClause]
  simp [step, lit]

theorem step_injective {t : ℕ} (ht : 0 < t) {e1 e2 : Edge} {j1 j2 : ℕ}
    (hj1 : j1 < t) (hj2 : j2 < t) (heq : step t e1 j1 = step t e2 j2) :
    e1 = e2 ∧ j1 = j2 := by
  by_cases ht1 : t = 1
  · subst ht1
    have h1 : j1 = 0 := by omega
    have h2 : j2 = 0 := by omega
    subst h1; subst h2
    rw [step_one, step_one] at heq
    have hbase : baseClause e1 = baseClause e2 := by
      ext l
      have hiff : (Sum.inl l.1, l.2) ∈ liftClause (baseClause e1) ↔
          (Sum.inl l.1, l.2) ∈ liftClause (baseClause e2) := by rw [heq]
      simpa [liftClause] using hiff
    exact ⟨baseClause_injective hbase, rfl⟩
  · have ht2 : 2 ≤ t := by omega
    by_cases h0 : j1 = 0
    · subst h0
      have hj20 : j2 = 0 := by
        by_contra hne
        have hmem : ((Sum.inr (e2, j2) : BigV), false) ∈ step t e2 j2 := by
          have : lit t e2 j2 = ((Sum.inr (e2, j2) : BigV), true) := by
            simp [lit, hne, show j2 ≠ t by omega]
          rw [step, this]
          simp
        rw [← heq] at hmem
        have h1ne : (1 : ℕ) ≠ t := by omega
        simp [step, lit, h1ne] at hmem
      subst hj20
      have h1ne : (1 : ℕ) ≠ t := by omega
      have hmem : ((Sum.inr (e1, 1) : BigV), true) ∈ step t e1 0 := by
        simp [step, lit, h1ne]
      rw [heq] at hmem
      simp [step, lit, h1ne] at hmem
      exact ⟨hmem, rfl⟩
    · have hmem : ((Sum.inr (e1, j1) : BigV), false) ∈ step t e1 j1 := by
        have : lit t e1 j1 = ((Sum.inr (e1, j1) : BigV), true) := by
          simp [lit, h0, show j1 ≠ t by omega]
        rw [step, this]
        simp
      rw [heq] at hmem
      by_cases h20 : j2 = 0
      · subst h20
        have h1ne : (1 : ℕ) ≠ t := by omega
        simp [step, lit, h1ne] at hmem
      · have hlit2 : lit t e2 j2 = ((Sum.inr (e2, j2) : BigV), true) := by
          simp [lit, h20, show j2 ≠ t by omega]
        have hlit2' : (lit t e2 (j2 + 1)).2 = false → ∃ v : BaseV, (lit t e2 (j2 + 1)).1 = Sum.inl v := by
          intro hf
          by_cases hjt : j2 + 1 = t
          · rw [hjt, lit_end ht]; exact ⟨(dst e2).1, rfl⟩
          · rw [lit_mid (Nat.succ_ne_zero _) hjt] at hf; simp at hf
        rw [step, hlit2] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton, Bool.not_true] at hmem
        rcases hmem with h1 | h2
        · have hpair := Prod.mk.inj (Sum.inr.inj (Prod.mk.inj h1).1)
          exact hpair
        · have hf : (lit t e2 (j2 + 1)).2 = false := by rw [← h2]
          obtain ⟨v, hv⟩ := hlit2' hf
          have h1 : (Sum.inr (e1, j1) : BigV) = (lit t e2 (j2 + 1)).1 := congrArg Prod.fst h2
          rw [hv] at h1
          exact absurd h1 (by simp)

def baseWit : Edge → BaseV → Bool
  | 0 => ![true, true, false, false]
  | 1 => ![false, false, true, true]
  | 2 => ![false, true, false, true]
  | 3 => ![false, true, true, false]
  | 4 => ![true, false, false, true]
  | 5 => ![true, false, true, false]

theorem baseF_indispensable (e : Edge) :
    (∀ e' : Edge, e' ≠ e → ClauseSat (baseWit e) (baseClause e')) ∧
    ¬ ClauseSat (baseWit e) (baseClause e) := by
  fin_cases e <;> constructor
  · intro e' hne; fin_cases e' <;> simp_all [ClauseSat, baseClause, baseWit, src, dst]
  · simp [ClauseSat, baseClause, baseWit, src, dst]
  · intro e' hne; fin_cases e' <;> simp_all [ClauseSat, baseClause, baseWit, src, dst]
  · simp [ClauseSat, baseClause, baseWit, src, dst]
  · intro e' hne; fin_cases e' <;> simp_all [ClauseSat, baseClause, baseWit, src, dst]
  · simp [ClauseSat, baseClause, baseWit, src, dst]
  · intro e' hne; fin_cases e' <;> simp_all [ClauseSat, baseClause, baseWit, src, dst]
  · simp [ClauseSat, baseClause, baseWit, src, dst]
  · intro e' hne; fin_cases e' <;> simp_all [ClauseSat, baseClause, baseWit, src, dst]
  · simp [ClauseSat, baseClause, baseWit, src, dst]
  · intro e' hne; fin_cases e' <;> simp_all [ClauseSat, baseClause, baseWit, src, dst]
  · simp [ClauseSat, baseClause, baseWit, src, dst]

def bigWit (e : Edge) (j : ℕ) : BigV → Bool
  | Sum.inl v => baseWit e v
  | Sum.inr (e', r) =>
      if e' = e then decide (r ≤ j)
      else decide (baseWit e (dst e').1 = (dst e').2)

theorem big_indispensable {t : ℕ} (ht : 0 < t) (e : Edge) (j : ℕ) (hj : j < t) :
    ∀ e' j', j' < t → (e' ≠ e ∨ j' ≠ j) → ClauseSat (bigWit e j) (step t e' j') := by
  intro e' j' hj' hne
  by_cases hee : e' = e
  · subst e'
    have hjj : j' ≠ j := hne.resolve_left (fun h => h rfl)
    by_cases hlt : j' < j
    · refine ⟨lit t e (j' + 1), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
      rw [lit_mid (Nat.succ_ne_zero _) (by omega)]
      simp [bigWit, show j' + 1 ≤ j by omega]
    · refine ⟨((lit t e j').1, !(lit t e j').2), Finset.mem_insert_self _ _, ?_⟩
      rw [lit_mid (by omega) (by omega)]
      simp [bigWit, show ¬ j' ≤ j by omega]
  · have hsat := (baseF_indispensable e).1 e' hee
    by_cases hdst : baseWit e (dst e').1 = (dst e').2
    · refine ⟨lit t e' (j' + 1), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
      by_cases hjt : j' + 1 = t
      · rw [hjt, lit_end ht]; simp [bigWit, hdst]
      · rw [lit_mid (Nat.succ_ne_zero _) hjt]; simp [bigWit, hee, hdst]
    · have hsrc : baseWit e (src e').1 = !(src e').2 := by
        rcases hsat with ⟨l, hl, hlv⟩
        simp only [baseClause, Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · exact hlv
        · exact absurd hlv hdst
      refine ⟨((lit t e' j').1, !(lit t e' j').2), Finset.mem_insert_self _ _, ?_⟩
      by_cases hj0 : j' = 0
      · simp [lit, hj0, bigWit, hsrc]
      · have hnet : j' ≠ t := by omega
        simp [lit, hj0, hnet, bigWit, hee, hdst]

theorem resolvent_sound {V : Type} [DecidableEq V] {a : V → Bool}
    {C D R : Clause V} (hres : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) :
    ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := hres
  cases hv : a v
  · rcases hC with ⟨l, hl, hlv⟩
    refine ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hl⟩), hlv⟩
    intro heq; subst heq; simp [hv] at hlv
  · rcases hD with ⟨l, hl, hlv⟩
    refine ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl⟩), hlv⟩
    intro heq; subst heq; simp [hv] at hlv

theorem derivation_sound {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {a : V → Bool} (ha : Satisfies a F) {π : List (Clause V)} (hπ : IsDerivation F π) :
    ∀ C ∈ π, ClauseSat a C := by
  induction hπ with
  | nil => intro C hC; simp at hC
  | ax _ hmem ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC'
    · exact ha C hmem
    · exact ih C hC'
  | res _ hC hD hres ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE'
    · exact resolvent_sound hres (ih _ hC) (ih _ hD)
    · exact ih E hE'

theorem not_sat_of_refutation {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (href : IsRefutation F π) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  have h := derivation_sound ha href.1 ∅ href.2
  rcases h with ⟨l, hl, _⟩
  exact Finset.notMem_empty l hl

theorem derivation_witness {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (hπ : IsDerivation F π) :
    ∃ w : Fin π.length → Option (Fin π.length × Fin π.length),
      ∀ i : Fin π.length,
        match w i with
        | none => π[i] ∈ F
        | some (j, k) => i.val < j.val ∧ i.val < k.val ∧ IsResolvent π[j] π[k] π[i] := by
  induction hπ with
  | nil => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | @ax π C _ hmem ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨fun i => if h : i.val = 0 then none else
      match w ⟨i.val - 1, by have := i.isLt; simp only [List.length_cons] at this; omega⟩ with
      | none => none
      | some (j, k) => some (⟨j.val + 1, by simp⟩, ⟨k.val + 1, by simp⟩), fun i => ?_⟩
    by_cases h0 : i.val = 0
    · simp only [h0, dite_true]
      have h0eq : (C :: π)[i] = C := by cases i with | mk v hv => simp only at h0; subst h0; rfl
      rw [h0eq]; exact hmem
    · simp only [h0, dite_false]
      have hi_lt : i.val - 1 < π.length := by have := i.isLt; simp only [List.length_cons] at this; omega
      have hwi := hw ⟨i.val - 1, hi_lt⟩
      have hidx : (C :: π)[i] = π[i.val - 1]'hi_lt := by
        cases i with | mk v hv => cases v with | zero => exact absurd rfl h0 | succ v' => rfl
      cases hwv : w ⟨i.val - 1, hi_lt⟩ with
      | none =>
        rw [hwv] at hwi
        simpa [hidx] using hwi
      | some jk =>
        rcases jk with ⟨j, k⟩
        rw [hwv] at hwi
        rcases hwi with ⟨hj, hk, hres⟩
        refine ⟨by dsimp at hj ⊢; omega, by dsimp at hk ⊢; omega, ?_⟩
        simpa [hidx] using hres
  | @res π C D R _ hC hD hres ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨j0, hj0_lt, hj0⟩ := List.mem_iff_getElem.mp hC
    obtain ⟨k0, hk0_lt, hk0⟩ := List.mem_iff_getElem.mp hD
    refine ⟨fun i => if h : i.val = 0 then
        some (⟨j0 + 1, by simp; omega⟩, ⟨k0 + 1, by simp; omega⟩)
      else match w ⟨i.val - 1, by have := i.isLt; simp only [List.length_cons] at this; omega⟩ with
      | none => none
      | some (j, k) => some (⟨j.val + 1, by simp⟩, ⟨k.val + 1, by simp⟩), fun i => ?_⟩
    by_cases h0 : i.val = 0
    · simp only [h0, dite_true]
      have h0eq : (R :: π)[i] = R := by cases i with | mk v hv => simp only at h0; subst h0; rfl
      refine ⟨by omega, by omega, ?_⟩
      simpa [h0eq, hj0, hk0] using hres
    · simp only [h0, dite_false]
      have hi_lt : i.val - 1 < π.length := by have := i.isLt; simp only [List.length_cons] at this; omega
      have hwi := hw ⟨i.val - 1, hi_lt⟩
      have hidx : (R :: π)[i] = π[i.val - 1]'hi_lt := by
        cases i with | mk v hv => cases v with | zero => exact absurd rfl h0 | succ v' => rfl
      cases hwv : w ⟨i.val - 1, hi_lt⟩ with
      | none =>
        rw [hwv] at hwi
        simpa [hidx] using hwi
      | some jk =>
        rcases jk with ⟨j, k⟩
        rw [hwv] at hwi
        rcases hwi with ⟨hj, hk, hres'⟩
        refine ⟨by dsimp at hj ⊢; omega, by dsimp at hk ⊢; omega, ?_⟩
        simpa [hidx] using hres'

theorem isDerivation_of_witness {V : Type} [DecidableEq V] {F : Set (Clause V)} :
    ∀ (π : List (Clause V)),
      (∃ w : Fin π.length → Option (Fin π.length × Fin π.length),
        ∀ i : Fin π.length,
          match w i with
          | none => π[i] ∈ F
          | some (j, k) => i.val < j.val ∧ i.val < k.val ∧ IsResolvent π[j] π[k] π[i]) →
      IsDerivation F π
  | [], _ => IsDerivation.nil
  | C :: π, ⟨w, hw⟩ => by
    have htail : IsDerivation F π := by
      apply isDerivation_of_witness π
      let w' : Fin π.length → Option (Fin π.length × Fin π.length) := fun i =>
        match hwi : w ⟨i.val + 1, by simp⟩ with
        | none => none
        | some (j, k) =>
            have hsp := hw ⟨i.val + 1, by simp⟩
            have hj0 : 0 < j.val := by rw [hwi] at hsp; dsimp at hsp; omega
            have hk0 : 0 < k.val := by rw [hwi] at hsp; dsimp at hsp; omega
            some (⟨j.val - 1, by have := j.isLt; simp only [List.length_cons] at this; omega⟩,
                  ⟨k.val - 1, by have := k.isLt; simp only [List.length_cons] at this; omega⟩)
      refine ⟨w', fun i => ?_⟩
      have hspec := hw ⟨i.val + 1, by simp⟩
      cases hwi : w ⟨i.val + 1, by simp⟩ with
      | none =>
        have hw'i : w' i = none := by dsimp only [w']; split <;> simp_all
        rw [hw'i]; rw [hwi] at hspec; simpa using hspec
      | some jk =>
        rcases jk with ⟨j, k⟩
        rw [hwi] at hspec
        rcases hspec with ⟨hj, hk, hres⟩
        have hjlt : j.val - 1 < π.length := by have := j.isLt; simp only [List.length_cons] at this; omega
        have hklt : k.val - 1 < π.length := by have := k.isLt; simp only [List.length_cons] at this; omega
        have hw'i : w' i = some (⟨j.val - 1, hjlt⟩, ⟨k.val - 1, hklt⟩) := by
          dsimp only [w']; split <;> simp_all
        rw [hw'i]
        have hj1 : (C :: π)[j] = π[j.val - 1]'hjlt := by
          cases j with | mk jv hjv => cases jv with | zero => dsimp at hj; omega | succ jv' => rfl
        have hk1 : (C :: π)[k] = π[k.val - 1]'hklt := by
          cases k with | mk kv hkv => cases kv with | zero => dsimp at hk; omega | succ kv' => rfl
        refine ⟨by dsimp at hj ⊢; omega, by dsimp at hk ⊢; omega, ?_⟩
        simpa [hj1, hk1] using hres
    have h0 := hw ⟨0, by simp⟩
    cases hw0 : w ⟨0, by simp⟩ with
    | none =>
      rw [hw0] at h0
      exact IsDerivation.ax htail h0
    | some jk =>
      rcases jk with ⟨j, k⟩
      rw [hw0] at h0
      rcases h0 with ⟨hj, hk, hres⟩
      have hjlt : j.val - 1 < π.length := by have := j.isLt; simp only [List.length_cons] at this; omega
      have hklt : k.val - 1 < π.length := by have := k.isLt; simp only [List.length_cons] at this; omega
      have hj1 : (C :: π)[j] = π[j.val - 1]'hjlt := by
        cases j with | mk jv hjv => cases jv with | zero => omega | succ jv' => rfl
      have hk1 : (C :: π)[k] = π[k.val - 1]'hklt := by
        cases k with | mk kv hkv => cases kv with | zero => omega | succ kv' => rfl
      rw [hj1, hk1] at hres
      exact IsDerivation.res htail (List.getElem_mem _) (List.getElem_mem _) hres

theorem isDerivation_drop {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (hπ : IsDerivation F π) : ∀ k, IsDerivation F (π.drop k) := by
  induction hπ with
  | nil => intro k; simp [IsDerivation.nil]
  | ax h1 hmem ih =>
    intro k
    cases k with
    | zero => exact IsDerivation.ax h1 hmem
    | succ k => exact ih k
  | res h1 hC hD hres ih =>
    intro k
    cases k with
    | zero => exact IsDerivation.res h1 hC hD hres
    | succ k => exact ih k

theorem witness_erase_unused {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (w : Fin π.length → Option (Fin π.length × Fin π.length))
    (hw : ∀ i : Fin π.length,
      match w i with
      | none => π[i] ∈ F
      | some (j, k) => i.val < j.val ∧ i.val < k.val ∧ IsResolvent π[j] π[k] π[i])
    (u : Fin π.length)
    (hunused : ∀ p : Fin π.length, ∀ j k, w p = some (j, k) → j ≠ u ∧ k ≠ u)
    (hne_emp : π[u] ≠ ∅) (hemp : ∅ ∈ π) :
    ∃ π', IsRefutation F π' ∧ π'.length < π.length := by
  let π' := π.eraseIdx u.val
  have hlen : π'.length = π.length - 1 := List.length_eraseIdx_of_lt u.isLt
  have hmap_lt : ∀ x : ℕ, x < π'.length → (if x < u.val then x else x + 1) < π.length := by
    intro x hx; split_ifs <;> omega
  let lift : Fin π'.length → Fin π.length := fun i =>
    ⟨if i.val < u.val then i.val else i.val + 1, hmap_lt i.val i.isLt⟩
  have hget : ∀ i : Fin π'.length, π'[i] = π[lift i] := by
    intro i
    dsimp only [π', lift]
    by_cases hi : i.val < u.val
    · simp only [hi, ite_true]
      exact List.getElem_eraseIdx_of_lt i.isLt hi
    · simp only [hi, ite_false]
      exact List.getElem_eraseIdx_of_ge i.isLt (by omega)
  let shrink : ∀ x : Fin π.length, x ≠ u → Fin π'.length := fun x hx =>
    ⟨if x.val < u.val then x.val else x.val - 1, by
      have hne : x.val ≠ u.val := fun h => hx (Fin.ext h)
      split_ifs <;> omega⟩
  have hlift_shrink : ∀ (x : Fin π.length) (hx : x ≠ u), lift (shrink x hx) = x := by
    intro x hx
    have hne : x.val ≠ u.val := fun h => hx (Fin.ext h)
    apply Fin.ext
    dsimp only [lift, shrink]
    by_cases hlt : x.val < u.val
    · simp [hlt]
    · have hge : ¬ x.val - 1 < u.val := by omega
      simp only [hlt, ite_false, hge]
      omega
  have hlt_shrink : ∀ (i : Fin π'.length) (x : Fin π.length) (hx : x ≠ u),
      (lift i).val < x.val → i.val < (shrink x hx).val := by
    intro i x hx hlt
    have hne : x.val ≠ u.val := fun h => hx (Fin.ext h)
    dsimp only [lift, shrink] at hlt ⊢
    split_ifs at hlt ⊢ <;> omega
  have hderiv : IsDerivation F π' := by
    apply isDerivation_of_witness π'
    let w' : Fin π'.length → Option (Fin π'.length × Fin π'.length) := fun i =>
      match hwi : w (lift i) with
      | none => none
      | some (j, k) =>
          have hne := hunused (lift i) j k hwi
          some (shrink j hne.1, shrink k hne.2)
    refine ⟨w', fun i => ?_⟩
    have hspec := hw (lift i)
    cases hwi : w (lift i) with
    | none =>
      have hw'i : w' i = none := by dsimp only [w']; split <;> simp_all
      rw [hw'i]; rw [hwi] at hspec; rw [hget i]; exact hspec
    | some jk =>
      rcases jk with ⟨j, k⟩
      have hne := hunused (lift i) j k hwi
      have hw'i : w' i = some (shrink j hne.1, shrink k hne.2) := by dsimp only [w']; split <;> simp_all
      rw [hw'i]; rw [hwi] at hspec
      rcases hspec with ⟨hj, hk, hres⟩
      refine ⟨hlt_shrink i j hne.1 hj, hlt_shrink i k hne.2 hk, ?_⟩
      rw [hget, hget, hget, hlift_shrink j hne.1, hlift_shrink k hne.2]
      exact hres
  have hemp' : (∅ : Clause V) ∈ π' := by
    obtain ⟨m, hm, hmeq⟩ := List.mem_iff_getElem.mp hemp
    have hmu : (⟨m, hm⟩ : Fin π.length) ≠ u := by
      intro h
      rw [← h] at hne_emp
      exact hne_emp hmeq
    have h1 := hget (shrink ⟨m, hm⟩ hmu)
    rw [hlift_shrink ⟨m, hm⟩ hmu] at h1
    change π'[shrink ⟨m, hm⟩ hmu] = π[m] at h1
    rw [hmeq] at h1
    rw [← h1]
    exact List.getElem_mem _
  exact ⟨π', ⟨hderiv, hemp'⟩, by have := u.isLt; omega⟩

theorem ax_line_of_indispensable {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (w : Fin π.length → Option (Fin π.length × Fin π.length))
    (hw : ∀ i : Fin π.length,
      match w i with
      | none => π[i] ∈ F
      | some (j, k) => i.val < j.val ∧ i.val < k.val ∧ IsResolvent π[j] π[k] π[i])
    (hemp : (∅ : Clause V) ∈ π) {C : Clause V}
    (hsat : Satisfiable (F \ {C})) :
    ∃ i : Fin π.length, w i = none ∧ π[i] = C := by
  by_contra hno
  push Not at hno
  have hderiv : IsDerivation (F \ {C}) π := by
    apply isDerivation_of_witness π
    refine ⟨w, fun i => ?_⟩
    have hwi := hw i
    cases hwv : w i with
    | none =>
      rw [hwv] at hwi
      exact ⟨hwi, hno i hwv⟩
    | some jk =>
      rw [hwv] at hwi
      exact hwi
  exact not_sat_of_refutation ⟨hderiv, hemp⟩ hsat

inductive IsDerivCount {V : Type} [DecidableEq V] (F : Set (Clause V)) :
    List (Clause V) → ℕ → Prop
  | nil : IsDerivCount F [] 0
  | ax {π : List (Clause V)} {r : ℕ} {C : Clause V} :
      IsDerivCount F π r → C ∈ F → IsDerivCount F (C :: π) r
  | res {π : List (Clause V)} {r : ℕ} {C D R : Clause V} :
      IsDerivCount F π r → C ∈ π → D ∈ π → IsResolvent C D R → IsDerivCount F (R :: π) (r + 1)

theorem isDerivCount_append {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π1 π2 : List (Clause V)} {r1 r2 : ℕ}
    (h1 : IsDerivCount F π1 r1) (h2 : IsDerivCount F π2 r2) :
    IsDerivCount F (π1 ++ π2) (r1 + r2) := by
  induction h1 with
  | nil => simpa using h2
  | ax _ hmem ih => exact IsDerivCount.ax ih hmem
  | res _ hC hD hres ih =>
    have hstep := IsDerivCount.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hres
    have hr : r1 + 1 + r2 = r1 + r2 + 1 := by omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

theorem isDerivCount_baseF_to_refutation {π : List (Clause BaseV)} {r : ℕ}
    (h : IsDerivCount baseF π r) (hemp : (∅ : Clause BaseV) ∈ π) :
    ∃ π', IsRefutation baseF π' ∧ π'.length ≤ 6 + r := by
  have hbase0 : IsDerivation baseF
      [baseClause 0, baseClause 1, baseClause 2, baseClause 3, baseClause 4, baseClause 5] := by
    refine IsDerivation.ax (IsDerivation.ax (IsDerivation.ax (IsDerivation.ax
      (IsDerivation.ax (IsDerivation.ax IsDerivation.nil ⟨5, rfl⟩) ⟨4, rfl⟩)
      ⟨3, rfl⟩) ⟨2, rfl⟩) ⟨1, rfl⟩) ⟨0, rfl⟩
  have hbase0_mem : ∀ C ∈ baseF,
      C ∈ ([baseClause 0, baseClause 1, baseClause 2, baseClause 3, baseClause 4, baseClause 5] :
        List (Clause BaseV)) := by
    rintro C ⟨e, rfl⟩
    fin_cases e <;> simp
  have haux : ∀ (π : List (Clause BaseV)) (r : ℕ), IsDerivCount baseF π r →
      ∃ π', IsDerivation baseF π' ∧ (∀ C ∈ π, C ∈ π') ∧
        (∀ C ∈ baseF, C ∈ π') ∧ π'.length ≤ 6 + r := by
    intro π r h
    induction h with
    | nil => exact ⟨_, hbase0, by simp, hbase0_mem, by simp⟩
    | ax _ hmem ih =>
      obtain ⟨π', hd, hsub, hall, hlen⟩ := ih
      refine ⟨π', hd, ?_, hall, hlen⟩
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact hall _ hmem
      · exact hsub _ hC'
    | res _ hC hD hres ih =>
      obtain ⟨π', hd, hsub, hall, hlen⟩ := ih
      refine ⟨_ :: π', IsDerivation.res hd (hsub _ hC) (hsub _ hD) hres, ?_, ?_, by simp; omega⟩
      · intro E hE
        rcases List.mem_cons.mp hE with rfl | hE'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub _ hE')
      · intro E hE
        exact List.mem_cons_of_mem _ (hall _ hE)
  obtain ⟨π', hd, hsub, _, hlen⟩ := haux π r h
  exact ⟨π', ⟨hd, hsub ∅ hemp⟩, hlen⟩

theorem baseF_min_len : ∀ π : List (Clause BaseV), IsRefutation baseF π → 12 ≤ π.length := by
  classical
  intro π0 href0
  by_contra hlt
  have hex : ∃ k, ∃ π : List (Clause BaseV), IsRefutation baseF π ∧ π.length = k :=
    ⟨π0.length, π0, href0, rfl⟩
  let mlen := Nat.find hex
  obtain ⟨π, href, hmlen⟩ := Nat.find_spec hex
  have hmin : ∀ π', IsRefutation baseF π' → π.length ≤ π'.length := by
    intro π' href'
    rw [hmlen]
    exact Nat.find_min' hex ⟨π', href', rfl⟩
  have hle11 : π.length ≤ 11 := by
    have := hmin π0 href0; omega
  have hpos : 0 < π.length := by
    cases π with
    | nil => simp [IsRefutation] at href
    | cons _ _ => simp
  have hhead_emp : π[0] = ∅ := by
    obtain ⟨i, hi, hieq⟩ := List.mem_iff_getElem.mp href.2
    by_cases hi0 : i = 0
    · subst hi0; exact hieq
    · exfalso
      have hdrop_d : IsDerivation baseF (π.drop i) := isDerivation_drop href.1 i
      have hdrop_e : (∅ : Clause BaseV) ∈ π.drop i := by
        have hlen_d : 0 < (π.drop i).length := by simp; omega
        have hget_d : (π.drop i)[0] = π[i] := by simp
        rw [hieq] at hget_d
        rw [← hget_d]
        exact List.getElem_mem hlen_d
      have hmin_d := hmin (π.drop i) ⟨hdrop_d, hdrop_e⟩
      simp at hmin_d
      omega
  have hnz_ne_emp : ∀ i : Fin π.length, i.val ≠ 0 → π[i] ≠ ∅ := by
    intro i hi0 heq
    have hdrop_d : IsDerivation baseF (π.drop i.val) := isDerivation_drop href.1 i.val
    have hdrop_e : (∅ : Clause BaseV) ∈ π.drop i.val := by
      have hlen_d : 0 < (π.drop i.val).length := by simp
      have hget_d : (π.drop i.val)[0] = π[i] := by simp
      rw [heq] at hget_d
      rw [← hget_d]
      exact List.getElem_mem hlen_d
    have hmin_d := hmin (π.drop i.val) ⟨hdrop_d, hdrop_e⟩
    simp at hmin_d
    omega
  obtain ⟨w, hw⟩ := derivation_witness href.1
  have hused : ∀ i : Fin π.length, i.val ≠ 0 →
      ∃ p : Fin π.length, ∃ j k, w p = some (j, k) ∧ (j = i ∨ k = i) := by
    intro i hi0
    by_contra hno
    push Not at hno
    obtain ⟨π', href', hlen'⟩ := witness_erase_unused w hw i hno (hnz_ne_emp i hi0) href.2
    have := hmin π' href'
    omega
  let axSet : Finset (Fin π.length) := Finset.univ.filter (fun i => w i = none)
  let resSet : Finset (Fin π.length) := Finset.univ.filter (fun i => (w i).isSome)
  have hpart : axSet.card + resSet.card = π.length := by
    have hdisj : Disjoint axSet resSet := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      have h1' : w i = none := (Finset.mem_filter.mp h1).2
      have h2' : (w i).isSome = true := (Finset.mem_filter.mp h2).2
      rw [h1'] at h2'; simp at h2'
    rw [← Finset.card_union_of_disjoint hdisj]
    have hun : axSet ∪ resSet = Finset.univ := by
      ext i
      simp only [axSet, resSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases w i <;> simp
    rw [hun, Finset.card_univ, Fintype.card_fin]
  have hax_has : ∀ e : Edge, ∃ i ∈ axSet, π[i] = baseClause e := by
    intro e
    have hsat : Satisfiable (baseF \ {baseClause e}) := by
      refine ⟨baseWit e, fun C hC => ?_⟩
      rcases hC with ⟨⟨e', rfl⟩, hne⟩
      have hee : e' ≠ e := fun h => hne (by simp [h])
      exact (baseF_indispensable e).1 e' hee
    obtain ⟨i, hwi, hieq⟩ := ax_line_of_indispensable w hw href.2 hsat
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hwi⟩, hieq⟩
  have hax_ge : 6 ≤ axSet.card := by
    choose f hf using hax_has
    have hinj : Set.InjOn f (↑(Finset.univ : Finset Edge) : Set Edge) := by
      intro e1 _ e2 _ hfeq
      have h1 := (hf e1).2
      have h2 := (hf e2).2
      rw [hfeq] at h1
      exact baseClause_injective (h1.symm.trans h2)
    have hsub : (Finset.univ : Finset Edge).image f ⊆ axSet := by
      intro i hi
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hi
      exact (hf e).1
    calc 6 = (Finset.univ : Finset Edge).card := by decide
      _ = ((Finset.univ : Finset Edge).image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ axSet.card := Finset.card_le_card hsub
  let slots : Finset (Fin π.length × Bool) := resSet ×ˢ Finset.univ
  let slotVal : Fin π.length × Bool → Fin π.length := fun pb =>
    match w pb.1 with
    | none => ⟨0, hpos⟩
    | some (j, k) => if pb.2 = false then j else k
  have hslot_nz : ∀ pb ∈ slots, slotVal pb ∈ Finset.univ.erase ⟨0, hpos⟩ := by
    intro pb hpb
    have hres : (w pb.1).isSome = true := (Finset.mem_filter.mp (Finset.mem_product.mp hpb).1).2
    have hspec := hw pb.1
    cases hwp : w pb.1 with
    | none => rw [hwp] at hres; simp at hres
    | some jk =>
      rcases jk with ⟨j, k⟩
      rw [hwp] at hspec
      rcases hspec with ⟨hj, hk, _⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      dsimp only [slotVal]
      rw [hwp]
      intro h0
      cases hpb2 : pb.2
      · simp [hpb2] at h0; have := congrArg Fin.val h0; simp at this; omega
      · simp [hpb2] at h0; have := congrArg Fin.val h0; simp at this; omega
  have hslot_surj : Finset.univ.erase ⟨0, hpos⟩ ⊆ slots.image slotVal := by
    intro i hi
    have hi0 : i.val ≠ 0 := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
    obtain ⟨p, j, k, hwp, hor⟩ := hused i hi0
    have hp : p ∈ resSet := Finset.mem_filter.mpr ⟨Finset.mem_univ p, by simp [hwp]⟩
    rcases hor with rfl | rfl
    · refine Finset.mem_image.mpr ⟨(p, false), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩, ?_⟩
      simp [slotVal, hwp]
    · refine Finset.mem_image.mpr ⟨(p, true), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩, ?_⟩
      simp [slotVal, hwp]
  have hslot_img : slots.image slotVal = Finset.univ.erase ⟨0, hpos⟩ := by
    apply Finset.Subset.antisymm
    · intro i hi
      obtain ⟨pb, hpb, rfl⟩ := Finset.mem_image.mp hi
      exact hslot_nz pb hpb
    · exact hslot_surj
  have hslot_card : slots.card = 2 * resSet.card := by
    rw [Finset.card_product]
    have : (Finset.univ : Finset Bool).card = 2 := by decide
    rw [this]; ring
  have hnz_card : (Finset.univ.erase ⟨0, hpos⟩ : Finset (Fin π.length)).card = π.length - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hle_slots : π.length - 1 ≤ 2 * resSet.card := by
    calc π.length - 1 = (slots.image slotVal).card := by rw [hslot_img, hnz_card]
      _ ≤ slots.card := Finset.card_image_le
      _ = 2 * resSet.card := hslot_card
  have hax6 : axSet.card = 6 := by omega
  have hres5 : resSet.card = 5 := by omega
  have hlen11 : π.length = 11 := by omega
  have hslot_inj : Set.InjOn slotVal (↑slots : Set (Fin π.length × Bool)) := by
    apply Finset.injOn_of_card_image_eq
    rw [hslot_img, hnz_card, hslot_card]
    omega
  have hax_unique : ∀ i1 ∈ axSet, ∀ i2 ∈ axSet, π[i1] = π[i2] → i1 = i2 := by
    have himg : axSet.image (fun i => π[i]) = (Finset.univ : Finset Edge).image baseClause := by
      apply Finset.Subset.antisymm
      · intro C hC
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
        have hwi : w i = none := (Finset.mem_filter.mp hi).2
        have hmem := hw i
        rw [hwi] at hmem
        obtain ⟨e, he⟩ := hmem
        exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he⟩
      · intro C hC
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hC
        obtain ⟨i, hi, hieq⟩ := hax_has e
        exact Finset.mem_image.mpr ⟨i, hi, hieq⟩
    have hcard_eq : (axSet.image (fun i => π[i])).card = axSet.card := by
      rw [himg, Finset.card_image_of_injective _ baseClause_injective, hax6]
      decide
    have hinj := Finset.injOn_of_card_image_eq hcard_eq
    intro i1 hi1 i2 hi2 heq
    exact hinj hi1 hi2 heq
  have hw0_some : ∃ j0 k0, w ⟨0, hpos⟩ = some (j0, k0) := by
    have h0 := hw ⟨0, hpos⟩
    cases h : w ⟨0, hpos⟩ with
    | none =>
      rw [h] at h0
      have h0e : π[(⟨0, hpos⟩ : Fin π.length)] = ∅ := hhead_emp
      rw [h0e] at h0
      obtain ⟨e, he⟩ := h0
      have : ((src e).1, !(src e).2) ∈ (∅ : Clause BaseV) := by
        rw [← he]; exact Finset.mem_insert_self _ _
      exact absurd this (Finset.notMem_empty _)
    | some jk => exact ⟨jk.1, jk.2, rfl⟩
  obtain ⟨j0, k0, hw0⟩ := hw0_some
  have hres0 : IsResolvent π[j0] π[k0] ∅ := by
    have h0 := hw ⟨0, hpos⟩
    rw [hw0] at h0
    have h0e : π[(⟨0, hpos⟩ : Fin π.length)] = ∅ := hhead_emp
    rw [h0e] at h0
    exact h0.2.2
  obtain ⟨v, hvj, hvk, hvemp⟩ := hres0
  have hpi_j0 : π[j0] = {(v, true)} := by
    ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have : l ∈ π[j0].erase (v, true) ∪ π[k0].erase (v, false) :=
        Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hl⟩)
      rw [← hvemp] at this
      exact Finset.notMem_empty l this
    · rintro rfl; exact hvj
  have hpi_k0 : π[k0] = {(v, false)} := by
    ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have : l ∈ π[j0].erase (v, true) ∪ π[k0].erase (v, false) :=
        Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hl⟩)
      rw [← hvemp] at this
      exact Finset.notMem_empty l this
    · rintro rfl; exact hvk
  let pStep : Fin π.length → Fin π.length → Prop := fun p c =>
    ∃ j k, w p = some (j, k) ∧ (c = j ∨ c = k)
  have hpStep_lt : ∀ p c, pStep p c → p.val < c.val := by
    rintro p c ⟨j, k, hwp, rfl | rfl⟩
    · have h := hw p; rw [hwp] at h; exact h.1
    · have h := hw p; rw [hwp] at h; exact h.2.1
  have hrtg_le : ∀ a b, Relation.ReflTransGen pStep a b → a.val ≤ b.val := by
    intro a b h
    induction h with
    | refl => exact le_refl _
    | tail _ hstep ih => exact le_trans ih (le_of_lt (hpStep_lt _ _ hstep))
  have hpStep_unique : ∀ p1 p2 c, pStep p1 c → pStep p2 c → p1 = p2 := by
    rintro p1 p2 c ⟨j1, k1, hw1, h1⟩ ⟨j2, k2, hw2, h2⟩
    have hp1 : p1 ∈ resSet := Finset.mem_filter.mpr ⟨Finset.mem_univ p1, by simp [hw1]⟩
    have hp2 : p2 ∈ resSet := Finset.mem_filter.mpr ⟨Finset.mem_univ p2, by simp [hw2]⟩
    have hmem_sl : ∀ (p : Fin π.length) (b : Bool), p ∈ resSet → (p, b) ∈ (↑slots : Set (Fin π.length × Bool)) :=
      fun p b hp => Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hp, Finset.mem_univ b⟩)
    rcases h1 with rfl | rfl <;> rcases h2 with h2' | h2'
    · have := hslot_inj (hmem_sl p1 false hp1) (hmem_sl p2 false hp2) (by simp [slotVal, hw1, hw2, h2'])
      exact (Prod.mk.inj this).1
    · have := hslot_inj (hmem_sl p1 false hp1) (hmem_sl p2 true hp2) (by simp [slotVal, hw1, hw2, h2'])
      exact (Prod.mk.inj this).1
    · have := hslot_inj (hmem_sl p1 true hp1) (hmem_sl p2 false hp2) (by simp [slotVal, hw1, hw2, h2'])
      exact (Prod.mk.inj this).1
    · have := hslot_inj (hmem_sl p1 true hp1) (hmem_sl p2 true hp2) (by simp [slotVal, hw1, hw2, h2'])
      exact (Prod.mk.inj this).1
  let Anc : Fin π.length → Finset (Fin π.length) := fun u =>
    Finset.univ.filter (Relation.ReflTransGen pStep u)
  have hj0k0 : j0 ≠ k0 := by
    intro h
    rw [h, hpi_k0] at hpi_j0
    have : (v, false) ∈ ({(v, true)} : Clause BaseV) := by
      rw [← hpi_j0]; exact Finset.mem_singleton_self _
    simp at this
  have hdisj_anc : Disjoint (Anc j0) (Anc k0) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    let inter := Anc j0 ∩ Anc k0
    have hne : inter.Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hx1, hx2⟩⟩
    let u := inter.min' hne
    have hu_mem : u ∈ inter := Finset.min'_mem inter hne
    have hu1 : Relation.ReflTransGen pStep j0 u :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hu_mem).1).2
    have hu2 : Relation.ReflTransGen pStep k0 u :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hu_mem).2).2
    have hu_ne_j0 : u ≠ j0 := by
      intro h
      have hu2' : Relation.ReflTransGen pStep k0 j0 := h ▸ hu2
      rcases Relation.ReflTransGen.cases_tail hu2' with heq | ⟨p, hp2, hpu⟩
      · exact hj0k0 heq
      · have hp0 : p = ⟨0, hpos⟩ := hpStep_unique p ⟨0, hpos⟩ j0 hpu ⟨j0, k0, hw0, Or.inl rfl⟩
        have hle := hrtg_le k0 p hp2
        have hk0_pos : 0 < k0.val := by
          have h := hw ⟨0, hpos⟩; rw [hw0] at h; exact h.2.1
        rw [hp0] at hle
        exact absurd hle (by simp; omega)
    have hu_ne_k0 : u ≠ k0 := by
      intro h
      have hu1' : Relation.ReflTransGen pStep j0 k0 := h ▸ hu1
      rcases Relation.ReflTransGen.cases_tail hu1' with heq | ⟨p, hp1, hpu⟩
      · exact hj0k0 heq.symm
      · have hp0 : p = ⟨0, hpos⟩ := hpStep_unique p ⟨0, hpos⟩ k0 hpu ⟨j0, k0, hw0, Or.inr rfl⟩
        have hle := hrtg_le j0 p hp1
        have hj0_pos : 0 < j0.val := by
          have h := hw ⟨0, hpos⟩; rw [hw0] at h; exact h.1
        rw [hp0] at hle
        exact absurd hle (by simp; omega)
    rcases Relation.ReflTransGen.cases_tail hu1 with heq1 | ⟨p1, hp1, hp1u⟩
    · exact hu_ne_j0 heq1
    · rcases Relation.ReflTransGen.cases_tail hu2 with heq2 | ⟨p2, hp2, hp2u⟩
      · exact hu_ne_k0 heq2
      · have hp12 : p1 = p2 := hpStep_unique p1 p2 u hp1u hp2u
        subst hp12
        have hp_mem : p1 ∈ inter := Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2⟩⟩
        have hle : u ≤ p1 := Finset.min'_le inter p1 hp_mem
        have hlt' : p1.val < u.val := hpStep_lt p1 u hp1u
        exact absurd (Fin.le_def.mp hle) (by omega)
  have hanc_sound : ∀ (a : BaseV → Bool) (r : ℕ) (u : Fin π.length),
      π.length - u.val ≤ r →
      (∀ i ∈ Anc u, w i = none → ClauseSat a π[i]) → ClauseSat a π[u] := by
    intro a r
    induction r with
    | zero => intro u hu _; omega
    | succ r ih =>
      intro u hu hsat
      have hspec := hw u
      cases hwu : w u with
      | none => exact hsat u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩) hwu
      | some jk =>
        rcases jk with ⟨j, k⟩
        rw [hwu] at hspec
        rcases hspec with ⟨hj, hk, hres⟩
        have hsat_j : ClauseSat a π[j] := ih j (by omega) fun i hi hwi =>
          hsat i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Relation.ReflTransGen.head ⟨j, k, hwu, Or.inl rfl⟩ (Finset.mem_filter.mp hi).2⟩) hwi
        have hsat_k : ClauseSat a π[k] := ih k (by omega) fun i hi hwi =>
          hsat i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Relation.ReflTransGen.head ⟨j, k, hwu, Or.inr rfl⟩ (Finset.mem_filter.mp hi).2⟩) hwi
        exact resolvent_sound hres hsat_j hsat_k
  have hmust_contain : ∀ (u : Fin π.length) (a : BaseV → Bool) (e : Edge),
      ¬ ClauseSat a π[u] →
      (∀ e' : Edge, e' ≠ e → ClauseSat a (baseClause e')) →
      ∃ i ∈ Anc u, i ∈ axSet ∧ π[i] = baseClause e := by
    intro u a e hnsat hall
    by_contra hno
    push Not at hno
    apply hnsat
    apply hanc_sound a π.length u (by omega)
    intro i hi hwi
    have hmem := hw i
    rw [hwi] at hmem
    obtain ⟨e', he'⟩ := hmem
    have hee : e' ≠ e := by
      intro h; subst h
      exact hno i hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩) he'.symm
    rw [← he']
    exact hall e' hee
  have hcontra_edge : ∀ (e : Edge) (a1 a2 : BaseV → Bool),
      a1 v = false → a2 v = true →
      (∀ e' : Edge, e' ≠ e → ClauseSat a1 (baseClause e')) →
      (∀ e' : Edge, e' ≠ e → ClauseSat a2 (baseClause e')) → False := by
    intro e a1 a2 ha1 ha2 h1 h2
    have hns1 : ¬ ClauseSat a1 π[j0] := by rw [hpi_j0]; simp [ClauseSat, ha1]
    have hns2 : ¬ ClauseSat a2 π[k0] := by rw [hpi_k0]; simp [ClauseSat, ha2]
    obtain ⟨i1, hi1_anc, hi1_ax, hi1_eq⟩ := hmust_contain j0 a1 e hns1 h1
    obtain ⟨i2, hi2_anc, hi2_ax, hi2_eq⟩ := hmust_contain k0 a2 e hns2 h2
    have hi12 : i1 = i2 := hax_unique i1 hi1_ax i2 hi2_ax (hi1_eq.trans hi2_eq.symm)
    subst hi12
    exact Finset.disjoint_left.mp hdisj_anc hi1_anc hi2_anc
  fin_cases v
  · exact hcontra_edge 1 ![false, false, true, true] ![true, false, true, true] rfl rfl
      (by unfold ClauseSat baseClause src dst; decide)
      (by unfold ClauseSat baseClause src dst; decide)
  · exact hcontra_edge 1 ![false, false, true, true] ![false, true, true, true] rfl rfl
      (by unfold ClauseSat baseClause src dst; decide)
      (by unfold ClauseSat baseClause src dst; decide)
  · exact hcontra_edge 0 ![true, true, false, false] ![true, true, true, false] rfl rfl
      (by unfold ClauseSat baseClause src dst; decide)
      (by unfold ClauseSat baseClause src dst; decide)
  · exact hcontra_edge 0 ![true, true, false, false] ![true, true, false, true] rfl rfl
      (by unfold ClauseSat baseClause src dst; decide)
      (by unfold ClauseSat baseClause src dst; decide)

theorem baseF_resCount_ge_six {π : List (Clause BaseV)} {r : ℕ}
    (h : IsDerivCount baseF π r) (hemp : (∅ : Clause BaseV) ∈ π) : 6 ≤ r := by
  obtain ⟨π', href', hlen'⟩ := isDerivCount_baseF_to_refutation h hemp
  have h12 := baseF_min_len π' href'
  omega

def substLit (σ : BigV → Literal BaseV) (l : Literal BigV) : Literal BaseV :=
  let (w, b) := σ l.1
  (w, if l.2 = true then b else !b)

theorem substLit_flip (σ : BigV → Literal BaseV) (v : BigV) (s : Bool) :
    substLit σ (v, !s) = ((substLit σ (v, s)).1, !(substLit σ (v, s)).2) := by
  unfold substLit
  cases σ v with
  | mk w b => cases s <;> cases b <;> rfl

def substClause (σ : BigV → Literal BaseV) (C : Clause BigV) : Clause BaseV :=
  C.image (substLit σ)

def Taut (C : Clause BaseV) : Prop :=
  ∃ w : BaseV, (w, true) ∈ C ∧ (w, false) ∈ C

theorem not_taut_empty : ¬ Taut (∅ : Clause BaseV) := by
  rintro ⟨w, h, _⟩; exact Finset.notMem_empty _ h

theorem not_taut_baseClause (e : Edge) : ¬ Taut (baseClause e) := by
  revert e; unfold Taut baseClause src dst; decide

theorem taut_of_taut_taut (σ : BigV → Literal BaseV) {C D R : Clause BigV}
    (hres : IsResolvent C D R) (hC : Taut (substClause σ C)) (hD : Taut (substClause σ D)) :
    Taut (substClause σ R) := by
  obtain ⟨v, _, _, rfl⟩ := hres
  obtain ⟨w, b, hσv⟩ : ∃ w b, σ v = (w, b) := ⟨(σ v).1, (σ v).2, rfl⟩
  have hvt : substLit σ (v, true) = (w, b) := by simp [substLit, hσv]
  have hvf : substLit σ (v, false) = (w, !b) := by simp [substLit, hσv]
  have hCside : Taut (substClause σ (C.erase (v, true) ∪ D.erase (v, false))) ∨
      (w, !b) ∈ substClause σ (C.erase (v, true) ∪ D.erase (v, false)) := by
    obtain ⟨x, hxT, hxF⟩ := hC
    by_cases hxw : x = w
    · subst hxw
      right
      have hnb : (x, !b) ∈ substClause σ C := by cases b; exact hxT; exact hxF
      obtain ⟨l, hlC, hls⟩ := Finset.mem_image.mp hnb
      have hlne : l ≠ (v, true) := by
        intro heq; subst heq; rw [hvt] at hls
        have := (Prod.mk.inj hls).2
        cases b <;> simp at this
      exact Finset.mem_image.mpr ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlne, hlC⟩), hls⟩
    · left
      obtain ⟨l1, hl1C, hl1s⟩ := Finset.mem_image.mp hxT
      obtain ⟨l2, hl2C, hl2s⟩ := Finset.mem_image.mp hxF
      have h1ne : l1 ≠ (v, true) := by
        intro heq; subst heq; rw [hvt] at hl1s; exact hxw (Prod.mk.inj hl1s).1.symm
      have h2ne : l2 ≠ (v, true) := by
        intro heq; subst heq; rw [hvt] at hl2s; exact hxw (Prod.mk.inj hl2s).1.symm
      exact ⟨x,
        Finset.mem_image.mpr ⟨l1, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h1ne, hl1C⟩), hl1s⟩,
        Finset.mem_image.mpr ⟨l2, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h2ne, hl2C⟩), hl2s⟩⟩
  have hDside : Taut (substClause σ (C.erase (v, true) ∪ D.erase (v, false))) ∨
      (w, b) ∈ substClause σ (C.erase (v, true) ∪ D.erase (v, false)) := by
    obtain ⟨x, hxT, hxF⟩ := hD
    by_cases hxw : x = w
    · subst hxw
      right
      have hb : (x, b) ∈ substClause σ D := by cases b; exact hxF; exact hxT
      obtain ⟨l, hlD, hls⟩ := Finset.mem_image.mp hb
      have hlne : l ≠ (v, false) := by
        intro heq; subst heq; rw [hvf] at hls
        have := (Prod.mk.inj hls).2
        cases b <;> simp at this
      exact Finset.mem_image.mpr ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlne, hlD⟩), hls⟩
    · left
      obtain ⟨l1, hl1D, hl1s⟩ := Finset.mem_image.mp hxT
      obtain ⟨l2, hl2D, hl2s⟩ := Finset.mem_image.mp hxF
      have h1ne : l1 ≠ (v, false) := by
        intro heq; subst heq; rw [hvf] at hl1s; exact hxw (Prod.mk.inj hl1s).1.symm
      have h2ne : l2 ≠ (v, false) := by
        intro heq; subst heq; rw [hvf] at hl2s; exact hxw (Prod.mk.inj hl2s).1.symm
      exact ⟨x,
        Finset.mem_image.mpr ⟨l1, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h1ne, hl1D⟩), hl1s⟩,
        Finset.mem_image.mpr ⟨l2, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h2ne, hl2D⟩), hl2s⟩⟩
  rcases hCside with hT | hnb
  · exact hT
  · rcases hDside with hT | hb
    · exact hT
    · cases b
      · exact ⟨w, hnb, hb⟩
      · exact ⟨w, hb, hnb⟩

theorem subset_of_res_taut_left (σ : BigV → Literal BaseV) {C D R : Clause BigV}
    (hres : IsResolvent C D R) (hC : Taut (substClause σ C)) (hR : ¬ Taut (substClause σ R)) :
    substClause σ D ⊆ substClause σ R := by
  obtain ⟨v, _, _, rfl⟩ := hres
  obtain ⟨w, b, hσv⟩ : ∃ w b, σ v = (w, b) := ⟨(σ v).1, (σ v).2, rfl⟩
  have hvt : substLit σ (v, true) = (w, b) := by simp [substLit, hσv]
  have hvf : substLit σ (v, false) = (w, !b) := by simp [substLit, hσv]
  have hnb_R : (w, !b) ∈ substClause σ (C.erase (v, true) ∪ D.erase (v, false)) := by
    obtain ⟨x, hxT, hxF⟩ := hC
    by_cases hxw : x = w
    · subst hxw
      have hnb : (x, !b) ∈ substClause σ C := by cases b; exact hxT; exact hxF
      obtain ⟨l, hlC, hls⟩ := Finset.mem_image.mp hnb
      have hlne : l ≠ (v, true) := by
        intro heq; subst heq; rw [hvt] at hls
        have := (Prod.mk.inj hls).2
        cases b <;> simp at this
      exact Finset.mem_image.mpr ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlne, hlC⟩), hls⟩
    · exfalso
      apply hR
      obtain ⟨l1, hl1C, hl1s⟩ := Finset.mem_image.mp hxT
      obtain ⟨l2, hl2C, hl2s⟩ := Finset.mem_image.mp hxF
      have h1ne : l1 ≠ (v, true) := by
        intro heq; subst heq; rw [hvt] at hl1s; exact hxw (Prod.mk.inj hl1s).1.symm
      have h2ne : l2 ≠ (v, true) := by
        intro heq; subst heq; rw [hvt] at hl2s; exact hxw (Prod.mk.inj hl2s).1.symm
      exact ⟨x,
        Finset.mem_image.mpr ⟨l1, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h1ne, hl1C⟩), hl1s⟩,
        Finset.mem_image.mpr ⟨l2, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h2ne, hl2C⟩), hl2s⟩⟩
  intro y hy
  obtain ⟨l, hlD, rfl⟩ := Finset.mem_image.mp hy
  by_cases hlv : l = (v, false)
  · subst hlv; rw [hvf]; exact hnb_R
  · exact Finset.mem_image.mpr ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hlD⟩), rfl⟩

theorem subset_of_res_taut_right (σ : BigV → Literal BaseV) {C D R : Clause BigV}
    (hres : IsResolvent C D R) (hD : Taut (substClause σ D)) (hR : ¬ Taut (substClause σ R)) :
    substClause σ C ⊆ substClause σ R := by
  obtain ⟨v, _, _, rfl⟩ := hres
  obtain ⟨w, b, hσv⟩ : ∃ w b, σ v = (w, b) := ⟨(σ v).1, (σ v).2, rfl⟩
  have hvt : substLit σ (v, true) = (w, b) := by simp [substLit, hσv]
  have hvf : substLit σ (v, false) = (w, !b) := by simp [substLit, hσv]
  have hb_R : (w, b) ∈ substClause σ (C.erase (v, true) ∪ D.erase (v, false)) := by
    obtain ⟨x, hxT, hxF⟩ := hD
    by_cases hxw : x = w
    · subst hxw
      have hb : (x, b) ∈ substClause σ D := by cases b; exact hxF; exact hxT
      obtain ⟨l, hlD, hls⟩ := Finset.mem_image.mp hb
      have hlne : l ≠ (v, false) := by
        intro heq; subst heq; rw [hvf] at hls
        have := (Prod.mk.inj hls).2
        cases b <;> simp at this
      exact Finset.mem_image.mpr ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlne, hlD⟩), hls⟩
    · exfalso
      apply hR
      obtain ⟨l1, hl1D, hl1s⟩ := Finset.mem_image.mp hxT
      obtain ⟨l2, hl2D, hl2s⟩ := Finset.mem_image.mp hxF
      have h1ne : l1 ≠ (v, false) := by
        intro heq; subst heq; rw [hvf] at hl1s; exact hxw (Prod.mk.inj hl1s).1.symm
      have h2ne : l2 ≠ (v, false) := by
        intro heq; subst heq; rw [hvf] at hl2s; exact hxw (Prod.mk.inj hl2s).1.symm
      exact ⟨x,
        Finset.mem_image.mpr ⟨l1, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h1ne, hl1D⟩), hl1s⟩,
        Finset.mem_image.mpr ⟨l2, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h2ne, hl2D⟩), hl2s⟩⟩
  intro y hy
  obtain ⟨l, hlC, rfl⟩ := Finset.mem_image.mp hy
  by_cases hlv : l = (v, true)
  · subst hlv; rw [hvt]; exact hb_R
  · exact Finset.mem_image.mpr ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hlC⟩), rfl⟩

theorem res_subst_step (σ : BigV → Literal BaseV) {C D R : Clause BigV}
    (hres : IsResolvent C D R) {C' D' : Clause BaseV}
    (hC' : C' ⊆ substClause σ C) (hD' : D' ⊆ substClause σ D) :
    C' ⊆ substClause σ R ∨ D' ⊆ substClause σ R ∨
      ∃ R', (IsResolvent C' D' R' ∨ IsResolvent D' C' R') ∧ R' ⊆ substClause σ R := by
  obtain ⟨v, _, _, rfl⟩ := hres
  obtain ⟨w, b, hσv⟩ : ∃ w b, σ v = (w, b) := ⟨(σ v).1, (σ v).2, rfl⟩
  have hvt : substLit σ (v, true) = (w, b) := by simp [substLit, hσv]
  have hvf : substLit σ (v, false) = (w, !b) := by simp [substLit, hσv]
  have hsubC : ∀ y ∈ C', y ≠ (w, b) → y ∈ substClause σ (C.erase (v, true) ∪ D.erase (v, false)) := by
    intro y hy hne
    obtain ⟨l, hlC, rfl⟩ := Finset.mem_image.mp (hC' hy)
    have hlv : l ≠ (v, true) := by intro h; subst h; exact hne hvt
    exact Finset.mem_image.mpr ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hlC⟩), rfl⟩
  have hsubD : ∀ y ∈ D', y ≠ (w, !b) → y ∈ substClause σ (C.erase (v, true) ∪ D.erase (v, false)) := by
    intro y hy hne
    obtain ⟨l, hlD, rfl⟩ := Finset.mem_image.mp (hD' hy)
    have hlv : l ≠ (v, false) := by intro h; subst h; exact hne hvf
    exact Finset.mem_image.mpr ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hlD⟩), rfl⟩
  by_cases h1 : (w, b) ∈ C'
  · by_cases h2 : (w, !b) ∈ D'
    · right; right
      refine ⟨C'.erase (w, b) ∪ D'.erase (w, !b), ?_, ?_⟩
      · cases b
        · right; exact ⟨w, h2, h1, by simp [Finset.union_comm]⟩
        · left; exact ⟨w, h1, h2, rfl⟩
      · intro y hy
        rcases Finset.mem_union.mp hy with hy1 | hy2
        · exact hsubC y (Finset.mem_erase.mp hy1).2 (Finset.mem_erase.mp hy1).1
        · exact hsubD y (Finset.mem_erase.mp hy2).2 (Finset.mem_erase.mp hy2).1
    · right; left
      intro y hy
      exact hsubD y hy (fun heq => h2 (heq ▸ hy))
  · left
    intro y hy
    exact hsubC y hy (fun heq => h1 (heq ▸ hy))

def sliceSubst (k : ℕ) : BigV → Literal BaseV
  | Sum.inl v => (v, true)
  | Sum.inr (e, r) => if r ≤ k then src e else dst e

theorem sliceSubst_step_eq {t : ℕ} {e : Edge} {k : ℕ} (hk : k < t) :
    substClause (sliceSubst k) (step t e k) = baseClause e := by
  have hleft : substLit (sliceSubst k) ((lit t e k).1, !(lit t e k).2) = ((src e).1, !(src e).2) := by
    by_cases hk0 : k = 0
    · subst hk0
      simp only [lit, ite_true, substLit, sliceSubst]
      cases (src e).2 <;> rfl
    · have hkt : k ≠ t := by omega
      simp only [lit, hk0, hkt, ite_false, substLit, sliceSubst, le_refl, ite_true]
      cases (src e).2 <;> rfl
  have hright : substLit (sliceSubst k) (lit t e (k + 1)) = ((dst e).1, (dst e).2) := by
    by_cases hkt : k + 1 = t
    · rw [hkt, lit_end (by omega)]; simp only [substLit, sliceSubst]; cases (dst e).2 <;> rfl
    · rw [lit_mid (Nat.succ_ne_zero _) hkt]
      simp only [substLit, sliceSubst, show ¬ k + 1 ≤ k by omega, ite_false]
      cases (dst e).2 <;> rfl
  simp only [substClause, step, Finset.image_insert, Finset.image_singleton, hleft, hright, baseClause]

theorem sliceSubst_step_taut {t : ℕ} {e : Edge} {k j : ℕ} (hk : k < t) (hj : j < t) (hne : j ≠ k) :
    Taut (substClause (sliceSubst k) (step t e j)) := by
  by_cases hlt : j < k
  · have hleft : substLit (sliceSubst k) ((lit t e j).1, !(lit t e j).2) = ((src e).1, !(src e).2) := by
      by_cases hj0 : j = 0
      · subst hj0; simp only [lit, ite_true, substLit, sliceSubst]; cases (src e).2 <;> rfl
      · simp only [lit, hj0, show j ≠ t by omega, ite_false, substLit, sliceSubst,
          show j ≤ k by omega, ite_true]
        cases (src e).2 <;> rfl
    have hright : substLit (sliceSubst k) (lit t e (j + 1)) = ((src e).1, (src e).2) := by
      by_cases hjt : j + 1 = t
      · exfalso; omega
      · rw [lit_mid (Nat.succ_ne_zero _) hjt]
        simp only [substLit, sliceSubst, show j + 1 ≤ k by omega, ite_true]
    have heq : substClause (sliceSubst k) (step t e j) = {((src e).1, !(src e).2), ((src e).1, (src e).2)} := by
      simp only [substClause, step, Finset.image_insert, Finset.image_singleton, hleft, hright]
    rw [heq]
    cases (src e).2
    · exact ⟨(src e).1, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    · exact ⟨(src e).1, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Finset.mem_insert_self _ _⟩
  · have hgt : k < j := by omega
    have hleft : substLit (sliceSubst k) ((lit t e j).1, !(lit t e j).2) = ((dst e).1, !(dst e).2) := by
      simp only [lit, show j ≠ 0 by omega, show j ≠ t by omega, ite_false, substLit, sliceSubst,
        show ¬ j ≤ k by omega]
      cases (dst e).2 <;> rfl
    have hright : substLit (sliceSubst k) (lit t e (j + 1)) = ((dst e).1, (dst e).2) := by
      by_cases hjt : j + 1 = t
      · rw [hjt, lit_end (by omega)]; simp only [substLit, sliceSubst]; cases (dst e).2 <;> rfl
      · rw [lit_mid (Nat.succ_ne_zero _) hjt]
        simp only [substLit, sliceSubst, show ¬ j + 1 ≤ k by omega, ite_false]
        cases (dst e).2 <;> rfl
    have heq : substClause (sliceSubst k) (step t e j) = {((dst e).1, !(dst e).2), ((dst e).1, (dst e).2)} := by
      simp only [substClause, step, Finset.image_insert, Finset.image_singleton, hleft, hright]
    rw [heq]
    cases (dst e).2
    · exact ⟨(dst e).1, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    · exact ⟨(dst e).1, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Finset.mem_insert_self _ _⟩

theorem dag_lower {t : ℕ} (ht : 0 < t) {π0 : List (Clause BigV)}
    (href0 : IsRefutation (big t) π0) : 12 * t ≤ π0.length := by
  classical
  have hex : ∃ k, ∃ π : List (Clause BigV), IsRefutation (big t) π ∧ π.length = k :=
    ⟨π0.length, π0, href0, rfl⟩
  let mlen := Nat.find hex
  obtain ⟨π, href, hmlen⟩ := Nat.find_spec hex
  have hmin : ∀ π', IsRefutation (big t) π' → π.length ≤ π'.length := by
    intro π' href'
    rw [hmlen]
    exact Nat.find_min' hex ⟨π', href', rfl⟩
  suffices h12 : 12 * t ≤ π.length from le_trans h12 (hmin π0 href0)
  obtain ⟨w, hw⟩ := derivation_witness href.1
  let σ := sliceSubst 0
  let isTaut : Fin π.length → Prop := fun i => Taut (substClause σ π[i])
  let axNon := Finset.univ.filter (fun i : Fin π.length => w i = none ∧ ¬ isTaut i)
  let axTaut := Finset.univ.filter (fun i : Fin π.length => w i = none ∧ isTaut i)
  let resTaut := Finset.univ.filter (fun i : Fin π.length => (w i).isSome ∧ isTaut i)
  let resMix := Finset.univ.filter (fun i : Fin π.length =>
    ∃ j k, w i = some (j, k) ∧ ¬ isTaut i ∧ (isTaut j ∨ isTaut k))
  let resReal := Finset.univ.filter (fun i : Fin π.length =>
    ∃ j k, w i = some (j, k) ∧ ¬ isTaut i ∧ ¬ isTaut j ∧ ¬ isTaut k)
  have hsum_card : axNon.card + axTaut.card + resTaut.card + resMix.card + resReal.card = π.length := by
    have hdisj1 : Disjoint axNon axTaut := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_filter.mp h1).2.2 (Finset.mem_filter.mp h2).2.2
    have hdisj2 : Disjoint (axNon ∪ axTaut) resTaut := by
      rw [Finset.disjoint_left]; intro i h1 h2
      have h2' := (Finset.mem_filter.mp h2).2.1
      rcases Finset.mem_union.mp h1 with h1a | h1b
      · rw [(Finset.mem_filter.mp h1a).2.1] at h2'; simp at h2'
      · rw [(Finset.mem_filter.mp h1b).2.1] at h2'; simp at h2'
    have hdisj3 : Disjoint (axNon ∪ axTaut ∪ resTaut) resMix := by
      rw [Finset.disjoint_left]; intro i h1 h2
      obtain ⟨j, k, hwi, hnt, _⟩ := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h1ab | h1c
      · rcases Finset.mem_union.mp h1ab with h1a | h1b
        · rw [(Finset.mem_filter.mp h1a).2.1] at hwi; simp at hwi
        · rw [(Finset.mem_filter.mp h1b).2.1] at hwi; simp at hwi
      · exact hnt (Finset.mem_filter.mp h1c).2.2
    have hdisj4 : Disjoint (axNon ∪ axTaut ∪ resTaut ∪ resMix) resReal := by
      rw [Finset.disjoint_left]; intro i h1 h2
      obtain ⟨j, k, hwi, hnt, hnj, hnk⟩ := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with h1abc | h1d
      · rcases Finset.mem_union.mp h1abc with h1ab | h1c
        · rcases Finset.mem_union.mp h1ab with h1a | h1b
          · rw [(Finset.mem_filter.mp h1a).2.1] at hwi; simp at hwi
          · rw [(Finset.mem_filter.mp h1b).2.1] at hwi; simp at hwi
        · exact hnt (Finset.mem_filter.mp h1c).2.2
      · obtain ⟨j', k', hwi', _, hjk⟩ := (Finset.mem_filter.mp h1d).2
        rw [hwi] at hwi'
        have hpair := Option.some.inj hwi'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        exact hjk.elim hnj hnk
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2,
      ← Finset.card_union_of_disjoint hdisj3, ← Finset.card_union_of_disjoint hdisj4]
    have hun : axNon ∪ axTaut ∪ resTaut ∪ resMix ∪ resReal = Finset.univ := by
      ext i
      simp only [axNon, axTaut, resTaut, resMix, resReal,
        Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases hwi : w i with
      | none =>
        by_cases htaut : isTaut i
        · left; left; left; right; exact ⟨rfl, htaut⟩
        · left; left; left; left; exact ⟨rfl, htaut⟩
      | some jk =>
        rcases jk with ⟨j, k⟩
        by_cases htaut : isTaut i
        · left; left; right; exact ⟨by simp, htaut⟩
        · by_cases hjk : isTaut j ∨ isTaut k
          · left; right; exact ⟨j, k, rfl, htaut, hjk⟩
          · right
            push Not at hjk
            exact ⟨j, k, rfl, htaut, hjk.1, hjk.2⟩
    rw [hun, Finset.card_univ, Fintype.card_fin]
  have hax_has : ∀ (e : Edge) (j : ℕ), j < t → ∃ i : Fin π.length, w i = none ∧ π[i] = step t e j := by
    intro e j hj
    have hsat : Satisfiable (big t \ {step t e j}) := by
      refine ⟨bigWit e j, fun C hC => ?_⟩
      rcases hC with ⟨⟨e', j', hj', rfl⟩, hne⟩
      have hne' : e' ≠ e ∨ j' ≠ j := by
        by_contra h
        push Not at h
        exact hne (by simp [h.1, h.2])
      exact big_indispensable ht e j hj e' j' hj' hne'
    exact ax_line_of_indispensable w hw href.2 hsat
  have haxNon_ge : 6 ≤ axNon.card := by
    choose f hf using fun e => hax_has e 0 ht
    have hinj : Set.InjOn f (↑(Finset.univ : Finset Edge) : Set Edge) := by
      intro e1 _ e2 _ hfeq
      have h1 := (hf e1).2
      have h2 := (hf e2).2
      rw [hfeq] at h1
      exact (step_injective ht ht ht (h1.symm.trans h2)).1
    have hsub : (Finset.univ : Finset Edge).image f ⊆ axNon := by
      intro i hi
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf e).1, ?_⟩
      dsimp only [isTaut, σ]
      rw [(hf e).2, sliceSubst_step_eq ht]
      exact not_taut_baseClause e
    calc 6 = (Finset.univ : Finset Edge).card := by decide
      _ = ((Finset.univ : Finset Edge).image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ axNon.card := Finset.card_le_card hsub
  have haxTaut_ge : 6 * (t - 1) ≤ axTaut.card := by
    let dom := (Finset.univ : Finset Edge) ×ˢ (Finset.range (t - 1))
    have hmem_t : ∀ p ∈ dom, p.2 + 1 < t := by
      intro p hp
      have := Finset.mem_range.mp (Finset.mem_product.mp hp).2
      omega
    let g : Edge × ℕ → Fin π.length := fun p =>
      if h : p.2 + 1 < t then (hax_has p.1 (p.2 + 1) h).choose else ⟨0, by
        cases π with
        | nil => simp [IsRefutation] at href
        | cons _ _ => simp⟩
    have hg_spec : ∀ p ∈ dom, w (g p) = none ∧ π[g p] = step t p.1 (p.2 + 1) := by
      intro p hp
      have hlt := hmem_t p hp
      have hgeq : g p = (hax_has p.1 (p.2 + 1) hlt).choose := dif_pos hlt
      have hsp := (hax_has p.1 (p.2 + 1) hlt).choose_spec
      exact ⟨hgeq.symm ▸ hsp.1, (congrArg (fun i => π[i]) hgeq).trans hsp.2⟩
    have hinj : Set.InjOn g (↑dom : Set (Edge × ℕ)) := by
      intro p1 hp1 p2 hp2 hgeq
      have h1 := (hg_spec p1 hp1).2
      have h2 := (hg_spec p2 hp2).2
      have h12 : step t p1.1 (p1.2 + 1) = step t p2.1 (p2.2 + 1) :=
        h1.symm.trans ((congrArg (fun i => π[i]) hgeq).trans h2)
      have hpair := step_injective ht (hmem_t p1 hp1) (hmem_t p2 hp2) h12
      exact Prod.ext hpair.1 (by omega)
    have hsub : dom.image g ⊆ axTaut := by
      intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hg_spec p hp).1, ?_⟩
      dsimp only [isTaut, σ]
      rw [(hg_spec p hp).2]
      exact sliceSubst_step_taut ht (hmem_t p hp) (by omega)
    calc 6 * (t - 1) = dom.card := by
          rw [Finset.card_product, Finset.card_range]
          have : (Finset.univ : Finset Edge).card = 6 := by decide
          rw [this]
      _ = (dom.image g).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ axTaut.card := Finset.card_le_card hsub
  have htaut_used : ∀ i ∈ axTaut ∪ resTaut,
      ∃ p : Fin π.length, ∃ j k, w p = some (j, k) ∧ (j = i ∨ k = i) := by
    intro i hi
    have hti : isTaut i := by
      rcases Finset.mem_union.mp hi with h1 | h2
      · exact (Finset.mem_filter.mp h1).2.2
      · exact (Finset.mem_filter.mp h2).2.2
    have hne_emp : π[i] ≠ ∅ := by
      intro hemp
      have : Taut (substClause σ ∅) := by rw [← hemp]; exact hti
      simp [substClause] at this
      exact not_taut_empty this
    by_contra hno
    push Not at hno
    obtain ⟨π', href', hlen'⟩ := witness_erase_unused w hw i hno hne_emp href.2
    have := hmin π' href'
    omega
  have haxTaut_le : axTaut.card ≤ resTaut.card + resMix.card := by
    let tautAll := axTaut ∪ resTaut
    let slotSet := (resTaut ×ˢ (Finset.univ : Finset Bool)) ∪ (resMix ×ˢ ({false} : Finset Bool))
    have hmap_ex : ∀ i ∈ tautAll, ∃ pb ∈ slotSet,
        ∃ j k, w pb.1 = some (j, k) ∧
          ((pb.1 ∈ resTaut ∧ (if pb.2 = false then j else k) = i) ∨
           (pb.1 ∈ resMix ∧ pb.2 = false ∧ ((isTaut j ∧ j = i) ∨ (isTaut k ∧ k = i)))) := by
      intro i hi
      have hti : isTaut i := by
        rcases Finset.mem_union.mp hi with h1 | h2
        · exact (Finset.mem_filter.mp h1).2.2
        · exact (Finset.mem_filter.mp h2).2.2
      obtain ⟨p, j, k, hwp, hjk⟩ := htaut_used i hi
      by_cases htp : isTaut p
      · have hp : p ∈ resTaut := Finset.mem_filter.mpr ⟨Finset.mem_univ p, by simp [hwp], htp⟩
        rcases hjk with rfl | rfl
        · refine ⟨(p, false), Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩),
            j, k, hwp, Or.inl ⟨hp, rfl⟩⟩
        · refine ⟨(p, true), Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩),
            j, k, hwp, Or.inl ⟨hp, rfl⟩⟩
      · have hjk_taut : isTaut j ∨ isTaut k := by
          rcases hjk with rfl | rfl
          · exact Or.inl hti
          · exact Or.inr hti
        have hp : p ∈ resMix := Finset.mem_filter.mpr ⟨Finset.mem_univ p, j, k, hwp, htp, hjk_taut⟩
        refine ⟨(p, false), Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hp, Finset.mem_singleton_self _⟩),
          j, k, hwp, Or.inr ⟨hp, rfl, ?_⟩⟩
        rcases hjk with rfl | rfl
        · exact Or.inl ⟨hti, rfl⟩
        · exact Or.inr ⟨hti, rfl⟩
    let φ : Fin π.length → Fin π.length × Bool := fun i =>
      if h : i ∈ tautAll then (hmap_ex i h).choose else (i, false)
    have hφ_sub : tautAll.image φ ⊆ slotSet := by
      intro pb hpb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hpb
      dsimp only [φ]
      rw [dif_pos hi]
      exact (hmap_ex i hi).choose_spec.1
    have hφ_inj : Set.InjOn φ (↑tautAll : Set (Fin π.length)) := by
      intro i1 hi1 i2 hi2 heq
      have hi1' : i1 ∈ tautAll := Finset.mem_coe.mp hi1
      have hi2' : i2 ∈ tautAll := Finset.mem_coe.mp hi2
      dsimp only [φ] at heq
      rw [dif_pos hi1', dif_pos hi2'] at heq
      have hs1 := (hmap_ex i1 hi1').choose_spec.2
      have hs2 := (hmap_ex i2 hi2').choose_spec.2
      rw [heq] at hs1
      obtain ⟨j1, k1, hw1, hc1⟩ := hs1
      obtain ⟨j2, k2, hw2, hc2⟩ := hs2
      rw [hw1] at hw2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hw2)
      rcases hc1 with ⟨hp1, h1⟩ | ⟨hp1, _, h1⟩
      · rcases hc2 with ⟨_, h2⟩ | ⟨hp2, _, _⟩
        · exact h1.symm.trans h2
        · obtain ⟨_, _, _, hnt, _⟩ := (Finset.mem_filter.mp hp2).2
          exact absurd (Finset.mem_filter.mp hp1).2.2 hnt
      · rcases hc2 with ⟨hp2, _⟩ | ⟨_, _, h2⟩
        · obtain ⟨_, _, _, hnt, _⟩ := (Finset.mem_filter.mp hp1).2
          exact absurd (Finset.mem_filter.mp hp2).2.2 hnt
        · have hnotboth : ¬ (isTaut j1 ∧ isTaut k1) := by
            rintro ⟨htj, htk⟩
            obtain ⟨_, _, _, hnt, _⟩ := (Finset.mem_filter.mp hp1).2
            have hspec := hw (hmap_ex i2 hi2').choose.1
            rw [hw1] at hspec
            exact hnt (taut_of_taut_taut σ hspec.2.2 htj htk)
          rcases h1 with ⟨htj1, rfl⟩ | ⟨htk1, rfl⟩ <;> rcases h2 with ⟨htj2, rfl⟩ | ⟨htk2, rfl⟩
          · rfl
          · exact absurd ⟨htj1, htk2⟩ hnotboth
          · exact absurd ⟨htj2, htk1⟩ hnotboth
          · rfl
    have hdisj_taut : Disjoint axTaut resTaut := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      have h1' := (Finset.mem_filter.mp h1).2.1
      have h2' := (Finset.mem_filter.mp h2).2.1
      rw [h1'] at h2'; simp at h2'
    have hslot_le : slotSet.card ≤ 2 * resTaut.card + resMix.card := by
      refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_product, Finset.card_product]
      have h2 : (Finset.univ : Finset Bool).card = 2 := by decide
      have h1 : ({false} : Finset Bool).card = 1 := by decide
      rw [h2, h1]; omega
    have hcard_taut : axTaut.card + resTaut.card ≤ 2 * resTaut.card + resMix.card := by
      calc axTaut.card + resTaut.card = tautAll.card := (Finset.card_union_of_disjoint hdisj_taut).symm
        _ = (tautAll.image φ).card := (Finset.card_image_of_injOn hφ_inj).symm
        _ ≤ slotSet.card := Finset.card_le_card hφ_sub
        _ ≤ 2 * resTaut.card + resMix.card := hslot_le
    omega
  have hresReal_ge : 6 ≤ resReal.card := by
    have hcontract : ∀ k ≤ π.length,
        ∃ (πb : List (Clause BaseV)) (r : ℕ) (out : Fin π.length → Clause BaseV),
          IsDerivCount baseF πb r ∧
          r ≤ (resReal.filter (fun i => π.length - k ≤ i.val)).card ∧
          ∀ i : Fin π.length, π.length - k ≤ i.val → ¬ isTaut i →
            out i ∈ πb ∧ out i ⊆ substClause σ π[i] := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨[], 0, fun _ => ∅, IsDerivCount.nil, Nat.zero_le _, fun i hi _ => by omega⟩
      | succ k ih =>
        intro hk
        obtain ⟨πb, r, out, hdc, hr, hout⟩ := ih (by omega)
        let idx : Fin π.length := ⟨π.length - (k + 1), by omega⟩
        have hidx_val : idx.val = π.length - (k + 1) := rfl
        have hgt_idx : ∀ j : Fin π.length, idx.val < j.val → π.length - k ≤ j.val := by
          intro j hj; dsimp only [idx] at hj; omega
        have hfilt_sub : resReal.filter (fun i => π.length - k ≤ i.val) ⊆
            resReal.filter (fun i => π.length - (k + 1) ≤ i.val) := by
          intro i hi
          obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨h1, by omega⟩
        have hcard_mono := Finset.card_le_card hfilt_sub
        by_cases hti : isTaut idx
        · refine ⟨πb, r, out, hdc, le_trans hr hcard_mono, fun i hi hnt => ?_⟩
          by_cases hieq : i = idx
          · subst hieq; exact absurd hti hnt
          · exact hout i (by have := Fin.val_ne_of_ne hieq; omega) hnt
        · have hspec := hw idx
          cases hwi : w idx with
          | none =>
            rw [hwi] at hspec
            obtain ⟨e, j, hj, heq⟩ := hspec
            have hj0 : j = 0 := by
              by_contra hne
              apply hti
              dsimp only [isTaut, σ]
              rw [heq]
              exact sliceSubst_step_taut ht hj hne
            subst hj0
            have hσeq : substClause σ π[idx] = baseClause e := by
              rw [heq]; exact sliceSubst_step_eq ht
            refine ⟨baseClause e :: πb, r, fun i => if i = idx then baseClause e else out i,
              IsDerivCount.ax hdc ⟨e, rfl⟩, le_trans hr hcard_mono, fun i hi hnt => ?_⟩
            by_cases hieq : i = idx
            · subst hieq
              simp only [ite_true, List.mem_cons_self, true_and]
              rw [hσeq]
            · simp only [hieq, ite_false]
              have hprev := hout i (by have := Fin.val_ne_of_ne hieq; omega) hnt
              exact ⟨List.mem_cons_of_mem _ hprev.1, hprev.2⟩
          | some jk =>
            rcases jk with ⟨j, k'⟩
            rw [hwi] at hspec
            rcases hspec with ⟨hj_lt, hk_lt, hres⟩
            by_cases htj : isTaut j
            · have htk : ¬ isTaut k' := fun htk => hti (taut_of_taut_taut σ hres htj htk)
              have hsub : substClause σ π[k'] ⊆ substClause σ π[idx] :=
                subset_of_res_taut_left σ hres htj hti
              have hk_prev := hout k' (hgt_idx k' hk_lt) htk
              refine ⟨πb, r, fun i => if i = idx then out k' else out i,
                hdc, le_trans hr hcard_mono, fun i hi hnt => ?_⟩
              by_cases hieq : i = idx
              · subst hieq; simp only [ite_true]; exact ⟨hk_prev.1, hk_prev.2.trans hsub⟩
              · simp only [hieq, ite_false]
                exact hout i (by have := Fin.val_ne_of_ne hieq; omega) hnt
            · by_cases htk : isTaut k'
              · have hsub : substClause σ π[j] ⊆ substClause σ π[idx] :=
                  subset_of_res_taut_right σ hres htk hti
                have hj_prev := hout j (hgt_idx j hj_lt) htj
                refine ⟨πb, r, fun i => if i = idx then out j else out i,
                  hdc, le_trans hr hcard_mono, fun i hi hnt => ?_⟩
                by_cases hieq : i = idx
                · subst hieq; simp only [ite_true]; exact ⟨hj_prev.1, hj_prev.2.trans hsub⟩
                · simp only [hieq, ite_false]
                  exact hout i (by have := Fin.val_ne_of_ne hieq; omega) hnt
              · have hj_prev := hout j (hgt_idx j hj_lt) htj
                have hk_prev := hout k' (hgt_idx k' hk_lt) htk
                rcases res_subst_step σ hres hj_prev.2 hk_prev.2 with h1 | h2 | ⟨R', hRres, hRsub⟩
                · refine ⟨πb, r, fun i => if i = idx then out j else out i,
                    hdc, le_trans hr hcard_mono, fun i hi hnt => ?_⟩
                  by_cases hieq : i = idx
                  · subst hieq; simp only [ite_true]; exact ⟨hj_prev.1, h1⟩
                  · simp only [hieq, ite_false]
                    exact hout i (by have := Fin.val_ne_of_ne hieq; omega) hnt
                · refine ⟨πb, r, fun i => if i = idx then out k' else out i,
                    hdc, le_trans hr hcard_mono, fun i hi hnt => ?_⟩
                  by_cases hieq : i = idx
                  · subst hieq; simp only [ite_true]; exact ⟨hk_prev.1, h2⟩
                  · simp only [hieq, ite_false]
                    exact hout i (by have := Fin.val_ne_of_ne hieq; omega) hnt
                · have hidx_real : idx ∈ resReal :=
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, k', hwi, hti, htj, htk⟩
                  have hidx_nmem : idx ∉ resReal.filter (fun i => π.length - k ≤ i.val) := by
                    intro h; have := (Finset.mem_filter.mp h).2; dsimp only [idx] at this; omega
                  have hcard_inc : (resReal.filter (fun i => π.length - k ≤ i.val)).card + 1 ≤
                      (resReal.filter (fun i => π.length - (k + 1) ≤ i.val)).card := by
                    have hsub' : insert idx (resReal.filter (fun i => π.length - k ≤ i.val)) ⊆
                        resReal.filter (fun i => π.length - (k + 1) ≤ i.val) := by
                      intro i hi
                      rcases Finset.mem_insert.mp hi with rfl | hi'
                      · exact Finset.mem_filter.mpr ⟨hidx_real, le_refl _⟩
                      · exact hfilt_sub hi'
                    calc _ = (insert idx (resReal.filter (fun i => π.length - k ≤ i.val))).card :=
                          (Finset.card_insert_of_notMem hidx_nmem).symm
                      _ ≤ _ := Finset.card_le_card hsub'
                  have hdc' : IsDerivCount baseF (R' :: πb) (r + 1) := by
                    rcases hRres with hr1 | hr2
                    · exact IsDerivCount.res hdc hj_prev.1 hk_prev.1 hr1
                    · exact IsDerivCount.res hdc hk_prev.1 hj_prev.1 hr2
                  refine ⟨R' :: πb, r + 1, fun i => if i = idx then R' else out i,
                    hdc', by omega, fun i hi hnt => ?_⟩
                  by_cases hieq : i = idx
                  · subst hieq; simp only [ite_true, List.mem_cons_self, true_and]; exact hRsub
                  · simp only [hieq, ite_false]
                    have hprev := hout i (by have := Fin.val_ne_of_ne hieq; omega) hnt
                    exact ⟨List.mem_cons_of_mem _ hprev.1, hprev.2⟩
    obtain ⟨πb, r, out, hdc, hr, hout⟩ := hcontract π.length (le_refl _)
    obtain ⟨i0, hi0_lt, hi0_eq⟩ := List.mem_iff_getElem.mp href.2
    have hnt0 : ¬ isTaut ⟨i0, hi0_lt⟩ := by
      dsimp only [isTaut]
      change ¬ Taut (substClause σ π[i0])
      rw [hi0_eq]
      simpa [substClause] using not_taut_empty
    have hout0 := hout ⟨i0, hi0_lt⟩ (by omega) hnt0
    have hemp_sub : out ⟨i0, hi0_lt⟩ = ∅ := by
      have hsub := hout0.2
      change out ⟨i0, hi0_lt⟩ ⊆ substClause σ π[i0] at hsub
      rw [hi0_eq] at hsub
      simpa [substClause] using hsub
    have hemp_mem : (∅ : Clause BaseV) ∈ πb := hemp_sub ▸ hout0.1
    have h6 := baseF_resCount_ge_six hdc hemp_mem
    have hle_all : (resReal.filter (fun i => π.length - π.length ≤ i.val)).card ≤ resReal.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  omega

theorem tree_lower {t N : ℕ} (ht : 0 < t)
    (nodes inner : Finset (List Bool)) (line : List Bool → Clause BigV) (cost : List Bool → ℕ)
    (hroot : [] ∈ nodes) (_hsub : inner ⊆ nodes) (hline0 : line [] = ∅)
    (hsum : (nodes \ inner).sum cost ≤ N)
    (hleaf : ∀ p ∈ nodes, p ∉ inner → line p ∈ big t ∧ cost p = 1)
    (hinner : ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    7 * t ≤ N := by
  classical
  let leaves := nodes \ inner
  have hleaves_le : leaves.card ≤ N := by
    have h1 : leaves.sum cost = leaves.card := by
      calc leaves.sum cost = leaves.sum (fun _ => 1) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have hp' := Finset.mem_sdiff.mp hp
            exact (hleaf p hp'.1 hp'.2).2
        _ = leaves.card := by simp
    rw [← h1]; exact hsum
  let sliceLeaves : ℕ → Finset (List Bool) := fun k =>
    leaves.filter (fun q => ∃ e : Edge, line q = step t e k)
  have hslice_ge : ∀ k < t, 7 ≤ (sliceLeaves k).card := by
    intro k hk
    let σ := sliceSubst k
    let subLeaves : List Bool → Finset (List Bool) := fun p =>
      (sliceLeaves k).filter (fun q => p <+: q)
    let desc : List Bool → Finset (List Bool) := fun p =>
      nodes.filter (fun q => p <+: q)
    have hrec : ∀ s (p : List Bool), (desc p).card ≤ s → p ∈ nodes →
        ¬ Taut (substClause σ (line p)) →
        ∃ (πb : List (Clause BaseV)) (r : ℕ) (C : Clause BaseV),
          IsDerivCount baseF πb r ∧ C ∈ πb ∧ C ⊆ substClause σ (line p) ∧
          1 + r ≤ (subLeaves p).card := by
      intro s
      induction s with
      | zero =>
        intro p hs hp _
        have hmem : p ∈ desc p := Finset.mem_filter.mpr ⟨hp, List.prefix_refl p⟩
        have hpos : 0 < (desc p).card := Finset.card_pos.mpr ⟨p, hmem⟩
        omega
      | succ s ih =>
        intro p hs hp hnt
        by_cases hpin : p ∈ inner
        · obtain ⟨hp0, hp1, hres⟩ := hinner p hpin
          have hsub0 : desc (p ++ [false]) ⊂ desc p := by
            refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, List.prefix_refl p⟩, ?_⟩
            · intro q hq
              obtain ⟨hqn, hpref⟩ := Finset.mem_filter.mp hq
              exact Finset.mem_filter.mpr ⟨hqn, (List.prefix_append p [false]).trans hpref⟩
            · intro h
              have hlen := ((Finset.mem_filter.mp h).2).length_le
              simp at hlen
          have hsub1 : desc (p ++ [true]) ⊂ desc p := by
            refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, List.prefix_refl p⟩, ?_⟩
            · intro q hq
              obtain ⟨hqn, hpref⟩ := Finset.mem_filter.mp hq
              exact Finset.mem_filter.mpr ⟨hqn, (List.prefix_append p [true]).trans hpref⟩
            · intro h
              have hlen := ((Finset.mem_filter.mp h).2).length_le
              simp at hlen
          have hc0 : (desc (p ++ [false])).card ≤ s := by
            have := Finset.card_lt_card hsub0; omega
          have hc1 : (desc (p ++ [true])).card ≤ s := by
            have := Finset.card_lt_card hsub1; omega
          have hdisj_sub : Disjoint (subLeaves (p ++ [false])) (subLeaves (p ++ [true])) := by
            rw [Finset.disjoint_left]
            intro q hq0 hq1
            obtain ⟨l0, hl0⟩ := (Finset.mem_filter.mp hq0).2
            obtain ⟨l1, hl1⟩ := (Finset.mem_filter.mp hq1).2
            rw [List.append_assoc] at hl0 hl1
            have hEq : [false] ++ l0 = [true] ++ l1 :=
              List.append_cancel_left (hl0.trans hl1.symm)
            simp at hEq
          have hsub_u : subLeaves (p ++ [false]) ∪ subLeaves (p ++ [true]) ⊆ subLeaves p := by
            intro q hq
            rcases Finset.mem_union.mp hq with hq0 | hq1
            · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq0
              exact Finset.mem_filter.mpr ⟨h1, (List.prefix_append p [false]).trans h2⟩
            · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq1
              exact Finset.mem_filter.mpr ⟨h1, (List.prefix_append p [true]).trans h2⟩
          have hcard_add : (subLeaves (p ++ [false])).card + (subLeaves (p ++ [true])).card ≤
              (subLeaves p).card := by
            rw [← Finset.card_union_of_disjoint hdisj_sub]
            exact Finset.card_le_card hsub_u
          by_cases ht0 : Taut (substClause σ (line (p ++ [false])))
          · have hnt1 : ¬ Taut (substClause σ (line (p ++ [true]))) :=
              fun ht1 => hnt (taut_of_taut_taut σ hres ht0 ht1)
            obtain ⟨π1, r1, C1, hd1, hm1, hs1, hle1⟩ := ih (p ++ [true]) hc1 hp1 hnt1
            have hsubR := subset_of_res_taut_left σ hres ht0 hnt
            exact ⟨π1, r1, C1, hd1, hm1, hs1.trans hsubR, by omega⟩
          · by_cases ht1 : Taut (substClause σ (line (p ++ [true])))
            · obtain ⟨π0, r0, C0, hd0, hm0, hs0, hle0⟩ := ih (p ++ [false]) hc0 hp0 ht0
              have hsubR := subset_of_res_taut_right σ hres ht1 hnt
              exact ⟨π0, r0, C0, hd0, hm0, hs0.trans hsubR, by omega⟩
            · obtain ⟨π0, r0, C0, hd0, hm0, hs0, hle0⟩ := ih (p ++ [false]) hc0 hp0 ht0
              obtain ⟨π1, r1, C1, hd1, hm1, hs1, hle1⟩ := ih (p ++ [true]) hc1 hp1 ht1
              rcases res_subst_step σ hres hs0 hs1 with h0 | h1 | ⟨R', hRres, hRsub⟩
              · exact ⟨π0, r0, C0, hd0, hm0, h0, by omega⟩
              · exact ⟨π1, r1, C1, hd1, hm1, h1, by omega⟩
              · have happ := isDerivCount_append hd0 hd1
                have hd' : IsDerivCount baseF (R' :: (π0 ++ π1)) (r0 + r1 + 1) := by
                  rcases hRres with hr1 | hr2
                  · exact IsDerivCount.res happ (List.mem_append_left _ hm0) (List.mem_append_right _ hm1) hr1
                  · exact IsDerivCount.res happ (List.mem_append_right _ hm1) (List.mem_append_left _ hm0) hr2
                exact ⟨R' :: (π0 ++ π1), r0 + r1 + 1, R', hd', List.mem_cons_self, hRsub, by omega⟩
        · obtain ⟨e, j, hj, hline⟩ := (hleaf p hp hpin).1
          have hjk : j = k := by
            by_contra hne
            apply hnt
            rw [hline]
            exact sliceSubst_step_taut hk hj hne
          subst hjk
          have hp_mem : p ∈ subLeaves p := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hp, hpin⟩, ⟨e, hline⟩⟩,
              List.prefix_refl p⟩
          have hcard1 : 1 ≤ (subLeaves p).card := Finset.card_pos.mpr ⟨p, hp_mem⟩
          have hσeq : substClause σ (line p) = baseClause e := by
            rw [hline]; exact sliceSubst_step_eq hk
          refine ⟨[baseClause e], 0, baseClause e, IsDerivCount.ax IsDerivCount.nil ⟨e, rfl⟩,
            List.mem_cons_self, by rw [hσeq], by omega⟩
    have hnt0 : ¬ Taut (substClause σ (line [])) := by
      rw [hline0]; simpa [substClause] using not_taut_empty
    obtain ⟨πb, r, C, hdc, hCmem, hCsub, hle⟩ := hrec (desc []).card [] (le_refl _) hroot hnt0
    have hC0 : C = ∅ := by
      rw [hline0] at hCsub
      simpa [substClause] using hCsub
    subst hC0
    have h6 := baseF_resCount_ge_six hdc hCmem
    have hsub_eq : subLeaves [] = sliceLeaves k := by
      ext q; simp [subLeaves]
    rw [hsub_eq] at hle
    omega
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range t) : Set ℕ) sliceLeaves := by
    intro k1 hk1 k2 hk2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    obtain ⟨e1, he1⟩ := (Finset.mem_filter.mp hq1).2
    obtain ⟨e2, he2⟩ := (Finset.mem_filter.mp hq2).2
    have hk1' : k1 < t := Finset.mem_range.mp hk1
    have hk2' : k2 < t := Finset.mem_range.mp hk2
    have hpair := step_injective ht hk1' hk2' (he1.symm.trans he2)
    exact hne hpair.2
  have hbi_sub : (Finset.range t).biUnion sliceLeaves ⊆ leaves := by
    intro q hq
    obtain ⟨k, _, hqk⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_filter.mp hqk).1
  calc 7 * t = ∑ _k ∈ Finset.range t, 7 := by simp [Nat.mul_comm]
    _ ≤ ∑ k ∈ Finset.range t, (sliceLeaves k).card :=
          Finset.sum_le_sum fun k hk => hslice_ge k (Finset.mem_range.mp hk)
    _ = ((Finset.range t).biUnion sliceLeaves).card := (Finset.card_biUnion hdisj).symm
    _ ≤ leaves.card := Finset.card_le_card hbi_sub
    _ ≤ N := hleaves_le

theorem isResolvent_chain_step {t : ℕ} (e : Edge) (k : ℕ) (hk : k + 1 < t) :
    IsResolvent
      ({((lit t e 0).1, !(lit t e 0).2), lit t e (k + 1)} : Clause BigV)
      (step t e (k + 1))
      ({((lit t e 0).1, !(lit t e 0).2), lit t e (k + 2)} : Clause BigV) := by
  have hlit_mid : lit t e (k + 1) = ((Sum.inr (e, k + 1) : BigV), true) := by
    simp [lit, show k + 1 ≠ t by omega]
  have hne_left : ((lit t e 0).1, !(lit t e 0).2) ≠ ((Sum.inr (e, k + 1) : BigV), true) := by
    simp [lit]
  have hne_right : lit t e (k + 2) ≠ ((Sum.inr (e, k + 1) : BigV), false) := by
    by_cases hkt : k + 2 = t
    · rw [hkt, lit_end (by omega)]; simp
    · rw [lit_mid (Nat.succ_ne_zero _) hkt]; simp
  refine ⟨Sum.inr (e, k + 1), by rw [hlit_mid]; simp, by rw [step, hlit_mid]; simp, ?_⟩
  rw [step, hlit_mid]
  ext l
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
    Bool.not_true]
  constructor
  · rintro (rfl | rfl)
    · left; exact ⟨hne_left, Or.inl rfl⟩
    · right; exact ⟨hne_right, Or.inr rfl⟩
  · rintro (⟨h1, rfl | rfl⟩ | ⟨h2, rfl | rfl⟩)
    · exact Or.inl rfl
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact Or.inr rfl

theorem isResolvent_lift_pair {C D R : Clause BaseV}
    (h : IsResolvent C D R) :
    IsResolvent (liftClause C) (liftClause D) (liftClause R) := by
  obtain ⟨u, hC, hD, rfl⟩ := h
  refine ⟨Sum.inl u, Finset.mem_image.mpr ⟨(u, true), hC, rfl⟩,
    Finset.mem_image.mpr ⟨(u, false), hD, rfl⟩, ?_⟩
  ext l
  simp only [liftClause, Finset.mem_image, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ⟨x, (⟨hxne, hxC⟩ | ⟨hxne, hxD⟩), rfl⟩
    · left; exact ⟨fun h => hxne (Prod.ext (Sum.inl.inj (Prod.mk.inj h).1) (Prod.mk.inj h).2),
        x, hxC, rfl⟩
    · right; exact ⟨fun h => hxne (Prod.ext (Sum.inl.inj (Prod.mk.inj h).1) (Prod.mk.inj h).2),
        x, hxD, rfl⟩
  · rintro (⟨hne, x, hxC, rfl⟩ | ⟨hne, x, hxD, rfl⟩)
    · exact ⟨x, Or.inl ⟨fun h => hne (by rw [h]), hxC⟩, rfl⟩
    · exact ⟨x, Or.inr ⟨fun h => hne (by rw [h]), hxD⟩, rfl⟩

theorem base_res1 : IsResolvent (baseClause 2) (baseClause 1) ({(0, true), (3, false)} : Clause BaseV) :=
  ⟨2, by decide, by decide, by decide⟩

theorem base_res2 : IsResolvent (baseClause 3) ({(0, true), (3, false)} : Clause BaseV) ({(0, true)} : Clause BaseV) :=
  ⟨3, by decide, by decide, by decide⟩

theorem base_res3 : IsResolvent (baseClause 4) (baseClause 1) ({(1, true), (3, false)} : Clause BaseV) :=
  ⟨2, by decide, by decide, by decide⟩

theorem base_res4 : IsResolvent (baseClause 5) ({(1, true), (3, false)} : Clause BaseV) ({(1, true)} : Clause BaseV) :=
  ⟨3, by decide, by decide, by decide⟩

theorem base_res5 : IsResolvent ({(0, true)} : Clause BaseV) (baseClause 0) ({(1, false)} : Clause BaseV) :=
  ⟨0, by decide, by decide, by decide⟩

theorem base_res6 : IsResolvent ({(1, true)} : Clause BaseV) ({(1, false)} : Clause BaseV) (∅ : Clause BaseV) :=
  ⟨1, by decide, by decide, by decide⟩

theorem chain_derivation {t : ℕ} (e : Edge) :
    ∀ k < t, ∀ π : List (Clause BigV), IsDerivation (big t) π →
      ∃ π', IsDerivation (big t) π' ∧
        (∀ C ∈ π, C ∈ π') ∧
        ({((lit t e 0).1, !(lit t e 0).2), lit t e (k + 1)} : Clause BigV) ∈ π' ∧
        π'.length = π.length + (2 * k + 1)
  | 0, hk, π, hπ =>
    ⟨step t e 0 :: π, IsDerivation.ax hπ ⟨e, 0, hk, rfl⟩,
      fun _ hC => List.mem_cons_of_mem _ hC, List.mem_cons_self, by simp⟩
  | k + 1, hk, π, hπ => by
    obtain ⟨π1, hπ1, hsub1, hmem1, hlen1⟩ := chain_derivation e k (by omega) π hπ
    let π2 := step t e (k + 1) :: π1
    have hπ2 : IsDerivation (big t) π2 := IsDerivation.ax hπ1 ⟨e, k + 1, hk, rfl⟩
    let R : Clause BigV := {((lit t e 0).1, !(lit t e 0).2), lit t e (k + 2)}
    have hres := isResolvent_chain_step e k hk
    refine ⟨R :: π2, IsDerivation.res hπ2 (List.mem_cons_of_mem _ hmem1) List.mem_cons_self hres,
      fun _ hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub1 _ hC)),
      List.mem_cons_self, ?_⟩
    simp [π2, hlen1]
    omega

theorem chain_end_eq {t : ℕ} (ht : 0 < t) (e : Edge) :
    ({((lit t e 0).1, !(lit t e 0).2), lit t e ((t - 1) + 1)} : Clause BigV) =
      liftClause (baseClause e) := by
  have h1 : (t - 1) + 1 = t := by omega
  rw [h1, liftClause_baseClause]
  simp [lit, show t ≠ 0 by omega]

theorem dag_upper {t L : ℕ} (ht : 0 < t) (hL : 12 * t ≤ L) :
    ∃ π, IsRefutation (big t) π ∧ π.length ≤ L := by
  have hstep : ∀ (e : Edge) (π : List (Clause BigV)), IsDerivation (big t) π →
      ∃ π', IsDerivation (big t) π' ∧ (∀ C ∈ π, C ∈ π') ∧
        liftClause (baseClause e) ∈ π' ∧ π'.length = π.length + (2 * t - 1) := by
    intro e π hπ
    obtain ⟨π', h1, h2, h3, h4⟩ := chain_derivation e (t - 1) (by omega) π hπ
    rw [chain_end_eq ht e] at h3
    exact ⟨π', h1, h2, h3, by omega⟩
  obtain ⟨π0, hd0, _, hm0, hl0⟩ := hstep 0 [] IsDerivation.nil
  obtain ⟨π1, hd1, hs1, hm1, hl1⟩ := hstep 1 π0 hd0
  obtain ⟨π2, hd2, hs2, hm2, hl2⟩ := hstep 2 π1 hd1
  obtain ⟨π3, hd3, hs3, hm3, hl3⟩ := hstep 3 π2 hd2
  obtain ⟨π4, hd4, hs4, hm4, hl4⟩ := hstep 4 π3 hd3
  obtain ⟨π5, hd5, hs5, hm5, hl5⟩ := hstep 5 π4 hd4
  have hc0 : liftClause (baseClause 0) ∈ π5 := hs5 _ (hs4 _ (hs3 _ (hs2 _ (hs1 _ hm0))))
  have hc1 : liftClause (baseClause 1) ∈ π5 := hs5 _ (hs4 _ (hs3 _ (hs2 _ hm1)))
  have hc2 : liftClause (baseClause 2) ∈ π5 := hs5 _ (hs4 _ (hs3 _ hm2))
  have hc3 : liftClause (baseClause 3) ∈ π5 := hs5 _ (hs4 _ hm3)
  have hc4 : liftClause (baseClause 4) ∈ π5 := hs5 _ hm4
  have hc5 : liftClause (baseClause 5) ∈ π5 := hm5
  let r1 := liftClause ({(0, true), (3, false)} : Clause BaseV)
  let r2 := liftClause ({(0, true)} : Clause BaseV)
  let r3 := liftClause ({(1, true), (3, false)} : Clause BaseV)
  let r4 := liftClause ({(1, true)} : Clause BaseV)
  let r5 := liftClause ({(1, false)} : Clause BaseV)
  let r6 := liftClause (∅ : Clause BaseV)
  have hr6_eq : r6 = (∅ : Clause BigV) := by simp [r6, liftClause]
  have hd_a := IsDerivation.res hd5 hc2 hc1 (isResolvent_lift_pair base_res1)
  have hd_b := IsDerivation.res hd_a (List.mem_cons_of_mem _ hc3) List.mem_cons_self
    (isResolvent_lift_pair base_res2)
  have hd_c := IsDerivation.res hd_b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc4))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc1)) (isResolvent_lift_pair base_res3)
  have hd_d := IsDerivation.res hd_c
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc5)))
    List.mem_cons_self (isResolvent_lift_pair base_res4)
  have hd_e := IsDerivation.res hd_d
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc0))))
    (isResolvent_lift_pair base_res5)
  have hd_f := IsDerivation.res hd_e
    (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
    (isResolvent_lift_pair base_res6)
  refine ⟨r6 :: r5 :: r4 :: r3 :: r2 :: r1 :: π5, ⟨hd_f, by rw [← hr6_eq]; exact List.mem_cons_self⟩, ?_⟩
  simp only [List.length_cons, hl5, hl4, hl3, hl2, hl1, hl0, List.length_nil]
  omega

structure ResTree (F : Set (Clause BigV)) (rootClause : Clause BigV) where
  nodes : Finset (List Bool)
  inner : Finset (List Bool)
  line : List Bool → Clause BigV
  hroot : [] ∈ nodes
  hsub : inner ⊆ nodes
  hline : line [] = rootClause
  hleaf : ∀ p ∈ nodes, p ∉ inner → line p ∈ F
  hpar : ∀ (p : List Bool) (a : Bool), p ++ [a] ∈ nodes → p ∈ inner
  hinner : ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
    IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)

def ResTree.leaf {F : Set (Clause BigV)} {C : Clause BigV} (hC : C ∈ F) : ResTree F C where
  nodes := {[]}
  inner := ∅
  line := fun _ => C
  hroot := Finset.mem_singleton_self []
  hsub := Finset.empty_subset _
  hline := rfl
  hleaf := fun _ _ _ => hC
  hpar := fun p a h => by simp at h
  hinner := fun p h => absurd h (Finset.notMem_empty p)

theorem ResTree.leaf_card {F : Set (Clause BigV)} {C : Clause BigV} (hC : C ∈ F) :
    ((ResTree.leaf hC).nodes \ (ResTree.leaf hC).inner).card = 1 := by
  simp [ResTree.leaf]

def ResTree.join {F : Set (Clause BigV)} {C0 C1 R : Clause BigV}
    (T0 : ResTree F C0) (T1 : ResTree F C1) (hres : IsResolvent C0 C1 R) : ResTree F R where
  nodes := insert [] (T0.nodes.image (false :: ·) ∪ T1.nodes.image (true :: ·))
  inner := insert [] (T0.inner.image (false :: ·) ∪ T1.inner.image (true :: ·))
  line := fun p => match p with
    | [] => R
    | false :: q => T0.line q
    | true :: q => T1.line q
  hroot := Finset.mem_insert_self [] _
  hsub := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact Finset.mem_insert_self [] _
    · apply Finset.mem_insert_of_mem
      rcases Finset.mem_union.mp hp' with h0 | h1
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h0
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, T0.hsub hq, rfl⟩)
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, T1.hsub hq, rfl⟩)
  hline := rfl
  hleaf := by
    intro p hp hpin
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact absurd (Finset.mem_insert_self [] _) hpin
    · rcases Finset.mem_union.mp hp' with h0 | h1
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h0
        have hqn : q ∉ T0.inner := fun hqi =>
          hpin (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hqi, rfl⟩)))
        exact T0.hleaf q hq hqn
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
        have hqn : q ∉ T1.inner := fun hqi =>
          hpin (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hqi, rfl⟩)))
        exact T1.hleaf q hq hqn
  hpar := by
    intro p a hpa
    cases p with
    | nil => exact Finset.mem_insert_self [] _
    | cons b q =>
      have hne : (b :: q) ++ [a] ≠ [] := by simp
      have hmem := (Finset.mem_insert.mp hpa).resolve_left hne
      cases b
      · rcases Finset.mem_union.mp hmem with h0 | h1
        · obtain ⟨r, hr, hreq⟩ := Finset.mem_image.mp h0
          have hq : q ++ [a] = r := (List.cons.inj hreq).2.symm
          rw [← hq] at hr
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, T0.hpar q a hr, rfl⟩))
        · obtain ⟨r, _, hreq⟩ := Finset.mem_image.mp h1
          simp at hreq
      · rcases Finset.mem_union.mp hmem with h0 | h1
        · obtain ⟨r, _, hreq⟩ := Finset.mem_image.mp h0
          simp at hreq
        · obtain ⟨r, hr, hreq⟩ := Finset.mem_image.mp h1
          have hq : q ++ [a] = r := (List.cons.inj hreq).2.symm
          rw [← hq] at hr
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, T1.hpar q a hr, rfl⟩))
  hinner := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], T0.hroot, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[], T1.hroot, rfl⟩)), ?_⟩
      simpa [T0.hline, T1.hline] using hres
    · rcases Finset.mem_union.mp hp' with h0 | h1
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h0
        obtain ⟨h1, h2, h3⟩ := T0.hinner q hq
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [false], h1, rfl⟩)),
          Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [true], h2, rfl⟩)), h3⟩
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨h1, h2, h3⟩ := T1.hinner q hq
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [false], h1, rfl⟩)),
          Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [true], h2, rfl⟩)), h3⟩

theorem ResTree.join_card {F : Set (Clause BigV)} {C0 C1 R : Clause BigV}
    (T0 : ResTree F C0) (T1 : ResTree F C1) (hres : IsResolvent C0 C1 R) :
    ((ResTree.join T0 T1 hres).nodes \ (ResTree.join T0 T1 hres).inner).card =
      (T0.nodes \ T0.inner).card + (T1.nodes \ T1.inner).card := by
  have heq : (ResTree.join T0 T1 hres).nodes \ (ResTree.join T0 T1 hres).inner =
      (T0.nodes \ T0.inner).image (false :: ·) ∪ (T1.nodes \ T1.inner).image (true :: ·) := by
    ext p
    simp only [ResTree.join, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨rfl | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩), hnot⟩
      · exact absurd (Or.inl rfl) hnot
      · left
        refine ⟨q, ⟨hq, fun hqi => hnot (Or.inr (Or.inl ⟨q, hqi, rfl⟩))⟩, rfl⟩
      · right
        refine ⟨q, ⟨hq, fun hqi => hnot (Or.inr (Or.inr ⟨q, hqi, rfl⟩))⟩, rfl⟩
    · rintro (⟨q, ⟨hq, hqn⟩, rfl⟩ | ⟨q, ⟨hq, hqn⟩, rfl⟩)
      · refine ⟨Or.inr (Or.inl ⟨q, hq, rfl⟩), ?_⟩
        rintro (h0 | (⟨r, hr, hreq⟩ | ⟨r, _, hreq⟩))
        · simp at h0
        · exact hqn ((List.cons.inj hreq).2 ▸ hr)
        · simp at hreq
      · refine ⟨Or.inr (Or.inr ⟨q, hq, rfl⟩), ?_⟩
        rintro (h0 | (⟨r, _, hreq⟩ | ⟨r, hr, hreq⟩))
        · simp at h0
        · simp at hreq
        · exact hqn ((List.cons.inj hreq).2 ▸ hr)
  have hdisj : Disjoint ((T0.nodes \ T0.inner).image (false :: ·))
      ((T1.nodes \ T1.inner).image (true :: ·)) := by
    rw [Finset.disjoint_left]
    intro p h0 h1
    obtain ⟨q0, _, rfl⟩ := Finset.mem_image.mp h0
    obtain ⟨q1, _, hreq⟩ := Finset.mem_image.mp h1
    simp at hreq
  rw [heq, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
    Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)]

def chainTree (t : ℕ) (e : Edge) :
    ∀ (k : ℕ) (hk : k < t),
      ResTree (big t) ({((lit t e 0).1, !(lit t e 0).2), lit t e (k + 1)} : Clause BigV)
  | 0, hk => ResTree.leaf ⟨e, 0, hk, rfl⟩
  | k + 1, hk =>
      ResTree.join (chainTree t e k (by omega)) (ResTree.leaf ⟨e, k + 1, hk, rfl⟩)
        (isResolvent_chain_step e k hk)

theorem chainTree_card (t : ℕ) (e : Edge) :
    ∀ (k : ℕ) (hk : k < t),
      ((chainTree t e k hk).nodes \ (chainTree t e k hk).inner).card = k + 1
  | 0, _hk => ResTree.leaf_card _
  | k + 1, hk => by
    unfold chainTree
    rw [ResTree.join_card, chainTree_card t e k (by omega)]
    simp [ResTree.leaf]

def ResTree.cast {F : Set (Clause BigV)} {C1 C2 : Clause BigV}
    (h : C1 = C2) (T : ResTree F C1) : ResTree F C2 where
  nodes := T.nodes
  inner := T.inner
  line := T.line
  hroot := T.hroot
  hsub := T.hsub
  hline := T.hline.trans h
  hleaf := T.hleaf
  hpar := T.hpar
  hinner := T.hinner

def baseTree (t : ℕ) (ht : 0 < t) (e : Edge) : ResTree (big t) (liftClause (baseClause e)) :=
  ResTree.cast (chain_end_eq ht e) (chainTree t e (t - 1) (by omega))

theorem baseTree_card (t : ℕ) (ht : 0 < t) (e : Edge) :
    ((baseTree t ht e).nodes \ (baseTree t ht e).inner).card = t := by
  have h := chainTree_card t e (t - 1) (by omega)
  exact h.trans (by omega)

theorem tree_upper {t N : ℕ} (ht : 0 < t) (hN : 7 * t ≤ N) :
    ∃ (nodes inner : Finset (List Bool)) (line : List Bool → Clause BigV) (cost : List Bool → ℕ),
      [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
      (nodes \ inner).sum cost ≤ N ∧
      (∀ p ∈ nodes, p ∉ inner → line p ∈ big t ∧ cost p = 1) ∧
      (∀ (p : List Bool) (a : Bool), p ++ [a] ∈ nodes → p ∈ inner) ∧
      ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
        IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) := by
  let T0 := baseTree t ht 0
  let T1 := baseTree t ht 1
  let T2 := baseTree t ht 2
  let T3 := baseTree t ht 3
  let T4 := baseTree t ht 4
  let T5 := baseTree t ht 5
  let Ta := ResTree.join T2 T1 (isResolvent_lift_pair base_res1)
  let Tb := ResTree.join T3 Ta (isResolvent_lift_pair base_res2)
  let Tc := ResTree.join T4 T1 (isResolvent_lift_pair base_res3)
  let Td := ResTree.join T5 Tc (isResolvent_lift_pair base_res4)
  let Te := ResTree.join Tb T0 (isResolvent_lift_pair base_res5)
  let Tf := ResTree.join Td Te (isResolvent_lift_pair base_res6)
  have hcard : (Tf.nodes \ Tf.inner).card = 7 * t := by
    simp only [Tf, Te, Td, Tc, Tb, Ta, ResTree.join_card, T0, T1, T2, T3, T4, T5, baseTree_card]
    omega
  have hline0 : Tf.line [] = (∅ : Clause BigV) := by
    rw [Tf.hline]
    simp [liftClause]
  refine ⟨Tf.nodes, Tf.inner, Tf.line, fun _ => 1, Tf.hroot, Tf.hsub, hline0, ?_,
    fun p hp hpin => ⟨Tf.hleaf p hp hpin, rfl⟩, Tf.hpar, Tf.hinner⟩
  simp only [Finset.sum_const, smul_eq_mul, mul_one, hcard]
  exact hN

end PEqualNP.Outside.L_pcx_287_aux

theorem PEqualNP.Outside.L_pcx_287 : (∀ t : ℕ, 0 < t →
  let n := 4
  let m := 6
  let src : Fin m → Fin n × Bool := ![(0,true),(2,true),(0,false),(0,false),(1,false),(1,false)]
  let dst : Fin m → Fin n × Bool := ![(1,false),(3,false),(2,true),(3,true),(2,true),(3,true)]
  let len := fun _ : Fin m => t
  let V := Fin n ⊕ (Fin m × ℕ)
  let lit := fun (e : Fin m) (j : ℕ) =>
    if j = 0 then ((Sum.inl (src e).1 : V), (src e).2)
    else if j = len e then ((Sum.inl (dst e).1 : V), (dst e).2)
    else ((Sum.inr (e,j) : V), true)
  let step := fun (e : Fin m) (j : ℕ) =>
    ({((lit e j).1, !(lit e j).2), lit e (j+1)} : PEqualNP.ProofComplexity.Clause V)
  let big : Set (PEqualNP.ProofComplexity.Clause V) := {C | ∃ e j, j < len e ∧ C = step e j}
  let tree := fun (leaf : PEqualNP.ProofComplexity.Clause V → ℕ → Prop) (K : ℕ) =>
    ∃ (nodes inner : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause V)
      (cost : List Bool → ℕ), [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
      (nodes \ inner).sum cost ≤ K ∧
      (∀ p ∈ nodes, p ∉ inner → leaf (line p) (cost p)) ∧
      (∀ (p : List Bool) (a : Bool), p ++ [a] ∈ nodes → p ∈ inner) ∧
      ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
        PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)
  ∀ L N : ℕ,
    ((∃ π, PEqualNP.ProofComplexity.IsRefutation big π ∧ π.length ≤ L) ↔ 12*t ≤ L) ∧
    (tree (fun C k => C ∈ big ∧ k = 1) N ↔ 7*t ≤ N)) := by
  intro t ht n m src dst len V lit step big tree L N
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨π, href, hlen⟩
    exact le_trans (PEqualNP.Outside.L_pcx_287_aux.dag_lower ht href) hlen
  · exact PEqualNP.Outside.L_pcx_287_aux.dag_upper ht
  · rintro ⟨nodes, inner, line, cost, hroot, hsub, hline0, hsum, hleaf, _, hinner⟩
    exact PEqualNP.Outside.L_pcx_287_aux.tree_lower ht nodes inner line cost
      hroot hsub hline0 hsum hleaf hinner
  · exact PEqualNP.Outside.L_pcx_287_aux.tree_upper ht
