import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_245_aux

open MvPolynomial PEqualNP.ProofComplexity

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  fin_cases c <;> decide

theorem add_self_eq_zero {n : ℕ} (p : Poly n) : p + p = 0 := by
  ext d
  rw [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero]
  exact zmod2_add_self (p.coeff d)

theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact absurd rfl h
  · rfl

theorem coeff_add' {n : ℕ} (p q : Poly n) (d : Fin n →₀ ℕ) :
    (p + q).coeff d = p.coeff d + q.coeff d := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

noncomputable def indF {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

theorem indF_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    indF S i = if i ∈ S then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [indF]
  | @insert j S hj ih =>
    unfold indF
    rw [Finset.sum_insert hj, Finsupp.add_apply, Finsupp.single_apply]
    change (if j = i then 1 else 0) + indF S i = if i ∈ insert j S then 1 else 0
    rw [ih]
    by_cases hji : j = i
    · subst hji; simp [hj]
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]

theorem indF_support {n : ℕ} (S : Finset (Fin n)) : (indF S).support = S := by
  ext i
  rw [Finsupp.mem_support_iff, indF_apply]
  by_cases hi : i ∈ S <;> simp [hi]

theorem indF_sum {n : ℕ} (S : Finset (Fin n)) : (indF S).sum (fun _ k => k) = S.card := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [indF_apply, Finset.sum_boole, Nat.cast_id]
  congr 1
  ext i
  simp

theorem indF_inj {n : ℕ} {S T : Finset (Fin n)} (h : indF S = indF T) : S = T := by
  rw [← indF_support S, ← indF_support T, h]

noncomputable def mon {n : ℕ} (S : Finset (Fin n)) : Poly n :=
  ∏ i ∈ S, X i

theorem mon_eq_monomial {n : ℕ} (S : Finset (Fin n)) : mon S = monomial (indF S) 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mon, indF, monomial_zero']
  | @insert i S hi ih =>
    rw [mon, Finset.prod_insert hi, ← mon, ih, X, monomial_mul_monomial, mul_one]
    congr 1
    unfold indF
    rw [Finset.sum_insert hi]

theorem coeff_mon {n : ℕ} (S T : Finset (Fin n)) :
    (mon S).coeff (indF T) = if S = T then 1 else 0 := by
  rw [mon_eq_monomial, coeff_monomial]
  by_cases h : S = T
  · subst h; simp
  · have hne : indF S ≠ indF T := fun e => h (indF_inj e)
    simp [h, hne]

noncomputable def ml {n : ℕ} (d : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  d.mapRange (fun k => min k 1) rfl

theorem ml_eq_indF_support {n : ℕ} (d : Fin n →₀ ℕ) : ml d = indF d.support := by
  ext i
  rw [ml, Finsupp.mapRange_apply, indF_apply]
  by_cases h : d i = 0
  · have hns : i ∉ d.support := Finsupp.notMem_support_iff.mpr h
    simp [h, hns]
  · have hs : i ∈ d.support := Finsupp.mem_support_iff.mpr h
    simp only [hs, ite_true]
    omega

noncomputable def nf {n : ℕ} (p : Poly n) : Poly n :=
  ∑ d ∈ p.support, monomial (ml d) (p.coeff d)

theorem nf_eq_sum_indF {n : ℕ} (p : Poly n) :
    nf p = ∑ d ∈ p.support, monomial (indF d.support) (p.coeff d) := by
  unfold nf
  refine Finset.sum_congr rfl fun d _ => by rw [ml_eq_indF_support]

theorem nf_monomial {n : ℕ} (d : Fin n →₀ ℕ) (c : ZMod 2) :
    nf (monomial d c) = monomial (indF d.support) c := by
  by_cases hc : c = 0
  · subst hc; simp [nf]
  · rw [nf_eq_sum_indF, support_monomial, ite_eq_right_of_eq_false _ _ (eq_false hc),
      Finset.sum_singleton, coeff_monomial, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem nf_add {n : ℕ} (p q : Poly n) : nf (p + q) = nf p + nf q := by
  classical
  have aux : ∀ (s : Finset (Fin n →₀ ℕ)) (r : Poly n), r.support ⊆ s →
      nf r = ∑ d ∈ s, monomial (indF d.support) (r.coeff d) := by
    intro s r hs
    rw [nf_eq_sum_indF]
    apply Finset.sum_subset hs
    intro d _ hd
    have h0 : r.coeff d = 0 := notMem_support_iff.mp hd
    rw [h0, map_zero]
  let s := p.support ∪ q.support
  have hpq : (p + q).support ⊆ s := support_add
  rw [aux s (p + q) hpq, aux s p Finset.subset_union_left, aux s q Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_add', map_add]

theorem nf_zero {n : ℕ} : nf (0 : Poly n) = 0 := by
  simp [nf]

theorem nf_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Poly n) :
    nf (∑ a ∈ s, f a) = ∑ a ∈ s, nf (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nf_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, nf_add, ih]

theorem nf_mul_monomial {n : ℕ} (d1 d2 : Fin n →₀ ℕ) (c1 c2 : ZMod 2) :
    nf (monomial d1 c1 * monomial d2 c2) = monomial (indF (d1.support ∪ d2.support)) (c1 * c2) := by
  rw [monomial_mul_monomial, nf_monomial]
  apply congrArg (fun s => monomial (indF s) (c1 * c2))
  ext i
  rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff,
    Finsupp.mem_support_iff, Finsupp.add_apply]
  omega

theorem nf_mul_boolAx {n : ℕ} (p : Poly n) (v : Fin n) :
    nf (p * (X v * X v + X v)) = 0 := by
  rw [p.as_sum, Finset.sum_mul, nf_sum]
  apply Finset.sum_eq_zero
  intro d _
  rw [mul_add, nf_add]
  have h1 : (X v : Poly n) * X v = monomial (Finsupp.single v 2) 1 := by
    rw [X, monomial_mul_monomial, mul_one, ← Finsupp.single_add]
  have h2 : (X v : Poly n) = monomial (Finsupp.single v 1) 1 := rfl
  rw [h1, h2, nf_mul_monomial, nf_mul_monomial]
  have hsupp : (Finsupp.single v 2).support = (Finsupp.single v 1).support := by
    ext i; simp
  rw [hsupp, add_self_eq_zero]

theorem nf_monomial_mul_mon {n : ℕ} (d : Fin n →₀ ℕ) (S : Finset (Fin n)) :
    nf (monomial d (1 : ZMod 2) * mon S) = mon (d.support ∪ S) := by
  rw [mon_eq_monomial, nf_mul_monomial, mul_one, indF_support, mon_eq_monomial]

theorem card_support_le_sum {n : ℕ} (d : Fin n →₀ ℕ) : d.support.card ≤ d.sum (fun _ k => k) := by
  rw [Finsupp.sum]
  calc d.support.card = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hne : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      omega

theorem totalDegree_X_le_one {n : ℕ} (j : Fin n) : (X j : Poly n).totalDegree ≤ 1 := by
  rw [X]
  exact (totalDegree_monomial_le (Finsupp.single j 1) (1 : ZMod 2)).trans (by simp)

theorem totalDegree_boolAx {n : ℕ} (v : Fin n) :
    (X v * X v + X v : Poly n).totalDegree = 2 := by
  have h1 : (X v : Poly n) * X v = monomial (Finsupp.single v 2) 1 := by
    rw [X, monomial_mul_monomial, mul_one, ← Finsupp.single_add]
  have h2 : (X v : Poly n) = monomial (Finsupp.single v 1) 1 := rfl
  apply le_antisymm
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · have := totalDegree_mul (X v : Poly n) (X v)
      have := totalDegree_X_le_one v
      omega
    · have := totalDegree_X_le_one v; omega
  · have hmem : Finsupp.single v 2 ∈ (X v * X v + X v : Poly n).support := by
      rw [mem_support_iff, coeff_add', h1, h2, coeff_monomial, coeff_monomial]
      have hne : Finsupp.single v 1 ≠ Finsupp.single v 2 := by
        intro h
        have := congrArg (fun f => f v) h
        simp at this
      simp [hne]
    have hle : (Finsupp.single v 2).sum (fun _ k => k) ≤ (X v * X v + X v : Poly n).totalDegree :=
      Finset.le_sup (f := fun e : Fin n →₀ ℕ => e.sum (fun _ k => k)) hmem
    rw [Finsupp.sum_single_index (by simp)] at hle
    exact hle

theorem totalDegree_clausePoly_le {n : ℕ} (C : Clause (Fin n)) :
    (clausePoly C).totalDegree ≤ C.card := by
  classical
  induction C using Finset.induction_on with
  | empty => simp [clausePoly]
  | @insert l C hl ih =>
    rw [clausePoly, Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    have h1 := totalDegree_mul (if l.2 = true then 1 + X l.1 else X l.1 : Poly n) (clausePoly C)
    have h2 : (if l.2 = true then 1 + X l.1 else X l.1 : Poly n).totalDegree ≤ 1 := by
      cases l.2
      · simp only [Bool.false_eq_true, ite_false]; exact totalDegree_X_le_one l.1
      · simp only [ite_true]
        exact (totalDegree_add (1 : Poly n) (X l.1)).trans (max_le (by simp) (totalDegree_X_le_one l.1))
    rw [clausePoly] at h1 ih
    omega

noncomputable def indP {n : ℕ} (v : Fin n) (a : Bool) : Poly n :=
  if a = true then X v else 1 + X v

theorem totalDegree_indP_le {n : ℕ} (v : Fin n) (a : Bool) :
    (indP v a).totalDegree ≤ 1 := by
  cases a
  · simp only [indP, Bool.false_eq_true, ite_false]
    exact (totalDegree_add (1 : Poly n) (X v)).trans (max_le (by simp) (totalDegree_X_le_one v))
  · simp only [indP, ite_true]
    exact totalDegree_X_le_one v

theorem indP_add_not {n : ℕ} (v : Fin n) (a : Bool) :
    indP v a + indP v (!a) = 1 := by
  cases a
  · simp only [indP, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
    calc (1 + X v : Poly n) + X v = 1 + (X v + X v) := by ring
      _ = 1 + 0 := by rw [add_self_eq_zero]
      _ = 1 := add_zero 1
  · simp only [indP, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    calc (X v : Poly n) + (1 + X v) = 1 + (X v + X v) := by ring
      _ = 1 + 0 := by rw [add_self_eq_zero]
      _ = 1 := add_zero 1

theorem indP_false_add_true {n : ℕ} (v : Fin n) :
    indP v false + indP v true = 1 :=
  indP_add_not v false

theorem indP_not_eq {n : ℕ} (v : Fin n) (a : Bool) :
    indP v (!a) = 1 + indP v a := by
  calc indP v (!a) = (indP v a + indP v (!a)) + indP v a := by
        rw [add_comm (indP v a), add_assoc, add_self_eq_zero, add_zero]
    _ = 1 + indP v a := by rw [indP_add_not]

theorem clausePoly_pair {n : ℕ} {u v : Fin n} (huv : u ≠ v) (a b : Bool) :
    clausePoly ({(u, !a), (v, !b)} : Clause (Fin n)) = indP u a * indP v b := by
  have hne : (u, !a) ≠ (v, !b) := fun h => huv (Prod.mk.inj h).1
  unfold clausePoly
  rw [Finset.prod_pair hne]
  cases a <;> cases b <;> simp [indP]

theorem totalDegree_clausePoly_pair {n : ℕ} {u v : Fin n} (huv : u ≠ v) (a b : Bool) :
    (clausePoly ({(u, !a), (v, !b)} : Clause (Fin n))).totalDegree = 2 := by
  apply le_antisymm
  · exact (totalDegree_clausePoly_le _).trans Finset.card_le_two
  · rw [clausePoly_pair huv]
    have hcoeff : (indP u a * indP v b).coeff (indF {u, v}) = 1 := by
      have hne0 : (∅ : Finset (Fin n)) ≠ {u, v} := by
        intro h; have : u ∈ (∅ : Finset (Fin n)) := h ▸ Finset.mem_insert_self u {v}; simp at this
      have hneu : ({u} : Finset (Fin n)) ≠ {u, v} := by
        intro h
        have : v ∈ ({u} : Finset (Fin n)) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
        simp [huv.symm] at this
      have hnev : ({v} : Finset (Fin n)) ≠ {u, v} := by
        intro h
        have : u ∈ ({v} : Finset (Fin n)) := h ▸ Finset.mem_insert_self u {v}
        simp [huv] at this
      have h1 : (1 : Poly n) = mon ∅ := by simp [mon]
      have hu : (X u : Poly n) = mon {u} := by simp [mon]
      have hv : (X v : Poly n) = mon {v} := by simp [mon]
      have huv_m : (X u * X v : Poly n) = mon {u, v} := by simp [mon, Finset.prod_pair huv]
      cases a <;> cases b
      · have hexp : indP u false * indP v false = mon ∅ + mon {u} + mon {v} + mon {u, v} := by
          simp only [indP, Bool.false_eq_true, ite_false]
          rw [← h1, ← hu, ← hv, ← huv_m]; ring
        rw [hexp, coeff_add', coeff_add', coeff_add', coeff_mon, coeff_mon, coeff_mon, coeff_mon]
        simp [hne0, hneu, hnev]
      · have hexp : indP u false * indP v true = mon {v} + mon {u, v} := by
          simp only [indP, Bool.false_eq_true, ite_false, ite_true]
          rw [← hv, ← huv_m]; ring
        rw [hexp, coeff_add', coeff_mon, coeff_mon]
        simp [hnev]
      · have hexp : indP u true * indP v false = mon {u} + mon {u, v} := by
          simp only [indP, Bool.false_eq_true, ite_false, ite_true]
          rw [← hu, ← huv_m]; ring
        rw [hexp, coeff_add', coeff_mon, coeff_mon]
        simp [hneu]
      · have hexp : indP u true * indP v true = mon {u, v} := by
          simp only [indP, ite_true]; exact huv_m
        rw [hexp, coeff_mon]
        simp
    have hmem : indF {u, v} ∈ (indP u a * indP v b).support := by
      rw [mem_support_iff, hcoeff]; decide
    have hle := Finset.le_sup (f := fun e : Fin n →₀ ℕ => e.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_pair huv] at hle
    exact hle

def pos (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n :=
  ⟨i % n, Nat.mod_lt _ hn⟩

theorem pos_ne_succ {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n) (i : Fin n) :
    i ≠ pos n hn (i.val + 1) := by
  intro h
  have hv : i.val = (i.val + 1) % n := congrArg Fin.val h
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

theorem pos_succ_pos {n : ℕ} (hn : 0 < n) (k : ℕ) :
    pos n hn ((pos n hn k).val + 1) = pos n hn (k + 1) := by
  apply Fin.ext
  change (k % n + 1) % n = (k + 1) % n
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem pos_add_n {n : ℕ} (hn : 0 < n) (k : ℕ) :
    pos n hn (k + n) = pos n hn k := by
  apply Fin.ext
  exact Nat.add_mod_right k n

def blockers (n : ℕ) (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) :
    Finset (Clause (Fin n)) :=
  let blocks := (Finset.univ : Finset (Fin n × (Bool × Bool))).filter
    (fun z => T z.1 z.2.1 z.2.2 = false)
  blocks.image (fun row =>
    ({(row.1, !row.2.1), (pos n hn (row.1.val + 1), !row.2.2)} : Clause (Fin n)))

def rejects (n : ℕ) (hn : 0 < n) (candidate : Fin n → Bool → Bool → Bool) : Prop :=
  ¬ ∃ x : Fin n → Bool, ∀ i : Fin n, candidate i (x i) (x (pos n hn (i.val + 1))) = true

theorem mem_blockers_of_false {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    {i : Fin n} {a b : Bool} (h : T i a b = false) :
    ({(i, !a), (pos n hn (i.val + 1), !b)} : Clause (Fin n)) ∈ blockers n hn T := by
  unfold blockers
  refine Finset.mem_image.mpr ⟨(i, (a, b)), ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

theorem mem_blockers_pos_of_false {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    {k : ℕ} {a b : Bool} (h : T (pos n hn k) a b = false) :
    ({(pos n hn k, !a), (pos n hn (k + 1), !b)} : Clause (Fin n)) ∈ blockers n hn T := by
  rw [← pos_succ_pos hn k]
  exact mem_blockers_of_false hn h

theorem totalDegree_mem_blockers {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n)
    {T : Fin n → Bool → Bool → Bool} {C : Clause (Fin n)} (hC : C ∈ blockers n hn T) :
    (clausePoly C).totalDegree = 2 := by
  unfold blockers at hC
  obtain ⟨⟨i, a, b⟩, _, rfl⟩ := Finset.mem_image.mp hC
  exact totalDegree_clausePoly_pair (pos_ne_succ hn h2 i) a b

theorem not_pcRefutable_one {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n)
    (T : Fin n → Bool → Bool → Bool) :
    ¬ PCRefutable (cnfSystem (↑(blockers n hn T) : Set (Clause (Fin n)))) 1 := by
  intro h1
  have hzero : ∀ p, PCDerivable (cnfSystem (↑(blockers n hn T) : Set (Clause (Fin n)))) 1 p → p = 0 := by
    intro p hp
    induction hp with
    | ax hmem hdeg =>
      rcases hmem with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
      · have := totalDegree_boolAx v; omega
      · have := totalDegree_mem_blockers hn h2 hC; omega
    | zero => rfl
    | add _ _ ih1 ih2 => rw [ih1, ih2, add_zero]
    | mulX j _ _ ih => rw [ih, mul_zero]
  have h10 : (1 : Poly n) = 0 := hzero 1 h1
  exact one_ne_zero h10

def hasPath {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (k m : ℕ) (a b : Bool) : Prop :=
  ∃ f : ℕ → Bool, f 0 = a ∧ f m = b ∧ ∀ j < m, T (pos n hn (k + j)) (f j) (f (j + 1)) = true

theorem hasPath_trans {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    {k m1 m2 : ℕ} {a b c : Bool}
    (h1 : hasPath hn T k m1 a b) (h2 : hasPath hn T (k + m1) m2 b c) :
    hasPath hn T k (m1 + m2) a c := by
  obtain ⟨f1, hf10, hf1m, hf1⟩ := h1
  obtain ⟨f2, hf20, hf2m, hf2⟩ := h2
  refine ⟨fun j => if j < m1 then f1 j else f2 (j - m1), ?_, ?_, ?_⟩
  · by_cases h0 : 0 < m1
    · simp [h0, hf10]
    · have hm1 : m1 = 0 := by omega
      subst hm1
      simp [hf20, ← hf10, hf1m]
  · simp [hf2m]
  · intro j hj
    by_cases hjm1 : j + 1 < m1
    · have hj1 : j < m1 := by omega
      simp only [hj1, hjm1, ite_true]
      exact hf1 j hj1
    · by_cases hj1 : j < m1
      · have hjeq : j + 1 = m1 := by omega
        dsimp only
        simp only [hj1, hjm1, ite_true, ite_false]
        rw [hjeq, Nat.sub_self, hf20, ← hf1m, ← hjeq]
        exact hf1 j hj1
      · have hj2 : ¬ j + 1 < m1 := by omega
        simp only [hj1, hj2, ite_false]
        have hsub : j + 1 - m1 = j - m1 + 1 := by omega
        rw [hsub]
        have hk : k + j = k + m1 + (j - m1) := by omega
        rw [hk]
        exact hf2 (j - m1) (by omega)

theorem not_hasPath_self_of_rejects {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    (hrej : rejects n hn T) (k : ℕ) (a : Bool) : ¬ hasPath hn T k n a a := by
  rintro ⟨f, hf0, hfn, hstep⟩
  apply hrej
  let off := n - k % n
  let idx : Fin n → ℕ := fun i => (i.val + off) % n
  refine ⟨fun i => f (idx i), fun i => ?_⟩
  have hlt : idx i < n := Nat.mod_lt _ hn
  have hki : pos n hn (k + idx i) = i := by
    apply Fin.ext
    change (k + (i.val + (n - k % n)) % n) % n = i.val
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hmod : k % n < n := Nat.mod_lt k hn
    have hdiv : k = n * (k / n) + k % n := (Nat.div_add_mod k n).symm
    have hmul : n * (k / n + 1) = n * (k / n) + n := by ring
    have hsum : k + (i.val + (n - k % n)) = i.val + n * (k / n + 1) := by omega
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  have hstep_i := hstep (idx i) hlt
  rw [hki] at hstep_i
  have hnext : idx (pos n hn (i.val + 1)) = (idx i + 1) % n := by
    change ((i.val + 1) % n + off) % n = ((i.val + off) % n + 1) % n
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    omega
  dsimp only
  by_cases hlast : idx i + 1 < n
  · rw [hnext, Nat.mod_eq_of_lt hlast]
    exact hstep_i
  · have heq : idx i + 1 = n := by omega
    rw [hnext, heq, Nat.mod_self, hf0, ← hfn, ← heq]
    exact hstep_i

def reachS {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) : ℕ → Finset Bool
  | 0 => Finset.univ
  | k + 1 => Finset.univ.filter (fun b => ∃ a ∈ reachS hn T k, T (pos n hn k) a b = true)

theorem reachS_subset_add_n {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) :
    ∀ k : ℕ, reachS hn T (k + n) ⊆ reachS hn T k
  | 0 => fun _ _ => Finset.mem_univ _
  | k + 1 => by
    intro b hb
    have h1 : k + 1 + n = k + n + 1 := by omega
    rw [h1] at hb
    obtain ⟨_, a, ha, hab⟩ := Finset.mem_filter.mp hb
    rw [pos_add_n] at hab
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, reachS_subset_add_n hn T k ha, hab⟩

theorem mem_reachS_add_iff {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (k : ℕ) : ∀ m b, b ∈ reachS hn T (k + m) ↔ ∃ a ∈ reachS hn T k, hasPath hn T k m a b
  | 0, b => by
    constructor
    · intro hb
      exact ⟨b, hb, fun _ => b, rfl, rfl, fun j hj => by omega⟩
    · rintro ⟨a, ha, f, hf0, hfm, _⟩
      have : a = b := by rw [← hf0, hfm]
      subst this; exact ha
  | m + 1, b => by
    constructor
    · intro hb
      have h1 : k + (m + 1) = k + m + 1 := by omega
      rw [h1] at hb
      obtain ⟨_, c, hc, hcb⟩ := Finset.mem_filter.mp hb
      obtain ⟨a, ha, hp⟩ := (mem_reachS_add_iff hn T k m c).mp hc
      refine ⟨a, ha, hasPath_trans hn hp ⟨fun j => if j = 0 then c else b, rfl, rfl, ?_⟩⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      simpa using hcb
    · rintro ⟨a, ha, f, hf0, hfm, hstep⟩
      have h1 : k + (m + 1) = k + m + 1 := by omega
      rw [h1]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, f m, ?_, ?_⟩
      · exact (mem_reachS_add_iff hn T k m (f m)).mpr
          ⟨a, ha, f, hf0, rfl, fun j hj => hstep j (by omega)⟩
      · rw [← hfm]
        exact hstep m (by omega)

theorem reachS_add_n_empty_of_card_one {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    (hrej : rejects n hn T) {k : ℕ} (hcard : (reachS hn T k).card = 1) :
    reachS hn T (k + n) = ∅ := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.eq_empty_iff_forall_notMem]
  intro b hb
  have hbk : b ∈ reachS hn T k := reachS_subset_add_n hn T k hb
  rw [hc, Finset.mem_singleton] at hbk
  subst hbk
  obtain ⟨a, ha, hp⟩ := (mem_reachS_add_iff hn T k n b).mp hb
  rw [hc, Finset.mem_singleton] at ha
  subst ha
  exact not_hasPath_self_of_rejects hn hrej k a hp

theorem reachS_card_le_two {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (k : ℕ) :
    (reachS hn T k).card ≤ 2 :=
  (Finset.card_le_univ _).trans (by decide)

theorem mem_singleton_not_false {S : Finset Bool} {x : Bool}
    (h1 : S = {x}) (h2 : (!x) ∈ S) : False := by
  rw [h1, Finset.mem_singleton] at h2
  cases x <;> simp at h2

theorem rejects_dichotomy {n : ℕ} (hn : 0 < n) {T : Fin n → Bool → Bool → Bool}
    (hrej : rejects n hn T) :
    (∃ p : ℕ → Bool, p 0 = false ∧ p n = true ∧
      ∀ j < n, T (pos n hn j) (p j) (!(p (j + 1))) = false ∧
        T (pos n hn j) (!(p j)) (p (j + 1)) = false) ∨
    (∃ i : Fin n, ∀ a b : Bool, T i a b = false) ∨
    (∃ (s l : ℕ) (c : ℕ → Bool), l + 1 ≤ n ∧
      (∀ a : Bool, T (pos n hn s) a (!(c 0)) = false) ∧
      (∀ j < l, T (pos n hn (s + 1 + j)) (c j) (!(c (j + 1))) = false) ∧
      (∀ b : Bool, T (pos n hn (s + 1 + l)) (c l) b = false)) := by
  classical
  by_cases hfull : (reachS hn T n).card = 2
  · left
    have hmem_all : ∀ b : Bool, b ∈ reachS hn T n := by
      have heq : reachS hn T n = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hfull]; decide)
      intro b; rw [heq]; exact Finset.mem_univ b
    obtain ⟨a1, _, hp1⟩ := (mem_reachS_add_iff hn T 0 n true).mp (by simpa using hmem_all true)
    obtain ⟨a0, _, hp0⟩ := (mem_reachS_add_iff hn T 0 n false).mp (by simpa using hmem_all false)
    have ha1 : a1 = false := by
      cases a1
      · rfl
      · exact absurd hp1 (not_hasPath_self_of_rejects hn hrej 0 true)
    have ha0 : a0 = true := by
      cases a0
      · exact absurd hp0 (not_hasPath_self_of_rejects hn hrej 0 false)
      · rfl
    subst ha1; subst ha0
    obtain ⟨p, hp00, hpn, hpstep⟩ := hp1
    obtain ⟨q, hq00, hqn, hqstep⟩ := hp0
    have hpq : ∀ j ≤ n, q j = !(p j) := by
      intro j hj
      by_cases heq : q j = p j
      · exfalso
        apply not_hasPath_self_of_rejects hn hrej 0 false
        have h1 : hasPath hn T 0 j false (p j) :=
          ⟨p, hp00, rfl, fun r hr => hpstep r (by omega)⟩
        have h2 : hasPath hn T (0 + j) (n - j) (p j) false := by
          refine ⟨fun r => q (j + r), ?_, ?_, ?_⟩
          · simp [heq]
          · dsimp only
            have : j + (n - j) = n := by omega
            rw [this, hqn]
          · intro r hr
            dsimp only
            have h1' : 0 + j + r = 0 + (j + r) := by omega
            have h2' : j + (r + 1) = j + r + 1 := by omega
            rw [h1', h2']
            exact hqstep (j + r) (by omega)
        have h3 := hasPath_trans hn h1 h2
        have hjn : j + (n - j) = n := by omega
        rwa [hjn] at h3
      · cases hpj : p j <;> cases hqj : q j <;> simp_all
    refine ⟨p, hp00, hpn, fun j hj => ⟨?_, ?_⟩⟩
    · cases hT : T (pos n hn j) (p j) (!(p (j + 1)))
      · rfl
      · exfalso
        apply not_hasPath_self_of_rejects hn hrej 0 false
        have h1 : hasPath hn T 0 (j + 1) false (q (j + 1)) := by
          refine ⟨fun r => if r ≤ j then p r else q (j + 1), by simp [hp00], by simp, ?_⟩
          intro r hr
          dsimp only
          by_cases hrj : r < j
          · have hr1 : r + 1 ≤ j := by omega
            have hr0 : r ≤ j := by omega
            simp only [hr0, hr1, ite_true]
            exact hpstep r (by omega)
          · have hreq : r = j := by omega
            subst hreq
            have hnot : ¬ r + 1 ≤ r := by omega
            simp only [le_refl, ite_true, hnot, ite_false]
            rw [hpq (r + 1) (by omega)]
            simpa using hT
        have h2 : hasPath hn T (0 + (j + 1)) (n - (j + 1)) (q (j + 1)) false := by
          refine ⟨fun r => q (j + 1 + r), by simp, ?_, ?_⟩
          · dsimp only
            have : j + 1 + (n - (j + 1)) = n := by omega
            rw [this, hqn]
          · intro r hr
            dsimp only
            have h1' : 0 + (j + 1) + r = 0 + (j + 1 + r) := by omega
            have h2' : j + 1 + (r + 1) = j + 1 + r + 1 := by omega
            rw [h1', h2']
            exact hqstep (j + 1 + r) (by omega)
        have h3 := hasPath_trans hn h1 h2
        have hjn : j + 1 + (n - (j + 1)) = n := by omega
        rwa [hjn] at h3
    · cases hT : T (pos n hn j) (!(p j)) (p (j + 1))
      · rfl
      · exfalso
        apply not_hasPath_self_of_rejects hn hrej 0 true
        have h1 : hasPath hn T 0 (j + 1) true (p (j + 1)) := by
          refine ⟨fun r => if r ≤ j then q r else p (j + 1), by simp [hq00], by simp, ?_⟩
          intro r hr
          dsimp only
          by_cases hrj : r < j
          · have hr1 : r + 1 ≤ j := by omega
            have hr0 : r ≤ j := by omega
            simp only [hr0, hr1, ite_true]
            exact hqstep r (by omega)
          · have hreq : r = j := by omega
            subst hreq
            have hnot : ¬ r + 1 ≤ r := by omega
            simp only [le_refl, ite_true, hnot, ite_false]
            rw [hpq r (by omega)]
            simpa using hT
        have h2 : hasPath hn T (0 + (j + 1)) (n - (j + 1)) (p (j + 1)) true := by
          refine ⟨fun r => p (j + 1 + r), by simp, ?_, ?_⟩
          · dsimp only
            have : j + 1 + (n - (j + 1)) = n := by omega
            rw [this, hpn]
          · intro r hr
            dsimp only
            have h1' : 0 + (j + 1) + r = 0 + (j + 1 + r) := by omega
            have h2' : j + 1 + (r + 1) = j + 1 + r + 1 := by omega
            rw [h1', h2']
            exact hpstep (j + 1 + r) (by omega)
        have h3 := hasPath_trans hn h1 h2
        have hjn : j + 1 + (n - (j + 1)) = n := by omega
        rwa [hjn] at h3
  · right
    have h2n_empty : reachS hn T (2 * n) = ∅ := by
      have hle : (reachS hn T n).card ≤ 2 := reachS_card_le_two hn T n
      have hlt : (reachS hn T n).card ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hlt with h0 | h1
      · have hemp : reachS hn T n = ∅ := Finset.card_eq_zero.mp h0
        have hsub : reachS hn T (n + n) ⊆ reachS hn T n := reachS_subset_add_n hn T n
        rw [hemp] at hsub
        have : 2 * n = n + n := by omega
        rw [this]
        exact Finset.subset_empty.mp hsub
      · have : 2 * n = n + n := by omega
        rw [this]
        exact reachS_add_n_empty_of_card_one hn hrej h1
    let empSet := (Finset.range (2 * n + 1)).filter (fun k => reachS hn T k = ∅)
    have hemp_ne : empSet.Nonempty :=
      ⟨2 * n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2n_empty⟩⟩
    let t := empSet.min' hemp_ne
    have ht_mem : t ∈ empSet := Finset.min'_mem empSet hemp_ne
    have ht_empty : reachS hn T t = ∅ := (Finset.mem_filter.mp ht_mem).2
    have ht_min : ∀ k < t, reachS hn T k ≠ ∅ := by
      intro k hkt hk0
      have hk_range : k < 2 * n + 1 := by
        have := (Finset.mem_range.mp (Finset.mem_filter.mp ht_mem).1)
        omega
      have hk_mem : k ∈ empSet := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_range, hk0⟩
      have hle := Finset.min'_le empSet k hk_mem
      omega
    have ht_pos : 0 < t := by
      by_contra h0
      have ht0 : t = 0 := by omega
      rw [ht0] at ht_empty
      have : (Finset.univ : Finset Bool) = ∅ := ht_empty
      exact absurd this (by decide)
    let twoSet := (Finset.range t).filter (fun k => (reachS hn T k).card = 2)
    have htwo_ne : twoSet.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht_pos, by change (Finset.univ : Finset Bool).card = 2; decide⟩⟩
    let s := twoSet.max' htwo_ne
    have hs_mem : s ∈ twoSet := Finset.max'_mem twoSet htwo_ne
    have hs_lt : s < t := Finset.mem_range.mp (Finset.mem_filter.mp hs_mem).1
    have hs_two : (reachS hn T s).card = 2 := (Finset.mem_filter.mp hs_mem).2
    have hs_univ : reachS hn T s = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hs_two]; decide)
    have hs_max : ∀ k, s < k → k < t → (reachS hn T k).card = 1 := by
      intro k hsk hkt
      have hne0 : (reachS hn T k).card ≠ 0 := fun h0 => ht_min k hkt (Finset.card_eq_zero.mp h0)
      have hle2 : (reachS hn T k).card ≤ 2 := reachS_card_le_two hn T k
      have hne2 : (reachS hn T k).card ≠ 2 := by
        intro h2k
        have hk_mem : k ∈ twoSet := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkt, h2k⟩
        have := Finset.le_max' twoSet k hk_mem
        omega
      omega
    by_cases hst : s + 1 = t
    · left
      refine ⟨pos n hn s, fun a b => ?_⟩
      cases hT : T (pos n hn s) a b
      · rfl
      · exfalso
        have hb : b ∈ reachS hn T (s + 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, by rw [hs_univ]; exact Finset.mem_univ a, hT⟩
        rw [hst, ht_empty] at hb
        exact Finset.notMem_empty b hb
    · right
      have hcard_s1 : (reachS hn T (s + 1)).card = 1 := hs_max (s + 1) (by omega) (by omega)
      have hs1n_empty : reachS hn T (s + 1 + n) = ∅ :=
        reachS_add_n_empty_of_card_one hn hrej hcard_s1
      have ht_le : t ≤ s + 1 + n := by
        by_contra hgt
        exact ht_min (s + 1 + n) (by omega) hs1n_empty
      let l := t - (s + 2)
      have hl_bound : l + 1 ≤ n := by omega
      have htl : s + 1 + l + 1 = t := by omega
      let c : ℕ → Bool := fun j => if true ∈ reachS hn T (s + 1 + j) then true else false
      have hc_eq : ∀ j ≤ l, reachS hn T (s + 1 + j) = {c j} := by
        intro j hj
        have hcardj : (reachS hn T (s + 1 + j)).card = 1 := hs_max (s + 1 + j) (by omega) (by omega)
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardj
        rw [hx]
        cases x
        · have : c j = false := by simp [c, hx]
          rw [this]
        · have : c j = true := by simp [c, hx]
          rw [this]
      refine ⟨s, l, c, hl_bound, ?_, ?_, ?_⟩
      · intro a
        cases hT : T (pos n hn s) a (!(c 0))
        · rfl
        · exfalso
          have hmem : (!(c 0)) ∈ reachS hn T (s + 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, by rw [hs_univ]; exact Finset.mem_univ a, hT⟩
          have hc0 := hc_eq 0 (Nat.zero_le l)
          simp only [add_zero] at hc0
          exact mem_singleton_not_false hc0 hmem
      · intro j hj
        cases hT : T (pos n hn (s + 1 + j)) (c j) (!(c (j + 1)))
        · rfl
        · exfalso
          have hcj : c j ∈ reachS hn T (s + 1 + j) := by
            rw [hc_eq j (by omega)]; exact Finset.mem_singleton_self _
          have hmem : (!(c (j + 1))) ∈ reachS hn T (s + 1 + j + 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, c j, hcj, hT⟩
          have hcj1 := hc_eq (j + 1) (by omega)
          have hidx : s + 1 + (j + 1) = s + 1 + j + 1 := by omega
          rw [hidx] at hcj1
          exact mem_singleton_not_false hcj1 hmem
      · intro b
        cases hT : T (pos n hn (s + 1 + l)) (c l) b
        · rfl
        · exfalso
          have hcl : c l ∈ reachS hn T (s + 1 + l) := by
            rw [hc_eq l (le_refl l)]; exact Finset.mem_singleton_self _
          have hmem : b ∈ reachS hn T (s + 1 + l + 1) := by
            unfold reachS
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c l, hcl, hT⟩
          rw [htl, ht_empty] at hmem
          exact Finset.notMem_empty b hmem

theorem pcDerivable_blocker {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n)
    {T : Fin n → Bool → Bool → Bool} {k : ℕ} {a b : Bool}
    (h : T (pos n hn k) a b = false) :
    PCDerivable (cnfSystem (↑(blockers n hn T) : Set (Clause (Fin n)))) 2
      (indP (pos n hn k) a * indP (pos n hn (k + 1)) b) := by
  have hmem := mem_blockers_pos_of_false hn h
  have hne : pos n hn k ≠ pos n hn (k + 1) := by
    rw [← pos_succ_pos hn k]
    exact pos_ne_succ hn h2 (pos n hn k)
  have hcp := clausePoly_pair hne a b
  have hdeg := totalDegree_clausePoly_pair hne a b
  rw [← hcp]
  exact PCDerivable.ax (Or.inr ⟨_, hmem, rfl⟩) (by omega)

theorem pcDerivable_mul_indP {n : ℕ} {G : Set (Poly n)} {v : Fin n} (b : Bool) {p : Poly n}
    (hp : PCDerivable G 2 p) (hdeg : p.totalDegree ≤ 1) :
    PCDerivable G 2 (p * indP v b) := by
  have hmul : (X v * p).totalDegree ≤ 2 := by
    have := totalDegree_mul (X v : Poly n) p
    have := totalDegree_X_le_one v
    omega
  cases b
  · have heq : p * indP v false = p + X v * p := by
      simp only [indP, Bool.false_eq_true, ite_false]; ring
    rw [heq]
    exact PCDerivable.add hp (PCDerivable.mulX v hp hmul)
  · have heq : p * indP v true = X v * p := by
      simp only [indP, ite_true]; ring
    rw [heq]
    exact PCDerivable.mulX v hp hmul

theorem pcRefutable_two {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n)
    (T : Fin n → Bool → Bool → Bool) (hrej : rejects n hn T) :
    PCRefutable (cnfSystem (↑(blockers n hn T) : Set (Clause (Fin n)))) 2 := by
  let G := cnfSystem (↑(blockers n hn T) : Set (Clause (Fin n)))
  rcases rejects_dichotomy hn hrej with
    ⟨p, hp0, hpn, hpblock⟩ | ⟨i, hempty⟩ | ⟨s, l, c, _, hstart, hchain, hend⟩
  · have hstep : ∀ j < n, PCDerivable G 2
        (indP (pos n hn j) (p j) + indP (pos n hn (j + 1)) (p (j + 1))) := by
      intro j hj
      have hb1 := pcDerivable_blocker hn h2 (hpblock j hj).1
      have hb2 := pcDerivable_blocker hn h2 (hpblock j hj).2
      have hadd := PCDerivable.add hb1 hb2
      have heq : indP (pos n hn j) (p j) * indP (pos n hn (j + 1)) (!(p (j + 1))) +
          indP (pos n hn j) (!(p j)) * indP (pos n hn (j + 1)) (p (j + 1)) =
          indP (pos n hn j) (p j) + indP (pos n hn (j + 1)) (p (j + 1)) := by
        rw [indP_not_eq, indP_not_eq]
        set A := indP (pos n hn j) (p j)
        set B := indP (pos n hn (j + 1)) (p (j + 1))
        calc A * (1 + B) + (1 + A) * B = (A + B) + (A * B + A * B) := by ring
          _ = A + B := by rw [add_self_eq_zero, add_zero]
      rwa [heq] at hadd
    have htele : ∀ m ≤ n, PCDerivable G 2 (indP (pos n hn 0) (p 0) + indP (pos n hn m) (p m)) := by
      intro m
      induction m with
      | zero =>
        intro _
        rw [add_self_eq_zero]
        exact PCDerivable.zero
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2' := hstep m (by omega)
        have hadd := PCDerivable.add h1 h2'
        have heq : (indP (pos n hn 0) (p 0) + indP (pos n hn m) (p m)) +
            (indP (pos n hn m) (p m) + indP (pos n hn (m + 1)) (p (m + 1))) =
            indP (pos n hn 0) (p 0) + indP (pos n hn (m + 1)) (p (m + 1)) := by
          set A := indP (pos n hn 0) (p 0)
          set B := indP (pos n hn m) (p m)
          set C := indP (pos n hn (m + 1)) (p (m + 1))
          calc (A + B) + (B + C) = (A + C) + (B + B) := by ring
            _ = A + C := by rw [add_self_eq_zero, add_zero]
        rwa [heq] at hadd
    have hfin := htele n (le_refl n)
    have hposn : pos n hn n = pos n hn 0 := by
      have := pos_add_n hn 0; simpa using this
    rw [hposn, hp0, hpn] at hfin
    have hsum1 : indP (pos n hn 0) false + indP (pos n hn 0) true = 1 := indP_false_add_true _
    rwa [hsum1] at hfin
  · have hpos_i : pos n hn i.val = i := by
      apply Fin.ext; exact Nat.mod_eq_of_lt i.isLt
    have hb : ∀ a b : Bool, PCDerivable G 2
        (indP (pos n hn i.val) a * indP (pos n hn (i.val + 1)) b) := by
      intro a b
      apply pcDerivable_blocker hn h2
      rw [hpos_i]
      exact hempty a b
    have h1 := PCDerivable.add (hb false false) (hb false true)
    have h2' := PCDerivable.add (hb true false) (hb true true)
    have h3 := PCDerivable.add h1 h2'
    have heq : (indP (pos n hn i.val) false * indP (pos n hn (i.val + 1)) false +
        indP (pos n hn i.val) false * indP (pos n hn (i.val + 1)) true) +
        (indP (pos n hn i.val) true * indP (pos n hn (i.val + 1)) false +
        indP (pos n hn i.val) true * indP (pos n hn (i.val + 1)) true) = 1 := by
      calc _ = (indP (pos n hn i.val) false + indP (pos n hn i.val) true) *
            (indP (pos n hn (i.val + 1)) false + indP (pos n hn (i.val + 1)) true) := by ring
        _ = 1 * 1 := by rw [indP_false_add_true _, indP_false_add_true _]
        _ = 1 := mul_one 1
    rwa [heq] at h3
  · have hunit0 : PCDerivable G 2 (indP (pos n hn (s + 1)) (!(c 0))) := by
      have h1 := pcDerivable_blocker hn h2 (hstart false)
      have h2' := pcDerivable_blocker hn h2 (hstart true)
      have hadd := PCDerivable.add h1 h2'
      have heq : indP (pos n hn s) false * indP (pos n hn (s + 1)) (!(c 0)) +
          indP (pos n hn s) true * indP (pos n hn (s + 1)) (!(c 0)) =
          indP (pos n hn (s + 1)) (!(c 0)) := by
        rw [← add_mul, indP_false_add_true _, one_mul]
      rwa [heq] at hadd
    have hprop : ∀ j ≤ l, PCDerivable G 2 (indP (pos n hn (s + 1 + j)) (!(c j))) := by
      intro j
      induction j with
      | zero => intro _; simpa using hunit0
      | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        have hmul := pcDerivable_mul_indP (!(c (j + 1))) (v := pos n hn (s + 1 + j + 1)) hprev
          (totalDegree_indP_le _ _)
        have hblk := pcDerivable_blocker hn h2 (hchain j (by omega))
        have hadd := PCDerivable.add hmul hblk
        have heq : indP (pos n hn (s + 1 + j)) (!(c j)) * indP (pos n hn (s + 1 + j + 1)) (!(c (j + 1))) +
            indP (pos n hn (s + 1 + j)) (c j) * indP (pos n hn (s + 1 + j + 1)) (!(c (j + 1))) =
            indP (pos n hn (s + 1 + (j + 1))) (!(c (j + 1))) := by
          have hidx : s + 1 + j + 1 = s + 1 + (j + 1) := by omega
          rw [hidx, ← add_mul, add_comm (indP _ (!(c j))), indP_add_not, one_mul]
        rwa [heq] at hadd
    have hlast1 := hprop l (le_refl l)
    have hlast2 : PCDerivable G 2 (indP (pos n hn (s + 1 + l)) (c l)) := by
      have h1 := pcDerivable_blocker hn h2 (hend false)
      have h2' := pcDerivable_blocker hn h2 (hend true)
      have hadd := PCDerivable.add h1 h2'
      have heq : indP (pos n hn (s + 1 + l)) (c l) * indP (pos n hn (s + 1 + l + 1)) false +
          indP (pos n hn (s + 1 + l)) (c l) * indP (pos n hn (s + 1 + l + 1)) true =
          indP (pos n hn (s + 1 + l)) (c l) := by
        rw [← mul_add, indP_false_add_true _, mul_one]
      rwa [heq] at hadd
    have hfin := PCDerivable.add hlast2 hlast1
    rw [indP_add_not] at hfin
    exact hfin

def StaticRep {n : ℕ} (clSet : Finset (Clause (Fin n))) (budget : ℕ) (target : Poly n) : Prop :=
  ∃ (q : Clause (Fin n) → Poly n) (b : Fin n → Poly n),
    (∀ C ∈ clSet, q C = 0 ∨ (q C).totalDegree + (clausePoly C).totalDegree ≤ budget) ∧
    (∀ v, b v = 0 ∨ (b v).totalDegree + 2 ≤ budget) ∧
    clSet.sum (fun C => q C * clausePoly C) + (∑ v, b v * (X v * X v + X v)) = target

theorem staticRep_mono {n : ℕ} {clSet : Finset (Clause (Fin n))} {d1 d2 : ℕ} {p : Poly n}
    (hd : d1 ≤ d2) (h : StaticRep clSet d1 p) : StaticRep clSet d2 p := by
  obtain ⟨q, b, hq, hb, heq⟩ := h
  refine ⟨q, b, ?_, ?_, heq⟩
  · intro C hC
    rcases hq C hC with h0 | hdeg
    · exact Or.inl h0
    · exact Or.inr (le_trans hdeg hd)
  · intro v
    rcases hb v with h0 | hdeg
    · exact Or.inl h0
    · exact Or.inr (le_trans hdeg hd)

theorem staticRep_zero {n : ℕ} (clSet : Finset (Clause (Fin n))) (budget : ℕ) :
    StaticRep clSet budget 0 :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => Or.inl rfl, fun _ => Or.inl rfl, by simp⟩

theorem staticRep_add {n : ℕ} {clSet : Finset (Clause (Fin n))} {budget : ℕ} {p1 p2 : Poly n}
    (h1 : StaticRep clSet budget p1) (h2 : StaticRep clSet budget p2) :
    StaticRep clSet budget (p1 + p2) := by
  obtain ⟨q1, b1, hq1, hb1, heq1⟩ := h1
  obtain ⟨q2, b2, hq2, hb2, heq2⟩ := h2
  refine ⟨fun C => q1 C + q2 C, fun v => b1 v + b2 v, ?_, ?_, ?_⟩
  · intro C hC
    dsimp only
    rcases hq1 C hC with h10 | h1d <;> rcases hq2 C hC with h20 | h2d
    · left; rw [h10, h20, add_zero]
    · right; rw [h10, zero_add]; exact h2d
    · right; rw [h20, add_zero]; exact h1d
    · right; have := totalDegree_add (q1 C) (q2 C); omega
  · intro v
    dsimp only
    rcases hb1 v with h10 | h1d <;> rcases hb2 v with h20 | h2d
    · left; rw [h10, h20, add_zero]
    · right; rw [h10, zero_add]; exact h2d
    · right; rw [h20, add_zero]; exact h1d
    · right; have := totalDegree_add (b1 v) (b2 v); omega
  · rw [← heq1, ← heq2]
    have hsum1 : clSet.sum (fun C => (q1 C + q2 C) * clausePoly C) =
        clSet.sum (fun C => q1 C * clausePoly C) + clSet.sum (fun C => q2 C * clausePoly C) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun C _ => add_mul _ _ _
    have hsum2 : (∑ v : Fin n, (b1 v + b2 v) * (X v * X v + X v)) =
        (∑ v : Fin n, b1 v * (X v * X v + X v)) + (∑ v : Fin n, b2 v * (X v * X v + X v)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => add_mul _ _ _
    rw [hsum1, hsum2]
    ring

theorem staticRep_mul {n : ℕ} {clSet : Finset (Clause (Fin n))} {d : ℕ} {p : Poly n}
    (r : Poly n) (hr : r.totalDegree ≤ 1) (hp : StaticRep clSet d p) :
    StaticRep clSet (d + 1) (r * p) := by
  obtain ⟨q, b, hq, hb, heq⟩ := hp
  refine ⟨fun C => r * q C, fun v => r * b v, ?_, ?_, ?_⟩
  · intro C hC
    dsimp only
    rcases hq C hC with h0 | hdeg
    · left; rw [h0, mul_zero]
    · right; have := totalDegree_mul r (q C); omega
  · intro v
    dsimp only
    rcases hb v with h0 | hdeg
    · left; rw [h0, mul_zero]
    · right; have := totalDegree_mul r (b v); omega
  · rw [← heq, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun C _ => by ring
    · exact Finset.sum_congr rfl fun v _ => by ring

theorem staticRep_single {n : ℕ} {clSet : Finset (Clause (Fin n))} {budget : ℕ}
    {C : Clause (Fin n)} (hC : C ∈ clSet) (r : Poly n)
    (hdeg : r.totalDegree + (clausePoly C).totalDegree ≤ budget) :
    StaticRep clSet budget (r * clausePoly C) := by
  classical
  refine ⟨fun C' => if C' = C then r else 0, fun _ => 0, ?_, fun _ => Or.inl rfl, ?_⟩
  · intro C' _
    by_cases h : C' = C
    · subst h; right; simpa using hdeg
    · left; simp [h]
  · simp only [zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single C]
    · simp
    · intro C' _ hne; simp [hne]
    · intro h; exact absurd hC h

theorem staticRep_blocker {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n)
    {T : Fin n → Bool → Bool → Bool} {k : ℕ} {a b : Bool}
    (h : T (pos n hn k) a b = false) :
    StaticRep (blockers n hn T) 2 (indP (pos n hn k) a * indP (pos n hn (k + 1)) b) := by
  have hmem := mem_blockers_pos_of_false hn h
  have hne : pos n hn k ≠ pos n hn (k + 1) := by
    rw [← pos_succ_pos hn k]
    exact pos_ne_succ hn h2 (pos n hn k)
  have hcp := clausePoly_pair hne a b
  have hdeg := totalDegree_clausePoly_pair hne a b
  have hrep := staticRep_single (budget := 2) hmem (1 : Poly n) (by simp [hdeg])
  rwa [one_mul, hcp] at hrep

theorem chain_interior {n : ℕ} {clSet : Finset (Clause (Fin n))} {y : ℕ → Poly n} {l : ℕ}
    (hydeg : ∀ j, (y j).totalDegree ≤ 1)
    (hstep : ∀ j < l, StaticRep clSet 2 (y j * (1 + y (j + 1)))) :
    ∀ k a b, a < b → b ≤ l → b - a ≤ 2 ^ k → StaticRep clSet (k + 2) (y a * (1 + y b))
  | 0, a, b, hab, hbl, hdiff => by
    have hba : b = a + 1 := by omega
    subst hba
    exact hstep a (by omega)
  | k + 1, a, b, hab, hbl, hdiff => by
    by_cases hle : b - a ≤ 2 ^ k
    · exact staticRep_mono (by omega) (chain_interior hydeg hstep k a b hab hbl hle)
    · let m := a + 2 ^ k
      have ham : a < m := by
        have : 0 < 2 ^ k := Nat.two_pow_pos k
        omega
      have hmb : m < b := by omega
      have hml : m ≤ l := by omega
      have h1 := chain_interior hydeg hstep k a m ham hml (by omega)
      have h2 := chain_interior hydeg hstep k m b hmb hbl (by omega)
      have hdeg1 : (1 + y b).totalDegree ≤ 1 :=
        (totalDegree_add (1 : Poly n) (y b)).trans (max_le (by simp) (hydeg b))
      have hm1 := staticRep_mul (1 + y b) hdeg1 h1
      have hm2 := staticRep_mul (y a) (hydeg a) h2
      have hsum := staticRep_add hm1 hm2
      have heq : (1 + y b) * (y a * (1 + y m)) + y a * (y m * (1 + y b)) = y a * (1 + y b) := by
        calc (1 + y b) * (y a * (1 + y m)) + y a * (y m * (1 + y b))
            = y a * (1 + y b) + (y a * y m * (1 + y b) + y a * y m * (1 + y b)) := by ring
          _ = y a * (1 + y b) := by rw [add_self_eq_zero, add_zero]
      have hk : k + 2 + 1 = k + 1 + 2 := by omega
      rw [heq, hk] at hsum
      exact hsum

theorem chain_left {n : ℕ} {clSet : Finset (Clause (Fin n))} {y : ℕ → Poly n} {l : ℕ}
    (hydeg : ∀ j, (y j).totalDegree ≤ 1)
    (h0 : StaticRep clSet 2 (1 + y 0))
    (hstep : ∀ j < l, StaticRep clSet 2 (y j * (1 + y (j + 1)))) :
    ∀ k b, b ≤ l → b + 2 ≤ 2 ^ (k + 1) → StaticRep clSet (k + 2) (1 + y b)
  | 0, b, _, hb => by
    have hb0 : b = 0 := by omega
    subst hb0; exact h0
  | k + 1, b, hbl, hb => by
    by_cases hle : b + 2 ≤ 2 ^ (k + 1)
    · exact staticRep_mono (by omega) (chain_left hydeg h0 hstep k b hbl hle)
    · let m := 2 ^ (k + 1) - 2
      have hpow : 2 ≤ 2 ^ (k + 1) := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      have hmb : m < b := by omega
      have hml : m ≤ l := by omega
      have h1 := chain_left hydeg h0 hstep k m hml (by omega)
      have hdegb : (1 + y b).totalDegree ≤ 1 :=
        (totalDegree_add (1 : Poly n) (y b)).trans (max_le (by simp) (hydeg b))
      have hm1 := staticRep_mul (1 + y b) hdegb h1
      have hdiff : b - m ≤ 2 ^ (k + 1) := by
        have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
        omega
      have h2 := chain_interior hydeg hstep (k + 1) m b hmb hbl hdiff
      have hk : k + 2 + 1 = k + 1 + 2 := by omega
      rw [hk] at hm1
      have hsum := staticRep_add hm1 h2
      have heq : (1 + y b) * (1 + y m) + y m * (1 + y b) = 1 + y b := by
        calc (1 + y b) * (1 + y m) + y m * (1 + y b)
            = (1 + y b) + (y m * (1 + y b) + y m * (1 + y b)) := by ring
          _ = 1 + y b := by rw [add_self_eq_zero, add_zero]
      rwa [heq] at hsum

theorem chain_right {n : ℕ} {clSet : Finset (Clause (Fin n))} {y : ℕ → Poly n} {l : ℕ}
    (hydeg : ∀ j, (y j).totalDegree ≤ 1)
    (hl : StaticRep clSet 2 (y l))
    (hstep : ∀ j < l, StaticRep clSet 2 (y j * (1 + y (j + 1)))) :
    ∀ k a, a ≤ l → (l - a) + 2 ≤ 2 ^ (k + 1) → StaticRep clSet (k + 2) (y a)
  | 0, a, hal, ha => by
    have hae : a = l := by omega
    subst hae; exact hl
  | k + 1, a, hal, ha => by
    by_cases hle : (l - a) + 2 ≤ 2 ^ (k + 1)
    · exact staticRep_mono (by omega) (chain_right hydeg hl hstep k a hal hle)
    · let m := l - (2 ^ (k + 1) - 2)
      have hpow : 2 ≤ 2 ^ (k + 1) := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      have ham : a < m := by omega
      have hml : m ≤ l := by omega
      have hdiff : m - a ≤ 2 ^ (k + 1) := by
        have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
        omega
      have h1 := chain_interior hydeg hstep (k + 1) a m ham hml hdiff
      have h2 := chain_right hydeg hl hstep k m hml (by omega)
      have hm2 := staticRep_mul (y a) (hydeg a) h2
      have hk : k + 2 + 1 = k + 1 + 2 := by omega
      rw [hk] at hm2
      have hsum := staticRep_add h1 hm2
      have heq : y a * (1 + y m) + y a * y m = y a := by
        calc y a * (1 + y m) + y a * y m
            = y a + (y a * y m + y a * y m) := by ring
          _ = y a := by rw [add_self_eq_zero, add_zero]
      rwa [heq] at hsum

theorem static_upper_n2 {n d : ℕ} (hn : 0 < n) (hn2 : n = 2) (hd2 : 2 ≤ d)
    (T : Fin n → Bool → Bool → Bool) (hrej : rejects n hn T) :
    StaticRep (blockers n hn T) d 1 := by
  subst hn2
  have hne01 : (⟨0, by decide⟩ : Fin 2) ≠ ⟨1, by decide⟩ := by decide
  have hword : ∀ a b : Bool, StaticRep (blockers 2 hn T) 2
      (indP ⟨0, by decide⟩ a * indP ⟨1, by decide⟩ b) := by
    intro a b
    by_cases h0 : T ⟨0, by decide⟩ a b = false
    · have := staticRep_blocker hn (le_refl 2) (k := 0) h0
      exact this
    · have h0t : T ⟨0, by decide⟩ a b = true := by cases h : T ⟨0, by decide⟩ a b <;> simp_all
      have h1 : T ⟨1, by decide⟩ b a = false := by
        cases h1c : T ⟨1, by decide⟩ b a
        · rfl
        · exfalso
          apply hrej
          refine ⟨fun i => if i.val = 0 then a else b, fun i => ?_⟩
          fin_cases i
          · simpa [pos] using h0t
          · simpa [pos] using h1c
      have hrep := staticRep_blocker hn (le_refl 2) (k := 1) h1
      have hcomm : indP (pos 2 hn 1) b * indP (pos 2 hn 2) a =
          indP ⟨0, by decide⟩ a * indP ⟨1, by decide⟩ b := by
        have hp1 : pos 2 hn 1 = ⟨1, by decide⟩ := rfl
        have hp2 : pos 2 hn 2 = ⟨0, by decide⟩ := rfl
        rw [hp1, hp2, mul_comm]
      rwa [hcomm] at hrep
  have hs1 := staticRep_add (hword false false) (hword false true)
  have hs2 := staticRep_add (hword true false) (hword true true)
  have hs := staticRep_add hs1 hs2
  have heq : (indP (⟨0, by decide⟩ : Fin 2) false * indP ⟨1, by decide⟩ false +
      indP ⟨0, by decide⟩ false * indP ⟨1, by decide⟩ true) +
      (indP ⟨0, by decide⟩ true * indP ⟨1, by decide⟩ false +
      indP ⟨0, by decide⟩ true * indP ⟨1, by decide⟩ true) = 1 := by
    calc _ = (indP (⟨0, by decide⟩ : Fin 2) false + indP ⟨0, by decide⟩ true) *
          (indP ⟨1, by decide⟩ false + indP ⟨1, by decide⟩ true) := by ring
      _ = 1 * 1 := by rw [indP_false_add_true _, indP_false_add_true _]
      _ = 1 := mul_one 1
  rw [heq] at hs
  exact staticRep_mono hd2 hs

theorem static_upper_pow {n d : ℕ} (hn : 0 < n) (h2 : 2 ≤ n) (hd : n + 2 < 2 ^ d)
    (T : Fin n → Bool → Bool → Bool) (hrej : rejects n hn T) :
    StaticRep (blockers n hn T) d 1 := by
  have hd2 : 2 ≤ d := by
    by_contra hlt
    have hd1 : d ≤ 1 := by omega
    have hpow : 2 ^ d ≤ 2 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd1 with rfl | rfl <;> decide
    omega
  rcases rejects_dichotomy hn hrej with
    ⟨p, hp0, hpn, hpblock⟩ | ⟨i, hempty⟩ | ⟨s, l, c, hl_bound, hstart, hchain, hend⟩
  · have hstep : ∀ j < n, StaticRep (blockers n hn T) 2
        (indP (pos n hn j) (p j) + indP (pos n hn (j + 1)) (p (j + 1))) := by
      intro j hj
      have hb1 := staticRep_blocker hn h2 (hpblock j hj).1
      have hb2 := staticRep_blocker hn h2 (hpblock j hj).2
      have hadd := staticRep_add hb1 hb2
      have heq : indP (pos n hn j) (p j) * indP (pos n hn (j + 1)) (!(p (j + 1))) +
          indP (pos n hn j) (!(p j)) * indP (pos n hn (j + 1)) (p (j + 1)) =
          indP (pos n hn j) (p j) + indP (pos n hn (j + 1)) (p (j + 1)) := by
        rw [indP_not_eq, indP_not_eq]
        set A := indP (pos n hn j) (p j)
        set B := indP (pos n hn (j + 1)) (p (j + 1))
        calc A * (1 + B) + (1 + A) * B = (A + B) + (A * B + A * B) := by ring
          _ = A + B := by rw [add_self_eq_zero, add_zero]
      rwa [heq] at hadd
    have htele : ∀ m ≤ n, StaticRep (blockers n hn T) 2
        (indP (pos n hn 0) (p 0) + indP (pos n hn m) (p m)) := by
      intro m
      induction m with
      | zero => intro _; rw [add_self_eq_zero]; exact staticRep_zero _ _
      | succ m ih =>
        intro hm
        have hadd := staticRep_add (ih (by omega)) (hstep m (by omega))
        have heq : (indP (pos n hn 0) (p 0) + indP (pos n hn m) (p m)) +
            (indP (pos n hn m) (p m) + indP (pos n hn (m + 1)) (p (m + 1))) =
            indP (pos n hn 0) (p 0) + indP (pos n hn (m + 1)) (p (m + 1)) := by
          set A := indP (pos n hn 0) (p 0)
          set B := indP (pos n hn m) (p m)
          set C := indP (pos n hn (m + 1)) (p (m + 1))
          calc (A + B) + (B + C) = (A + C) + (B + B) := by ring
            _ = A + C := by rw [add_self_eq_zero, add_zero]
        rwa [heq] at hadd
    have hfin := htele n (le_refl n)
    have hposn : pos n hn n = pos n hn 0 := by
      have := pos_add_n hn 0; simpa using this
    rw [hposn, hp0, hpn, indP_false_add_true _] at hfin
    exact staticRep_mono hd2 hfin
  · have hpos_i : pos n hn i.val = i := by
      apply Fin.ext; exact Nat.mod_eq_of_lt i.isLt
    have hb : ∀ a b : Bool, StaticRep (blockers n hn T) 2
        (indP (pos n hn i.val) a * indP (pos n hn (i.val + 1)) b) := by
      intro a b
      apply staticRep_blocker hn h2
      rw [hpos_i]
      exact hempty a b
    have hs := staticRep_add (staticRep_add (hb false false) (hb false true))
      (staticRep_add (hb true false) (hb true true))
    have heq : (indP (pos n hn i.val) false * indP (pos n hn (i.val + 1)) false +
        indP (pos n hn i.val) false * indP (pos n hn (i.val + 1)) true) +
        (indP (pos n hn i.val) true * indP (pos n hn (i.val + 1)) false +
        indP (pos n hn i.val) true * indP (pos n hn (i.val + 1)) true) = 1 := by
      calc _ = (indP (pos n hn i.val) false + indP (pos n hn i.val) true) *
            (indP (pos n hn (i.val + 1)) false + indP (pos n hn (i.val + 1)) true) := by ring
        _ = 1 * 1 := by rw [indP_false_add_true _, indP_false_add_true _]
        _ = 1 := mul_one 1
    rw [heq] at hs
    exact staticRep_mono hd2 hs
  · let y : ℕ → Poly n := fun j => indP (pos n hn (s + 1 + j)) (c j)
    have hydeg : ∀ j, (y j).totalDegree ≤ 1 := fun j => totalDegree_indP_le _ _
    have h0 : StaticRep (blockers n hn T) 2 (1 + y 0) := by
      have hadd := staticRep_add (staticRep_blocker hn h2 (hstart false))
        (staticRep_blocker hn h2 (hstart true))
      have heq : indP (pos n hn s) false * indP (pos n hn (s + 1)) (!(c 0)) +
          indP (pos n hn s) true * indP (pos n hn (s + 1)) (!(c 0)) = 1 + y 0 := by
        rw [← add_mul, indP_false_add_true _, one_mul]
        dsimp only [y]
        rw [add_zero, indP_not_eq]
      rwa [heq] at hadd
    have hl_end : StaticRep (blockers n hn T) 2 (y l) := by
      have hadd := staticRep_add (staticRep_blocker hn h2 (hend false))
        (staticRep_blocker hn h2 (hend true))
      have heq : indP (pos n hn (s + 1 + l)) (c l) * indP (pos n hn (s + 1 + l + 1)) false +
          indP (pos n hn (s + 1 + l)) (c l) * indP (pos n hn (s + 1 + l + 1)) true = y l := by
        rw [← mul_add, indP_false_add_true _, mul_one]
      rwa [heq] at hadd
    have hstep : ∀ j < l, StaticRep (blockers n hn T) 2 (y j * (1 + y (j + 1))) := by
      intro j hj
      have hblk := staticRep_blocker hn h2 (hchain j hj)
      have heq : indP (pos n hn (s + 1 + j)) (c j) * indP (pos n hn (s + 1 + j + 1)) (!(c (j + 1))) =
          y j * (1 + y (j + 1)) := by
        dsimp only [y]
        have hidx : s + 1 + j + 1 = s + 1 + (j + 1) := by omega
        rw [hidx, indP_not_eq]
      rwa [heq] at hblk
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    have hl4 : l + 4 ≤ 2 ^ (k + 2) := by omega
    have hpow2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    have hpow1 : 2 ≤ 2 ^ (k + 1) := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    let m := min l (2 ^ (k + 1) - 2)
    have hml : m ≤ l := min_le_left _ _
    have hm_left : m + 2 ≤ 2 ^ (k + 1) := by
      have := min_le_right l (2 ^ (k + 1) - 2); omega
    have hm_right : (l - m) + 2 ≤ 2 ^ (k + 1) := by
      by_cases hlm : l ≤ 2 ^ (k + 1) - 2
      · have hm_eq : m = l := min_eq_left hlm
        omega
      · have hm_eq : m = 2 ^ (k + 1) - 2 := min_eq_right (by omega)
        omega
    have hL := chain_left hydeg h0 hstep k m hml hm_left
    have hR := chain_right hydeg hl_end hstep k m hml hm_right
    have hsum := staticRep_add hL hR
    have heq : (1 + y m) + y m = 1 := by
      calc (1 + y m) + y m = 1 + (y m + y m) := by ring
        _ = 1 := by rw [add_self_eq_zero, add_zero]
    rwa [heq] at hsum

def natEnabled (z : ℕ) (A : Finset ℕ) : Prop :=
  z = 0 ∨ ∃ w, z = w + 1 ∧ w ∈ A

def natUp (d : ℕ) (A B : Finset ℕ) : Prop :=
  B.card ≤ d ∧ ∃ z, z ∉ A ∧ B = insert z A ∧ natEnabled z A

def natStep (d : ℕ) (A B : Finset ℕ) : Prop :=
  natUp d A B ∨ natUp d B A

theorem natStep_symm {d : ℕ} {A B : Finset ℕ} (h : natStep d A B) : natStep d B A :=
  h.symm

theorem natRtg_symm {d : ℕ} {A B : Finset ℕ}
    (h : Relation.ReflTransGen (natStep d) A B) : Relation.ReflTransGen (natStep d) B A := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (natStep_symm hstep) ih

theorem rtg_to_seq {α : Type*} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) :
    ∃ (L : ℕ) (f : ℕ → α), f 0 = a ∧ f L = b ∧ ∀ i < L, R (f i) (f (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i hi => by omega⟩
  | @tail c d _ hcd ih =>
    obtain ⟨L, f, hf0, hfL, hstep⟩ := ih
    refine ⟨L + 1, fun i => if i ≤ L then f i else d, by simp [hf0], by simp, ?_⟩
    intro i hi
    by_cases hiL : i < L
    · have hi1 : i + 1 ≤ L := by omega
      have hi0 : i ≤ L := by omega
      simp only [hi0, hi1, ite_true]
      exact hstep i hiL
    · have hieq : i = L := by omega
      subst hieq
      have hnot : ¬ i + 1 ≤ i := by omega
      dsimp only
      simp only [le_refl, ite_true, hnot, ite_false, hfL]
      exact hcd

theorem seq_to_rtg {α : Type*} {R : α → α → Prop} {L : ℕ} {f : ℕ → α}
    (hstep : ∀ i < L, R (f i) (f (i + 1)) ∨ f i = f (i + 1)) :
    Relation.ReflTransGen R (f 0) (f L) := by
  induction L with
  | zero => exact Relation.ReflTransGen.refl
  | succ L ih =>
    have h1 := ih (fun i hi => hstep i (by omega))
    rcases hstep L (by omega) with hr | heq
    · exact Relation.ReflTransGen.tail h1 hr
    · rw [← heq]; exact h1

def projBelow (m : ℕ) (U : Finset ℕ) : Finset ℕ :=
  U.filter (fun x => x < m)

def shiftAbove (m : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (U.filter (fun x => m ≤ x)).image (fun x => x - m)

theorem card_projBelow_add_shiftAbove (m : ℕ) (U : Finset ℕ) :
    (projBelow m U).card + (shiftAbove m U).card = U.card := by
  have hinj : Set.InjOn (fun x => x - m) (↑(U.filter (fun x => m ≤ x)) : Set ℕ) := by
    intro a ha b hb hab
    have ha' : m ≤ a := (Finset.mem_filter.mp ha).2
    have hb' : m ≤ b := (Finset.mem_filter.mp hb).2
    dsimp only at hab
    omega
  rw [shiftAbove, Finset.card_image_of_injOn hinj, projBelow]
  have hdisj : Disjoint (U.filter (fun x => x < m)) (U.filter (fun x => m ≤ x)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    omega
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    by_cases hxm : x < m
    · exact Or.inl ⟨hx, hxm⟩
    · exact Or.inr ⟨hx, by omega⟩

theorem natUp_projBelow {d m : ℕ} {A B : Finset ℕ} (h : natUp (d + 1) A B)
    (hcard : (projBelow m B).card ≤ d) :
    natUp d (projBelow m A) (projBelow m B) ∨ projBelow m A = projBelow m B := by
  obtain ⟨_, z, hzA, rfl, hen⟩ := h
  by_cases hzm : z < m
  · left
    refine ⟨hcard, z, ?_, ?_, ?_⟩
    · intro hz; exact hzA (Finset.mem_filter.mp hz).1
    · ext x
      simp only [projBelow, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxm⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hxm⟩
      · rintro (rfl | ⟨hx, hxm⟩)
        · exact ⟨Or.inl rfl, hzm⟩
        · exact ⟨Or.inr hx, hxm⟩
    · rcases hen with rfl | ⟨w, rfl, hwA⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨w, rfl, Finset.mem_filter.mpr ⟨hwA, by omega⟩⟩
  · right
    ext x
    simp only [projBelow, Finset.mem_filter, Finset.mem_insert]
    constructor
    · intro ⟨hx, hxm⟩; exact ⟨Or.inr hx, hxm⟩
    · rintro ⟨rfl | hx, hxm⟩
      · omega
      · exact ⟨hx, hxm⟩

theorem natStep_projBelow {d m : ℕ} {A B : Finset ℕ} (h : natStep (d + 1) A B)
    (hA : (projBelow m A).card ≤ d) (hB : (projBelow m B).card ≤ d) :
    natStep d (projBelow m A) (projBelow m B) ∨ projBelow m A = projBelow m B := by
  rcases h with hab | hba
  · rcases natUp_projBelow hab hB with hu | heq
    · exact Or.inl (Or.inl hu)
    · exact Or.inr heq
  · rcases natUp_projBelow hba hA with hu | heq
    · exact Or.inl (Or.inr hu)
    · exact Or.inr heq.symm

theorem natUp_shiftAbove {d m : ℕ} {A B : Finset ℕ} (h : natUp (d + 1) A B)
    (hcard : (shiftAbove m B).card ≤ d) :
    natUp d (shiftAbove m A) (shiftAbove m B) ∨ shiftAbove m A = shiftAbove m B := by
  obtain ⟨_, z, hzA, rfl, hen⟩ := h
  by_cases hzm : m ≤ z
  · left
    refine ⟨hcard, z - m, ?_, ?_, ?_⟩
    · intro hz
      obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hz
      obtain ⟨hxA, hxge⟩ := Finset.mem_filter.mp hx
      have hxz : x = z := by omega
      subst hxz
      exact hzA hxA
    · ext y
      simp only [shiftAbove, Finset.mem_image, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨x, ⟨rfl | hxA, hxge⟩, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨x, ⟨hxA, hxge⟩, rfl⟩
      · rintro (rfl | ⟨x, ⟨hxA, hxge⟩, rfl⟩)
        · exact ⟨z, ⟨Or.inl rfl, hzm⟩, rfl⟩
        · exact ⟨x, ⟨Or.inr hxA, hxge⟩, rfl⟩
    · by_cases hzeq : z = m
      · left; omega
      · right
        rcases hen with rfl | ⟨w, rfl, hwA⟩
        · omega
        · refine ⟨w - m, by omega, Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hwA, by omega⟩, rfl⟩⟩
  · right
    ext y
    simp only [shiftAbove, Finset.mem_image, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨x, ⟨hxA, hxge⟩, rfl⟩; exact ⟨x, ⟨Or.inr hxA, hxge⟩, rfl⟩
    · rintro ⟨x, ⟨rfl | hxA, hxge⟩, rfl⟩
      · omega
      · exact ⟨x, ⟨hxA, hxge⟩, rfl⟩

theorem natStep_shiftAbove {d m : ℕ} {A B : Finset ℕ} (h : natStep (d + 1) A B)
    (hA : (shiftAbove m A).card ≤ d) (hB : (shiftAbove m B).card ≤ d) :
    natStep d (shiftAbove m A) (shiftAbove m B) ∨ shiftAbove m A = shiftAbove m B := by
  rcases h with hab | hba
  · rcases natUp_shiftAbove hab hB with hu | heq
    · exact Or.inl (Or.inl hu)
    · exact Or.inr heq
  · rcases natUp_shiftAbove hba hA with hu | heq
    · exact Or.inl (Or.inr hu)
    · exact Or.inr heq.symm

theorem natStep_card_le {d : ℕ} {A B : Finset ℕ} (h : natStep d A B) :
    A.card ≤ d ∧ B.card ≤ d := by
  rcases h with ⟨hB, z, _, rfl, _⟩ | ⟨hA, z, _, rfl, _⟩
  · exact ⟨le_trans (Finset.card_le_card (Finset.subset_insert z A)) hB, hB⟩
  · exact ⟨hA, le_trans (Finset.card_le_card (Finset.subset_insert z B)) hA⟩

theorem natReach_card_le {d : ℕ} {U : Finset ℕ}
    (h : Relation.ReflTransGen (natStep d) ∅ U) : U.card ≤ d := by
  cases h with
  | refl => simp
  | tail _ hstep => exact (natStep_card_le hstep).2

theorem natReach_one_subset {U : Finset ℕ}
    (h : Relation.ReflTransGen (natStep 1) ∅ U) : ∀ v ∈ U, v = 0 := by
  induction h with
  | refl => intro v hv; exact absurd hv (Finset.notMem_empty v)
  | @tail A B _ hstep ih =>
    intro v hv
    rcases hstep with ⟨hB, z, hzA, rfl, hen⟩ | ⟨_, z, _, hAeq, _⟩
    · rcases Finset.mem_insert.mp hv with rfl | hvA
      · rcases hen with rfl | ⟨w, rfl, hwA⟩
        · rfl
        · have hA1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨w, hwA⟩
          rw [Finset.card_insert_of_notMem hzA] at hB
          omega
      · exact ih v hvA
    · rw [hAeq] at ih
      exact ih v (Finset.mem_insert_of_mem hv)

theorem natReach_bound_aux : ∀ d : ℕ, 1 ≤ d → ∀ U : Finset ℕ,
    Relation.ReflTransGen (natStep d) ∅ U → ∀ v ∈ U, v + 2 ≤ 2 ^ d
  | 0, hd, _, _, _, _ => by omega
  | 1, _, U, hU, v, hv => by
    have hv0 := natReach_one_subset hU v hv
    subst hv0; decide
  | d + 2, _, U, hU, v, hv => by
    let p := d + 1
    have hp1 : 1 ≤ p := by omega
    let m := 2 ^ p
    have hm1 : 1 ≤ m := Nat.one_le_two_pow
    by_cases hvm : v < m
    · have : 2 ^ (d + 2) = 2 * m := by dsimp only [m, p]; ring
      have : 2 ≤ m := by
        have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
        have : m = 2 * 2 ^ d := by dsimp only [m, p]; ring
        omega
      omega
    · obtain ⟨L, f, hf0, hfL, hstep⟩ := rtg_to_seq hU
      have hcard_f : ∀ i ≤ L, (f i).card ≤ p + 1 := by
        intro i hi
        by_cases hL0 : L = 0
        · subst hL0
          have hi0 : i = 0 := by omega
          subst hi0
          rw [hf0]; simp
        · by_cases hiL : i < L
          · exact (natStep_card_le (hstep i hiL)).1
          · have hiL' : i = L := by omega
            rw [hiL']
            have hL1 : L - 1 + 1 = L := by omega
            have h2' := (natStep_card_le (hstep (L - 1) (by omega))).2
            rwa [hL1] at h2'
      have hL_pos : 0 < L := by
        by_contra h0
        have hL0 : L = 0 := by omega
        rw [hL0, hf0] at hfL
        rw [← hfL] at hv
        exact Finset.notMem_empty v hv
      let lowSet := (Finset.range L).filter (fun i => ∀ x ∈ f i, x < m)
      have hlow_ne : lowSet.Nonempty :=
        ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hL_pos, by rw [hf0]; simp⟩⟩
      let t0 := lowSet.max' hlow_ne
      have ht0_mem : t0 ∈ lowSet := Finset.max'_mem lowSet hlow_ne
      have ht0_lt : t0 < L := Finset.mem_range.mp (Finset.mem_filter.mp ht0_mem).1
      have ht0_low : ∀ x ∈ f t0, x < m := (Finset.mem_filter.mp ht0_mem).2
      have habove : ∀ t, t0 < t → t ≤ L → (shiftAbove m (f t)).Nonempty := by
        intro t ht1 ht2
        by_cases htL : t = L
        · subst htL
          rw [hfL]
          exact ⟨v - m, Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, by omega⟩, rfl⟩⟩
        · have hnot : ¬ ∀ x ∈ f t, x < m := by
            intro hall
            have htmem : t ∈ lowSet := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hall⟩
            have := Finset.le_max' lowSet t htmem
            omega
          push Not at hnot
          obtain ⟨x, hx, hxm⟩ := hnot
          exact ⟨x - m, Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxm⟩, rfl⟩⟩
      have hbelow_le : ∀ t, t0 < t → t ≤ L → (projBelow m (f t)).card ≤ p := by
        intro t ht1 ht2
        have hpos : 1 ≤ (shiftAbove m (f t)).card := Finset.card_pos.mpr (habove t ht1 ht2)
        have hsum := card_projBelow_add_shiftAbove m (f t)
        have hle := hcard_f t ht2
        omega
      have hm_pred : m - 1 ∈ projBelow m (f (t0 + 1)) := by
        rcases hstep t0 ht0_lt with ⟨_, z, hz, hfeq, hen⟩ | ⟨_, z, _, hfeq, _⟩
        · have hzm : m ≤ z := by
            obtain ⟨y, hy⟩ := habove (t0 + 1) (by omega) (by omega)
            obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
            obtain ⟨hxf, hxm⟩ := Finset.mem_filter.mp hx
            rw [hfeq] at hxf
            rcases Finset.mem_insert.mp hxf with rfl | hxt0
            · exact hxm
            · exact absurd (ht0_low x hxt0) (by omega)
          rcases hen with rfl | ⟨w, rfl, hwt0⟩
          · omega
          · have hwm : w < m := ht0_low w hwt0
            have hw_eq : w = m - 1 := by omega
            subst hw_eq
            exact Finset.mem_filter.mpr ⟨by rw [hfeq]; exact Finset.mem_insert_of_mem hwt0, hwm⟩
        · exfalso
          obtain ⟨y, hy⟩ := habove (t0 + 1) (by omega) (by omega)
          obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
          obtain ⟨hxf, hxm⟩ := Finset.mem_filter.mp hx
          have hxt0 : x ∈ f t0 := by rw [hfeq]; exact Finset.mem_insert_of_mem hxf
          exact absurd (ht0_low x hxt0) (by omega)
      have hbelow_ne : ∀ t, t0 < t → t ≤ L → (projBelow m (f t)).Nonempty := by
        intro t ht1 ht2
        by_contra hemp
        have hemp' : projBelow m (f t) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
        let K := t - (t0 + 1)
        let g : ℕ → Finset ℕ := fun i => projBelow m (f (t - i))
        have hg_step : ∀ i < K, natStep p (g i) (g (i + 1)) ∨ g i = g (i + 1) := by
          intro i hi
          have hs := natStep_symm (hstep (t - (i + 1)) (by omega))
          have hidx : t - (i + 1) + 1 = t - i := by omega
          rw [hidx] at hs
          exact natStep_projBelow hs (hbelow_le (t - i) (by omega) (by omega))
            (hbelow_le (t - (i + 1)) (by omega) (by omega))
        have hreach : Relation.ReflTransGen (natStep p) (g 0) (g K) := seq_to_rtg hg_step
        have hg0 : g 0 = ∅ := by simp [g, hemp']
        have hgK : g K = projBelow m (f (t0 + 1)) := by
          dsimp only [g, K]
          congr 2; omega
        rw [hg0, hgK] at hreach
        have hbd := natReach_bound_aux p hp1 (projBelow m (f (t0 + 1))) hreach (m - 1) hm_pred
        omega
      have habove_le : ∀ t, t0 ≤ t → t ≤ L → (shiftAbove m (f t)).card ≤ p := by
        intro t ht1 ht2
        by_cases hteq : t = t0
        · subst hteq
          have hemp : shiftAbove m (f t0) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro y hy
            obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
            obtain ⟨hxf, hxm⟩ := Finset.mem_filter.mp hx
            exact absurd (ht0_low x hxf) (by omega)
          rw [hemp]; simp
        · have hpos : 1 ≤ (projBelow m (f t)).card :=
            Finset.card_pos.mpr (hbelow_ne t (by omega) ht2)
          have hsum := card_projBelow_add_shiftAbove m (f t)
          have hle := hcard_f t ht2
          omega
      let M := L - t0
      let h : ℕ → Finset ℕ := fun i => shiftAbove m (f (t0 + i))
      have hh_step : ∀ i < M, natStep p (h i) (h (i + 1)) ∨ h i = h (i + 1) := by
        intro i hi
        have hs := hstep (t0 + i) (by omega)
        have hidx : t0 + i + 1 = t0 + (i + 1) := by omega
        rw [hidx] at hs
        exact natStep_shiftAbove hs (habove_le (t0 + i) (by omega) (by omega))
          (habove_le (t0 + (i + 1)) (by omega) (by omega))
      have hreach : Relation.ReflTransGen (natStep p) (h 0) (h M) := seq_to_rtg hh_step
      have hh0 : h 0 = ∅ := by
        dsimp only [h]; rw [add_zero, Finset.eq_empty_iff_forall_notMem]
        intro y hy
        obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
        obtain ⟨hxf, hxm⟩ := Finset.mem_filter.mp hx
        exact absurd (ht0_low x hxf) (by omega)
      have hhM : h M = shiftAbove m U := by
        dsimp only [h, M]
        have : t0 + (L - t0) = L := by omega
        rw [this, hfL]
      rw [hh0, hhM] at hreach
      have hvm_mem : v - m ∈ shiftAbove m U :=
        Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, by omega⟩, rfl⟩
      have hbd := natReach_bound_aux p hp1 (shiftAbove m U) hreach (v - m) hvm_mem
      have : 2 ^ (d + 2) = 2 * m := by dsimp only [m, p]; ring
      omega

theorem natReach_strict_of_card_lt {d : ℕ} (hd : 1 ≤ d) {U : Finset ℕ}
    (hU : Relation.ReflTransGen (natStep d) ∅ U) (hcard : U.card < d)
    {v : ℕ} (hv : v ∈ U) : v + 3 ≤ 2 ^ d := by
  by_cases hv1 : v + 1 ∈ U
  · have := natReach_bound_aux d hd U hU (v + 1) hv1
    omega
  · have hup : natUp d U (insert (v + 1) U) := by
      refine ⟨?_, v + 1, hv1, rfl, Or.inr ⟨v, rfl, hv⟩⟩
      rw [Finset.card_insert_of_notMem hv1]
      omega
    have hU' := Relation.ReflTransGen.tail hU (Or.inl hup)
    have := natReach_bound_aux d hd (insert (v + 1) U) hU' (v + 1) (Finset.mem_insert_self _ _)
    omega

theorem natReach_singleton_one {p : ℕ} (hp : 2 ≤ p) :
    Relation.ReflTransGen (natStep p) ∅ ({1} : Finset ℕ) := by
  have h1 : natUp p ∅ ({0} : Finset ℕ) := ⟨by simp; omega, 0, by simp, by simp, Or.inl rfl⟩
  have h2 : natUp p ({0} : Finset ℕ) ({0, 1} : Finset ℕ) := by
    refine ⟨?_, 1, by simp, by ext x; simp [or_comm], Or.inr ⟨0, rfl, by simp⟩⟩
    have : ({0, 1} : Finset ℕ).card = 2 := by decide
    omega
  have h3 : natUp p ({1} : Finset ℕ) ({0, 1} : Finset ℕ) := by
    refine ⟨?_, 0, by simp, by ext x; simp, Or.inl rfl⟩
    have : ({0, 1} : Finset ℕ).card = 2 := by decide
    omega
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Or.inl h1)) (Or.inl h2))
    (Or.inr h3)

theorem natReach_strict_of_one_mem {d : ℕ} (hd : 3 ≤ d) {U : Finset ℕ}
    (hU : Relation.ReflTransGen (natStep d) ∅ U) (h1 : 1 ∈ U)
    {v : ℕ} (hv : v ∈ U) : v + 3 ≤ 2 ^ d := by
  obtain ⟨p, rfl⟩ : ∃ p, d = p + 1 := ⟨d - 1, by omega⟩
  have hp2 : 2 ≤ p := by omega
  have hp1 : 1 ≤ p := by omega
  let m := 2 ^ p
  have hm4 : 4 ≤ m := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    have : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    have : 2 ^ (q + 2) = 4 * 2 ^ q := by ring
    dsimp only [m]; omega
  have hbound := natReach_bound_aux (p + 1) (by omega) U hU v hv
  by_contra hnot
  have hpow : 2 ^ (p + 1) = 2 * m := by dsimp only [m]; ring
  have hveq : v = 2 * m - 2 := by omega
  obtain ⟨L, f, hf0, hfL, hstep⟩ := rtg_to_seq hU
  have hcard_f : ∀ i ≤ L, (f i).card ≤ p + 1 := by
    intro i hi
    by_cases hL0 : L = 0
    · subst hL0
      have hi0 : i = 0 := by omega
      subst hi0
      rw [hf0]; simp
    · by_cases hiL : i < L
      · exact (natStep_card_le (hstep i hiL)).1
      · have hiL' : i = L := by omega
        rw [hiL']
        have hL1 : L - 1 + 1 = L := by omega
        have h2' := (natStep_card_le (hstep (L - 1) (by omega))).2
        rwa [hL1] at h2'
  have hL_pos : 0 < L := by
    by_contra h0
    have hL0 : L = 0 := by omega
    rw [hL0, hf0] at hfL
    rw [← hfL] at hv
    exact Finset.notMem_empty v hv
  let lowSet := (Finset.range L).filter (fun i => ∀ x ∈ f i, x < m)
  have hlow_ne : lowSet.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hL_pos, by rw [hf0]; simp⟩⟩
  let t0 := lowSet.max' hlow_ne
  have ht0_mem : t0 ∈ lowSet := Finset.max'_mem lowSet hlow_ne
  have ht0_lt : t0 < L := Finset.mem_range.mp (Finset.mem_filter.mp ht0_mem).1
  have ht0_low : ∀ x ∈ f t0, x < m := (Finset.mem_filter.mp ht0_mem).2
  have habove : ∀ t, t0 < t → t ≤ L → (shiftAbove m (f t)).Nonempty := by
    intro t ht1 ht2
    by_cases htL : t = L
    · subst htL; rw [hfL]
      exact ⟨v - m, Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, by omega⟩, rfl⟩⟩
    · have hnot' : ¬ ∀ x ∈ f t, x < m := by
        intro hall
        have htmem : t ∈ lowSet := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hall⟩
        have := Finset.le_max' lowSet t htmem
        omega
      push Not at hnot'
      obtain ⟨x, hx, hxm⟩ := hnot'
      exact ⟨x - m, Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxm⟩, rfl⟩⟩
  have hbelow_le : ∀ t, t0 < t → t ≤ L → (projBelow m (f t)).card ≤ p := by
    intro t ht1 ht2
    have hpos : 1 ≤ (shiftAbove m (f t)).card := Finset.card_pos.mpr (habove t ht1 ht2)
    have hsum := card_projBelow_add_shiftAbove m (f t)
    have hle := hcard_f t ht2
    omega
  have hm_pred : m - 1 ∈ projBelow m (f (t0 + 1)) := by
    rcases hstep t0 ht0_lt with ⟨_, z, hz, hfeq, hen⟩ | ⟨_, z, _, hfeq, _⟩
    · have hzm : m ≤ z := by
        obtain ⟨y, hy⟩ := habove (t0 + 1) (by omega) (by omega)
        obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
        obtain ⟨hxf, hxm⟩ := Finset.mem_filter.mp hx
        rw [hfeq] at hxf
        rcases Finset.mem_insert.mp hxf with rfl | hxt0
        · exact hxm
        · exact absurd (ht0_low x hxt0) (by omega)
      rcases hen with rfl | ⟨w, rfl, hwt0⟩
      · omega
      · have hwm : w < m := ht0_low w hwt0
        have hw_eq : w = m - 1 := by omega
        subst hw_eq
        exact Finset.mem_filter.mpr ⟨by rw [hfeq]; exact Finset.mem_insert_of_mem hwt0, hwm⟩
    · exfalso
      obtain ⟨y, hy⟩ := habove (t0 + 1) (by omega) (by omega)
      obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
      obtain ⟨hxf, hxm⟩ := Finset.mem_filter.mp hx
      have hxt0 : x ∈ f t0 := by rw [hfeq]; exact Finset.mem_insert_of_mem hxf
      exact absurd (ht0_low x hxt0) (by omega)
  have hbelow_ne : ∀ t, t0 < t → t ≤ L → (projBelow m (f t)).Nonempty := by
    intro t ht1 ht2
    by_contra hemp
    have hemp' : projBelow m (f t) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
    let K := t - (t0 + 1)
    let g : ℕ → Finset ℕ := fun i => projBelow m (f (t - i))
    have hg_step : ∀ i < K, natStep p (g i) (g (i + 1)) ∨ g i = g (i + 1) := by
      intro i hi
      have hs := natStep_symm (hstep (t - (i + 1)) (by omega))
      have hidx : t - (i + 1) + 1 = t - i := by omega
      rw [hidx] at hs
      exact natStep_projBelow hs (hbelow_le (t - i) (by omega) (by omega))
        (hbelow_le (t - (i + 1)) (by omega) (by omega))
    have hreach : Relation.ReflTransGen (natStep p) (g 0) (g K) := seq_to_rtg hg_step
    have hg0 : g 0 = ∅ := by simp [g, hemp']
    have hgK : g K = projBelow m (f (t0 + 1)) := by dsimp only [g, K]; congr 2; omega
    rw [hg0, hgK] at hreach
    have hbd := natReach_bound_aux p hp1 (projBelow m (f (t0 + 1))) hreach (m - 1) hm_pred
    omega
  have habove_le : ∀ t, t0 ≤ t → t ≤ L → (shiftAbove m (f t)).card ≤ p := by
    intro t ht1 ht2
    by_cases hteq : t = t0
    · subst hteq
      have hemp : shiftAbove m (f t0) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
        obtain ⟨hxf, hxm⟩ := Finset.mem_filter.mp hx
        exact absurd (ht0_low x hxf) (by omega)
      rw [hemp]; simp
    · have hpos : 1 ≤ (projBelow m (f t)).card :=
        Finset.card_pos.mpr (hbelow_ne t (by omega) ht2)
      have hsum := card_projBelow_add_shiftAbove m (f t)
      have hle := hcard_f t ht2
      omega
  let M := L - t0
  let h : ℕ → Finset ℕ := fun i => shiftAbove m (f (t0 + i))
  have hh_step : ∀ i < M, natStep p (h i) (h (i + 1)) ∨ h i = h (i + 1) := by
    intro i hi
    have hs := hstep (t0 + i) (by omega)
    have hidx : t0 + i + 1 = t0 + (i + 1) := by omega
    rw [hidx] at hs
    exact natStep_shiftAbove hs (habove_le (t0 + i) (by omega) (by omega))
      (habove_le (t0 + (i + 1)) (by omega) (by omega))
  have hreachA : Relation.ReflTransGen (natStep p) ∅ (shiftAbove m U) := by
    have hr := seq_to_rtg hh_step
    have hh0 : h 0 = ∅ := by
      dsimp only [h]; rw [add_zero, Finset.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
      obtain ⟨hxf, hxm⟩ := Finset.mem_filter.mp hx
      exact absurd (ht0_low x hxf) (by omega)
    have hhM : h M = shiftAbove m U := by
      dsimp only [h, M]
      have hsumL : t0 + (L - t0) = L := by omega
      rw [hsumL, hfL]
    rwa [hh0, hhM] at hr
  have hvm_mem : v - m ∈ shiftAbove m U :=
    Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, by omega⟩, rfl⟩
  have hcardA_eq : (shiftAbove m U).card = p := by
    have hle : (shiftAbove m U).card ≤ p := natReach_card_le hreachA
    by_contra hne
    have hlt : (shiftAbove m U).card < p := by omega
    have hst := natReach_strict_of_card_lt hp1 hreachA hlt hvm_mem
    omega
  have hcardB_le : (projBelow m U).card ≤ 1 := by
    have hsum := card_projBelow_add_shiftAbove m U
    have hUle := natReach_card_le hU
    omega
  have h1B : 1 ∈ projBelow m U := Finset.mem_filter.mpr ⟨h1, by omega⟩
  have hBeq : projBelow m U = {1} := by
    have hsub : ({1} : Finset ℕ) ⊆ projBelow m U := Finset.singleton_subset_iff.mpr h1B
    exact (Finset.eq_of_subset_of_card_le hsub (by simpa using hcardB_le)).symm
  let K := L - (t0 + 1)
  let g : ℕ → Finset ℕ := fun i => projBelow m (f (L - i))
  have hg_step : ∀ i < K, natStep p (g i) (g (i + 1)) ∨ g i = g (i + 1) := by
    intro i hi
    have hs := natStep_symm (hstep (L - (i + 1)) (by omega))
    have hidx : L - (i + 1) + 1 = L - i := by omega
    rw [hidx] at hs
    exact natStep_projBelow hs (hbelow_le (L - i) (by omega) (by omega))
      (hbelow_le (L - (i + 1)) (by omega) (by omega))
  have hreachB : Relation.ReflTransGen (natStep p) ({1} : Finset ℕ) (projBelow m (f (t0 + 1))) := by
    have hr := seq_to_rtg hg_step
    have hg0 : g 0 = {1} := by simp [g, hfL, hBeq]
    have hgK : g K = projBelow m (f (t0 + 1)) := by dsimp only [g, K]; congr 2; omega
    rwa [hg0, hgK] at hr
  have hreach_full := (natReach_singleton_one hp2).trans hreachB
  have hbd := natReach_bound_aux p hp1 (projBelow m (f (t0 + 1))) hreach_full (m - 1) hm_pred
  omega

def optToNat {n : ℕ} : Option (Fin n) → ℕ
  | none => 0
  | some i => i.val + 1

theorem optToNat_injective {n : ℕ} : Function.Injective (@optToNat n) := by
  intro a b h
  cases a <;> cases b <;> simp [optToNat] at h
  · rfl
  · exact congrArg some (Fin.ext h)

def anchoredTable (n : ℕ) (_hn : 0 < n) (i : Fin n) (a b : Bool) : Bool :=
  if i.val + 1 = n then
    (!a) && b
  else
    !(a && !b)

theorem rejects_anchoredTable {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n) :
    rejects n hn (anchoredTable n hn) := by
  rintro ⟨x, hx⟩
  let t : Fin n := ⟨n - 1, by omega⟩
  have hxt := hx t
  have hpos_t : pos n hn (t.val + 1) = ⟨0, hn⟩ := by
    apply Fin.ext
    change (n - 1 + 1) % n = 0
    have : n - 1 + 1 = n := by omega
    rw [this, Nat.mod_self]
  have ht_cond : t.val + 1 = n := by dsimp only [t]; omega
  rw [hpos_t] at hxt
  simp only [anchoredTable, ht_cond, ite_true, Bool.and_eq_true, Bool.not_eq_true'] at hxt
  have htrue : ∀ k (hk : k < n), x ⟨k, hk⟩ = true := by
    intro k
    induction k with
    | zero => intro _; exact hxt.2
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hstep := hx ⟨k, by omega⟩
      have hne : k + 1 ≠ n := by omega
      have hposk : pos n hn (k + 1) = ⟨k + 1, hk⟩ := by
        apply Fin.ext; exact Nat.mod_eq_of_lt hk
      simp only [anchoredTable, hne, ite_false, hposk, hprev, Bool.true_and,
        Bool.not_not] at hstep
      exact hstep
  have hxt_true := htrue (n - 1) (by omega)
  exact Bool.false_ne_true (hxt.1.symm.trans hxt_true)

def pin1 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, true), (s, true)}
def pin2 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, false), (s, true)}
def pin3 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, false), (s, false)}

def chainClause {n : ℕ} (i j : Fin n) : Clause (Fin n) := {(i, false), (j, true)}

theorem clausePoly_pin1 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    clausePoly (pin1 s t) = (1 + X s) + X t + X t * X s := by
  have h := clausePoly_pair hst.symm false false
  change clausePoly (pin1 s t) = _
  rw [show pin1 s t = {(t, !false), (s, !false)} from rfl, h]
  simp only [indP, Bool.false_eq_true, ite_false]
  ring

theorem clausePoly_pin2 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    clausePoly (pin2 s t) = X t + X t * X s := by
  have h := clausePoly_pair hst.symm true false
  change clausePoly (pin2 s t) = _
  rw [show pin2 s t = {(t, !true), (s, !false)} from rfl, h]
  simp only [indP, Bool.false_eq_true, ite_false, ite_true]
  ring

theorem clausePoly_pin3 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    clausePoly (pin3 s t) = X t * X s := by
  have h := clausePoly_pair hst.symm true true
  change clausePoly (pin3 s t) = _
  rw [show pin3 s t = {(t, !true), (s, !true)} from rfl, h]
  simp only [indP, ite_true]

theorem clausePoly_chainClause {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    clausePoly (chainClause i j) = mon {i} + mon {i, j} := by
  have h := clausePoly_pair hij true false
  change clausePoly (chainClause i j) = _
  rw [show chainClause i j = {(i, !true), (j, !false)} from rfl, h]
  simp only [indP, Bool.false_eq_true, ite_false, ite_true, mon, Finset.prod_singleton,
    Finset.prod_pair hij]
  ring

theorem static_anchored_to_pebble {n d : ℕ} (hn : 0 < n) (h2 : 2 ≤ n)
    (hstat : StaticRep (blockers n hn (anchoredTable n hn)) d 1) :
    ∃ U : Finset ℕ, n ∈ U ∧ (U.card < d ∨ 1 ∈ U) ∧ Relation.ReflTransGen (natStep d) ∅ U := by
  classical
  by_contra hno
  let F := blockers n hn (anchoredTable n hn)
  let Comp : Finset (Fin n) → Prop := fun S =>
    Relation.ReflTransGen (natStep d) ∅ ((S.image some).image optToNat)
  let chi : Poly n → ZMod 2 := fun p =>
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Comp S), (nf p).coeff (indF S)
  have hchi_add : ∀ p1 p2 : Poly n, chi (p1 + p2) = chi p1 + chi p2 := by
    intro p1 p2; simp only [chi, nf_add, coeff_add', Finset.sum_add_distrib]
  have hchi_zero : chi 0 = 0 := by simp [chi, nf_zero]
  have hchi_sum : ∀ {ι : Type} (I : Finset ι) (f : ι → Poly n),
      chi (∑ a ∈ I, f a) = ∑ a ∈ I, chi (f a) := by
    intro ι I f
    induction I using Finset.induction_on with
    | empty => simp [hchi_zero]
    | @insert a I ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hchi_add, ih]
  have hchi_mon : ∀ S : Finset (Fin n), chi (mon S) = if Comp S then 1 else 0 := by
    intro S
    have hnf_mon : nf (mon S) = mon S := by
      rw [mon_eq_monomial, nf_monomial, indF_support]
    simp only [chi, hnf_mon, coeff_mon]
    by_cases hS : Comp S
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hS)]
      have hmem : S ∈ Finset.univ.filter (fun T : Finset (Fin n) => Comp T) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩
      rw [Finset.sum_eq_single S]
      · simp
      · intro T _ hTS; simp [hTS.symm]
      · intro h; exact absurd hmem h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hS)]
      apply Finset.sum_eq_zero
      intro T hT
      have hTS : S ≠ T := by intro e; subst e; exact hS (Finset.mem_filter.mp hT).2
      simp [hTS]
  have hchi_nf : ∀ p : Poly n, chi p = chi (nf p) := by
    intro p
    have hnf2 : nf (nf p) = nf p := by
      conv_lhs => rw [nf_eq_sum_indF p]
      rw [nf_sum]
      conv_rhs => rw [nf_eq_sum_indF p]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [nf_monomial, indF_support]
    simp only [chi, hnf2]
  have hchi_one : chi 1 = 1 := by
    have h1 : (1 : Poly n) = mon ∅ := by simp [mon]
    rw [h1, hchi_mon]
    have hC0 : Comp ∅ := by simp [Comp, Relation.ReflTransGen.refl]
    simp [hC0]
  have hchi_bool : ∀ (p : Poly n) (v : Fin n), chi (p * (X v * X v + X v)) = 0 := by
    intro p v; rw [hchi_nf, nf_mul_boolAx, hchi_zero]
  let img : Finset (Fin n) → Finset ℕ := fun S => (S.image some).image optToNat
  have himg_card : ∀ S : Finset (Fin n), (img S).card = S.card := by
    intro S
    dsimp only [img]
    rw [Finset.card_image_of_injective _ optToNat_injective,
      Finset.card_image_of_injective _ (Option.some_injective (Fin n))]
  have himg_mem : ∀ (S : Finset (Fin n)) (x : ℕ), x ∈ img S ↔ ∃ i ∈ S, i.val + 1 = x := by
    intro S x
    simp only [img, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨some i, ⟨i, hi, rfl⟩, rfl⟩
  have himg_insert : ∀ (S : Finset (Fin n)) (i : Fin n),
      img (insert i S) = insert (i.val + 1) (img S) := by
    intro S i
    simp only [img, Finset.image_insert, optToNat]
  let s : Fin n := ⟨0, hn⟩
  let t : Fin n := ⟨n - 1, by omega⟩
  have hst : s ≠ t := by intro h; have := congrArg Fin.val h; dsimp only [s, t] at this; omega
  have hbridge_s : ∀ (M : Finset (Fin n)), s ∉ M → M.card + 2 ≤ d →
      Relation.ReflTransGen (natStep d) (img M) (img (insert s M)) := by
    intro M hns hcard
    have h0M : 0 ∉ img M := by
      rw [himg_mem]; rintro ⟨i, _, hi⟩; omega
    have h1M : 1 ∉ img M := by
      rw [himg_mem]; rintro ⟨i, hi, hi1⟩
      have his : i = s := Fin.ext (by dsimp only [s]; omega)
      subst his; exact hns hi
    have h1ins : 1 ∉ insert 0 (img M) := by simp [h1M]
    have h0ins : 0 ∉ insert 1 (img M) := by simp [h0M]
    have hstep1 : natUp d (img M) (insert 0 (img M)) :=
      ⟨by rw [Finset.card_insert_of_notMem h0M, himg_card]; omega, 0, h0M, rfl, Or.inl rfl⟩
    have hstep2 : natUp d (insert 0 (img M)) (insert 1 (insert 0 (img M))) :=
      ⟨by rw [Finset.card_insert_of_notMem h1ins, Finset.card_insert_of_notMem h0M, himg_card]; omega,
        1, h1ins, rfl, Or.inr ⟨0, rfl, Finset.mem_insert_self 0 _⟩⟩
    have hstep3 : natUp d (insert 1 (img M)) (insert 1 (insert 0 (img M))) :=
      ⟨by rw [Finset.card_insert_of_notMem h1ins, Finset.card_insert_of_notMem h0M, himg_card]; omega,
        0, h0ins, by ext x; simp [or_left_comm], Or.inl rfl⟩
    have hfin : Relation.ReflTransGen (natStep d) (img M) (insert 1 (img M)) :=
      Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Or.inl hstep1)) (Or.inl hstep2))
        (Or.inr hstep3)
    have hiseq : img (insert s M) = insert 1 (img M) := by
      exact himg_insert M s
    rwa [← hiseq] at hfin
  have hchi_pin_gen : ∀ (e : Fin n →₀ ℕ), e.support.card + 2 ≤ d →
      chi (monomial e (1 : ZMod 2) * (1 + X s)) = 0 ∧
      chi (monomial e (1 : ZMod 2) * X t) = 0 ∧
      chi (monomial e (1 : ZMod 2) * (X t * X s)) = 0 := by
    intro e hec
    refine ⟨?_, ?_, ?_⟩
    · have h1s : (1 + X s : Poly n) = mon ∅ + mon {s} := by simp [mon]
      rw [hchi_nf, h1s, mul_add, nf_add, nf_monomial_mul_mon, nf_monomial_mul_mon,
        hchi_add, hchi_mon, hchi_mon]
      simp only [Finset.union_empty, Finset.union_singleton]
      by_cases hsM : s ∈ e.support
      · rw [Finset.insert_eq_of_mem hsM]; exact zmod2_add_self _
      · have hbr := hbridge_s e.support hsM hec
        have hiff : Comp e.support ↔ Comp (insert s e.support) :=
          ⟨fun h => h.trans hbr, fun h => h.trans (natRtg_symm hbr)⟩
        by_cases hM : Comp e.support
        · have hM' := hiff.mp hM
          simp only [hM, hM', ite_true]
          exact zmod2_add_self 1
        · have hM' : ¬ Comp (insert s e.support) := fun h => hM (hiff.mpr h)
          simp [hM, hM']
    · have hXt : (X t : Poly n) = mon {t} := by simp [mon]
      rw [hchi_nf, hXt, nf_monomial_mul_mon, Finset.union_singleton, hchi_mon]
      have hnc : ¬ Comp (insert t e.support) := by
        intro hc
        apply hno
        refine ⟨img (insert t e.support), ?_, Or.inl ?_, hc⟩
        · rw [himg_mem]; exact ⟨t, Finset.mem_insert_self t _, by dsimp only [t]; omega⟩
        · rw [himg_card]
          have := Finset.card_insert_le t e.support; omega
      simp [hnc]
    · have hXts : (X t * X s : Poly n) = mon {t, s} := by simp [mon, Finset.prod_pair hst.symm]
      rw [hchi_nf, hXts, nf_monomial_mul_mon, hchi_mon]
      have hnc : ¬ Comp (e.support ∪ {t, s}) := by
        intro hc
        apply hno
        refine ⟨img (e.support ∪ {t, s}), ?_, Or.inr ?_, hc⟩
        · rw [himg_mem]
          exact ⟨t, Finset.mem_union_right _ (Finset.mem_insert_self t {s}), by dsimp only [t]; omega⟩
        · rw [himg_mem]
          exact ⟨s, Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self s)), rfl⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnc)]
  obtain ⟨q, b, hq, hb, heq⟩ := hstat
  have hchi_lhs : chi (F.sum (fun C => q C * clausePoly C) + ∑ v, b v * (X v * X v + X v)) = 0 := by
    rw [hchi_add, hchi_sum, hchi_sum]
    have hb0 : ∑ v : Fin n, chi (b v * (X v * X v + X v)) = 0 :=
      Finset.sum_eq_zero fun v _ => hchi_bool (b v) v
    have hF0 : ∑ C ∈ F, chi (q C * clausePoly C) = 0 := by
      apply Finset.sum_eq_zero
      intro C hCF
      rcases hq C hCF with hq0 | hqdeg
      · rw [hq0, zero_mul, hchi_zero]
      · have hCdeg : (clausePoly C).totalDegree = 2 := totalDegree_mem_blockers hn h2 hCF
        rw [hCdeg] at hqdeg
        unfold F blockers at hCF
        obtain ⟨⟨i, a, bval⟩, hfilt, rfl⟩ := Finset.mem_image.mp hCF
        have hfalse : anchoredTable n hn i a bval = false := (Finset.mem_filter.mp hfilt).2
        rw [(q _).as_sum, Finset.sum_mul, hchi_sum]
        apply Finset.sum_eq_zero
        intro e he
        have hc : (q _).coeff e = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp he)
        rw [hc]
        have hed : e.sum (fun _ k => k) ≤ (q _).totalDegree :=
          Finset.le_sup (f := fun m : Fin n →₀ ℕ => m.sum (fun _ k => k)) he
        have hMcard : e.support.card + 2 ≤ d := by
          have := card_support_le_sum e; omega
        dsimp only
        by_cases hit : i.val + 1 = n
        · have hieq : i = t := Fin.ext (by dsimp only [t]; omega)
          have hpos_i : pos n hn (i.val + 1) = s := by
            apply Fin.ext; change (i.val + 1) % n = 0; rw [hit, Nat.mod_self]
          rw [hpos_i, hieq]
          obtain ⟨hp1, hp2, hp3⟩ := hchi_pin_gen e hMcard
          cases a <;> cases bval
          · change chi (monomial e (1 : ZMod 2) * clausePoly (pin1 s t)) = 0
            rw [clausePoly_pin1 hst, mul_add, mul_add, hchi_add, hchi_add, hp1, hp2, hp3]
            simp
          · simp [anchoredTable, hit] at hfalse
          · change chi (monomial e (1 : ZMod 2) * clausePoly (pin2 s t)) = 0
            rw [clausePoly_pin2 hst, mul_add, hchi_add, hp2, hp3]
            simp
          · change chi (monomial e (1 : ZMod 2) * clausePoly (pin3 s t)) = 0
            rw [clausePoly_pin3 hst, hp3]
        · have hab : a = true ∧ bval = false := by
            simp only [anchoredTable, hit, ite_false] at hfalse
            cases a <;> cases bval <;> simp at hfalse ⊢
          rcases hab with ⟨rfl, rfl⟩
          let j : Fin n := pos n hn (i.val + 1)
          have hjval : j.val = i.val + 1 := Nat.mod_eq_of_lt (by omega)
          have hij : i ≠ j := pos_ne_succ hn h2 i
          change chi (monomial e (1 : ZMod 2) * clausePoly (chainClause i j)) = 0
          rw [hchi_nf, clausePoly_chainClause hij, mul_add, nf_add,
            nf_monomial_mul_mon, nf_monomial_mul_mon, hchi_add, hchi_mon, hchi_mon]
          set A := e.support ∪ {i}
          set B := e.support ∪ {i, j}
          have hBeq : B = insert j A := by
            ext x; simp only [A, B, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
          by_cases hjA : j ∈ A
          · rw [hBeq, Finset.insert_eq_of_mem hjA]; exact zmod2_add_self _
          · have hBcard : (img B).card ≤ d := by
              rw [himg_card, hBeq, Finset.card_insert_of_notMem hjA]
              have hA_le : A.card ≤ e.support.card + 1 :=
                (Finset.card_union_le e.support {i}).trans (by simp)
              omega
            have hj_nmem : j.val + 1 ∉ img A := by
              rw [himg_mem]; rintro ⟨u, hu, huval⟩
              have huj : u = j := Fin.ext (by omega)
              subst huj; exact hjA hu
            have hi_mem : i.val + 1 ∈ img A := by
              rw [himg_mem]
              exact ⟨i, Finset.mem_union_right _ (Finset.mem_singleton_self i), rfl⟩
            have hup : natUp d (img A) (img B) := by
              refine ⟨hBcard, j.val + 1, hj_nmem, ?_, Or.inr ⟨i.val + 1, by omega, hi_mem⟩⟩
              rw [hBeq, himg_insert]
            have hiff : Comp A ↔ Comp B :=
              ⟨fun hA => Relation.ReflTransGen.tail hA (Or.inl hup),
               fun hB => Relation.ReflTransGen.tail hB (Or.inr hup)⟩
            by_cases hA : Comp A
            · have hB := hiff.mp hA
              simp only [hA, hB, ite_true]
              exact zmod2_add_self 1
            · have hB : ¬ Comp B := fun h => hA (hiff.mpr h)
              simp [hA, hB]
    rw [hF0, hb0, add_zero]
  rw [heq, hchi_one] at hchi_lhs
  exact one_ne_zero hchi_lhs

theorem static_lower {n d : ℕ} (hn : 0 < n) (h2 : 2 ≤ n)
    (hall : ∀ T, rejects n hn T → StaticRep (blockers n hn T) d 1) :
    (n = 2 ∧ 2 ≤ d) ∨ n + 2 < 2 ^ d := by
  have hstat := hall (anchoredTable n hn) (rejects_anchoredTable hn h2)
  have hd2 : 2 ≤ d := by
    by_contra hlt
    obtain ⟨q, b, hq, hb, heq⟩ := hstat
    have hq0 : ∀ C ∈ blockers n hn (anchoredTable n hn), q C = 0 := by
      intro C hC
      rcases hq C hC with h0 | hdeg
      · exact h0
      · have := totalDegree_mem_blockers hn h2 hC; omega
    have hb0 : ∀ v, b v = 0 := by
      intro v
      rcases hb v with h0 | hdeg
      · exact h0
      · omega
    have hsum1 : (blockers n hn (anchoredTable n hn)).sum (fun C => q C * clausePoly C) = 0 :=
      Finset.sum_eq_zero fun C hC => by rw [hq0 C hC, zero_mul]
    have hsum2 : (∑ v : Fin n, b v * (X v * X v + X v)) = 0 :=
      Finset.sum_eq_zero fun v _ => by rw [hb0 v, zero_mul]
    rw [hsum1, hsum2, add_zero] at heq
    exact zero_ne_one heq
  obtain ⟨U, hnU, hcond, hreach⟩ := static_anchored_to_pebble hn h2 hstat
  by_cases hd3 : 3 ≤ d
  · right
    rcases hcond with hlt | h1
    · have := natReach_strict_of_card_lt (by omega) hreach hlt hnU
      omega
    · have := natReach_strict_of_one_mem hd3 hreach h1 hnU
      omega
  · left
    have hd_eq : d = 2 := by omega
    subst hd_eq
    have hbd := natReach_bound_aux 2 (by decide) U hreach n hnU
    exact ⟨by omega, le_refl 2⟩

end PEqualNP.Outside.L_pcx_245_aux

theorem PEqualNP.Outside.L_pcx_245 : (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n →
  let P := MvPolynomial (Fin n) (ZMod 2)
  let static := fun (axioms : Finset (PEqualNP.ProofComplexity.Clause (Fin n))) (budget : ℕ) =>
    ∃ (q : PEqualNP.ProofComplexity.Clause (Fin n) → P) (b : Fin n → P),
      (∀ C ∈ axioms, q C = 0 ∨ (q C).totalDegree + (PEqualNP.ProofComplexity.clausePoly C).totalDegree ≤ budget) ∧
      (∀ v, b v = 0 ∨ (b v).totalDegree + 2 ≤ budget) ∧
      axioms.sum (fun C => q C * PEqualNP.ProofComplexity.clausePoly C) +
        (∑ v, b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) = 1
  let pos := fun i : ℕ => (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)
  let blockers := fun T : Fin n → Bool → Bool → Bool =>
    let blocks := (Finset.univ : Finset (Fin n × (Bool × Bool))).filter
      (fun z => T z.1 z.2.1 z.2.2 = false)
    blocks.image (fun row =>
      ({(row.1, !row.2.1), (pos (row.1.val+1), !row.2.2)} : PEqualNP.ProofComplexity.Clause (Fin n)))
  let rejects := fun candidate : Fin n → Bool → Bool → Bool =>
    ¬ ∃ x : Fin n → Bool, ∀ i : Fin n, candidate i (x i) (x (pos (i.val+1))) = true
  (∀ table, rejects table →
    let G := PEqualNP.ProofComplexity.cnfSystem (↑(blockers table) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    PEqualNP.ProofComplexity.PCRefutable G 2 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable G 1) ∧
  (∀ d : ℕ, (∀ table, rejects table → static (blockers table) d) ↔ (n = 2 ∧ 2 ≤ d) ∨ n+2 < 2^d)) := by
  intro n hn h2 P static pos blockers rejects
  refine ⟨fun table hrej => ⟨?_, ?_⟩, fun d => ⟨?_, ?_⟩⟩
  · exact PEqualNP.Outside.L_pcx_245_aux.pcRefutable_two hn h2 table hrej
  · exact PEqualNP.Outside.L_pcx_245_aux.not_pcRefutable_one hn h2 table
  · exact PEqualNP.Outside.L_pcx_245_aux.static_lower hn h2
  · intro hcond table hrej
    rcases hcond with ⟨hn2, hd2⟩ | hpow
    · exact PEqualNP.Outside.L_pcx_245_aux.static_upper_n2 hn hn2 hd2 table hrej
    · exact PEqualNP.Outside.L_pcx_245_aux.static_upper_pow hn h2 hpow table hrej
