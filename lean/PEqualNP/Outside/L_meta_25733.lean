import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25733

def lab (n b : ℕ) (t : Fin n) (j : Fin b) : Fin (n * b) :=
  ⟨t.val + n * j.val, by
    have h1 := t.isLt
    have h2 := j.isLt
    calc t.val + n * j.val < n + n * j.val := by omega
      _ = n * (j.val + 1) := by ring
      _ ≤ n * b := Nat.mul_le_mul_left n (by omega)⟩

def typ (n b : ℕ) (hn : 0 < n) (x : Fin (n * b)) : Fin n := ⟨x.val % n, Nat.mod_lt _ hn⟩

def idx (n b : ℕ) (hn : 0 < n) (x : Fin (n * b)) : Fin b :=
  ⟨x.val / n, (Nat.div_lt_iff_lt_mul hn).mpr (lt_of_lt_of_eq x.isLt (Nat.mul_comm n b))⟩

theorem typ_lab (n b : ℕ) (hn : 0 < n) (t : Fin n) (j : Fin b) : typ n b hn (lab n b t j) = t := by
  apply Fin.ext
  simp only [typ, lab]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]

theorem idx_lab (n b : ℕ) (hn : 0 < n) (t : Fin n) (j : Fin b) : idx n b hn (lab n b t j) = j := by
  apply Fin.ext
  simp only [idx, lab]
  rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt t.isLt, zero_add]

theorem lab_typ_idx (n b : ℕ) (hn : 0 < n) (x : Fin (n * b)) :
    lab n b (typ n b hn x) (idx n b hn x) = x := by
  apply Fin.ext
  simp only [typ, idx, lab]
  exact Nat.mod_add_div _ _

theorem lab_eq_iff (n b : ℕ) (hn : 0 < n) (x : Fin (n * b)) (j : Fin b) :
    x = lab n b (typ n b hn x) j ↔ j = idx n b hn x := by
  constructor
  · intro h
    have := congrArg (idx n b hn) h
    rw [idx_lab] at this
    exact this.symm
  · intro h
    rw [h, lab_typ_idx]

theorem card_typ (n b : ℕ) (hn : 0 < n) (c : Fin n) :
    (Finset.univ.filter (fun y : Fin (n * b) => typ n b hn y = c)).card = b := by
  have : (Finset.univ.filter (fun y : Fin (n * b) => typ n b hn y = c))
      = (Finset.univ : Finset (Fin b)).image (fun j => lab n b c j) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      exact ⟨idx n b hn y, by rw [← hy, lab_typ_idx]⟩
    · rintro ⟨j, rfl⟩
      exact typ_lab n b hn c j
  rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro j1 j2 h
  have := congrArg (idx n b hn) h
  rwa [idx_lab, idx_lab] at this

theorem cnt2 (n b : ℕ) (t1 t2 : Fin n) (ht : t1 ≠ t2) (j1 j2 : Fin b) :
    (Finset.univ.filter (fun f : Fin n → Fin b => f t1 = j1 ∧ f t2 = j2)).card * b ^ 2 ≤ b ^ n := by
  have hcard : b ^ n = (Finset.univ : Finset (Fin n → Fin b)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hprod : (Finset.univ.filter (fun f : Fin n → Fin b => f t1 = j1 ∧ f t2 = j2)).card * b ^ 2
      = ((Finset.univ.filter (fun f : Fin n → Fin b => f t1 = j1 ∧ f t2 = j2)) ×ˢ
          (Finset.univ : Finset (Fin b × Fin b))).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  rw [hprod, hcard]
  apply Finset.card_le_card_of_injOn
    (fun p => Function.update (Function.update p.1 t1 p.2.1) t2 p.2.2)
  · intro p _
    exact Finset.mem_univ _
  · intro p hp p' hp' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, and_true] at hp hp'
    have e1 : p.2.2 = p'.2.2 := by
      have := congrFun heq t2
      simpa using this
    have e2 : p.2.1 = p'.2.1 := by
      have := congrFun heq t1
      simpa [Function.update_of_ne ht] using this
    have e3 : p.1 = p'.1 := by
      funext t
      by_cases h1 : t = t1
      · rw [h1, hp.1, hp'.1]
      · by_cases h2 : t = t2
        · rw [h2, hp.2, hp'.2]
        · have := congrFun heq t
          simpa [Function.update_of_ne h2, Function.update_of_ne h1] using this
    exact Prod.ext e3 (Prod.ext e2 e1)

def ct (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (f : Fin n → Fin b) (t : Fin n) : Fin n :=
  typ n b hn (π (lab n b t (f t)))

def acnt (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (c t : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin b => typ n b hn (π (lab n b t j)) = c)).card

theorem acnt_le (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (c t : Fin n) :
    acnt n b hn π c t ≤ b := by
  unfold acnt
  calc _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_filter_le _ _
    _ = b := by rw [Finset.card_univ, Fintype.card_fin]

theorem avoid_card (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (c : Fin n) :
    (Finset.univ.filter (fun f : Fin n → Fin b => ∀ t, ct n b hn π f t ≠ c)).card
      = ∏ t : Fin n, (b - acnt n b hn π c t) := by
  have h1 : (Finset.univ.filter (fun f : Fin n → Fin b => ∀ t, ct n b hn π f t ≠ c))
      = Fintype.piFinset (fun t : Fin n =>
          Finset.univ.filter (fun j : Fin b => typ n b hn (π (lab n b t j)) ≠ c)) := by
    ext f
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro h t
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h.2 t⟩
    · intro h
      exact ⟨Finset.mem_univ _, fun t => (Finset.mem_filter.mp (h t)).2⟩
  rw [h1, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro t _
  have h2 : (Finset.univ.filter (fun j : Fin b => typ n b hn (π (lab n b t j)) = c)).card
      + (Finset.univ.filter (fun j : Fin b => typ n b hn (π (lab n b t j)) ≠ c)).card = b := by
    have h3 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin b))) (fun j : Fin b => typ n b hn (π (lab n b t j)) = c)
    rw [Finset.card_univ, Fintype.card_fin] at h3
    exact h3
  unfold acnt
  omega

theorem acnt_sum (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (c : Fin n) :
    ∑ t : Fin n, acnt n b hn π c t = b := by
  have h1 : ∑ t : Fin n, acnt n b hn π c t
      = (Finset.univ.filter (fun p : Fin n × Fin b => typ n b hn (π (lab n b p.1 p.2)) = c)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    unfold acnt
    rw [Finset.card_filter]
  have h2 : (Finset.univ.filter (fun p : Fin n × Fin b => typ n b hn (π (lab n b p.1 p.2)) = c)).card
      = (Finset.univ.filter (fun y : Fin (n * b) => typ n b hn y = c)).card := by
    apply Finset.card_bij' (fun p _ => π (lab n b p.1 p.2))
      (fun y _ => (typ n b hn (π.symm y), idx n b hn (π.symm y)))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [lab_typ_idx, Equiv.apply_symm_apply]
      exact hy
    · intro p _
      simp only [Equiv.symm_apply_apply, typ_lab, idx_lab]
    · intro y _
      simp only [lab_typ_idx, Equiv.apply_symm_apply]
  rw [h1, h2, card_typ]

theorem exp_bound (n b : ℕ) (hb : 0 < b) (a : Fin n → ℕ) (ha : ∀ t, a t ≤ b) (hs : ∑ t, a t = b) :
    8 * ∏ t : Fin n, (b - a t) ≤ 3 * b ^ n := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : ∀ t : Fin n, ((b - a t : ℕ) : ℝ) ≤ (b : ℝ) * Real.exp (-((a t : ℝ) / b)) := by
    intro t
    have h2 := Real.one_sub_le_exp_neg ((a t : ℝ) / b)
    rw [Nat.cast_sub (ha t)]
    have h3 : (b : ℝ) - (a t : ℝ) = (b : ℝ) * (1 - (a t : ℝ) / b) := by field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 hbR.le
  have h4 : ∏ t : Fin n, ((b - a t : ℕ) : ℝ) ≤ ∏ t : Fin n, ((b : ℝ) * Real.exp (-((a t : ℝ) / b))) :=
    Finset.prod_le_prod₀ (fun t _ => Nat.cast_nonneg _) (fun t _ => h1 t)
  have h5 : ∏ t : Fin n, ((b : ℝ) * Real.exp (-((a t : ℝ) / b))) = (b : ℝ) ^ n * Real.exp (-1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Nat.cast_sum, hs, div_self hbR.ne']
  have h6 : Real.exp (-1) < 3 / 8 := by
    have h7 := Real.exp_one_gt_d9
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have h8 : (8 : ℝ) * ∏ t : Fin n, ((b - a t : ℕ) : ℝ) ≤ 3 * (b : ℝ) ^ n := by
    have hbn : (0 : ℝ) ≤ (b : ℝ) ^ n := by positivity
    calc (8 : ℝ) * ∏ t : Fin n, ((b - a t : ℕ) : ℝ) ≤ 8 * ((b : ℝ) ^ n * Real.exp (-1)) := by
          rw [← h5]; exact mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ ≤ 8 * ((b : ℝ) ^ n * (3 / 8)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left h6.le hbn
      _ = 3 * (b : ℝ) ^ n := by ring
  exact_mod_cast h8

def hitS (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (f : Fin n → Fin b) : Finset (Fin n) :=
  Finset.univ.image (ct n b hn π f)

def missed (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (f : Fin n → Fin b) : ℕ :=
  (Finset.univ.filter (fun c : Fin n => ∀ t, ct n b hn π f t ≠ c)).card

theorem hit_add_missed (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (f : Fin n → Fin b) :
    (hitS n b hn π f).card + missed n b hn π f = n := by
  have h1 : hitS n b hn π f = Finset.univ.filter (fun c : Fin n => ∃ t, ct n b hn π f t = c) := by
    ext c
    simp [hitS]
  have h2 : (Finset.univ.filter (fun c : Fin n => ∀ t, ct n b hn π f t ≠ c))
      = Finset.univ.filter (fun c : Fin n => ¬ ∃ t, ct n b hn π f t = c) := by
    apply Finset.filter_congr
    intro c _
    simp
  have h3 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun c : Fin n => ∃ t, ct n b hn π f t = c)
  rw [Finset.card_univ, Fintype.card_fin] at h3
  unfold missed
  rw [h1, h2]
  exact h3

theorem missed_sum (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (π : Equiv.Perm (Fin (n * b))) :
    8 * ∑ f : Fin n → Fin b, missed n b hn π f ≤ 3 * n * b ^ n := by
  have h1 : ∑ f : Fin n → Fin b, missed n b hn π f
      = ∑ c : Fin n, (Finset.univ.filter (fun f : Fin n → Fin b => ∀ t, ct n b hn π f t ≠ c)).card := by
    unfold missed
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [h1, Finset.mul_sum]
  calc ∑ c : Fin n, 8 * (Finset.univ.filter (fun f : Fin n → Fin b => ∀ t, ct n b hn π f t ≠ c)).card
      ≤ ∑ c : Fin n, 3 * b ^ n := by
        apply Finset.sum_le_sum
        intro c _
        rw [avoid_card]
        exact exp_bound n b hb (acnt n b hn π c) (acnt_le n b hn π c) (acnt_sum n b hn π c)
    _ = 3 * n * b ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring

theorem good_count (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (π : Equiv.Perm (Fin (n * b))) :
    b ^ n < 4 * (Finset.univ.filter (fun f : Fin n → Fin b =>
      (n + 1) / 2 ≤ (hitS n b hn π f).card)).card := by
  set G := (Finset.univ.filter (fun f : Fin n → Fin b => (n + 1) / 2 ≤ (hitS n b hn π f).card)).card
    with hG
  set Bd := (Finset.univ.filter (fun f : Fin n → Fin b => ¬ (n + 1) / 2 ≤ (hitS n b hn π f).card)).card
    with hBd
  have hGB : G + Bd = b ^ n := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n → Fin b)))
      (fun f : Fin n → Fin b => (n + 1) / 2 ≤ (hitS n b hn π f).card)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  have hP : 0 < b ^ n := pow_pos hb n
  have hm := missed_sum n b hn hb π
  have hbad : (n + 1) * Bd ≤ 2 * ∑ f : Fin n → Fin b, missed n b hn π f := by
    have h1 : ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin b =>
        ¬ (n + 1) / 2 ≤ (hitS n b hn π f).card), (n + 1)
        ≤ ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin b =>
        ¬ (n + 1) / 2 ≤ (hitS n b hn π f).card), 2 * missed n b hn π f := by
      apply Finset.sum_le_sum
      intro f hf
      rw [Finset.mem_filter] at hf
      have := hit_add_missed n b hn π f
      omega
    have h2 : ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin b =>
        ¬ (n + 1) / 2 ≤ (hitS n b hn π f).card), 2 * missed n b hn π f
        ≤ 2 * ∑ f : Fin n → Fin b, missed n b hn π f := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_const, smul_eq_mul, ← hBd] at h1
    calc (n + 1) * Bd = Bd * (n + 1) := by ring
      _ ≤ _ := h1.trans h2
  by_contra hcon
  have h4 : 4 * G ≤ b ^ n := by omega
  have h5 : 3 * b ^ n ≤ 4 * Bd := by omega
  have h6 : (n + 1) * (3 * b ^ n) ≤ (n + 1) * (4 * Bd) := Nat.mul_le_mul_left _ h5
  have h7 : (n + 1) * (4 * Bd) ≤ 3 * n * b ^ n := by
    calc (n + 1) * (4 * Bd) = 4 * ((n + 1) * Bd) := by ring
      _ ≤ 4 * (2 * ∑ f : Fin n → Fin b, missed n b hn π f) := Nat.mul_le_mul_left _ hbad
      _ = 8 * ∑ f : Fin n → Fin b, missed n b hn π f := by ring
      _ ≤ 3 * n * b ^ n := hm
  have h8 : (n + 1) * (3 * b ^ n) = 3 * n * b ^ n + 3 * b ^ n := by ring
  omega

def NErr (n b : ℕ) (hn : 0 < n) (Err : Finset (Fin (n * b) × Fin (n * b))) (f : Fin n → Fin b) : ℕ :=
  (Err.filter (fun z => typ n b hn z.1 ≠ typ n b hn z.2 ∧
    z.1 = lab n b (typ n b hn z.1) (f (typ n b hn z.1)) ∧
    z.2 = lab n b (typ n b hn z.2) (f (typ n b hn z.2)))).card

theorem sumN (n b : ℕ) (hn : 0 < n) (Err : Finset (Fin (n * b) × Fin (n * b))) :
    (∑ f : Fin n → Fin b, NErr n b hn Err f) * b ^ 2 ≤ Err.card * b ^ n := by
  have h1 : ∑ f : Fin n → Fin b, NErr n b hn Err f
      = ∑ z ∈ Err, (Finset.univ.filter (fun f : Fin n → Fin b =>
          typ n b hn z.1 ≠ typ n b hn z.2 ∧
          z.1 = lab n b (typ n b hn z.1) (f (typ n b hn z.1)) ∧
          z.2 = lab n b (typ n b hn z.2) (f (typ n b hn z.2)))).card := by
    unfold NErr
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have h2 : ∀ z ∈ Err, (Finset.univ.filter (fun f : Fin n → Fin b =>
          typ n b hn z.1 ≠ typ n b hn z.2 ∧
          z.1 = lab n b (typ n b hn z.1) (f (typ n b hn z.1)) ∧
          z.2 = lab n b (typ n b hn z.2) (f (typ n b hn z.2)))).card * b ^ 2 ≤ b ^ n := by
    intro z _
    by_cases hz : typ n b hn z.1 = typ n b hn z.2
    · have : (Finset.univ.filter (fun f : Fin n → Fin b =>
          typ n b hn z.1 ≠ typ n b hn z.2 ∧
          z.1 = lab n b (typ n b hn z.1) (f (typ n b hn z.1)) ∧
          z.2 = lab n b (typ n b hn z.2) (f (typ n b hn z.2)))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro f _ h
        exact h.1 hz
      rw [this]
      simp
    · have hsub : (Finset.univ.filter (fun f : Fin n → Fin b =>
          typ n b hn z.1 ≠ typ n b hn z.2 ∧
          z.1 = lab n b (typ n b hn z.1) (f (typ n b hn z.1)) ∧
          z.2 = lab n b (typ n b hn z.2) (f (typ n b hn z.2))))
          ⊆ Finset.univ.filter (fun f : Fin n → Fin b =>
            f (typ n b hn z.1) = idx n b hn z.1 ∧ f (typ n b hn z.2) = idx n b hn z.2) := by
        intro f hf
        rw [Finset.mem_filter] at hf ⊢
        exact ⟨Finset.mem_univ _, (lab_eq_iff n b hn z.1 _).mp hf.2.2.1,
          (lab_eq_iff n b hn z.2 _).mp hf.2.2.2⟩
      calc _ ≤ (Finset.univ.filter (fun f : Fin n → Fin b =>
            f (typ n b hn z.1) = idx n b hn z.1 ∧ f (typ n b hn z.2) = idx n b hn z.2)).card * b ^ 2 :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ ≤ b ^ n := cnt2 n b _ _ hz _ _
  rw [h1, Finset.sum_mul]
  calc _ ≤ ∑ z ∈ Err, b ^ n := Finset.sum_le_sum h2
    _ = Err.card * b ^ n := by rw [Finset.sum_const, smul_eq_mul]

theorem main_exists (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (π : Equiv.Perm (Fin (n * b)))
    (Err : Finset (Fin (n * b) × Fin (n * b))) (E : ℕ) (hE : Err.card ≤ E) :
    ∃ f : Fin n → Fin b, (n + 1) / 2 ≤ (hitS n b hn π f).card ∧ NErr n b hn Err f * b ^ 2 ≤ 4 * E := by
  by_contra hcon
  have hcon' : ∀ f : Fin n → Fin b, (n + 1) / 2 ≤ (hitS n b hn π f).card →
      4 * E + 1 ≤ NErr n b hn Err f * b ^ 2 := by
    intro f hf
    by_contra h
    exact hcon ⟨f, hf, by omega⟩
  have hg := good_count n b hn hb π
  set Good := Finset.univ.filter (fun f : Fin n → Fin b => (n + 1) / 2 ≤ (hitS n b hn π f).card)
    with hGood
  have h1 : Good.card * (4 * E + 1) ≤ ∑ f ∈ Good, NErr n b hn Err f * b ^ 2 := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro f hf
    exact hcon' f (Finset.mem_filter.mp hf).2
  have h2 : ∑ f ∈ Good, NErr n b hn Err f * b ^ 2 ≤ ∑ f : Fin n → Fin b, NErr n b hn Err f * b ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have h3 : ∑ f : Fin n → Fin b, NErr n b hn Err f * b ^ 2
      = (∑ f : Fin n → Fin b, NErr n b hn Err f) * b ^ 2 := (Finset.sum_mul _ _ _).symm
  have h4 := sumN n b hn Err
  have h5 : Err.card * b ^ n ≤ E * b ^ n := Nat.mul_le_mul_right _ hE
  have hP : 0 < b ^ n := pow_pos hb n
  have h6 : E * b ^ n ≤ E * (4 * Good.card) := Nat.mul_le_mul_left E (by omega)
  have a1 : Good.card * (4 * E + 1) = 4 * (E * Good.card) + Good.card := by ring
  have a2 : E * (4 * Good.card) = 4 * (E * Good.card) := by ring
  omega

theorem select (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (f : Fin n → Fin b) (h : ℕ)
    (hh : h ≤ (hitS n b hn π f).card) :
    ∃ row : Fin h → Fin n, Function.Injective row ∧
      Function.Injective (fun i => ct n b hn π f (row i)) := by
  classical
  have hcard : Fintype.card (Fin h) ≤ Fintype.card {c // c ∈ hitS n b hn π f} := by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact hh
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hex : ∀ c : {c // c ∈ hitS n b hn π f}, ∃ t, ct n b hn π f t = c.val := by
    intro c
    have := c.property
    unfold hitS at this
    rw [Finset.mem_image] at this
    obtain ⟨t, _, ht⟩ := this
    exact ⟨t, ht⟩
  choose σ hσ using hex
  refine ⟨fun i => σ (ι i), ?_, ?_⟩
  · intro i j hij
    have hij' : σ (ι i) = σ (ι j) := hij
    have h1 : (ι i).val = (ι j).val := by rw [← hσ (ι i), ← hσ (ι j), hij']
    exact ι.injective (Subtype.ext h1)
  · intro i j hij
    simp only [hσ] at hij
    exact ι.injective (Subtype.ext hij)

theorem decode (n b q : ℕ) (hn : 0 < n) (hb : 0 < b) (rowCap colCap : Fin q → ℕ)
    (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin (n * b))) (E : ℕ)
    (rf cf : Fin (n * b) → Bool) (R C : Fin q → Finset (Fin (n * b)))
    (out : Finset (Fin (n * b)) → (Fin q → Bool) → Bool)
    (hcap : ∀ t, (R t).card ≤ rowCap t ∧ (C t).card ≤ colCap t)
    (herr : ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
        out {z.1, z.2} (fun t => decide (z.1 ∈ R t ∨ π z.2 ∈ C t)) ≠
          Bool.xor (G (typ n b hn z.1) (typ n b hn (π z.2))) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E) :
    ∃ row col : Fin ((n + 1) / 2) ↪ Fin n,
      ∃ (rf' cf' : Fin ((n + 1) / 2) → Bool) (R' C' : Fin q → Finset (Fin ((n + 1) / 2)))
        (out' : Finset (Fin ((n + 1) / 2)) → (Fin q → Bool) → Bool),
        (∀ t, (R' t).card ≤ rowCap t ∧ (C' t).card ≤ colCap t) ∧
        ((Finset.univ : Finset (Fin ((n + 1) / 2) × Fin ((n + 1) / 2))).filter (fun z =>
          out' {z.1, z.2} (fun t => decide (z.1 ∈ R' t ∨ (Equiv.refl _) z.2 ∈ C' t)) ≠
            Bool.xor (G (row z.1) (col ((Equiv.refl _) z.2)))
              (Bool.xor (rf' z.1) (cf' ((Equiv.refl _) z.2))))).card ≤ 4 * E / b ^ 2 := by
  classical
  obtain ⟨f, hf1, hf2⟩ := main_exists n b hn hb π _ E herr
  obtain ⟨row, hrow, hcol⟩ := select n b hn π f ((n + 1) / 2) hf1
  set e : Fin ((n + 1) / 2) → Fin (n * b) := fun i => lab n b (row i) (f (row i)) with he
  have he_typ : ∀ i, typ n b hn (e i) = row i := fun i => typ_lab n b hn _ _
  have he_inj : Function.Injective e := by
    intro i j hij
    apply hrow
    rw [← he_typ i, ← he_typ j, hij]
  have hπe_inj : Function.Injective (fun i => π (e i)) := fun i j hij => he_inj (π.injective hij)
  refine ⟨⟨row, hrow⟩, ⟨fun i => ct n b hn π f (row i), hcol⟩, fun i => rf (e i),
    fun j => cf (π (e j)), fun t => Finset.univ.filter (fun i => e i ∈ R t),
    fun t => Finset.univ.filter (fun j => π (e j) ∈ C t),
    fun S w => if hS : ∃ i, S = {i} then
        Bool.xor (G (row hS.choose) (ct n b hn π f (row hS.choose)))
          (Bool.xor (rf (e hS.choose)) (cf (π (e hS.choose))))
      else out (S.image e) w, ?_, ?_⟩
  · intro t
    constructor
    · calc (Finset.univ.filter (fun i => e i ∈ R t)).card ≤ (R t).card :=
            Finset.card_le_card_of_injOn e (fun i hi => (Finset.mem_filter.mp hi).2) he_inj.injOn
        _ ≤ rowCap t := (hcap t).1
    · calc (Finset.univ.filter (fun j => π (e j) ∈ C t)).card ≤ (C t).card :=
            Finset.card_le_card_of_injOn (fun j => π (e j))
              (fun j hj => (Finset.mem_filter.mp hj).2) hπe_inj.injOn
        _ ≤ colCap t := (hcap t).2
  · refine le_trans ?_ ((Nat.le_div_iff_mul_le (by positivity)).mpr hf2)
    unfold NErr
    apply Finset.card_le_card_of_injOn (fun z : Fin ((n + 1) / 2) × Fin ((n + 1) / 2) => (e z.1, e z.2))
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz
      have hz2 := hz.2
      simp only [Function.Embedding.coeFn_mk, Equiv.refl_apply] at hz2
      have hne : z.1 ≠ z.2 := by
        intro heq
        apply hz2
        have hS : ∃ i, ({z.1, z.2} : Finset (Fin ((n + 1) / 2))) = {i} := ⟨z.1, by rw [heq]; simp⟩
        have hc : hS.choose = z.1 := by
          have h1 := hS.choose_spec
          have h2 : z.1 ∈ ({hS.choose} : Finset (Fin ((n + 1) / 2))) := by
            rw [← h1]; exact Finset.mem_insert_self _ _
          exact (Finset.mem_singleton.mp h2).symm
        rw [dif_pos hS, hc, ← heq]
      have hnS : ¬ ∃ i, ({z.1, z.2} : Finset (Fin ((n + 1) / 2))) = {i} := by
        rintro ⟨i, hi⟩
        have h1 := Finset.card_pair hne
        rw [hi, Finset.card_singleton] at h1
        omega
      simp only [dif_neg hnS, Finset.image_insert, Finset.image_singleton, Finset.mem_filter,
        Finset.mem_univ, true_and] at hz2
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_, ?_, ?_⟩
      · show out {e z.1, e z.2} (fun t => decide (e z.1 ∈ R t ∨ π (e z.2) ∈ C t)) ≠
          Bool.xor (G (typ n b hn (e z.1)) (typ n b hn (π (e z.2)))) (Bool.xor (rf (e z.1)) (cf (π (e z.2))))
        rw [he_typ]
        exact hz2
      · show typ n b hn (e z.1) ≠ typ n b hn (e z.2)
        rw [he_typ, he_typ]
        exact fun h => hne (hrow h)
      · show e z.1 = lab n b (typ n b hn (e z.1)) (f (typ n b hn (e z.1)))
        rw [he_typ]
      · show e z.2 = lab n b (typ n b hn (e z.2)) (f (typ n b hn (e z.2)))
        rw [he_typ]
    · intro z _ z' _ hzz
      have h1 : e z.1 = e z'.1 := congrArg Prod.fst hzz
      have h2 : e z.2 = e z'.2 := congrArg Prod.snd hzz
      exact Prod.ext (he_inj h1) (he_inj h2)

end PEqualNP.Outside.L_meta_25733

theorem PEqualNP.Outside.L_meta_25733 : (∀ (n b q : ℕ) (hn : 0 < n), 0 < b →
  ∀ (rowCap colCap : Fin q → ℕ),
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (π : Equiv.Perm (Fin s)) (E : ℕ) =>
    ∃ (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      (∀ t, (R t).card ≤ rowCap t ∧ (C t).card ≤ colCap t) ∧
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun t => decide (z.1 ∈ R t ∨ π z.2 ∈ C t)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E
  let typ := fun label : Fin (n*b) => (⟨label.val % n, Nat.mod_lt _ hn⟩ : Fin n)
  let h := (n+1)/2
  ∀ (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin (n*b))) (E : ℕ),
    fits (n*b) (fun x y => G (typ x) (typ y)) π E →
    ∃ row col : Fin h ↪ Fin n,
      fits h (fun x y => G (row x) (col y)) (Equiv.refl _) (4*E/b^2)) := by
  intro n b q hn hb rowCap colCap
  dsimp only
  intro G π E hfit
  obtain ⟨rf, cf, R, C, out, hcap, herr⟩ := hfit
  exact PEqualNP.Outside.L_meta_25733.decode n b q hn hb rowCap colCap G π E rf cf R C out hcap herr
