import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38163

section
variable {r c : Nat} (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)

theorem two_rows (H1 : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (H2 : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    ∀ x (i j : Fin 3), i ≠ j → rowOK x i ∨ rowOK x j := by
  intro x i j hij
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> decide
  obtain ⟨y, hy⟩ := (H2 k).2
  obtain ⟨l, hl1, hl2⟩ := H1 x y
  have hlk : l ≠ k := fun e => hy (e ▸ hl2)
  have : l = i ∨ l = j := by
    simp only [ne_eq, Fin.ext_iff] at hij hki hkj hlk ⊢
    omega
  rcases this with rfl | rfl
  · exact Or.inl hl1
  · exact Or.inr hl1

theorem two_cols (H1 : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (H2 : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    ∀ y (i j : Fin 3), i ≠ j → colOK y i ∨ colOK y j := by
  intro y i j hij
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> decide
  obtain ⟨x, hx⟩ := (H2 k).1
  obtain ⟨l, hl1, hl2⟩ := H1 x y
  have hlk : l ≠ k := fun e => hx (e ▸ hl1)
  have : l = i ∨ l = j := by
    simp only [ne_eq, Fin.ext_iff] at hij hki hkj hlk ⊢
    omega
  rcases this with rfl | rfl
  · exact Or.inl hl2
  · exact Or.inr hl2

def bL (j : Fin 5) (x : Fin r) : Prop :=
  if j = 0 then rowOK x 2 else if j = 1 then rowOK x 1 else if j = 2 then ¬ rowOK x 1
  else ¬ rowOK x 2

def bR (j : Fin 5) (y : Fin c) : Prop :=
  if j = 0 then colOK y 2 else if j = 1 then ¬ colOK y 2 else if j = 2 then ¬ colOK y 2
  else if j = 3 then colOK y 2 ∧ colOK y 1 else colOK y 2 ∧ ¬ colOK y 1

def bT (j : Fin 5) : Fin 3 :=
  if j = 0 then 2 else if j = 1 then 1 else if j = 2 then 0 else if j = 3 then 1 else 0

theorem base_unique (x : Fin r) (y : Fin c) :
    ∃! j : Fin 5, bL rowOK j x ∧ bR colOK j y := by
  classical
  by_cases c2 : colOK y 2
  · by_cases r2 : rowOK x 2
    · refine ⟨0, ⟨by simp [bL, r2], by simp [bR, c2]⟩, ?_⟩
      rintro j ⟨hl, hr⟩
      fin_cases j <;> simp_all [bL, bR]
    · by_cases c1 : colOK y 1
      · refine ⟨3, ⟨by simp [bL, r2], by simp [bR, c2, c1]⟩, ?_⟩
        rintro j ⟨hl, hr⟩
        fin_cases j <;> simp_all [bL, bR]
      · refine ⟨4, ⟨by simp [bL, r2], by simp [bR, c2, c1]⟩, ?_⟩
        rintro j ⟨hl, hr⟩
        fin_cases j <;> simp_all [bL, bR]
  · by_cases r1 : rowOK x 1
    · refine ⟨1, ⟨by simp [bL, r1], by simp [bR, c2]⟩, ?_⟩
      rintro j ⟨hl, hr⟩
      fin_cases j <;> simp_all [bL, bR]
    · refine ⟨2, ⟨by simp [bL, r1], by simp [bR, c2]⟩, ?_⟩
      rintro j ⟨hl, hr⟩
      fin_cases j <;> simp_all [bL, bR]

theorem base_valid (hrow : ∀ x (i j : Fin 3), i ≠ j → rowOK x i ∨ rowOK x j)
    (hcol : ∀ y (i j : Fin 3), i ≠ j → colOK y i ∨ colOK y j)
    (j : Fin 5) (x : Fin r) (y : Fin c) (hl : bL rowOK j x) (hr : bR colOK j y) :
    rowOK x (bT j) ∧ colOK y (bT j) := by
  fin_cases j
  · simp only [bL, bR, bT] at hl hr ⊢
    simp_all
  · simp only [bL, bR, bT] at hl hr ⊢
    simp at hl hr ⊢
    exact ⟨hl, (hcol y 1 2 (by decide)).resolve_right hr⟩
  · simp only [bL, bR, bT] at hl hr ⊢
    simp at hl hr ⊢
    exact ⟨(hrow x 0 1 (by decide)).resolve_right hl, (hcol y 0 2 (by decide)).resolve_right hr⟩
  · simp only [bL, bR, bT] at hl hr ⊢
    simp at hl hr ⊢
    exact ⟨(hrow x 1 2 (by decide)).resolve_right hl, hr.2⟩
  · simp only [bL, bR, bT] at hl hr ⊢
    simp at hl hr ⊢
    exact ⟨(hrow x 0 2 (by decide)).resolve_right hl, (hcol y 0 1 (by decide)).resolve_right hr.2⟩

theorem upper (n : Nat) (H1 : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (H2 : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    ∃ (left : Fin (5 ^ (n + 1)) → (Fin (n + 1) → Fin r) → Prop)
      (right : Fin (5 ^ (n + 1)) → (Fin (n + 1) → Fin c) → Prop)
      (tag : Fin (5 ^ (n + 1)) → Fin (n + 1) → Fin 3),
      (∀ (x : Fin (n + 1) → Fin r) (y : Fin (n + 1) → Fin c),
        ∃! j : Fin (5 ^ (n + 1)), left j x ∧ right j y) ∧
      ∀ (j : Fin (5 ^ (n + 1))) (x : Fin (n + 1) → Fin r) (y : Fin (n + 1) → Fin c),
        left j x → right j y → ∀ k, rowOK (x k) (tag j k) ∧ colOK (y k) (tag j k) := by
  have hrow := two_rows rowOK colOK H1 H2
  have hcol := two_cols rowOK colOK H1 H2
  let e : (Fin (n + 1) → Fin 5) ≃ Fin (5 ^ (n + 1)) := finFunctionFinEquiv
  refine ⟨fun j x => ∀ k, bL rowOK (e.symm j k) (x k),
    fun j y => ∀ k, bR colOK (e.symm j k) (y k), fun j k => bT (e.symm j k), ?_, ?_⟩
  · intro x y
    choose J hJ hJu using fun k => base_unique rowOK colOK (x k) (y k)
    refine ⟨e J, ⟨fun k => ?_, fun k => ?_⟩, ?_⟩
    · simpa using (hJ k).1
    · simpa using (hJ k).2
    · rintro j ⟨hl, hr⟩
      have h : e.symm j = J := funext fun k => hJu k _ ⟨hl k, hr k⟩
      rw [← h, Equiv.apply_symm_apply]
  · intro j x y hl hr k
    exact base_valid rowOK colOK hrow hcol (e.symm j k) (x k) (y k) (hl k) (hr k)

end

theorem card5 {β : Type} [DecidableEq β] (s : Finset β) (v1 v2 v3 v4 v5 : β)
    (h : [v1, v2, v3, v4, v5].Nodup) (hs : ∀ v ∈ [v1, v2, v3, v4, v5], v ∈ s) :
    5 ≤ s.card := by
  have hc := List.toFinset_card_of_nodup h
  have hsub : [v1, v2, v3, v4, v5].toFinset ⊆ s := by
    intro v hv
    exact hs v (List.mem_toFinset.mp hv)
  have := Finset.card_le_card hsub
  simp only [List.length_cons, List.length_nil] at hc
  omega

theorem five {β : Type} [DecidableEq β] (g : Fin 3 × Fin 3 → β) (τ : β → Fin 3)
    (hrect : ∀ a b a' b' : Fin 3, g (a, b) = g (a', b') → g (a, b') = g (a, b))
    (hvalid : ∀ q, τ (g q) ≠ q.1 ∧ τ (g q) ≠ q.2) :
    5 ≤ (Finset.univ.image g).card := by
  have nc : ∀ q q' : Fin 3 × Fin 3,
      (∀ t : Fin 3, t = q.1 ∨ t = q.2 ∨ t = q'.1 ∨ t = q'.2) → g q ≠ g q' := by
    intro q q' hall e
    have h1 := hvalid q
    have h2 := hvalid q'
    rw [e] at h1
    rcases hall (τ (g q')) with h | h | h | h
    · exact h1.1 h
    · exact h1.2 h
    · exact h2.1 h
    · exact h2.2 h
  have mem : ∀ q, g q ∈ Finset.univ.image g := fun q => Finset.mem_image_of_mem g (Finset.mem_univ q)
  have n1 := nc (0, 1) (0, 2) (by decide)
  have n2 := nc (0, 1) (2, 0) (by decide)
  have n3 := nc (0, 1) (1, 2) (by decide)
  have n4 := nc (0, 1) (2, 1) (by decide)
  have n5 := nc (1, 0) (0, 2) (by decide)
  have n6 := nc (1, 0) (2, 0) (by decide)
  have n7 := nc (1, 0) (1, 2) (by decide)
  have n8 := nc (1, 0) (2, 1) (by decide)
  have n9 := nc (0, 2) (1, 2) (by decide)
  have n10 := nc (0, 2) (2, 1) (by decide)
  have n11 := nc (2, 0) (1, 2) (by decide)
  have n12 := nc (2, 0) (2, 1) (by decide)
  by_cases c01 : g (0, 1) = g (1, 0)
  · have c02 : g (0, 2) ≠ g (2, 0) := by
      intro c02
      have e1 := hrect 0 1 1 0 c01
      have e2 := hrect 0 2 2 0 c02
      exact n1 (e1.symm.trans e2)
    have c12 : g (1, 2) ≠ g (2, 1) := by
      intro c12
      have e1 := hrect 1 0 0 1 c01.symm
      have e2 := hrect 1 2 2 1 c12
      exact n7 (e1.symm.trans e2)
    refine card5 _ (g (0, 1)) (g (0, 2)) (g (2, 0)) (g (1, 2)) (g (2, 1)) ?_ ?_
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨n1, n2, n3, n4⟩, ⟨c02, n9, n10⟩, ⟨n11, n12⟩, c12, by simp⟩
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact mem _
  · by_cases c02 : g (0, 2) = g (2, 0)
    · have c12 : g (1, 2) ≠ g (2, 1) := by
        intro c12
        have e1 := hrect 2 0 0 2 c02.symm
        have e2 := hrect 2 1 1 2 c12.symm
        exact n12 (e1.symm.trans e2)
      refine card5 _ (g (0, 1)) (g (1, 0)) (g (0, 2)) (g (1, 2)) (g (2, 1)) ?_ ?_
      · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨⟨c01, n1, n3, n4⟩, ⟨n5, n7, n8⟩, ⟨n9, n10⟩, c12, by simp⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact mem _
    · refine card5 _ (g (0, 1)) (g (1, 0)) (g (0, 2)) (g (2, 0)) (g (1, 2)) ?_ ?_
      · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨⟨c01, n1, n2, n3⟩, ⟨n5, n6, n7⟩, ⟨c02, n9⟩, n11, by simp⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact mem _

theorem lower {r c : Nat} (n : Nat) (rowOK : Fin r → Fin 3 → Prop)
    (colOK : Fin c → Fin 3 → Prop)
    (H2 : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) (p : Nat)
    (left : Fin p → (Fin (n + 1) → Fin r) → Prop) (right : Fin p → (Fin (n + 1) → Fin c) → Prop)
    (tag : Fin p → Fin (n + 1) → Fin 3)
    (hpart : ∀ (x : Fin (n + 1) → Fin r) (y : Fin (n + 1) → Fin c),
      ∃! j : Fin p, left j x ∧ right j y)
    (hval : ∀ (j : Fin p) (x : Fin (n + 1) → Fin r) (y : Fin (n + 1) → Fin c),
      left j x → right j y → ∀ k, rowOK (x k) (tag j k) ∧ colOK (y k) (tag j k)) :
    5 * 3 ^ n ≤ p := by
  classical
  choose xs hxs using fun a : Fin 3 => (H2 a).1
  choose ys hys using fun b : Fin 3 => (H2 b).2
  let rowv : Fin 3 → (Fin n → Fin 3 × Fin 3) → Fin (n + 1) → Fin r :=
    fun a σ => Fin.cons (xs a) (fun k => xs (σ k).1)
  let colv : Fin 3 → (Fin n → Fin 3 × Fin 3) → Fin (n + 1) → Fin c :=
    fun b σ => Fin.cons (ys b) (fun k => ys (σ k).2)
  let offd : Finset (Fin 3 × Fin 3) := Finset.univ.filter (fun q => q.1 ≠ q.2)
  let U : Finset (Fin n → Fin 3 × Fin 3) := Fintype.piFinset (fun _ => offd)
  let meets : Fin p → (Fin n → Fin 3 × Fin 3) → Prop :=
    fun j σ => ∃ a b, left j (rowv a σ) ∧ right j (colv b σ)
  have hB : ∀ j, (U.filter (meets j)).card ≤ 2 ^ n := by
    intro j
    let P : Fin 3 → Finset (Fin 3 × Fin 3) := fun t => offd.filter (fun q => q.1 ≠ t ∧ q.2 ≠ t)
    have hP : ∀ t, (P t).card = 2 := by
      intro t
      fin_cases t <;> rfl
    have hsub : U.filter (meets j) ⊆ Fintype.piFinset (fun k : Fin n => P (tag j k.succ)) := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      obtain ⟨hU, a, b, hl, hr⟩ := hσ
      rw [Fintype.mem_piFinset] at hU ⊢
      intro k
      have hv := hval j _ _ hl hr k.succ
      simp only [rowv, colv, Fin.cons_succ] at hv
      have h1 : (σ k).1 ≠ tag j k.succ := fun e => hxs _ (e ▸ hv.1)
      have h2 : (σ k).2 ≠ tag j k.succ := fun e => hys _ (e ▸ hv.2)
      simp only [P, Finset.mem_filter]
      exact ⟨hU k, h1, h2⟩
    calc (U.filter (meets j)).card
        ≤ (Fintype.piFinset (fun k : Fin n => P (tag j k.succ))).card := Finset.card_le_card hsub
      _ = ∏ k : Fin n, (P (tag j k.succ)).card := Fintype.card_piFinset _
      _ = 2 ^ n := by simp [hP]
  have hA : ∀ σ ∈ U, 5 ≤ (Finset.univ.filter (fun j => meets j σ)).card := by
    intro σ _
    choose g hg hgu using fun q : Fin 3 × Fin 3 => hpart (rowv q.1 σ) (colv q.2 σ)
    have hrect : ∀ a b a' b' : Fin 3, g (a, b) = g (a', b') → g (a, b') = g (a, b) := by
      intro a b a' b' h
      exact (hgu (a, b') (g (a, b)) ⟨(hg (a, b)).1, h ▸ (hg (a', b')).2⟩).symm
    have hvalid : ∀ q, tag (g q) 0 ≠ q.1 ∧ tag (g q) 0 ≠ q.2 := by
      intro q
      have hv := hval (g q) _ _ (hg q).1 (hg q).2 0
      simp only [rowv, colv, Fin.cons_zero] at hv
      exact ⟨fun e => hxs _ (e ▸ hv.1), fun e => hys _ (e ▸ hv.2)⟩
    have hsub : Finset.univ.image g ⊆ Finset.univ.filter (fun j => meets j σ) := by
      intro j hj
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.1, q.2, (hg q).1, (hg q).2⟩
    exact (five g (fun j => tag j 0) hrect hvalid).trans (Finset.card_le_card hsub)
  have hU : U.card = 6 ^ n := by
    have : offd.card = 6 := by rfl
    simp [U, Fintype.card_piFinset, this]
  have hsum : ∑ σ ∈ U, (Finset.univ.filter (fun j => meets j σ)).card
      = ∑ j, (U.filter (meets j)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h1 : 5 * 6 ^ n ≤ ∑ σ ∈ U, (Finset.univ.filter (fun j => meets j σ)).card := by
    calc 5 * 6 ^ n = ∑ _σ ∈ U, 5 := by simp [hU, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hA
  have h2 : ∑ j, (U.filter (meets j)).card ≤ p * 2 ^ n := by
    calc ∑ j, (U.filter (meets j)).card ≤ ∑ _j : Fin p, 2 ^ n := Finset.sum_le_sum fun j _ => hB j
      _ = p * 2 ^ n := by simp
  have h6 : (6 : Nat) ^ n = 3 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have hpos : 0 < 2 ^ n := by positivity
  have key : 5 * 3 ^ n * 2 ^ n ≤ p * 2 ^ n := by
    rw [mul_assoc, ← h6]
    omega
  exact Nat.le_of_mul_le_mul_right key hpos

end PEqualNP.Outside.L_meta_38163

theorem PEqualNP.Outside.L_meta_38163 : (∀ (n r c : Nat) (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop),
  (∀ x y, ∃ i, rowOK x i ∧ colOK y i) →
  (∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) →
  let Rows := Fin (n+1) → Fin r
  let Cols := Fin (n+1) → Fin c
  let partition := fun (p : Nat) =>
    ∃ (left : Fin p → Rows → Prop) (right : Fin p → Cols → Prop)
      (tag : Fin p → Fin (n+1) → Fin 3),
      (∀ (x : Rows) (y : Cols), ∃! j : Fin p, left j x ∧ right j y) ∧
      ∀ (j : Fin p) (x : Rows) (y : Cols), left j x → right j y →
        ∀ k, rowOK (x k) (tag j k) ∧ colOK (y k) (tag j k)
  partition (5^(n+1)) ∧ ∀ p, partition p → 5 * 3^n ≤ p) := by
  intro n r c rowOK colOK H1 H2 Rows Cols partition
  exact ⟨PEqualNP.Outside.L_meta_38163.upper rowOK colOK n H1 H2,
    fun p ⟨left, right, tag, hpart, hval⟩ =>
      PEqualNP.Outside.L_meta_38163.lower n rowOK colOK H2 p left right tag hpart hval⟩
