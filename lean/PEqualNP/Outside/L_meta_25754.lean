import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25754

def sgn (t : ZMod 2) : ℤ := if t = 0 then 1 else -1

theorem sgn_add (s t : ZMod 2) : sgn (s + t) = sgn s * sgn t := by
  revert s t; decide

theorem sgn_sum {ι : Type} (S : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ S, f i) = ∏ i ∈ S, sgn (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sgn]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

theorem z2_add_eq_zero (s t : ZMod 2) : s + t = 0 ↔ t = s := by
  revert s t; decide

def mix (k d : ℕ) (x : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 :=
  x (i - (d : ZMod k)) + x i + x (i + (d : ZMod k))

theorem mix_add (k d : ℕ) (x y : ZMod k → ZMod 2) : mix k d (x + y) = mix k d x + mix k d y := by
  funext i
  simp only [mix, Pi.add_apply]
  ring

theorem fun_add_eq_zero (k : ℕ) (s t : ZMod k → ZMod 2) : s + t = 0 ↔ t = s := by
  constructor
  · intro h
    funext i
    exact (z2_add_eq_zero (s i) (t i)).mp (by simpa using congrFun h i)
  · intro h
    subst h
    funext i
    exact (z2_add_eq_zero (t i) (t i)).mpr rfl

theorem dot_mix (k d : ℕ) [NeZero k] (u x : ZMod k → ZMod 2) :
    dotProduct u (mix k d x) = dotProduct (mix k d u) x := by
  simp only [dotProduct, mix, mul_add, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ i, u i * x (i - (d : ZMod k)) = ∑ i, u (i + (d : ZMod k)) * x i := by
    rw [← Equiv.sum_comp (Equiv.addRight (d : ZMod k))]
    simp
  have h2 : ∑ i, u i * x (i + (d : ZMod k)) = ∑ i, u (i - (d : ZMod k)) * x i := by
    rw [← Equiv.sum_comp (Equiv.subRight (d : ZMod k))]
    simp
  rw [h1, h2]
  ring

theorem orth (k : ℕ) [NeZero k] (c : ZMod k → ZMod 2) :
    ∑ x : ZMod k → ZMod 2, sgn (dotProduct c x)
      = if c = 0 then (Fintype.card (ZMod k → ZMod 2) : ℤ) else 0 := by
  split_ifs with h
  · subst h
    simp [sgn]
  · obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    have hc1 : c i0 = 1 := by
      revert hi0
      generalize c i0 = t
      revert t
      decide
    have key : ∑ x : ZMod k → ZMod 2, sgn (dotProduct c x)
        = - ∑ x : ZMod k → ZMod 2, sgn (dotProduct c x) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight (Pi.single i0 (1 : ZMod 2)))]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      have h1 : dotProduct c (Pi.single i0 (1 : ZMod 2)) = 1 := by
        rw [dotProduct_single, hc1]; rfl
      simp only [Equiv.coe_addRight, dotProduct_add, sgn_add, h1]
      simp [sgn]
    linarith

theorem fourier (k d : ℕ) [NeZero k] (a : ZMod k → ZMod 2) (F : (ZMod k → ZMod 2) → ℤ)
    [DecidablePred (fun u : ZMod k → ZMod 2 => mix k d u = a)] :
    ∑ x : ZMod k → ZMod 2, sgn (dotProduct a x) * F (mix k d x)
      = ∑ u ∈ Finset.univ.filter (fun u : ZMod k → ZMod 2 => mix k d u = a),
          ∑ y : ZMod k → ZMod 2, sgn (dotProduct u y) * F y := by
  set N : ℤ := (Fintype.card (ZMod k → ZMod 2) : ℤ) with hN
  have hNpos : (0 : ℤ) < N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  have e1 : ∀ u : ZMod k → ZMod 2, (if mix k d u = a then N else 0)
      = ∑ x : ZMod k → ZMod 2, sgn (dotProduct (a + mix k d u) x) := by
    intro u
    rw [orth]
    by_cases h : mix k d u = a
    · rw [if_pos h, if_pos ((fun_add_eq_zero k a (mix k d u)).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((fun_add_eq_zero k a (mix k d u)).mp h'))]
  have e2 : ∀ x y : ZMod k → ZMod 2, ∑ u : ZMod k → ZMod 2, sgn (dotProduct u (mix k d x + y))
      = if y = mix k d x then N else 0 := by
    intro x y
    have := orth k (mix k d x + y)
    simp only [dotProduct_comm (mix k d x + y)] at this
    rw [this]
    by_cases h : y = mix k d x
    · rw [if_pos h, if_pos ((fun_add_eq_zero k (mix k d x) y).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((fun_add_eq_zero k (mix k d x) y).mp h'))]
  have main : N * (∑ u ∈ Finset.univ.filter (fun u : ZMod k → ZMod 2 => mix k d u = a),
          ∑ y : ZMod k → ZMod 2, sgn (dotProduct u y) * F y)
      = N * ∑ x : ZMod k → ZMod 2, sgn (dotProduct a x) * F (mix k d x) := by
    calc N * (∑ u ∈ Finset.univ.filter (fun u : ZMod k → ZMod 2 => mix k d u = a),
          ∑ y : ZMod k → ZMod 2, sgn (dotProduct u y) * F y)
        = ∑ u : ZMod k → ZMod 2, (if mix k d u = a then N else 0)
            * ∑ y : ZMod k → ZMod 2, sgn (dotProduct u y) * F y := by
          rw [Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          split_ifs <;> simp
      _ = ∑ u : ZMod k → ZMod 2, ∑ x : ZMod k → ZMod 2, ∑ y : ZMod k → ZMod 2,
            sgn (dotProduct a x) * F y * sgn (dotProduct u (mix k d x + y)) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [e1 u, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          rw [add_dotProduct, sgn_add, dotProduct_add, sgn_add, dot_mix k d u x]
          ring
      _ = ∑ x : ZMod k → ZMod 2, ∑ y : ZMod k → ZMod 2,
            sgn (dotProduct a x) * F y * (if y = mix k d x then N else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [← Finset.mul_sum, e2 x y]
      _ = N * ∑ x : ZMod k → ZMod 2, sgn (dotProduct a x) * F (mix k d x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_eq_single (mix k d x)]
          · rw [if_pos rfl]; ring
          · intro y _ hy
            rw [if_neg hy]; ring
          · intro h
            exact absurd (Finset.mem_univ _) h
  exact (mul_left_cancel₀ (ne_of_gt hNpos) main).symm

theorem path_sum (G : ℕ → Matrix (ZMod 2) (ZMod 2) ℤ) : ∀ (m : ℕ) (p q : ZMod 2),
    (((List.range m).map G).prod) p q
      = ∑ s : Fin (m + 1) → ZMod 2, (if s 0 = p ∧ s (Fin.last m) = q then
          ∏ j : Fin m, G j (s j.castSucc) (s j.succ) else 0) := by
  intro m
  induction m with
  | zero =>
    intro p q
    rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp]
    simp only [List.range_zero, List.map_nil, List.prod_nil, Matrix.one_apply, Finset.univ_eq_empty,
      Finset.prod_empty]
    revert p q
    decide
  | succ m ih =>
    intro p q
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      Matrix.mul_apply]
    rw [← (Fin.snocEquiv (fun _ : Fin (m + 2) => ZMod 2)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
    have step : ∀ t : ZMod 2, ∑ s' : Fin (m + 1) → ZMod 2,
        (if (Fin.snoc s' t : Fin (m + 2) → ZMod 2) 0 = p ∧
            (Fin.snoc s' t : Fin (m + 2) → ZMod 2) (Fin.last (m + 1)) = q then
          ∏ j : Fin (m + 1), G j ((Fin.snoc s' t : Fin (m + 2) → ZMod 2) j.castSucc)
            ((Fin.snoc s' t : Fin (m + 2) → ZMod 2) j.succ) else 0)
        = if t = q then ∑ r : ZMod 2, (((List.range m).map G).prod) p r * G m r q else 0 := by
      intro t
      have hs : ∀ s' : Fin (m + 1) → ZMod 2,
          (if (Fin.snoc s' t : Fin (m + 2) → ZMod 2) 0 = p ∧
              (Fin.snoc s' t : Fin (m + 2) → ZMod 2) (Fin.last (m + 1)) = q then
            ∏ j : Fin (m + 1), G j ((Fin.snoc s' t : Fin (m + 2) → ZMod 2) j.castSucc)
              ((Fin.snoc s' t : Fin (m + 2) → ZMod 2) j.succ) else 0)
          = if t = q then (if s' 0 = p then
              (∏ j : Fin m, G j (s' j.castSucc) (s' j.succ)) * G m (s' (Fin.last m)) q else 0)
            else 0 := by
        intro s'
        have h0 : (Fin.snoc s' t : Fin (m + 2) → ZMod 2) 0 = s' 0 := by
          rw [show (0 : Fin (m + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
        rw [Fin.prod_univ_castSucc, h0]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, Fin.coe_castSucc, Fin.val_last,
          Fin.succ_castSucc]
        by_cases htq : t = q
        · subst htq
          simp
        · simp [htq]
      rw [Finset.sum_congr rfl (fun s' _ => hs s')]
      by_cases htq : t = q
      · subst htq
        simp only [if_true]
        simp_rw [ih p, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s' _
        rw [Finset.sum_eq_single (s' (Fin.last m))]
        · by_cases hp : s' 0 = p <;> simp [hp]
        · intro r _ hr
          have : ¬ (s' 0 = p ∧ s' (Fin.last m) = r) := fun h => hr h.2.symm
          simp [this]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · simp [htq]
    refine Eq.trans ?_ (Finset.sum_congr rfl (fun t _ => (step t).symm))
    rw [Finset.sum_ite_eq' Finset.univ q, if_pos (Finset.mem_univ q)]

theorem snoc_succ (n : ℕ) (y : Fin (n + 1) → ZMod 2) (j : Fin (n + 1)) :
    (Fin.snoc y (y 0) : Fin (n + 2) → ZMod 2) j.succ = y (j + 1) := by
  induction j using Fin.lastCases with
  | last => rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  | cast i => rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.coeSucc_eq_succ]

theorem trace_cycle (n : ℕ) (G : ℕ → Matrix (ZMod 2) (ZMod 2) ℤ) :
    Matrix.trace (((List.range (n + 1)).map G).prod)
      = ∑ y : Fin (n + 1) → ZMod 2, ∏ i : Fin (n + 1), G i (y i) (y (i + 1)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [path_sum G (n + 1)]
  rw [Finset.sum_comm]
  have h1 : ∀ s : Fin (n + 2) → ZMod 2, ∑ p : ZMod 2,
      (if s 0 = p ∧ s (Fin.last (n + 1)) = p then
        ∏ j : Fin (n + 1), G j (s j.castSucc) (s j.succ) else 0)
      = if s (Fin.last (n + 1)) = s 0 then
        ∏ j : Fin (n + 1), G j (s j.castSucc) (s j.succ) else 0 := by
    intro s
    rw [Finset.sum_eq_single (s 0)]
    · simp
    · intro p _ hp
      have : ¬ (s 0 = p ∧ s (Fin.last (n + 1)) = p) := fun h => hp h.1.symm
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun s _ => h1 s)]
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => ZMod 2)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
  have h0 : ∀ t : ZMod 2, (Fin.snoc y t : Fin (n + 2) → ZMod 2) 0 = y 0 := by
    intro t
    rw [show (0 : Fin (n + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
  have hl : ∀ t : ZMod 2, (Fin.snoc y t : Fin (n + 2) → ZMod 2) (Fin.last (n + 1)) = t :=
    fun t => Fin.snoc_last _ _
  simp only [h0, hl]
  rw [Finset.sum_eq_single (y 0)]
  · simp only [if_true]
    apply Finset.prod_congr rfl
    intro j _
    rw [Fin.snoc_castSucc, snoc_succ]
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ _) h

def nl (k : ℕ) (y : ZMod k → ZMod 2) (j : ZMod k) : ZMod 2 := y j + (1 + y (j + 1)) * y (j + 2)

def transfer (k : ℕ) (u b : ZMod k → ZMod 2) (j : ℕ) : Matrix (ZMod 2) (ZMod 2) ℤ :=
  fun left right =>
    sgn ((u (j : ZMod k) + b (j : ZMod k) + b ((j : ZMod k) - 2)) * left
      + b ((j : ZMod k) - 1) * left * right)

theorem expo (k : ℕ) [NeZero k] (u b y : ZMod k → ZMod 2) :
    dotProduct u y + dotProduct b (nl k y)
      = ∑ i : ZMod k, ((u i + b i + b (i - 2)) * y i + b (i - 1) * y i * y (i + 1)) := by
  have h1 : ∑ j : ZMod k, b j * y (j + 2) = ∑ i : ZMod k, b (i - 2) * y i := by
    rw [← Equiv.sum_comp (Equiv.subRight (2 : ZMod k))]
    simp
  have h2 : ∑ j : ZMod k, b j * (y (j + 1) * y (j + 2))
      = ∑ i : ZMod k, b (i - 1) * (y i * y (i + 1)) := by
    rw [← Equiv.sum_comp (Equiv.subRight (1 : ZMod k))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Equiv.subRight_apply]
    rw [sub_add_cancel, show i - 1 + 2 = i + 1 by ring]
  have hL : dotProduct b (nl k y) = (∑ i : ZMod k, b i * y i)
      + ((∑ j : ZMod k, b j * y (j + 2)) + ∑ j : ZMod k, b j * (y (j + 1) * y (j + 2))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [nl]
    ring
  have hR : ∑ i : ZMod k, ((u i + b i + b (i - 2)) * y i + b (i - 1) * y i * y (i + 1))
      = (∑ i : ZMod k, u i * y i) + ((∑ i : ZMod k, b i * y i)
        + ((∑ i : ZMod k, b (i - 2) * y i) + ∑ i : ZMod k, b (i - 1) * (y i * y (i + 1)))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hL, hR, h1, h2]
  rfl

theorem walsh_trace (n : ℕ) (u b : ZMod (n + 1) → ZMod 2) :
    ∑ y : ZMod (n + 1) → ZMod 2, sgn (dotProduct u y + dotProduct b (nl (n + 1) y))
      = Matrix.trace (((List.range (n + 1)).map (transfer (n + 1) u b)).prod) := by
  rw [trace_cycle]
  apply Finset.sum_congr rfl
  intro y _
  rw [expo, sgn_sum]
  apply Finset.prod_congr rfl
  intro i _
  have hc : ((ZMod.val (i : ZMod (n + 1)) : ℕ) : ZMod (n + 1)) = i := ZMod.natCast_zmod_val i
  have ht : transfer (n + 1) u b (ZMod.val (i : ZMod (n + 1))) (y i) (y (i + 1))
      = sgn ((u i + b i + b (i - 2)) * y i + b (i - 1) * y i * y (i + 1)) := by
    simp only [transfer]
    rw [hc]
  exact ht.symm


theorem fun_self (k : ℕ) (a : ZMod k → ZMod 2) : a + a = 0 := (fun_add_eq_zero k a a).mpr rfl

def rot (k s : ℕ) (w : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 := w (i - (s : ZMod k))

def back (k s : ℕ) (b : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 := b (i + (s : ZMod k))

theorem dot_rot (k s : ℕ) [NeZero k] (a w : ZMod k → ZMod 2) :
    dotProduct a (rot k s w) = dotProduct (back k s a) w := by
  simp only [dotProduct, rot, back]
  rw [← Equiv.sum_comp (Equiv.addRight (s : ZMod k))]
  simp

def kern (k d : ℕ) [NeZero k] (a b : ZMod k → ZMod 2) : ℤ :=
  ∑ u ∈ Finset.univ.filter (fun v : ZMod k → ZMod 2 => mix k d v = a),
    Matrix.trace (List.prod (α := Matrix (ZMod 2) (ZMod 2) ℤ) ((List.range k).map (fun j =>
      let i := (j : ZMod k)
      (fun (l h : ZMod 2) => sgn ((u i+b i+b (i-2))*l+b (i-1)*l*h) : Matrix (ZMod 2) (ZMod 2) ℤ))))

theorem kern_alt (k d : ℕ) [NeZero k] (a b : ZMod k → ZMod 2) :
    kern k d a b = ∑ u ∈ Finset.univ.filter (fun v : ZMod k → ZMod 2 => mix k d v = a),
      Matrix.trace (List.prod ((List.range k).map (transfer k u b))) := by
  unfold kern
  apply Finset.sum_congr rfl
  intro u _
  congr 2
  simp only [List.bind_eq_flatMap, List.pure_def]
  rw [← List.map_eq_flatMap]
  exact List.map_map

theorem kern_eq (k d : ℕ) [NeZero k] (a b : ZMod k → ZMod 2) :
    kern k d a b
      = ∑ x : ZMod k → ZMod 2,
          sgn (dotProduct a x) * sgn (dotProduct b (nl k (mix k d x))) := by
  rw [kern_alt]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  have h2 := fourier (n + 1) d a (fun y => sgn (dotProduct b (nl (n + 1) y)))
  have h3 : ∀ u : ZMod (n + 1) → ZMod 2,
      ∑ y : ZMod (n + 1) → ZMod 2,
          sgn (dotProduct u y) * (fun y => sgn (dotProduct b (nl (n + 1) y))) y
        = Matrix.trace (((List.range (n + 1)).map (transfer (n + 1) u b)).prod) := by
    intro u
    rw [← walsh_trace]
    apply Finset.sum_congr rfl
    intro y _
    rw [sgn_add]
  rw [Finset.sum_congr rfl (fun u _ => h3 u)] at h2
  exact h2.symm

theorem card_V (k : ℕ) [NeZero k] : (Fintype.card (ZMod k → ZMod 2) : ℤ) = 2 ^ k := by
  simp [ZMod.card]

theorem orth2 (k : ℕ) [NeZero k] (c : ZMod k → ZMod 2) :
    ∑ a : ZMod k → ZMod 2, sgn (dotProduct a c) = if c = 0 then (2:ℤ) ^ k else 0 := by
  rw [← card_V k, ← orth k c]
  apply Finset.sum_congr rfl
  intro a _
  rw [dotProduct_comm]

theorem inversion (k : ℕ) [NeZero k] (G : (ZMod k → ZMod 2) → ℤ) (x0 : ZMod k → ZMod 2) :
    ∑ a : ZMod k → ZMod 2,
        (∑ x : ZMod k → ZMod 2, sgn (dotProduct a x) * G x) * sgn (dotProduct a x0)
      = (2:ℤ) ^ k * G x0 := by
  have h : ∀ x : ZMod k → ZMod 2,
      ∑ a : ZMod k → ZMod 2, sgn (dotProduct a x) * G x * sgn (dotProduct a x0)
        = if x = x0 then (2:ℤ) ^ k * G x0 else 0 := by
    intro x
    have h1 : ∑ a : ZMod k → ZMod 2, sgn (dotProduct a x) * G x * sgn (dotProduct a x0)
        = G x * ∑ a : ZMod k → ZMod 2, sgn (dotProduct a (x + x0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [dotProduct_add, sgn_add]
      ring
    rw [h1, orth2]
    by_cases hx : x = x0
    · subst hx
      rw [if_pos (fun_self k x), if_pos rfl]
      ring
    · have hne : ¬ (x + x0 = 0) := fun h0 => hx ((fun_add_eq_zero k x x0).mp h0).symm
      rw [if_neg hne, if_neg hx]
      ring
  calc ∑ a : ZMod k → ZMod 2,
        (∑ x : ZMod k → ZMod 2, sgn (dotProduct a x) * G x) * sgn (dotProduct a x0)
      = ∑ a : ZMod k → ZMod 2, ∑ x : ZMod k → ZMod 2,
          sgn (dotProduct a x) * G x * sgn (dotProduct a x0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
    _ = ∑ x : ZMod k → ZMod 2, ∑ a : ZMod k → ZMod 2,
          sgn (dotProduct a x) * G x * sgn (dotProduct a x0) := Finset.sum_comm
    _ = ∑ x : ZMod k → ZMod 2, (if x = x0 then (2:ℤ) ^ k * G x0 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact h x
    _ = (2:ℤ) ^ k * G x0 := by
        simp

theorem triple {ι κ ω : Type} [Fintype ω] (s : Finset ι) (t : Finset κ)
    (f : ι → ω → ℤ) (g : κ → ω → ℤ) (h : ω → ℤ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ w : ω, h w * (f a w * g b w)
      = ∑ w : ω, h w * ((∑ a ∈ s, f a w) * (∑ b ∈ t, g b w)) := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ w : ω, h w * (f a w * g b w)
      = ∑ a ∈ s, ∑ w : ω, ∑ b ∈ t, h w * (f a w * g b w) := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
    _ = ∑ w : ω, ∑ a ∈ s, ∑ b ∈ t, h w * (f a w * g b w) := Finset.sum_comm
    _ = ∑ w : ω, h w * ((∑ a ∈ s, f a w) * (∑ b ∈ t, g b w)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum, Finset.mul_sum]

def stepO (k r : ℕ) (C : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2)
    (st : (ZMod k → ZMod 2) × (ZMod k → ZMod 2)) (tick : ℕ) :
    (ZMod k → ZMod 2) × (ZMod k → ZMod 2) :=
  (nl k (mix k 1 st.1) + rot k (2 * tick) key + C (tick + 1),
   nl k (mix k 2 st.2) + rot k (3 * (tick + 1) + 1) key + C (r + tick + 1))

def orb (k r : ℕ) (row col : ZMod k → ZMod 2) (C : ℕ → ZMod k → ZMod 2) (m : ℕ)
    (key : ZMod k → ZMod 2) : (ZMod k → ZMod 2) × (ZMod k → ZMod 2) :=
  (List.range m).foldl (stepO k r C key) (rot k 1 key + row, rot k 3 key + col)

def stepH (k r : ℕ) [NeZero k] (C : ℕ → ZMod k → ZMod 2)
    (old : (ZMod k → ZMod 2) → (ZMod k → ZMod 2) → (ZMod k → ZMod 2) → ℤ) (ρ : ℕ)
    (p s t : ZMod k → ZMod 2) : ℤ :=
  sgn (dotProduct p (C (ρ + 1)) + dotProduct s (C (r + ρ + 1))) *
    ∑ a : ZMod k → ZMod 2, ∑ b : ZMod k → ZMod 2, kern k 1 a p * kern k 2 b s *
      old a b (t + back k (2 * ρ) p + back k (3 * (ρ + 1) + 1) s)

def init (k : ℕ) [NeZero k] (row col a b q : ZMod k → ZMod 2) : ℤ :=
  if q + back k 1 a + back k 3 b = 0 then (2:ℤ) ^ k * sgn (dotProduct a row + dotProduct b col) else 0

def HH (k r : ℕ) [NeZero k] (row col : ZMod k → ZMod 2) (C : ℕ → ZMod k → ZMod 2) (m : ℕ) :
    (ZMod k → ZMod 2) → (ZMod k → ZMod 2) → (ZMod k → ZMod 2) → ℤ :=
  (List.range m).foldl (stepH k r C) (init k row col)

theorem base_eq (k : ℕ) [NeZero k] (row col a b q : ZMod k → ZMod 2) :
    init k row col a b q
      = ∑ w : ZMod k → ZMod 2,
          sgn (dotProduct a (rot k 1 w + row) + dotProduct b (rot k 3 w + col)
            + dotProduct q w) := by
  have h : ∀ w : ZMod k → ZMod 2,
      sgn (dotProduct a (rot k 1 w + row) + dotProduct b (rot k 3 w + col)
            + dotProduct q w)
        = sgn (dotProduct a row + dotProduct b col)
          * sgn (dotProduct (q + back k 1 a + back k 3 b) w) := by
    intro w
    rw [← sgn_add]
    congr 1
    simp only [dotProduct_add, add_dotProduct, dot_rot]
    ring
  rw [Finset.sum_congr rfl (fun w _ => h w), ← Finset.mul_sum, orth, card_V]
  unfold init
  split_ifs with h0
  · ring
  · ring

theorem step_lemma (k r : ℕ) [NeZero k] (C : ℕ → ZMod k → ZMod 2)
    (old : (ZMod k → ZMod 2) → (ZMod k → ZMod 2) → (ZMod k → ZMod 2) → ℤ)
    (X Y : (ZMod k → ZMod 2) → (ZMod k → ZMod 2)) (c : ℤ) (ρ : ℕ)
    (hold : ∀ a b q : ZMod k → ZMod 2, old a b q
      = c * ∑ w : ZMod k → ZMod 2,
          sgn (dotProduct a (X w) + dotProduct b (Y w) + dotProduct q w))
    (p s t : ZMod k → ZMod 2) :
    stepH k r C old ρ p s t = c * ((2:ℤ) ^ k) ^ 2 *
      ∑ w : ZMod k → ZMod 2,
        sgn (dotProduct p (nl k (mix k 1 (X w)) + rot k (2 * ρ) w + C (ρ + 1))
          + dotProduct s (nl k (mix k 2 (Y w)) + rot k (3 * (ρ + 1) + 1) w
              + C (r + ρ + 1))
          + dotProduct t w) := by
  have hk1 : ∀ w : ZMod k → ZMod 2,
      ∑ a : ZMod k → ZMod 2, kern k 1 a p * sgn (dotProduct a (X w))
        = (2:ℤ) ^ k * sgn (dotProduct p (nl k (mix k 1 (X w)))) := by
    intro w
    calc ∑ a : ZMod k → ZMod 2, kern k 1 a p * sgn (dotProduct a (X w))
        = ∑ a : ZMod k → ZMod 2,
            (∑ x : ZMod k → ZMod 2,
              sgn (dotProduct a x) * sgn (dotProduct p (nl k (mix k 1 x))))
              * sgn (dotProduct a (X w)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [kern_eq]
      _ = (2:ℤ) ^ k * sgn (dotProduct p (nl k (mix k 1 (X w)))) :=
          inversion k (fun x => sgn (dotProduct p (nl k (mix k 1 x)))) (X w)
  have hk2 : ∀ w : ZMod k → ZMod 2,
      ∑ b : ZMod k → ZMod 2, kern k 2 b s * sgn (dotProduct b (Y w))
        = (2:ℤ) ^ k * sgn (dotProduct s (nl k (mix k 2 (Y w)))) := by
    intro w
    calc ∑ b : ZMod k → ZMod 2, kern k 2 b s * sgn (dotProduct b (Y w))
        = ∑ b : ZMod k → ZMod 2,
            (∑ x : ZMod k → ZMod 2,
              sgn (dotProduct b x) * sgn (dotProduct s (nl k (mix k 2 x))))
              * sgn (dotProduct b (Y w)) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [kern_eq]
      _ = (2:ℤ) ^ k * sgn (dotProduct s (nl k (mix k 2 (Y w)))) :=
          inversion k (fun x => sgn (dotProduct s (nl k (mix k 2 x)))) (Y w)
  have e1 : ∀ a b : ZMod k → ZMod 2,
      kern k 1 a p * kern k 2 b s
          * old a b (t + back k (2 * ρ) p + back k (3 * (ρ + 1) + 1) s)
        = ∑ w : ZMod k → ZMod 2,
            (c * sgn (dotProduct (t + back k (2 * ρ) p + back k (3 * (ρ + 1) + 1) s) w))
              * ((kern k 1 a p * sgn (dotProduct a (X w)))
                * (kern k 2 b s * sgn (dotProduct b (Y w)))) := by
    intro a b
    rw [hold, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [sgn_add, sgn_add]
    ring
  unfold stepH
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => e1 a b)), triple]
  refine (Finset.mul_sum _ _ _).trans ?_
  refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
  apply Finset.sum_congr rfl
  intro w _
  rw [hk1 w, hk2 w]
  have harg : dotProduct p (nl k (mix k 1 (X w)) + rot k (2 * ρ) w + C (ρ + 1))
          + dotProduct s (nl k (mix k 2 (Y w)) + rot k (3 * (ρ + 1) + 1) w
              + C (r + ρ + 1))
          + dotProduct t w
      = (dotProduct p (C (ρ + 1)) + dotProduct s (C (r + ρ + 1)))
        + (dotProduct (t + back k (2 * ρ) p + back k (3 * (ρ + 1) + 1) s) w
          + (dotProduct p (nl k (mix k 1 (X w)))
            + dotProduct s (nl k (mix k 2 (Y w))))) := by
    simp only [dotProduct_add, add_dotProduct, dot_rot]
    ring
  rw [harg]
  simp only [sgn_add]
  ring

theorem HH_eq (k r : ℕ) [NeZero k] (row col : ZMod k → ZMod 2) (C : ℕ → ZMod k → ZMod 2) :
    ∀ (m : ℕ) (a b q : ZMod k → ZMod 2),
      HH k r row col C m a b q = ((2:ℤ) ^ k) ^ (2 * m) *
        ∑ w : ZMod k → ZMod 2,
          sgn (dotProduct a (orb k r row col C m w).1
            + dotProduct b (orb k r row col C m w).2 + dotProduct q w) := by
  intro m
  induction m with
  | zero =>
    intro a b q
    have h0 : HH k r row col C 0 = init k row col := rfl
    rw [h0, base_eq k row col a b q, Nat.mul_zero, pow_zero, one_mul]
    rfl
  | succ m ih =>
    intro a b q
    have hH : HH k r row col C (m + 1)
        = stepH k r C (HH k r row col C m) m := by
      simp only [HH, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hO : ∀ w : ZMod k → ZMod 2, orb k r row col C (m + 1) w
        = stepO k r C w (orb k r row col C m w) m := by
      intro w
      simp only [orb, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hH, step_lemma k r C _ (fun w => (orb k r row col C m w).1)
      (fun w => (orb k r row col C m w).2) _ m ih a b q]
    rw [show ((2:ℤ) ^ k) ^ (2 * (m + 1))
      = ((2:ℤ) ^ k) ^ (2 * m) * ((2:ℤ) ^ k) ^ 2 by ring]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    rw [hO w]
    rfl

theorem sub_orth (k : ℕ) [NeZero k] (S : Finset (ZMod k)) (c : ZMod k → ZMod 2) :
    ∑ a ∈ Finset.univ.filter (fun mask : ZMod k → ZMod 2 => ∀ i : ZMod k, i ∉ S → mask i = 0),
        sgn (dotProduct a c)
      = if (∀ i ∈ S, c i = 0) then (2:ℤ) ^ S.card else 0 := by
  have hs : Finset.univ.filter (fun mask : ZMod k → ZMod 2 => ∀ i : ZMod k, i ∉ S → mask i = 0)
      = Fintype.piFinset (fun i : ZMod k => if i ∈ S then (Finset.univ : Finset (ZMod 2)) else {0}) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · rw [if_pos hi]
        exact Finset.mem_univ _
      · rw [if_neg hi, Finset.mem_singleton]
        exact h i hi
    · intro h i hi
      have h' := h i
      rw [if_neg hi, Finset.mem_singleton] at h'
      exact h'
  rw [hs]
  have h1 : ∀ a : ZMod k → ZMod 2, sgn (dotProduct a c) = ∏ i : ZMod k, sgn (a i * c i) := by
    intro a
    exact sgn_sum Finset.univ (fun i => a i * c i)
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  refine Eq.trans (Finset.prod_univ_sum
    (fun i : ZMod k => if i ∈ S then (Finset.univ : Finset (ZMod 2)) else {0})
    (fun (i : ZMod k) (j : ZMod 2) => sgn (j * c i))).symm ?_
  have h2 : ∀ i : ZMod k,
      ∑ j ∈ (if i ∈ S then (Finset.univ : Finset (ZMod 2)) else {0}), sgn (j * c i)
        = if i ∈ S then (if c i = 0 then (2:ℤ) else 0) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos hi]
      generalize c i = x
      revert x
      decide
    · rw [if_neg hi, if_neg hi, Finset.sum_singleton]
      simp [sgn]
  rw [Finset.prod_congr rfl (fun i _ => h2 i), Finset.prod_ite_mem, Finset.univ_inter]
  split_ifs with h
  · rw [Finset.prod_congr rfl (fun i hi => if_pos (h i hi)), Finset.prod_const]
  · push_neg at h
    obtain ⟨i, hi, hc⟩ := h
    exact Finset.prod_eq_zero hi (if_neg hc)

theorem count (k r : ℕ) [NeZero k] (row col : ZMod k → ZMod 2) (C : ℕ → ZMod k → ZMod 2)
    (S T : Finset (ZMod k)) (y z : ZMod k → ZMod 2) :
    (∑ a ∈ Finset.univ.filter (fun mask : ZMod k → ZMod 2 =>
          ∀ i : ZMod k, i ∉ S → mask i = 0),
      ∑ b ∈ Finset.univ.filter (fun mask : ZMod k → ZMod 2 =>
          ∀ i : ZMod k, i ∉ T → mask i = 0),
        sgn (dotProduct a y + dotProduct b z) * HH k r row col C r a b 0)
      = ((2:ℤ) ^ k) ^ (2 * r) * (2:ℤ) ^ (S.card + T.card)
        * (((Finset.univ.filter (fun w : ZMod k → ZMod 2 =>
            (∀ i ∈ S, (orb k r row col C r w).1 i = y i)
              ∧ (∀ j ∈ T, (orb k r row col C r w).2 j = z j))).card : ℕ) : ℤ) := by
  have e1 : ∀ a b : ZMod k → ZMod 2,
      sgn (dotProduct a y + dotProduct b z) * HH k r row col C r a b 0
        = ∑ w : ZMod k → ZMod 2, ((2:ℤ) ^ k) ^ (2 * r)
            * (sgn (dotProduct a (y + (orb k r row col C r w).1))
              * sgn (dotProduct b (z + (orb k r row col C r w).2))) := by
    intro a b
    rw [HH_eq k r row col C r a b 0, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [zero_dotProduct, add_zero, dotProduct_add, sgn_add]
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => e1 a b)), triple]
  rw [← Finset.sum_boole, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [sub_orth, sub_orth]
  have hPe : (∀ i ∈ S, (y + (orb k r row col C r w).1) i = 0)
      ↔ (∀ i ∈ S, (orb k r row col C r w).1 i = y i) := by
    constructor
    · intro h i hi
      exact (z2_add_eq_zero (y i) ((orb k r row col C r w).1 i)).mp (h i hi)
    · intro h i hi
      exact (z2_add_eq_zero (y i) ((orb k r row col C r w).1 i)).mpr (h i hi)
  have hQe : (∀ j ∈ T, (z + (orb k r row col C r w).2) j = 0)
      ↔ (∀ j ∈ T, (orb k r row col C r w).2 j = z j) := by
    constructor
    · intro h j hj
      exact (z2_add_eq_zero (z j) ((orb k r row col C r w).2 j)).mp (h j hj)
    · intro h j hj
      exact (z2_add_eq_zero (z j) ((orb k r row col C r w).2 j)).mpr (h j hj)
  by_cases hP : ∀ i ∈ S, (orb k r row col C r w).1 i = y i
  · by_cases hQ : ∀ j ∈ T, (orb k r row col C r w).2 j = z j
    · rw [if_pos (hPe.mpr hP), if_pos (hQe.mpr hQ), if_pos ⟨hP, hQ⟩]
      ring
    · have hq1 : ¬ (∀ j ∈ T, (z + (orb k r row col C r w).2) j = 0) := fun h => hQ (hQe.mp h)
      have hq2 : ¬ ((∀ i ∈ S, (orb k r row col C r w).1 i = y i)
          ∧ (∀ j ∈ T, (orb k r row col C r w).2 j = z j)) := fun h => hQ h.2
      rw [if_neg hq1, if_neg hq2]
      ring
  · have hp1 : ¬ (∀ i ∈ S, (y + (orb k r row col C r w).1) i = 0) := fun h => hP (hPe.mp h)
    have hp2 : ¬ ((∀ i ∈ S, (orb k r row col C r w).1 i = y i)
        ∧ (∀ j ∈ T, (orb k r row col C r w).2 j = z j)) := fun h => hP h.1
    rw [if_neg hp1, if_neg hp2]
    ring

end PEqualNP.Outside.L_meta_25754

theorem PEqualNP.Outside.L_meta_25754 : (∀ (k : ℕ) [NeZero k] (r : ℕ),
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let N := (2:ℤ)^k
  let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
  let rot := fun (s : ℕ) (word : V) (i : I) => word (i-(s : I))
  let back := fun (s : ℕ) (b : V) (i : I) => b (i+(s : I))
  let mix := fun (d : ℕ) (x : V) (i : I) => x (i-(d : I)) + x i + x (i+(d : I))
  let nl := fun (y : V) (j : I) => y j + (1+y (j+1))*y (j+2)
  let kernel := fun (d : ℕ) (a b : V) =>
    ∑ u ∈ Finset.univ.filter (fun v : V => mix d v = a),
      Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j =>
        let i := (j : I)
        (fun (l h : B) => sign ((u i+b i+b (i-2))*l+b (i-1)*l*h) : Matrix B B ℤ))))
  ∀ (row col : V) (C : ℕ → V),
    let orbit := fun (key : V) =>
      (List.range r).foldl (fun (st : V × V) tick =>
        (nl (mix 1 st.1) + rot (2*tick) key + C (tick+1),
         nl (mix 2 st.2) + rot (3*(tick+1)+1) key + C (r+tick+1)))
        (rot 1 key + row, rot 3 key + col)
    let initial := fun (a b q : V) =>
      if q + back 1 a + back 3 b = 0 then N*sign (dotProduct a row + dotProduct b col) else 0
    let H := (List.range r).foldl (fun (old : V → V → V → ℤ) roundIndex p s t =>
      sign (dotProduct p (C (roundIndex+1)) + dotProduct s (C (r+roundIndex+1))) *
        ∑ a : V, ∑ b : V, kernel 1 a p * kernel 2 b s *
          old a b (t + back (2*roundIndex) p + back (3*(roundIndex+1)+1) s)) initial
    (∀ a b q : V, H a b q = N^(2*r) *
      ∑ w : V, sign (dotProduct a (orbit w).1 + dotProduct b (orbit w).2 + dotProduct q w)) ∧
    ∀ (S T : Finset I) (y z : V),
      let supported := fun (sites : Finset I) => Finset.univ.filter (fun mask : V =>
        ∀ i : I, i ∉ sites → mask i = 0)
      let passing := Finset.univ.filter (fun w : V =>
        (∀ i ∈ S, (orbit w).1 i = y i) ∧ (∀ j ∈ T, (orbit w).2 j = z j))
      (∑ a ∈ supported S, ∑ b ∈ supported T,
        sign (dotProduct a y + dotProduct b z) * H a b 0) =
        N^(2*r) * (2:ℤ)^(S.card+T.card) * (passing.card : ℤ)) := by
  intro k inst r
  intro I B V N sign rot back mix nl kernel row col C orbit initial H
  constructor
  · intro a b q
    exact PEqualNP.Outside.L_meta_25754.HH_eq k r row col C r a b q
  · intro S T y z supported passing
    exact PEqualNP.Outside.L_meta_25754.count k r row col C S T y z
