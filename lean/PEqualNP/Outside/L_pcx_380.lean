import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_380

open Module

abbrev Wd (n : ℕ) := Fin n → ZMod 2
abbrev Du (n : ℕ) := (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2
abbrev Hs (w : ℕ) := List (Fin w → ZMod 2)
abbrev Ask (n w : ℕ) := Hs w → Fin w → Du n × ZMod 2 × ZMod 2

theorem foldl_range_iter {α : Type} (f : α → α) (a : α) (s : ℕ) :
    (List.range s).foldl (fun h (_ : ℕ) => f h) a = f^[s] a := by
  induction s with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ_apply']; rfl

theorem z2a : ∀ p q r c d : ZMod 2, (p + c * 0 + d = q + r + c * 1 + d ↔ q + p = r + c) := by decide
theorem z2b : ∀ p q c l d : ZMod 2, (p + c * l + d = q + c * l + d ↔ p - q = 0) := by decide
theorem z2c : ∀ p q r : ZMod 2, (p = r → (q = r ↔ q - p = 0)) := by decide

section hist
variable {n w : ℕ} (ask : Ask n w)

def ans (l : ZMod 2) (x : Wd n) (h : Hs w) : Fin w → ZMod 2 :=
  fun i : Fin w => (ask h i).1 x + (ask h i).2.1 * l + (ask h i).2.2

def stp (l : ZMod 2) (x : Wd n) (h : Hs w) : Hs w := h ++ [ans ask l x h]

def HH (l : ZMod 2) (x : Wd n) (j : ℕ) : Hs w := (stp ask l x)^[j] []

theorem HH_zero (l : ZMod 2) (x : Wd n) : HH ask l x 0 = [] := rfl

theorem HH_succ (l : ZMod 2) (x : Wd n) (j : ℕ) :
    HH ask l x (j+1) = HH ask l x j ++ [ans ask l x (HH ask l x j)] := by
  unfold HH
  rw [Function.iterate_succ_apply']
  rfl

theorem HH_length (l : ZMod 2) (x : Wd n) (j : ℕ) : (HH ask l x j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [HH_succ, List.length_append, ih]; rfl

theorem HH_succ_eq (l l' : ZMod 2) (x y : Wd n) (j : ℕ) :
    HH ask l x (j+1) = HH ask l' y (j+1) ↔
      HH ask l x j = HH ask l' y j ∧ ans ask l x (HH ask l x j) = ans ask l' y (HH ask l' y j) := by
  rw [HH_succ, HH_succ]
  constructor
  · intro h
    have := List.append_inj h (by rw [HH_length, HH_length])
    exact ⟨this.1, by simpa using this.2⟩
  · rintro ⟨h1, h2⟩
    rw [h2, h1]

theorem HH_le (l l' : ZMod 2) (x y : Wd n) (j : ℕ) (h : HH ask l x j = HH ask l' y j) :
    ∀ t ≤ j, HH ask l x t = HH ask l' y t := by
  induction j with
  | zero => intro t ht; obtain rfl : t = 0 := by omega
            exact h
  | succ j ih =>
    intro t ht
    rcases Nat.lt_or_ge t (j+1) with h1 | h1
    · exact ih ((HH_succ_eq ask l l' x y j).mp h).1 t (by omega)
    · obtain rfl : t = j+1 := by omega
      exact h

def ev (v : Wd n) : Submodule (ZMod 2) (Du n) :=
  LinearMap.ker (Module.Dual.eval (ZMod 2) (Wd n) v)

theorem mem_ev (v : Wd n) (a : Du n) : a ∈ ev v ↔ a v = 0 := by
  unfold ev
  rw [LinearMap.mem_ker, Module.Dual.eval_apply]

def Aj (x : Wd n) : ℕ → Submodule (ZMod 2) (Du n)
  | 0 => ⊥
  | j+1 => Aj x j ⊔ Submodule.span (ZMod 2) (Set.range (fun i : Fin w => (ask (HH ask 0 x j) i).1))

theorem Aj_succ (x : Wd n) (j : ℕ) : Aj ask x (j+1) =
    Aj ask x j ⊔ Submodule.span (ZMod 2) (Set.range (fun i : Fin w => (ask (HH ask 0 x j) i).1)) := rfl

theorem Aj_mono (x : Wd n) (j : ℕ) : Aj ask x j ≤ Aj ask x (j+1) := le_sup_left

theorem Aj_succ_le (x : Wd n) (j : ℕ) (S : Submodule (ZMod 2) (Du n)) :
    Aj ask x (j+1) ≤ S ↔ Aj ask x j ≤ S ∧ ∀ i : Fin w, (ask (HH ask 0 x j) i).1 ∈ S := by
  rw [Aj_succ, sup_le_iff, Submodule.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => h2 ⟨i, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact h2 i

theorem Aj_congr (x y : Wd n) (j : ℕ) (h : HH ask 0 y j = HH ask 0 x j) :
    ∀ t ≤ j + 1, Aj ask y t = Aj ask x t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [Aj_succ, Aj_succ, ih (by omega), HH_le ask 0 0 y x j h t (by omega)]

theorem node0 (x y : Wd n) : ∀ j : ℕ, HH ask 0 y j = HH ask 0 x j ↔ Aj ask x j ≤ ev (y - x) := by
  intro j
  induction j with
  | zero => simp [HH_zero, Aj]
  | succ j ih =>
    rw [HH_succ_eq, Aj_succ_le]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨ih.mp h1, fun i => ?_⟩
      have h3 := congrFun h2 i
      rw [h1] at h3
      unfold ans at h3
      rw [mem_ev, map_sub]
      exact (z2b _ _ _ _ _).mp h3
    · rintro ⟨h1, h2⟩
      have h3 := ih.mpr h1
      refine ⟨h3, ?_⟩
      funext i
      rw [h3]
      unfold ans
      have h4 := h2 i
      rw [mem_ev, map_sub] at h4
      exact (z2b _ _ _ _ _).mpr h4

end hist

section mat
variable {n w : ℕ} (ask : Ask n w) (T : Wd n ≃ₗ[ZMod 2] Wd n) (b : Wd n)

def Mt (j : ℕ) (x : Wd n) : Prop := HH ask 0 x j = HH ask 1 (T x + b) j

def Nn (v : Wd n) : Wd n := T v + v

theorem Nn_sub (x y : Wd n) : Nn T (y - x) = (T y + y) - (T x + x) := by
  unfold Nn
  rw [map_sub]
  abel

theorem Mt_zero (x : Wd n) : Mt ask T b 0 x := rfl

theorem Mt_succ (j : ℕ) (y : Wd n) : Mt ask T b (j+1) y ↔
    Mt ask T b j y ∧ ∀ i : Fin w, (ask (HH ask 0 y j) i).1 (T y + y) =
      (ask (HH ask 0 y j) i).1 b + (ask (HH ask 0 y j) i).2.1 := by
  unfold Mt
  rw [HH_succ_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    have h3 := congrFun h2 i
    rw [← h1] at h3
    unfold ans at h3
    simp only [map_add] at h3 ⊢
    exact (z2a _ _ _ _ _).mp h3
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    funext i
    rw [← h1]
    unfold ans
    have h3 := h2 i
    simp only [map_add] at h3 ⊢
    exact (z2a _ _ _ _ _).mpr h3

theorem step_core (j : ℕ) (x y : Wd n) (hH : HH ask 0 y j = HH ask 0 x j) (hx : Mt ask T b (j+1) x)
    (hlev : Mt ask T b j y ↔ Aj ask x j ≤ ev (Nn T (y - x))) :
    Mt ask T b (j+1) y ↔ Aj ask x (j+1) ≤ ev (Nn T (y - x)) := by
  rw [Mt_succ, Aj_succ_le, hlev, hH]
  have hx2 := ((Mt_succ ask T b j x).mp hx).2
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  rw [mem_ev, Nn_sub, map_sub]
  exact z2c _ _ _ (hx2 i)

theorem lvl : ∀ (j : ℕ) (x y : Wd n), HH ask 0 y j = HH ask 0 x j → Mt ask T b j x →
    (Mt ask T b j y ↔ Aj ask x j ≤ ev (Nn T (y - x))) := by
  intro j
  induction j with
  | zero =>
    intro x y _ _
    simp [Mt_zero, Aj]
  | succ j ih =>
    intro x y hH hx
    have h1 := ((HH_succ_eq ask 0 0 y x j).mp hH).1
    exact step_core ask T b j x y h1 hx (ih x y h1 ((Mt_succ ask T b j x).mp hx).1)

theorem nxt (j : ℕ) (x y : Wd n) (hH : HH ask 0 y j = HH ask 0 x j) (hx : Mt ask T b (j+1) x) :
    Mt ask T b (j+1) y ↔ Aj ask x (j+1) ≤ ev (Nn T (y - x)) :=
  step_core ask T b j x y hH hx (lvl ask T b j x y hH ((Mt_succ ask T b j x).mp hx).1)

end mat

section cnt
variable {n w : ℕ} (ask : Ask n w) (T : Wd n ≃ₗ[ZMod 2] Wd n) (b : Wd n)

def shift (S : Submodule (ZMod 2) (Du n)) : Submodule (ZMod 2) (Du n) :=
  Submodule.span (ZMod 2) (Set.image (fun a : Du n => a.comp T.toLinearMap + a) (S : Set (Du n)))

theorem shift_mono {S S' : Submodule (ZMod 2) (Du n)} (h : S ≤ S') : shift T S ≤ shift T S' :=
  Submodule.span_mono (Set.image_mono h)

theorem shift_le_ev (S : Submodule (ZMod 2) (Du n)) (v : Wd n) : shift T S ≤ ev v ↔ S ≤ ev (Nn T v) := by
  unfold shift
  rw [Submodule.span_le]
  constructor
  · intro h a ha
    have h1 : (a.comp T.toLinearMap + a) ∈ ev v := h ⟨a, ha, rfl⟩
    rw [mem_ev] at h1 ⊢
    unfold Nn
    rw [map_add]
    simpa using h1
  · rintro h _ ⟨a, ha, rfl⟩
    have h1 : a ∈ ev (Nn T v) := h ha
    rw [mem_ev] at h1
    unfold Nn at h1
    rw [map_add] at h1
    show (a.comp T.toLinearMap + a) ∈ ev v
    rw [mem_ev]
    simpa using h1

theorem mem_coann (S : Submodule (ZMod 2) (Du n)) (v : Wd n) : v ∈ S.dualCoannihilator ↔ S ≤ ev v := by
  rw [Submodule.mem_dualCoannihilator]
  exact ⟨fun h a ha => (mem_ev v a).mpr (h a ha), fun h a ha => (mem_ev v a).mp (h ha)⟩

theorem card_coset (W : Submodule (ZMod 2) (Wd n)) (x : Wd n) [DecidablePred fun y : Wd n => y - x ∈ W] :
    (Finset.univ.filter (fun y : Wd n => y - x ∈ W)).card = 2 ^ finrank (ZMod 2) W := by
  classical
  have h1 : (Finset.univ.filter (fun y : Wd n => y - x ∈ W)).card = Fintype.card W := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr ⟨fun y => ⟨y.1 - x, y.2⟩, fun v => ⟨v.1 + x, by simp⟩,
      fun y => by simp, fun v => by simp⟩
  rw [h1, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]

theorem fr_coann (S : Submodule (ZMod 2) (Du n)) :
    finrank (ZMod 2) S + finrank (ZMod 2) S.dualCoannihilator = n := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (K := ZMod 2) (V := Wd n) S
  rw [h]
  simp

theorem nodeS (j : ℕ) (x y : Wd n) (hx : Mt ask T b j x) :
    (HH ask 0 y j = HH ask 0 x j ∧ Mt ask T b j y) ↔
      y - x ∈ (Aj ask x j ⊔ shift T (Aj ask x j)).dualCoannihilator := by
  rw [mem_coann, sup_le_iff, shift_le_ev, ← node0]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (lvl ask T b j x y h1 hx).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (lvl ask T b j x y h1 hx).mpr h2⟩

theorem nodeS' (j : ℕ) (x y : Wd n) (hx : Mt ask T b (j+1) x) :
    (HH ask 0 y j = HH ask 0 x j ∧ Mt ask T b (j+1) y) ↔
      y - x ∈ ((Aj ask x j ⊔ shift T (Aj ask x j)) ⊔ shift T (Aj ask x (j+1))).dualCoannihilator := by
  have e : (Aj ask x j ⊔ shift T (Aj ask x j)) ⊔ shift T (Aj ask x (j+1)) =
      Aj ask x j ⊔ shift T (Aj ask x (j+1)) := by
    rw [sup_assoc, sup_eq_right.mpr (shift_mono T (Aj_mono ask x j))]
  rw [e, mem_coann, sup_le_iff, shift_le_ev, ← node0]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (nxt ask T b j x y h1 hx).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (nxt ask T b j x y h1 hx).mpr h2⟩

noncomputable def cst (x : Wd n) (j : ℕ) : ℕ :=
  finrank (ZMod 2) ((Aj ask x j ⊔ shift T (Aj ask x j)) ⊔ shift T (Aj ask x (j+1)) : Submodule (ZMod 2) (Du n))
    - finrank (ZMod 2) (Aj ask x j ⊔ shift T (Aj ask x j) : Submodule (ZMod 2) (Du n))

noncomputable def Cc (x : Wd n) (j : ℕ) : ℕ := ∑ t ∈ Finset.range j, cst ask T x t

open Classical in
noncomputable def MS (j : ℕ) : Finset (Wd n) := Finset.univ.filter (fun x => Mt ask T b j x)

theorem mem_MS (j : ℕ) (x : Wd n) : x ∈ MS ask T b j ↔ Mt ask T b j x := by
  unfold MS
  simp

theorem MS_sub (j : ℕ) : MS ask T b (j+1) ⊆ MS ask T b j := by
  intro x hx
  rw [mem_MS] at hx ⊢
  exact ((Mt_succ ask T b j x).mp hx).1

theorem cst_congr (x y : Wd n) (j : ℕ) (h : HH ask 0 y j = HH ask 0 x j) :
    ∀ t ≤ j, cst ask T y t = cst ask T x t := by
  intro t ht
  unfold cst
  rw [Aj_congr ask x y j h t (by omega), Aj_congr ask x y j h (t+1) (by omega)]

theorem Cc_congr (x y : Wd n) (j : ℕ) (h : HH ask 0 y j = HH ask 0 x j) :
    ∀ t ≤ j + 1, Cc ask T y t = Cc ask T x t := by
  intro t ht
  unfold Cc
  apply Finset.sum_congr rfl
  intro u hu
  exact cst_congr ask T x y j h u (by have := Finset.mem_range.mp hu; omega)

theorem ratio (j : ℕ) (x : Wd n) (hx : Mt ask T b (j+1) x) :
    ((MS ask T b (j+1)).filter (fun y => HH ask 0 y j = HH ask 0 x j)).card * 2 ^ cst ask T x j =
      ((MS ask T b j).filter (fun y => HH ask 0 y j = HH ask 0 x j)).card := by
  classical
  have hx0 := ((Mt_succ ask T b j x).mp hx).1
  have e1 : (MS ask T b (j+1)).filter (fun y => HH ask 0 y j = HH ask 0 x j) =
      Finset.univ.filter (fun y : Wd n => y - x ∈
        ((Aj ask x j ⊔ shift T (Aj ask x j)) ⊔ shift T (Aj ask x (j+1))).dualCoannihilator) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_filter, mem_MS, ← nodeS' ask T b j x y hx]
    simp [and_comm]
  have e2 : (MS ask T b j).filter (fun y => HH ask 0 y j = HH ask 0 x j) =
      Finset.univ.filter (fun y : Wd n => y - x ∈
        (Aj ask x j ⊔ shift T (Aj ask x j)).dualCoannihilator) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_filter, mem_MS, ← nodeS ask T b j x y hx0]
    simp [and_comm]
  rw [e1, e2, card_coset, card_coset, ← pow_add]
  congr 1
  have h1 := fr_coann (Aj ask x j ⊔ shift T (Aj ask x j))
  have h2 := fr_coann ((Aj ask x j ⊔ shift T (Aj ask x j)) ⊔ shift T (Aj ask x (j+1)))
  have h3 : finrank (ZMod 2) (Aj ask x j ⊔ shift T (Aj ask x j) : Submodule (ZMod 2) (Du n)) ≤
      finrank (ZMod 2) ((Aj ask x j ⊔ shift T (Aj ask x j)) ⊔ shift T (Aj ask x (j+1)) : Submodule (ZMod 2) (Du n)) :=
    Submodule.finrank_mono le_sup_left
  unfold cst
  have key : ∀ a b c d : ℕ, b + d = n → a + c = n → b ≤ a → c + (a - b) = d := by omega
  exact key _ _ _ _ h1 h2 h3

noncomputable def Phi (j : ℕ) : ℕ := ∑ x ∈ MS ask T b j, 2 ^ Cc ask T x j

theorem fiber_eq (j : ℕ) (β : Hs w) (hne : ∃ x ∈ MS ask T b (j+1), HH ask 0 x j = β) :
    ∑ x ∈ (MS ask T b (j+1)).filter (fun x => HH ask 0 x j = β), 2 ^ Cc ask T x (j+1) =
      ∑ y ∈ (MS ask T b j).filter (fun y => HH ask 0 y j = β), 2 ^ Cc ask T y j := by
  obtain ⟨x0, hx0, rfl⟩ := hne
  have hL : ∀ x ∈ (MS ask T b (j+1)).filter (fun x => HH ask 0 x j = HH ask 0 x0 j),
      2 ^ Cc ask T x (j+1) = 2 ^ Cc ask T x0 j * 2 ^ cst ask T x0 j := by
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    rw [Cc_congr ask T x0 x j h (j+1) (le_refl _), ← pow_add]
    congr 1
    unfold Cc
    rw [Finset.sum_range_succ]
  have hR : ∀ y ∈ (MS ask T b j).filter (fun y => HH ask 0 y j = HH ask 0 x0 j),
      2 ^ Cc ask T y j = 2 ^ Cc ask T x0 j := by
    intro y hy
    have h := (Finset.mem_filter.mp hy).2
    rw [Cc_congr ask T x0 y j h j (by omega)]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, ← ratio ask T b j x0 ((mem_MS ask T b (j+1) x0).mp hx0)]
  ring

theorem Phi_le (j : ℕ) : Phi ask T b (j+1) ≤ Phi ask T b j := by
  unfold Phi
  have m1 : ∀ x ∈ MS ask T b (j+1), HH ask 0 x j ∈ (MS ask T b j).image (fun x => HH ask 0 x j) :=
    fun x hx => Finset.mem_image_of_mem _ (MS_sub ask T b j hx)
  have m2 : ∀ x ∈ MS ask T b j, HH ask 0 x j ∈ (MS ask T b j).image (fun x => HH ask 0 x j) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to m1, ← Finset.sum_fiberwise_of_maps_to m2]
  apply Finset.sum_le_sum
  intro β _
  by_cases hne : ∃ x ∈ MS ask T b (j+1), HH ask 0 x j = β
  · exact le_of_eq (fiber_eq ask T b j β hne)
  · rw [Finset.sum_eq_zero]
    · exact Nat.zero_le _
    · intro x hx
      exfalso
      exact hne ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

theorem Phi_eq (j : ℕ) (hlive : ∀ x ∈ MS ask T b j, ∃ y ∈ MS ask T b (j+1), HH ask 0 y j = HH ask 0 x j) :
    Phi ask T b (j+1) = Phi ask T b j := by
  unfold Phi
  have m1 : ∀ x ∈ MS ask T b (j+1), HH ask 0 x j ∈ (MS ask T b j).image (fun x => HH ask 0 x j) :=
    fun x hx => Finset.mem_image_of_mem _ (MS_sub ask T b j hx)
  have m2 : ∀ x ∈ MS ask T b j, HH ask 0 x j ∈ (MS ask T b j).image (fun x => HH ask 0 x j) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to m1, ← Finset.sum_fiberwise_of_maps_to m2]
  apply Finset.sum_congr rfl
  intro β hβ
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hβ
  exact fiber_eq ask T b j _ (hlive x hx)

theorem Phi_zero : Phi ask T b 0 = 2 ^ n := by
  unfold Phi
  have h1 : MS ask T b 0 = Finset.univ := by
    ext x
    simp [mem_MS, Mt_zero]
  rw [h1]
  simp [Cc, ZMod.card]

theorem Phi_bound (j : ℕ) : Phi ask T b j ≤ 2 ^ n := by
  induction j with
  | zero => exact le_of_eq (Phi_zero ask T b)
  | succ j ih => exact le_trans (Phi_le ask T b j) ih

end cnt

section fwd
variable {n w : ℕ} (ask : Ask n w) (T : Wd n ≃ₗ[ZMod 2] Wd n) (b : Wd n)

theorem top_of_inj (s : ℕ) (hinj : Function.Injective (fun x : Wd n => HH ask 0 x s)) (x : Wd n) :
    Aj ask x s = ⊤ := by
  have h0 : (Aj ask x s).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [mem_coann] at hv
    have h1 : HH ask 0 (x + v) s = HH ask 0 x s := by
      rw [node0]
      simpa using hv
    have h2 : x + v = x := hinj h1
    have h3 : v = 0 := by simpa using h2
    rw [h3]
    exact zero_mem _
  apply Submodule.eq_top_of_finrank_eq
  have h3 := fr_coann (Aj ask x s)
  rw [h0, finrank_bot, add_zero] at h3
  rw [h3, Subspace.dual_finrank_eq]
  simp

theorem fwd (s K : ℕ) (hinj : Function.Injective (fun x : Wd n => HH ask 0 x s))
    (hK : K ≤ (MS ask T b s).card) :
    ∃ flag : ℕ → Submodule (ZMod 2) (Du n),
      flag 0 = ⊥ ∧ flag s = ⊤ ∧ (∀ j < s, flag j ≤ flag (j+1)) ∧
      K * 2 ^ ((Finset.range s).sum (fun j =>
        let base := flag j ⊔ shift T (flag j)
        finrank (ZMod 2) (base ⊔ shift T (flag (j+1)) : Submodule (ZMod 2) (Du n)) - finrank (ZMod 2) base)) ≤ 2 ^ n := by
  by_cases hne : (MS ask T b s).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image (MS ask T b s) (fun x => Cc ask T x s) hne
    refine ⟨fun j => Aj ask x0 j, rfl, top_of_inj ask s hinj x0, fun j _ => Aj_mono ask x0 j, ?_⟩
    show K * 2 ^ Cc ask T x0 s ≤ 2 ^ n
    calc K * 2 ^ Cc ask T x0 s ≤ (MS ask T b s).card * 2 ^ Cc ask T x0 s := Nat.mul_le_mul_right _ hK
      _ = ∑ _x ∈ MS ask T b s, 2 ^ Cc ask T x0 s := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ MS ask T b s, 2 ^ Cc ask T x s :=
          Finset.sum_le_sum (fun x hx => Nat.pow_le_pow_right (by norm_num) (hmin x hx))
      _ ≤ 2 ^ n := Phi_bound ask T b s
  · have hK0 : K = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne] at hK
      simpa using hK
    refine ⟨fun j => Aj ask 0 j, rfl, top_of_inj ask s hinj 0, fun j _ => Aj_mono ask 0 j, ?_⟩
    rw [hK0]
    simp

end fwd

section bwd
variable {n : ℕ} (T : Wd n ≃ₗ[ZMod 2] Wd n) (b : Wd n) (flag : ℕ → Submodule (ZMod 2) (Du n))

theorem z2d : ∀ p r : ZMod 2, p = r + (p + r) := by decide
theorem z2e : ∀ p q c l d : ZMod 2, p = q → p + c * l + d = q + c * l + d := by decide

theorem fin_Du (n : ℕ) : Finite (Du n) :=
  Finite.of_injective (fun f : Du n => (f : Wd n → ZMod 2)) DFunLike.coe_injective

noncomputable def enu (n : ℕ) : Fin (Nat.card (Du n)) → Du n := (@Finite.equivFin (Du n) (fin_Du n)).symm

theorem enu_surj (n : ℕ) : Function.Surjective (enu n) := Equiv.surjective _

open Classical in
noncomputable def qa (j : ℕ) (i : Fin (Nat.card (Du n))) : Du n :=
  if enu n i ∈ flag (j+1) then enu n i else 0

theorem qa_mem (j : ℕ) (i : Fin (Nat.card (Du n))) : qa flag j i ∈ flag (j+1) := by
  unfold qa
  split_ifs with h
  · exact h
  · exact zero_mem _

theorem qa_hit (j : ℕ) (a : Du n) (ha : a ∈ flag (j+1)) : ∃ i, qa flag j i = a := by
  obtain ⟨i, rfl⟩ := enu_surj n a
  refine ⟨i, ?_⟩
  unfold qa
  simp [ha]

theorem qa_span (j : ℕ) : Submodule.span (ZMod 2) (Set.range (qa flag j)) = flag (j+1) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact qa_mem flag j i
  · intro a ha
    obtain ⟨i, rfl⟩ := qa_hit flag j a ha
    exact Submodule.subset_span ⟨i, rfl⟩

def Wp (j : ℕ) : Submodule (ZMod 2) (Wd n) :=
  ((flag j ⊔ shift T (flag j)) ⊔ shift T (flag (j+1))).dualCoannihilator

noncomputable def rep : List (Fin (Nat.card (Du n)) → ZMod 2) → Wd n
  | [] => 0
  | r :: t => Classical.epsilon (fun y : Wd n =>
      y - rep t ∈ Wp T flag t.length ∧ ∀ i, qa flag t.length i y = r i)

noncomputable def askc : Ask n (Nat.card (Du n)) := fun h i =>
  (qa flag h.length i,
    qa flag h.length i (T (rep T flag h.reverse) + rep T flag h.reverse) + qa flag h.length i b, 0)

theorem askc_fst (h : Hs (Nat.card (Du n))) (i : Fin (Nat.card (Du n))) :
    (askc T b flag h i).1 = qa flag h.length i := rfl

theorem Aj_flag (s : ℕ) (h0 : flag 0 = ⊥) (hm : ∀ j < s, flag j ≤ flag (j+1)) (x : Wd n) :
    ∀ j ≤ s, Aj (askc T b flag) x j = flag j := by
  intro j
  induction j with
  | zero => intro _; rw [h0]; rfl
  | succ j ih =>
    intro hj
    rw [Aj_succ, ih (by omega)]
    have e : (fun i : Fin (Nat.card (Du n)) => (askc T b flag (HH (askc T b flag) 0 x j) i).1) = qa flag j := by
      funext i
      rw [askc_fst, HH_length]
    rw [e, qa_span]
    exact sup_eq_right.mpr (hm j (by omega))

theorem inj_c (s : ℕ) (h0 : flag 0 = ⊥) (hs : flag s = ⊤) (l : ZMod 2) :
    Function.Injective (fun x : Wd n => HH (askc T b flag) l x s) := by
  intro x y hxy
  have key : ∀ a : Du n, a x = a y := by
    cases s with
    | zero =>
      intro a
      have ha : a ∈ flag 0 := by rw [hs]; exact Submodule.mem_top
      rw [h0, Submodule.mem_bot] at ha
      rw [ha]
      rfl
    | succ s' =>
      intro a
      have hxy' : HH (askc T b flag) l x (s'+1) = HH (askc T b flag) l y (s'+1) := hxy
      rw [HH_succ_eq] at hxy'
      obtain ⟨h1, h2⟩ := hxy'
      obtain ⟨i, hi⟩ := qa_hit flag s' a (by rw [hs]; exact Submodule.mem_top)
      have h3 := congrFun h2 i
      rw [← h1] at h3
      unfold ans at h3
      rw [askc_fst, HH_length, hi] at h3
      have h4 := (z2b _ _ _ _ _).mp h3
      exact sub_eq_zero.mp h4
  funext k
  exact key (LinearMap.proj k)

theorem surv (j : ℕ) (h : Hs (Nat.card (Du n)))
    (h1 : HH (askc T b flag) 0 (rep T flag h.reverse) j = h)
    (h2 : Mt (askc T b flag) T b j (rep T flag h.reverse)) :
    Mt (askc T b flag) T b (j+1) (rep T flag h.reverse) := by
  rw [Mt_succ]
  refine ⟨h2, fun i => ?_⟩
  rw [h1]
  exact z2d _ _

theorem inv (s : ℕ) (h0 : flag 0 = ⊥) (hm : ∀ j < s, flag j ≤ flag (j+1)) :
    ∀ j ≤ s, ∀ x : Wd n, Mt (askc T b flag) T b j x →
      (HH (askc T b flag) 0 (rep T flag (HH (askc T b flag) 0 x j).reverse) j = HH (askc T b flag) 0 x j ∧
        Mt (askc T b flag) T b j (rep T flag (HH (askc T b flag) 0 x j).reverse)) := by
  intro j
  induction j with
  | zero =>
    intro _ x _
    exact ⟨rfl, Mt_zero _ T b _⟩
  | succ j ih =>
    intro hj x hx
    have hxj := ((Mt_succ (askc T b flag) T b j x).mp hx).1
    obtain ⟨i1, i2⟩ := ih (by omega) x hxj
    have i3 := surv T b flag j _ i1 i2
    have e1 : Aj (askc T b flag) (rep T flag (HH (askc T b flag) 0 x j).reverse) j = flag j :=
      Aj_flag T b flag s h0 hm _ j (by omega)
    have e2 : Aj (askc T b flag) (rep T flag (HH (askc T b flag) 0 x j).reverse) (j+1) = flag (j+1) :=
      Aj_flag T b flag s h0 hm _ (j+1) hj
    have nd := fun y => nodeS' (askc T b flag) T b j (rep T flag (HH (askc T b flag) 0 x j).reverse) y i3
    rw [e1, e2] at nd
    have hrev : (HH (askc T b flag) 0 x (j+1)).reverse =
        ans (askc T b flag) 0 x (HH (askc T b flag) 0 x j) :: (HH (askc T b flag) 0 x j).reverse := by
      rw [HH_succ, List.reverse_append]
      rfl
    have hlen : (HH (askc T b flag) 0 x j).reverse.length = j := by
      rw [List.length_reverse, HH_length]
    have hans : ∀ (z : Wd n) (i : Fin (Nat.card (Du n))),
        ans (askc T b flag) 0 z (HH (askc T b flag) 0 x j) i = qa flag j i z := by
      intro z i
      unfold ans
      rw [askc_fst, HH_length]
      simp [askc]
    have hP : x - rep T flag (HH (askc T b flag) 0 x j).reverse ∈ Wp T flag j ∧
        ∀ i, qa flag j i x = ans (askc T b flag) 0 x (HH (askc T b flag) 0 x j) i :=
      ⟨(nd x).mp ⟨i1.symm, hx⟩, fun i => (hans x i).symm⟩
    have hspec := Classical.epsilon_spec (p := fun y : Wd n =>
      y - rep T flag (HH (askc T b flag) 0 x j).reverse ∈ Wp T flag j ∧
        ∀ i, qa flag j i y = ans (askc T b flag) 0 x (HH (askc T b flag) 0 x j) i) ⟨x, hP⟩
    have hrep : rep T flag (HH (askc T b flag) 0 x (j+1)).reverse =
        Classical.epsilon (fun y : Wd n =>
          y - rep T flag (HH (askc T b flag) 0 x j).reverse ∈ Wp T flag j ∧
            ∀ i, qa flag j i y = ans (askc T b flag) 0 x (HH (askc T b flag) 0 x j) i) := by
      rw [hrev]
      show Classical.epsilon _ = _
      rw [hlen]
    rw [hrep]
    obtain ⟨q1, q2⟩ := hspec
    obtain ⟨r1, r2⟩ := (nd _).mpr q1
    refine ⟨?_, r2⟩
    rw [HH_succ_eq]
    refine ⟨r1.trans i1, ?_⟩
    rw [r1.trans i1]
    funext i
    rw [hans, hans, q2 i, hans]

theorem live (s : ℕ) (h0 : flag 0 = ⊥) (hm : ∀ j < s, flag j ≤ flag (j+1)) (j : ℕ) (hj : j < s) :
    ∀ x ∈ MS (askc T b flag) T b j, ∃ y ∈ MS (askc T b flag) T b (j+1),
      HH (askc T b flag) 0 y j = HH (askc T b flag) 0 x j := by
  intro x hx
  rw [mem_MS] at hx
  obtain ⟨i1, i2⟩ := inv T b flag s h0 hm j (by omega) x hx
  exact ⟨_, (mem_MS _ T b (j+1) _).mpr (surv T b flag j _ i1 i2), i1⟩

theorem Phi_c (s : ℕ) (h0 : flag 0 = ⊥) (hm : ∀ j < s, flag j ≤ flag (j+1)) :
    ∀ j ≤ s, Phi (askc T b flag) T b j = 2 ^ n := by
  intro j
  induction j with
  | zero => intro _; exact Phi_zero _ T b
  | succ j ih =>
    intro hj
    rw [Phi_eq _ T b j (live T b flag s h0 hm j (by omega)), ih (by omega)]

theorem bwd (s K : ℕ) (h0 : flag 0 = ⊥) (hm : ∀ j < s, flag j ≤ flag (j+1))
    (hK : K * 2 ^ ((Finset.range s).sum (fun j =>
        let base := flag j ⊔ shift T (flag j)
        finrank (ZMod 2) (base ⊔ shift T (flag (j+1)) : Submodule (ZMod 2) (Du n)) - finrank (ZMod 2) base)) ≤ 2 ^ n) :
    K ≤ (MS (askc T b flag) T b s).card := by
  have hC : ∀ x : Wd n, Cc (askc T b flag) T x s = (Finset.range s).sum (fun j =>
        let base := flag j ⊔ shift T (flag j)
        finrank (ZMod 2) (base ⊔ shift T (flag (j+1)) : Submodule (ZMod 2) (Du n)) - finrank (ZMod 2) base) := by
    intro x
    unfold Cc
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    unfold cst
    rw [Aj_flag T b flag s h0 hm x j (by omega), Aj_flag T b flag s h0 hm x (j+1) (by omega)]
  have hP := Phi_c T b flag s h0 hm s (le_refl _)
  unfold Phi at hP
  rw [Finset.sum_congr rfl (fun x _ => by rw [hC x]), Finset.sum_const, smul_eq_mul] at hP
  rw [← hP] at hK
  exact Nat.le_of_mul_le_mul_right hK (by positivity)

end bwd

def trc (n s w : ℕ) (ask : List (Fin w → ZMod 2) → Fin w → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Fin n → ZMod 2) : List (Fin w → ZMod 2) :=
  (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
      hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]) []

theorem trc_eq (n s w : ℕ) (ask : Ask n w) (layer : ZMod 2) (word : Wd n) :
    trc n s w ask layer word = HH ask layer word s :=
  foldl_range_iter (stp ask layer word) [] s

theorem main (n s : ℕ) (T : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (b : Fin n → ZMod 2) (K : ℕ) :
    (∃ (w : ℕ) (ask : List (Fin w → ZMod 2) → Fin w → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) × ZMod 2 × ZMod 2),
        (∀ layer : ZMod 2, Function.Injective (trc n s w ask layer)) ∧
        K ≤ (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
          trc n s w ask 0 x = trc n s w ask 1 (T x + b))).card) ↔
      ∃ flag : ℕ → Submodule (ZMod 2) ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2),
        flag 0 = ⊥ ∧ flag s = ⊤ ∧ (∀ j < s, flag j ≤ flag (j+1)) ∧
        K * 2 ^ ((Finset.range s).sum (fun j =>
          let base := flag j ⊔ shift T (flag j)
          Module.finrank (ZMod 2) (base ⊔ shift T (flag (j+1)) : Submodule (ZMod 2) ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)) - Module.finrank (ZMod 2) base)) ≤ 2 ^ n := by
  have hcard : ∀ (w : ℕ) (ask : Ask n w), (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      trc n s w ask 0 x = trc n s w ask 1 (T x + b))) = MS ask T b s := by
    intro w ask
    ext x
    rw [mem_MS, Finset.mem_filter, trc_eq, trc_eq]
    simp [Mt]
  constructor
  · rintro ⟨w, ask, hinj, hK⟩
    rw [hcard] at hK
    have hinj0 : Function.Injective (fun x : Wd n => HH ask 0 x s) := by
      intro x y hxy
      apply hinj 0
      rw [trc_eq, trc_eq]
      exact hxy
    exact fwd ask T b s K hinj0 hK
  · rintro ⟨flag, h0, hs, hm, hK⟩
    refine ⟨Nat.card (Du n), askc T b flag, ?_, ?_⟩
    · intro layer x y hxy
      rw [trc_eq, trc_eq] at hxy
      exact inj_c T b flag s h0 hs layer hxy
    · rw [hcard]
      exact bwd T b flag s K h0 hm hK

end PEqualNP.Outside.L_pcx_380

theorem PEqualNP.Outside.L_pcx_380 : (∀ (n s : ℕ),
  let V := Fin n → ZMod 2
  let U := V →ₗ[ZMod 2] ZMod 2
  let transcript := fun (w : ℕ)
      (ask : List (Fin w → ZMod 2) → Fin w → U × ZMod 2 × ZMod 2)
      (layer : ZMod 2) (word : V) =>
    (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
      hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]) []
  ∀ (T : V ≃ₗ[ZMod 2] V) (b : V),
    let feasible := fun K : ℕ =>
      ∃ (w : ℕ) (ask : List (Fin w → ZMod 2) → Fin w → U × ZMod 2 × ZMod 2),
        (∀ layer : ZMod 2, Function.Injective (transcript w ask layer)) ∧
        K ≤ (Finset.univ.filter (fun x : V =>
          transcript w ask 0 x = transcript w ask 1 (T x + b))).card
    let shift := fun S : Submodule (ZMod 2) U =>
      Submodule.span (ZMod 2) (Set.image (fun a : U => a.comp T.toLinearMap + a) (S : Set U))
    ∀ K : ℕ, feasible K ↔
      ∃ flag : ℕ → Submodule (ZMod 2) U,
        flag 0 = ⊥ ∧ flag s = ⊤ ∧ (∀ j < s, flag j ≤ flag (j+1)) ∧
        K * 2 ^ ((Finset.range s).sum (fun j =>
          let base := flag j ⊔ shift (flag j)
          Module.finrank (ZMod 2) (base ⊔ shift (flag (j+1)) : Submodule (ZMod 2) U) - Module.finrank (ZMod 2) base)) ≤ 2 ^ n) := by
  intro n s V U transcript T b feasible shift K
  exact PEqualNP.Outside.L_pcx_380.main n s T b K
