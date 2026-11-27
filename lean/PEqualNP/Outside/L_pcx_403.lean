import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_403

open Finset

theorem psd_shift {G Y : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype Y] [DecidableEq Y]
    (T : G → Y) (SS : Finset G) (h0 : SS.Nonempty)
    (hadd : ∀ a ∈ SS, ∀ b ∈ SS, a + b ∈ SS) (hneg : ∀ a ∈ SS, -a ∈ SS) (t : G) :
    ∑ s ∈ SS, (univ.filter (fun w : G => T w = T (w + (t + s)))).card ≤
      ∑ s ∈ SS, (univ.filter (fun w : G => T w = T (w + s))).card := by
  let φ : Y → G → ℕ := fun y w => if T w = y then 1 else 0
  let c : Y → G → ℕ := fun y w => ∑ s ∈ SS, φ y (w + s)
  have hA : ∀ v : G, (univ.filter (fun w : G => T w = T (w + v))).card = ∑ w : G, ∑ y : Y, φ y w * φ y (w + v) := by
    intro v
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro w _
    simp only [φ, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [eq_comm]
  have hinv : ∀ (y : Y) (w : G), ∀ s0 ∈ SS, c y (w + s0) = c y w := by
    intro y w s0 hs0
    simp only [c]
    refine Finset.sum_bij' (fun s _ => s0 + s) (fun s _ => -s0 + s) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      exact hadd s0 hs0 s hs
    · intro s hs
      exact hadd _ (hneg s0 hs0) s hs
    · intro s _
      simp
    · intro s _
      simp
    · intro s _
      rw [add_assoc]
  have hQ : ∀ t : G, ∑ y : Y, ∑ w : G, c y w * c y (w + t) =
      SS.card * ∑ s ∈ SS, (univ.filter (fun w : G => T w = T (w + (t + s)))).card := by
    intro t
    have h1 : ∀ y : Y, ∑ w : G, c y w * c y (w + t) = SS.card * ∑ w : G, φ y w * c y (w + t) := by
      intro y
      have h2 : ∀ s ∈ SS, ∑ w : G, φ y (w + s) * c y (w + t) = ∑ w : G, φ y w * c y (w + t) := by
        intro s hs
        rw [← Equiv.sum_comp (Equiv.addRight s) (fun w => φ y w * c y (w + t))]
        apply Finset.sum_congr rfl
        intro w _
        simp only [Equiv.coe_addRight]
        rw [show w + s + t = (w + t) + s by abel, hinv y (w + t) s hs]
      calc ∑ w : G, c y w * c y (w + t)
          = ∑ w : G, ∑ s ∈ SS, φ y (w + s) * c y (w + t) := by
            apply Finset.sum_congr rfl
            intro w _
            simp only [c]
            rw [Finset.sum_mul]
        _ = ∑ s ∈ SS, ∑ w : G, φ y (w + s) * c y (w + t) := Finset.sum_comm
        _ = ∑ s ∈ SS, ∑ w : G, φ y w * c y (w + t) := Finset.sum_congr rfl h2
        _ = SS.card * ∑ w : G, φ y w * c y (w + t) := by
            rw [Finset.sum_const, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Finset.mul_sum]
    congr 1
    calc ∑ y : Y, ∑ w : G, φ y w * c y (w + t)
        = ∑ y : Y, ∑ w : G, ∑ s ∈ SS, φ y w * φ y (w + (t + s)) := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro w _
          simp only [c]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          rw [add_assoc]
      _ = ∑ y : Y, ∑ s ∈ SS, ∑ w : G, φ y w * φ y (w + (t + s)) := by
          apply Finset.sum_congr rfl
          intro y _
          exact Finset.sum_comm
      _ = ∑ s ∈ SS, ∑ y : Y, ∑ w : G, φ y w * φ y (w + (t + s)) := Finset.sum_comm
      _ = ∑ s ∈ SS, ∑ w : G, ∑ y : Y, φ y w * φ y (w + (t + s)) := by
          apply Finset.sum_congr rfl
          intro s _
          exact Finset.sum_comm
      _ = ∑ s ∈ SS, (univ.filter (fun w : G => T w = T (w + (t + s)))).card := by
          apply Finset.sum_congr rfl
          intro s _
          rw [hA]
  have hle : ∀ t : G, ∑ y : Y, ∑ w : G, c y w * c y (w + t) ≤ ∑ y : Y, ∑ w : G, c y w * c y (w + 0) := by
    intro t
    apply Finset.sum_le_sum
    intro y _
    have e1 : ∑ w : G, c y (w + t) * c y (w + t) = ∑ w : G, c y w * c y w :=
      Equiv.sum_comp (Equiv.addRight t) (fun w => c y w * c y w)
    have e2 : ∑ w : G, 2 * (c y w * c y (w + t)) ≤ ∑ w : G, (c y w * c y w + c y (w + t) * c y (w + t)) := by
      apply Finset.sum_le_sum
      intro w _
      nlinarith [sq_nonneg ((c y w : ℤ) - (c y (w + t) : ℤ)), sq_abs ((c y w : ℤ) - (c y (w + t) : ℤ))]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, e1] at e2
    simp only [add_zero]
    omega
  have key := hle t
  rw [hQ t, hQ 0] at key
  have hpos : 0 < SS.card := Finset.card_pos.mpr h0
  have key2 := Nat.le_of_mul_le_mul_left key hpos
  simpa using key2

open Classical

abbrev E3 := Fin 3 → ZMod 2
abbrev Xr (r : ℕ) := Fin r → Fin 3 → ZMod 2

def tg {r : ℕ} (z : Xr r) : Fin r → ZMod 2 := fun i => z i 2 + z i 0 * z i 1

def aa (e : E3) : ℕ :=
  (univ.filter (fun w : E3 => w 2 + w 0 * w 1 = (w + e) 2 + (w + e) 0 * (w + e) 1)).card

def AA {r : ℕ} (u : Xr r) : ℕ := (univ.filter (fun w : Xr r => tg w = tg (w + u))).card

theorem AA_prod {r : ℕ} (u : Xr r) : AA u = ∏ i, aa (u i) := by
  unfold AA aa
  rw [← Fintype.card_piFinset]
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  unfold tg
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

theorem AA_cons {r : ℕ} (e : E3) (v : Xr r) : AA (Fin.cons e v : Xr (r+1)) = aa e * AA v := by
  rw [AA_prod, AA_prod, Fin.prod_univ_succ]
  simp

noncomputable def NN {r : ℕ} (S : Submodule (ZMod 2) (Xr r)) : ℕ := ∑ u : Xr r, if u ∈ S then AA u else 0

theorem card_eq_NN {r : ℕ} (S : Submodule (ZMod 2) (Xr r)) :
    Nat.card {p : Xr r × Xr r // p.2 ∈ S ∧ tg p.1 = tg (p.1 + p.2)} = NN S := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  unfold NN
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u ∈ S
  · rw [if_pos hu]
    unfold AA
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro w _
    simp [hu]
  · rw [if_neg hu]
    apply Finset.sum_eq_zero
    intro w _
    simp [hu]

theorem sum_cons {r : ℕ} (F : Xr (r+1) → ℕ) :
    ∑ u : Xr (r+1), F u = ∑ e : E3, ∑ v : Xr r, F (Fin.cons e v) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1) => E3)) F, Fintype.sum_prod_type]
  rfl

theorem card_sub {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (W : Submodule (ZMod 2) V) :
    (univ.filter (fun v : V => v ∈ W)).card = 2 ^ Module.finrank (ZMod 2) W := by
  rw [← Fintype.card_subtype, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]

def consL (r : ℕ) : Xr r →ₗ[ZMod 2] Xr (r+1) :=
  LinearMap.pi (fun i : Fin (r+1) =>
    (Fin.cases (0 : Xr r →ₗ[ZMod 2] E3) (fun j : Fin r => (LinearMap.proj j : Xr r →ₗ[ZMod 2] E3)) i :
      Xr r →ₗ[ZMod 2] E3))

theorem consL_eq {r : ℕ} (v : Xr r) : consL r v = (Fin.cons 0 v : Xr (r+1)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [consL]
  · intro j
    simp [consL]

def hd {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) : Submodule (ZMod 2) E3 :=
  S.map (LinearMap.proj (0 : Fin (r+1)) : Xr (r+1) →ₗ[ZMod 2] E3)

def tl {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) : Submodule (ZMod 2) (Xr r) := S.comap (consL r)

theorem mem_tl {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) (v : Xr r) :
    v ∈ tl S ↔ (Fin.cons 0 v : Xr (r+1)) ∈ S := by
  unfold tl
  rw [Submodule.mem_comap, consL_eq]

theorem mem_hd {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) (e : E3) :
    e ∈ hd S ↔ ∃ v : Xr r, (Fin.cons e v : Xr (r+1)) ∈ S := by
  unfold hd
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Fin.tail u, ?_⟩
    have : (Fin.cons (u 0) (Fin.tail u) : Xr (r+1)) = u := Fin.cons_self_tail u
    simp only [LinearMap.proj_apply]
    rw [this]
    exact hu
  · rintro ⟨v, hv⟩
    exact ⟨_, hv, by simp⟩

theorem cons_sub {r : ℕ} (e : E3) (v v0 : Xr r) :
    (Fin.cons e v : Xr (r+1)) - Fin.cons e v0 = Fin.cons 0 (v - v0) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

theorem cons_mem_iff {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) (e : E3) (v0 : Xr r)
    (h0 : (Fin.cons e v0 : Xr (r+1)) ∈ S) (v : Xr r) :
    (Fin.cons e v : Xr (r+1)) ∈ S ↔ v - v0 ∈ tl S := by
  rw [mem_tl, ← cons_sub]
  exact (Submodule.sub_mem_iff_left S h0).symm

theorem inner_eq {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) (e : E3) (v0 : Xr r)
    (h0 : (Fin.cons e v0 : Xr (r+1)) ∈ S) (β : Xr r → ℕ) :
    ∑ v : Xr r, (if (Fin.cons e v : Xr (r+1)) ∈ S then β v else 0) =
      ∑ s : Xr r, (if s ∈ tl S then β (v0 + s) else 0) := by
  rw [← Equiv.sum_comp (Equiv.addLeft v0) (fun v : Xr r => if (Fin.cons e v : Xr (r+1)) ∈ S then β v else 0)]
  apply Finset.sum_congr rfl
  intro s _
  have hiff : (Fin.cons e (v0 + s) : Xr (r+1)) ∈ S ↔ s ∈ tl S := by
    rw [cons_mem_iff S e v0 h0]
    simp
  show (if (Fin.cons e (v0 + s) : Xr (r+1)) ∈ S then β (v0 + s) else 0) = _
  by_cases hs : s ∈ tl S
  · rw [if_pos hs, if_pos (hiff.mpr hs)]
  · rw [if_neg hs, if_neg (fun h => hs (hiff.mp h))]

theorem inner_zero {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) (e : E3) (he : e ∉ hd S) (β : Xr r → ℕ) :
    ∑ v : Xr r, (if (Fin.cons e v : Xr (r+1)) ∈ S then β v else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro v _
  rw [if_neg]
  intro hv
  exact he ((mem_hd S e).mpr ⟨v, hv⟩)

theorem shift_NN {r : ℕ} (S : Submodule (ZMod 2) (Xr r)) (t : Xr r) :
    ∑ s : Xr r, (if s ∈ S then AA (t + s) else 0) ≤ NN S := by
  unfold NN
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  unfold AA
  apply psd_shift tg (univ.filter (fun s : Xr r => s ∈ S))
  · exact ⟨0, by simp⟩
  · intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at *
    exact S.add_mem ha hb
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at *
    exact S.neg_mem ha

theorem NN_succ_le {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) :
    NN S ≤ (∑ e : E3, if e ∈ hd S then aa e else 0) * NN (tl S) := by
  have h1 : NN S = ∑ e : E3, aa e * ∑ v : Xr r, (if (Fin.cons e v : Xr (r+1)) ∈ S then AA v else 0) := by
    unfold NN
    rw [sum_cons]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [AA_cons]
    split_ifs <;> simp
  rw [h1, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : e ∈ hd S
  · rw [if_pos he]
    obtain ⟨v0, hv0⟩ := (mem_hd S e).mp he
    rw [inner_eq S e v0 hv0]
    exact Nat.mul_le_mul_left _ (shift_NN (tl S) v0)
  · rw [if_neg he, inner_zero S e he]
    simp

theorem card_succ {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) :
    (univ.filter (fun u : Xr (r+1) => u ∈ S)).card =
      (univ.filter (fun e : E3 => e ∈ hd S)).card * (univ.filter (fun v : Xr r => v ∈ tl S)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, sum_cons, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ hd S
  · rw [if_pos he, one_mul]
    obtain ⟨v0, hv0⟩ := (mem_hd S e).mp he
    rw [inner_eq S e v0 hv0 (fun _ => 1)]
  · rw [if_neg he, zero_mul, inner_zero S e he (fun _ => 1)]

theorem finrank_succ {r : ℕ} (S : Submodule (ZMod 2) (Xr (r+1))) :
    Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) (hd S) + Module.finrank (ZMod 2) (tl S) := by
  have h := card_succ S
  rw [card_sub, card_sub, card_sub, ← pow_add] at h
  exact Nat.pow_right_injective (le_refl 2) h

def gg (d : ℕ) : ℕ := if d = 0 then 8 else if d = 1 then 12 else if d = 2 then 20 else 32

def best (r h : ℕ) : ℕ :=
  if h = 1 then 12*8^(r-1) else 20^((2*h)%3) * 32^((h-2*((2*h)%3))/3) * 8^(r-(2*h)%3-(h-2*((2*h)%3))/3)

theorem gg0 : gg 0 = 8 := by decide
theorem gg1 : gg 1 = 12 := by decide
theorem gg2 : gg 2 = 20 := by decide
theorem gg3 : gg 3 = 32 := by decide

theorem best_f0 (q k : ℕ) : best (q + k) (3*q) = 32^q * 8^k := by
  unfold best
  have h1 : ¬ (3*q = 1) := by omega
  have h2 : (2*(3*q)) % 3 = 0 := by omega
  rw [if_neg h1, h2]
  have h3 : (3*q - 2*0)/3 = q := by omega
  have h4 : q + k - 0 - q = k := by omega
  rw [h3, h4]
  ring

theorem best_f1 (k : ℕ) : best (k+1) 1 = 12 * 8^k := by
  unfold best
  simp

theorem best_f2 (q k : ℕ) : best (q + 1 + k) (3*q+2) = 20 * 32^q * 8^k := by
  unfold best
  have h1 : ¬ (3*q+2 = 1) := by omega
  have h2 : (2*(3*q+2)) % 3 = 1 := by omega
  rw [if_neg h1, h2]
  have h3 : (3*q + 2 - 2*1)/3 = q := by omega
  have h4 : q + 1 + k - 1 - q = k := by omega
  rw [h3, h4]
  ring

theorem best_f4 (q k : ℕ) : best (q + 2 + k) (3*q+4) = 400 * 32^q * 8^k := by
  unfold best
  have h1 : ¬ (3*q+4 = 1) := by omega
  have h2 : (2*(3*q+4)) % 3 = 2 := by omega
  rw [if_neg h1, h2]
  have h3 : (3*q + 4 - 2*2)/3 = q := by omega
  have h4 : q + 2 + k - 2 - q = k := by omega
  rw [h3, h4]
  ring

theorem shape (r m : ℕ) (hm : m ≤ 3*r) :
    (∃ q k, m = 3*q ∧ r = q + k) ∨ (∃ k, m = 1 ∧ r = k+1) ∨
      (∃ q k, m = 3*q+2 ∧ r = q+1+k) ∨ (∃ q k, m = 3*q+4 ∧ r = q+2+k) := by
  have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases h3 with h | h | h
  · left
    exact ⟨m/3, r - m/3, by omega, by omega⟩
  · by_cases h1 : m = 1
    · right; left
      exact ⟨r - 1, h1, by omega⟩
    · right; right; right
      exact ⟨(m-4)/3, r - (m-4)/3 - 2, by omega, by omega⟩
  · right; right; left
    exact ⟨m/3, r - m/3 - 1, by omega, by omega⟩

theorem cmp (X Y c1 c2 P : ℕ) (hX : X = c1 * P) (hY : Y = c2 * P) (h : c1 ≤ c2) : X ≤ Y := by
  rw [hX, hY]
  exact Nat.mul_le_mul_right P h

theorem best_zero : best 0 0 = 1 := by
  have := best_f0 0 0
  simpa using this

theorem best_le (r h d : ℕ) (hd : d ≤ 3) (hdh : d ≤ h) (hm : h - d ≤ 3*r) :
    gg d * best r (h-d) ≤ best (r+1) h := by
  obtain ⟨m, rfl⟩ : ∃ m, h = m + d := ⟨h - d, by omega⟩
  have e : m + d - d = m := by omega
  rw [e] at hm ⊢
  have hd4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases shape r m hm with ⟨q, k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨q, k, rfl, rfl⟩ | ⟨q, k, rfl, rfl⟩
  · rw [best_f0]
    rcases hd4 with rfl | rfl | rfl | rfl
    · rw [show q + k + 1 = q + (k+1) by omega, show 3*q + 0 = 3*q by omega, best_f0, gg0]
      exact cmp _ _ 8 8 (32^q * 8^k) (by ring) (by ring) (by norm_num)
    · cases q with
      | zero =>
        rw [show 0 + k + 1 = k + 1 by omega, show 3*0 + 1 = 1 by omega, best_f1, gg1]
        exact cmp _ _ 12 12 (8^k) (by ring) (by ring) (by norm_num)
      | succ q' =>
        rw [show q' + 1 + k + 1 = q' + 2 + k by omega, show 3*(q'+1) + 1 = 3*q' + 4 by omega, best_f4, gg1]
        exact cmp _ _ 384 400 (32^q' * 8^k) (by ring) (by ring) (by norm_num)
    · rw [show q + k + 1 = q + 1 + k by omega, best_f2, gg2]
      exact cmp _ _ 20 20 (32^q * 8^k) (by ring) (by ring) (by norm_num)
    · rw [show q + k + 1 = (q+1) + k by omega, show 3*q + 3 = 3*(q+1) by omega, best_f0, gg3]
      exact cmp _ _ 32 32 (32^q * 8^k) (by ring) (by ring) (by norm_num)
  · rw [best_f1]
    rcases hd4 with rfl | rfl | rfl | rfl
    · rw [show 1 + 0 = 1 by omega, best_f1, gg0]
      exact cmp _ _ 96 96 (8^k) (by ring) (by ring) (by norm_num)
    · rw [show k + 1 + 1 = 0 + 1 + (k+1) by omega, show 1 + 1 = 3*0 + 2 by omega, best_f2, gg1]
      exact cmp _ _ 144 160 (8^k) (by ring) (by ring) (by norm_num)
    · rw [show k + 1 + 1 = 1 + (k+1) by omega, show 1 + 2 = 3*1 by omega, best_f0, gg2]
      exact cmp _ _ 240 256 (8^k) (by ring) (by ring) (by norm_num)
    · rw [show k + 1 + 1 = 0 + 2 + k by omega, show 1 + 3 = 3*0 + 4 by omega, best_f4, gg3]
      exact cmp _ _ 384 400 (8^k) (by ring) (by ring) (by norm_num)
  · rw [best_f2]
    rcases hd4 with rfl | rfl | rfl | rfl
    · rw [show q + 1 + k + 1 = q + 1 + (k+1) by omega, show 3*q + 2 + 0 = 3*q + 2 by omega, best_f2, gg0]
      exact cmp _ _ 160 160 (32^q * 8^k) (by ring) (by ring) (by norm_num)
    · rw [show q + 1 + k + 1 = (q+1) + (k+1) by omega, show 3*q + 2 + 1 = 3*(q+1) by omega, best_f0, gg1]
      exact cmp _ _ 240 256 (32^q * 8^k) (by ring) (by ring) (by norm_num)
    · rw [show q + 1 + k + 1 = q + 2 + k by omega, show 3*q + 2 + 2 = 3*q + 4 by omega, best_f4, gg2]
      exact cmp _ _ 400 400 (32^q * 8^k) (by ring) (by ring) (by norm_num)
    · rw [show q + 1 + k + 1 = (q+1) + 1 + k by omega, show 3*q + 2 + 3 = 3*(q+1) + 2 by omega, best_f2, gg3]
      exact cmp _ _ 640 640 (32^q * 8^k) (by ring) (by ring) (by norm_num)
  · rw [best_f4]
    rcases hd4 with rfl | rfl | rfl | rfl
    · rw [show q + 2 + k + 1 = q + 2 + (k+1) by omega, show 3*q + 4 + 0 = 3*q + 4 by omega, best_f4, gg0]
      exact cmp _ _ 3200 3200 (32^q * 8^k) (by ring) (by ring) (by norm_num)
    · rw [show q + 2 + k + 1 = (q+1) + 1 + (k+1) by omega, show 3*q + 4 + 1 = 3*(q+1) + 2 by omega, best_f2, gg1]
      exact cmp _ _ 4800 5120 (32^q * 8^k) (by ring) (by ring) (by norm_num)
    · rw [show q + 2 + k + 1 = (q+2) + (k+1) by omega, show 3*q + 4 + 2 = 3*(q+2) by omega, best_f0, gg2]
      exact cmp _ _ 8000 8192 (32^q * 8^k) (by ring) (by ring) (by norm_num)
    · rw [show q + 2 + k + 1 = (q+1) + 2 + k by omega, show 3*q + 4 + 3 = 3*(q+1) + 4 by omega, best_f4, gg3]
      exact cmp _ _ 12800 12800 (32^q * 8^k) (by ring) (by ring) (by norm_num)

theorem shape2 (r h : ℕ) (hh : h ≤ 3*(r+1)) :
    h = 0 ∨ h = 1 ∨ (∃ q k, h = 3*q+2 ∧ r = q + k) ∨ (∃ q k, h = 3*(q+1) ∧ r = q + k) ∨
      (∃ q k, h = 3*q+4 ∧ r = q + 1 + k) := by
  have h3 : h % 3 = 0 ∨ h % 3 = 1 ∨ h % 3 = 2 := by omega
  rcases h3 with h0 | h0 | h0
  · by_cases hz : h = 0
    · left; exact hz
    · right; right; right; left
      exact ⟨h/3 - 1, r - (h/3 - 1), by omega, by omega⟩
  · by_cases h1 : h = 1
    · right; left; exact h1
    · right; right; right; right
      exact ⟨(h-4)/3, r - (h-4)/3 - 1, by omega, by omega⟩
  · right; right; left
    exact ⟨h/3, r - h/3, by omega, by omega⟩

theorem best_eq (r h : ℕ) (hh : h ≤ 3*(r+1)) :
    ∃ d, d ≤ 3 ∧ d ≤ h ∧ h - d ≤ 3*r ∧ gg d * best r (h-d) = best (r+1) h := by
  rcases shape2 r h hh with rfl | rfl | ⟨q, k, rfl, rfl⟩ | ⟨q, k, rfl, rfl⟩ | ⟨q, k, rfl, rfl⟩
  · refine ⟨0, by omega, by omega, by omega, ?_⟩
    have e1 : best r (0 - 0) = 8^r := by
      have := best_f0 0 r
      simpa using this
    have e2 : best (r+1) 0 = 8^(r+1) := by
      have := best_f0 0 (r+1)
      simpa using this
    rw [e1, e2, gg0]
    ring
  · refine ⟨1, by omega, by omega, by omega, ?_⟩
    have e1 : best r (1 - 1) = 8^r := by
      have := best_f0 0 r
      simpa using this
    rw [e1, best_f1, gg1]
  · refine ⟨2, by omega, by omega, by omega, ?_⟩
    rw [show 3*q + 2 - 2 = 3*q by omega, best_f0, show q + k + 1 = q + 1 + k by omega, best_f2, gg2]
    ring
  · refine ⟨3, by omega, by omega, by omega, ?_⟩
    rw [show 3*(q+1) - 3 = 3*q by omega, best_f0, show q + k + 1 = (q+1) + k by omega, best_f0, gg3]
    ring
  · refine ⟨2, by omega, by omega, by omega, ?_⟩
    rw [show 3*q + 4 - 2 = 3*q + 2 by omega, best_f2, show q + 1 + k + 1 = q + 2 + k by omega, best_f4, gg2]
    ring


theorem aa_le : ∀ e : E3, aa e ≤ 4 + (if e = 0 then 4 else 0) := by decide

theorem aa_total : ∑ e : E3, aa e = 32 := by decide

theorem dsum : ∀ d, d ≤ 3 → (∑ e : E3, if (∀ i : Fin 3, d ≤ i.val → e i = 0) then aa e else 0) = gg d := by
  decide

theorem dcard : ∀ d, d ≤ 3 → (univ.filter (fun e : E3 => ∀ i : Fin 3, d ≤ i.val → e i = 0)).card = 2 ^ d := by
  decide

theorem hd_bound (D : Submodule (ZMod 2) E3) :
    (∑ e : E3, if e ∈ D then aa e else 0) ≤ gg (Module.finrank (ZMod 2) D) := by
  have hc := card_sub D
  have h1 : (∑ e : E3, if e ∈ D then aa e else 0) ≤ 4 * (univ.filter (fun e : E3 => e ∈ D)).card + 4 := by
    calc (∑ e : E3, if e ∈ D then aa e else 0)
        ≤ ∑ e : E3, (4 * (if e ∈ D then 1 else 0) + (if e = 0 then 4 else 0)) := by
          apply Finset.sum_le_sum
          intro e _
          by_cases he : e ∈ D
          · rw [if_pos he, if_pos he]
            exact aa_le e
          · rw [if_neg he]
            exact Nat.zero_le _
      _ = 4 * (univ.filter (fun e : E3 => e ∈ D)).card + 4 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter]
          simp
  have hle : Module.finrank (ZMod 2) D ≤ 3 := by
    have := Submodule.finrank_le D
    simpa using this
  rcases Nat.lt_or_ge (Module.finrank (ZMod 2) D) 3 with hlt | hge
  · have h3 : Module.finrank (ZMod 2) D = 0 ∨ Module.finrank (ZMod 2) D = 1 ∨ Module.finrank (ZMod 2) D = 2 := by
      omega
    rw [hc] at h1
    rcases h3 with h | h | h <;> rw [h] at h1 ⊢ <;> simpa [gg] using h1
  · have h3 : Module.finrank (ZMod 2) D = 3 := by omega
    have htop : D = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h3]; simp)
    rw [h3, htop]
    simp [aa_total, gg]

theorem fr_le (r : ℕ) (S : Submodule (ZMod 2) (Xr r)) : Module.finrank (ZMod 2) S ≤ 3 * r := by
  have h := Submodule.finrank_le S
  have e : Module.finrank (ZMod 2) (Fin r → Fin 3 → ZMod 2) = 3 * r := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  exact h.trans (le_of_eq e)

theorem NN_zero (S : Submodule (ZMod 2) (Xr 0)) : NN S = 1 := by
  unfold NN
  rw [Fintype.sum_subsingleton _ (0 : Xr 0), if_pos (zero_mem S), AA_prod]
  simp

theorem upper : ∀ (r : ℕ) (S : Submodule (ZMod 2) (Xr r)), NN S ≤ best r (Module.finrank (ZMod 2) S) := by
  intro r
  induction r with
  | zero =>
    intro S
    have hf : Module.finrank (ZMod 2) S = 0 := by
      have := fr_le 0 S
      omega
    rw [hf, best_zero, NN_zero]
  | succ r ih =>
    intro S
    have h1 := NN_succ_le S
    have h2 := hd_bound (hd S)
    have h3 := ih (tl S)
    have h4 := finrank_succ S
    have hd3 : Module.finrank (ZMod 2) (hd S) ≤ 3 := by
      have := Submodule.finrank_le (hd S)
      simpa using this
    have h6 := fr_le r (tl S)
    have h5 := best_le r (Module.finrank (ZMod 2) S) (Module.finrank (ZMod 2) (hd S)) hd3 (by omega) (by omega)
    have h7 : Module.finrank (ZMod 2) S - Module.finrank (ZMod 2) (hd S) = Module.finrank (ZMod 2) (tl S) := by
      omega
    rw [h7] at h5
    exact le_trans h1 (le_trans (Nat.mul_le_mul h2 h3) h5)

def dL (d : ℕ) : E3 →ₗ[ZMod 2] E3 :=
  LinearMap.pi (fun i : Fin 3 => if d ≤ i.val then (LinearMap.proj i : E3 →ₗ[ZMod 2] ZMod 2) else 0)

def tailL (r : ℕ) : Xr (r+1) →ₗ[ZMod 2] Xr r :=
  LinearMap.pi (fun j : Fin r => (LinearMap.proj j.succ : Xr (r+1) →ₗ[ZMod 2] E3))

def PS {r : ℕ} (d : ℕ) (S' : Submodule (ZMod 2) (Xr r)) : Submodule (ZMod 2) (Xr (r+1)) :=
  LinearMap.ker ((dL d).comp (LinearMap.proj (0 : Fin (r+1)) : Xr (r+1) →ₗ[ZMod 2] E3)) ⊓ S'.comap (tailL r)

theorem mem_PS {r : ℕ} (d : ℕ) (S' : Submodule (ZMod 2) (Xr r)) (e : E3) (v : Xr r) :
    (Fin.cons e v : Xr (r+1)) ∈ PS d S' ↔ (∀ i : Fin 3, d ≤ i.val → e i = 0) ∧ v ∈ S' := by
  unfold PS
  rw [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_comap]
  have e1 : tailL r (Fin.cons e v : Xr (r+1)) = v := by
    funext j
    simp [tailL]
  rw [e1]
  apply and_congr_left'
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, Fin.cons_zero]
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [dL, hi] using this
  · intro h
    funext i
    by_cases hi : d ≤ i.val
    · simp [dL, hi, h i hi]
    · simp [dL, hi]

theorem NN_PS {r : ℕ} (d : ℕ) (S' : Submodule (ZMod 2) (Xr r)) :
    NN (PS d S') = (∑ e : E3, if (∀ i : Fin 3, d ≤ i.val → e i = 0) then aa e else 0) * NN S' := by
  unfold NN
  rw [sum_cons, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [AA_cons]
  by_cases h1 : (∀ i : Fin 3, d ≤ i.val → e i = 0) <;> by_cases h2 : v ∈ S' <;> simp [mem_PS, h1, h2]

theorem card_PS {r : ℕ} (d : ℕ) (S' : Submodule (ZMod 2) (Xr r)) :
    (univ.filter (fun u : Xr (r+1) => u ∈ PS d S')).card =
      (univ.filter (fun e : E3 => ∀ i : Fin 3, d ≤ i.val → e i = 0)).card *
        (univ.filter (fun v : Xr r => v ∈ S')).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, sum_cons, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h1 : (∀ i : Fin 3, d ≤ i.val → e i = 0) <;> by_cases h2 : v ∈ S' <;> simp [mem_PS, h1, h2]

theorem lower : ∀ (r h : ℕ), h ≤ 3 * r →
    ∃ S : Submodule (ZMod 2) (Xr r), Module.finrank (ZMod 2) S = h ∧ best r h ≤ NN S := by
  intro r
  induction r with
  | zero =>
    intro h hh
    have h0 : h = 0 := by omega
    subst h0
    refine ⟨⊥, by simp, ?_⟩
    rw [best_zero, NN_zero]
  | succ r ih =>
    intro h hh
    obtain ⟨d, hd3, hdh, hm, heq⟩ := best_eq r h (by omega)
    obtain ⟨S', hS', hN⟩ := ih (h - d) hm
    refine ⟨PS d S', ?_, ?_⟩
    · have hc := card_PS d S'
      rw [card_sub, card_sub, dcard d hd3, ← pow_add] at hc
      have := Nat.pow_right_injective (le_refl 2) hc
      omega
    · rw [NN_PS, dsum d hd3, ← heq]
      exact Nat.mul_le_mul_left _ hN

theorem main403 (r h : ℕ) (hh : h ≤ 3*r) (K : ℕ) :
    (∃ S : Submodule (ZMod 2) (Xr r), Module.finrank (ZMod 2) S = h ∧
      K ≤ Nat.card {p : Xr r × Xr r // p.2 ∈ S ∧ tg p.1 = tg (p.1 + p.2)}) ↔ K ≤ best r h := by
  constructor
  · rintro ⟨S, hS, hK⟩
    rw [card_eq_NN] at hK
    have := upper r S
    rw [hS] at this
    exact le_trans hK this
  · intro hK
    obtain ⟨S, hS, hN⟩ := lower r h hh
    refine ⟨S, hS, ?_⟩
    rw [card_eq_NN]
    exact le_trans hK hN

end PEqualNP.Outside.L_pcx_403

theorem PEqualNP.Outside.L_pcx_403 : (∀ (r h : ℕ) (_ : h ≤ 3*r),
  let F := ZMod 2
  let X := Fin r → Fin 3 → F
  let Y := Fin r → F
  let target := fun (z : X) (i : Fin r) => z i 2 + z i 0 * z i 1
  let a := (2*h)%3
  let b := (h-2*a)/3
  let best := if h = 1 then 12*8^(r-1) else 20^a * 32^b * 8^(r-a-b)
  ∀ K : ℕ,
    (∃ S : Submodule F X, Module.finrank F S = h ∧
      K ≤ Nat.card {p : X × X // p.2 ∈ S ∧ target p.1 = target (p.1+p.2)}) ↔ K ≤ best) := by
  intro r h hh F X Y target a b best K
  exact PEqualNP.Outside.L_pcx_403.main403 r h hh K
