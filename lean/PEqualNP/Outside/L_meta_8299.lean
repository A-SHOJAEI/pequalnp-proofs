import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8299

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def targetA (u : Fin 6) (v : Fin 4) : Bool :=
  (13124385 : ℕ).testBit (4 * u.val + v.val)

private def on (a c : ℕ) : ℕ → Bool :=
  fun i => decide (i = a) || decide (i = c)

private theorem on_iff (a c i : ℕ) : on a c i = true ↔ i = a ∨ i = c := by
  simp [on]

private theorem on_comm (a c : ℕ) : on a c = on c a := by
  funext i; simp [on, Bool.or_comm]

private def Dep (F : (ℕ → Bool) → Bool) (N : Finset ℕ) : Prop :=
  ∀ x y : ℕ → Bool, (∀ i ∈ N, x i = y i) → F x = F y

private def StrongFree (F : (ℕ → Bool) → Bool) (N : Finset ℕ) : Prop :=
  F (fun _ => false) = false ∧
  ∀ a ∈ N, ∀ c ∈ N, ∀ d ∈ N,
    F (on a a) = false → F (on c c) = false → F (on d d) = false →
    F (on a c) = true → F (on a d) = true →
    ∀ x : ℕ → Bool, F (Function.update x c true) = F (Function.update x d true)

private def OneCenter (F : (ℕ → Bool) → Bool) (N B : Finset ℕ) : Prop :=
  F (fun _ => false) = false ∧
  B ⊆ N ∧
  (N \ B).Nonempty ∧
  (∀ x ∈ B, ∀ y ∈ B, F (on x x) = F (on y y) ∧ ∀ z ∈ N \ B, F (on x z) = F (on y z)) ∧
  (∀ a ∈ N \ B, ∀ c ∈ N \ B, ∀ d ∈ N \ B, ∀ b ∈ N,
    F (on a a) = false → F (on b b) = false → F (on c c) = false → F (on d d) = false →
    F (on a c) = true → F (on a d) = true → F (on b c) = true → F (on b d) = true)

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem update_false_all (t : ℕ) :
    Function.update (fun _ : ℕ => false) t false = fun _ => false := by
  funext i; by_cases h : i = t <;> simp [Function.update, h]

private theorem strongFree_rename {F : (ℕ → Bool) → Bool} {N : Finset ℕ}
    (hd : Dep F N) (hsf : StrongFree F N) {t p : ℕ}
    (ht : t ∈ N) (hp : p ∉ N.erase t) :
    StrongFree (fun x => F (Function.update x t (x p))) (N.erase t ∪ {p}) := by
  let r : ℕ → ℕ := fun u => if u = p then t else u
  have hr_mem : ∀ u ∈ N.erase t ∪ {p}, r u ∈ N := by
    intro u hu
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hu
    rcases hu with ⟨_, h2⟩ | rfl
    · by_cases hup : u = p
      · simp [r, hup, ht]
      · simp [r, hup, h2]
    · simp [r, ht]
  have hkey : ∀ u ∈ N.erase t ∪ {p}, ∀ v ∈ N.erase t ∪ {p},
      F (Function.update (on u v) t (on u v p)) = F (on (r u) (r v)) := by
    intro u hu v hv
    refine hd _ _ fun i hi => bool_ext ?_
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hu hv
    by_cases hit : i = t
    · subst hit
      rw [Function.update_self, on_iff, on_iff]
      have hru : i = r u ↔ u = p := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · rcases hu with ⟨hne, _⟩ | rfl
          · exact ⟨fun h => absurd h.symm hne, fun h => absurd h h1⟩
          · exact absurd rfl h1
      have hrv : i = r v ↔ v = p := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · rcases hv with ⟨hne, _⟩ | rfl
          · exact ⟨fun h => absurd h.symm hne, fun h => absurd h h1⟩
          · exact absurd rfl h1
      rw [hru, hrv]
      constructor <;> (rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm])
    · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
      have hip : i ≠ p := fun h => hp (h ▸ hiE)
      rw [Function.update_of_ne hit, on_iff, on_iff]
      have hru : i = r u ↔ i = u := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun h => absurd h hit, fun h => absurd (h.trans h1) hip⟩
        · rfl
      have hrv : i = r v ↔ i = v := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun h => absurd h hit, fun h => absurd (h.trans h1) hip⟩
        · rfl
      rw [hru, hrv]
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t false) = false
    rw [update_false_all]; exact hsf.1
  · intro a ha c hc d hd' ha0 hc0 hd0 hac had x
    dsimp only at ha0 hc0 hd0 hac had ⊢
    rw [hkey a ha a ha] at ha0
    rw [hkey c hc c hc] at hc0
    rw [hkey d hd' d hd'] at hd0
    rw [hkey a ha c hc] at hac
    rw [hkey a ha d hd'] at had
    have hsub := hsf.2 (r a) (hr_mem a ha) (r c) (hr_mem c hc) (r d) (hr_mem d hd')
      ha0 hc0 hd0 hac had (Function.update x t (x p))
    have hstep : ∀ u ∈ N.erase t ∪ {p},
        F (Function.update (Function.update x u true) t ((Function.update x u true) p)) =
        F (Function.update (Function.update x t (x p)) (r u) true) := by
      intro u hu
      refine hd _ _ fun i hi => ?_
      by_cases hup : u = p
      · subst hup
        simp only [r, ite_true, Function.update_self]
        by_cases hit : i = t
        · subst hit; simp [Function.update]
        · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
          have hip : i ≠ u := fun h => hp (h ▸ hiE)
          simp [Function.update, hit, hip]
      · have huE : u ∈ N.erase t := by
          simp only [Finset.mem_union, Finset.mem_singleton] at hu
          rcases hu with h | h; exact h; exact absurd h hup
        have hut : u ≠ t := Finset.ne_of_mem_erase huE
        simp only [r, if_neg hup]
        by_cases hit : i = t
        · subst hit
          simp [Function.update, Ne.symm hup, Ne.symm hut]
        · by_cases hiu : i = u
          · subst hiu; simp [Function.update, hit]
          · simp [Function.update, hit, hiu]
    rw [hstep c hc, hstep d hd']
    exact hsub

private theorem strongFree_or {F : (ℕ → Bool) → Bool} {N : Finset ℕ}
    (hd : Dep F N) (hsf : StrongFree F N) {t p q : ℕ}
    (ht : t ∈ N) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) :
    StrongFree (fun x => F (Function.update x t (x p || x q))) (N.erase t ∪ {p, q}) := by
  let r : ℕ → ℕ := fun u => if u = p ∨ u = q then t else u
  have hr_mem : ∀ u ∈ N.erase t ∪ {p, q}, r u ∈ N := by
    intro u hu
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with ⟨_, h2⟩ | rfl | rfl
    · by_cases h1 : u = p ∨ u = q
      · simp [r, h1, ht]
      · simp [r, h1, h2]
    · simp [r, ht]
    · simp [r, ht]
  have hkey : ∀ u ∈ N.erase t ∪ {p, q}, ∀ v ∈ N.erase t ∪ {p, q},
      F (Function.update (on u v) t (on u v p || on u v q)) = F (on (r u) (r v)) := by
    intro u hu v hv
    refine hd _ _ fun i hi => bool_ext ?_
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hu hv
    by_cases hit : i = t
    · subst hit
      rw [Function.update_self, Bool.or_eq_true, on_iff, on_iff, on_iff]
      have hru : i = r u ↔ u = p ∨ u = q := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · rcases hu with ⟨hne, _⟩ | rfl | rfl
          · exact ⟨fun h => absurd h.symm hne, fun h => absurd h h1⟩
          · exact absurd (Or.inl rfl) h1
          · exact absurd (Or.inr rfl) h1
      have hrv : i = r v ↔ v = p ∨ v = q := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · rcases hv with ⟨hne, _⟩ | rfl | rfl
          · exact ⟨fun h => absurd h.symm hne, fun h => absurd h h1⟩
          · exact absurd (Or.inl rfl) h1
          · exact absurd (Or.inr rfl) h1
      rw [hru, hrv]
      constructor
      · rintro ((h | h) | (h | h))
        · exact Or.inl (Or.inl h.symm)
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inl (Or.inr h.symm)
        · exact Or.inr (Or.inr h.symm)
      · rintro ((h | h) | (h | h))
        · exact Or.inl (Or.inl h.symm)
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inl (Or.inr h.symm)
        · exact Or.inr (Or.inr h.symm)
    · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
      have hip : i ≠ p := fun h => hp (h ▸ hiE)
      have hiq : i ≠ q := fun h => hq (h ▸ hiE)
      rw [Function.update_of_ne hit, on_iff, on_iff]
      have hru : i = r u ↔ i = u := by
        simp only [r]; split_ifs with h1
        · refine ⟨fun h => absurd h hit, fun h => ?_⟩
          rcases h1 with rfl | rfl
          · exact absurd h hip
          · exact absurd h hiq
        · rfl
      have hrv : i = r v ↔ i = v := by
        simp only [r]; split_ifs with h1
        · refine ⟨fun h => absurd h hit, fun h => ?_⟩
          rcases h1 with rfl | rfl
          · exact absurd h hip
          · exact absurd h hiq
        · rfl
      rw [hru, hrv]
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false || false)) = false
    simp only [Bool.or_self]; rw [update_false_all]; exact hsf.1
  · intro a ha c hc d hd' ha0 hc0 hd0 hac had x
    dsimp only at ha0 hc0 hd0 hac had ⊢
    rw [hkey a ha a ha] at ha0
    rw [hkey c hc c hc] at hc0
    rw [hkey d hd' d hd'] at hd0
    rw [hkey a ha c hc] at hac
    rw [hkey a ha d hd'] at had
    have hsub := hsf.2 (r a) (hr_mem a ha) (r c) (hr_mem c hc) (r d) (hr_mem d hd')
      ha0 hc0 hd0 hac had (Function.update x t (x p || x q))
    have hstep : ∀ u ∈ N.erase t ∪ {p, q},
        F (Function.update (Function.update x u true) t
          ((Function.update x u true) p || (Function.update x u true) q)) =
        F (Function.update (Function.update x t (x p || x q)) (r u) true) := by
      intro u hu
      refine hd _ _ fun i hi => ?_
      by_cases h1 : u = p ∨ u = q
      · simp only [r, if_pos h1]
        have hor : (Function.update x u true p || Function.update x u true q) = true := by
          rcases h1 with rfl | rfl <;> simp [Function.update]
        rw [hor]
        by_cases hit : i = t
        · subst hit; simp [Function.update]
        · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
          have hiu : i ≠ u := by
            rcases h1 with rfl | rfl
            · exact fun h => hp (h ▸ hiE)
            · exact fun h => hq (h ▸ hiE)
          simp [Function.update, hit, hiu]
      · have hup : u ≠ p := fun h => h1 (Or.inl h)
        have huq : u ≠ q := fun h => h1 (Or.inr h)
        have huE : u ∈ N.erase t := by
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | rfl | rfl
          · exact h
          · exact absurd rfl hup
          · exact absurd rfl huq
        have hut : u ≠ t := Finset.ne_of_mem_erase huE
        simp only [r, if_neg h1]
        by_cases hit : i = t
        · subst hit
          simp [Function.update, Ne.symm hup, Ne.symm huq, Ne.symm hut]
        · by_cases hiu : i = u
          · subst hiu; simp [Function.update, hit]
          · simp [Function.update, hit, hiu]
    rw [hstep c hc, hstep d hd']
    exact hsub

private theorem and_nb {F : (ℕ → Bool) → Bool} {N : Finset ℕ}
    (hd : Dep F N) {t p q : ℕ}
    (hpq : p ≠ q) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t)
    {e f : ℕ} (he : e = p ∨ e = q)
    (hf0 : F (Function.update (on f f) t (on f f p && on f f q)) = false)
    (hef : F (Function.update (on e f) t (on e f p && on e f q)) = true) :
    (e = p ∧ f = q) ∨ (e = q ∧ f = p) := by
  by_contra hn
  have hfalse : (on e f p && on e f q) = false := by
    cases h : (on e f p && on e f q)
    · rfl
    · exfalso
      rw [Bool.and_eq_true, on_iff, on_iff] at h
      rcases h with ⟨rfl | rfl, rfl | rfl⟩
      · exact hpq rfl
      · exact hn (Or.inl ⟨rfl, rfl⟩)
      · exact hn (Or.inr ⟨rfl, rfl⟩)
      · exact hpq rfl
  have hf_false : (on f f p && on f f q) = false := by
    cases h : (on f f p && on f f q)
    · rfl
    · exfalso
      rw [Bool.and_eq_true, on_iff, on_iff] at h
      rcases h with ⟨h1 | h1, h2 | h2⟩ <;> exact hpq (h1.trans h2.symm)
  rw [hfalse] at hef
  rw [hf_false] at hf0
  have heq : F (Function.update (on e f) t false) = F (Function.update (on f f) t false) := by
    refine hd _ _ fun i hi => ?_
    by_cases hit : i = t
    · subst hit; simp [Function.update]
    · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
      have hie : i ≠ e := by
        rcases he with rfl | rfl
        · exact fun h => hp (h ▸ hiE)
        · exact fun h => hq (h ▸ hiE)
      simp [Function.update, hit, on, hie]
  rw [heq, hf0] at hef
  exact Bool.noConfusion hef

private theorem strongFree_and {F : (ℕ → Bool) → Bool} {N : Finset ℕ}
    (hd : Dep F N) (hsf : StrongFree F N) {t p q : ℕ}
    (hpq : p ≠ q) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) :
    StrongFree (fun x => F (Function.update x t (x p && x q))) (N.erase t ∪ {p, q}) := by
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false && false)) = false
    simp only [Bool.and_self]; rw [update_false_all]; exact hsf.1
  · intro a ha c hc d hd' ha0 hc0 hd0 hac had x
    dsimp only at ha0 hc0 hd0 hac had ⊢
    by_cases hA : a = p ∨ a = q
    · have e1 := and_nb hd hpq hp hq hA hc0 hac
      have e2 := and_nb hd hpq hp hq hA hd0 had
      have hcd : c = d := by
        rcases e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e2 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
        · rfl
        · exact absurd h1 hpq
        · exact absurd h1.symm hpq
        · rfl
      rw [hcd]
    · by_cases hC : c = p ∨ c = q
      · rw [on_comm a c] at hac
        have e1 := and_nb hd hpq hp hq hC ha0 hac
        rcases e1 with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact absurd (Or.inr rfl) hA
        · exact absurd (Or.inl rfl) hA
      · by_cases hD : d = p ∨ d = q
        · rw [on_comm a d] at had
          have e1 := and_nb hd hpq hp hq hD ha0 had
          rcases e1 with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact absurd (Or.inr rfl) hA
          · exact absurd (Or.inl rfl) hA
        · have hmemE : ∀ u ∈ N.erase t ∪ {p, q}, ¬(u = p ∨ u = q) → u ∈ N.erase t := by
            intro u hu hu'
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with h | h | h
            · exact h
            · exact absurd (Or.inl h) hu'
            · exact absurd (Or.inr h) hu'
          have haE := hmemE a ha hA
          have hcE := hmemE c hc hC
          have hdE := hmemE d hd' hD
          have hpair : ∀ u ∈ N.erase t, ∀ v ∈ N.erase t,
              F (Function.update (on u v) t (on u v p && on u v q)) = F (on u v) := by
            intro u hu v hv
            have hup : u ≠ p := fun h => hp (h ▸ hu)
            have hvp : v ≠ p := fun h => hp (h ▸ hv)
            have hut : u ≠ t := Finset.ne_of_mem_erase hu
            have hvt : v ≠ t := Finset.ne_of_mem_erase hv
            refine hd _ _ fun i _ => ?_
            by_cases hit : i = t
            · subst hit; simp [Function.update, on, Ne.symm hup, Ne.symm hvp, Ne.symm hut, Ne.symm hvt]
            · simp [Function.update, hit]
          rw [hpair a haE a haE] at ha0
          rw [hpair c hcE c hcE] at hc0
          rw [hpair d hdE d hdE] at hd0
          rw [hpair a haE c hcE] at hac
          rw [hpair a haE d hdE] at had
          have hsub := hsf.2 a (Finset.mem_of_mem_erase haE) c (Finset.mem_of_mem_erase hcE)
            d (Finset.mem_of_mem_erase hdE) ha0 hc0 hd0 hac had (Function.update x t (x p && x q))
          have hupd : ∀ u ∈ N.erase t,
              F (Function.update (Function.update x u true) t
                ((Function.update x u true) p && (Function.update x u true) q)) =
              F (Function.update (Function.update x t (x p && x q)) u true) := by
            intro u hu
            have hup : u ≠ p := fun h => hp (h ▸ hu)
            have huq : u ≠ q := fun h => hq (h ▸ hu)
            have hut : u ≠ t := Finset.ne_of_mem_erase hu
            refine hd _ _ fun i _ => ?_
            by_cases hit : i = t
            · subst hit; simp [Function.update, Ne.symm hup, Ne.symm huq, Ne.symm hut]
            · by_cases hiu : i = u
              · subst hiu; simp [Function.update, hit]
              · simp [Function.update, hit, hiu]
          rw [hupd c hcE, hupd d hdE]
          exact hsub

private theorem strongFree_to_oneCenter_or {F : (ℕ → Bool) → Bool} {N : Finset ℕ}
    (hd : Dep F N) (hsf : StrongFree F N) {t p q : ℕ}
    (ht : t ∈ N) (hp : p ∈ N.erase t) (hq : q ∉ N.erase t) :
    OneCenter (fun x => F (Function.update x t (x p || x q))) (N.erase t ∪ {p, q}) {p} := by
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  let N' : Finset ℕ := N.erase t ∪ {p, q}
  have hsub : {p} ⊆ N' := by
    intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_union_left _ hp
  have hne : (N' \ {p}).Nonempty :=
    ⟨q, Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ (by simp), by simp [Ne.symm hpq]⟩⟩
  let r : ℕ → ℕ := fun u => if u = q then t else u
  have hr_mem : ∀ u ∈ N' \ {p}, r u ∈ N := by
    intro u hu
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hu
    rcases hu with ⟨huN', hup⟩
    simp only [N', Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at huN'
    by_cases huq : u = q
    · simp [r, huq, ht]
    · simp only [r, if_neg huq]
      rcases huN' with ⟨_, h2⟩ | h | h
      · exact h2
      · exact absurd h hup
      · exact absurd h huq
  have hkey_out : ∀ u ∈ N' \ {p}, ∀ v ∈ N' \ {p},
      F (Function.update (on u v) t (on u v p || on u v q)) = F (on (r u) (r v)) := by
    intro u hu v hv
    have hup : u ≠ p := Finset.mem_singleton.not.1 (Finset.mem_sdiff.1 hu).2
    have hvp : v ≠ p := Finset.mem_singleton.not.1 (Finset.mem_sdiff.1 hv).2
    have huN' := (Finset.mem_sdiff.1 hu).1
    have hvN' := (Finset.mem_sdiff.1 hv).1
    refine hd _ _ fun i hi => bool_ext ?_
    by_cases hit : i = t
    · subst hit
      rw [Function.update_self, Bool.or_eq_true, on_iff, on_iff, on_iff]
      have hru : i = r u ↔ u = q := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · have huE : u ∈ N.erase i := by
            simp only [N', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at huN'
            rcases huN' with h | h | h
            · exact h
            · exact absurd h hup
            · exact absurd h h1
          exact ⟨fun h => absurd h.symm (Finset.ne_of_mem_erase huE), fun h => absurd h h1⟩
      have hrv : i = r v ↔ v = q := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · have hvE : v ∈ N.erase i := by
            simp only [N', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hvN'
            rcases hvN' with h | h | h
            · exact h
            · exact absurd h hvp
            · exact absurd h h1
          exact ⟨fun h => absurd h.symm (Finset.ne_of_mem_erase hvE), fun h => absurd h h1⟩
      rw [hru, hrv]
      constructor
      · rintro ((h | h) | (h | h))
        · exact absurd h.symm hup
        · exact absurd h.symm hvp
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inr (Or.inr h.symm)
    · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
      have hiq : i ≠ q := fun h => hq (h ▸ hiE)
      rw [Function.update_of_ne hit, on_iff, on_iff]
      have hru : i = r u ↔ i = u := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun h => absurd h hit, fun h => absurd (h.trans h1) hiq⟩
        · rfl
      have hrv : i = r v ↔ i = v := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun h => absurd h hit, fun h => absurd (h.trans h1) hiq⟩
        · rfl
      rw [hru, hrv]
  have hkey_p : ∀ c ∈ N' \ {p},
      F (Function.update (on p c) t (on p c p || on p c q)) =
      F (Function.update (on p t) (r c) true) := by
    intro c hc
    have hcp : c ≠ p := Finset.mem_singleton.not.1 (Finset.mem_sdiff.1 hc).2
    have hcN' := (Finset.mem_sdiff.1 hc).1
    have hor : (on p c p || on p c q) = true := by simp [on]
    rw [hor]
    refine hd _ _ fun i hi => ?_
    by_cases hcq : c = q
    · subst hcq
      simp only [r, ite_true]
      by_cases hit : i = t
      · subst hit; simp [Function.update]
      · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
        have hic : i ≠ c := fun h => hq (h ▸ hiE)
        simp [Function.update, hit, on, hic]
    · have hcE : c ∈ N.erase t := by
        simp only [N', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hcN'
        rcases hcN' with h | h | h
        · exact h
        · exact absurd h hcp
        · exact absurd h hcq
      have hct : c ≠ t := Finset.ne_of_mem_erase hcE
      simp only [r, if_neg hcq]
      by_cases hit : i = t
      · subst hit; simp [Function.update, Ne.symm hct, on]
      · by_cases hic : i = c
        · subst hic; simp [Function.update, hit, on]
        · simp [Function.update, hit, hic, on]
  refine ⟨?_, hsub, hne, ?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false || false)) = false
    simp only [Bool.or_self]; rw [update_false_all]; exact hsf.1
  · intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy; subst hx; subst hy
    exact ⟨rfl, fun _ _ => rfl⟩
  · intro a ha c hc d hd' b hb ha0 hb0 hc0 hd0 hac had hbc
    dsimp only at ha0 hb0 hc0 hd0 hac had hbc ⊢
    rw [hkey_out a ha a ha] at ha0
    rw [hkey_out c hc c hc] at hc0
    rw [hkey_out d hd' d hd'] at hd0
    rw [hkey_out a ha c hc] at hac
    rw [hkey_out a ha d hd'] at had
    have hsf' := hsf.2 (r a) (hr_mem a ha) (r c) (hr_mem c hc) (r d) (hr_mem d hd') ha0 hc0 hd0 hac had
    by_cases hbp : b = p
    · subst hbp
      rw [hkey_p c hc] at hbc
      rw [hkey_p d hd']
      rw [← hsf' (on b t)]
      exact hbc
    · have hb_out : b ∈ N' \ {p} := Finset.mem_sdiff.2 ⟨hb, Finset.mem_singleton.not.2 hbp⟩
      rw [hkey_out b hb_out c hc] at hbc
      rw [hkey_out b hb_out d hd']
      have h1 : Function.update (on (r b) (r b)) (r c) true = on (r b) (r c) := by
        funext i; by_cases h : i = r c <;> simp [Function.update, on, h]
      have h2 : Function.update (on (r b) (r b)) (r d) true = on (r b) (r d) := by
        funext i; by_cases h : i = r d <;> simp [Function.update, on, h]
      have h3 := hsf' (on (r b) (r b))
      rw [h1, h2] at h3
      rw [← h3]
      exact hbc

private theorem strongFree_to_oneCenter_and {F : (ℕ → Bool) → Bool} {N : Finset ℕ}
    (hd : Dep F N) (hsf : StrongFree F N) {t p q : ℕ}
    (hp : p ∈ N.erase t) (hq : q ∉ N.erase t) :
    OneCenter (fun x => F (Function.update x t (x p && x q))) (N.erase t ∪ {p, q}) {p} := by
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  let N' : Finset ℕ := N.erase t ∪ {p, q}
  have hsub : {p} ⊆ N' := by
    intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_union_left _ hp
  have hne : (N' \ {p}).Nonempty :=
    ⟨q, Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ (by simp), by simp [Ne.symm hpq]⟩⟩
  have hq_iso : ∀ u ∈ N' \ {p},
      F (Function.update (on u u) t (on u u p && on u u q)) = false →
      F (Function.update (on q u) t (on q u p && on q u q)) = false := by
    intro u hu hu0
    have hup : u ≠ p := Finset.mem_singleton.not.1 (Finset.mem_sdiff.1 hu).2
    have hfalse1 : (on q u p && on q u q) = false := by
      simp [on, hpq, Ne.symm hup]
    have hfalse2 : (on u u p && on u u q) = false := by
      simp [on, Ne.symm hup]
    rw [hfalse1]; rw [hfalse2] at hu0
    have heq : F (Function.update (on q u) t false) = F (Function.update (on u u) t false) := by
      refine hd _ _ fun i hi => ?_
      by_cases hit : i = t
      · subst hit; simp [Function.update]
      · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
        have hiq : i ≠ q := fun h => hq (h ▸ hiE)
        simp [Function.update, hit, on, hiq]
    rw [heq]; exact hu0
  have hmemE : ∀ u ∈ N', u ≠ q → u ∈ N.erase t := by
    intro u hu huq
    simp only [N', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | rfl | h
    · exact h
    · exact hp
    · exact absurd h huq
  have hpairE : ∀ u ∈ N.erase t, ∀ v ∈ N.erase t,
      F (Function.update (on u v) t (on u v p && on u v q)) = F (on u v) := by
    intro u hu v hv
    have huq : u ≠ q := fun h => hq (h ▸ hu)
    have hvq : v ≠ q := fun h => hq (h ▸ hv)
    have hut : u ≠ t := Finset.ne_of_mem_erase hu
    have hvt : v ≠ t := Finset.ne_of_mem_erase hv
    refine hd _ _ fun i _ => ?_
    by_cases hit : i = t
    · subst hit; simp [Function.update, on, Ne.symm huq, Ne.symm hvq, Ne.symm hut, Ne.symm hvt]
    · simp [Function.update, hit]
  refine ⟨?_, hsub, hne, ?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false && false)) = false
    simp only [Bool.and_self]; rw [update_false_all]; exact hsf.1
  · intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy; subst hx; subst hy
    exact ⟨rfl, fun _ _ => rfl⟩
  · intro a ha c hc d hd' b hb ha0 hb0 hc0 hd0 hac had hbc
    dsimp only at ha0 hb0 hc0 hd0 hac had hbc ⊢
    have haq : a ≠ q := by
      intro h; rw [h] at hac; rw [hq_iso c hc hc0] at hac; exact Bool.noConfusion hac
    have hcq : c ≠ q := by
      intro h; rw [h] at hac; rw [on_comm a q, hq_iso a ha ha0] at hac; exact Bool.noConfusion hac
    have hdq : d ≠ q := by
      intro h; rw [h] at had; rw [on_comm a q, hq_iso a ha ha0] at had; exact Bool.noConfusion had
    have hbq : b ≠ q := by
      intro h; rw [h] at hbc; rw [hq_iso c hc hc0] at hbc; exact Bool.noConfusion hbc
    have haE := hmemE a (Finset.mem_sdiff.1 ha).1 haq
    have hcE := hmemE c (Finset.mem_sdiff.1 hc).1 hcq
    have hdE := hmemE d (Finset.mem_sdiff.1 hd').1 hdq
    have hbE := hmemE b hb hbq
    rw [hpairE a haE a haE] at ha0
    rw [hpairE c hcE c hcE] at hc0
    rw [hpairE d hdE d hdE] at hd0
    rw [hpairE a haE c hcE] at hac
    rw [hpairE a haE d hdE] at had
    rw [hpairE b hbE c hcE] at hbc
    rw [hpairE b hbE d hdE]
    have h1 : Function.update (on b b) c true = on b c := by
      funext i; by_cases h : i = c <;> simp [Function.update, on, h]
    have h2 : Function.update (on b b) d true = on b d := by
      funext i; by_cases h : i = d <;> simp [Function.update, on, h]
    have h3 := hsf.2 a (Finset.mem_of_mem_erase haE) c (Finset.mem_of_mem_erase hcE)
      d (Finset.mem_of_mem_erase hdE) ha0 hc0 hd0 hac had (on b b)
    rw [h1, h2] at h3
    rw [← h3]
    exact hbc

private theorem oneCenter_or {F : (ℕ → Bool) → Bool} {N B : Finset ℕ}
    (hd : Dep F N) (hoc : OneCenter F N B) {t p q : ℕ}
    (ht : t ∈ N) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) :
    ∃ B', OneCenter (fun x => F (Function.update x t (x p || x q))) (N.erase t ∪ {p, q}) B' := by
  rcases hoc with ⟨hF0, hBN, hne, htwin, haf⟩
  let N' : Finset ℕ := N.erase t ∪ {p, q}
  let r : ℕ → ℕ := fun u => if u = p ∨ u = q then t else u
  have hr_mem : ∀ u ∈ N', r u ∈ N := by
    intro u hu
    simp only [N', Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with ⟨_, h2⟩ | rfl | rfl
    · by_cases h1 : u = p ∨ u = q
      · simp [r, h1, ht]
      · simp [r, h1, h2]
    · simp [r, ht]
    · simp [r, ht]
  have hkey : ∀ u ∈ N', ∀ v ∈ N',
      F (Function.update (on u v) t (on u v p || on u v q)) = F (on (r u) (r v)) := by
    intro u hu v hv
    refine hd _ _ fun i hi => bool_ext ?_
    simp only [N', Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hu hv
    by_cases hit : i = t
    · subst hit
      rw [Function.update_self, Bool.or_eq_true, on_iff, on_iff, on_iff]
      have hru : i = r u ↔ u = p ∨ u = q := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · rcases hu with ⟨hne', _⟩ | rfl | rfl
          · exact ⟨fun h => absurd h.symm hne', fun h => absurd h h1⟩
          · exact absurd (Or.inl rfl) h1
          · exact absurd (Or.inr rfl) h1
      have hrv : i = r v ↔ v = p ∨ v = q := by
        simp only [r]; split_ifs with h1
        · exact ⟨fun _ => h1, fun _ => rfl⟩
        · rcases hv with ⟨hne', _⟩ | rfl | rfl
          · exact ⟨fun h => absurd h.symm hne', fun h => absurd h h1⟩
          · exact absurd (Or.inl rfl) h1
          · exact absurd (Or.inr rfl) h1
      rw [hru, hrv]
      constructor
      · rintro ((h | h) | (h | h))
        · exact Or.inl (Or.inl h.symm)
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inl (Or.inr h.symm)
        · exact Or.inr (Or.inr h.symm)
      · rintro ((h | h) | (h | h))
        · exact Or.inl (Or.inl h.symm)
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inl (Or.inr h.symm)
        · exact Or.inr (Or.inr h.symm)
    · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
      have hip : i ≠ p := fun h => hp (h ▸ hiE)
      have hiq : i ≠ q := fun h => hq (h ▸ hiE)
      rw [Function.update_of_ne hit, on_iff, on_iff]
      have hru : i = r u ↔ i = u := by
        simp only [r]; split_ifs with h1
        · refine ⟨fun h => absurd h hit, fun h => ?_⟩
          rcases h1 with rfl | rfl
          · exact absurd h hip
          · exact absurd h hiq
        · rfl
      have hrv : i = r v ↔ i = v := by
        simp only [r]; split_ifs with h1
        · refine ⟨fun h => absurd h hit, fun h => ?_⟩
          rcases h1 with rfl | rfl
          · exact absurd h hip
          · exact absurd h hiq
        · rfl
      rw [hru, hrv]
  by_cases htB : t ∈ B
  · refine ⟨B.erase t ∪ {p, q}, ?_, ?_, ?_, ?_, ?_⟩
    · show F (Function.update (fun _ => false) t (false || false)) = false
      simp only [Bool.or_self]; rw [update_false_all]; exact hF0
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with ⟨h1, h2⟩ | h | h
      · exact Or.inl ⟨h1, hBN h2⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases hne with ⟨z, hz⟩
      rw [Finset.mem_sdiff] at hz
      have hzt : z ≠ t := fun h => hz.2 (h ▸ htB)
      have hzE : z ∈ N.erase t := Finset.mem_erase.2 ⟨hzt, hz.1⟩
      have hzp : z ≠ p := fun h => hp (h ▸ hzE)
      have hzq : z ≠ q := fun h => hq (h ▸ hzE)
      refine ⟨z, Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ hzE, ?_⟩⟩
      simp [hz.2, hzp, hzq]
    · intro x hx y hy
      have hxN' : x ∈ N' := by
        simp only [N', Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨h1, hBN h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hyN' : y ∈ N' := by
        simp only [N', Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
        rcases hy with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨h1, hBN h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hrx : r x ∈ B := by
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with ⟨_, h2⟩ | rfl | rfl
        · by_cases h1 : x = p ∨ x = q; simp [r, h1, htB]; simp [r, h1, h2]
        · simp [r, htB]
        · simp [r, htB]
      have hry : r y ∈ B := by
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with ⟨_, h2⟩ | rfl | rfl
        · by_cases h1 : y = p ∨ y = q; simp [r, h1, htB]; simp [r, h1, h2]
        · simp [r, htB]
        · simp [r, htB]
      constructor
      · dsimp only
        rw [hkey x hxN' x hxN', hkey y hyN' y hyN']
        exact (htwin (r x) hrx (r y) hry).1
      · intro z hz
        dsimp only
        rw [Finset.mem_sdiff] at hz
        have hzp : z ≠ p := fun h => hz.2 (by simp [h])
        have hzq : z ≠ q := fun h => hz.2 (by simp [h])
        have hzE : z ∈ N.erase t := by
          have hz1 := hz.1
          simp only [N', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hz1
          rcases hz1 with h | h | h
          · exact h
          · exact absurd h hzp
          · exact absurd h hzq
        have hrz : r z = z := by simp [r, hzp, hzq]
        have hzNB : z ∈ N \ B := Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase hzE, fun h =>
          hz.2 (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hzE, h⟩))⟩
        rw [hkey x hxN' z hz.1, hkey y hyN' z hz.1, hrz]
        exact (htwin (r x) hrx (r y) hry).2 z hzNB
    · intro a ha c hc d hd' b hb ha0 hb0 hc0 hd0 hac had hbc
      dsimp only at ha0 hb0 hc0 hd0 hac had hbc ⊢
      have hout : ∀ u ∈ N' \ (B.erase t ∪ {p, q}), r u ∈ N \ B := by
        intro u hu
        rw [Finset.mem_sdiff] at hu
        have hup : u ≠ p := fun h => hu.2 (by simp [h])
        have huq : u ≠ q := fun h => hu.2 (by simp [h])
        have huE : u ∈ N.erase t := by
          have hu1 := hu.1
          simp only [N', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu1
          rcases hu1 with h | h | h
          · exact h
          · exact absurd h hup
          · exact absurd h huq
        have hru : r u = u := by simp [r, hup, huq]
        rw [hru]
        exact Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase huE, fun h =>
          hu.2 (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase huE, h⟩))⟩
      have haN' := (Finset.mem_sdiff.1 ha).1
      have hcN' := (Finset.mem_sdiff.1 hc).1
      have hdN' := (Finset.mem_sdiff.1 hd').1
      rw [hkey a haN' a haN'] at ha0
      rw [hkey b hb b hb] at hb0
      rw [hkey c hcN' c hcN'] at hc0
      rw [hkey d hdN' d hdN'] at hd0
      rw [hkey a haN' c hcN'] at hac
      rw [hkey a haN' d hdN'] at had
      rw [hkey b hb c hcN'] at hbc
      rw [hkey b hb d hdN']
      exact haf (r a) (hout a ha) (r c) (hout c hc) (r d) (hout d hd') (r b) (hr_mem b hb)
        ha0 hb0 hc0 hd0 hac had hbc
  · refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
    · show F (Function.update (fun _ => false) t (false || false)) = false
      simp only [Bool.or_self]; rw [update_false_all]; exact hF0
    · intro x hx
      have hxt : x ≠ t := fun h => htB (h ▸ hx)
      exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hxt, hBN hx⟩)
    · refine ⟨p, Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ (by simp), fun h => ?_⟩⟩
      have hpt : p ≠ t := fun he => htB (he ▸ h)
      exact hp (Finset.mem_erase.2 ⟨hpt, hBN h⟩)
    · intro x hx y hy
      have hxE : x ∈ N.erase t := Finset.mem_erase.2 ⟨fun h => htB (h ▸ hx), hBN hx⟩
      have hyE : y ∈ N.erase t := Finset.mem_erase.2 ⟨fun h => htB (h ▸ hy), hBN hy⟩
      have hrx : r x = x := by
        simp only [r, if_neg (show ¬(x = p ∨ x = q) from by
          rintro (rfl | rfl); exact hp hxE; exact hq hxE)]
      have hry : r y = y := by
        simp only [r, if_neg (show ¬(y = p ∨ y = q) from by
          rintro (rfl | rfl); exact hp hyE; exact hq hyE)]
      constructor
      · dsimp only
        rw [hkey x (Finset.mem_union_left _ hxE) x (Finset.mem_union_left _ hxE),
            hkey y (Finset.mem_union_left _ hyE) y (Finset.mem_union_left _ hyE), hrx, hry]
        exact (htwin x hx y hy).1
      · intro z hz
        dsimp only
        have hzN' := (Finset.mem_sdiff.1 hz).1
        have hzB := (Finset.mem_sdiff.1 hz).2
        have hrzNB : r z ∈ N \ B := by
          refine Finset.mem_sdiff.2 ⟨hr_mem z hzN', ?_⟩
          simp only [r]; split_ifs with h1
          · exact htB
          · exact hzB
        rw [hkey x (Finset.mem_union_left _ hxE) z hzN',
            hkey y (Finset.mem_union_left _ hyE) z hzN', hrx, hry]
        exact (htwin x hx y hy).2 (r z) hrzNB
    · intro a ha c hc d hd' b hb ha0 hb0 hc0 hd0 hac had hbc
      dsimp only at ha0 hb0 hc0 hd0 hac had hbc ⊢
      have hout : ∀ u ∈ N' \ B, r u ∈ N \ B := by
        intro u hu
        refine Finset.mem_sdiff.2 ⟨hr_mem u (Finset.mem_sdiff.1 hu).1, ?_⟩
        simp only [r]; split_ifs with h1
        · exact htB
        · exact (Finset.mem_sdiff.1 hu).2
      have haN' := (Finset.mem_sdiff.1 ha).1
      have hcN' := (Finset.mem_sdiff.1 hc).1
      have hdN' := (Finset.mem_sdiff.1 hd').1
      rw [hkey a haN' a haN'] at ha0
      rw [hkey b hb b hb] at hb0
      rw [hkey c hcN' c hcN'] at hc0
      rw [hkey d hdN' d hdN'] at hd0
      rw [hkey a haN' c hcN'] at hac
      rw [hkey a haN' d hdN'] at had
      rw [hkey b hb c hcN'] at hbc
      rw [hkey b hb d hdN']
      exact haf (r a) (hout a ha) (r c) (hout c hc) (r d) (hout d hd') (r b) (hr_mem b hb)
        ha0 hb0 hc0 hd0 hac had hbc

private theorem oneCenter_and {F : (ℕ → Bool) → Bool} {N B : Finset ℕ}
    (hd : Dep F N) (hoc : OneCenter F N B) {t p q : ℕ}
    (hpq : p ≠ q) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) :
    ∃ B', OneCenter (fun x => F (Function.update x t (x p && x q))) (N.erase t ∪ {p, q}) B' := by
  rcases hoc with ⟨hF0, hBN, _, htwin, haf⟩
  let N' : Finset ℕ := N.erase t ∪ {p, q}
  let B' : Finset ℕ := B.erase t
  have hB'E : B' ⊆ N.erase t := Finset.erase_subset_erase t hBN
  have hB'N' : B' ⊆ N' := Finset.Subset.trans hB'E Finset.subset_union_left
  have hp_not_B' : p ∉ B' := fun h => hp (hB'E h)
  have hne' : (N' \ B').Nonempty :=
    ⟨p, Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ (by simp), hp_not_B'⟩⟩
  have hpairE : ∀ u ∈ N.erase t, ∀ v ∈ N.erase t,
      F (Function.update (on u v) t (on u v p && on u v q)) = F (on u v) := by
    intro u hu v hv
    have hup : u ≠ p := fun h => hp (h ▸ hu)
    have hvp : v ≠ p := fun h => hp (h ▸ hv)
    have hut : u ≠ t := Finset.ne_of_mem_erase hu
    have hvt : v ≠ t := Finset.ne_of_mem_erase hv
    refine hd _ _ fun i _ => ?_
    by_cases hit : i = t
    · subst hit; simp [Function.update, on, Ne.symm hup, Ne.symm hvp, Ne.symm hut, Ne.symm hvt]
    · simp [Function.update, hit]
  have hpair_pq : ∀ x ∈ N.erase t, ∀ z, (z = p ∨ z = q) →
      F (Function.update (on x z) t (on x z p && on x z q)) = F (on x x) := by
    intro x hx z hz
    have hxp : x ≠ p := fun h => hp (h ▸ hx)
    have hxq : x ≠ q := fun h => hq (h ▸ hx)
    have hxt : x ≠ t := Finset.ne_of_mem_erase hx
    have hfalse : (on x z p && on x z q) = false := by
      cases h : (on x z p && on x z q)
      · rfl
      · exfalso
        rw [Bool.and_eq_true, on_iff, on_iff] at h
        rcases hz with rfl | rfl
        · rcases h.2 with h1 | h1
          · exact hxq h1.symm
          · exact hpq h1.symm
        · rcases h.1 with h1 | h1
          · exact hxp h1.symm
          · exact hpq h1
    rw [hfalse]
    refine hd _ _ fun i hi => ?_
    by_cases hit : i = t
    · subst hit; simp [Function.update, on, Ne.symm hxt]
    · have hiE : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
      have hiz : i ≠ z := by
        rcases hz with rfl | rfl
        · exact fun h => hp (h ▸ hiE)
        · exact fun h => hq (h ▸ hiE)
      simp [Function.update, hit, on, hiz]
  refine ⟨B', ?_, hB'N', hne', ?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false && false)) = false
    simp only [Bool.and_self]; rw [update_false_all]; exact hF0
  · intro x hx y hy
    have hxE := hB'E hx
    have hyE := hB'E hy
    have hxB := Finset.mem_of_mem_erase hx
    have hyB := Finset.mem_of_mem_erase hy
    constructor
    · dsimp only
      rw [hpairE x hxE x hxE, hpairE y hyE y hyE]
      exact (htwin x hxB y hyB).1
    · intro z hz
      dsimp only
      by_cases hzpq : z = p ∨ z = q
      · rw [hpair_pq x hxE z hzpq, hpair_pq y hyE z hzpq]
        exact (htwin x hxB y hyB).1
      · have hzE : z ∈ N.erase t := by
          have hz1 := (Finset.mem_sdiff.1 hz).1
          simp only [N', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hz1
          rcases hz1 with h | h | h
          · exact h
          · exact absurd (Or.inl h) hzpq
          · exact absurd (Or.inr h) hzpq
        have hzNB : z ∈ N \ B := Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase hzE, fun h =>
          (Finset.mem_sdiff.1 hz).2 (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hzE, h⟩)⟩
        rw [hpairE x hxE z hzE, hpairE y hyE z hzE]
        exact (htwin x hxB y hyB).2 z hzNB
  · intro a ha c hc d hd' b hb ha0 hb0 hc0 hd0 hac had hbc
    dsimp only at ha0 hb0 hc0 hd0 hac had hbc ⊢
    by_cases hA : a = p ∨ a = q
    · have e1 := and_nb hd hpq hp hq hA hc0 hac
      have e2 := and_nb hd hpq hp hq hA hd0 had
      have hcd : c = d := by
        rcases e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e2 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
        · rfl
        · exact absurd h1 hpq
        · exact absurd h1.symm hpq
        · rfl
      rw [← hcd]; exact hbc
    · by_cases hC : c = p ∨ c = q
      · rw [on_comm a c] at hac
        have e1 := and_nb hd hpq hp hq hC ha0 hac
        rcases e1 with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact absurd (Or.inr rfl) hA
        · exact absurd (Or.inl rfl) hA
      · by_cases hD : d = p ∨ d = q
        · rw [on_comm a d] at had
          have e1 := and_nb hd hpq hp hq hD ha0 had
          rcases e1 with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · exact absurd (Or.inr rfl) hA
          · exact absurd (Or.inl rfl) hA
        · by_cases hB : b = p ∨ b = q
          · have e1 := and_nb hd hpq hp hq hB hc0 hbc
            rcases e1 with ⟨_, rfl⟩ | ⟨_, rfl⟩
            · exact absurd (Or.inr rfl) hC
            · exact absurd (Or.inl rfl) hC
          · have hmemE : ∀ u ∈ N', ¬(u = p ∨ u = q) → u ∈ N.erase t := by
              intro u hu hu'
              simp only [N', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu
              rcases hu with h | h | h
              · exact h
              · exact absurd (Or.inl h) hu'
              · exact absurd (Or.inr h) hu'
            have haE := hmemE a (Finset.mem_sdiff.1 ha).1 hA
            have hcE := hmemE c (Finset.mem_sdiff.1 hc).1 hC
            have hdE := hmemE d (Finset.mem_sdiff.1 hd').1 hD
            have hbE := hmemE b hb hB
            have hout : ∀ u ∈ N' \ B', u ∈ N.erase t → u ∈ N \ B := by
              intro u hu huE
              exact Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase huE, fun h =>
                (Finset.mem_sdiff.1 hu).2 (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase huE, h⟩)⟩
            rw [hpairE a haE a haE] at ha0
            rw [hpairE b hbE b hbE] at hb0
            rw [hpairE c hcE c hcE] at hc0
            rw [hpairE d hdE d hdE] at hd0
            rw [hpairE a haE c hcE] at hac
            rw [hpairE a haE d hdE] at had
            rw [hpairE b hbE c hcE] at hbc
            rw [hpairE b hbE d hdE]
            exact haf a (hout a ha haE) c (hout c hc hcE) d (hout d hd' hdE)
              b (Finset.mem_of_mem_erase hbE) ha0 hb0 hc0 hd0 hac had hbc

private def run : List Gate → ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, x => x
  | g :: gs, t, x => run gs (t + 1) (Function.update x t (g.op.eval (g.inputs.map x)))

private theorem getD_snoc (w : List Bool) (v : Bool) (j : ℕ) :
    (w ++ [v]).getD j false = if j = w.length then v else w.getD j false := by
  by_cases hj : j < w.length
  · have hne : j ≠ w.length := Nat.ne_of_lt hj
    rw [if_neg hne, List.getD_eq_getElem _ _ (by simp; omega),
        List.getD_eq_getElem _ _ hj, List.getElem_append_left hj]
  · by_cases heq : j = w.length
    · subst heq
      rw [if_pos rfl, List.getD_eq_getElem _ _ (by simp)]
      simp
    · rw [if_neg heq, List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private theorem run_eq (gs : List Gate) : ∀ (w : List Bool) (i : ℕ),
    (wiresFrom gs w).getD i false = run gs w.length (fun j => w.getD j false) i := by
  induction gs with
  | nil => intro w i; rfl
  | cons g gs ih =>
    intro w i
    have e : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) := rfl
    rw [e, ih, List.length_append, List.length_singleton, run]
    congr 2
    funext j
    rw [getD_snoc, Function.update_apply]

private theorem run_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (t : ℕ) (x y : ℕ → Bool), (∀ i, x i = true → y i = true) →
      ∀ i, run gs t x i = true → run gs t y i = true := by
  induction gs with
  | nil => intro t x y hxy i hi; exact hxy i hi
  | cons g gs ih =>
    intro t x y hxy i hi
    have hgs := fun g' h => hg g' (List.mem_cons_of_mem _ h)
    have hg0 := hg g (List.mem_cons_self ..)
    refine ih hgs (t + 1) _ _ (fun j hj => ?_) i hi
    by_cases hjt : j = t
    · subst hjt
      simp only [Function.update_self] at hj ⊢
      rcases hg0 with hop | hop <;> rw [hop] at hj ⊢
      · simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hj ⊢
        rintro b ⟨a, ha, rfl⟩
        exact hxy a (hj (x a) ⟨a, ha, rfl⟩)
      · simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hj ⊢
        rcases hj with ⟨_, ⟨a, ha, rfl⟩, hxa⟩
        exact ⟨y a, ⟨a, ha, rfl⟩, hxy a hxa⟩
    · simp only [Function.update_of_ne hjt] at hj ⊢
      exact hxy j hj

private theorem back_one (o : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ t, ∃ N : Finset ℕ, N.card ≤ 1 + gs.length ∧ Dep (fun x => run gs t x o) N ∧
      (N.card = 1 + gs.length → StrongFree (fun x => run gs t x o) N) ∧
      (N.card = gs.length →
        StrongFree (fun x => run gs t x o) N ∨
        ∃ B : Finset ℕ, OneCenter (fun x => run gs t x o) N B) := by
  induction gs with
  | nil =>
    intro t
    refine ⟨{o}, by simp, fun x y h => h o (by simp), ?_, ?_⟩
    · intro _
      refine ⟨rfl, ?_⟩
      intro a ha _ _ _ _ ha0
      simp only [Finset.mem_singleton] at ha; subst ha
      simp [run, on] at ha0
    · intro h; simp at h
  | cons g gs ih =>
    intro t
    have hgs := fun g' h => hg g' (List.mem_cons_of_mem _ h)
    have hg0 := hg g (List.mem_cons_self ..)
    obtain ⟨N, hc, hd, hSF, hOC⟩ := ih hgs (t + 1)
    by_cases ht : t ∈ N
    · let N' : Finset ℕ := N.erase t ∪ g.inputs.toFinset
      have hcard_le : N'.card ≤ N.card + 1 := by
        dsimp only [N']
        have h1 := Finset.card_union_le (N.erase t) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
        have h5 := hg0.2
        omega
      have hdep' : Dep (fun x => run (g :: gs) t x o) N' := by
        intro x y h
        refine hd _ _ fun i hi => ?_
        by_cases hit : i = t
        · subst hit
          simp only [Function.update_self]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact h a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · simp only [Function.update_of_ne hit]
          exact h i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hit, hi⟩))
      have hstep_fresh : N'.card = N.card + 1 →
          ∃ p q, p ≠ q ∧ p ∉ N.erase t ∧ q ∉ N.erase t ∧
            g.inputs = [p, q] ∧ N' = N.erase t ∪ {p, q} := by
        intro hinc
        dsimp only [N'] at hinc
        have h1 := Finset.card_union_add_card_inter (N.erase t) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
        have h5 := hg0.2
        have hlen2 : g.inputs.length = 2 := by omega
        have htc2 : g.inputs.toFinset.card = 2 := by omega
        have hinter : (N.erase t ∩ g.inputs.toFinset).card = 0 := by omega
        match hgi : g.inputs with
        | [p, q] =>
          rw [hgi] at htc2 hinter
          have hpq : p ≠ q := by
            rintro rfl; simp at htc2
          have htf : ([p, q] : List ℕ).toFinset = {p, q} := by simp
          rw [htf] at hinter
          have hdisj : Disjoint (N.erase t) ({p, q} : Finset ℕ) := by
            rw [Finset.disjoint_iff_inter_eq_empty]
            exact Finset.card_eq_zero.1 hinter
          have hp : p ∉ N.erase t := fun h => Finset.disjoint_left.1 hdisj h (by simp)
          have hq : q ∉ N.erase t := fun h => Finset.disjoint_left.1 hdisj h (by simp)
          refine ⟨p, q, hpq, hp, hq, rfl, ?_⟩
          simp [N', hgi]
        | [] => simp [hgi] at hlen2
        | [_] => simp [hgi] at hlen2
        | _ :: _ :: _ :: _ => simp [hgi] at hlen2
      have hfresh_SF : N'.card = N.card + 1 → StrongFree (fun x => run gs (t + 1) x o) N →
          StrongFree (fun x => run (g :: gs) t x o) N' := by
        intro hinc hsfN
        obtain ⟨p, q, hpq, hp, hq, hins, hN'eq⟩ := hstep_fresh hinc
        rw [hN'eq]
        rcases hg0.1 with hop | hop
        · have heq : (fun x => run (g :: gs) t x o) =
              (fun x => run gs (t + 1) (Function.update x t (x p && x q)) o) := by
            funext x; simp [run, hop, hins, GateOp.eval]
          rw [heq]
          exact strongFree_and hd hsfN hpq hp hq
        · have heq : (fun x => run (g :: gs) t x o) =
              (fun x => run gs (t + 1) (Function.update x t (x p || x q)) o) := by
            funext x; simp [run, hop, hins, GateOp.eval]
          rw [heq]
          exact strongFree_or hd hsfN ht hp hq
      have hfresh_OC : N'.card = N.card + 1 →
          (∃ B, OneCenter (fun x => run gs (t + 1) x o) N B) →
          ∃ B', OneCenter (fun x => run (g :: gs) t x o) N' B' := by
        intro hinc ⟨B, hocB⟩
        obtain ⟨p, q, hpq, hp, hq, hins, hN'eq⟩ := hstep_fresh hinc
        rw [hN'eq]
        rcases hg0.1 with hop | hop
        · have heq : (fun x => run (g :: gs) t x o) =
              (fun x => run gs (t + 1) (Function.update x t (x p && x q)) o) := by
            funext x; simp [run, hop, hins, GateOp.eval]
          rw [heq]
          exact oneCenter_and hd hocB hpq hp hq
        · have heq : (fun x => run (g :: gs) t x o) =
              (fun x => run gs (t + 1) (Function.update x t (x p || x q)) o) := by
            funext x; simp [run, hop, hins, GateOp.eval]
          rw [heq]
          exact oneCenter_or hd hocB ht hp hq
      refine ⟨N', by rw [List.length_cons]; omega, hdep', ?_, ?_⟩
      · intro heq
        rw [List.length_cons] at heq
        have hN : N.card = 1 + gs.length := by omega
        have hinc : N'.card = N.card + 1 := by omega
        exact hfresh_SF hinc (hSF hN)
      · intro heq
        rw [List.length_cons] at heq
        by_cases hN : N.card = gs.length
        · have hinc : N'.card = N.card + 1 := by omega
          rcases hOC hN with hsfN | hocN
          · exact Or.inl (hfresh_SF hinc hsfN)
          · exact Or.inr (hfresh_OC hinc hocN)
        · have hN1 : N.card = 1 + gs.length := by omega
          have hsame : N'.card = N.card := by omega
          have hsfN := hSF hN1
          have h1 := Finset.card_union_add_card_inter (N.erase t) g.inputs.toFinset
          have h2 := Finset.card_erase_of_mem ht
          have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
          have hlen_le := hg0.2
          match hgi : g.inputs with
          | [] =>
            have hN'eq : N' = N.erase t := by simp [N', hgi]
            rw [hN'eq] at hsame; omega
          | [p] =>
            have hN'eq : N' = N.erase t ∪ {p} := by simp [N', hgi]
            have hp : p ∉ N.erase t := by
              intro hmem
              have hEq : N' = N.erase t := by
                rw [hN'eq]; exact Finset.union_eq_left.2 (Finset.singleton_subset_iff.2 hmem)
              rw [hEq] at hsame; omega
            rw [hN'eq]
            left
            have heq' : (fun x => run (g :: gs) t x o) =
                (fun x => run gs (t + 1) (Function.update x t (x p)) o) := by
              funext x; rcases hg0.1 with h | h <;> simp [run, h, hgi, GateOp.eval]
            rw [heq']
            exact strongFree_rename hd hsfN ht hp
          | [p, q] =>
            by_cases hpq : p = q
            · subst hpq
              have hN'eq : N' = N.erase t ∪ {p} := by simp [N', hgi]
              have hp : p ∉ N.erase t := by
                intro hmem
                have hEq : N' = N.erase t := by
                  rw [hN'eq]; exact Finset.union_eq_left.2 (Finset.singleton_subset_iff.2 hmem)
                rw [hEq] at hsame; omega
              rw [hN'eq]
              left
              have heq' : (fun x => run (g :: gs) t x o) =
                  (fun x => run gs (t + 1) (Function.update x t (x p)) o) := by
                funext x; rcases hg0.1 with h | h <;> simp [run, h, hgi, GateOp.eval]
              rw [heq']
              exact strongFree_rename hd hsfN ht hp
            · have htf : g.inputs.toFinset = {p, q} := by simp [hgi]
              have htc2 : g.inputs.toFinset.card = 2 := by
                rw [htf]; exact Finset.card_pair hpq
              have hN'eq : N' = N.erase t ∪ {p, q} := by simp [N', hgi]
              have h1' : N'.card + (N.erase t ∩ {p, q}).card = (N.erase t).card + 2 := by
                have := h1
                rw [htf] at this
                rw [Finset.card_pair hpq] at this
                simpa [N', htf] using this
              have hinter1 : (N.erase t ∩ ({p, q} : Finset ℕ)).card = 1 := by omega
              rw [hN'eq]
              right
              by_cases hpE : p ∈ N.erase t
              · have hqE : q ∉ N.erase t := by
                  intro hqE
                  have hsub2 : ({p, q} : Finset ℕ) ⊆ N.erase t ∩ {p, q} := by
                    intro u hu
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
                    refine Finset.mem_inter.2 ⟨?_, by simp [hu]⟩
                    rcases hu with rfl | rfl <;> assumption
                  have hle := Finset.card_le_card hsub2
                  rw [Finset.card_pair hpq] at hle; omega
                rcases hg0.1 with hop | hop
                · have heq' : (fun x => run (g :: gs) t x o) =
                      (fun x => run gs (t + 1) (Function.update x t (x p && x q)) o) := by
                    funext x; simp [run, hop, hgi, GateOp.eval]
                  rw [heq']
                  exact ⟨{p}, strongFree_to_oneCenter_and hd hsfN hpE hqE⟩
                · have heq' : (fun x => run (g :: gs) t x o) =
                      (fun x => run gs (t + 1) (Function.update x t (x p || x q)) o) := by
                    funext x; simp [run, hop, hgi, GateOp.eval]
                  rw [heq']
                  exact ⟨{p}, strongFree_to_oneCenter_or hd hsfN ht hpE hqE⟩
              · have hqE : q ∈ N.erase t := by
                  by_contra hqE
                  have hempty : N.erase t ∩ ({p, q} : Finset ℕ) = ∅ := by
                    ext u
                    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
                      Finset.notMem_empty, iff_false]
                    rintro ⟨hu, rfl | rfl⟩ <;> contradiction
                  rw [hempty, Finset.card_empty] at hinter1; omega
                have hN'sw : N.erase t ∪ {p, q} = N.erase t ∪ {q, p} := by
                  congr 1; exact Finset.pair_comm p q
                rw [hN'sw]
                rcases hg0.1 with hop | hop
                · have heq' : (fun x => run (g :: gs) t x o) =
                      (fun x => run gs (t + 1) (Function.update x t (x q && x p)) o) := by
                    funext x; simp [run, hop, hgi, GateOp.eval, Bool.and_comm]
                  rw [heq']
                  exact ⟨{q}, strongFree_to_oneCenter_and hd hsfN hqE hpE⟩
                · have heq' : (fun x => run (g :: gs) t x o) =
                      (fun x => run gs (t + 1) (Function.update x t (x q || x p)) o) := by
                    funext x; simp [run, hop, hgi, GateOp.eval, Bool.or_comm]
                  rw [heq']
                  exact ⟨{q}, strongFree_to_oneCenter_or hd hsfN ht hqE hpE⟩
          | _ :: _ :: _ :: _ => simp [hgi] at hlen_le
    · refine ⟨N, by rw [List.length_cons]; omega, ?_, ?_, ?_⟩
      · intro x y h
        dsimp only
        have h1 : run (g :: gs) t x o = run gs (t + 1) x o :=
          hd _ _ fun i hi => Function.update_of_ne (fun he : i = t => ht (he ▸ hi)) _ _
        have h2 : run (g :: gs) t y o = run gs (t + 1) y o :=
          hd _ _ fun i hi => Function.update_of_ne (fun he : i = t => ht (he ▸ hi)) _ _
        rw [h1, h2]; exact hd x y h
      · intro heq; rw [List.length_cons] at heq; omega
      · intro heq
        rw [List.length_cons] at heq
        have hN : N.card = 1 + gs.length := by omega
        have heqF : (fun x => run (g :: gs) t x o) = (fun x => run gs (t + 1) x o) := by
          funext x
          exact hd _ _ fun i hi => Function.update_of_ne (fun he : i = t => ht (he ▸ hi)) _ _
        rw [heqF]
        exact Or.inl (hSF hN)

private theorem oneEach_getD (u : Fin 6) (v : Fin 4) (j : ℕ) :
    (oneEach u v).getD j false = on u.val (6 + v.val) j := by
  unfold oneEach on
  by_cases hj : j < 6
  · have hlt : j < (List.ofFn fun i : Fin 6 => decide (i = u)).length := by simp [hj]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt,
        List.getElem_ofFn]
    have hne : j ≠ 6 + v.val := by omega
    simp [Fin.ext_iff, hne]
  · by_cases hj2 : j < 10
    · have hge : (List.ofFn fun i : Fin 6 => decide (i = u)).length ≤ j := by simp; omega
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right hge]
      simp only [List.length_ofFn, List.getElem_ofFn]
      have hne : j ≠ u.val := by omega
      simp only [hne, decide_false, Bool.false_or]
      congr 1; simp [Fin.ext_iff]; omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h1 : j ≠ u.val := by omega
      have h2 : j ≠ 6 + v.val := by omega
      simp [h1, h2]

private theorem no_strongFree {F : (ℕ → Bool) → Bool} {N : Finset ℕ}
    (hsub : Finset.range 10 ⊆ N)
    (hsolo : ∀ i < 10, F (on i i) = false)
    (hrep : ∀ (u : Fin 6) (v : Fin 4), F (on u.val (6 + v.val)) = targetA u v)
    (hsf : StrongFree F N) : False := by
  have hm : ∀ i < 10, i ∈ N := fun i hi => hsub (Finset.mem_range.2 hi)
  have h26 : F (on 2 6) = true := (hrep ⟨2, by omega⟩ ⟨0, by omega⟩).trans (by decide)
  have h27 : F (on 2 7) = true := (hrep ⟨2, by omega⟩ ⟨1, by omega⟩).trans (by decide)
  have h06 : F (on 0 6) = true := (hrep ⟨0, by omega⟩ ⟨0, by omega⟩).trans (by decide)
  have h07 : F (on 0 7) = false := (hrep ⟨0, by omega⟩ ⟨1, by omega⟩).trans (by decide)
  have h1 := hsf.2 2 (hm 2 (by omega)) 6 (hm 6 (by omega)) 7 (hm 7 (by omega))
    (hsolo 2 (by omega)) (hsolo 6 (by omega)) (hsolo 7 (by omega)) h26 h27 (on 0 0)
  have hu6 : Function.update (on 0 0) 6 true = on 0 6 := by
    funext i; by_cases h : i = 6 <;> simp [Function.update, on, h]
  have hu7 : Function.update (on 0 0) 7 true = on 0 7 := by
    funext i; by_cases h : i = 7 <;> simp [Function.update, on, h]
  rw [hu6, hu7, h06, h07] at h1
  exact Bool.noConfusion h1

private theorem no_oneCenter {F : (ℕ → Bool) → Bool} {B : Finset ℕ}
    (hsolo : ∀ i < 10, F (on i i) = false)
    (hrep : ∀ (u : Fin 6) (v : Fin 4), F (on u.val (6 + v.val)) = targetA u v)
    (hoc : OneCenter F (Finset.range 10) B) : False := by
  rcases hoc with ⟨_, _, hne, htwin, haf⟩
  have hmem : ∀ i < 10, i ∈ Finset.range 10 := fun i hi => Finset.mem_range.2 hi
  have hAF : ∀ a c d b, a < 10 → c < 10 → d < 10 → b < 10 →
      a ∉ B → c ∉ B → d ∉ B →
      F (on a c) = true → F (on a d) = true → F (on b c) = true → F (on b d) = true := by
    intro a c d b ha hc hd hb haB hcB hdB hac had hbc
    exact haf a (Finset.mem_sdiff.2 ⟨hmem a ha, haB⟩)
      c (Finset.mem_sdiff.2 ⟨hmem c hc, hcB⟩)
      d (Finset.mem_sdiff.2 ⟨hmem d hd, hdB⟩)
      b (hmem b hb) (hsolo a ha) (hsolo b hb) (hsolo c hc) (hsolo d hd) hac had hbc
  have hTw : ∀ x y z, x ∈ B → y ∈ B → z < 10 → z ∉ B → F (on x z) = F (on y z) := by
    intro x y z hx hy hz hzB
    exact (htwin x hx y hy).2 z (Finset.mem_sdiff.2 ⟨hmem z hz, hzB⟩)
  have hE : ∀ (u : Fin 6) (v : Fin 4) (b : Bool), targetA u v = b → F (on u.val (6 + v.val)) = b :=
    fun u v b hb => (hrep u v).trans hb
  have hE' : ∀ (u : Fin 6) (v : Fin 4) (b : Bool), targetA u v = b → F (on (6 + v.val) u.val) = b :=
    fun u v b hb => by rw [on_comm]; exact (hrep u v).trans hb
  have hL1 : 0 ∈ B ∨ 1 ∈ B ∨ 2 ∈ B := by
    by_contra h
    push Not at h
    rcases h with ⟨h0, h1, h2⟩
    by_cases h6 : 6 ∈ B
    · by_cases h7 : 7 ∈ B
      · have heq := hTw 6 7 0 h6 h7 (by omega) h0
        have e6 : F (on 6 0) = true := hE' ⟨0, by omega⟩ ⟨0, by omega⟩ true (by decide)
        have e7 : F (on 7 0) = false := hE' ⟨0, by omega⟩ ⟨1, by omega⟩ false (by decide)
        rw [e6, e7] at heq; exact Bool.noConfusion heq
      · have h61 := hAF 7 2 1 6 (by omega) (by omega) (by omega) (by omega) h7 h2 h1
          (hE' ⟨2, by omega⟩ ⟨1, by omega⟩ true (by decide))
          (hE' ⟨1, by omega⟩ ⟨1, by omega⟩ true (by decide))
          (hE' ⟨2, by omega⟩ ⟨0, by omega⟩ true (by decide))
        have e61 : F (on 6 1) = false := hE' ⟨1, by omega⟩ ⟨0, by omega⟩ false (by decide)
        rw [e61] at h61; exact Bool.noConfusion h61
    · by_cases h7 : 7 ∈ B
      · have h70 := hAF 6 2 0 7 (by omega) (by omega) (by omega) (by omega) h6 h2 h0
          (hE' ⟨2, by omega⟩ ⟨0, by omega⟩ true (by decide))
          (hE' ⟨0, by omega⟩ ⟨0, by omega⟩ true (by decide))
          (hE' ⟨2, by omega⟩ ⟨1, by omega⟩ true (by decide))
        have e70 : F (on 7 0) = false := hE' ⟨0, by omega⟩ ⟨1, by omega⟩ false (by decide)
        rw [e70] at h70; exact Bool.noConfusion h70
      · have h07 := hAF 2 6 7 0 (by omega) (by omega) (by omega) (by omega) h2 h6 h7
          (hE ⟨2, by omega⟩ ⟨0, by omega⟩ true (by decide))
          (hE ⟨2, by omega⟩ ⟨1, by omega⟩ true (by decide))
          (hE ⟨0, by omega⟩ ⟨0, by omega⟩ true (by decide))
        have e07 : F (on 0 7) = false := hE ⟨0, by omega⟩ ⟨1, by omega⟩ false (by decide)
        rw [e07] at h07; exact Bool.noConfusion h07
  have hL2 : 3 ∈ B ∨ 4 ∈ B ∨ 5 ∈ B := by
    by_contra h
    push Not at h
    rcases h with ⟨h3, h4, h5⟩
    by_cases h8 : 8 ∈ B
    · by_cases h9 : 9 ∈ B
      · have heq := hTw 8 9 3 h8 h9 (by omega) h3
        have e8 : F (on 8 3) = true := hE' ⟨3, by omega⟩ ⟨2, by omega⟩ true (by decide)
        have e9 : F (on 9 3) = false := hE' ⟨3, by omega⟩ ⟨3, by omega⟩ false (by decide)
        rw [e8, e9] at heq; exact Bool.noConfusion heq
      · have h84 := hAF 9 5 4 8 (by omega) (by omega) (by omega) (by omega) h9 h5 h4
          (hE' ⟨5, by omega⟩ ⟨3, by omega⟩ true (by decide))
          (hE' ⟨4, by omega⟩ ⟨3, by omega⟩ true (by decide))
          (hE' ⟨5, by omega⟩ ⟨2, by omega⟩ true (by decide))
        have e84 : F (on 8 4) = false := hE' ⟨4, by omega⟩ ⟨2, by omega⟩ false (by decide)
        rw [e84] at h84; exact Bool.noConfusion h84
    · by_cases h9 : 9 ∈ B
      · have h93 := hAF 8 5 3 9 (by omega) (by omega) (by omega) (by omega) h8 h5 h3
          (hE' ⟨5, by omega⟩ ⟨2, by omega⟩ true (by decide))
          (hE' ⟨3, by omega⟩ ⟨2, by omega⟩ true (by decide))
          (hE' ⟨5, by omega⟩ ⟨3, by omega⟩ true (by decide))
        have e93 : F (on 9 3) = false := hE' ⟨3, by omega⟩ ⟨3, by omega⟩ false (by decide)
        rw [e93] at h93; exact Bool.noConfusion h93
      · have h39 := hAF 5 8 9 3 (by omega) (by omega) (by omega) (by omega) h5 h8 h9
          (hE ⟨5, by omega⟩ ⟨2, by omega⟩ true (by decide))
          (hE ⟨5, by omega⟩ ⟨3, by omega⟩ true (by decide))
          (hE ⟨3, by omega⟩ ⟨2, by omega⟩ true (by decide))
        have e39 : F (on 3 9) = false := hE ⟨3, by omega⟩ ⟨3, by omega⟩ false (by decide)
        rw [e39] at h39; exact Bool.noConfusion h39
  have h6in : 6 ∈ B := by
    by_contra h6
    have hy : ∃ y ∈ B, F (on y 6) = false := by
      rcases hL2 with h | h | h
      · exact ⟨3, h, hE ⟨3, by omega⟩ ⟨0, by omega⟩ false (by decide)⟩
      · exact ⟨4, h, hE ⟨4, by omega⟩ ⟨0, by omega⟩ false (by decide)⟩
      · exact ⟨5, h, hE ⟨5, by omega⟩ ⟨0, by omega⟩ false (by decide)⟩
    rcases hy with ⟨y, hyB, hy6⟩
    have h0 : 0 ∉ B := fun h0B => by
      have heq := hTw 0 y 6 h0B hyB (by omega) h6
      have e06 : F (on 0 6) = true := hE ⟨0, by omega⟩ ⟨0, by omega⟩ true (by decide)
      rw [e06, hy6] at heq; exact Bool.noConfusion heq
    have h2 : 2 ∉ B := fun h2B => by
      have heq := hTw 2 y 6 h2B hyB (by omega) h6
      have e26 : F (on 2 6) = true := hE ⟨2, by omega⟩ ⟨0, by omega⟩ true (by decide)
      rw [e26, hy6] at heq; exact Bool.noConfusion heq
    by_cases h7 : 7 ∈ B
    · have h70 := hAF 6 2 0 7 (by omega) (by omega) (by omega) (by omega) h6 h2 h0
        (hE' ⟨2, by omega⟩ ⟨0, by omega⟩ true (by decide))
        (hE' ⟨0, by omega⟩ ⟨0, by omega⟩ true (by decide))
        (hE' ⟨2, by omega⟩ ⟨1, by omega⟩ true (by decide))
      have e70 : F (on 7 0) = false := hE' ⟨0, by omega⟩ ⟨1, by omega⟩ false (by decide)
      rw [e70] at h70; exact Bool.noConfusion h70
    · have h07 := hAF 2 6 7 0 (by omega) (by omega) (by omega) (by omega) h2 h6 h7
        (hE ⟨2, by omega⟩ ⟨0, by omega⟩ true (by decide))
        (hE ⟨2, by omega⟩ ⟨1, by omega⟩ true (by decide))
        (hE ⟨0, by omega⟩ ⟨0, by omega⟩ true (by decide))
      have e07 : F (on 0 7) = false := hE ⟨0, by omega⟩ ⟨1, by omega⟩ false (by decide)
      rw [e07] at h07; exact Bool.noConfusion h07
  have h7in : 7 ∈ B := by
    by_contra h7
    have hy : ∃ y ∈ B, F (on y 7) = false := by
      rcases hL2 with h | h | h
      · exact ⟨3, h, hE ⟨3, by omega⟩ ⟨1, by omega⟩ false (by decide)⟩
      · exact ⟨4, h, hE ⟨4, by omega⟩ ⟨1, by omega⟩ false (by decide)⟩
      · exact ⟨5, h, hE ⟨5, by omega⟩ ⟨1, by omega⟩ false (by decide)⟩
    rcases hy with ⟨y, hyB, hy7⟩
    have h1 : 1 ∉ B := fun h1B => by
      have heq := hTw 1 y 7 h1B hyB (by omega) h7
      have e17 : F (on 1 7) = true := hE ⟨1, by omega⟩ ⟨1, by omega⟩ true (by decide)
      rw [e17, hy7] at heq; exact Bool.noConfusion heq
    have h2 : 2 ∉ B := fun h2B => by
      have heq := hTw 2 y 7 h2B hyB (by omega) h7
      have e27 : F (on 2 7) = true := hE ⟨2, by omega⟩ ⟨1, by omega⟩ true (by decide)
      rw [e27, hy7] at heq; exact Bool.noConfusion heq
    have h61 := hAF 7 2 1 6 (by omega) (by omega) (by omega) (by omega) h7 h2 h1
      (hE' ⟨2, by omega⟩ ⟨1, by omega⟩ true (by decide))
      (hE' ⟨1, by omega⟩ ⟨1, by omega⟩ true (by decide))
      (hE' ⟨2, by omega⟩ ⟨0, by omega⟩ true (by decide))
    have e61 : F (on 6 1) = false := hE' ⟨1, by omega⟩ ⟨0, by omega⟩ false (by decide)
    rw [e61] at h61; exact Bool.noConfusion h61
  have h8in : 8 ∈ B := by
    by_contra h8
    have hy : ∃ y ∈ B, F (on y 8) = false := by
      rcases hL1 with h | h | h
      · exact ⟨0, h, hE ⟨0, by omega⟩ ⟨2, by omega⟩ false (by decide)⟩
      · exact ⟨1, h, hE ⟨1, by omega⟩ ⟨2, by omega⟩ false (by decide)⟩
      · exact ⟨2, h, hE ⟨2, by omega⟩ ⟨2, by omega⟩ false (by decide)⟩
    rcases hy with ⟨y, hyB, hy8⟩
    have h3 : 3 ∉ B := fun h3B => by
      have heq := hTw 3 y 8 h3B hyB (by omega) h8
      have e38 : F (on 3 8) = true := hE ⟨3, by omega⟩ ⟨2, by omega⟩ true (by decide)
      rw [e38, hy8] at heq; exact Bool.noConfusion heq
    have h5 : 5 ∉ B := fun h5B => by
      have heq := hTw 5 y 8 h5B hyB (by omega) h8
      have e58 : F (on 5 8) = true := hE ⟨5, by omega⟩ ⟨2, by omega⟩ true (by decide)
      rw [e58, hy8] at heq; exact Bool.noConfusion heq
    by_cases h9 : 9 ∈ B
    · have h93 := hAF 8 5 3 9 (by omega) (by omega) (by omega) (by omega) h8 h5 h3
        (hE' ⟨5, by omega⟩ ⟨2, by omega⟩ true (by decide))
        (hE' ⟨3, by omega⟩ ⟨2, by omega⟩ true (by decide))
        (hE' ⟨5, by omega⟩ ⟨3, by omega⟩ true (by decide))
      have e93 : F (on 9 3) = false := hE' ⟨3, by omega⟩ ⟨3, by omega⟩ false (by decide)
      rw [e93] at h93; exact Bool.noConfusion h93
    · have h39 := hAF 5 8 9 3 (by omega) (by omega) (by omega) (by omega) h5 h8 h9
        (hE ⟨5, by omega⟩ ⟨2, by omega⟩ true (by decide))
        (hE ⟨5, by omega⟩ ⟨3, by omega⟩ true (by decide))
        (hE ⟨3, by omega⟩ ⟨2, by omega⟩ true (by decide))
      have e39 : F (on 3 9) = false := hE ⟨3, by omega⟩ ⟨3, by omega⟩ false (by decide)
      rw [e39] at h39; exact Bool.noConfusion h39
  have h9in : 9 ∈ B := by
    by_contra h9
    have hy : ∃ y ∈ B, F (on y 9) = false := by
      rcases hL1 with h | h | h
      · exact ⟨0, h, hE ⟨0, by omega⟩ ⟨3, by omega⟩ false (by decide)⟩
      · exact ⟨1, h, hE ⟨1, by omega⟩ ⟨3, by omega⟩ false (by decide)⟩
      · exact ⟨2, h, hE ⟨2, by omega⟩ ⟨3, by omega⟩ false (by decide)⟩
    rcases hy with ⟨y, hyB, hy9⟩
    have h4 : 4 ∉ B := fun h4B => by
      have heq := hTw 4 y 9 h4B hyB (by omega) h9
      have e49 : F (on 4 9) = true := hE ⟨4, by omega⟩ ⟨3, by omega⟩ true (by decide)
      rw [e49, hy9] at heq; exact Bool.noConfusion heq
    have h5 : 5 ∉ B := fun h5B => by
      have heq := hTw 5 y 9 h5B hyB (by omega) h9
      have e59 : F (on 5 9) = true := hE ⟨5, by omega⟩ ⟨3, by omega⟩ true (by decide)
      rw [e59, hy9] at heq; exact Bool.noConfusion heq
    have h84 := hAF 9 5 4 8 (by omega) (by omega) (by omega) (by omega) h9 h5 h4
      (hE' ⟨5, by omega⟩ ⟨3, by omega⟩ true (by decide))
      (hE' ⟨4, by omega⟩ ⟨3, by omega⟩ true (by decide))
      (hE' ⟨5, by omega⟩ ⟨2, by omega⟩ true (by decide))
    have e84 : F (on 8 4) = false := hE' ⟨4, by omega⟩ ⟨2, by omega⟩ false (by decide)
    rw [e84] at h84; exact Bool.noConfusion h84
  rcases hne with ⟨z, hz⟩
  rw [Finset.mem_sdiff, Finset.mem_range] at hz
  rcases hz with ⟨hz10, hzB⟩
  have hz6 : z < 6 := by
    by_contra h
    have : z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> contradiction
  have hcontra : ∀ (r1 r2 : Fin 4),
      (13124385 : ℕ).testBit (4 * z + r1.val) = true →
      (13124385 : ℕ).testBit (4 * z + r2.val) = false → False := by
    intro r1 r2 ht1 hf2
    have hr1B : 6 + r1.val ∈ B := by
      have : r1.val = 0 ∨ r1.val = 1 ∨ r1.val = 2 ∨ r1.val = 3 := by omega
      rcases this with h | h | h | h <;> rw [h] <;> assumption
    have hr2B : 6 + r2.val ∈ B := by
      have : r2.val = 0 ∨ r2.val = 1 ∨ r2.val = 2 ∨ r2.val = 3 := by omega
      rcases this with h | h | h | h <;> rw [h] <;> assumption
    have heq := hTw (6 + r1.val) (6 + r2.val) z hr1B hr2B hz10 hzB
    rw [hE' ⟨z, hz6⟩ r1 true ht1, hE' ⟨z, hz6⟩ r2 false hf2] at heq
    exact Bool.noConfusion heq
  have hzcases : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 := by omega
  rcases hzcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hcontra (0 : Fin 4) (1 : Fin 4) (by decide) (by decide)
  · exact hcontra (1 : Fin 4) (0 : Fin 4) (by decide) (by decide)
  · exact hcontra (0 : Fin 4) (2 : Fin 4) (by decide) (by decide)
  · exact hcontra (2 : Fin 4) (3 : Fin 4) (by decide) (by decide)
  · exact hcontra (3 : Fin 4) (2 : Fin 4) (by decide) (by decide)
  · exact hcontra (2 : Fin 4) (0 : Fin 4) (by decide) (by decide)

theorem main_proof :
    ¬ PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 6) (v : Fin 4) => (13124385 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  rintro ⟨C, hmono, hsize, hrep⟩
  have hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h1 := hmono g hg
    exact ⟨h1.1, h1.2⟩
  let F : (ℕ → Bool) → Bool := fun x => run C.gates 10 x C.output
  have hF_rep : ∀ (u : Fin 6) (v : Fin 4), F (on u.val (6 + v.val)) = targetA u v := by
    intro u v
    have hev := hrep u v
    have hlen : (oneEach u v).length = 10 := by simp [oneEach]
    have hrun := run_eq C.gates (oneEach u v) C.output
    rw [hlen] at hrun
    have hfun : (fun j => (oneEach u v).getD j false) = on u.val (6 + v.val) := by
      funext j; exact oneEach_getD u v j
    rw [hfun] at hrun
    change (wiresFrom C.gates (oneEach u v)).getD C.output false = targetA u v at hev
    rw [hrun] at hev
    exact hev
  have hF_mono : ∀ x y : ℕ → Bool, (∀ i, x i = true → y i = true) → F x = true → F y = true :=
    fun x y hxy hx => run_mono C.gates (fun g hg => (hgates g hg).1) 10 x y hxy C.output hx
  have hsolo : ∀ i < 10, F (on i i) = false := by
    intro i hi
    cases hval : F (on i i)
    · rfl
    · exfalso
      have hsub : ∀ (u : Fin 6) (v : Fin 4), (i = u.val ∨ i = 6 + v.val) →
          targetA u v = false → False := by
        intro u v hmem hfalse
        have h1 : F (on u.val (6 + v.val)) = true := hF_mono (on i i) (on u.val (6 + v.val))
          (fun j hj => by
            rw [on_iff] at hj ⊢
            have : j = i := by rcases hj with rfl | rfl <;> rfl
            subst this; exact hmem) hval
        rw [hF_rep u v, hfalse] at h1
        exact Bool.noConfusion h1
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
                    i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsub (0 : Fin 6) (1 : Fin 4) (Or.inl rfl) (by decide)
      · exact hsub (1 : Fin 6) (0 : Fin 4) (Or.inl rfl) (by decide)
      · exact hsub (2 : Fin 6) (2 : Fin 4) (Or.inl rfl) (by decide)
      · exact hsub (3 : Fin 6) (3 : Fin 4) (Or.inl rfl) (by decide)
      · exact hsub (4 : Fin 6) (2 : Fin 4) (Or.inl rfl) (by decide)
      · exact hsub (5 : Fin 6) (0 : Fin 4) (Or.inl rfl) (by decide)
      · exact hsub (1 : Fin 6) (0 : Fin 4) (Or.inr rfl) (by decide)
      · exact hsub (0 : Fin 6) (1 : Fin 4) (Or.inr rfl) (by decide)
      · exact hsub (4 : Fin 6) (2 : Fin 4) (Or.inr rfl) (by decide)
      · exact hsub (3 : Fin 6) (3 : Fin 4) (Or.inr rfl) (by decide)
  obtain ⟨N, hc, hd, hSF, hOC⟩ := back_one C.output C.gates hgates 10
  have hrange : Finset.range 10 ⊆ N := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_contra hiN
    have hflip : ∀ (u : Fin 6) (v : Fin 4), targetA u v = true →
        (i = u.val ∨ i = 6 + v.val) → False := by
      intro u v ht hmem
      rcases hmem with rfl | rfl
      · have heq : F (on u.val (6 + v.val)) = F (on (6 + v.val) (6 + v.val)) := by
          refine hd _ _ fun j hj => ?_
          have hju : j ≠ u.val := fun h => hiN (h ▸ hj)
          simp [on, hju]
        rw [hF_rep u v, ht, hsolo (6 + v.val) (by omega)] at heq
        exact Bool.noConfusion heq
      · have heq : F (on u.val (6 + v.val)) = F (on u.val u.val) := by
          refine hd _ _ fun j hj => ?_
          have hjv : j ≠ 6 + v.val := fun h => hiN (h ▸ hj)
          simp [on, hjv]
        rw [hF_rep u v, ht, hsolo u.val (by omega)] at heq
        exact Bool.noConfusion heq
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
                  i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hflip (0 : Fin 6) (0 : Fin 4) (by decide) (Or.inl rfl)
    · exact hflip (1 : Fin 6) (1 : Fin 4) (by decide) (Or.inl rfl)
    · exact hflip (2 : Fin 6) (0 : Fin 4) (by decide) (Or.inl rfl)
    · exact hflip (3 : Fin 6) (2 : Fin 4) (by decide) (Or.inl rfl)
    · exact hflip (4 : Fin 6) (3 : Fin 4) (by decide) (Or.inl rfl)
    · exact hflip (5 : Fin 6) (2 : Fin 4) (by decide) (Or.inl rfl)
    · exact hflip (0 : Fin 6) (0 : Fin 4) (by decide) (Or.inr rfl)
    · exact hflip (1 : Fin 6) (1 : Fin 4) (by decide) (Or.inr rfl)
    · exact hflip (3 : Fin 6) (2 : Fin 4) (by decide) (Or.inr rfl)
    · exact hflip (4 : Fin 6) (3 : Fin 4) (by decide) (Or.inr rfl)
  have h10 : 10 ≤ N.card := by
    have := Finset.card_le_card hrange
    simpa using this
  have hsz : C.gates.length ≤ 10 := hsize
  by_cases heq1 : N.card = 1 + C.gates.length
  · exact no_strongFree hrange hsolo hF_rep (hSF heq1)
  · have hN10 : N.card = 10 := by omega
    have hg10 : C.gates.length = 10 := by omega
    have hNeq : N = Finset.range 10 :=
      (Finset.eq_of_subset_of_card_le hrange (by simp [hN10])).symm
    rcases hOC (by omega) with hsf | ⟨B, hoc⟩
    · exact no_strongFree hrange hsolo hF_rep hsf
    · rw [hNeq] at hoc
      exact no_oneCenter hsolo hF_rep hoc

end PEqualNP.Outside.L_meta_8299

theorem PEqualNP.Outside.L_meta_8299 :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 6) (v : Fin 4) => (13124385 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  exact PEqualNP.Outside.L_meta_8299.main_proof
