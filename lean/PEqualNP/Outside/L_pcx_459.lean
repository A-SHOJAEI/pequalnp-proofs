import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_459

open MvPolynomial PEqualNP.ProofComplexity

section toolkit

variable {σ τ : Type}

theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega

theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)

theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

theorem pcRefutable_no_common_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (h : PCRefutable F B) : ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := pcDerivable_eval_eq_zero h a ha
  simp at this

theorem totalDegree_bind₁_le (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ (ZMod 2)) :
    (bind₁ φ p).totalDegree ≤ T * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ a.support, (φ i ^ a i).totalDegree
      ≤ ∑ i ∈ a.support, T * a i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hφ i))
    _ = T * ∑ i ∈ a.support, a i := by rw [Finset.mul_sum]
    _ ≤ T * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree ha)

theorem pcDerivable_replay {F : Set (MvPolynomial σ (ZMod 2))}
    {G : Set (MvPolynomial τ (ZMod 2))} {T D s : ℕ}
    (φ : σ → MvPolynomial τ (ZMod 2)) (hφ : ∀ j, (φ j).totalDegree ≤ T)
    (w : MvPolynomial τ (ZMod 2)) (hw : w.totalDegree ≤ s)
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G (T * D + s) (w * bind₁ φ a))
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F D p) :
    PCDerivable G (T * D + s) (w * bind₁ φ p) := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add, mul_add]
    exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simpa using PCDerivable.zero
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    have hrw : w * bind₁ φ (X j * p) = φ j * (w * bind₁ φ p) := by
      rw [map_mul, bind₁_X_right]
      ring
    rw [hrw]
    have hb := totalDegree_bind₁_le φ hφ p
    have hwb : (w * bind₁ φ p).totalDegree ≤ s + T * p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hw hb)
    have hbound : (φ j).totalDegree + (w * bind₁ φ p).totalDegree ≤ T * D + s := by
      have h1 : T * (1 + p.totalDegree) ≤ T * D :=
        Nat.mul_le_mul_left _ (hXp ▸ hdeg)
      have h2 := hφ j
      rw [mul_add, mul_one] at h1
      omega
    have := pcDerivable_mul_left ih (φ j)
    rwa [max_eq_left hbound] at this

end toolkit

section boolvanish

variable {σ : Type}

noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v

noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a

theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]

theorem boolDerivable_monomial (d : ℕ) :
    ∀ (n : ℕ) (a : σ →₀ ℕ), (a.sum fun _ e => e) = n → n ≤ d →
      PCDerivable (boolAxioms σ) d (monomial a 1 + monomial (mlin a) 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn hd
  by_cases hall : ∀ v, a v ≤ 1
  · have : mlin a = a := by
      ext v; rw [mlin_apply]; have := hall v; omega
    rw [this, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact .zero
  simp only [not_forall, not_le] at hall
  obtain ⟨v, hv⟩ := hall
  set b := a - Finsupp.single v 2 with hb
  have ha : a = b + Finsupp.single v 2 := by
    ext w
    simp only [hb, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  set a' := b + Finsupp.single v 1 with ha'
  have hsum : ∀ c : σ →₀ ℕ, ∀ k, ((c + Finsupp.single v k).sum fun _ e => e)
      = (c.sum fun _ e => e) + k := by
    intro c k
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hmlin : mlin a' = mlin a := by
    ext w
    simp only [mlin_apply, ha, ha', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hna : (a.sum fun _ e => e) = (b.sum fun _ e => e) + 2 := by rw [ha, hsum]
  have hna' : (a'.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by rw [ha', hsum]
  have hstep : PCDerivable (boolAxioms σ) d (monomial a 1 + monomial a' 1) := by
    have hid : monomial a (1 : ZMod 2) + monomial a' 1
        = monomial b 1 * (X v * X v + X v) := by
      rw [mul_add, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
        ← Finsupp.single_add, ha, ha', one_mul, one_mul]
    rw [hid]
    have hax : PCDerivable (boolAxioms σ) d (X v * X v + X v) := by
      refine .ax ⟨v, rfl⟩ ?_
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · rw [totalDegree_X]; omega
    refine pcDerivable_monomial_mul b hax ?_
    have : (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
      · rw [totalDegree_X]; omega
    omega
  have hrest := ih _ (by omega) a' rfl (by omega)
  rw [hmlin] at hrest
  have := PCDerivable.add hstep hrest
  have e : monomial a (1 : ZMod 2) + monomial a' 1 + (monomial a' 1 + monomial (mlin a) 1)
      = monomial a 1 + monomial (mlin a) 1 := by
    rw [add_assoc, ← add_assoc (monomial a' 1), ← two_smul (ZMod 2) (monomial a' 1),
      show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  rwa [e] at this

theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
    (hq : ∀ a ∈ q.support, ∀ v, a v ≤ 1) (h0 : ∀ x : σ → ZMod 2, eval x q = 0) : q = 0 := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_finset_rename q
  have hinj : Function.Injective (Subtype.val : s → σ) := Subtype.val_injective
  have hr : r = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero s (ZMod 2) r (fun y => ?_) ?_
    · have := h0 (fun v => if h : v ∈ s then y ⟨v, h⟩ else 0)
      rw [eval_rename] at this
      have hy : ((fun v => if h : v ∈ s then y ⟨v, h⟩ else 0) ∘ Subtype.val) = y := by
        funext w
        simp
      rwa [hy] at this
    · rw [mem_restrictDegree]
      intro c hc i
      have hc' : Finsupp.mapDomain Subtype.val c ∈ (rename Subtype.val r).support := by
        rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
        exact mem_support_iff.mp hc
      have := hq _ hc' i
      rw [Finsupp.mapDomain_apply_of_injective hinj] at this
      simpa using this
  rw [hr, map_zero]

theorem vanish_derivable : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p := by
  classical
  intro σ F d p hF hd hvan
  set p' : MvPolynomial σ (ZMod 2) :=
    ∑ a ∈ p.support, monomial (mlin a) (p.coeff a) with hp'
  have hcoeff : ∀ a ∈ p.support, p.coeff a = 1 := by
    intro a ha
    have h0 : p.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize p.coeff a = c at h0
    revert h0; revert c; decide
  have hder : PCDerivable (boolAxioms σ) d (p + p') := by
    have : p + p' = ∑ a ∈ p.support, (monomial a 1 + monomial (mlin a) 1) := by
      conv_lhs => rw [p.as_sum]
      rw [hp', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hcoeff a ha]
    rw [this]
    refine pcDerivable_sum _ _ fun a ha => boolDerivable_monomial d _ a rfl ?_
    exact (le_totalDegree ha).trans hd
  have hbool : ∀ x : σ → ZMod 2, ∀ f ∈ boolAxioms σ, eval x f = 0 := by
    rintro x f ⟨v, rfl⟩
    simp only [map_add, map_mul, eval_X]
    generalize x v = c
    revert c; decide
  have hp'0 : p' = 0 := by
    refine eq_zero_of_multilinear p' ?_ ?_
    · intro c hc v
      obtain ⟨a, -, hca⟩ := Finset.mem_biUnion.mp (support_sum hc)
      rw [support_monomial] at hca
      split_ifs at hca
      · simp at hca
      · rw [Finset.mem_singleton.mp hca, mlin_apply]; omega
    · intro x
      have h1 := pcDerivable_eval_eq_zero hder x (hbool x)
      rwa [map_add, hvan x, zero_add] at h1
  have hpp : p = p + p' := by rw [hp'0, add_zero]
  rw [hpp]
  refine pcDerivable_mono hder le_rfl ?_
  rintro f ⟨v, rfl⟩
  exact hF v

end boolvanish

theorem deg_le {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) : p.totalDegree ≤ B := by
  induction h with
  | ax _ hdeg => exact hdeg
  | zero => simp
  | add _ _ ih1 ih2 => exact (totalDegree_add _ _).trans (max_le ih1 ih2)
  | mulX j _ hdeg _ => exact hdeg

theorem transfer {σ : Type} {G H : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (hax : ∀ a ∈ G, a.totalDegree ≤ D → PCDerivable H D a)
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable G D p) : PCDerivable H D p := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih hdeg

theorem transfer_rename {σ τ : Type} (f : σ → τ) {G : Set (MvPolynomial σ (ZMod 2))}
    {H : Set (MvPolynomial τ (ZMod 2))} {D : ℕ}
    (hax : ∀ a ∈ G, a.totalDegree ≤ D → PCDerivable H D (rename f a))
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable G D p) :
    PCDerivable H D (rename f p) := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => simpa using (PCDerivable.zero : PCDerivable H D 0)
  | add _ _ ih1 ih2 =>
    rw [map_add]
    exact .add ih1 ih2
  | @mulX j q _ hdeg ih =>
    have e : rename f (X j * q) = X (f j) * rename f q := by rw [map_mul, rename_X]
    rw [e]
    refine .mulX (f j) ih ?_
    rw [← e]
    exact (totalDegree_rename_le f _).trans hdeg

theorem prod_der {σ : Type} {F S T : Set (MvPolynomial σ (ZMod 2))} {B0 B1 : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (hp : PCDerivable (F ∪ S) B0 p) :
    ∀ {q : MvPolynomial σ (ZMod 2)}, PCDerivable (F ∪ T) B1 q →
      PCDerivable (F ∪ {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}) (B0 + B1) (p * q) := by
  induction hp with
  | @ax p hp hdeg =>
    intro q hq
    rcases hp with hpF | hpS
    · have hqd := deg_le hq
      have h1 : PCDerivable (F ∪ {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}) (B0 + B1) p :=
        .ax (Or.inl hpF) (by omega)
      have h2 := pcDerivable_mul_left h1 q
      rw [mul_comm]
      exact pcDerivable_mono h2 (max_le le_rfl (by omega)) subset_rfl
    · induction hq with
      | @ax q hq hqdeg =>
        rcases hq with hqF | hqT
        · have h1 : PCDerivable (F ∪ {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}) (B0 + B1) q :=
            .ax (Or.inl hqF) (by omega)
          exact pcDerivable_mono (pcDerivable_mul_left h1 p) (max_le le_rfl (by omega))
            subset_rfl
        · exact .ax (Or.inr ⟨p, hpS, q, hqT, rfl⟩)
            ((totalDegree_mul _ _).trans (by omega))
      | zero => simpa using (PCDerivable.zero :
          PCDerivable (F ∪ {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}) (B0 + B1) 0)
      | add _ _ ih1 ih2 =>
        rw [mul_add]
        exact .add ih1 ih2
      | @mulX j q _ hqdeg ih =>
        have e : p * (X j * q) = X j * (p * q) := by ring
        rw [e]
        refine .mulX j ih ?_
        rw [← e]
        exact (totalDegree_mul _ _).trans (by omega)
  | zero =>
    intro q _
    simpa using (PCDerivable.zero :
      PCDerivable (F ∪ {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}) (B0 + B1) 0)
  | add _ _ ih1 ih2 =>
    intro q hq
    rw [add_mul]
    exact .add (ih1 hq) (ih2 hq)
  | @mulX j p _ hdeg ih =>
    intro q hq
    have hqd := deg_le hq
    have e : X j * p * q = X j * (p * q) := by ring
    rw [e]
    refine .mulX j (ih hq) ?_
    rw [← e]
    exact (totalDegree_mul _ _).trans (by omega)

theorem comb {σ : Type} {G : Set (MvPolynomial σ (ZMod 2))}
    (hB : ∀ v : σ, X v * X v + X v ∈ G) {D N : ℕ} (t : MvPolynomial σ (ZMod 2))
    (g r : Fin N → MvPolynomial σ (ZMod 2)) (hr : ∀ k, r k ∈ G)
    (hdeg : ∀ k, (g k).totalDegree + (r k).totalDegree ≤ D) (ht : t.totalDegree ≤ D)
    (hev : ∀ x : σ → ZMod 2, eval x t = ∑ k, eval x (g k) * eval x (r k)) :
    PCDerivable G D t := by
  have hs : PCDerivable G D (∑ k, g k * r k) := by
    refine pcDerivable_sum _ _ fun k _ => ?_
    have h1 : PCDerivable G D (r k) := .ax (hr k) (by have := hdeg k; omega)
    exact pcDerivable_mono (pcDerivable_mul_left h1 (g k)) (max_le le_rfl (hdeg k)) subset_rfl
  have hsd : (∑ k, g k * r k).totalDegree ≤ D :=
    totalDegree_finsetSum_le fun k _ => (totalDegree_mul _ _).trans (hdeg k)
  have hE : PCDerivable G D (t - ∑ k, g k * r k) := by
    refine vanish_derivable σ G D _ hB ((totalDegree_sub _ _).trans (max_le ht hsd)) ?_
    intro x
    rw [map_sub, hev x, map_sum]
    simp only [map_mul, sub_self]
  have e : (∑ k, g k * r k) + (t - ∑ k, g k * r k) = t := by ring
  have := PCDerivable.add hs hE
  rwa [e] at this

theorem deg_one_add {τ : Type} {q : MvPolynomial τ (ZMod 2)} {k : ℕ} (hq : q.totalDegree ≤ k) :
    (1 + q).totalDegree ≤ k :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)

theorem deg_mul_le {τ : Type} {p q : MvPolynomial τ (ZMod 2)} {k l : ℕ}
    (hp : p.totalDegree ≤ k) (hq : q.totalDegree ≤ l) : (p * q).totalDegree ≤ k + l :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)

theorem deg_add_le {τ : Type} {p q : MvPolynomial τ (ZMod 2)} {k : ℕ}
    (hp : p.totalDegree ≤ k) (hq : q.totalDegree ≤ k) : (p + q).totalDegree ≤ k :=
  (totalDegree_add _ _).trans (max_le hp hq)

theorem deg_ren {σ : Type} {p : MvPolynomial σ (ZMod 2)} {k : ℕ} (hp : p.totalDegree ≤ k) :
    (rename (Sum.inl : σ → σ ⊕ Unit) p).totalDegree ≤ k :=
  (totalDegree_rename_le _ _).trans hp

theorem key1 : ∀ A Bv H : ZMod 2, A * (1 + Bv) = (1 + Bv) * (A + H * Bv) := by decide

theorem key2 : ∀ Ai Bi Aj Bj H : ZMod 2,
    Ai * Bj + Aj * Bi = Bj * (Ai + H * Bi) + Bi * (Aj + H * Bj) := by decide

theorem key3 : ∀ Ai Bi Aj Bj : ZMod 2,
    Ai * (Aj + Bj) = Ai * (Ai * Bj + Aj * Bi) + Aj * (Ai * (1 + Bi)) := by decide

theorem key4 : ∀ Ai Bi Aj Bj : ZMod 2,
    Ai * (Aj + Bj) = Ai * (Aj * Bi + Ai * Bj) + Aj * (Ai * (1 + Bi)) := by decide

theorem key5 : ∀ Ai Bi : ZMod 2, Ai * (Ai + Bi) = Ai * (Ai * (1 + Bi)) := by decide

section
variable {σ : Type} {m d : ℕ} (F : Set (MvPolynomial σ (ZMod 2)))
  (a b : Fin m → MvPolynomial σ (ZMod 2))

theorem part1 (hB : ∀ v : σ, X v * X v + X v ∈ F)
    (hd : ∀ i, (a i).totalDegree ≤ d + 1 ∧ (b i).totalDegree ≤ d) (B : ℕ)
    (hr : PCRefutable (F ∪ Set.range (fun i => a i * (1 + b i)) ∪
      {z : MvPolynomial σ (ZMod 2) | ∃ i j : Fin m, i < j ∧ z = a i * b j + a j * b i}) B) :
    PCRefutable (Set.image (fun p : MvPolynomial σ (ZMod 2) =>
        rename (Sum.inl : σ → σ ⊕ Unit) p) F ∪
      {(X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) * X (Sum.inr ()) + X (Sum.inr ())} ∪
      Set.range (fun i => rename (Sum.inl : σ → σ ⊕ Unit) (a i) +
        (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
          rename (Sum.inl : σ → σ ⊕ Unit) (b i))) (max B (2 * d + 1)) := by
  set H : Set (MvPolynomial (σ ⊕ Unit) (ZMod 2)) := Set.image (fun p : MvPolynomial σ (ZMod 2) =>
        rename (Sum.inl : σ → σ ⊕ Unit) p) F ∪
      {(X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) * X (Sum.inr ()) + X (Sum.inr ())} ∪
      Set.range (fun i => rename (Sum.inl : σ → σ ⊕ Unit) (a i) +
        (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
          rename (Sum.inl : σ → σ ⊕ Unit) (b i)) with hH
  have hBH : ∀ u : σ ⊕ Unit, X u * X u + X u ∈ H := by
    rintro (v | ⟨⟩)
    · refine Or.inl (Or.inl ⟨_, hB v, ?_⟩)
      simp only [map_add, map_mul, rename_X]
    · exact Or.inl (Or.inr rfl)
  have hR : ∀ i, rename (Sum.inl : σ → σ ⊕ Unit) (a i) +
      (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
        rename (Sum.inl : σ → σ ⊕ Unit) (b i) ∈ H := fun i => Or.inr ⟨i, rfl⟩
  have hRd : ∀ i, (rename (Sum.inl : σ → σ ⊕ Unit) (a i) +
      (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
        rename (Sum.inl : σ → σ ⊕ Unit) (b i)).totalDegree ≤ d + 1 := fun i =>
    deg_add_le (deg_ren (hd i).1)
      ((deg_mul_le (totalDegree_X _).le (deg_ren (hd i).2)).trans (by omega))
  have h1 : PCDerivable _ (max B (2 * d + 1)) 1 :=
    pcDerivable_mono hr (le_max_left B (2 * d + 1)) subset_rfl
  have h2 := transfer_rename (Sum.inl : σ → σ ⊕ Unit) (H := H) ?_ h1
  · show PCDerivable _ _ 1
    simpa using h2
  intro p hp hpd
  rcases hp with (hpF | ⟨i, rfl⟩) | ⟨i, j, hij, rfl⟩
  · exact .ax (Or.inl (Or.inl ⟨p, hpF, rfl⟩)) ((totalDegree_rename_le _ _).trans hpd)
  · refine pcDerivable_mono (comb (D := 2 * d + 1) (N := 1) hBH _
      (fun _ => 1 + rename Sum.inl (b i)) (fun _ => _) (fun _ => hR i) ?_ ?_ ?_)
      (le_max_right _ _) subset_rfl
    · intro k
      have := deg_one_add (deg_ren (hd i).2)
      have := hRd i
      omega
    · exact (deg_ren (deg_mul_le (hd i).1 (deg_one_add (hd i).2))).trans (by omega)
    · intro x
      simp only [Fin.sum_univ_one, map_add, map_mul, map_one, eval_rename, eval_X]
      exact key1 _ _ _
  · refine pcDerivable_mono (comb (D := 2 * d + 1) (N := 2) hBH _
      ![rename Sum.inl (b j), rename Sum.inl (b i)]
      ![rename (Sum.inl : σ → σ ⊕ Unit) (a i) +
          (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
            rename (Sum.inl : σ → σ ⊕ Unit) (b i),
        rename (Sum.inl : σ → σ ⊕ Unit) (a j) +
          (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
            rename (Sum.inl : σ → σ ⊕ Unit) (b j)] ?_ ?_ ?_ ?_)
      (le_max_right _ _) subset_rfl
    · intro k
      fin_cases k
      · exact hR i
      · exact hR j
    · intro k
      fin_cases k
      · have := deg_ren (hd j).2
        have := hRd i
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        omega
      · have := deg_ren (hd i).2
        have := hRd j
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        omega
    · exact (deg_ren (deg_add_le (deg_mul_le (hd i).1 (hd j).2)
        (deg_mul_le (hd j).1 (hd i).2))).trans (by omega)
    · intro x
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_add, map_mul, eval_rename, eval_X]
      exact key2 _ _ _ _ _

theorem part2 (hB : ∀ v : σ, X v * X v + X v ∈ F)
    (hd : ∀ i, (a i).totalDegree ≤ d + 1 ∧ (b i).totalDegree ≤ d) (B0 B1 : ℕ)
    (h0 : PCRefutable (F ∪ Set.range a) B0)
    (h1 : PCRefutable (F ∪ Set.range (fun i => a i + b i)) B1) :
    PCRefutable (F ∪ Set.range (fun i => a i * (1 + b i)) ∪
      {z : MvPolynomial σ (ZMod 2) | ∃ i j : Fin m, i < j ∧ z = a i * b j + a j * b i})
      (max (B0 + B1) (3 * d + 2)) := by
  set W : Set (MvPolynomial σ (ZMod 2)) := F ∪ Set.range (fun i => a i * (1 + b i)) ∪
      {z : MvPolynomial σ (ZMod 2) | ∃ i j : Fin m, i < j ∧ z = a i * b j + a j * b i} with hW
  have hBW : ∀ v : σ, X v * X v + X v ∈ W := fun v => Or.inl (Or.inl (hB v))
  have hDg : ∀ i, a i * (1 + b i) ∈ W := fun i => Or.inl (Or.inr ⟨i, rfl⟩)
  have hDd : ∀ i, (a i * (1 + b i)).totalDegree ≤ 2 * d + 1 := fun i =>
    (deg_mul_le (hd i).1 (deg_one_add (hd i).2)).trans (by omega)
  have hpair : ∀ i j : Fin m, PCDerivable W (3 * d + 2) (a i * (a j + b j)) := by
    intro i j
    have ht : (a i * (a j + b j)).totalDegree ≤ 3 * d + 2 :=
      (deg_mul_le (hd i).1 (deg_add_le (hd j).1 ((hd j).2.trans (by omega)))).trans
        (by omega)
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine comb (N := 2) hBW _ ![a i, a j] ![a i * b j + a j * b i, a i * (1 + b i)]
        ?_ ?_ ht ?_
      · intro k
        fin_cases k
        · exact Or.inr ⟨i, j, hij, rfl⟩
        · exact hDg i
      · intro k
        fin_cases k
        · have := (deg_add_le (deg_mul_le (hd i).1 (hd j).2) (deg_mul_le (hd j).1 (hd i).2))
          have := (hd i).1
          simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
          omega
        · have := hDd i
          have := (hd j).1
          simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero]
          omega
      · intro x
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          map_add, map_mul, map_one]
        exact key3 _ _ _ _
    · refine comb (N := 1) hBW _ ![a i] ![a i * (1 + b i)] ?_ ?_ ht ?_
      · intro k
        fin_cases k
        exact hDg i
      · intro k
        fin_cases k
        have := hDd i
        have := (hd i).1
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        omega
      · intro x
        simp only [Fin.sum_univ_one, Matrix.cons_val_zero, map_add, map_mul, map_one]
        exact key5 _ _
    · refine comb (N := 2) hBW _ ![a i, a j] ![a j * b i + a i * b j, a i * (1 + b i)]
        ?_ ?_ ht ?_
      · intro k
        fin_cases k
        · exact Or.inr ⟨j, i, hij, rfl⟩
        · exact hDg i
      · intro k
        fin_cases k
        · have := (deg_add_le (deg_mul_le (hd j).1 (hd i).2) (deg_mul_le (hd i).1 (hd j).2))
          have := (hd i).1
          simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
          omega
        · have := hDd i
          have := (hd j).1
          simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero]
          omega
      · intro x
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          map_add, map_mul, map_one]
        exact key4 _ _ _ _
  have hp := prod_der (h0 : PCDerivable _ B0 1) (h1 : PCDerivable _ B1 1)
  rw [one_mul] at hp
  have hp' := pcDerivable_mono hp (le_max_left (B0 + B1) (3 * d + 2)) subset_rfl
  refine transfer ?_ hp'
  intro p hp hpd
  rcases hp with hpF | ⟨s, ⟨i, rfl⟩, t, ⟨j, rfl⟩, rfl⟩
  · exact .ax (Or.inl (Or.inl hpF)) hpd
  · exact pcDerivable_mono (hpair i j) (le_max_right _ _) subset_rfl

theorem spec (c : ZMod 2) (hc : c * c + c = 0) (G : Set (MvPolynomial σ (ZMod 2))) (B : ℕ)
    (hG : ∀ i, a i + C c * b i ∈ G) (hFG : F ⊆ G)
    (hr : PCRefutable (Set.image (fun p : MvPolynomial σ (ZMod 2) =>
        rename (Sum.inl : σ → σ ⊕ Unit) p) F ∪
      {(X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) * X (Sum.inr ()) + X (Sum.inr ())} ∪
      Set.range (fun i => rename (Sum.inl : σ → σ ⊕ Unit) (a i) +
        (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
          rename (Sum.inl : σ → σ ⊕ Unit) (b i))) B) :
    PCRefutable G B := by
  set φ : σ ⊕ Unit → MvPolynomial σ (ZMod 2) := Sum.elim X (fun _ => C c) with hφ
  have hφd : ∀ j, (φ j).totalDegree ≤ 1 := by
    rintro (v | u)
    · simp [hφ]
    · simp [hφ]
  have hcomp : φ ∘ (Sum.inl : σ → σ ⊕ Unit) = X := by
    funext v
    simp [hφ]
  have himg : ∀ p : MvPolynomial σ (ZMod 2), bind₁ φ (rename Sum.inl p) = p := by
    intro p
    rw [bind₁_rename, hcomp, bind₁_X_left]
    rfl
  have hh : bind₁ φ (X (Sum.inr ())) = C c := by simp [hφ]
  have h2 := pcDerivable_replay (T := 1) (s := 0) (G := G) φ hφd 1 (by simp) ?_ hr
  · show PCDerivable _ _ 1
    simpa using h2
  intro p hp hpd
  have hpd' : (bind₁ φ p).totalDegree ≤ B :=
    (totalDegree_bind₁_le φ hφd p).trans (by omega)
  simp only [Nat.add_zero, one_mul]
  rcases hp with (⟨f, hf, rfl⟩ | hpH) | ⟨i, rfl⟩
  · rw [himg] at hpd' ⊢
    exact .ax (hFG hf) hpd'
  · rw [Set.mem_singleton_iff] at hpH
    subst hpH
    have e : bind₁ φ ((X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) * X (Sum.inr ()) +
        X (Sum.inr ())) = 0 := by
      rw [map_add, map_mul, hh, ← map_mul, ← map_add, hc, map_zero]
    rw [e]
    exact .zero
  · have e : bind₁ φ (rename (Sum.inl : σ → σ ⊕ Unit) (a i) +
        (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
          rename (Sum.inl : σ → σ ⊕ Unit) (b i)) = a i + C c * b i := by
      rw [map_add, map_mul, himg, himg, hh]
    rw [e] at hpd' ⊢
    exact .ax (hG i) hpd'

theorem part3 (hB : ∀ v : σ, X v * X v + X v ∈ F)
    (hd : ∀ i, (a i).totalDegree ≤ d + 1 ∧ (b i).totalDegree ≤ d) (B : ℕ)
    (hr : PCRefutable (Set.image (fun p : MvPolynomial σ (ZMod 2) =>
        rename (Sum.inl : σ → σ ⊕ Unit) p) F ∪
      {(X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) * X (Sum.inr ()) + X (Sum.inr ())} ∪
      Set.range (fun i => rename (Sum.inl : σ → σ ⊕ Unit) (a i) +
        (X (Sum.inr ()) : MvPolynomial (σ ⊕ Unit) (ZMod 2)) *
          rename (Sum.inl : σ → σ ⊕ Unit) (b i))) B) :
    PCRefutable (F ∪ Set.range (fun i => a i * (1 + b i)) ∪
      {z : MvPolynomial σ (ZMod 2) | ∃ i j : Fin m, i < j ∧ z = a i * b j + a j * b i})
      (max (2 * B) (3 * d + 2)) := by
  have h0 : PCRefutable (F ∪ Set.range a) B :=
    spec F a b 0 (by decide) _ B (fun i => Or.inr ⟨i, by simp⟩) Set.subset_union_left hr
  have h1 : PCRefutable (F ∪ Set.range (fun i => a i + b i)) B :=
    spec F a b 1 (by decide) _ B (fun i => Or.inr ⟨i, by simp⟩) Set.subset_union_left hr
  have := part2 F a b hB hd B B h0 h1
  rwa [two_mul]

end

end PEqualNP.Outside.L_pcx_459

theorem PEqualNP.Outside.L_pcx_459 : (∀ (n m d : ℕ),
  let K := ZMod 2
  let V := Fin n
  let P := MvPolynomial V K
  let U := V ⊕ Unit
  let A := MvPolynomial U K
  let refP := @PEqualNP.ProofComplexity.PCRefutable V
  let refA := @PEqualNP.ProofComplexity.PCRefutable U
  let lift := fun p : P => MvPolynomial.rename (Sum.inl : V → U) p
  let h : A := MvPolynomial.X (Sum.inr ())
  ∀ (F : Set P) (a b : Fin m → P),
    (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
    (∀ i, (a i).totalDegree ≤ d+1 ∧ (b i).totalDegree ≤ d) →
    let hidden := Set.image lift F ∪ {h*h+h} ∪ Set.range (fun i => lift (a i) + h * lift (b i))
    let visible := F ∪ Set.range (fun i => a i * (1+b i)) ∪
      {z : P | ∃ i j : Fin m, i < j ∧ z = a i * b j + a j * b i}
    (∀ B, refP visible B → refA hidden (max B (2*d+1))) ∧
    (∀ B₀ B₁, refP (F ∪ Set.range a) B₀ →
      refP (F ∪ Set.range (fun i => a i+b i)) B₁ →
      refP visible (max (B₀+B₁) (3*d+2))) ∧
    ∀ B, refA hidden B → refP visible (max (2*B) (3*d+2))) := by
  intro n m d K V P U A refP refA lift h F a b hB hdeg hidden visible
  exact ⟨PEqualNP.Outside.L_pcx_459.part1 F a b hB hdeg,
    PEqualNP.Outside.L_pcx_459.part2 F a b hB hdeg,
    PEqualNP.Outside.L_pcx_459.part3 F a b hB hdeg⟩
