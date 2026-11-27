import Mathlib

/-!
# Common edges of lattice paths and Shankar's inequality

A word of length `m` is a map `Fin m → Bool`; `true` is a north step and `false` an east step.
**Convention.** The index `0` is the *last* letter of the word, i.e. the last step of the path,
and `Fin.tail x` is the word with its last letter removed. With this convention the number of
common edges `ce m x y` of the two paths is defined by recursion on the last step:
the last steps of two paths are the same edge exactly when they have the same direction and
the two paths without their last steps end at the same point, that is, have the same weight.
This is the append rule (Lemma 2.1(b) of the paper); `ce_cons` states it.

The main result is `shankar_inequality`: an admissible system of length `m` has
`∑ |A|^2 ≤ 2^m` (Shankar, Lemma 2.3 of arXiv:2607.23117; Theorem 2.6 of the paper).
`even_family_card_sq_le` derives the bound `|F|^2 ≤ 2^m` for a family whose members pairwise
share a number of edges of the parity of `m`; for paths from `(0,0)` to `(n,n)` this is
Shankar's bound `|F| ≤ 2^n` for even families.
-/

namespace LatticePaths

open Finset

/-- Words of length `m`; index `0` is the last letter. -/
abbrev Word (m : ℕ) := Fin m → Bool

/-- The weight of a word: its number of north steps. -/
def wt {m : ℕ} (x : Word m) : ℕ := (univ.filter fun i => x i = true).card

/-- The number of common edges of the paths of two words of length `m`. -/
def ce : (m : ℕ) → Word m → Word m → ℕ
  | 0, _, _ => 0
  | m + 1, x, y =>
      ce m (Fin.tail x) (Fin.tail y) +
        if x 0 = y 0 ∧ wt (Fin.tail x) = wt (Fin.tail y) then 1 else 0

theorem wt_cons {m : ℕ} (a : Bool) (u : Word m) :
    wt (Fin.cons a u : Word (m + 1)) = wt u + (if a = true then 1 else 0) := by
  unfold wt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- The append rule: adding a last step to both paths. -/
theorem ce_cons {m : ℕ} (a b : Bool) (u v : Word m) :
    ce (m + 1) (Fin.cons a u) (Fin.cons b v) =
      ce m u v + if a = b ∧ wt u = wt v then 1 else 0 := by
  simp [ce, Fin.tail_cons]

theorem ce_self : ∀ (m : ℕ) (x : Word m), ce m x x = m
  | 0, _ => rfl
  | m + 1, x => by simp [ce, ce_self m]

theorem ce_comm : ∀ (m : ℕ) (x y : Word m), ce m x y = ce m y x
  | 0, _, _ => rfl
  | m + 1, x, y => by
      simp only [ce, ce_comm m (Fin.tail x) (Fin.tail y)]
      congr 1
      by_cases h : x 0 = y 0 ∧ wt (Fin.tail x) = wt (Fin.tail y)
      · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

/-- Admissible systems (Definition 2.3 of the paper). The constancy in (A3) is stated as the
equality of the values on any two pairs. -/
structure Admissible (m : ℕ) (S : Finset (Finset (Word m))) : Prop where
  nonempty : ∀ A ∈ S, A.Nonempty
  disj : ∀ A ∈ S, ∀ A' ∈ S, A ≠ A' → Disjoint A A'
  wt_const : ∀ A ∈ S, ∀ x ∈ A, ∀ y ∈ A, wt x = wt y
  inner : ∀ A ∈ S, ∀ x ∈ A, ∀ y ∈ A, ((ce m x y : ℕ) : ZMod 2) = m
  cross : ∀ A ∈ S, ∀ A' ∈ S, A ≠ A' → ∀ x ∈ A, ∀ y ∈ A', ∀ x' ∈ A, ∀ y' ∈ A',
    ((ce m x y : ℕ) : ZMod 2) = ce m x' y'

/-- The norm `∑ |A|^2` of a system. -/
def norm {m : ℕ} (S : Finset (Finset (Word m))) : ℕ := ∑ A ∈ S, A.card ^ 2

/-- Appending the last letter `a`. -/
def consW {m : ℕ} (a : Bool) (u : Word m) : Word (m + 1) := Fin.cons (α := fun _ => Bool) a u

theorem consW_injective {m : ℕ} (a : Bool) : Function.Injective (consW (m := m) a) := by
  intro u v h
  exact Fin.cons_right_injective (α := fun _ => Bool) a h

/-- The words `u` with `u` followed by the last letter `a` in `A`. -/
noncomputable def sl {m : ℕ} (A : Finset (Word (m + 1))) (a : Bool) : Finset (Word m) :=
  A.preimage (consW a) (consW_injective a).injOn

theorem mem_sl {m : ℕ} {A : Finset (Word (m + 1))} {a : Bool} {u : Word m} :
    u ∈ sl A a ↔ (Fin.cons a u : Word (m + 1)) ∈ A := by
  simp [sl, consW]

theorem card_sl {m : ℕ} (A : Finset (Word (m + 1))) (a : Bool) :
    (sl A a).card = (A.filter fun x => x 0 = a).card := by
  unfold sl
  rw [Finset.card_preimage]
  congr 1
  ext x
  simp only [Finset.mem_filter, Set.mem_range]
  constructor
  · rintro ⟨hx, u, rfl⟩
    exact ⟨hx, by simp [consW]⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, Fin.tail x, ?_⟩
    rw [← h]
    unfold consW
    exact Fin.cons_self_tail x

theorem card_eq_sl {m : ℕ} (A : Finset (Word (m + 1))) :
    A.card = (sl A false).card + (sl A true).card := by
  rw [card_sl, card_sl, ← Finset.card_filter_add_card_filter_not (s := A) (fun x => x 0 = false)]
  congr 2
  ext x
  cases x 0 <;> simp

section step

open Classical

variable {m : ℕ} {S : Finset (Finset (Word (m + 1)))}

/-- A class is split if both of its last letters occur. -/
def Split (A : Finset (Word (m + 1))) : Prop := (sl A false).Nonempty ∧ (sl A true).Nonempty

theorem wt_ne_of_ne {a b : Bool} (hab : a ≠ b) (u v : Word m)
    (h : wt (Fin.cons a u : Word (m + 1)) = wt (Fin.cons b v : Word (m + 1))) : wt u ≠ wt v := by
  rw [wt_cons, wt_cons] at h
  intro h'
  rw [h'] at h
  cases a <;> cases b <;> simp_all

/-- Lemma 2.4 of the paper. -/
theorem split_lemma (hS : Admissible (m + 1) S) {A A' : Finset (Word (m + 1))} (hA : A ∈ S)
    (hA' : A' ∈ S) {a b : Bool} (hab : a ≠ b) {u : Word m} (hu : (Fin.cons a u : Word _) ∈ A)
    (hu' : (Fin.cons b u : Word _) ∈ A') (v : Word m) : (Fin.cons b v : Word _) ∉ A := by
  intro hv
  have hne : A ≠ A' := by
    rintro rfl
    exact wt_ne_of_ne hab u u (hS.wt_const A hA _ hu _ hu') rfl
  have h1 := hS.inner A hA _ hu _ hv
  rw [ce_cons, if_neg (fun h => hab h.1)] at h1
  simp only [add_zero] at h1
  have h2 := hS.cross A hA A' hA' hne _ hv _ hu' _ hu _ hu'
  have hw : wt v ≠ wt u := fun h => wt_ne_of_ne hab u v (hS.wt_const A hA _ hu _ hv) h.symm
  rw [ce_cons, ce_cons, if_neg (fun h => hw h.2), if_neg (fun h => hab h.1), ce_self,
    ce_comm] at h2
  simp only [add_zero] at h2
  rw [h2] at h1
  push_cast at h1
  have : (1 : ZMod 2) = 0 := by linear_combination -h1
  exact absurd this (by decide)

/-- The index set of the system `G_e`. -/
noncomputable def Idx (S : Finset (Finset (Word (m + 1)))) (e : Bool) :
    Finset (Finset (Word (m + 1)) × Bool) :=
  (S ×ˢ univ).filter fun p => (sl p.1 p.2).Nonempty ∧ (p.2 = e ∨ Split p.1)

/-- The system `G_e` of length `m` (equation (2.2) of the paper). -/
noncomputable def G (S : Finset (Finset (Word (m + 1)))) (e : Bool) : Finset (Finset (Word m)) :=
  (Idx S e).image fun p => sl p.1 p.2

theorem mem_Idx {e : Bool} {p : Finset (Word (m + 1)) × Bool} :
    p ∈ Idx S e ↔ p.1 ∈ S ∧ (sl p.1 p.2).Nonempty ∧ (p.2 = e ∨ Split p.1) := by
  simp [Idx]

theorem idx_disjoint (hS : Admissible (m + 1) S) {e : Bool} {p q : Finset (Word (m + 1)) × Bool}
    (hp : p ∈ Idx S e) (hq : q ∈ Idx S e) (hpq : p ≠ q) : Disjoint (sl p.1 p.2) (sl q.1 q.2) := by
  obtain ⟨A, a⟩ := p
  obtain ⟨A', b⟩ := q
  rw [mem_Idx] at hp hq
  rw [Finset.disjoint_left]
  intro u hu hu'
  rw [mem_sl] at hu hu'
  by_cases hAA : A = A'
  · subst hAA
    have hab : a ≠ b := fun h => hpq (by rw [h])
    exact wt_ne_of_ne hab u u (hS.wt_const A hp.1 _ hu _ hu') rfl
  · by_cases hab : a = b
    · subst hab
      exact Finset.disjoint_left.mp (hS.disj A hp.1 A' hq.1 hAA) hu hu'
    · -- neither class is split
      have h1 : ¬ Split A := by
        intro hs
        have hb : (sl A b).Nonempty := by
          cases b with
          | false => exact hs.1
          | true => exact hs.2
        obtain ⟨v, hv⟩ := hb
        exact split_lemma hS hp.1 hq.1 hab hu hu' v (mem_sl.mp hv)
      have h2 : ¬ Split A' := by
        intro hs
        have ha : (sl A' a).Nonempty := by
          cases a with
          | false => exact hs.1
          | true => exact hs.2
        obtain ⟨v, hv⟩ := ha
        exact split_lemma hS hq.1 hp.1 (Ne.symm hab) hu' hu v (mem_sl.mp hv)
      rcases hp.2.2 with h | h
      · rcases hq.2.2 with h' | h'
        · exact hab (h.trans h'.symm)
        · exact h2 h'
      · exact h1 h

theorem idx_injOn (hS : Admissible (m + 1) S) (e : Bool) :
    Set.InjOn (fun p : Finset (Word (m + 1)) × Bool => sl p.1 p.2) (Idx S e) := by
  intro p hp q hq hpq
  by_contra hne
  have hd := idx_disjoint hS hp hq hne
  simp only at hpq
  rw [hpq, disjoint_self, Finset.bot_eq_empty] at hd
  have : (sl q.1 q.2).Nonempty := (mem_Idx.mp hq).2.1
  rw [hd] at this
  exact Finset.not_nonempty_empty this

theorem norm_G (hS : Admissible (m + 1) S) (e : Bool) :
    norm (G S e) = ∑ p ∈ Idx S e, (sl p.1 p.2).card ^ 2 := by
  unfold norm G
  rw [Finset.sum_image (fun p hp q hq h => idx_injOn hS e hp hq h)]

theorem admissible_G (hS : Admissible (m + 1) S) (e : Bool) : Admissible m (G S e) := by
  constructor
  · intro X hX
    simp only [G, Finset.mem_image] at hX
    obtain ⟨p, hp, rfl⟩ := hX
    exact (mem_Idx.mp hp).2.1
  · intro X hX X' hX' hne
    simp only [G, Finset.mem_image] at hX hX'
    obtain ⟨p, hp, rfl⟩ := hX
    obtain ⟨q, hq, rfl⟩ := hX'
    exact idx_disjoint hS hp hq (fun h => hne (by rw [h]))
  · intro X hX u hu v hv
    simp only [G, Finset.mem_image] at hX
    obtain ⟨⟨A, a⟩, hp, rfl⟩ := hX
    rw [mem_Idx] at hp
    rw [mem_sl] at hu hv
    have h := hS.wt_const A hp.1 _ hu _ hv
    rw [wt_cons, wt_cons] at h
    omega
  · intro X hX u hu v hv
    simp only [G, Finset.mem_image] at hX
    obtain ⟨⟨A, a⟩, hp, rfl⟩ := hX
    rw [mem_Idx] at hp
    rw [mem_sl] at hu hv
    have hw := hS.wt_const A hp.1 _ hu _ hv
    rw [wt_cons, wt_cons] at hw
    have h := hS.inner A hp.1 _ hu _ hv
    rw [ce_cons, if_pos ⟨rfl, by omega⟩] at h
    push_cast at h
    linear_combination h
  · intro X hX X' hX' hne u hu v hv u' hu' v' hv'
    simp only [G, Finset.mem_image] at hX hX'
    obtain ⟨⟨A, a⟩, hp, rfl⟩ := hX
    obtain ⟨⟨A', b⟩, hq, rfl⟩ := hX'
    rw [mem_Idx] at hp hq
    rw [mem_sl] at hu hv hu' hv'
    have hwu : wt u = wt u' := by
      have h := hS.wt_const A hp.1 _ hu _ hu'
      rw [wt_cons, wt_cons] at h; omega
    have hwv : wt v = wt v' := by
      have h := hS.wt_const A' hq.1 _ hv _ hv'
      rw [wt_cons, wt_cons] at h; omega
    have key : ((ce (m + 1) (Fin.cons a u) (Fin.cons b v) : ℕ) : ZMod 2) =
        ce (m + 1) (Fin.cons a u') (Fin.cons b v') := by
      by_cases hAA : A = A'
      · subst hAA
        rw [hS.inner A hp.1 _ hu _ hv, hS.inner A hp.1 _ hu' _ hv']
      · exact hS.cross A hp.1 A' hq.1 hAA _ hu _ hv _ hu' _ hv'
    rw [ce_cons, ce_cons] at key
    have hc : (a = b ∧ wt u = wt v) ↔ (a = b ∧ wt u' = wt v') := by
      rw [hwu, hwv]
    by_cases h : a = b ∧ wt u = wt v
    · rw [if_pos h, if_pos (hc.mp h)] at key
      push_cast at key
      linear_combination key
    · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))] at key
      simp only [add_zero] at key
      exact key

/-- Proposition 2.5(ii) of the paper: `‖S‖ ≤ ‖G_0‖ + ‖G_1‖`. -/
theorem norm_le_G (hS : Admissible (m + 1) S) : norm S ≤ norm (G S false) + norm (G S true) := by
  rw [norm_G hS, norm_G hS]
  unfold Idx norm
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_product, Finset.sum_product,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro A hA
  simp only [Fintype.sum_bool]
  have hcard := card_eq_sl A
  set c0 := (sl A false).card with hc0
  set c1 := (sl A true).card with hc1
  rw [hcard]
  by_cases h0 : (sl A false).Nonempty <;> by_cases h1 : (sl A true).Nonempty
  · have hs : Split A := ⟨h0, h1⟩
    simp only [h0, h1, hs, or_true, and_self, if_true]
    nlinarith [sq_nonneg ((c0 : ℤ) - c1)]
  · have hs : ¬ Split A := fun h => h1 h.2
    have : c1 = 0 := by rw [hc1, Finset.card_eq_zero]; exact Finset.not_nonempty_iff_eq_empty.mp h1
    simp [h0, h1, hs, this]
  · have hs : ¬ Split A := fun h => h0 h.1
    have : c0 = 0 := by rw [hc0, Finset.card_eq_zero]; exact Finset.not_nonempty_iff_eq_empty.mp h0
    simp [h0, h1, hs, this]
  · exfalso
    have hA0 := hS.nonempty A hA
    rw [← Finset.card_pos, hcard] at hA0
    have e0 : c0 = 0 := by
      rw [hc0]; exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h0)
    have e1 : c1 = 0 := by
      rw [hc1]; exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h1)
    omega

end step

theorem norm_le_one_of_zero (S : Finset (Finset (Word 0))) (hS : Admissible 0 S) : norm S ≤ 1 := by
  unfold norm
  have hc : ∀ A ∈ S, A.card ≤ 1 := fun A _ => by
    calc A.card ≤ (univ : Finset (Word 0)).card := Finset.card_le_univ A
      _ = 1 := by simp
  calc ∑ A ∈ S, A.card ^ 2 ≤ ∑ A ∈ S, A.card := by
        apply Finset.sum_le_sum; intro A hA
        have := hc A hA
        interval_cases A.card <;> simp
    _ = (S.biUnion id).card := by
        rw [Finset.card_biUnion]; · rfl
        intro A hA A' hA' hne; exact hS.disj A hA A' hA' hne
    _ ≤ (univ : Finset (Word 0)).card := Finset.card_le_univ _
    _ = 1 := by simp

/-- **Shankar's inequality** (Theorem 2.6 of the paper). -/
theorem shankar_inequality : ∀ (m : ℕ) (S : Finset (Finset (Word m))), Admissible m S →
    norm S ≤ 2 ^ m
  | 0, S, hS => by simpa using norm_le_one_of_zero S hS
  | m + 1, S, hS => by
      calc norm S ≤ norm (G S false) + norm (G S true) := norm_le_G hS
        _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add (shankar_inequality m _ (admissible_G hS false))
            (shankar_inequality m _ (admissible_G hS true))
        _ = 2 ^ (m + 1) := by ring

/-- A family of words of one weight whose members pairwise share a number of edges congruent to
`m` modulo `2` satisfies `|F|^2 ≤ 2^m`. For `m = 2n` and weight `n` (paths from `(0,0)` to
`(n,n)` with pairwise even numbers of common edges) this is Shankar's bound `|F| ≤ 2^n`. -/
theorem even_family_card_sq_le {m : ℕ} (F : Finset (Word m)) (hF : F.Nonempty)
    (hw : ∀ x ∈ F, ∀ y ∈ F, wt x = wt y)
    (hpar : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ((ce m x y : ℕ) : ZMod 2) = m) :
    F.card ^ 2 ≤ 2 ^ m := by
  have hS : Admissible m {F} := by
    constructor
    · intro A hA; rw [Finset.mem_singleton] at hA; subst hA; exact hF
    · intro A hA A' hA' hne
      rw [Finset.mem_singleton] at hA hA'; exact absurd (hA.trans hA'.symm) hne
    · intro A hA; rw [Finset.mem_singleton] at hA; subst hA; exact hw
    · intro A hA x hx y hy
      rw [Finset.mem_singleton] at hA; subst hA
      by_cases hxy : x = y
      · subst hxy; rw [ce_self]
      · exact hpar x hx y hy hxy
    · intro A hA A' hA' hne
      rw [Finset.mem_singleton] at hA hA'; exact absurd (hA.trans hA'.symm) hne
  simpa [norm] using shankar_inequality m {F} hS

theorem even_family_square {n : ℕ} (F : Finset (Word (2 * n))) (hw : ∀ x ∈ F, wt x = n)
    (hpar : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ((ce (2 * n) x y : ℕ) : ZMod 2) = 0) :
    F.card ≤ 2 ^ n := by
  rcases F.eq_empty_or_nonempty with h | h
  · simp [h]
  have := even_family_card_sq_le F h (fun x hx y hy => by rw [hw x hx, hw y hy])
    (fun x hx y hy hxy => by
      rw [hpar x hx y hy hxy]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul])
  have h4 : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by ring
  rw [h4] at this
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this

end LatticePaths
