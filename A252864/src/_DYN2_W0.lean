/-
  A252864 — `_DYN2_W0.lean`.  WIERSZ `j = 0` TWIERDZENIA `[R3]`:  `n₁′ = n₅ + 7`.
  Lean 4, BEZ Mathlib.
  ⛔ ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.

  To jedyny wiersz z NAPŁYWEM — wektor afiniczny `w = (7,0,0,0,0)`.
-/
import «_DYN2_B»
import «_DYN2_Naplyw»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat A252864.MostL A252864.DYN

/-! ## 0.  Lista siedmiu węzłów napływu `W(n)` w koordynatach `(j,k)` -/

/-- `W(n)` jawnie: głowa `(a,b) = (n−2,1)`, ogon `c = 2..7` daje `(n+c−3, n+2c−3)`. -/
def Wlist (n : Nat) : List Node :=
  [(n-2, n-1), (n-1, n+1), (n, n+3), (n+1, n+5), (n+2, n+7), (n+3, n+9), (n+4, n+11)]

theorem Wlist_len (n : Nat) : (Wlist n).length = 7 := rfl

theorem Wlist_nodup (n : Nat) (hn : 10 ≤ n) : (Wlist n).Nodup := by
  simp only [Wlist, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, Prod.mk.injEq, and_true, not_or, not_false_eq_true]
  omega

/-- Każdy węzeł `W(n)` ma `b ≤ 7`, czyli `k < j + 8`. -/
theorem Wlist_small (n : Nat) (hn : 10 ≤ n) (w : Node) (hw : w ∈ Wlist n) : w.2 < w.1 + 8 := by
  simp only [Wlist, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (dsimp only; omega)

/-- Charakteryzacja członkostwa w `W(n)` we współrzędnych `(a,b)`. -/
theorem mem_Wlist (n a b : Nat) (hn : 10 ≤ n) :
    (a, a + b) ∈ Wlist n ↔ ((b = 1 ∧ a = n - 2) ∨ (2 ≤ b ∧ b ≤ 7 ∧ a = n + b - 3)) := by
  simp only [Wlist, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  omega

/-! ## 1.  Mosty klas na `klab` -/

theorem klab_eq0 (a b : Nat) : klab a b = 0 ↔ C0 a b := by
  rw [← klR_klab]; exact klR_eq0 a b

theorem klab_eq4 (a b : Nat) (ha : 1 ≤ a) : klab a b = 4 ↔ ¬ C3 a b := by
  rw [← klR_klab]; exact klR_eq4 a b ha

/-- Klasa 4 ⇒ węzeł NIE leży w `I₁` (łańcuch zagnieżdżeń `C0 → C1 → C2 → C3`). -/
theorem kl4_notC0 (a b : Nat) (ha : 1 ≤ a) (h : klab a b = 4) : ¬ C0 a b := by
  have h3 := (klab_eq4 a b ha).mp h
  intro h0
  exact h3 (nest_23 a b ha (nest_12 a b ha (nest_01 a b ha h0)))

/-! ## 2.  NORMALIZACJA — element listy `vv` w koordynatach `(a,b)` -/

theorem inRk_iff (n : Nat) (k : Fin 5) (z : Node) :
    (z ∈ (run n).2.1 ∧ (8 ≤ z.1 && z.1 < z.2 && klR z == k) = true)
      ↔ ∃ a b, 8 ≤ a ∧ 1 ≤ b ∧ z = (a, a + b) ∧ L a (a + b) = n ∧ klab a b = k := by
  constructor
  · rintro ⟨hz, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨h8, hlt⟩, hcl⟩ := hp
    obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b, 8 ≤ a ∧ 1 ≤ b ∧ z = (a, a + b) := by
      refine ⟨z.1, z.2 - z.1, h8, by omega, ?_⟩
      have : z.1 + (z.2 - z.1) = z.2 := by omega
      rw [this]
    exact ⟨a, b, ha, hb, rfl, ((mem_gen_iff _ _).mp hz).2, by rw [← klR_klab]; exact hcl⟩
  · rintro ⟨a, b, ha, hb, rfl, hL, hcl⟩
    refine ⟨(mem_gen_iff _ _).mpr ⟨by omega, hL⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨ha, by omega⟩, by rw [klR_klab]; exact hcl⟩

/-! ## 3.  Siedem węzłów `W(n)` — poziom `n` i klasa `0` -/

theorem W_head_ok (m : Nat) : L (m + 8) (m + 8 + 1) = m + 10 ∧ klab (m + 8) 1 = 0 := by
  refine ⟨?_, (klab_eq0 _ _).mpr (b1_in_I1 (m + 8) (by omega))⟩
  have h := W_head_level (m + 10) (by omega)
  have e1 : m + 10 - 2 = m + 8 := by omega
  have e2 : m + 10 - 1 = m + 8 + 1 := by omega
  rw [e1, e2] at h
  exact h

theorem W_tail_ok (m c : Nat) (h2 : 2 ≤ c) (h7 : c ≤ 7) :
    L (m + 7 + c) (m + 7 + c + c) = m + 10 ∧ klab (m + 7 + c) c = 0 := by
  refine ⟨?_, (klab_eq0 _ _).mpr (C0_tail m c h2 h7)⟩
  have h := W_tail_level (m + 10) c (by omega) h2 h7
  have e1 : m + 10 + c - 3 = m + 7 + c := by omega
  have e2 : m + 10 + 2 * c - 3 = m + 7 + c + c := by omega
  rw [e1, e2] at h
  exact h

/-! ## 4.  ROZBIÓR `[R3]` DLA `j = 0` — obraz `childB` klasy 4 ⊍ napływ `W(n)` -/

theorem row0_mem (n : Nat) (hn : 10 ≤ n) (z : Node) :
    (z ∈ (run n).2.1 ∧ (8 ≤ z.1 && z.1 < z.2 && klR z == 0) = true)
      ↔ ((∃ q, (q ∈ (run (n-1)).2.1 ∧ (8 ≤ q.1 && q.1 < q.2 && klR q == 4) = true)
              ∧ childB q = z) ∨ z ∈ Wlist n) := by
  rw [inRk_iff]
  constructor
  · rintro ⟨a, b, ha, hb, rfl, hL, hcl⟩
    have hC0 : C0 a b := (klab_eq0 a b).mp hcl
    rcases Nat.lt_or_ge b 8 with hb7 | hb8
    · exact Or.inr ((mem_Wlist n a b hn).mpr (a_wyznaczone n a b hn ha hb (by omega) hL))
    · refine Or.inl ?_
      have hC2 : C2 a b := nest_12 a b (by omega) (nest_01 a b (by omega) hC0)
      have hpar : tparent a (a + b) = (b, a) := (parent_B_iff a b ha (by omega)).mpr hC2
      have hba : b < a := by
        have hw : wRodzic a b := duze_b_ma_rodzica a b ha hb8
        simp only [wRodzic, hpar] at hw
        exact hw.2
      obtain ⟨r, rfl⟩ : ∃ r, a = b + r := ⟨a - b, by omega⟩
      have hr : 1 ≤ r := by omega
      have hlv := tparent_lvl (b + r) (b + r + b) (by omega) (by omega)
      simp only [hpar] at hlv
      have hk4 : klab b r = 4 := by
        have hfin5 : ∀ x : Fin 5, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
        rcases hfin5 (klab b r) with h|h|h|h|h
        · exfalso
          have hC0br : C0 b r := (klab_eq0 b r).mp h
          have e : b + r + b = 2 * b + r := by omega
          have hpar' : tparent (b + r) (2 * b + r) = (b, b + r) := by rw [← e]; exact hpar
          exact ((R2_B b r (by omega)).mp hpar') hC0br
        · exfalso
          have hx := D3_B_I2 b r (by omega) hr h
          rw [hcl] at hx; exact absurd hx (by decide)
        · exfalso
          have hx := D3_B_I3 b r (by omega) hr h
          rw [hcl] at hx; exact absurd hx (by decide)
        · exfalso
          have hx := D3_B_I4 b r (by omega) hr h
          rw [hcl] at hx; exact absurd hx (by decide)
        · exact h
      refine ⟨(b, b + r), ?_, ?_⟩
      · rw [inRk_iff]
        exact ⟨b, r, by omega, hr, rfl, by omega, hk4⟩
      · simp only [childB, Prod.mk.injEq, and_true, true_and]
        all_goals omega
  · rintro (⟨q, hq, rfl⟩ | hw)
    · rw [inRk_iff] at hq
      obtain ⟨p, r, hp, hr, rfl, hqL, hqcl⟩ := hq
      have hnC0 : ¬ C0 p r := kl4_notC0 p r (by omega) hqcl
      have htc : IsTChild (p, p + r) (p + r, 2 * p + r) := (R2_B p r hp).mpr hnC0
      simp only [IsTChild] at htc
      have hlv := tparent_lvl (p + r) (2 * p + r) (by omega) (by omega)
      simp only [htc] at hlv
      refine ⟨p + r, p, by omega, by omega, ?_, ?_, D3_B_I5 p r hp hr hqcl⟩
      · simp only [childB, Prod.mk.injEq, and_true, true_and]
        all_goals omega
      · have e : p + r + p = 2 * p + r := by omega
        rw [e]; omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      simp only [Wlist, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨m+8, 1, by omega, by omega, by simp only [Prod.mk.injEq, and_true, true_and]; all_goals omega,
          (W_head_ok m).1, (W_head_ok m).2⟩
      · exact ⟨m+7+2, 2, by omega, by omega, by simp only [Prod.mk.injEq, and_true, true_and]; all_goals omega,
          (W_tail_ok m 2 (by omega) (by omega)).1, (W_tail_ok m 2 (by omega) (by omega)).2⟩
      · exact ⟨m+7+3, 3, by omega, by omega, by simp only [Prod.mk.injEq, and_true, true_and]; all_goals omega,
          (W_tail_ok m 3 (by omega) (by omega)).1, (W_tail_ok m 3 (by omega) (by omega)).2⟩
      · exact ⟨m+7+4, 4, by omega, by omega, by simp only [Prod.mk.injEq, and_true, true_and]; all_goals omega,
          (W_tail_ok m 4 (by omega) (by omega)).1, (W_tail_ok m 4 (by omega) (by omega)).2⟩
      · exact ⟨m+7+5, 5, by omega, by omega, by simp only [Prod.mk.injEq, and_true, true_and]; all_goals omega,
          (W_tail_ok m 5 (by omega) (by omega)).1, (W_tail_ok m 5 (by omega) (by omega)).2⟩
      · exact ⟨m+7+6, 6, by omega, by omega, by simp only [Prod.mk.injEq, and_true, true_and]; all_goals omega,
          (W_tail_ok m 6 (by omega) (by omega)).1, (W_tail_ok m 6 (by omega) (by omega)).2⟩
      · exact ⟨m+7+7, 7, by omega, by omega, by simp only [Prod.mk.injEq, and_true, true_and]; all_goals omega,
          (W_tail_ok m 7 (by omega) (by omega)).1, (W_tail_ok m 7 (by omega) (by omega)).2⟩

/-! ## 5.  WIERSZ `j = 0` TWIERDZENIA `[R3]`:  `n₁′ = n₅ + 7` -/

/-- **`thm:dynamics`, wiersz `j = 0`.**  Węzły klasy `I₁` na poziomie `n` to dokładnie
    B-dzieci węzłów klasy `I₅` z poziomu `n−1` ORAZ siedem węzłów NAPŁYWU `W(n)`.
    Siódemka to wektor afiniczny `w = (7,0,0,0,0)`. -/
theorem row0 (n : Nat) (hn : 10 ≤ n) : vv klR n 0 = vv klR (n-1) 4 + 7 := by
  have h : vv klR n 0 = vv klR (n-1) 4 + ([] : List Node).length + (Wlist n).length := by
    unfold vv
    refine LICZ.length_split3' _ _ [] (Wlist n) childB childB
      (LICZ.nodup_filter _ _ (Bfs.gen_nodup n))
      (LICZ.nodup_filter _ _ (Bfs.gen_nodup (n-1)))
      (by simp) (Wlist_nodup n hn) childB_inj childB_inj
      (by intro x y _ hy; simp at hy)
      ?_ (by intro x y hx _; simp at hx) ?_
    · -- ROZŁĄCZNOŚĆ obrazu z napływem: B-dziecko ma `k − j = p ≥ 8`, węzeł `W(n)` ma `≤ 7`
      intro x w hx hw hc
      have hx' := (LICZ.mem_filter_iff _ _ _).mp hx
      rw [inRk_iff] at hx'
      obtain ⟨p, r, hp, hr, rfl, _, _⟩ := hx'
      have hs := Wlist_small n hn w hw
      rw [← hc] at hs
      simp only [childB] at hs
      omega
    · -- ZAWARTOŚĆ list — to jest `row0_mem`
      intro z
      rw [LICZ.mem_filter_iff, row0_mem n hn z]
      constructor
      · rintro (⟨q, hq, rfl⟩ | hw)
        · exact Or.inl ⟨q, (LICZ.mem_filter_iff _ _ _).mpr hq, rfl⟩
        · exact Or.inr (Or.inr hw)
      · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, _⟩ | hw)
        · exact Or.inl ⟨q, (LICZ.mem_filter_iff _ _ _).mp hq, rfl⟩
        · simp at hq
        · exact Or.inr hw
  have e0 : ([] : List Node).length = 0 := rfl
  rw [e0, Wlist_len n] at h
  omega

end A252864.DYN2
