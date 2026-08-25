/-
  A252864 — `_DYN2_W12.lean`.  WIERSZE `j = 1` i `j = 2` MACIERZY `M` (`thm:dynamics`,
  MOST.md:397-416).
  ⛔ ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`, ZERO Mathlib.

  TEZY:
    `row1 : vv klR n 1 = vv klR (n-1) 3`                  (`M 1 3 = 1`, `w 1 = 0`)
    `row2 : vv klR n 2 = vv klR (n-1) 1 + vv klR (n-1) 2` (`M 2 1 = M 2 2 = 1`, `w 2 = 0`)

  ODWZOROWANIE: `childB`, nie `childA` (to jest cała różnica wobec `_DYN2_W3` / `_DYN2_W4`).
  `childB (A, A+B) = (A+B, A+(A+B))`, czyli B-rodzicem węzła `(a, a+b)` jest `(b, a)`.
-/
import «_DYN2_B»
import «_DYN2_Naplyw»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat A252864.MostL A252864.DYN

/-! ## 0.  Kształt `childB` w koordynatach `(a,b)` -/

/-- `childB` na węźle zapisanym jako `(u, u+v)`.  `rfl`, bo `childB p = (p.2, p.1 + p.2)`. -/
theorem childB_ab (u v : Nat) : childB (u, u + v) = (u + v, u + (u + v)) := rfl

/-- Każdy element `Fin 5` jest jedną z pięciu wartości — potrzebne do WYCZERPANIA klas. -/
theorem fin5_cases : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide

/-! ## 1.  KROK W PRZÓD — wspólny rdzeń wierszy 1 i 2

Węzeł `z = (a, a+b)` z `¬C0` i `C2` (czyli klasy 1 albo 2) na poziomie `n ≥ 10`:
① rodzicem-drzewowym jest B-rodzic `(b, a)`  ② `b ≥ 8`  ③ `b < a`  ④ poziom `n−1`
⑤ B-rodzic NIE jest klasy 0 (bo `z` jest jego dzieckiem drzewowym — `R2_B`). -/

theorem B_pack (n a b : Nat) (hn : 10 ≤ n) (ha : 8 ≤ a) (hb : 1 ≤ b)
    (hL : L a (a + b) = n) (hn0 : ¬ C0 a b) (hC2 : C2 a b) :
    ∃ B, a = b + B ∧ 8 ≤ b ∧ 1 ≤ B ∧ L b (b + B) = n - 1 ∧ ¬ C0 b B
         ∧ tparent a (a + b) = (b, a) := by
  -- ① `b ≥ 2`: przy `b = 1` węzeł leżałby w `I₁` (`b1_in_I1`), a mamy `¬C0`
  have hb2 : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with h | h
    · exfalso
      have hb1 : b = 1 := by omega
      subst hb1
      exact hn0 (b1_in_I1 a ha)
    · exact h
  -- ① rodzicem-drzewowym jest B-rodzic
  have htp : tparent a (a + b) = (b, a) := (parent_B_iff a b ha hb2).mpr hC2
  have hfst : (tparent a (a + b)).1 = b := by rw [htp]
  have hsnd : (tparent a (a + b)).2 = a := by rw [htp]
  -- ② `b ≥ 8` — inaczej B-rodzic wypada z `R`, więc `z` byłby NAPŁYWEM, a napływ leży w `I₁`
  have hb8 : 8 ≤ b := by
    rcases Nat.lt_or_ge b 8 with h | h
    · exfalso
      have hnw : ¬ wRodzic a b := by
        intro hw
        have h1 := hw.1
        rw [hfst] at h1
        omega
      rcases (naplyw_iff n a b hn ha hb hL).mp hnw with ⟨he, _⟩ | ⟨_, h7, hae⟩
      · omega
      · have hC0 := C0_tail (n - 10) b (by omega) (by omega)
        have e : n - 10 + 7 + b = a := by omega
        rw [e] at hC0
        exact hn0 hC0
    · exact h
  -- ③ `b < a`:  gdyby `a ≤ b`, to `(3a+1)² ≤ (a+2b+1)² < 5(a+1)²` ⇒ `4a² < 4a+4` ⇒ `a ≤ 1`
  have hba : b < a := by
    rcases Nat.lt_or_ge b a with h | h
    · exact h
    · exfalso
      have hm : (3*a + 1) * (3*a + 1) ≤ (a + 2*b + 1) * (a + 2*b + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have ea : (3*a + 1) * (3*a + 1) = 9 * (a*a) + 6*a + 1 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        rw [KW.c33 a]
        omega
      have eb : (a + 1) * (a + 1) = a*a + 2*a + 1 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        omega
      have h8 : 8 * a ≤ a * a := Nat.mul_le_mul_right a ha
      simp only [C2] at hC2
      omega
  -- ④ poziom rodzica = `n − 1`
  have hlvl : L b a + 1 = L a (a + b) := by
    have hh := tparent_lvl a (a + b) (by omega) (by omega)
    rw [hfst, hsnd] at hh
    exact hh
  have eab : b + (a - b) = a := by omega
  refine ⟨a - b, by omega, hb8, by omega, ?_, ?_, htp⟩
  · rw [eab]; omega
  · -- ⑤ `z` JEST dzieckiem drzewowym B-rodzica, więc B-rodzic nie leży w `I₁` (`R2_B`)
    have e2 : 2*b + (a - b) = a + b := by omega
    have hIsT : IsTChild (b, b + (a - b)) (b + (a - b), 2*b + (a - b)) := by
      show tparent (b + (a - b)) (2*b + (a - b)) = (b, b + (a - b))
      rw [eab, e2]
      exact htp
    exact (R2_B b (a - b) hb8).mp hIsT

/-! ## 2.  KROK WSTECZ — poziom B-dziecka

`q = (A, A+B)` z `¬C0` ma B-dziecko DRZEWOWE (`R2_B`), więc leży ono poziom wyżej. -/

theorem B_back_level (n A B : Nat) (hn : 10 ≤ n) (hA : 8 ≤ A) (hB : 1 ≤ B)
    (hL : L A (A + B) = n - 1) (hn0 : ¬ C0 A B) :
    L (A + B) (A + (A + B)) = n := by
  have hIsT : IsTChild (A, A + B) (A + B, 2*A + B) := (R2_B A B hA).mpr hn0
  have htp : tparent (A + B) (2*A + B) = (A, A + B) := hIsT
  have hf : (tparent (A + B) (2*A + B)).1 = A := by rw [htp]
  have hs : (tparent (A + B) (2*A + B)).2 = A + B := by rw [htp]
  have hh := tparent_lvl (A + B) (2*A + B) (by omega) (by omega)
  rw [hf, hs] at hh
  have e : 2*A + B = A + (A + B) := by omega
  rw [e] at hh
  omega

/-! ## 3.  WIERSZ `j = 1` NA POZIOMIE CZŁONKOSTWA:  `I₂(n) = B(I₄(n−1))` -/

theorem row1_mem (n : Nat) (hn : 10 ≤ n) (z : Node) :
    (z ∈ (run n).2.1 ∧ (8 ≤ z.1 && z.1 < z.2 && klR z == 1) = true)
      ↔ ∃ q, (q ∈ (run (n-1)).2.1 ∧ (8 ≤ q.1 && q.1 < q.2 && klR q == 3) = true)
             ∧ childB q = z := by
  constructor
  · -- W PRZÓD: `z` klasy 2 (`I₂`) ⇒ jego B-rodzic ma klasę 3 (`I₄`) na poziomie `n−1`
    rintro ⟨hz, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨h8, hlt⟩, hcl⟩ := hp
    obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b, 8 ≤ a ∧ 1 ≤ b ∧ z = (a, a + b) := by
      refine ⟨z.1, z.2 - z.1, by omega, by omega, ?_⟩
      have : z.1 + (z.2 - z.1) = z.2 := by omega
      rw [this]
    have hL : L a (a + b) = n := ((mem_gen_iff _ _).mp hz).2
    have hcl1 := (klR_eq1 a b).mp hcl
    have hC2 : C2 a b := (class_le2_iff a b (by omega)).mp (Or.inr (Or.inl hcl))
    obtain ⟨B, rfl, hb8, hB1, hqL, hqn0, htp⟩ := B_pack n a b hn ha hb hL hcl1.1 hC2
    -- KLASA RODZICA PRZEZ WYCZERPANIE: 0 pada na `R2_B`, 1/2/4 dają złą klasę dziecka
    have hqcl : klab b B = 3 := by
      rcases fin5_cases (klab b B) with h | h | h | h | h
      · exact absurd ((klR_eq0 b B).mp (by rw [klR_klab]; exact h)) hqn0
      · exfalso
        have hd := D3_B_I2 b B hb8 hB1 h
        rw [← klR_klab, hcl] at hd
        exact absurd hd (by decide)
      · exfalso
        have hd := D3_B_I3 b B hb8 hB1 h
        rw [← klR_klab, hcl] at hd
        exact absurd hd (by decide)
      · exact h
      · exfalso
        have hd := D3_B_I5 b B hb8 hB1 h
        rw [← klR_klab, hcl] at hd
        exact absurd hd (by decide)
    refine ⟨(b, b + B), ⟨?_, ?_⟩, ?_⟩
    · exact (mem_gen_iff _ _).mpr ⟨by omega, hqL⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨⟨hb8, by omega⟩, ?_⟩
      rw [klR_klab]
      exact hqcl
    · rw [childB_ab]
      have e : b + (b + B) = b + B + b := by omega
      rw [e]
  · -- WSTECZ: rodzic klasy 3 (`I₄`) ⇒ jego B-dziecko ma klasę 1 (`I₂`) na poziomie `n`
    rintro ⟨q, ⟨hq, hqp⟩, rfl⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hqp
    obtain ⟨⟨h8, hlt⟩, hcl⟩ := hqp
    obtain ⟨A, B, hA, hB, rfl⟩ : ∃ A B, 8 ≤ A ∧ 1 ≤ B ∧ q = (A, A + B) := by
      refine ⟨q.1, q.2 - q.1, by omega, by omega, ?_⟩
      have : q.1 + (q.2 - q.1) = q.2 := by omega
      rw [this]
    have hqL : L A (A + B) = n - 1 := ((mem_gen_iff _ _).mp hq).2
    have hqn0 : ¬ C0 A B := ((klR_eq3 A B).mp hcl).1
    have hzL : L (A + B) (A + (A + B)) = n := B_back_level n A B hn hA hB hqL hqn0
    have hclab : klab A B = 3 := by rw [← klR_klab]; exact hcl
    have hzc : klab (A + B) A = 1 := D3_B_I4 A B hA hB hclab
    rw [childB_ab]
    refine ⟨(mem_gen_iff _ _).mpr ⟨by omega, hzL⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have e : A + (A + B) = A + B + A := by omega
    rw [e, klR_klab]
    exact hzc

/-! ## 4.  WIERSZ `j = 2` NA POZIOMIE CZŁONKOSTWA:  `I₃(n) = B(I₂(n−1)) ⊍ B(I₃(n−1))` -/

theorem row2_mem (n : Nat) (hn : 10 ≤ n) (z : Node) :
    (z ∈ (run n).2.1 ∧ (8 ≤ z.1 && z.1 < z.2 && klR z == 2) = true)
      ↔ (∃ q, (q ∈ (run (n-1)).2.1 ∧ (8 ≤ q.1 && q.1 < q.2 && klR q == 1) = true)
              ∧ childB q = z)
        ∨ (∃ q, (q ∈ (run (n-1)).2.1 ∧ (8 ≤ q.1 && q.1 < q.2 && klR q == 2) = true)
                ∧ childB q = z) := by
  constructor
  · rintro ⟨hz, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨h8, hlt⟩, hcl⟩ := hp
    obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b, 8 ≤ a ∧ 1 ≤ b ∧ z = (a, a + b) := by
      refine ⟨z.1, z.2 - z.1, by omega, by omega, ?_⟩
      have : z.1 + (z.2 - z.1) = z.2 := by omega
      rw [this]
    have hL : L a (a + b) = n := ((mem_gen_iff _ _).mp hz).2
    have hcl2 := (klR_eq2 a b).mp hcl
    obtain ⟨B, rfl, hb8, hB1, hqL, hqn0, htp⟩ :=
      B_pack n a b hn ha hb hL hcl2.1 hcl2.2.2
    -- KLASA RODZICA ∈ {1,2}: 0 pada na `R2_B`, 3 dałoby dziecko klasy 1, 4 — klasy 0
    have hqcl : klab b B = 1 ∨ klab b B = 2 := by
      rcases fin5_cases (klab b B) with h | h | h | h | h
      · exact absurd ((klR_eq0 b B).mp (by rw [klR_klab]; exact h)) hqn0
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have hd := D3_B_I4 b B hb8 hB1 h
        rw [← klR_klab, hcl] at hd
        exact absurd hd (by decide)
      · exfalso
        have hd := D3_B_I5 b B hb8 hB1 h
        rw [← klR_klab, hcl] at hd
        exact absurd hd (by decide)
    have hmem : (b, b + B) ∈ (run (n-1)).2.1 := (mem_gen_iff _ _).mpr ⟨by omega, hqL⟩
    have hchild : childB (b, b + B) = (b + B, b + B + b) := by
      rw [childB_ab]
      have e : b + (b + B) = b + B + b := by omega
      rw [e]
    rcases hqcl with h | h
    · left
      refine ⟨(b, b + B), ⟨hmem, ?_⟩, hchild⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨⟨hb8, by omega⟩, ?_⟩
      rw [klR_klab]; exact h
    · right
      refine ⟨(b, b + B), ⟨hmem, ?_⟩, hchild⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨⟨hb8, by omega⟩, ?_⟩
      rw [klR_klab]; exact h
  · -- WSTECZ: oba źródła dają `¬C0` i klasę dziecka 2 (`D3_B_I2` / `D3_B_I3`)
    intro hor
    have hcore : ∃ A B, 8 ≤ A ∧ 1 ≤ B ∧ ¬ C0 A B ∧ klab (A + B) A = 2
                   ∧ L A (A + B) = n - 1 ∧ childB (A, A + B) = z := by
      rcases hor with ⟨q, ⟨hq, hqp⟩, hqz⟩ | ⟨q, ⟨hq, hqp⟩, hqz⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hqp
        obtain ⟨⟨h8, hlt⟩, hcl⟩ := hqp
        obtain ⟨A, B, hA, hB, rfl⟩ : ∃ A B, 8 ≤ A ∧ 1 ≤ B ∧ q = (A, A + B) := by
          refine ⟨q.1, q.2 - q.1, by omega, by omega, ?_⟩
          have : q.1 + (q.2 - q.1) = q.2 := by omega
          rw [this]
        have hqL : L A (A + B) = n - 1 := ((mem_gen_iff _ _).mp hq).2
        have hclab : klab A B = 1 := by rw [← klR_klab]; exact hcl
        exact ⟨A, B, hA, hB, ((klR_eq1 A B).mp hcl).1,
               D3_B_I2 A B hA hB hclab, hqL, hqz⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hqp
        obtain ⟨⟨h8, hlt⟩, hcl⟩ := hqp
        obtain ⟨A, B, hA, hB, rfl⟩ : ∃ A B, 8 ≤ A ∧ 1 ≤ B ∧ q = (A, A + B) := by
          refine ⟨q.1, q.2 - q.1, by omega, by omega, ?_⟩
          have : q.1 + (q.2 - q.1) = q.2 := by omega
          rw [this]
        have hqL : L A (A + B) = n - 1 := ((mem_gen_iff _ _).mp hq).2
        have hclab : klab A B = 2 := by rw [← klR_klab]; exact hcl
        exact ⟨A, B, hA, hB, ((klR_eq2 A B).mp hcl).1,
               D3_B_I3 A B hA hB hclab, hqL, hqz⟩
    obtain ⟨A, B, hA, hB, hqn0, hzc, hqL, hqz⟩ := hcore
    rw [childB_ab] at hqz
    subst hqz
    have hzL : L (A + B) (A + (A + B)) = n := B_back_level n A B hn hA hB hqL hqn0
    refine ⟨(mem_gen_iff _ _).mpr ⟨by omega, hzL⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have e : A + (A + B) = A + B + A := by omega
    rw [e, klR_klab]
    exact hzc

/-! ## 5.  DWIE TEZY GŁÓWNE — wiersze `j = 1` i `j = 2` twierdzenia `[R3]` -/

/-- **WIERSZ `j = 1`:** `n₂′ = n₄`  (`M 1 3 = 1`, `w 1 = 0`). -/
theorem row1 (n : Nat) (hn : 10 ≤ n) : vv klR n 1 = vv klR (n-1) 3 := by
  unfold vv
  refine LICZ.length_split1 _ _ childB
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup n))
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup (n-1))) childB_inj ?_
  intro z
  rw [LICZ.mem_filter_iff]
  rw [row1_mem n hn z]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, (LICZ.mem_filter_iff _ _ _).mpr hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, (LICZ.mem_filter_iff _ _ _).mp hq, rfl⟩

/-- **WIERSZ `j = 2`:** `n₃′ = n₂ + n₃`  (`M 2 1 = M 2 2 = 1`, `w 2 = 0`).
    Dwa źródła z TĄ SAMĄ funkcją `childB` ⇒ `length_split2'` (wersja z primem). -/
theorem row2 (n : Nat) (hn : 10 ≤ n) : vv klR n 2 = vv klR (n-1) 1 + vv klR (n-1) 2 := by
  unfold vv
  refine LICZ.length_split2' _ _ _ childB childB
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup n))
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup (n-1)))
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup (n-1)))
    childB_inj childB_inj ?_ ?_
  · -- ROZŁĄCZNOŚĆ OBRAZÓW: `childB` injektywne, a węzeł nie ma naraz klasy 1 i 2
    intro x y hx hy hxy
    have hx1 : klR x = 1 := by
      have := (LICZ.mem_filter_iff _ _ _).mp hx
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      exact this.2.2
    have hy2 : klR y = 2 := by
      have := (LICZ.mem_filter_iff _ _ _).mp hy
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      exact this.2.2
    have hxyeq : x = y := childB_inj x y hxy
    rw [hxyeq, hy2] at hx1
    exact absurd hx1 (by decide)
  · intro z
    rw [LICZ.mem_filter_iff, row2_mem n hn z]
    constructor
    · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact Or.inl ⟨q, (LICZ.mem_filter_iff _ _ _).mpr hq, rfl⟩
      · exact Or.inr ⟨q, (LICZ.mem_filter_iff _ _ _).mpr hq, rfl⟩
    · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact Or.inl ⟨q, (LICZ.mem_filter_iff _ _ _).mp hq, rfl⟩
      · exact Or.inr ⟨q, (LICZ.mem_filter_iff _ _ _).mp hq, rfl⟩

end A252864.DYN2
