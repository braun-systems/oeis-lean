/-
  A252864 — `_DYN2_Wiersze.lean`.  WIERSZE MACIERZY `M` JAKO RÓWNOŚCI DŁUGOŚCI LIST.
  ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.
-/
import «_DYN2_Ksztalt»
import «_DYN2_Licz»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat A252864.MostL A252864.DYN

/-! ## 0.  `[D3.1]` — żaden węzeł nie leży na progu (niewymierność √5) -/

/-- `m² ≠ 5n²` dla `n ≥ 1` — niewymierność √5 w postaci, której potrzebuję ([D3.1]). -/
theorem sq5_mod (m : Nat) (h : (m * m) % 5 = 0) : m % 5 = 0 := by
  have hm : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  have e : (m * m) % 5 = ((m % 5) * (m % 5)) % 5 := Nat.mul_mod m m 5
  rcases hm with h5|h5|h5|h5|h5 <;> rw [h5] at e <;> omega

theorem nosq5 : ∀ m n : Nat, 1 ≤ n → m * m ≠ 5 * (n * n) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m IH =>
    intro n hn hc
    have h5m : m % 5 = 0 := by
      apply sq5_mod
      omega
    obtain ⟨t, ht⟩ : ∃ t, m = 5 * t := ⟨m / 5, by omega⟩
    subst ht
    -- 25t² = 5n²  ⇒  n² = 5t²
    have e1 : 5 * t * (5 * t) = 5 * (5 * (t * t)) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [e1] at hc
    have e2 : n * n = 5 * (t * t) := by omega
    have e3 : (5*t) * (5*t) = 25 * (t * t) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · exfalso
        have : n * n = 0 := by simpa using e2
        have hn0 : n = 0 := by
          rcases Nat.eq_zero_or_pos n with rfl | hp
          · rfl
          · exfalso; have := Nat.mul_le_mul hp hp; omega
        omega
      · exact h
    have hlt : n < 5 * t := by
      rcases Nat.lt_or_ge n (5 * t) with h | hge
      · exact h
      · exfalso
        have h1 : (5*t) * (5*t) ≤ n * n := Nat.mul_le_mul hge hge
        rw [e3] at h1
        have htt : 1 ≤ t * t := Nat.mul_le_mul ht1 ht1
        omega
    exact IH n hlt t ht1 e2

/-! ## 1.  Warunki klas jako nazwane predykaty -/

abbrev C0 (a b : Nat) : Prop := (a+2*b+2)*(a+2*b+2) < 5*(a*a)
abbrev C1 (a b : Nat) : Prop := (a+2*b+3)*(a+2*b+3) < 5*((a+1)*(a+1))
abbrev C2 (a b : Nat) : Prop := (a+2*b+1)*(a+2*b+1) < 5*((a+1)*(a+1))
abbrev C3 (a b : Nat) : Prop := (a+2*b)*(a+2*b) + 1 < 5*((a+1)*(a+1)) + 2*(a+2*b)

theorem klR_val (a b : Nat) : klR (a, a+b) =
    (if C0 a b then 0 else if C1 a b then 1 else if C2 a b then 2 else if C3 a b then 3 else 4) := by
  simp only [klR, Nat.add_sub_cancel_left, C0, C1, C2, C3]

theorem klR_eq2 (a b : Nat) : klR (a, a+b) = 2 ↔ (¬ C0 a b ∧ ¬ C1 a b ∧ C2 a b) := by
  rw [klR_val]; by_cases h0 : C0 a b
  · simp [h0]
  · by_cases h1 : C1 a b
    · simp [h0, h1]
    · by_cases h2 : C2 a b
      · simp [h0, h1, h2]
      · by_cases h3 : C3 a b
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]

theorem klR_eq3 (a b : Nat) : klR (a, a+b) = 3 ↔ (¬ C0 a b ∧ ¬ C1 a b ∧ ¬ C2 a b ∧ C3 a b) := by
  rw [klR_val]; by_cases h0 : C0 a b
  · simp [h0]
  · by_cases h1 : C1 a b
    · simp [h0, h1]
    · by_cases h2 : C2 a b
      · simp [h0, h1, h2]
      · by_cases h3 : C3 a b
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]

/-! ## 2.  Zagnieżdżenie progów `I₁ ⊂ I₂` — potrzebne w KAŻDYM wierszu -/

theorem nest01 (a b : Nat) (ha : 1 ≤ a) : C0 a b → C1 a b := by
  intro h
  have hs : a + 2*b + 2 ≤ 3*a - 1 := by
    rcases Nat.lt_or_ge (a + 2*b + 2) (3*a) with hlt | hge
    · omega
    · exfalso
      have h1 : (3*a) * (3*a) ≤ (a+2*b+2) * (a+2*b+2) := Nat.mul_le_mul hge hge
      have e : (3*a) * (3*a) = 9 * (a*a) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e] at h1
      have haa : 1 ≤ a * a := Nat.mul_le_mul ha ha
      simp only [C0] at h
      omega
  simp only [C0] at h
  simp only [C1]
  have e1 : (a+2*b+3)*(a+2*b+3) = (a+2*b+2)*(a+2*b+2) + 2*(a+2*b+2) + 1 := by
    simp only [Nat.add_mul, Nat.mul_add]; omega
  have e2 : 5*((a+1)*(a+1)) = 5*(a*a) + 10*a + 5 := by
    simp only [Nat.add_mul, Nat.mul_add]; omega
  omega

/-! ## 3.  WIERSZ `j = 3`:  `I₄(n) = A(I₃(n−1))`  — jedno źródło, odwzorowanie `childA` -/

theorem childA_inj (x y : Node) (h : childA x = childA y) : x = y := by
  simp only [childA, Prod.mk.injEq] at h
  exact Prod.ext h.1 (by omega)

theorem row3_mem (n : Nat) (hn : 1 ≤ n) (z : Node) :
    (z ∈ (run n).2.1 ∧ (8 ≤ z.1 && z.1 < z.2 && klR z == 3) = true)
      ↔ ∃ q, (q ∈ (run (n-1)).2.1 ∧ (8 ≤ q.1 && q.1 < q.2 && klR q == 2) = true)
             ∧ childA q = z := by
  constructor
  · rintro ⟨hz, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨h8, hlt⟩, hcl⟩ := hp
    obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b, 8 ≤ a ∧ 1 ≤ b ∧ z = (a, a + b) := by
      refine ⟨z.1, z.2 - z.1, by omega, by omega, ?_⟩
      have : z.1 + (z.2 - z.1) = z.2 := by omega
      rw [this]
    have hL : L a (a + b) = n := ((mem_gen_iff _ _).mp hz).2
    rw [klR_eq3] at hcl
    obtain ⟨hn0, hn1, hn2, h3⟩ := hcl
    -- `b = 1` dałoby klasę 0 (`b1_in_I1`) — sprzeczność z `¬C0`
    have hb2 : 2 ≤ b := by
      rcases Nat.lt_or_ge b 2 with h | h
      · exfalso; have hb1 : b = 1 := by omega
        subst hb1; exact hn0 (b1_in_I1 a ha)
      · exact h
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    have hc1 : 1 ≤ c := by omega
    -- klasa rodzica = 2
    have en1 : a + 2*(c+1) + 1 = a + 2*c + 3 := by omega
    have en0 : a + 2*(c+1) = a + 2*c + 2 := by omega
    have eex : (a+2*c+2)*(a+2*c+2) = (a+2*c+1)*(a+2*c+1) + 2*(a+2*c+1) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    have hqn1 : ¬ C1 a c := by
      simp only [C1]; simp only [C2, en1] at hn2; exact hn2
    have hqC2 : C2 a c := by
      simp only [C2]; simp only [C3, en0] at h3; omega
    have hqn0 : ¬ C0 a c := fun hh => hqn1 (nest01 a c (by omega) hh)
    -- poziom rodzica = n−1, przez A-LEMAT
    have hstrict : (a + 2*c + 3)^2 > 5*(a+1)^2 := by
      have e1 : (a + 2*c + 3)^2 = (a + 2*c + 3) * (a + 2*c + 3) := KW.sqp _
      have e2 : 5*(a+1)^2 = 5*((a+1)*(a+1)) := by rw [KW.sqp]
      have hne := nosq5 (a + 2*c + 3) (a+1) (by omega)
      simp only [C1] at hqn1
      omega
    have hstep := (A_lemat a c ha hc1).mpr hstrict
    have enorm : a + (c+1) = a + c + 1 := by omega
    rw [enorm] at hL
    have hqL : L a (a + c) = n - 1 := by omega
    refine ⟨(a, a + c), ⟨?_, ?_⟩, ?_⟩
    · exact (mem_gen_iff _ _).mpr ⟨by omega, hqL⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨ha, by omega⟩, (klR_eq2 a c).mpr ⟨hqn0, hqn1, hqC2⟩⟩
    · simp [childA, Nat.add_assoc]
  · rintro ⟨q, ⟨hq, hqp⟩, rfl⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hqp
    obtain ⟨⟨h8, hlt⟩, hcl⟩ := hqp
    obtain ⟨a, c, ha, hc1, rfl⟩ : ∃ a c, 8 ≤ a ∧ 1 ≤ c ∧ q = (a, a + c) := by
      refine ⟨q.1, q.2 - q.1, by omega, by omega, ?_⟩
      have : q.1 + (q.2 - q.1) = q.2 := by omega
      rw [this]
    have hqL : L a (a + c) = n - 1 := ((mem_gen_iff _ _).mp hq).2
    rw [klR_eq2] at hcl
    obtain ⟨hqn0, hqn1, hqC2⟩ := hcl
    have hstrict : (a + 2*c + 3)^2 > 5*(a+1)^2 := by
      have hne := nosq5 (a + 2*c + 3) (a+1) (by omega)
      have e1 : (a + 2*c + 3)^2 = (a + 2*c + 3) * (a + 2*c + 3) := KW.sqp _
      have e2 : 5*(a+1)^2 = 5*((a+1)*(a+1)) := by rw [KW.sqp]
      simp only [C1] at hqn1
      omega
    have hstep := (A_lemat a c ha hc1).mpr hstrict
    have hzL : L a (a + (c+1)) = n := by
      have e : a + (c+1) = a + c + 1 := by omega
      rw [e]; omega
    have en1 : a + 2*(c+1) + 1 = a + 2*c + 3 := by omega
    have en0 : a + 2*(c+1) = a + 2*c + 2 := by omega
    have eex : (a+2*c+2)*(a+2*c+2) = (a+2*c+1)*(a+2*c+1) + 2*(a+2*c+1) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    have hn2 : ¬ C2 a (c+1) := by
      simp only [C2, en1]; simp only [C1] at hqn1; exact hqn1
    have h3 : C3 a (c+1) := by
      simp only [C3, en0]; simp only [C2] at hqC2; omega
    have hn1 : ¬ C1 a (c+1) := by
      simp only [C1]; simp only [C1] at hqn1
      have hmono : (a+2*c+3)*(a+2*c+3) ≤ (a+2*(c+1)+3)*(a+2*(c+1)+3) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have hn0 : ¬ C0 a (c+1) := fun hh => hn1 (nest01 a (c+1) (by omega) hh)
    refine ⟨?_, ?_⟩
    · have e : childA (a, a + c) = (a, a + (c+1)) := by simp [childA, Nat.add_assoc]
      rw [e]; exact (mem_gen_iff _ _).mpr ⟨by omega, hzL⟩
    · have e : childA (a, a + c) = (a, a + (c+1)) := by simp [childA, Nat.add_assoc]
      rw [e]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨ha, by omega⟩, (klR_eq3 a (c+1)).mpr ⟨hn0, hn1, hn2, h3⟩⟩

end A252864.DYN2
