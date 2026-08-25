/-
  A252864 — `_DYN2_W4.lean`.  WIERSZ `j = 4` MACIERZY `M` (`thm:dynamics`, MOST.md:397-416).
  ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`, ZERO Mathlib.

  TEZA:  `vv klR n 4 = vv klR (n-1) 3 + vv klR (n-1) 4`   (czyli `M 4 3 = M 4 4 = 1`, `w 4 = 0`)
  Klasa `I₅` na poziomie `n` = A-obrazy klas `I₄` i `I₅` z poziomu `n−1`.
-/
import «_DYN2_Wiersze»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat A252864.MostL A252864.DYN

/-! ## 0.  Brakujące ogniwa zagnieżdżenia progów: `C1 → C2 → C3` -/

/-- `I₂ ⊂ I₃`: `(x+1)² ≤ (x+3)²`, więc `C1 → C2`. -/
theorem nest12 (a b : Nat) : C1 a b → C2 a b := by
  intro h
  simp only [C1] at h
  simp only [C2]
  have hmono : (a+2*b+1)*(a+2*b+1) ≤ (a+2*b+3)*(a+2*b+3) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `I₃ ⊂ I₄`: rozwinięcie `(x+1)² = x² + 2x + 1` sprowadza to do arytmetyki liniowej. -/
theorem nest23 (a b : Nat) : C2 a b → C3 a b := by
  intro h
  simp only [C2] at h
  simp only [C3]
  have eex : (a+2*b+1)*(a+2*b+1) = (a+2*b)*(a+2*b) + 2*(a+2*b) + 1 := by
    simp only [Nat.add_mul, Nat.mul_add]; omega
  omega

/-! ## 1.  Klasa 4 jako koniunkcja warunków (analogicznie do `klR_eq2` / `klR_eq3`) -/

theorem klR_eq4_full (a b : Nat) :
    klR (a, a+b) = 4 ↔ (¬ C0 a b ∧ ¬ C1 a b ∧ ¬ C2 a b ∧ ¬ C3 a b) := by
  rw [klR_val]; by_cases h0 : C0 a b
  · simp [h0]
  · by_cases h1 : C1 a b
    · simp [h0, h1]
    · by_cases h2 : C2 a b
      · simp [h0, h1, h2]
      · by_cases h3 : C3 a b
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]

/-- Postać normalna klasy 4: samo `¬ C3` wystarcza (przy `a ≥ 1`), bo `C0 → C1 → C2 → C3`. -/
theorem klR_eq4_neg (a b : Nat) (ha : 1 ≤ a) : klR (a, a+b) = 4 ↔ ¬ C3 a b := by
  rw [klR_eq4_full]
  constructor
  · rintro ⟨_, _, _, h⟩; exact h
  · intro h3
    have h2 : ¬ C2 a b := fun hh => h3 (nest23 a b hh)
    have h1 : ¬ C1 a b := fun hh => h2 (nest12 a b hh)
    have h0 : ¬ C0 a b := fun hh => h1 (nest01 a b ha hh)
    exact ⟨h0, h1, h2, h3⟩

/-! ## 2.  WIERSZ `j = 4` na poziomie CZŁONKOSTWA — dwa źródła, jedno odwzorowanie `childA` -/

theorem row4_mem (n : Nat) (hn : 1 ≤ n) (z : Node) :
    (z ∈ (run n).2.1 ∧ (8 ≤ z.1 && z.1 < z.2 && klR z == 4) = true)
      ↔ (∃ q, (q ∈ (run (n-1)).2.1 ∧ (8 ≤ q.1 && q.1 < q.2 && klR q == 3) = true)
              ∧ childA q = z)
        ∨ (∃ q, (q ∈ (run (n-1)).2.1 ∧ (8 ≤ q.1 && q.1 < q.2 && klR q == 4) = true)
                ∧ childA q = z) := by
  constructor
  · -- KROK W PRZÓD: `z` klasy 4 ⇒ jego A-rodzic ma klasę 3 albo 4 i leży na poziomie `n−1`.
    rintro ⟨hz, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨h8, hlt⟩, hcl⟩ := hp
    obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b, 8 ≤ a ∧ 1 ≤ b ∧ z = (a, a + b) := by
      refine ⟨z.1, z.2 - z.1, by omega, by omega, ?_⟩
      have : z.1 + (z.2 - z.1) = z.2 := by omega
      rw [this]
    have hL : L a (a + b) = n := ((mem_gen_iff _ _).mp hz).2
    rw [klR_eq4_full] at hcl
    obtain ⟨hn0, hn1, hn2, hn3⟩ := hcl
    -- `b = 1` dałoby `C0` (`b1_in_I1`) — sprzeczność z `¬ C0`
    have hb2 : 2 ≤ b := by
      rcases Nat.lt_or_ge b 2 with h | h
      · exfalso; have hb1 : b = 1 := by omega
        subst hb1; exact hn0 (b1_in_I1 a ha)
      · exact h
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    have hc1 : 1 ≤ c := by omega
    -- TOŻSAMOŚĆ `C3 a (c+1) ≡ C2 a c` (podstawienie `x ↦ x+2` przy stałym `a`)
    have en0 : a + 2*(c+1) = a + 2*c + 2 := by omega
    have eex : (a+2*c+2)*(a+2*c+2) = (a+2*c+1)*(a+2*c+1) + 2*(a+2*c+1) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    have hqn2 : ¬ C2 a c := by
      intro hh
      apply hn3
      simp only [C3, en0]
      simp only [C2] at hh
      omega
    have hqn1 : ¬ C1 a c := fun hh => hqn2 (nest12 a c hh)
    have hqn0 : ¬ C0 a c := fun hh => hqn1 (nest01 a c (by omega) hh)
    -- POZIOM RODZICA = `n−1`, przez A-LEMAT (ostrość z `nosq5`)
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
    have hqmem : (a, a + c) ∈ (run (n-1)).2.1 := (mem_gen_iff _ _).mpr ⟨by omega, hqL⟩
    have hchild : childA (a, a + c) = (a, a + (c+1)) := by simp [childA, Nat.add_assoc]
    -- ROZBIÓR PO `C3 a c`: zachodzi ⇒ rodzic klasy 3; nie zachodzi ⇒ rodzic klasy 4
    by_cases h3c : C3 a c
    · left
      refine ⟨(a, a + c), ⟨hqmem, ?_⟩, hchild⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨ha, by omega⟩, (klR_eq3 a c).mpr ⟨hqn0, hqn1, hqn2, h3c⟩⟩
    · right
      refine ⟨(a, a + c), ⟨hqmem, ?_⟩, hchild⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨ha, by omega⟩, (klR_eq4_full a c).mpr ⟨hqn0, hqn1, hqn2, h3c⟩⟩
  · -- KROK WSTECZ: rodzic klasy 3 albo 4 ⇒ jego A-dziecko ma klasę 4 na poziomie `n`.
    -- Oba przypadki dają TĘ SAMĄ przesłankę `¬ C2 a c`, więc rozbiór schodzi od razu.
    intro hor
    have hcore : ∃ a c, 8 ≤ a ∧ 1 ≤ c ∧ ¬ C1 a c ∧ ¬ C2 a c
                   ∧ L a (a + c) = n - 1 ∧ childA (a, a + c) = z := by
      rcases hor with ⟨q, ⟨hq, hqp⟩, hqz⟩ | ⟨q, ⟨hq, hqp⟩, hqz⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hqp
        obtain ⟨⟨h8, hlt⟩, hcl⟩ := hqp
        obtain ⟨a, c, ha, hc1, rfl⟩ : ∃ a c, 8 ≤ a ∧ 1 ≤ c ∧ q = (a, a + c) := by
          refine ⟨q.1, q.2 - q.1, by omega, by omega, ?_⟩
          have : q.1 + (q.2 - q.1) = q.2 := by omega
          rw [this]
        have hqL : L a (a + c) = n - 1 := ((mem_gen_iff _ _).mp hq).2
        rw [klR_eq3] at hcl
        exact ⟨a, c, ha, hc1, hcl.2.1, hcl.2.2.1, hqL, hqz⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hqp
        obtain ⟨⟨h8, hlt⟩, hcl⟩ := hqp
        obtain ⟨a, c, ha, hc1, rfl⟩ : ∃ a c, 8 ≤ a ∧ 1 ≤ c ∧ q = (a, a + c) := by
          refine ⟨q.1, q.2 - q.1, by omega, by omega, ?_⟩
          have : q.1 + (q.2 - q.1) = q.2 := by omega
          rw [this]
        have hqL : L a (a + c) = n - 1 := ((mem_gen_iff _ _).mp hq).2
        rw [klR_eq4_full] at hcl
        exact ⟨a, c, ha, hc1, hcl.2.1, hcl.2.2.1, hqL, hqz⟩
    obtain ⟨a, c, ha, hc1, hqn1, hqn2, hqL, hqz⟩ := hcore
    have hchild : childA (a, a + c) = (a, a + (c+1)) := by simp [childA, Nat.add_assoc]
    rw [hchild] at hqz
    subst hqz
    -- poziom dziecka = `n`
    have hstrict : (a + 2*c + 3)^2 > 5*(a+1)^2 := by
      have e1 : (a + 2*c + 3)^2 = (a + 2*c + 3) * (a + 2*c + 3) := KW.sqp _
      have e2 : 5*(a+1)^2 = 5*((a+1)*(a+1)) := by rw [KW.sqp]
      have hne := nosq5 (a + 2*c + 3) (a+1) (by omega)
      simp only [C1] at hqn1
      omega
    have hstep := (A_lemat a c ha hc1).mpr hstrict
    have hzL : L a (a + (c+1)) = n := by
      have e : a + (c+1) = a + c + 1 := by omega
      rw [e]; omega
    -- klasa dziecka = 4, przez tożsamość `C3 a (c+1) ≡ C2 a c`
    have en0 : a + 2*(c+1) = a + 2*c + 2 := by omega
    have eex : (a+2*c+2)*(a+2*c+2) = (a+2*c+1)*(a+2*c+1) + 2*(a+2*c+1) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    have hzn3 : ¬ C3 a (c+1) := by
      intro hh
      apply hqn2
      simp only [C3, en0] at hh
      simp only [C2]
      omega
    refine ⟨(mem_gen_iff _ _).mpr ⟨by omega, hzL⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨ha, by omega⟩, (klR_eq4_neg a (c+1) (by omega)).mpr hzn3⟩

/-! ## 3.  WIERSZ `j = 4` JAKO RÓWNOŚĆ DŁUGOŚCI — `[R3]`, `M 4 3 = M 4 4 = 1`, `w 4 = 0` -/

/-- **WIERSZ `j = 4` TWIERDZENIA `[R3]`:** `n₅′ = n₄ + n₅`. -/
theorem row4 (n : Nat) (hn : 1 ≤ n) :
    vv klR n 4 = vv klR (n-1) 3 + vv klR (n-1) 4 := by
  unfold vv
  refine LICZ.length_split2' _ _ _ childA childA
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup n))
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup (n-1)))
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup (n-1)))
    childA_inj childA_inj ?_ ?_
  · -- ROZŁĄCZNOŚĆ OBRAZÓW: `childA` injektywne, a jeden węzeł nie ma naraz klasy 3 i 4.
    intro x y hx hy hxy
    have hx3 : klR x = 3 := by
      have := (LICZ.mem_filter_iff _ _ _).mp hx
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      exact this.2.2
    have hy4 : klR y = 4 := by
      have := (LICZ.mem_filter_iff _ _ _).mp hy
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      exact this.2.2
    have hxyeq : x = y := childA_inj x y hxy
    rw [hxyeq, hy4] at hx3
    exact absurd hx3 (by decide)
  · intro z
    rw [LICZ.mem_filter_iff, row4_mem n hn z]
    constructor
    · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact Or.inl ⟨q, (LICZ.mem_filter_iff _ _ _).mpr hq, rfl⟩
      · exact Or.inr ⟨q, (LICZ.mem_filter_iff _ _ _).mpr hq, rfl⟩
    · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact Or.inl ⟨q, (LICZ.mem_filter_iff _ _ _).mp hq, rfl⟩
      · exact Or.inr ⟨q, (LICZ.mem_filter_iff _ _ _).mp hq, rfl⟩

end A252864.DYN2
