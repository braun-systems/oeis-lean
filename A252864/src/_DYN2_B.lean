/-
  A252864 — `_DYN2_B.lean`.  INFRASTRUKTURA WIERSZY B (`j = 0,1,2`) twierdzenia `[R3]`.
  ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.

  🔑 ZDANIE PORZĄDKUJĄCE CAŁY ROZBIÓR (zmierzone: 0 kontrprzykładów na a,b < 900):
      klasa ∈ {0,1,2} ⇒ rodzicem-drzewowym jest B-rodzic
      klasa ∈ {3,4}   ⇒ rodzicem-drzewowym jest A-rodzic
  bo `klasa ≤ 2 ⟺ C2(a,b)`, a `C2` to DOKŁADNIE zaprzeczenie warunku A-LEMATU.
-/
import «_DYN2_W3»
import «_DYN2_Klasy»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat A252864.MostL A252864.DYN

/-- Most między moim `klR` (na węzłach) a `klab` z `_DYN2_Klasy` (na `(a,b)`). -/
theorem klR_klab (a b : Nat) : klR (a, a + b) = klab a b := by simp [klR, klab]

theorem childB_inj (x y : Node) (h : childB x = childB y) : x = y := by
  simp only [childB, Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.1

/-! ## Pozostałe charakteryzacje klas -/

theorem klR_eq0 (a b : Nat) : klR (a, a+b) = 0 ↔ C0 a b := by
  rw [klR_val]; by_cases h0 : C0 a b
  · simp [h0]
  · by_cases h1 : C1 a b
    · simp [h0, h1]
    · by_cases h2 : C2 a b
      · simp [h0, h1, h2]
      · by_cases h3 : C3 a b
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]

theorem klR_eq1 (a b : Nat) : klR (a, a+b) = 1 ↔ (¬ C0 a b ∧ C1 a b) := by
  rw [klR_val]; by_cases h0 : C0 a b
  · simp [h0]
  · by_cases h1 : C1 a b
    · simp [h0, h1]
    · by_cases h2 : C2 a b
      · simp [h0, h1, h2]
      · by_cases h3 : C3 a b
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]

theorem klR_eq4 (a b : Nat) (ha : 1 ≤ a) : klR (a, a+b) = 4 ↔ ¬ C3 a b := by
  rw [klR_val]; by_cases h0 : C0 a b
  · simp [h0]; exact nest_23 a b (by omega) (nest_12 a b (by omega) (nest_01 a b (by omega) h0))
  · by_cases h1 : C1 a b
    · simp [h0, h1]; exact nest_23 a b (by omega) (nest_12 a b (by omega) h1)
    · by_cases h2 : C2 a b
      · simp [h0, h1, h2]; exact nest_23 a b (by omega) h2
      · by_cases h3 : C3 a b
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]

/-- **Klasa ≤ 2 ⟺ `C2`.**  Zdanie porządkujące rozbiór. -/
theorem class_le2_iff (a b : Nat) (ha : 1 ≤ a) :
    (klR (a,a+b) = 0 ∨ klR (a,a+b) = 1 ∨ klR (a,a+b) = 2) ↔ C2 a b := by
  rw [klR_eq0, klR_eq1, klR_eq2]
  constructor
  · rintro (h | ⟨_, h⟩ | ⟨_, _, h⟩)
    · exact nest_12 a b ha (nest_01 a b ha h)
    · exact nest_12 a b ha h
    · exact h
  · intro h2
    by_cases h0 : C0 a b
    · exact Or.inl h0
    · by_cases h1 : C1 a b
      · exact Or.inr (Or.inl ⟨h0, h1⟩)
      · exact Or.inr (Or.inr ⟨h0, h1, h2⟩)

/-! ## Który rodzic — rozstrzygnięcie przez A-LEMAT -/

/-- **Rodzicem-drzewowym jest B-rodzic ⟺ `C2(a,b)`** (dla `b ≥ 2`; przy `b = 1`
    oba rodzice i tak leżą poza `R`). -/
theorem parent_B_iff (a b : Nat) (ha : 8 ≤ a) (hb : 2 ≤ b) :
    tparent a (a + b) = (b, a) ↔ C2 a b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hc1 : 1 ≤ c := by omega
  have enorm : a + (c + 1) = a + c + 1 := by omega
  have hA := parent_A_iff a c ha hc1
  rw [← enorm] at hA
  -- `(a+2c+3)² > 5(a+1)²` ⟺ `¬ C2 a (c+1)`
  have eC2 : C2 a (c+1) ↔ (a + 2*c + 3) * (a + 2*c + 3) < 5*((a+1)*(a+1)) := by
    have e : a + 2*(c+1) + 1 = a + 2*c + 3 := by omega
    simp only [C2, e]
  have hne := nosq5 (a + 2*c + 3) (a+1) (by omega)
  have esq1 : (a + 2*c + 3)^2 = (a + 2*c + 3) * (a + 2*c + 3) := KW.sqp _
  have esq2 : (a+1)^2 = (a+1)*(a+1) := KW.sqp _
  have hdist : ¬ ((a, a + (c+1) - 1) = (c+1, a)) := by
    intro h
    have h1 : a = c + 1 := congrArg Prod.fst h
    have h2 : a + (c+1) - 1 = a := congrArg Prod.snd h
    omega
  have hcases := tparent_cases a (c+1)
  constructor
  · intro hB
    rw [eC2]
    rcases Nat.lt_or_ge ((a + 2*c + 3) * (a + 2*c + 3)) (5*((a+1)*(a+1))) with h | h
    · exact h
    · exfalso
      have : tparent a (a + (c+1)) = (a, a + (c+1) - 1) := by
        have := hA.mpr (by omega)
        have e2 : a + (c+1) - 1 = a + c := by omega
        rw [e2]; exact this
      rw [hB] at this
      exact hdist this.symm
  · intro hC
    rw [eC2] at hC
    rcases hcases with h | h
    · exfalso
      have e2 : a + (c+1) - 1 = a + c := by omega
      rw [e2] at h
      have := hA.mp h
      omega
    · exact h

/-! ## `[R3.1]` ogon — siedem węzłów napływu leży w `I₁` (`MOST.md:388-395`) -/

theorem C0_tail (m c : Nat) (h2 : 2 ≤ c) (h7 : c ≤ 7) : C0 (m + 7 + c) c := by
  have hc : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [C0, Nat.mul_add, Nat.add_mul]; omega)

end A252864.DYN2
