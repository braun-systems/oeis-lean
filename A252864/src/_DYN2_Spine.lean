/-
  A252864 — `_DYN2_Spine.lean`.  KRĘGOSŁUP ROZBIORU `[R3]` (`MOST.md:400-416`).
  ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.

  Dowód `thm:dynamics` jest rozbiorem zbioru `R ∩ poziom n` względem RODZICA-DRZEWOWEGO.
  Ten plik dostarcza sam rozbiór — bez klas, bez zliczania:
    · `mem_R_gen_iff`  — członkostwo w `R ∩ poziom n` w czystej arytmetyce `L`
    · `tparent_cases`  — rodzic to A-rodzic `(a,b−1)` albo B-rodzic `(b,a−b)`, trzeciej opcji nie ma
    · `parent_A_iff`   — który z nich, wyrażone NIERÓWNOŚCIĄ (przez `R2_A`, czyli przez A-LEMAT)
    · `b1_class0`      — cały wiersz `b = 1` leży w `I₁` (to jest głowa napływu `W(n)`)
-/
import «_DYN2_R2»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat A252864.MostL A252864.DYN

/-! ## 1.  `R ∩ poziom n` w arytmetyce -/

/-- Region `R` jako predykat obliczalny (kopia `Seq.inRb`). -/
def inRb (p : Node) : Bool := 8 ≤ p.1 && p.1 < p.2

theorem inRb_ab (a b : Nat) : inRb (a, a + b) = true ↔ (8 ≤ a ∧ 1 ≤ b) := by
  simp [inRb]; omega

/-- Każdy węzeł `R` zapisuje się jako `(a, a+b)` z `a ≥ 8`, `b ≥ 1`. -/
theorem R_shape (p : Node) (h : inRb p = true) : ∃ a b, 8 ≤ a ∧ 1 ≤ b ∧ p = (a, a + b) := by
  refine ⟨p.1, p.2 - p.1, ?_, ?_, ?_⟩
  · simp [inRb] at h; omega
  · simp [inRb] at h; omega
  · simp [inRb] at h
    have : p.1 + (p.2 - p.1) = p.2 := by omega
    rw [this]

theorem mem_R_gen_iff (a b n : Nat) :
    ((a, a + b) ∈ (run n).2.1 ∧ inRb (a, a + b) = true)
      ↔ (8 ≤ a ∧ 1 ≤ b ∧ L a (a + b) = n) := by
  rw [mem_gen_iff, inRb_ab]
  constructor
  · rintro ⟨⟨_, hL⟩, h8, h1⟩; exact ⟨h8, h1, hL⟩
  · rintro ⟨h8, h1, hL⟩; exact ⟨⟨by omega, hL⟩, h8, h1⟩

/-! ## 2.  Dwa możliwe rodzice — i rozstrzygnięcie, który to jest -/

/-- `MOST.md:400-402` — rodzic-drzewowy węzła `(a,b) ∈ R` to A-rodzic `(a,b−1)`
    albo B-rodzic `(b, a−b)`; w zapisie `(j,k)`: `(a, a+b−1)` albo `(b, a)`. -/
theorem tparent_cases (a b : Nat) :
    tparent a (a + b) = (a, a + b - 1) ∨ tparent a (a + b) = (b, a) := by
  have h := tparent_is_A_or_B a (a + b)
  have e : a + b - a = b := by omega
  rw [e] at h
  exact h

/-- **Który rodzic** — przez `R2_A` w węźle `(a, b−1)`, czyli przez A-LEMAT.
    A-rodzic jest rodzicem-drzewowym ⟺ `(a+2b+1)² > 5(a+1)²`. -/
theorem parent_A_iff (a bq : Nat) (ha : 8 ≤ a) (hbq : 1 ≤ bq) :
    tparent a (a + bq + 1) = (a, a + bq) ↔ (a + 2*bq + 3)^2 > 5*(a+1)^2 := by
  have h := R2_A a bq ha hbq
  simpa [IsTChild] using h

/-! ## 3.  Wiersz `b = 1` — głowa napływu.  `MOST.md:388`, węzeł `(n−2, 1)`.

Dla `a ≥ 8` węzeł `(a,1)` leży w `I₁`: `(a+4)² < 5a² ⟺ 4a² > 8a+16 ⟺ a² > 2a+4`. -/

theorem b1_in_I1 (a : Nat) (ha : 8 ≤ a) : (a + 2*1 + 2) * (a + 2*1 + 2) < 5 * (a * a) := by
  -- `(a+4)² < 5a²`.  Podstawienie `a = q + 8` linearyzuje po rozwinięciu kwadratów.
  obtain ⟨q, rfl⟩ : ∃ q, a = q + 8 := ⟨a - 8, by omega⟩
  have e1 : (q + 8 + 2*1 + 2) * (q + 8 + 2*1 + 2) = q*q + 24*q + 144 := by
    simp only [Nat.add_mul, Nat.mul_add]; omega
  have e2 : 5 * ((q + 8) * (q + 8)) = 5*(q*q) + 80*q + 320 := by
    simp only [Nat.add_mul, Nat.mul_add]; omega
  rw [e1, e2]
  have : 0 ≤ q * q := Nat.zero_le _
  omega

/-- A-rodzic węzła `(a,1)` to `(a,0)` — POZA `R`; B-rodzic to `(1, a−1)` — też poza `R`.
    Czyli **każdy** węzeł wiersza `b = 1` jest napływem. -/
theorem b1_parent_outside (a : Nat) (ha : 8 ≤ a) :
    ¬ (inRb (tparent a (a + 1)) = true) := by
  have h := tparent_cases a 1
  have e : a + 1 - 1 = a := by omega
  rcases h with h | h
  · rw [h, e]; simp [inRb]
  · rw [h]; simp [inRb]

end A252864.DYN2
