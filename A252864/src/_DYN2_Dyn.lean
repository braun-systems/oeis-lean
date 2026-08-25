/-
  A252864 — `_DYN2_Dyn.lean`.  ZŁOŻENIE: `thm:dynamics` = `[R3]` (`MOST.md:397-416`).
  ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.

  Pięć wierszy macierzy `M`, każdy jako osobna równość długości list:
    j=0  n₁′ = n₅ + 7   (childB z klasy I₅  +  NAPŁYW W(n), 7 węzłów)   `_DYN2_W0`
    j=1  n₂′ = n₄       (childB z klasy I₄)                             `_DYN2_W12`
    j=2  n₃′ = n₂ + n₃  (childB z klas I₂, I₃)                          `_DYN2_W12`
    j=3  n₄′ = n₃       (childA z klasy I₃)                             `_DYN2_W3`
    j=4  n₅′ = n₄ + n₅  (childA z klas I₄, I₅)                          `_DYN2_W4`
-/
import «_DYN2_W0»
import «_DYN2_W12»
import «_DYN2_W4»

namespace A252864.DYN2

open A252864.Tree A252864.Seq

/-- **TWIERDZENIE R3 (DYNAMIKA)** — `v(n) = M·v(n−1) + (7,0,0,0,0)` dla `n ≥ 10`.
    Kształt 1:1 z `Seq.dynamics`; `klR`/`MM`/`ww`/`vv` są kopiami `rfl` z `Sequence.lean`. -/
theorem dynamics (n : Nat) (hn : 10 ≤ n) (j : Fin 5) :
    vv klR n j = (List.finRange 5).foldl (fun acc k => acc + MM j k * vv klR (n - 1) k) 0
               + ww j := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rcases hj with rfl|rfl|rfl|rfl|rfl
  · rw [rhs_0]; exact row0 n hn
  · rw [rhs_1]; exact row1 n hn
  · rw [rhs_2]; exact row2 n hn
  · rw [rhs_3]; exact row3 n (by omega)
  · rw [rhs_4]; exact row4 n (by omega)

end A252864.DYN2
