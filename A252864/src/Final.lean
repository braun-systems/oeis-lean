/-
  A252864 — `Final.lean`.  DOMKNIĘCIE ŁAŃCUCHA `stoll` BEZ `sorry`.
  Lean 4, BEZ Mathlib.

  PO CO TEN PLIK ISTNIEJE — obejście CYKLU IMPORTÓW, nie nowa matematyka.
  ------------------------------------------------------------------------
  · `FiveTerm.lean:255` ma `five_term_of_dyn` — bierze JEDNĄ hipotezę `hdyn`
    (dynamikę `v klasaR1`) i oddaje LEMAT K.
  · `_DYN2_W0/W12/W3/W4` mają pięć wierszy tej dynamiki, DOWIEDZIONYCH,
    ale w terminach LOKALNYCH kopii `vv`/`klR`/`MM`/`ww` z `_DYN2_Ksztalt`.
  · `FiveTerm` importuje `Sequence`, więc dowodu `five_term` NIE DA SIĘ wstawić
    w `Sequence.lean` — byłby cykl.  Ten moduł stoi OBOK: importuje oba drzewa
    (`FiveTerm` i `_DYN2_*`), które nie zależą od siebie nawzajem.

  🟢 MOST `vv klR ≡ Seq.v klasaR1` JEST DEFINICYJNY — cztery `rfl` w
     `_FINAL_probe1.lean` (0,754 s).  Nie ma tu żadnego nowego rozumowania.

  ⚠️ `Sequence.five_term` z `sorry` ZOSTAJE nietknięty — jest świadkiem starej
     drogi.  Ten plik NIE modyfikuje `Sequence.lean` ani `FiveTerm.lean`.
-/
import FiveTerm
import «_FINAL_Jadro»
import «_DYN2_W0»
import «_DYN2_W12»
import «_DYN2_W3»
import «_DYN2_W4»

namespace A252864.Final

open A252864.Tree A252864.Seq A252864.DYN2

/-! ## 1.  ZŁOŻENIE PIĘCIU WIERSZY W JEDNO ZDANIE `hdyn`

Rozbicie po `j : Fin 5` przez wyczerpanie — wzorzec wzięty z `_DYN2_W0.lean:115`.
Każdy przypadek: `rhs_j` (kształt `foldl`, `_DYN2_Ksztalt`) + `row_j` (treść).
Most `vv klR ≡ v klasaR1`, `MM ≡ M`, `ww ≡ w` działa przez `rfl`, więc `exact`
przechodzi bez ani jednego `rw`. -/

theorem dyn_klasaR1 : ∀ n, 10 ≤ n → ∀ j, v klasaR1 n j =
    (List.finRange 5).foldl (fun acc k => acc + M j k * v klasaR1 (n - 1) k) 0 + w j := by
  intro n hn j
  have hfin5 : ∀ x : Fin 5, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
  rcases hfin5 j with rfl | rfl | rfl | rfl | rfl
  · exact (DYN2.row0 n hn).trans (DYN2.rhs_0 DYN2.klR (n - 1)).symm
  · exact (DYN2.row1 n hn).trans (DYN2.rhs_1 DYN2.klR (n - 1)).symm
  · exact (DYN2.row2 n hn).trans (DYN2.rhs_2 DYN2.klR (n - 1)).symm
  · exact (DYN2.row3 n (by omega)).trans (DYN2.rhs_3 DYN2.klR (n - 1)).symm
  · exact (DYN2.row4 n (by omega)).trans (DYN2.rhs_4 DYN2.klR (n - 1)).symm

/-! ## 2.  LEMAT K — bez `sorry` -/

/-- **[LEMAT K]** — to samo zdanie co `Seq.five_term`, ale DOWIEDZIONE.

    ⚠️ NIE przez `five_term_of_dyn`: ono ma zaszyte `transfer_ini_{C,G}_klasaR1`,
    które w repo idą przez `native_decide`.  Wołam `five_term_of_transfer` wprost,
    podając strukturę `Transfer klasaR1` z polami POCZĄTKOWYMI Z JĄDRA
    (`_FINAL_Jadro.lean`).  Efekt: ZERO aksjomatów kompilatora w całym łańcuchu. -/
theorem five_term_proved (k : Nat) :
    a (k + 14) + a (k + 10) + a (k + 9) = 2 * a (k + 13) :=
  five_term_of_transfer (klasa := klasaR1)
    { dyn := dyn_klasaR1
      ini_C := ini_C_jadro
      ini_G := ini_G_jadro } k

/-! ## 3.  POWTÓRZONE OGNIWA `pair → regime → stoll`

Dowody skopiowane 1:1 z `Sequence.lean:978-1013`; JEDYNA zmiana to
`five_term k` → `five_term_proved k` w `pair`. -/

theorem pair (k : Nat) :
    a (k + 12) = a (k + 11) + a (k + 9) ∧ a (k + 13) = a (k + 12) + a (k + 10) := by
  induction k with
  | zero => exact ⟨base12, base13⟩
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show a (k + 14) = a (k + 13) + a (k + 11)
      have hK := five_term_proved k
      have h1 := ih.1
      have h2 := ih.2
      omega

theorem regime (n : Nat) (hn : 13 ≤ n) : a n = a (n - 1) + a (n - 3) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e1 : 13 + k - 1 = k + 12 := by omega
  have e3 : 13 + k - 3 = k + 10 := by omega
  have e0 : 13 + k = k + 13 := by omega
  rw [e1, e3, e0]
  exact (pair k).2

/-- **KONJEKTURA STOLLA (MathOverflow 195207, 2015) — BEZ `sorry`.** -/
theorem stoll_proved (n : Nat) (hn : 12 ≤ n) : a n = a (n - 1) + a (n - 3) := by
  rcases Nat.lt_or_ge n 13 with h | h
  · have h12 : n = 12 := by omega
    subst h12; exact case_twelve
  · exact regime n h

end A252864.Final
