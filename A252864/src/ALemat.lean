/-
  A252864 — ALemat.lean.   A-LEMAT: kiedy krok `A` zwiększa numer pokolenia.
  , domknięcie `core_le_dual` 24.08.2026 (F1b).
  Lean 4.34.0-rc2, BEZ Mathlib.

  TEZA (ze zlecenia):  dla `a ≥ 8`, `b ≥ 1`
      l(a, b+1) = l(a, b) + 1   ↔   (a+2b+3)² > 5(a+1)²
  w układzie `(a,b) = (j, k−j)`, gdzie `(j,k)` jest węzłem drzewa Kimberlinga.

  CO TEN PLIK ROBI:
    ① definicje i ogniwa ①/② są w `ALematDef.lean` (rozcięcie 24.08 — patrz tam);
    ② ogniwo ③ (`core_le_dual`) — DOMKNIĘTE 24.08.2026 przez `core_le_dual_ell`
       z `ALematGlowna.lean` (indukcja wzajemna P/C/Q po sumie `a+b`);
    ③ A-lemat złożony z ② i ③.
  Kontrole maszynowe (`native_decide`) są w OSOBNYM pliku `ALematCheck.lean`.
-/
import ALematGlowna

namespace A252864.ALemat


/-! ## 6.  OGNIWO ③ — DOMKNIĘTE 24.08.2026.  Przypadek `1 ≤ b ≤ a−1`

Tu B-rodzic ISTNIEJE i jest równy `(b+1, a)`, bo `(a+b+1) − a = b+1`.
Z `L_step_two`:  `L a (a+b+1) = 1 + min (L a (a+b)) (L (b+1) a)`,
więc krok A zwiększa `L` o 1 **dokładnie wtedy**, gdy `L a (a+b) ≤ L (b+1) a`.
Cały ciężar A-lematu siedzi więc w JEDNEJ nierówności między dwiema wartościami `L`. -/

/-- **OGNIWO ③ — UDOWODNIONE** (24.08.2026, `sorry` zdjęty).

    Słownie: **czy koszt dojścia do `(a, a+b)` jest ≤ kosztowi dojścia do `(b+1, a)`
    — rozstrzyga to próg Wythoffa węzła `(b+1, a)`.**

    DOWÓD: `ALematGlowna.core_le_dual_ell` — indukcja wzajemna P/C/Q po sumie `a+b`
    (`LEM_A_wstecz.md [W2]–[W11]` dla „⟸" i `LEM_B_dolne.md [B4]–[B6]` dla „⟹"),
    z kaskadą wyjątków `[W10]` domkniętą wartościami z `ALematBazy` (drabina w jądrze).
    Tutaj zostaje wyłącznie przejście układu współrzędnych:
      `ell a b = L a (a+b)` oraz `ell (b+1) (a−b−1) = L (b+1) a` (bo `(b+1)+(a−b−1) = a`),
    i `Hi a b ↔ fphi (b+1) > a` przez `ineq_iff_beatty_dual` (ogniwo ①b).

    ⚠️ Próg `8 ≤ a` jest CIASNY, nie ostrożnościowy: pod nim leżą wszystkie wyjątki
    kaskady (`Pexc`: `a ≤ 7`, `Qexc`: `a = 4`) i teza PADA w dokładnie 6 punktach.

    STATUS EMPIRYCZNY (kontrola rachunku, nie przesłanka) — trzy okna:
    `M=400` → 19 680 par, `M=800` → 79 380, `M=1300` → 210 255. **Zero niezgodności
    w każdym oknie.**  Rozkład NIEZDEGENEROWANY (dla `a<60`: 659 razy TAK, 1031 razy NIE),
    więc „0 niezgodności" nie znaczy „zawsze fałsz = zawsze fałsz". -/
theorem core_le_dual (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) (hba : b < a) :
    (L a (a+b) ≤ L (b+1) a ↔ fphi (b+1) > a) := by
  have h := core_le_dual_ell a b ha hb hba
  have e : (b+1) + (a-b-1) = a := by omega
  simp only [ell, e] at h
  rw [h]
  exact ineq_iff_beatty_dual a b (Nat.le_of_lt hba)

/-- To samo w postaci pierwotnej (przez próg `⌊(a+1)φ⌋`).
    Wyprowadzone z `core_le_dual`, BEZ własnego `sorry`. -/
theorem core_le (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) (hba : b < a) :
    (L a (a+b) ≤ L (b+1) a ↔ fphi (a+1) ≤ a + b + 1) := by
  rw [core_le_dual a b ha hb hba, beatty_forms_agree a b (Nat.le_of_lt hba)]

/-- Przypadek `1 ≤ b ≤ a−1`, wyprowadzony Z `core_le` W CAŁOŚCI (bez własnego `sorry`). -/
theorem A_lemat_case_b_lt_a (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) (hba : b < a) :
    (L a (a+b+1) = L a (a+b) + 1 ↔ (a + 2*b + 3)^2 > 5*(a+1)^2) := by
  cases a with
  | zero => omega
  | succ j =>
    have h1 : (j+1) < (j+1)+b+1 := by omega
    have h2 : (j+1)+b+1 ≤ 2*(j+1) := by omega
    have hstep := L_step_two j ((j+1)+b+1) h1 h2
    have he : (j+1)+b+1-1 = (j+1)+b := by omega
    have he2 : (j+1)+b+1-(j+1) = b+1 := by omega
    rw [he, he2] at hstep
    rw [hstep, ineq_iff_beatty]
    rw [← core_le (j+1) b ha hb hba]
    constructor
    · intro h
      have := Nat.min_le_left (L (j+1) ((j+1)+b)) (L (b+1) (j+1))
      have := Nat.min_le_right (L (j+1) ((j+1)+b)) (L (b+1) (j+1))
      omega
    · intro h
      have : min (L (j+1) ((j+1)+b)) (L (b+1) (j+1)) = L (j+1) ((j+1)+b) :=
        Nat.min_eq_left h
      omega

/-! ## 7.  A-LEMAT — teza główna, złożona z ② i ③ -/

/-- **A-LEMAT.**  Dla `a ≥ 8`, `b ≥ 1`, w układzie `(a,b) = (j, k−j)`:
    krok `A` zwiększa numer pokolenia o 1 ⟺ `(a+2b+3)² > 5(a+1)²`.

    Zależy WYŁĄCZNIE od `core_le` (ogniwo ③).  Ogniwa ① i ② są udowodnione. -/
theorem A_lemat (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    (L a (a+b+1) = L a (a+b) + 1 ↔ (a + 2*b + 3)^2 > 5*(a+1)^2) := by
  rcases Nat.lt_or_ge b a with h | h
  · exact A_lemat_case_b_lt_a a b ha hb h
  · exact A_lemat_case_b_ge_a a b ha h

/-! ## 8.  KONTROLA UJEMNA — teza w ZŁYM układzie współrzędnych jest FAŁSZEM

Do 22.08 repo zapisywało A-lemat w układzie `(a,b) = (j,k)`.  Zmierzone (BFS, `j,k ≤ 400`):
**30 177 kontrprzykładów na 77 028 węzłów** — wobec ZERA w układzie `(j, k−j)`.
Najmniejszy świadek to `(j,k) = (8,9)`: nierówność w złym układzie mówi TAK
(`(8+2·9+3)² = 841 > 405`), a `L` przy kroku A nie rośnie — ONO SPADA, `10 → 9`. -/

theorem wrong_frame_is_false :
    L 8 9 = 10 ∧ L 8 10 = 9 ∧ (8 + 2*9 + 3)^2 > 5*(8+1)^2 := by native_decide

/-- Świadek, że próg `8 ≤ a` jest CIASNY: w `(j,k) = (7,11)`, czyli `(a,b) = (7,4)`,
    nierówność zachodzi (`(7+8+3)² = 324 > 320`), a `L` przy kroku A NIE rośnie. -/
theorem threshold_8_is_tight :
    L 7 11 = 7 ∧ L 7 12 = 7 ∧ (7 + 2*4 + 3)^2 > 5*(7+1)^2 := by native_decide

/-- I drugi typ świadka spod progu — `(j,k) = (4,6)`, `(a,b) = (4,2)`:
    tu `L` ROŚNIE, a nierówność NIE zachodzi (`(4+4+3)² = 121 < 125`).
    Czyli pod progiem padają OBIE strony równoważności, nie jedna. -/
theorem threshold_8_is_tight_other_way :
    L 4 6 = 5 ∧ L 4 7 = 6 ∧ ¬ ((4 + 2*2 + 3)^2 > 5*(4+1)^2) := by native_decide

end A252864.ALemat
