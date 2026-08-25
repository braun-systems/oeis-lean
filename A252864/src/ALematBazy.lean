/-
  A252864 — ALematBazy.lean.  BAZY INDUKCJI dla A-lematu.
  Lean 4.34.0-rc2, BEZ Mathlib, BEZ `sorry`.

  DWIE RZECZY:
    (A) `[W11.3]` — rodzina `ℓ(k,k−1) ≤ k+1` dla `k ≥ 6`, indukcja po `k`
        z krokiem `ell_add_phi2` (moneta `v₂ = φ²`) i bazą `ℓ(6,5) = 7`.
    (B) skończone wartości `ell` z kaskady wyjątków `LEM_A_wstecz.md [W10]`.

  🔑 JAK ZDOBYTE SĄ WARTOŚCI SKOŃCZONE — to jest cała trudność tego pliku.
  `decide` NIE DZIAŁA na `L`: rekursja jest dobrze ufundowana, więc jądro nie
  redukuje jej do wartości ("reduction got stuck at the Decidable instance").
  `native_decide` też NIE JEST tu użyte.  Zamiast tego każda wartość jest
  ROZWINIĘTA W JĄDRZE: `ell_two3` / `ell_one3` (przepisania rekurencji bez
  odejmowania) stosowane po kolei, aż do przypadków brzegowych `ell a 0 = a+1`
  i `ell 0 b = b`.  Domknięcie rekurencyjne wszystkich celów ma 232 węzły
  i wszystkie są tu wypisane (po rundzie 2: 232).  ⇒ **CAŁY PLIK STOI NA JĄDRZE.**
-/
import ALematRep

namespace A252864.ALemat

/-! ## 0.  Przepisania rekurencji BEZ ODEJMOWANIA

`ell_rec_two` / `ell_rec_one` mają w tezie `b-1` i `a-b`.  Na literałach
`rw` nie dopasuje `ell 6 (5-1)` do `ell 6 4`.  Poniższe warianty przenoszą
odejmowanie do hipotez równościowych, dowodzonych przez `omega`. -/

/-- Rekurencja dwóch rodziców, wariant literałowy: `b = b'+1`, `a = b + c`. -/
theorem ell_two3 (a b b' c : Nat) (hb : b = b' + 1) (hc : a = b + c) :
    ell a b = 1 + min (ell a b') (ell b c) := by
  have h1 : 1 ≤ b := by omega
  have h2 : b ≤ a := by omega
  have hstep := ell_rec_two a b h1 h2
  have e1 : b - 1 = b' := by omega
  have e2 : a - b = c := by omega
  rw [e1, e2] at hstep
  exact hstep

/-- Rekurencja jednego rodzica, wariant literałowy: `b = b'+1`, `a < b`. -/
theorem ell_one3 (a b b' : Nat) (hb : b = b' + 1) (hab : a < b) :
    ell a b = 1 + ell a b' := by
  have h1 : 1 ≤ b := by omega
  have hstep := ell_rec_one a b h1 hab
  have e1 : b - 1 = b' := by omega
  rw [e1] at hstep
  exact hstep

/-! ## 1.  DRABINA WARTOŚCI — 232 węzłów domknięcia rekurencyjnego

Wygenerowane mechanicznie z rekurencji, ale KAŻDE stoi na jądrze: `ell_two3`
/ `ell_one3` + wartości niższe.  Kontrola niezależna: własne BFS po grafie
`A:(a,b)→(a,b+1)`, `B:(a,b)→(a+b,a)` ze startem `(0,0)` — 0 niezgodności
z tą rekurencją na wszystkich `(a,b)` z `a,b ≤ 60`. -/

private theorem e_6_0 : ell 6 0 = 7 := ell_a0 6 (by omega)
private theorem e_1_0 : ell 1 0 = 2 := ell_a0 1 (by omega)
private theorem e_1_1 : ell 1 1 = 3 := by
  have h := ell_two3 1 1 0 0 (by omega) (by omega)
  rw [e_1_0] at h
  omega
private theorem e_1_2 : ell 1 2 = 4 := by
  have h := ell_one3 1 2 1 (by omega) (by omega)
  rw [e_1_1] at h
  omega
private theorem e_1_3 : ell 1 3 = 5 := by
  have h := ell_one3 1 3 2 (by omega) (by omega)
  rw [e_1_2] at h
  omega
private theorem e_1_4 : ell 1 4 = 6 := by
  have h := ell_one3 1 4 3 (by omega) (by omega)
  rw [e_1_3] at h
  omega
private theorem e_1_5 : ell 1 5 = 7 := by
  have h := ell_one3 1 5 4 (by omega) (by omega)
  rw [e_1_4] at h
  omega
private theorem e_6_1 : ell 6 1 = 8 := by
  have h := ell_two3 6 1 0 5 (by omega) (by omega)
  rw [e_6_0, e_1_5] at h
  omega
private theorem e_2_0 : ell 2 0 = 3 := ell_a0 2 (by omega)
private theorem e_2_1 : ell 2 1 = 4 := by
  have h := ell_two3 2 1 0 1 (by omega) (by omega)
  rw [e_2_0, e_1_1] at h
  omega
private theorem e_2_2 : ell 2 2 = 4 := by
  have h := ell_two3 2 2 1 0 (by omega) (by omega)
  rw [e_2_1, e_2_0] at h
  omega
private theorem e_2_3 : ell 2 3 = 5 := by
  have h := ell_one3 2 3 2 (by omega) (by omega)
  rw [e_2_2] at h
  omega
private theorem e_2_4 : ell 2 4 = 6 := by
  have h := ell_one3 2 4 3 (by omega) (by omega)
  rw [e_2_3] at h
  omega
private theorem e_6_2 : ell 6 2 = 7 := by
  have h := ell_two3 6 2 1 4 (by omega) (by omega)
  rw [e_6_1, e_2_4] at h
  omega
private theorem e_3_0 : ell 3 0 = 4 := ell_a0 3 (by omega)
private theorem e_3_1 : ell 3 1 = 5 := by
  have h := ell_two3 3 1 0 2 (by omega) (by omega)
  rw [e_3_0, e_1_2] at h
  omega
private theorem e_3_2 : ell 3 2 = 5 := by
  have h := ell_two3 3 2 1 1 (by omega) (by omega)
  rw [e_3_1, e_2_1] at h
  omega
private theorem e_3_3 : ell 3 3 = 5 := by
  have h := ell_two3 3 3 2 0 (by omega) (by omega)
  rw [e_3_2, e_3_0] at h
  omega
private theorem e_6_3 : ell 6 3 = 6 := by
  have h := ell_two3 6 3 2 3 (by omega) (by omega)
  rw [e_6_2, e_3_3] at h
  omega
private theorem e_4_0 : ell 4 0 = 5 := ell_a0 4 (by omega)
private theorem e_4_1 : ell 4 1 = 6 := by
  have h := ell_two3 4 1 0 3 (by omega) (by omega)
  rw [e_4_0, e_1_3] at h
  omega
private theorem e_4_2 : ell 4 2 = 5 := by
  have h := ell_two3 4 2 1 2 (by omega) (by omega)
  rw [e_4_1, e_2_2] at h
  omega
private theorem e_6_4 : ell 6 4 = 6 := by
  have h := ell_two3 6 4 3 2 (by omega) (by omega)
  rw [e_6_3, e_4_2] at h
  omega
private theorem e_5_0 : ell 5 0 = 6 := ell_a0 5 (by omega)
private theorem e_5_1 : ell 5 1 = 7 := by
  have h := ell_two3 5 1 0 4 (by omega) (by omega)
  rw [e_5_0, e_1_4] at h
  omega
private theorem e_6_5 : ell 6 5 = 7 := by
  have h := ell_two3 6 5 4 1 (by omega) (by omega)
  rw [e_6_4, e_5_1] at h
  omega
private theorem e_10_0 : ell 10 0 = 11 := ell_a0 10 (by omega)
private theorem e_1_6 : ell 1 6 = 8 := by
  have h := ell_one3 1 6 5 (by omega) (by omega)
  rw [e_1_5] at h
  omega
private theorem e_1_7 : ell 1 7 = 9 := by
  have h := ell_one3 1 7 6 (by omega) (by omega)
  rw [e_1_6] at h
  omega
private theorem e_1_8 : ell 1 8 = 10 := by
  have h := ell_one3 1 8 7 (by omega) (by omega)
  rw [e_1_7] at h
  omega
private theorem e_1_9 : ell 1 9 = 11 := by
  have h := ell_one3 1 9 8 (by omega) (by omega)
  rw [e_1_8] at h
  omega
private theorem e_10_1 : ell 10 1 = 12 := by
  have h := ell_two3 10 1 0 9 (by omega) (by omega)
  rw [e_10_0, e_1_9] at h
  omega
private theorem e_2_5 : ell 2 5 = 7 := by
  have h := ell_one3 2 5 4 (by omega) (by omega)
  rw [e_2_4] at h
  omega
private theorem e_2_6 : ell 2 6 = 8 := by
  have h := ell_one3 2 6 5 (by omega) (by omega)
  rw [e_2_5] at h
  omega
private theorem e_2_7 : ell 2 7 = 9 := by
  have h := ell_one3 2 7 6 (by omega) (by omega)
  rw [e_2_6] at h
  omega
private theorem e_2_8 : ell 2 8 = 10 := by
  have h := ell_one3 2 8 7 (by omega) (by omega)
  rw [e_2_7] at h
  omega
private theorem e_10_2 : ell 10 2 = 11 := by
  have h := ell_two3 10 2 1 8 (by omega) (by omega)
  rw [e_10_1, e_2_8] at h
  omega
private theorem e_3_4 : ell 3 4 = 6 := by
  have h := ell_one3 3 4 3 (by omega) (by omega)
  rw [e_3_3] at h
  omega
private theorem e_3_5 : ell 3 5 = 7 := by
  have h := ell_one3 3 5 4 (by omega) (by omega)
  rw [e_3_4] at h
  omega
private theorem e_3_6 : ell 3 6 = 8 := by
  have h := ell_one3 3 6 5 (by omega) (by omega)
  rw [e_3_5] at h
  omega
private theorem e_3_7 : ell 3 7 = 9 := by
  have h := ell_one3 3 7 6 (by omega) (by omega)
  rw [e_3_6] at h
  omega
private theorem e_10_3 : ell 10 3 = 10 := by
  have h := ell_two3 10 3 2 7 (by omega) (by omega)
  rw [e_10_2, e_3_7] at h
  omega
private theorem e_4_3 : ell 4 3 = 6 := by
  have h := ell_two3 4 3 2 1 (by omega) (by omega)
  rw [e_4_2, e_3_1] at h
  omega
private theorem e_4_4 : ell 4 4 = 6 := by
  have h := ell_two3 4 4 3 0 (by omega) (by omega)
  rw [e_4_3, e_4_0] at h
  omega
private theorem e_4_5 : ell 4 5 = 7 := by
  have h := ell_one3 4 5 4 (by omega) (by omega)
  rw [e_4_4] at h
  omega
private theorem e_4_6 : ell 4 6 = 8 := by
  have h := ell_one3 4 6 5 (by omega) (by omega)
  rw [e_4_5] at h
  omega
private theorem e_10_4 : ell 10 4 = 9 := by
  have h := ell_two3 10 4 3 6 (by omega) (by omega)
  rw [e_10_3, e_4_6] at h
  omega
private theorem e_5_2 : ell 5 2 = 6 := by
  have h := ell_two3 5 2 1 3 (by omega) (by omega)
  rw [e_5_1, e_2_3] at h
  omega
private theorem e_5_3 : ell 5 3 = 6 := by
  have h := ell_two3 5 3 2 2 (by omega) (by omega)
  rw [e_5_2, e_3_2] at h
  omega
private theorem e_5_4 : ell 5 4 = 7 := by
  have h := ell_two3 5 4 3 1 (by omega) (by omega)
  rw [e_5_3, e_4_1] at h
  omega
private theorem e_5_5 : ell 5 5 = 7 := by
  have h := ell_two3 5 5 4 0 (by omega) (by omega)
  rw [e_5_4, e_5_0] at h
  omega
private theorem e_10_5 : ell 10 5 = 8 := by
  have h := ell_two3 10 5 4 5 (by omega) (by omega)
  rw [e_10_4, e_5_5] at h
  omega
private theorem e_10_6 : ell 10 6 = 7 := by
  have h := ell_two3 10 6 5 4 (by omega) (by omega)
  rw [e_10_5, e_6_4] at h
  omega
private theorem e_7_0 : ell 7 0 = 8 := ell_a0 7 (by omega)
private theorem e_7_1 : ell 7 1 = 9 := by
  have h := ell_two3 7 1 0 6 (by omega) (by omega)
  rw [e_7_0, e_1_6] at h
  omega
private theorem e_7_2 : ell 7 2 = 8 := by
  have h := ell_two3 7 2 1 5 (by omega) (by omega)
  rw [e_7_1, e_2_5] at h
  omega
private theorem e_7_3 : ell 7 3 = 7 := by
  have h := ell_two3 7 3 2 4 (by omega) (by omega)
  rw [e_7_2, e_3_4] at h
  omega
private theorem e_10_7 : ell 10 7 = 8 := by
  have h := ell_two3 10 7 6 3 (by omega) (by omega)
  rw [e_10_6, e_7_3] at h
  omega
private theorem e_11_0 : ell 11 0 = 12 := ell_a0 11 (by omega)
private theorem e_1_10 : ell 1 10 = 12 := by
  have h := ell_one3 1 10 9 (by omega) (by omega)
  rw [e_1_9] at h
  omega
private theorem e_11_1 : ell 11 1 = 13 := by
  have h := ell_two3 11 1 0 10 (by omega) (by omega)
  rw [e_11_0, e_1_10] at h
  omega
private theorem e_2_9 : ell 2 9 = 11 := by
  have h := ell_one3 2 9 8 (by omega) (by omega)
  rw [e_2_8] at h
  omega
private theorem e_11_2 : ell 11 2 = 12 := by
  have h := ell_two3 11 2 1 9 (by omega) (by omega)
  rw [e_11_1, e_2_9] at h
  omega
private theorem e_3_8 : ell 3 8 = 10 := by
  have h := ell_one3 3 8 7 (by omega) (by omega)
  rw [e_3_7] at h
  omega
private theorem e_11_3 : ell 11 3 = 11 := by
  have h := ell_two3 11 3 2 8 (by omega) (by omega)
  rw [e_11_2, e_3_8] at h
  omega
private theorem e_4_7 : ell 4 7 = 9 := by
  have h := ell_one3 4 7 6 (by omega) (by omega)
  rw [e_4_6] at h
  omega
private theorem e_11_4 : ell 11 4 = 10 := by
  have h := ell_two3 11 4 3 7 (by omega) (by omega)
  rw [e_11_3, e_4_7] at h
  omega
private theorem e_5_6 : ell 5 6 = 8 := by
  have h := ell_one3 5 6 5 (by omega) (by omega)
  rw [e_5_5] at h
  omega
private theorem e_11_5 : ell 11 5 = 9 := by
  have h := ell_two3 11 5 4 6 (by omega) (by omega)
  rw [e_11_4, e_5_6] at h
  omega
private theorem e_11_6 : ell 11 6 = 8 := by
  have h := ell_two3 11 6 5 5 (by omega) (by omega)
  rw [e_11_5, e_6_5] at h
  omega
private theorem e_7_4 : ell 7 4 = 7 := by
  have h := ell_two3 7 4 3 3 (by omega) (by omega)
  rw [e_7_3, e_4_3] at h
  omega
private theorem e_11_7 : ell 11 7 = 8 := by
  have h := ell_two3 11 7 6 4 (by omega) (by omega)
  rw [e_11_6, e_7_4] at h
  omega
private theorem e_8_0 : ell 8 0 = 9 := ell_a0 8 (by omega)
private theorem e_8_1 : ell 8 1 = 10 := by
  have h := ell_two3 8 1 0 7 (by omega) (by omega)
  rw [e_8_0, e_1_7] at h
  omega
private theorem e_8_2 : ell 8 2 = 9 := by
  have h := ell_two3 8 2 1 6 (by omega) (by omega)
  rw [e_8_1, e_2_6] at h
  omega
private theorem e_8_3 : ell 8 3 = 8 := by
  have h := ell_two3 8 3 2 5 (by omega) (by omega)
  rw [e_8_2, e_3_5] at h
  omega
private theorem e_11_8 : ell 11 8 = 9 := by
  have h := ell_two3 11 8 7 3 (by omega) (by omega)
  rw [e_11_7, e_8_3] at h
  omega
private theorem e_13_0 : ell 13 0 = 14 := ell_a0 13 (by omega)
private theorem e_1_11 : ell 1 11 = 13 := by
  have h := ell_one3 1 11 10 (by omega) (by omega)
  rw [e_1_10] at h
  omega
private theorem e_1_12 : ell 1 12 = 14 := by
  have h := ell_one3 1 12 11 (by omega) (by omega)
  rw [e_1_11] at h
  omega
private theorem e_13_1 : ell 13 1 = 15 := by
  have h := ell_two3 13 1 0 12 (by omega) (by omega)
  rw [e_13_0, e_1_12] at h
  omega
private theorem e_2_10 : ell 2 10 = 12 := by
  have h := ell_one3 2 10 9 (by omega) (by omega)
  rw [e_2_9] at h
  omega
private theorem e_2_11 : ell 2 11 = 13 := by
  have h := ell_one3 2 11 10 (by omega) (by omega)
  rw [e_2_10] at h
  omega
private theorem e_13_2 : ell 13 2 = 14 := by
  have h := ell_two3 13 2 1 11 (by omega) (by omega)
  rw [e_13_1, e_2_11] at h
  omega
private theorem e_3_9 : ell 3 9 = 11 := by
  have h := ell_one3 3 9 8 (by omega) (by omega)
  rw [e_3_8] at h
  omega
private theorem e_3_10 : ell 3 10 = 12 := by
  have h := ell_one3 3 10 9 (by omega) (by omega)
  rw [e_3_9] at h
  omega
private theorem e_13_3 : ell 13 3 = 13 := by
  have h := ell_two3 13 3 2 10 (by omega) (by omega)
  rw [e_13_2, e_3_10] at h
  omega
private theorem e_4_8 : ell 4 8 = 10 := by
  have h := ell_one3 4 8 7 (by omega) (by omega)
  rw [e_4_7] at h
  omega
private theorem e_4_9 : ell 4 9 = 11 := by
  have h := ell_one3 4 9 8 (by omega) (by omega)
  rw [e_4_8] at h
  omega
private theorem e_13_4 : ell 13 4 = 12 := by
  have h := ell_two3 13 4 3 9 (by omega) (by omega)
  rw [e_13_3, e_4_9] at h
  omega
private theorem e_5_7 : ell 5 7 = 9 := by
  have h := ell_one3 5 7 6 (by omega) (by omega)
  rw [e_5_6] at h
  omega
private theorem e_5_8 : ell 5 8 = 10 := by
  have h := ell_one3 5 8 7 (by omega) (by omega)
  rw [e_5_7] at h
  omega
private theorem e_13_5 : ell 13 5 = 11 := by
  have h := ell_two3 13 5 4 8 (by omega) (by omega)
  rw [e_13_4, e_5_8] at h
  omega
private theorem e_6_6 : ell 6 6 = 8 := by
  have h := ell_two3 6 6 5 0 (by omega) (by omega)
  rw [e_6_5, e_6_0] at h
  omega
private theorem e_6_7 : ell 6 7 = 9 := by
  have h := ell_one3 6 7 6 (by omega) (by omega)
  rw [e_6_6] at h
  omega
private theorem e_13_6 : ell 13 6 = 10 := by
  have h := ell_two3 13 6 5 7 (by omega) (by omega)
  rw [e_13_5, e_6_7] at h
  omega
private theorem e_7_5 : ell 7 5 = 7 := by
  have h := ell_two3 7 5 4 2 (by omega) (by omega)
  rw [e_7_4, e_5_2] at h
  omega
private theorem e_7_6 : ell 7 6 = 8 := by
  have h := ell_two3 7 6 5 1 (by omega) (by omega)
  rw [e_7_5, e_6_1] at h
  omega
private theorem e_13_7 : ell 13 7 = 9 := by
  have h := ell_two3 13 7 6 6 (by omega) (by omega)
  rw [e_13_6, e_7_6] at h
  omega
private theorem e_8_4 : ell 8 4 = 7 := by
  have h := ell_two3 8 4 3 4 (by omega) (by omega)
  rw [e_8_3, e_4_4] at h
  omega
private theorem e_8_5 : ell 8 5 = 7 := by
  have h := ell_two3 8 5 4 3 (by omega) (by omega)
  rw [e_8_4, e_5_3] at h
  omega
private theorem e_13_8 : ell 13 8 = 8 := by
  have h := ell_two3 13 8 7 5 (by omega) (by omega)
  rw [e_13_7, e_8_5] at h
  omega
private theorem e_9_0 : ell 9 0 = 10 := ell_a0 9 (by omega)
private theorem e_9_1 : ell 9 1 = 11 := by
  have h := ell_two3 9 1 0 8 (by omega) (by omega)
  rw [e_9_0, e_1_8] at h
  omega
private theorem e_9_2 : ell 9 2 = 10 := by
  have h := ell_two3 9 2 1 7 (by omega) (by omega)
  rw [e_9_1, e_2_7] at h
  omega
private theorem e_9_3 : ell 9 3 = 9 := by
  have h := ell_two3 9 3 2 6 (by omega) (by omega)
  rw [e_9_2, e_3_6] at h
  omega
private theorem e_9_4 : ell 9 4 = 8 := by
  have h := ell_two3 9 4 3 5 (by omega) (by omega)
  rw [e_9_3, e_4_5] at h
  omega
private theorem e_13_9 : ell 13 9 = 9 := by
  have h := ell_two3 13 9 8 4 (by omega) (by omega)
  rw [e_13_8, e_9_4] at h
  omega
private theorem e_14_0 : ell 14 0 = 15 := ell_a0 14 (by omega)
private theorem e_1_13 : ell 1 13 = 15 := by
  have h := ell_one3 1 13 12 (by omega) (by omega)
  rw [e_1_12] at h
  omega
private theorem e_14_1 : ell 14 1 = 16 := by
  have h := ell_two3 14 1 0 13 (by omega) (by omega)
  rw [e_14_0, e_1_13] at h
  omega
private theorem e_2_12 : ell 2 12 = 14 := by
  have h := ell_one3 2 12 11 (by omega) (by omega)
  rw [e_2_11] at h
  omega
private theorem e_14_2 : ell 14 2 = 15 := by
  have h := ell_two3 14 2 1 12 (by omega) (by omega)
  rw [e_14_1, e_2_12] at h
  omega
private theorem e_3_11 : ell 3 11 = 13 := by
  have h := ell_one3 3 11 10 (by omega) (by omega)
  rw [e_3_10] at h
  omega
private theorem e_14_3 : ell 14 3 = 14 := by
  have h := ell_two3 14 3 2 11 (by omega) (by omega)
  rw [e_14_2, e_3_11] at h
  omega
private theorem e_4_10 : ell 4 10 = 12 := by
  have h := ell_one3 4 10 9 (by omega) (by omega)
  rw [e_4_9] at h
  omega
private theorem e_14_4 : ell 14 4 = 13 := by
  have h := ell_two3 14 4 3 10 (by omega) (by omega)
  rw [e_14_3, e_4_10] at h
  omega
private theorem e_5_9 : ell 5 9 = 11 := by
  have h := ell_one3 5 9 8 (by omega) (by omega)
  rw [e_5_8] at h
  omega
private theorem e_14_5 : ell 14 5 = 12 := by
  have h := ell_two3 14 5 4 9 (by omega) (by omega)
  rw [e_14_4, e_5_9] at h
  omega
private theorem e_6_8 : ell 6 8 = 10 := by
  have h := ell_one3 6 8 7 (by omega) (by omega)
  rw [e_6_7] at h
  omega
private theorem e_14_6 : ell 14 6 = 11 := by
  have h := ell_two3 14 6 5 8 (by omega) (by omega)
  rw [e_14_5, e_6_8] at h
  omega
private theorem e_7_7 : ell 7 7 = 9 := by
  have h := ell_two3 7 7 6 0 (by omega) (by omega)
  rw [e_7_6, e_7_0] at h
  omega
private theorem e_14_7 : ell 14 7 = 10 := by
  have h := ell_two3 14 7 6 7 (by omega) (by omega)
  rw [e_14_6, e_7_7] at h
  omega
private theorem e_8_6 : ell 8 6 = 8 := by
  have h := ell_two3 8 6 5 2 (by omega) (by omega)
  rw [e_8_5, e_6_2] at h
  omega
private theorem e_14_8 : ell 14 8 = 9 := by
  have h := ell_two3 14 8 7 6 (by omega) (by omega)
  rw [e_14_7, e_8_6] at h
  omega
private theorem e_9_5 : ell 9 5 = 8 := by
  have h := ell_two3 9 5 4 4 (by omega) (by omega)
  rw [e_9_4, e_5_4] at h
  omega
private theorem e_14_9 : ell 14 9 = 9 := by
  have h := ell_two3 14 9 8 5 (by omega) (by omega)
  rw [e_14_8, e_9_5] at h
  omega
private theorem e_14_10 : ell 14 10 = 10 := by
  have h := ell_two3 14 10 9 4 (by omega) (by omega)
  rw [e_14_9, e_10_4] at h
  omega
private theorem e_15_0 : ell 15 0 = 16 := ell_a0 15 (by omega)
private theorem e_1_14 : ell 1 14 = 16 := by
  have h := ell_one3 1 14 13 (by omega) (by omega)
  rw [e_1_13] at h
  omega
private theorem e_15_1 : ell 15 1 = 17 := by
  have h := ell_two3 15 1 0 14 (by omega) (by omega)
  rw [e_15_0, e_1_14] at h
  omega
private theorem e_2_13 : ell 2 13 = 15 := by
  have h := ell_one3 2 13 12 (by omega) (by omega)
  rw [e_2_12] at h
  omega
private theorem e_15_2 : ell 15 2 = 16 := by
  have h := ell_two3 15 2 1 13 (by omega) (by omega)
  rw [e_15_1, e_2_13] at h
  omega
private theorem e_3_12 : ell 3 12 = 14 := by
  have h := ell_one3 3 12 11 (by omega) (by omega)
  rw [e_3_11] at h
  omega
private theorem e_15_3 : ell 15 3 = 15 := by
  have h := ell_two3 15 3 2 12 (by omega) (by omega)
  rw [e_15_2, e_3_12] at h
  omega
private theorem e_4_11 : ell 4 11 = 13 := by
  have h := ell_one3 4 11 10 (by omega) (by omega)
  rw [e_4_10] at h
  omega
private theorem e_15_4 : ell 15 4 = 14 := by
  have h := ell_two3 15 4 3 11 (by omega) (by omega)
  rw [e_15_3, e_4_11] at h
  omega
private theorem e_5_10 : ell 5 10 = 12 := by
  have h := ell_one3 5 10 9 (by omega) (by omega)
  rw [e_5_9] at h
  omega
private theorem e_15_5 : ell 15 5 = 13 := by
  have h := ell_two3 15 5 4 10 (by omega) (by omega)
  rw [e_15_4, e_5_10] at h
  omega
private theorem e_6_9 : ell 6 9 = 11 := by
  have h := ell_one3 6 9 8 (by omega) (by omega)
  rw [e_6_8] at h
  omega
private theorem e_15_6 : ell 15 6 = 12 := by
  have h := ell_two3 15 6 5 9 (by omega) (by omega)
  rw [e_15_5, e_6_9] at h
  omega
private theorem e_7_8 : ell 7 8 = 10 := by
  have h := ell_one3 7 8 7 (by omega) (by omega)
  rw [e_7_7] at h
  omega
private theorem e_15_7 : ell 15 7 = 11 := by
  have h := ell_two3 15 7 6 8 (by omega) (by omega)
  rw [e_15_6, e_7_8] at h
  omega
private theorem e_8_7 : ell 8 7 = 9 := by
  have h := ell_two3 8 7 6 1 (by omega) (by omega)
  rw [e_8_6, e_7_1] at h
  omega
private theorem e_15_8 : ell 15 8 = 10 := by
  have h := ell_two3 15 8 7 7 (by omega) (by omega)
  rw [e_15_7, e_8_7] at h
  omega
private theorem e_9_6 : ell 9 6 = 7 := by
  have h := ell_two3 9 6 5 3 (by omega) (by omega)
  rw [e_9_5, e_6_3] at h
  omega
private theorem e_15_9 : ell 15 9 = 8 := by
  have h := ell_two3 15 9 8 6 (by omega) (by omega)
  rw [e_15_8, e_9_6] at h
  omega
private theorem e_15_10 : ell 15 10 = 9 := by
  have h := ell_two3 15 10 9 5 (by omega) (by omega)
  rw [e_15_9, e_10_5] at h
  omega
private theorem e_16_0 : ell 16 0 = 17 := ell_a0 16 (by omega)
private theorem e_1_15 : ell 1 15 = 17 := by
  have h := ell_one3 1 15 14 (by omega) (by omega)
  rw [e_1_14] at h
  omega
private theorem e_16_1 : ell 16 1 = 18 := by
  have h := ell_two3 16 1 0 15 (by omega) (by omega)
  rw [e_16_0, e_1_15] at h
  omega
private theorem e_2_14 : ell 2 14 = 16 := by
  have h := ell_one3 2 14 13 (by omega) (by omega)
  rw [e_2_13] at h
  omega
private theorem e_16_2 : ell 16 2 = 17 := by
  have h := ell_two3 16 2 1 14 (by omega) (by omega)
  rw [e_16_1, e_2_14] at h
  omega
private theorem e_3_13 : ell 3 13 = 15 := by
  have h := ell_one3 3 13 12 (by omega) (by omega)
  rw [e_3_12] at h
  omega
private theorem e_16_3 : ell 16 3 = 16 := by
  have h := ell_two3 16 3 2 13 (by omega) (by omega)
  rw [e_16_2, e_3_13] at h
  omega
private theorem e_4_12 : ell 4 12 = 14 := by
  have h := ell_one3 4 12 11 (by omega) (by omega)
  rw [e_4_11] at h
  omega
private theorem e_16_4 : ell 16 4 = 15 := by
  have h := ell_two3 16 4 3 12 (by omega) (by omega)
  rw [e_16_3, e_4_12] at h
  omega
private theorem e_5_11 : ell 5 11 = 13 := by
  have h := ell_one3 5 11 10 (by omega) (by omega)
  rw [e_5_10] at h
  omega
private theorem e_16_5 : ell 16 5 = 14 := by
  have h := ell_two3 16 5 4 11 (by omega) (by omega)
  rw [e_16_4, e_5_11] at h
  omega
private theorem e_6_10 : ell 6 10 = 12 := by
  have h := ell_one3 6 10 9 (by omega) (by omega)
  rw [e_6_9] at h
  omega
private theorem e_16_6 : ell 16 6 = 13 := by
  have h := ell_two3 16 6 5 10 (by omega) (by omega)
  rw [e_16_5, e_6_10] at h
  omega
private theorem e_7_9 : ell 7 9 = 11 := by
  have h := ell_one3 7 9 8 (by omega) (by omega)
  rw [e_7_8] at h
  omega
private theorem e_16_7 : ell 16 7 = 12 := by
  have h := ell_two3 16 7 6 9 (by omega) (by omega)
  rw [e_16_6, e_7_9] at h
  omega
private theorem e_8_8 : ell 8 8 = 10 := by
  have h := ell_two3 8 8 7 0 (by omega) (by omega)
  rw [e_8_7, e_8_0] at h
  omega
private theorem e_16_8 : ell 16 8 = 11 := by
  have h := ell_two3 16 8 7 8 (by omega) (by omega)
  rw [e_16_7, e_8_8] at h
  omega
private theorem e_9_7 : ell 9 7 = 8 := by
  have h := ell_two3 9 7 6 2 (by omega) (by omega)
  rw [e_9_6, e_7_2] at h
  omega
private theorem e_16_9 : ell 16 9 = 9 := by
  have h := ell_two3 16 9 8 7 (by omega) (by omega)
  rw [e_16_8, e_9_7] at h
  omega
private theorem e_16_10 : ell 16 10 = 8 := by
  have h := ell_two3 16 10 9 6 (by omega) (by omega)
  rw [e_16_9, e_10_6] at h
  omega
private theorem e_16_11 : ell 16 11 = 9 := by
  have h := ell_two3 16 11 10 5 (by omega) (by omega)
  rw [e_16_10, e_11_5] at h
  omega
private theorem e_20_0 : ell 20 0 = 21 := ell_a0 20 (by omega)
private theorem e_1_16 : ell 1 16 = 18 := by
  have h := ell_one3 1 16 15 (by omega) (by omega)
  rw [e_1_15] at h
  omega
private theorem e_1_17 : ell 1 17 = 19 := by
  have h := ell_one3 1 17 16 (by omega) (by omega)
  rw [e_1_16] at h
  omega
private theorem e_1_18 : ell 1 18 = 20 := by
  have h := ell_one3 1 18 17 (by omega) (by omega)
  rw [e_1_17] at h
  omega
private theorem e_1_19 : ell 1 19 = 21 := by
  have h := ell_one3 1 19 18 (by omega) (by omega)
  rw [e_1_18] at h
  omega
private theorem e_20_1 : ell 20 1 = 22 := by
  have h := ell_two3 20 1 0 19 (by omega) (by omega)
  rw [e_20_0, e_1_19] at h
  omega
private theorem e_2_15 : ell 2 15 = 17 := by
  have h := ell_one3 2 15 14 (by omega) (by omega)
  rw [e_2_14] at h
  omega
private theorem e_2_16 : ell 2 16 = 18 := by
  have h := ell_one3 2 16 15 (by omega) (by omega)
  rw [e_2_15] at h
  omega
private theorem e_2_17 : ell 2 17 = 19 := by
  have h := ell_one3 2 17 16 (by omega) (by omega)
  rw [e_2_16] at h
  omega
private theorem e_2_18 : ell 2 18 = 20 := by
  have h := ell_one3 2 18 17 (by omega) (by omega)
  rw [e_2_17] at h
  omega
private theorem e_20_2 : ell 20 2 = 21 := by
  have h := ell_two3 20 2 1 18 (by omega) (by omega)
  rw [e_20_1, e_2_18] at h
  omega
private theorem e_3_14 : ell 3 14 = 16 := by
  have h := ell_one3 3 14 13 (by omega) (by omega)
  rw [e_3_13] at h
  omega
private theorem e_3_15 : ell 3 15 = 17 := by
  have h := ell_one3 3 15 14 (by omega) (by omega)
  rw [e_3_14] at h
  omega
private theorem e_3_16 : ell 3 16 = 18 := by
  have h := ell_one3 3 16 15 (by omega) (by omega)
  rw [e_3_15] at h
  omega
private theorem e_3_17 : ell 3 17 = 19 := by
  have h := ell_one3 3 17 16 (by omega) (by omega)
  rw [e_3_16] at h
  omega
private theorem e_20_3 : ell 20 3 = 20 := by
  have h := ell_two3 20 3 2 17 (by omega) (by omega)
  rw [e_20_2, e_3_17] at h
  omega
private theorem e_4_13 : ell 4 13 = 15 := by
  have h := ell_one3 4 13 12 (by omega) (by omega)
  rw [e_4_12] at h
  omega
private theorem e_4_14 : ell 4 14 = 16 := by
  have h := ell_one3 4 14 13 (by omega) (by omega)
  rw [e_4_13] at h
  omega
private theorem e_4_15 : ell 4 15 = 17 := by
  have h := ell_one3 4 15 14 (by omega) (by omega)
  rw [e_4_14] at h
  omega
private theorem e_4_16 : ell 4 16 = 18 := by
  have h := ell_one3 4 16 15 (by omega) (by omega)
  rw [e_4_15] at h
  omega
private theorem e_20_4 : ell 20 4 = 19 := by
  have h := ell_two3 20 4 3 16 (by omega) (by omega)
  rw [e_20_3, e_4_16] at h
  omega
private theorem e_5_12 : ell 5 12 = 14 := by
  have h := ell_one3 5 12 11 (by omega) (by omega)
  rw [e_5_11] at h
  omega
private theorem e_5_13 : ell 5 13 = 15 := by
  have h := ell_one3 5 13 12 (by omega) (by omega)
  rw [e_5_12] at h
  omega
private theorem e_5_14 : ell 5 14 = 16 := by
  have h := ell_one3 5 14 13 (by omega) (by omega)
  rw [e_5_13] at h
  omega
private theorem e_5_15 : ell 5 15 = 17 := by
  have h := ell_one3 5 15 14 (by omega) (by omega)
  rw [e_5_14] at h
  omega
private theorem e_20_5 : ell 20 5 = 18 := by
  have h := ell_two3 20 5 4 15 (by omega) (by omega)
  rw [e_20_4, e_5_15] at h
  omega
private theorem e_6_11 : ell 6 11 = 13 := by
  have h := ell_one3 6 11 10 (by omega) (by omega)
  rw [e_6_10] at h
  omega
private theorem e_6_12 : ell 6 12 = 14 := by
  have h := ell_one3 6 12 11 (by omega) (by omega)
  rw [e_6_11] at h
  omega
private theorem e_6_13 : ell 6 13 = 15 := by
  have h := ell_one3 6 13 12 (by omega) (by omega)
  rw [e_6_12] at h
  omega
private theorem e_6_14 : ell 6 14 = 16 := by
  have h := ell_one3 6 14 13 (by omega) (by omega)
  rw [e_6_13] at h
  omega
private theorem e_20_6 : ell 20 6 = 17 := by
  have h := ell_two3 20 6 5 14 (by omega) (by omega)
  rw [e_20_5, e_6_14] at h
  omega
private theorem e_7_10 : ell 7 10 = 12 := by
  have h := ell_one3 7 10 9 (by omega) (by omega)
  rw [e_7_9] at h
  omega
private theorem e_7_11 : ell 7 11 = 13 := by
  have h := ell_one3 7 11 10 (by omega) (by omega)
  rw [e_7_10] at h
  omega
private theorem e_7_12 : ell 7 12 = 14 := by
  have h := ell_one3 7 12 11 (by omega) (by omega)
  rw [e_7_11] at h
  omega
private theorem e_7_13 : ell 7 13 = 15 := by
  have h := ell_one3 7 13 12 (by omega) (by omega)
  rw [e_7_12] at h
  omega
private theorem e_20_7 : ell 20 7 = 16 := by
  have h := ell_two3 20 7 6 13 (by omega) (by omega)
  rw [e_20_6, e_7_13] at h
  omega
private theorem e_8_9 : ell 8 9 = 11 := by
  have h := ell_one3 8 9 8 (by omega) (by omega)
  rw [e_8_8] at h
  omega
private theorem e_8_10 : ell 8 10 = 12 := by
  have h := ell_one3 8 10 9 (by omega) (by omega)
  rw [e_8_9] at h
  omega
private theorem e_8_11 : ell 8 11 = 13 := by
  have h := ell_one3 8 11 10 (by omega) (by omega)
  rw [e_8_10] at h
  omega
private theorem e_8_12 : ell 8 12 = 14 := by
  have h := ell_one3 8 12 11 (by omega) (by omega)
  rw [e_8_11] at h
  omega
private theorem e_20_8 : ell 20 8 = 15 := by
  have h := ell_two3 20 8 7 12 (by omega) (by omega)
  rw [e_20_7, e_8_12] at h
  omega
private theorem e_9_8 : ell 9 8 = 9 := by
  have h := ell_two3 9 8 7 1 (by omega) (by omega)
  rw [e_9_7, e_8_1] at h
  omega
private theorem e_9_9 : ell 9 9 = 10 := by
  have h := ell_two3 9 9 8 0 (by omega) (by omega)
  rw [e_9_8, e_9_0] at h
  omega
private theorem e_9_10 : ell 9 10 = 11 := by
  have h := ell_one3 9 10 9 (by omega) (by omega)
  rw [e_9_9] at h
  omega
private theorem e_9_11 : ell 9 11 = 12 := by
  have h := ell_one3 9 11 10 (by omega) (by omega)
  rw [e_9_10] at h
  omega
private theorem e_20_9 : ell 20 9 = 13 := by
  have h := ell_two3 20 9 8 11 (by omega) (by omega)
  rw [e_20_8, e_9_11] at h
  omega
private theorem e_10_8 : ell 10 8 = 9 := by
  have h := ell_two3 10 8 7 2 (by omega) (by omega)
  rw [e_10_7, e_8_2] at h
  omega
private theorem e_10_9 : ell 10 9 = 10 := by
  have h := ell_two3 10 9 8 1 (by omega) (by omega)
  rw [e_10_8, e_9_1] at h
  omega
private theorem e_10_10 : ell 10 10 = 11 := by
  have h := ell_two3 10 10 9 0 (by omega) (by omega)
  rw [e_10_9, e_10_0] at h
  omega
private theorem e_20_10 : ell 20 10 = 12 := by
  have h := ell_two3 20 10 9 10 (by omega) (by omega)
  rw [e_20_9, e_10_10] at h
  omega
private theorem e_11_9 : ell 11 9 = 10 := by
  have h := ell_two3 11 9 8 2 (by omega) (by omega)
  rw [e_11_8, e_9_2] at h
  omega
private theorem e_20_11 : ell 20 11 = 11 := by
  have h := ell_two3 20 11 10 9 (by omega) (by omega)
  rw [e_20_10, e_11_9] at h
  omega
private theorem e_12_0 : ell 12 0 = 13 := ell_a0 12 (by omega)
private theorem e_12_1 : ell 12 1 = 14 := by
  have h := ell_two3 12 1 0 11 (by omega) (by omega)
  rw [e_12_0, e_1_11] at h
  omega
private theorem e_12_2 : ell 12 2 = 13 := by
  have h := ell_two3 12 2 1 10 (by omega) (by omega)
  rw [e_12_1, e_2_10] at h
  omega
private theorem e_12_3 : ell 12 3 = 12 := by
  have h := ell_two3 12 3 2 9 (by omega) (by omega)
  rw [e_12_2, e_3_9] at h
  omega
private theorem e_12_4 : ell 12 4 = 11 := by
  have h := ell_two3 12 4 3 8 (by omega) (by omega)
  rw [e_12_3, e_4_8] at h
  omega
private theorem e_12_5 : ell 12 5 = 10 := by
  have h := ell_two3 12 5 4 7 (by omega) (by omega)
  rw [e_12_4, e_5_7] at h
  omega
private theorem e_12_6 : ell 12 6 = 9 := by
  have h := ell_two3 12 6 5 6 (by omega) (by omega)
  rw [e_12_5, e_6_6] at h
  omega
private theorem e_12_7 : ell 12 7 = 8 := by
  have h := ell_two3 12 7 6 5 (by omega) (by omega)
  rw [e_12_6, e_7_5] at h
  omega
private theorem e_12_8 : ell 12 8 = 8 := by
  have h := ell_two3 12 8 7 4 (by omega) (by omega)
  rw [e_12_7, e_8_4] at h
  omega
private theorem e_20_12 : ell 20 12 = 9 := by
  have h := ell_two3 20 12 11 8 (by omega) (by omega)
  rw [e_20_11, e_12_8] at h
  omega
private theorem e_20_13 : ell 20 13 = 10 := by
  have h := ell_two3 20 13 12 7 (by omega) (by omega)
  rw [e_20_12, e_13_7] at h
  omega

/-! ## 2.  CZĘŚĆ A — `[W11.3]`: rodzina `ℓ(k,k−1) ≤ k+1` dla `k ≥ 6`

Krok to `ell_add_phi2` (dodanie monety `v₂ = φ² = (1,1)`, czyli `[W7]`+`[W6.3–4]`+`[B3.1]`):
`ℓ(k,k−1) = ℓ((k−1)+1, (k−2)+1) ≤ ℓ(k−1,k−2) + 1`.
Baza to `ℓ(6,5) = 7` — zdobyta w §1, jądrowo.

⚠️ Próg `k ≥ 6` jest CIASNY, nie ostrożnościowy: `ℓ(k,k−1) = k+2` dla `k = 2,3,4,5`
(patrz §3, `ell_2_1 … ell_5_4`) — to są prawdziwe wyjątki `[W11.4]`, korzeń kaskady. -/

private theorem ell_diag_aux : ∀ m k j, k = m+6 → j = m+5 → ell k j ≤ m+7 := by
  intro m
  induction m with
  | zero =>
    intro k j hk hj
    subst hk; subst hj
    show ell 6 5 ≤ 7
    have h := e_6_5
    omega
  | succ n ih =>
    intro k j hk hj
    have h := ih (n+6) (n+5) rfl rfl
    have hstep := ell_add_phi2 (n+6) (n+5) (by omega) (by omega)
    have ek : k = (n+6)+1 := by omega
    have ej : j = (n+5)+1 := by omega
    subst ek; subst ej
    omega

/-- **`[W11.3]`** — `ℓ(k,k−1) ≤ k+1` dla `k ≥ 6`. -/
theorem ell_diag (k : Nat) (hk : 6 ≤ k) : ell k (k-1) ≤ k + 1 := by
  have h := ell_diag_aux (k-6) k (k-1) (by omega) (by omega)
  omega

/-- `[W11.1]` w zapisie prozy: `ℓ(k,0) = k+1`.  (Przepakowanie `ell_a0`.) -/
theorem ell_col0 (k : Nat) (hk : 1 ≤ k) : ell k 0 = k + 1 := ell_a0 k hk

/-- Wniosek `[W11.3]` ⟹ `ℓ(k,k−1) ≤ ℓ(k,0)` dla `k ≥ 6` — to jest ta postać,
    której używa proza (H2 w `LEM_A_wstecz.md`). -/
theorem ell_diag_le_col0 (k : Nat) (hk : 6 ≤ k) : ell k (k-1) ≤ ell k 0 := by
  have h1 := ell_diag k hk
  have h2 := ell_col0 k (by omega)
  omega

/-! ## 3.  CZĘŚĆ B — skończone wartości z kaskady wyjątków `[W10]`

Każda z tych liczb została zweryfikowana DWIEMA niezależnymi drogami:
① rozwinięciem rekurencji w jądrze Leana (§1),
② własnym BFS po grafie ruchów `A`/`B` ze startem `(0,0)` (Python, poza repo).
Obie drogi dają te same wartości i obie zgadzają się z tabelą `[W10]`. -/

/-! ### 3a.  Baza `[W11]` -/

/-- Baza indukcji `[W11.3]`: `ℓ(6,5) = 7`. -/
theorem ell_6_5 : ell 6 5 = 7 := e_6_5

/-! ### 3b.  Węzły PRAWDZIWE ze zepsutym krokiem — tabela `[W10]`

| węzeł | `ℓ(a,b)` | `ℓ(a,b+1)` |  wszystkie mają przyrost `+1` |
-/

theorem ell_10_6  : ell 10 6  = 7  := e_10_6
theorem ell_10_7  : ell 10 7  = 8  := e_10_7
theorem ell_11_7  : ell 11 7  = 8  := e_11_7
theorem ell_11_8  : ell 11 8  = 9  := e_11_8
theorem ell_13_8  : ell 13 8  = 8  := e_13_8
theorem ell_13_9  : ell 13 9  = 9  := e_13_9
theorem ell_14_9  : ell 14 9  = 9  := e_14_9
theorem ell_14_10 : ell 14 10 = 10 := e_14_10
theorem ell_15_9  : ell 15 9  = 8  := e_15_9
theorem ell_15_10 : ell 15 10 = 9  := e_15_10
theorem ell_16_10 : ell 16 10 = 8  := e_16_10
theorem ell_16_11 : ell 16 11 = 9  := e_16_11
theorem ell_20_12 : ell 20 12 = 9  := e_20_12
theorem ell_20_13 : ell 20 13 = 10 := e_20_13

/-- Cała tabela `[W10]` w jednym zdaniu: w każdym z siedmiu węzłów krok `A`
    ZWIĘKSZA `ℓ` dokładnie o 1 (przyrost ✓ z kolumny czwartej). -/
theorem W10_przyrost :
    ell 10 7  = ell 10 6  + 1 ∧
    ell 11 8  = ell 11 7  + 1 ∧
    ell 13 9  = ell 13 8  + 1 ∧
    ell 14 10 = ell 14 9  + 1 ∧
    ell 15 10 = ell 15 9  + 1 ∧
    ell 16 11 = ell 16 10 + 1 ∧
    ell 20 13 = ell 20 12 + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ell_10_6, ell_10_7, ell_11_7, ell_11_8, ell_13_8, ell_13_9,
               ell_14_9, ell_14_10, ell_15_9, ell_15_10, ell_16_10, ell_16_11,
               ell_20_12, ell_20_13]

/-! ### 3c.  Pięć wyjątków `P` — pary „przed i po kroku `A`"

`[W10]` mówi: `ℓ = 4,5,6,7,7` BEZ przyrostu, czyli `ℓ(a,b) = ℓ(a,b+1)`.
SPRAWDZONE, nie założone — obie kolumny są tu policzone osobno. -/

theorem ell_2_1 : ell 2 1 = 4 := e_2_1
theorem ell_2_2 : ell 2 2 = 4 := e_2_2
theorem ell_3_2 : ell 3 2 = 5 := e_3_2
theorem ell_3_3 : ell 3 3 = 5 := e_3_3
theorem ell_4_3 : ell 4 3 = 6 := e_4_3
theorem ell_4_4 : ell 4 4 = 6 := e_4_4
theorem ell_5_4 : ell 5 4 = 7 := e_5_4
theorem ell_5_5 : ell 5 5 = 7 := e_5_5
theorem ell_7_4 : ell 7 4 = 7 := e_7_4
theorem ell_7_5 : ell 7 5 = 7 := e_7_5

/-- **Wyjątki `P` NIE MAJĄ przyrostu** — potwierdzenie zdania z `[W10]`,
    a zarazem powód, dla którego `[W11.3]` musi startować od `k = 6`. -/
theorem W10_wyjatki_P_bez_przyrostu :
    ell 2 2 = ell 2 1 ∧ ell 3 3 = ell 3 2 ∧ ell 4 4 = ell 4 3 ∧
    ell 5 5 = ell 5 4 ∧ ell 7 5 = ell 7 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ell_2_1, ell_2_2, ell_3_2, ell_3_3, ell_4_3, ell_4_4,
               ell_5_4, ell_5_5, ell_7_4, ell_7_5]

/-- **Próg `k ≥ 6` w `[W11.3]` jest CIASNY**: dla `k = 2,3,4,5` mamy
    `ℓ(k,k−1) = k+2 > k+1`.  To są wyjątki `[W11.4]`, korzeń kaskady `[W10]`. -/
theorem ell_diag_prog_ciasny :
    ell 2 1 = 2 + 2 ∧ ell 3 2 = 3 + 2 ∧ ell 4 3 = 4 + 2 ∧ ell 5 4 = 5 + 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [ell_2_1, ell_3_2, ell_4_3, ell_5_4]

/-! ## 4.  RODZINY ZE WZOREM — dwa brzegi, zamiast nieskończenie wielu węzłów

Zweryfikowane własnym BFS przed dowodzeniem: `ℓ(a,1) = a+2` — 0 naruszeń dla
`a = 2…300`; `ℓ(2,m) = m+2` — 0 naruszeń dla `m = 2…300`; okna `a+b ≤ 200/400/800`
dają identyczne wartości. -/

/-- `ℓ(1,m) = m+2` dla KAŻDEGO `m` (także `m = 0`: `ℓ(1,0) = 2`).
    Dla `m ≥ 2` B-rodzica nie ma, więc każdy krok `A` dokłada 1. -/
theorem ell_1m (m : Nat) : ell 1 m = m + 2 := by
  induction m with
  | zero => exact ell_a0 1 (by omega)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      show ell 1 1 = 3
      exact e_1_1
    · have hs := ell_one3 1 (n+1) n rfl (by omega)
      omega

/-- **`ℓ(a,1) = a+2` dla `a ≥ 2`.**  B-rodzic węzła `(a,1)` to `(1,a−1)`,
    a oba ramiona minimum są równe `a+1`. -/
theorem ell_a1 (a : Nat) (ha : 2 ≤ a) : ell a 1 = a + 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = 1 + c := ⟨a-1, by omega⟩
  have h := ell_two3 (1+c) 1 0 c rfl rfl
  rw [ell_a0 (1+c) (by omega), ell_1m c] at h
  omega

private theorem ell_2m_aux : ∀ n b, b = n+2 → ell 2 b = n+4 := by
  intro n
  induction n with
  | zero =>
    intro b hb
    subst hb
    show ell 2 2 = 4
    exact e_2_2
  | succ k ih =>
    intro b hb
    have h := ih (k+2) rfl
    have hs := ell_one3 2 ((k+2)+1) (k+2) rfl (by omega)
    have hbe : b = (k+2)+1 := by omega
    subst hbe
    omega

/-- **`ℓ(2,m) = m+2` dla `m ≥ 2`.**  Dla `m > 2` B-rodzica nie ma (`m > a = 2`),
    więc `ℓ` rośnie o 1 na krok; baza `ℓ(2,2) = 4`. -/
theorem ell_2m (m : Nat) (hm : 2 ≤ m) : ell 2 m = m + 2 := by
  have h := ell_2m_aux (m-2) m (by omega)
  omega

/-! ## 5.  ŁATKI `P` i `Q` — jedenaście wartości `ℓ` (runda 2, zlecenie `kopacz`)

Wszystkie jedenaście sprawdzone MOIM BFS niezależnie od jego DP, na trzech
oknach (`a+b ≤ 200/400/800` — wartości identyczne): **zero rozbieżności**.
Żadna nie wymagała rozszerzenia drabiny z §1 — całe domknięcie już tam było. -/

/-- Łatki `P` — prawe strony. -/
theorem ell_7_3  : ell 7 3  = 7 := e_7_3
theorem ell_9_4  : ell 9 4  = 8 := e_9_4
theorem ell_10_5 : ell 10 5 = 8 := e_10_5
theorem ell_11_5 : ell 11 5 = 9 := e_11_5
theorem ell_13_7 : ell 13 7 = 9 := e_13_7

/-- Łatki `Q` — obie strony. -/
theorem ell_6_3  : ell 6 3  = 6 := e_6_3
theorem ell_4_2  : ell 4 2  = 5 := e_4_2
theorem ell_8_4  : ell 8 4  = 7 := e_8_4
theorem ell_5_3  : ell 5 3  = 6 := e_5_3
theorem ell_6_4  : ell 6 4  = 6 := e_6_4
theorem ell_12_7 : ell 12 7 = 8 := e_12_7

/-! ### 5a.  KONTROLA KRZYŻOWA — rodziny ze §4 vs drabina z §1

Gdyby `ell_a1` / `ell_2m` miały złą stałą albo sprzeczne hipotezy (twierdzenie
prawdziwe o niczym), te trzy zdania by nie przeszły: każde konfrontuje WZÓR
z wartością policzoną niezależnie w drabinie. -/

/-- `ℓ(2,1) = 4` — droga ①: DRABINA z §1 (rozwinięcie rekurencji). -/
private theorem kontrola_2_1_drabina : ell 2 1 = 2 + 2 := e_2_1
/-- `ℓ(2,1) = 4` — droga ②: WZÓR `ell_a1` z §4.  Gdyby wzór miał złą stałą,
    to zdanie by nie przeszło, mimo że droga ① przechodzi. -/
private theorem kontrola_2_1_wzor : ell 2 1 = 2 + 2 := ell_a1 2 (by omega)

/-- `ℓ(2,2) = 4` — droga ①: DRABINA. -/
private theorem kontrola_2_2_drabina : ell 2 2 = 2 + 2 := e_2_2
/-- `ℓ(2,2) = 4` — droga ②: WZÓR `ell_2m`. -/
private theorem kontrola_2_2_wzor : ell 2 2 = 2 + 2 := ell_2m 2 (by omega)

/-- `ℓ(4,1) = 6` — droga ①: DRABINA. -/
private theorem kontrola_4_1_drabina : ell 4 1 = 4 + 2 := e_4_1
/-- `ℓ(4,1) = 6` — droga ②: WZÓR `ell_a1`. -/
private theorem kontrola_4_1_wzor : ell 4 1 = 4 + 2 := ell_a1 4 (by omega)

/-- Obie rodziny są NIEPUSTE i niesprzeczne z drabiną — zebrane w jedno zdanie. -/
theorem rodziny_zgodne_z_drabina :
    ell 2 1 = 4 ∧ ell 2 2 = 4 ∧ ell 4 1 = 6 ∧ ell 4 2 = 5 :=
  ⟨kontrola_2_1_wzor, kontrola_2_2_wzor, kontrola_4_1_wzor, e_4_2⟩

end A252864.ALemat
