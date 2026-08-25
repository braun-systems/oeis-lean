/-
  A252864 — ALematProgi.lean.  SIEDEM LEMATÓW ARYTMETYCZNYCH: progi w Z[φ] → czysty `Nat`.
  Lean 4.34.0-rc2, BEZ Mathlib, BEZ `sorry`, BEZ `decide`, BEZ `native_decide`.

  Jedyna rzecz spoza czystej liniowej arytmetyki, jakiej używam, to `no_sqrt5`
  z `ALemat.lean` (niewymierność √5 w postaci `c*c = 5*(d*d) → d = 0`).
  Wszystko inne to: tożsamość kwadratowa + `omega` po atomach-iloczynach.

  DWIE TOŻSAMOŚCI, NA KTÓRYCH STOI CAŁY PLIK (obie sprawdzone `grind`-em niżej):
    (3b+s+4)² + (b+2s+3)² = 5(b+s+2)² + 5(b+1)²      -- dla `hi_iff_I1`
    (3d+s+4)² + (d+2s+3)² = 5(d+s+2)² + 5(d+1)²      -- dla `not_hi_B_branch`
  To jest ta sama tożsamość `N(z) + N(z′) = ...` w dwóch podstawieniach.
-/
import ALematRep

namespace A252864.ALemat

/-!
  CO ZMIERZYŁEM, A CZEGO NIE (uczciwie, `[N=400]` = kwadrat `(a,b) < 400²`):
  · kontrola dodatnia — żadne zdanie nie jest puste: `Hi` prawdziwe 110 634×,
    fałszywe 49 366×; `I1` prawdziwe 49 119×.  Przesłanki lematów 2–7 mają
    49 119 / 49 119 / 48 967 / 49 366 / 49 366 świadków.
  · mutacja — 4 celowo BŁĘDNE warianty (próg `2 ≤ a`, `a-b` zamiast `a-b-1`,
    `c-d` zamiast `c-d-1`, odwrócone `c < d`) kompilator ODRZUCIŁ 4/4.
  · CIASNOŚĆ ZAŁOŻEŃ, mierzona przez PRÓBĘ ICH ZDJĘCIA:
      `not_hi_b1  (3 ≤ a)` — CIASNE, `a = 2` daje `49 ≤ 45`, fałsz.
      `hi_iff_I1  (b < a)` — POTRZEBNE, kontrświadek `(a,b) = (0,0)`.
      `I1_not_hi_pred (1 ≤ c)` — ZBĘDNE (`I1 0 d` jest zawsze fałszywe).
      `not_hi_A   (1 ≤ d)`  — ZBĘDNE (w `Nat` `0-1 = 0`, teza = przesłanka).
      `not_hi_B_branch (d < c)` — ZBĘDNE, bo `not_hi_lt` wyprowadza je z `¬Hi c d`.
    ⚠️ Trzech zbędnych NIE USUNĄŁEM — sygnatury były zamówione sztywno.
       Zapisuję je jako fakt, nie jako propozycję zmiany.
-/

/-! ## 0.  Definicje progów -/

/-- `Hi a b` ⟺ `z′(a,b) ≥ φ−2`, gdzie `z′ = aφ′+b`.  (Odczytane z `LEM_A_wstecz.md [W1.2]`.) -/
def Hi (a b : Nat) : Prop := 5*(a+1)^2 < (a+2*b+3)^2

/-- `I1 c d` ⟺ `z′(c,d) < −1` (klasa `I₁`). -/
def I1 (c d : Nat) : Prop := (c+2*d+2)^2 < 5*c^2

/-! ## 1.  `hi_iff_I1` — czysta TOŻSAMOŚĆ, nie ciągi Beatty'ego -/

/-- Przy `b < a`: próg `Hi` na `(a,b)` to dokładnie klasa `I₁` na sprzężeniu `(b+1, a−b−1)`.
    Dowód: podstawienie `a = b+s+1` zabija odejmowanie w `Nat`, a potem jedna
    tożsamość kwadratowa i `omega` po czterech atomach-iloczynach. -/
theorem hi_iff_I1 (a b : Nat) (h : b < a) : Hi a b ↔ I1 (b+1) (a-b-1) := by
  obtain ⟨s, rfl⟩ : ∃ s, a = b + s + 1 := ⟨a - b - 1, by omega⟩
  have e0 : b + s + 1 - b - 1 = s := by omega
  simp only [Hi, I1, e0]
  have e1 : b + s + 1 + 1 = b + s + 2 := by omega
  have e2 : b + s + 1 + 2*b + 3 = 3*b + s + 4 := by omega
  have e3 : b + 1 + 2*s + 2 = b + 2*s + 3 := by omega
  rw [e1, e2, e3]
  simp only [Nat.pow_two]
  have hid : (3*b+s+4)*(3*b+s+4) + (b+2*s+3)*(b+2*s+3)
      = 5*((b+s+2)*(b+s+2)) + 5*((b+1)*(b+1)) := by grind
  omega

/-! ## 2.  `I1_not_hi` — klasa `I₁` wyklucza próg -/

/-- Z `(c+2d+2)² < 5c²` wynika `(c+2d+3)² ≤ 5(c+1)²`.
    Klucz: `u := c+2d+2` spełnia `u < 3c` (bo `u² < 5c² ≤ 9c²`), więc
    `(u+1)² = u²+2u+1 ≤ 5c²+2u < 5c²+6c ≤ 5(c+1)²`. -/
theorem I1_not_hi (c d : Nat) (h : I1 c d) : ¬ Hi c d := by
  simp only [I1] at h
  simp only [Hi, Nat.not_lt]
  simp only [Nat.pow_two] at h ⊢
  have hu : c + 2*d + 2 < 3*c := by
    rcases Nat.lt_or_ge (c + 2*d + 2) (3*c) with hh | hh
    · exact hh
    · exfalso
      have hmm : (3*c)*(3*c) ≤ (c+2*d+2)*(c+2*d+2) := Nat.mul_le_mul hh hh
      have e : (3*c)*(3*c) = 9*(c*c) := by grind
      omega
  have hexp1 : (c+2*d+3)*(c+2*d+3) = (c+2*d+2)*(c+2*d+2) + 2*(c+2*d+2) + 1 := by grind
  have hexp2 : 5*((c+1)*(c+1)) = 5*(c*c) + 10*c + 5 := by grind
  omega

/-! ## 3.  `I1_not_hi_pred` — to samo, przesunięte o jeden -/

/-- `¬Hi (c−1) d` to dosłownie `(c+2d+2)² ≤ 5c²`, czyli osłabienie `I1 c d`. -/
theorem I1_not_hi_pred (c d : Nat) (hc : 1 ≤ c) (h : I1 c d) : ¬ Hi (c-1) d := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have e0 : c' + 1 - 1 = c' := by omega
  simp only [I1] at h
  simp only [Hi, Nat.not_lt, e0]
  have e1 : c' + 1 + 2*d + 2 = c' + 2*d + 3 := by omega
  rw [e1] at h
  simp only [Nat.pow_two] at h ⊢
  omega

/-! ## 4.  `not_hi_A` — krok `A⁻¹` obniża `z′`, więc brak progu się dziedziczy -/

/-- `¬Hi c d` daje `(c+2d+3)² ≤ 5(c+1)²`; a `c+2(d−1)+3 = c+2d+1 ≤ c+2d+3`,
    więc monotoniczność kwadratu załatwia tezę. -/
theorem not_hi_A (c d : Nat) (hd : 1 ≤ d) (h : ¬ Hi c d) : ¬ Hi c (d-1) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have e0 : d' + 1 - 1 = d' := by omega
  simp only [Hi, Nat.not_lt, e0] at h ⊢
  have e1 : c + 2*(d'+1) + 3 = c + 2*d' + 5 := by omega
  rw [e1] at h
  simp only [Nat.pow_two] at h ⊢
  have hm : (c+2*d'+3)*(c+2*d'+3) ≤ (c+2*d'+5)*(c+2*d'+5) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-! ## 5.  `not_hi_b1` — próg `b = 1` jest ciasny od `a = 3` -/

/-- `(a+5)² ≤ 5(a+1)²` dla `a ≥ 3`.  Po podstawieniu `a = t+3` zostaje
    `t²+16t+64 ≤ 5t²+40t+80`, czyli `0 ≤ 4t²+24t+16` — liniowo w atomie `t*t`.
    ⚠️ Próg `3` jest ciasny: dla `a = 2` wychodzi `49 ≤ 45`, czyli FAŁSZ. -/
theorem not_hi_b1 (a : Nat) (ha : 3 ≤ a) : ¬ Hi a 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, a = t + 3 := ⟨a - 3, by omega⟩
  simp only [Hi, Nat.not_lt]
  have e1 : t + 3 + 2*1 + 3 = t + 8 := by omega
  have e2 : t + 3 + 1 = t + 4 := by omega
  rw [e1, e2]
  simp only [Nat.pow_two]
  have h1 : (t+8)*(t+8) = t*t + 16*t + 64 := by grind
  have h2 : 5*((t+4)*(t+4)) = 5*(t*t) + 40*t + 80 := by grind
  omega

/-! ## 6.  `not_hi_lt` — brak progu wymusza `d < c` -/

/-- Gdyby `d ≥ c`, to `c+2d+3 ≥ 3(c+1)`, więc `9(c+1)² ≤ (c+2d+3)² ≤ 5(c+1)²`,
    a `(c+1)² ≥ 1` — sprzeczność. -/
theorem not_hi_lt (c d : Nat) (h : ¬ Hi c d) : d < c := by
  simp only [Hi, Nat.not_lt] at h
  rcases Nat.lt_or_ge d c with hh | hh
  · exact hh
  · exfalso
    have h1 : 3*(c+1) ≤ c + 2*d + 3 := by omega
    have h2 : (3*(c+1))*(3*(c+1)) ≤ (c+2*d+3)*(c+2*d+3) := Nat.mul_le_mul h1 h1
    have e : (3*(c+1))*(3*(c+1)) = 9*((c+1)*(c+1)) := by grind
    have hpos : 0 < (c+1)*(c+1) := Nat.mul_pos (by omega) (by omega)
    simp only [Nat.pow_two] at h
    omega

/-! ## 7.  `not_hi_B_branch` — gałąź `B`, jedyne miejsce, gdzie potrzebna jest niewymierność √5

Sens: `z = φu`, `u = (d, c−d)`, `z′ = φ′u′`, a `φ′ < 0`, więc `z′ < φ−2`
przechodzi na `u′ > φ⁻¹`, czyli `(u−1)′ > φ−2`, czyli `Hi d (c−d−1)`.

W `Nat` po podstawieniu `c = d+s+1`:
  przesłanka `(3d+s+4)² ≤ 5(d+s+2)²`,  teza `5(d+1)² < (d+2s+3)²`,
a tożsamość `(3d+s+4)² + (d+2s+3)² = 5(d+s+2)² + 5(d+1)²` zamienia jedno w drugie
— ALE tylko przy nierówności OSTREJ.  Przesłanka daje `≤`.
🔴 Równość `(3d+s+4)² = 5(d+s+2)²` jest wykluczona WYŁĄCZNIE przez `no_sqrt5`
(`d+s+2 ≥ 2 ≠ 0`).  Bez niewymierności √5 ten lemat NIE PRZECHODZI.

⚠️ To zdanie było najpierw ASERCJĄ, potem POMIAREM — świadek: ta sama treść
z wyciętym `hne` daje `error: omega could not prove the goal` (kontrprzykład
`omega` ma dokładnie kształt równości).  `no_sqrt5` NIE pojawia się w
`#print axioms`, bo jest TWIERDZENIEM, nie aksjomatem — audyt aksjomatów
nie jest testem na tę zależność i nie wolno go za taki brać. -/
theorem not_hi_B_branch (c d : Nat) (h1 : d < c) (h : ¬ Hi c d) : Hi d (c-d-1) := by
  obtain ⟨s, rfl⟩ : ∃ s, c = d + s + 1 := ⟨c - d - 1, by omega⟩
  have e0 : d + s + 1 - d - 1 = s := by omega
  simp only [Hi, Nat.not_lt, e0] at h ⊢
  have e1 : d + s + 1 + 2*d + 3 = 3*d + s + 4 := by omega
  have e2 : d + s + 1 + 1 = d + s + 2 := by omega
  rw [e1, e2] at h
  simp only [Nat.pow_two] at h ⊢
  have hid : (3*d+s+4)*(3*d+s+4) + (d+2*s+3)*(d+2*s+3)
      = 5*((d+s+2)*(d+s+2)) + 5*((d+1)*(d+1)) := by grind
  have hne : (3*d+s+4)*(3*d+s+4) ≠ 5*((d+s+2)*(d+s+2)) := by
    intro hEq
    have := no_sqrt5 _ _ hEq
    omega
  omega

end A252864.ALemat
