/-
  A252864 — `_DYN2_Naplyw.lean`.  `[M6]` / `[R3.1]` — ZBIÓR NAPŁYWU TO DOKŁADNIE 7 WĘZŁÓW.
  Lean 4, BEZ Mathlib.
  ⛔ ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.

  WSPÓŁRZĘDNE.  Węzeł zapisujemy jako parę `(j,k)`; `(a,b)` to `(j, k−j)`, czyli `(j,k) = (a, a+b)`.
  Region `R := {a ≥ 8 ∧ b ≥ 1}` = `{p : 8 ≤ p.1 ∧ p.1 < p.2}`.
  A-rodzic `(a,b) ↦ (a, b−1)`  ·  B-rodzic `(a,b) ↦ (b, a−b)`.
-/
import «_DYN2_R2»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat A252864.MostL A252864.DYN

/-! ## 0.  Rodzic-drzewowy węzła `(a, a+b)` — rozwinięcie `if` w koordynatach `(a,b)` -/

/-- `tparent` w koordynatach `(a,b)`: A-rodzic to `(a, a+b−1)`, B-rodzic to `(b, a)`. -/
theorem tparent_ab (a b : Nat) :
    tparent a (a + b)
      = if a < a + b ∧ L a (a + b - 1) + 1 = L a (a + b) then (a, a + b - 1) else (b, a) := by
  have e : a + b - a = b := by omega
  simp only [tparent, e]

/-! ## 1.  Węzły, dla których lemat wierszowy `kappa_row` NIE ma przesłanki `2b ≤ a`

`kappa_row` wymaga `2*d ≤ c`.  Dla `a ≥ 8`, `1 ≤ b ≤ 7` przesłanka zawodzi tylko na
DWUNASTU węzłach — i wszystkie leżą na poziomie `< 10`, więc `hn : 10 ≤ n` je wycina.
(Zmierzone w Pythonie przed dowodem: `L 8 13 = 7 … L 13 20 = 9`, maksimum 9.) -/

theorem male_wezly (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) (hb7 : b ≤ 7) (hlt : a < 2 * b) :
    L a (a + b) < 10 := by
  have hcase :
      (a = 8 ∧ b = 5) ∨ (a = 9 ∧ b = 5) ∨ (a = 8 ∧ b = 6) ∨ (a = 9 ∧ b = 6)
      ∨ (a = 10 ∧ b = 6) ∨ (a = 11 ∧ b = 6) ∨ (a = 8 ∧ b = 7) ∨ (a = 9 ∧ b = 7)
      ∨ (a = 10 ∧ b = 7) ∨ (a = 11 ∧ b = 7) ∨ (a = 12 ∧ b = 7) ∨ (a = 13 ∧ b = 7) := by
    omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [L]

/-! ## 2.  `kap` maleje o 1 na `d = 1..7`

`kap = 5,6,5,4,3,2,1,0` (to `κ+4`, `MOST.md:100`).  Od `d = 1` w górę jest ŚCIŚLE MALEJĄCA —
i to jest cały powód, dla którego A-rodzic nie jest rodzicem-drzewowym przy `2 ≤ b ≤ 7`:
warunek A żąda WZROSTU `ℓ` o 1, a wiersz maleje. -/

theorem kap_dec (c : Nat) (hc : 1 ≤ c) (h7 : c ≤ 6) : kap (c + 1) + 1 = kap c := by
  have h : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [kap]

/-! ## 3.  Poziom WYZNACZA `a` — lemat wierszowy [M5.1] zamiast lematu kolumnowego [M2.2]

⚠️ Tu jest odejście od planu.  Plan przewidywał `col_one` na B-rodzicu (kolumna `b`, poziom `n−1`).
To NIE PRZECHODZI dla `b = 7`, `n = 10`: `col_one` żąda `prog 7 = 10 ≤ n−1 = 9` — fałsz —
i wniosek też byłby fałszywy, bo `L 7 8 = 9` ORAZ `L 7 14 = 9` (dwa węzły, nie jeden).
Zamiast tego `kappa_row` daje `a` wprost z `(n,b)`, jednym rachunkiem dla wszystkich `b = 1..7`. -/

/-- Dla `a ≥ 8`, `1 ≤ b ≤ 7` na poziomie `n ≥ 10`: przesłanka `2b ≤ a` jest DARMOWA,
    a poziom spełnia `n + 4 = a + kap b`. -/
theorem kappa_ab (n a b : Nat) (hn : 10 ≤ n) (ha : 8 ≤ a) (hb : 1 ≤ b) (hb7 : b ≤ 7)
    (hL : L a (a + b) = n) : 2 * b ≤ a ∧ n + 4 = a + kap b := by
  have h2b : 2 * b ≤ a := by
    rcases Nat.lt_or_ge a (2 * b) with hlt | hge
    · have hm := male_wezly a b ha hb hb7 hlt
      omega
    · exact hge
  refine ⟨h2b, ?_⟩
  have h := kappa_row b hb7 a (by omega) h2b
  omega

/-- **Prawa strona tezy jest WYMUSZONA przez `b ≤ 7`** — `a` nie ma swobody. -/
theorem a_wyznaczone (n a b : Nat) (hn : 10 ≤ n) (ha : 8 ≤ a) (hb : 1 ≤ b) (hb7 : b ≤ 7)
    (hL : L a (a + b) = n) :
    (b = 1 ∧ a = n - 2) ∨ (2 ≤ b ∧ b ≤ 7 ∧ a = n + b - 3) := by
  have h := (kappa_ab n a b hn ha hb hb7 hL).2
  have hc : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp [kap] at h; omega)

/-- **Przy `2 ≤ b ≤ 7` A-rodzic NIE jest rodzicem-drzewowym.**  Wiersz maleje, warunek A żąda wzrostu. -/
theorem A_nie_dziala (a b : Nat) (ha : 8 ≤ a) (hb2 : 2 ≤ b) (hb7 : b ≤ 7) (h2b : 2 * b ≤ a) :
    ¬ (L a (a + b - 1) + 1 = L a (a + b)) := by
  have h1 := kappa_row b hb7 a (by omega) h2b
  have h2 := kappa_row (b - 1) (by omega) a (by omega) (by omega)
  have e : a + (b - 1) = a + b - 1 := by omega
  rw [e] at h2
  have h3 := kap_dec (b - 1) (by omega) (by omega)
  have e2 : b - 1 + 1 = b := by omega
  rw [e2] at h3
  omega

/-! ## 4.  Na przekątnej `a = b` rodzicem-drzewowym JEST A-rodzic

To jest jedyne miejsce, w którym potrzebny jest A-LEMAT (przez `R2_A`).  Bez tego węzeł
`(a,a)` z `a ≥ 8` miałby B-rodzica `(a, 0)` — czyli w `(j,k)` parę `(a,a)`, która NIE leży
w `R` (brak `p.1 < p.2`) — i punkt (1) rozbioru by padł. -/

theorem A_dziala_na_przekatnej (a : Nat) (ha : 8 ≤ a) :
    L a (a + a - 1) + 1 = L a (a + a) := by
  have hR := R2_A a (a - 1) ha (by omega)
  have e1 : a + (a - 1) = a + a - 1 := by omega
  rw [e1] at hR
  have e2 : a + a - 1 + 1 = a + a := by omega
  rw [e2] at hR
  have e3 : a + 2 * (a - 1) + 3 = 3 * a + 1 := by omega
  rw [e3] at hR
  have hsq : (3 * a + 1) ^ 2 > 5 * (a + 1) ^ 2 := by
    rw [KW.sqp, KW.sqp]
    have h8 : 8 * a ≤ a * a := Nat.mul_le_mul_right a ha
    have ea : (3 * a + 1) * (3 * a + 1) = 9 * (a * a) + 6 * a + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      rw [KW.c33 a]
      omega
    have eb : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    rw [ea, eb]
    omega
  have ht := tchild_iff_A a (a + a - 1) (by omega)
  rw [e2] at ht
  exact (ht.mp (hR.mpr hsq)).symm

/-! ## 5.  Rodzic-drzewowy: rozstrzygnięcie gałęzi -/

/-- Gdy warunek A zawodzi, rodzicem-drzewowym jest B-rodzic `(b, a)`. -/
theorem tparent_B (a b : Nat) (hcond : ¬ (L a (a + b - 1) + 1 = L a (a + b))) :
    tparent a (a + b) = (b, a) := by
  rw [tparent_ab, if_neg]
  intro h
  exact hcond h.2

/-- Gdy warunek A działa (i `b ≥ 1`), rodzicem-drzewowym jest A-rodzic `(a, a+b−1)`. -/
theorem tparent_A (a b : Nat) (hb : 1 ≤ b) (hcond : L a (a + b - 1) + 1 = L a (a + b)) :
    tparent a (a + b) = (a, a + b - 1) := by
  rw [tparent_ab, if_pos ⟨by omega, hcond⟩]

/-! ## 6.  `[M6]` / `[R3.1]` — TEZA GŁÓWNA -/

/-- Rodzic-drzewowy węzła `(a,b)` leży w regionie `R = {8 ≤ p.1 ∧ p.1 < p.2}`. -/
def wRodzic (a b : Nat) : Prop :=
  8 ≤ (tparent a (a + b)).1 ∧ (tparent a (a + b)).1 < (tparent a (a + b)).2

/-- **`b ≤ 7` ⇒ NAPŁYW.**  Przy `b = 1` oba możliwe rodziców wypadają z `R`
    (A-rodzic ma `p.1 = p.2`, B-rodzic ma `p.1 = 1 < 8`); przy `2 ≤ b ≤ 7`
    warunek A zawodzi (wiersz maleje), więc rodzicem jest B-rodzic `(b,a)` z `b ≤ 7 < 8`. -/
theorem naplyw_maleB (n a b : Nat) (hn : 10 ≤ n) (ha : 8 ≤ a) (hb : 1 ≤ b) (hb7 : b ≤ 7)
    (hL : L a (a + b) = n) : ¬ wRodzic a b := by
  have h2b := (kappa_ab n a b hn ha hb hb7 hL).1
  intro hw
  simp only [wRodzic] at hw
  rcases Nat.lt_or_ge 1 b with hb2 | hb1
  · -- `2 ≤ b ≤ 7`: B-rodzic `(b, a)`, a `8 ≤ b` jest fałszem
    rw [tparent_B a b (A_nie_dziala a b ha (by omega) hb7 h2b)] at hw
    omega
  · -- `b = 1`
    have hbe : b = 1 := by omega
    subst hbe
    by_cases hcond : L a (a + 1 - 1) + 1 = L a (a + 1)
    · rw [tparent_A a 1 (by omega) hcond] at hw
      -- A-rodzic to `(a, a+1−1) = (a, a)`: brak `p.1 < p.2`
      omega
    · rw [tparent_B a 1 hcond] at hw
      -- B-rodzic to `(1, a)`: brak `8 ≤ p.1`
      omega

/-- **`b ≥ 8` ⇒ BRAK NAPŁYWU.**  A-rodzic `(a, a+b−1)` zawsze leży w `R`; B-rodzic `(b,a)`
    też, bo `b ≥ 8` i `b < a` — a `b = a` jest wykluczone przez `A_dziala_na_przekatnej`. -/
theorem duze_b_ma_rodzica (a b : Nat) (ha : 8 ≤ a) (hb8 : 8 ≤ b) : wRodzic a b := by
  simp only [wRodzic]
  by_cases hcond : L a (a + b - 1) + 1 = L a (a + b)
  · rw [tparent_A a b (by omega) hcond]
    exact ⟨by omega, by omega⟩
  · rw [tparent_B a b hcond]
    refine ⟨by omega, ?_⟩
    -- `b ≤ a` z `tparent_le`; `b = a` przeczy `A_dziala_na_przekatnej`
    have hle := tparent_le a (a + b) (by omega) (by omega)
    rw [tparent_B a b hcond] at hle
    have hne : b ≠ a := by
      intro he
      subst he
      exact hcond (A_dziala_na_przekatnej b hb8)
    show b < a
    omega

/-- **[M6] / [R3.1] — ZBIÓR NAPŁYWU TO DOKŁADNIE SIEDEM WĘZŁÓW.**
    Węzeł `(a,b)` regionu `R` z poziomu `n ≥ 10` ma rodzica-drzewowego POZA `R`
    wtedy i tylko wtedy, gdy należy do `W(n) = {(n−2,1)} ∪ {(n+c−3, c) : c = 2..7}`. -/
theorem naplyw_iff (n a b : Nat) (hn : 10 ≤ n) (ha : 8 ≤ a) (hb : 1 ≤ b) (hL : L a (a + b) = n) :
    ¬ wRodzic a b ↔ ((b = 1 ∧ a = n - 2) ∨ (2 ≤ b ∧ b ≤ 7 ∧ a = n + b - 3)) := by
  rcases Nat.lt_or_ge b 8 with hb7 | hb8
  · -- `b ≤ 7`: OBIE strony prawdziwe
    constructor
    · intro _
      exact a_wyznaczone n a b hn ha hb (by omega) hL
    · intro _
      exact naplyw_maleB n a b hn ha hb (by omega) hL
  · -- `b ≥ 8`: OBIE strony fałszywe
    constructor
    · intro hnw
      exact absurd (duze_b_ma_rodzica a b ha hb8) hnw
    · intro hr
      rcases hr with ⟨he, _⟩ | ⟨_, h7, _⟩
      · omega
      · omega

/-! ## 7.  DOMKNIĘCIE W DRUGĄ STRONĘ — siedem węzłów NAPRAWDĘ leży na poziomie `n` i w `R` -/

/-- Głowa `W(n)`: węzeł `(a,b) = (n−2, 1)`, czyli `(j,k) = (n−2, n−1)`. -/
theorem W_head_level (n : Nat) (hn : 10 ≤ n) : L (n - 2) (n - 1) = n := by
  have h := kappa_row 1 (by omega) (n - 2) (by omega) (by omega)
  have e : n - 2 + 1 = n - 1 := by omega
  rw [e] at h
  simp only [kap] at h
  omega

/-- Ogon `W(n)`: węzeł `(a,b) = (n+c−3, c)` dla `c = 2..7`, czyli `(j,k) = (n+c−3, n+2c−3)`. -/
theorem W_tail_level (n c : Nat) (hn : 10 ≤ n) (h2 : 2 ≤ c) (h7 : c ≤ 7) :
    L (n + c - 3) (n + 2 * c - 3) = n := by
  have h := kappa_row c h7 (n + c - 3) (by omega) (by omega)
  have e : n + c - 3 + c = n + 2 * c - 3 := by omega
  rw [e] at h
  have hc : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [kap] at h; omega)

/-- Siedem węzłów `W(n)` leży w regionie `R` (`8 ≤ a`, `b ≥ 1`). -/
theorem W_in_R (n c : Nat) (hn : 10 ≤ n) (h2 : 2 ≤ c) (h7 : c ≤ 7) :
    8 ≤ n - 2 ∧ 8 ≤ n + c - 3 := by
  omega

/-! ## 8.  KONTROLA PRZYRZĄDU — teza NIE jest prawdziwa o niczym

Bez tego `naplyw_iff` mogłoby mieć przesłanki niespełnialne (`hL` + `hn` + `ha`) i być
prawdziwe pusto.  Poniżej jeden świadek DODATNI (napływ istnieje) i jeden UJEMNY
(`¬ wRodzic` NIE zachodzi zawsze — więc lewa strona coś rozróżnia). -/

/-- KONTROLA DODATNIA: węzeł `(a,b) = (8,1)` leży na poziomie `10` i JEST napływem. -/
theorem kontrola_dodatnia : L 8 (8 + 1) = 10 ∧ ¬ wRodzic 8 1 := by
  have hL : L 8 (8 + 1) = 10 := by simp [L]
  exact ⟨hL, naplyw_maleB 10 8 1 (by omega) (by omega) (by omega) (by omega) hL⟩

/-- KONTROLA UJEMNA: węzeł `(a,b) = (8,8)` ma rodzica-drzewowego W `R` — czyli
    `¬ wRodzic` nie jest twierdzeniem trywialnie prawdziwym. -/
theorem kontrola_ujemna : wRodzic 8 8 :=
  duze_b_ma_rodzica 8 8 (by omega) (by omega)

end A252864.DYN2
