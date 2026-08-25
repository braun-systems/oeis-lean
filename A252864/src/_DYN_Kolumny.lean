/-
  A252864 — `_DYN_Kolumny.lean`.  CZTERY KRÓTKIE INDUKCJE Z `MOST.md:63-109`.
  Lean 4.34.0-rc2, BEZ Mathlib.

  CO TU JEST (przepisane z prozy, nie wymyślone od nowa):
    · [W11.1] `MOST.md:41`  — `ℓ(0,b)=b`, `ℓ(a,0)=a+1`          → `row_zero`, `col_b0`
    · [M2.1]  `MOST.md:65`  — LEMAT KOLUMNOWY `ℓ(a,b)=h(a)+(b−a)` dla `b ≥ a`  → `L_col`
    · [M2.2]  `MOST.md:70`  — JEDEN WĘZEŁ NA KOLUMNĘ dla `n ≥ próg(a)`         → `col_one`
    · [M3]    `MOST.md:80`  — WIERSZ `b=0`                                     → `row_unique`
    · [M5.1]  `MOST.md:100` — `ℓ(c,d) = c + κ(d)`                              → `kappa_row`

  ⚠️ UKŁAD WSPÓŁRZĘDNYCH.  `MOST.md` pisze `(a,b)` z `A:(a,b)→(a,b+1)`,
  `B:(a,b)→(a+b,a)`.  Lean (`ALemat.L j k`) używa `(j,k)` z `k = a+b`.
  Słownik:  `ℓ(a,b) = L a (a+b)`.  Zatem:
    `h(a) := ℓ(a,a) = L a (2a)`   ·   `ℓ(a,0) = L a a`   ·   `ℓ(c,d) = L c (c+d)`.

  ⛔ ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.  Wartości skończone `L`
  liczone przez `simp [L]` (równania definicyjne) — kontrola ujemna: `L 8 8 = 99`
  NIE przechodzi przez `simp [L]` (zmierzone, `_DYN_probe2.lean`).
-/
import ALematDef

namespace A252864.DYN

open A252864.ALemat

/-! ## 0.  Tablica [M1] — `h`, `M`, `próg` jako funkcje, nie jako komentarz -/

/-- `h(a) = ℓ(a,a)`, tabela `MOST.md:50-59` (kolumna `h(a)`). -/
def hval : Nat → Nat
  | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 8 | _ => 9

/-- `próg(a) = max(h(a), M(a)+1)`, tabela `MOST.md:50-59` (ostatnia kolumna). -/
def prog : Nat → Nat
  | 0 => 0 | 1 => 3 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 8 | 6 => 9 | _ => 10

/-- Certyfikaty skończone tabeli [M1]: `h(a) = L a (2a)` dla `a = 0..7`.
    (W `MOST.md` to „36 wartości policzonych dwoma silnikami BFS"; tu policzone
    przez jądro Leana z równań definicyjnych `L`.) -/
theorem h_table :
    L 0 0 = 0 ∧ L 1 2 = 3 ∧ L 2 4 = 4 ∧ L 3 6 = 5
    ∧ L 4 8 = 6 ∧ L 5 10 = 7 ∧ L 6 12 = 8 ∧ L 7 14 = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [L]

theorem hval_eq (a : Nat) (ha : a ≤ 7) : L a (2 * a) = hval a := by
  have h : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [hval, L]

/-! ## 1.  [W11.1] — dwa brzegi, wprost z definicji `L` -/

/-- `MOST.md:41` — `ℓ(0,b) = b`. -/
theorem row_zero (k : Nat) : L 0 k = k := by rw [L]

/-- `MOST.md:41` — `ℓ(a,0) = a+1` dla `a ≥ 1`. -/
theorem col_b0 (a : Nat) (ha : 1 ≤ a) : L a a = a + 1 := by
  cases a with
  | zero => omega
  | succ j => rw [L]; simp

/-! ## 2.  [M2.1] LEMAT KOLUMNOWY — `MOST.md:65-67`

> Dla `b ≥ a` węzeł `(a,b+1)` nie ma B-rodzica, więc `ℓ(a,b+1) = ℓ(a,b)+1`;
> indukcja od `b = a`.

W `(j,k)`: „`b ≥ a`" to „`k ≥ 2a`", a „brak B-rodzica" to dokładnie przesłanka
`2*(j+1) < k` lematu `L_step_no_B` (`ALematDef.lean:205`). -/

theorem L_col (a : Nat) : ∀ d : Nat, L a (2 * a + d) = L a (2 * a) + d := by
  intro d
  induction d with
  | zero => simp
  | succ e ih =>
    cases a with
    | zero => simp [row_zero]
    | succ j =>
      have hlt : 2 * (j + 1) < 2 * (j + 1) + (e + 1) := by omega
      have hs := L_step_no_B j (2 * (j + 1) + (e + 1)) hlt
      have he : 2 * (j + 1) + (e + 1) - 1 = 2 * (j + 1) + e := by omega
      rw [he] at hs
      rw [hs, ih]
      omega

/-- Postać z `MOST.md:65` po podstawieniu `h`: `ℓ(a,b) = h(a) + (b−a)` dla `b ≥ a`, `a ≤ 7`. -/
theorem L_col_h (a k : Nat) (ha : a ≤ 7) (hk : 2 * a ≤ k) :
    L a k = hval a + (k - 2 * a) := by
  have e : k = 2 * a + (k - 2 * a) := by omega
  rw [e, L_col a (k - 2 * a), hval_eq a ha]
  omega

/-! ## 3.  [M3] WIERSZ `b = 0` — `MOST.md:80-82` -/

/-- Na poziomie `n` wiersz `b=0` zawiera DOKŁADNIE `(n−1,0)` (dla `n ≥ 2`). -/
theorem row_unique (a n : Nat) (ha : 1 ≤ a) : L a a = n ↔ a + 1 = n := by
  rw [col_b0 a ha]

/-- Część wiersza z `a ≥ 8` (rozłączna z kolumnami `a ≤ 7`) — dokładnie 1 węzeł
    na poziom dla `n ≥ 9`, bo `n−1 ≥ 8 ⟺ n ≥ 9`. -/
theorem row_ge8 (n : Nat) (hn : 9 ≤ n) : 8 ≤ n - 1 ∧ L (n - 1) (n - 1) = n := by
  refine ⟨by omega, ?_⟩
  rw [col_b0 (n - 1) (by omega)]
  omega

/-! ## 4.  [M2.2] JEDEN WĘZEŁ NA KOLUMNĘ — `MOST.md:70-76`

> Dla `b ≥ a` funkcja `b ↦ ℓ(a,b)` jest ściśle rosnąca i przebiega `{h(a), h(a)+1, …}`.
> Dla `b < a` (skończenie wiele) wszystkie `ℓ(a,b) ≤ M(a) < n`.

Druga połowa to 28 wartości skończonych — wypisane, nie założone. -/

/-- Skończona część kolumny (`b < a`, czyli `a ≤ k < 2a`) leży ŚCIŚLE POD progiem. -/
theorem below_prog (a k : Nat) (ha : a ≤ 7) (h1 : a ≤ k) (h2 : k < 2 * a) :
    L a k < prog a := by
  have hA : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
  rcases hA with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · omega
  · have : k = 1 := by omega
    subst this; simp [prog, L]
  · have : k = 2 ∨ k = 3 := by omega
    rcases this with rfl|rfl <;> simp [prog, L]
  · have : k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl|rfl|rfl <;> simp [prog, L]
  · have : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases this with rfl|rfl|rfl|rfl <;> simp [prog, L]
  · have : k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [prog, L]
  · have : k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [prog, L]
  · have : k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [prog, L]

theorem hval_le_prog (a : Nat) (ha : a ≤ 7) : hval a ≤ prog a := by
  have hA : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
  rcases hA with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [hval, prog]

/-- **[M2.2]** Dla `a ≤ 7` i `n ≥ próg(a)` kolumna `a` ma na poziomie `n` DOKŁADNIE
    jeden węzeł, i jest nim `(a, a+n−h(a))` — czyli `k = 2a + n − h(a)`. -/
theorem col_one (a : Nat) (ha : a ≤ 7) (n : Nat) (hn : prog a ≤ n) (k : Nat) (hk : a ≤ k) :
    L a k = n ↔ k = 2 * a + n - hval a := by
  have hhp := hval_le_prog a ha
  rcases Nat.lt_or_ge k (2 * a) with hlt | hge
  · -- część skończona: obie strony fałszywe
    have hb := below_prog a k ha hk hlt
    constructor
    · intro he; omega
    · intro he; omega
  · rw [L_col_h a k ha hge]
    omega

/-! ## 5.  [M5.1] WZORY WIERSZOWE `ℓ(c,d) = c + κ(d)` — `MOST.md:100-107`

`κ = 1, 2, 1, 0, −1, −2, −3, −4` dla `d = 0..7` — WARTOŚCI UJEMNE.  Żeby nie
wychodzić z `Nat`, zapisuję `κ(d) + 4` (czyli `5,6,5,4,3,2,1,0`) i twierdzenie
w postaci `L c (c+d) + 4 = c + kap d`. -/

/-- `κ(d) + 4`. -/
def kap : Nat → Nat
  | 0 => 5 | 1 => 6 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2 | 6 => 1 | _ => 0

/-- Rozwinięcie [B1] w wierszu: `ℓ(c,d) = 1 + min(ℓ(c,d−1), ℓ(d,c−d))`. -/
theorem row_step (c d : Nat) (hd : 1 ≤ d) (hc : 2 * d ≤ c) :
    L c (c + d) = 1 + min (L c (c + d - 1)) (L d c) := by
  have hc1 : 1 ≤ c := by omega
  have hcc : c - 1 + 1 = c := by omega
  have hs := L_step_two (c - 1) (c + d) (by omega) (by omega)
  rw [hcc] at hs
  have he : c + d - c = d := by omega
  rw [he] at hs
  exact hs

/-- **[M5.1]** Dla `d ≤ 7` i `c ≥ max(1, 2d)`: `ℓ(c,d) = c + κ(d)`.
    Indukcja po `d`, dokładnie jak `MOST.md:102-105`. -/
theorem kappa_row : ∀ (d : Nat), d ≤ 7 → ∀ (c : Nat), 1 ≤ c → 2 * d ≤ c →
    L c (c + d) + 4 = c + kap d := by
  intro d
  induction d with
  | zero =>
    intro _ c hc _
    have : c + 0 = c := by omega
    rw [this, col_b0 c hc]
    simp [kap]
  | succ e ih =>
    intro hd7 c hc hcd
    have hstep := row_step c (e + 1) (by omega) hcd
    -- pierwszy człon: hipoteza indukcyjna dla `e`
    have h1 : L c (c + e) + 4 = c + kap e := ih (by omega) c hc (by omega)
    have hcm : c + (e + 1) - 1 = c + e := by omega
    rw [hcm] at hstep
    -- drugi człon: lemat kolumnowy [M2.1] w kolumnie `e+1`
    have h2 : L (e + 1) c = hval (e + 1) + (c - 2 * (e + 1)) :=
      L_col_h (e + 1) c (by omega) hcd
    rw [hstep]
    -- rozstrzygnięcie minimum: oba człony to `c + stała`, więc `omega` (zna `min` na ℕ)
    -- po rozbiciu `e` na 7 przypadków (wartości `hval`, `kap` są wtedy konkretne)
    have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 := by omega
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (simp only [kap, hval] at h1 h2 ⊢; omega)

end A252864.DYN
