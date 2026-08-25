/-
  A252864 — `_DYN_Drzewo.lean`.  DRZEWO A-PREFERUJĄCE ([D9], `MOST.md:30-31`).
  Lean 4.34.0-rc2, BEZ Mathlib.

  PO CO TEN PLIK ISTNIEJE
  Dowód `thm:dynamics` (`MOST.md:400-402`) zaczyna się od zdania:
    „każdy węzeł ≠(0,0) ma DOKŁADNIE JEDNEGO rodzica-drzewowego i leży on
     na poziomie n−1"
  i całe [R3] jest rozbiorem względem tego rodzica.  **W repo Leanowym pojęcia
  drzewa A-preferującego NIE MA NIGDZIE** (grep 24.08: `Sequence`, `Bfs`, `Tree`,
  `ALemat*`, `MostL` — zero trafień; jedyne „B-rodzic" to człon rekurencji Bellmana,
  nie wybór rodzica).  `Seq.parentInR` liczy KANDYDATÓW na rodzica, a nie rodzica
  drzewowego — i sam `Sequence.lean:970-978` odnotowuje, że obie definicje DAJĄ
  RÓŻNE LICZBY (`inflow 9 = 6` wobec 7 po rodzicu rzeczywistym).

  Ten plik dokłada brakującą cegłę, BEZ A-LEMATU:
    · `tparent`      — rodzic-drzewowy, definicja obliczalna
    · `tparent_lvl`  — leży DOKŁADNIE poziom niżej           (`MOST.md:401-402`)
    · `tparent_le`   — zostaje w dziedzinie `j ≤ k`
    · `tparent_is_A_or_B` — jest A-rodzicem albo B-rodzicem, trzeciej opcji nie ma
    · `tchild_iff_A` — A-dziecko jest dzieckiem drzewowym ⟺ `ℓ(A p) = ℓ(p)+1`
                       (to jest DOKŁADNIE część „A-dziecko" dowodu `thm:children`,
                        `MOST.md:366-369` — bez A-LEMATU, bo A-LEMAT wchodzi
                        dopiero przy PRZEŁOŻENIU tego warunku na klasy `I₃∪I₄∪I₅`)

  ⛔ ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.
-/
import _DYN_Kolumny

namespace A252864.DYN

open A252864.ALemat

/-! ## 1.  Rodzic-drzewowy

`MOST.md:30-31` ([D9]): rodzicem `p=(a,b) ≠ (0,0)` jest A-rodzic `(a,b−1)`,
gdy `b ≥ 1` i `ℓ(a,b−1) = ℓ(p)−1`; w przeciwnym razie B-rodzic `(b, a−b)`.

W `(j,k)`: A-rodzic `(j,k)` to `(j, k−1)` (istnieje ⟺ `j < k`),
B-rodzic to `(k−j, j)` (istnieje ⟺ `k ≤ 2j`). -/

def tparent (j k : Nat) : Nat × Nat :=
  if j < k ∧ L j (k - 1) + 1 = L j k then (j, k - 1) else (k - j, j)

/-- Rodzic-drzewowy jest A-rodzicem albo B-rodzicem — trzeciej możliwości nie ma. -/
theorem tparent_is_A_or_B (j k : Nat) :
    tparent j k = (j, k - 1) ∨ tparent j k = (k - j, j) := by
  unfold tparent
  by_cases h : j < k ∧ L j (k - 1) + 1 = L j k
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [h])

/-- **`MOST.md:401-402`** — rodzic-drzewowy leży DOKŁADNIE poziom niżej.
    Bez A-LEMATU: cała treść siedzi w rekurencji dwóch rodziców [B1]. -/
theorem tparent_lvl (j k : Nat) (hjk : j ≤ k) (hne : ¬ (j = 0 ∧ k = 0)) :
    L (tparent j k).1 (tparent j k).2 + 1 = L j k := by
  unfold tparent
  by_cases hA : j < k ∧ L j (k - 1) + 1 = L j k
  · simp only [hA, if_pos]
    exact hA.2
  · -- A-rodzic NIE jest geodezyjny ⇒ musi nim być B-rodzic
    simp only [hA, if_neg, not_false_iff]
    cases j with
    | zero =>
      -- `L 0 k = k`, a `L 0 (k−1) + 1 = k` dla `k ≥ 1` — więc gałąź A zawsze łapie;
      -- pozostaje wyłącznie `k = 0`, wykluczone przez `hne`.
      exfalso
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact hne ⟨rfl, rfl⟩
      · exact hA ⟨hk, by rw [row_zero, row_zero]; omega⟩
    | succ i =>
      by_cases h1 : k ≤ i + 1
      · -- `k = i+1` (bo `i+1 ≤ k`): B-rodzic to `(0, i+1)`, poziom `i+1`
        have hk : k = i + 1 := Nat.le_antisymm h1 hjk
        subst hk
        have e0 : i + 1 - (i + 1) = 0 := by omega
        rw [e0, row_zero, L]
        simp
      · by_cases h2 : k ≤ 2 * (i + 1)
        · have hs := L_step_two i k (by omega) h2
          -- minimum musi być osiągnięte na B-rodzicu, bo A-rodzic odpadł
          have hmin := Nat.min_le_left (L (i + 1) (k - 1)) (L (k - (i + 1)) (i + 1))
          have hmin2 := Nat.min_le_right (L (i + 1) (k - 1)) (L (k - (i + 1)) (i + 1))
          have hnotA : L (i + 1) (k - 1) + 1 ≠ L (i + 1) k := by
            intro hc; exact hA ⟨by omega, hc⟩
          omega
        · -- brak B-rodzica ⇒ gałąź A jest wymuszona ⇒ `hA` nie mogło zawieść
          exfalso
          have hs := L_step_no_B i k (by omega)
          exact hA ⟨by omega, by omega⟩

/-- Rodzic-drzewowy zostaje w dziedzinie drzewa (`j ≤ k`). -/
theorem tparent_le (j k : Nat) (hjk : j ≤ k) (hne : ¬ (j = 0 ∧ k = 0)) :
    (tparent j k).1 ≤ (tparent j k).2 := by
  by_cases hA : j < k ∧ L j (k - 1) + 1 = L j k
  · simp only [tparent, if_pos hA]
    -- A-rodzic `(j, k−1)`: trzeba `j ≤ k−1`, czyli `j < k` — to jest `hA.1`
    show j ≤ k - 1
    have := hA.1
    omega
  · simp only [tparent, if_neg hA]
    -- B-rodzic `(k−j, j)`: trzeba `k − j ≤ j`, czyli `k ≤ 2j`.
    -- Gdy `k > 2j`, B-rodzica nie ma — ale wtedy gałąź A jest wymuszona (`L_step_no_B`),
    -- więc `hA` nie mogło zawieść.
    show k - j ≤ j
    rcases Nat.lt_or_ge (2 * j) k with hk2 | hk2
    · exfalso
      cases j with
      | zero =>
        exact hA ⟨by omega, by rw [row_zero, row_zero]; omega⟩
      | succ i =>
        have hs := L_step_no_B i k (by omega)
        exact hA ⟨by omega, by omega⟩
    · omega

/-! ## 2.  Część „A-dziecko" dowodu `thm:children` (`MOST.md:366-369`)

> `A(p)=(a,b+1)` jest dzieckiem drzewowym `p` ⟺ `ℓ(a,b+1)=ℓ(a,b)+1`.

To jest połowa `thm:children`, która **NIE stoi na A-LEMACIE** — A-LEMAT wchodzi
dopiero w następnym zdaniu, przy przełożeniu warunku `ℓ(a,b+1)=ℓ(a,b)+1` na
przynależność `p ∈ I₃∪I₄∪I₅`. -/

/-- Węzeł `q` jest dzieckiem drzewowym `p`, gdy `p` jest jego rodzicem-drzewowym. -/
def IsTChild (p q : Nat × Nat) : Prop := tparent q.1 q.2 = p

/-- **`MOST.md:366-369`, kierunki (⟸) i (⟹) razem.**
    A-dziecko `(j,k+1)` jest dzieckiem drzewowym `(j,k)` ⟺ `ℓ` rośnie o 1. -/
theorem tchild_iff_A (j k : Nat) (hjk : j ≤ k) :
    IsTChild (j, k) (j, k + 1) ↔ L j (k + 1) = L j k + 1 := by
  have hk1 : k + 1 - 1 = k := by omega
  simp only [IsTChild, tparent, hk1]
  constructor
  · intro h
    by_cases hA : j < k + 1 ∧ L j k + 1 = L j (k + 1)
    · omega
    · -- gałąź „else": rodzicem byłby B-rodzic `(k+1−j, j)`; ale wtedy `(k+1−j, j) = (j,k)`
      -- wymusza `j = k` i `k + 1 − j = j`, czyli `k + 1 = 2j = 2k` ⇒ `k = 1`, `j = 1`.
      -- Sprawdzenie wprost: `L 1 2 = 3`, `L 1 1 = 2` — więc gałąź A JEDNAK działa.
      rw [if_neg hA] at h
      have h1 : k + 1 - j = j := congrArg Prod.fst h
      have h2 : j = k := congrArg Prod.snd h
      subst h2
      have hj : j = 1 := by omega
      subst hj
      exact absurd ⟨by omega, by simp [L]⟩ hA
  · intro h
    rw [if_pos ⟨by omega, by omega⟩]

end A252864.DYN
