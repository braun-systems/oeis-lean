/-
  A252864 — _DYN2_Klasy.lean.   KLASY `I₁..I₅` WE WSPÓŁRZĘDNYCH `(a,b)`:
  zagnieżdżenia progów, siedem inkluzji `[D3]`, brak równości na progu `[D3.1]`.
  Lean 4.34.0-rc2, BEZ Mathlib.

  `klab` = kopia 1:1 `klasaR1` z `Sequence.lean:780-787`, tylko we współrzędnych
  `(a,b)` zamiast `(p.1, p.2 - p.1)`.

  ⚠️ Zakazane w tym pliku: `sorry`, `native_decide`, `axiom`, Mathlib.
-/
import ALematDef

namespace A252864.DYN2

/-! ## 0.  Definicja klasy -/

/-- Kopia `klasaR1` (`Sequence.lean:780-787`) we współrzędnych `(a,b)`. -/
def klab (a b : Nat) : Fin 5 :=
  let x := a + 2 * b
  if (x + 2) * (x + 2) < 5 * (a * a) then 0
  else if (x + 3) * (x + 3) < 5 * ((a+1) * (a+1)) then 1
  else if (x + 1) * (x + 1) < 5 * ((a+1) * (a+1)) then 2
  else if x * x + 1 < 5 * ((a+1) * (a+1)) + 2 * x then 3
  else 4

/-- Ta sama funkcja sparametryzowana bezpośrednio przez `x` (a nie przez `b`).
    Dzięki temu dziecko A (`b ↦ b+1`) i dziecko B (`(a,b) ↦ (a+b, a)`) opisuje
    się tym samym predykatem z inną wartością `x`. -/
def klx (a x : Nat) : Fin 5 :=
  if (x + 2) * (x + 2) < 5 * (a * a) then 0
  else if (x + 3) * (x + 3) < 5 * ((a+1) * (a+1)) then 1
  else if (x + 1) * (x + 1) < 5 * ((a+1) * (a+1)) then 2
  else if x * x + 1 < 5 * ((a+1) * (a+1)) + 2 * x then 3
  else 4

theorem klab_klx (a b : Nat) : klab a b = klx a (a + 2 * b) := rfl

/-! ## 1.  Narzędzie: rozbijanie kwadratów bez `ring` (nie ma Mathlib) -/

/-- Jedyny „silnik" mnożenia w tym pliku.  Wszystko inne jest jego instancją. -/
theorem key (u v : Nat) : (u + v) * (u + v) = u * u + 2 * (u * v) + v * v := by
  have h1 : (u + v) * (u + v) = (u + v) * u + (u + v) * v := Nat.mul_add _ _ _
  have h2 : (u + v) * u = u * u + v * u := Nat.add_mul _ _ _
  have h3 : (u + v) * v = u * v + v * v := Nat.add_mul _ _ _
  have h4 : v * u = u * v := Nat.mul_comm _ _
  omega

/-- `(a+2b)² = a² + 4ab + 4b²`. -/
theorem sq_x (a b : Nat) : (a + 2 * b) * (a + 2 * b) = a * a + 4 * (a * b) + 4 * (b * b) := by
  have e1 := key a (2 * b)
  have e2 : a * (2 * b) = 2 * (a * b) := Nat.mul_left_comm a 2 b
  have e3 : (2 * b) * (2 * b) = 2 * (b * (2 * b)) := Nat.mul_assoc 2 b (2 * b)
  have e4 : b * (2 * b) = 2 * (b * b) := Nat.mul_left_comm b 2 b
  omega

/-- `(a+b)² = a² + 2ab + b²`. -/
theorem sq_ab (a b : Nat) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := key a b

/-- `(a+1)² = a² + 2a + 1`. -/
theorem sq_a1 (a : Nat) : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
  have e1 := key a 1
  have e2 : a * 1 = a := Nat.mul_one a
  omega

/-! ## 2.  Trzy zagnieżdżenia progów (dla `1 ≤ a`) -/

/-- Pomocnicze: z `(x+2)² < 5a²` wynika `x < 3a` (dla dowolnego `a`).
    Gdyby `3a ≤ x`, to `9a² ≤ x² < 5a²` — sprzeczne już w ℕ. -/
theorem lt_3a_of_sq (a x : Nat) (h : (x + 2) * (x + 2) < 5 * (a * a)) : x < 3 * a := by
  rcases Nat.lt_or_ge x (3 * a) with hc | hle
  · exact hc
  exfalso
  have hm : (3 * a) * (3 * a) ≤ x * x := Nat.mul_le_mul hle hle
  have e1 : (3 * a) * (3 * a) = 3 * (a * (3 * a)) := Nat.mul_assoc 3 a (3 * a)
  have e2 : a * (3 * a) = 3 * (a * a) := Nat.mul_left_comm a 3 a
  have e3 := key x 2
  have e4 : x * 2 = 2 * x := Nat.mul_comm x 2
  omega

theorem nest_01 (a b : Nat) (ha : 1 ≤ a) :
    (a + 2 * b + 2) * (a + 2 * b + 2) < 5 * (a * a) →
    (a + 2 * b + 3) * (a + 2 * b + 3) < 5 * ((a + 1) * (a + 1)) := by
  intro h
  have hlt := lt_3a_of_sq a (a + 2 * b) h
  have e2 := key (a + 2 * b) 2
  have e3 := key (a + 2 * b) 3
  have f2 : (a + 2 * b) * 2 = 2 * (a + 2 * b) := Nat.mul_comm _ 2
  have f3 : (a + 2 * b) * 3 = 3 * (a + 2 * b) := Nat.mul_comm _ 3
  have ea := sq_a1 a
  omega

theorem nest_12 (a b : Nat) (ha : 1 ≤ a) :
    (a + 2 * b + 3) * (a + 2 * b + 3) < 5 * ((a + 1) * (a + 1)) →
    (a + 2 * b + 1) * (a + 2 * b + 1) < 5 * ((a + 1) * (a + 1)) := by
  intro h
  have e3 := key (a + 2 * b) 3
  have e1 := key (a + 2 * b) 1
  have f3 : (a + 2 * b) * 3 = 3 * (a + 2 * b) := Nat.mul_comm _ 3
  have f1 : (a + 2 * b) * 1 = a + 2 * b := Nat.mul_one _
  omega

theorem nest_23 (a b : Nat) (ha : 1 ≤ a) :
    (a + 2 * b + 1) * (a + 2 * b + 1) < 5 * ((a + 1) * (a + 1)) →
    (a + 2 * b) * (a + 2 * b) + 1 < 5 * ((a + 1) * (a + 1)) + 2 * (a + 2 * b) := by
  intro h
  have e1 := key (a + 2 * b) 1
  have f1 : (a + 2 * b) * 1 = a + 2 * b := Nat.mul_one _
  omega

/-! ### 2b.  Te same zagnieżdżenia dla dowolnego `x` (potrzebne dla dzieci) -/

theorem nest01x (a x : Nat) :
    (x + 2) * (x + 2) < 5 * (a * a) → (x + 3) * (x + 3) < 5 * ((a + 1) * (a + 1)) := by
  intro h
  have hlt := lt_3a_of_sq a x h
  have e2 := key x 2
  have e3 := key x 3
  have f2 : x * 2 = 2 * x := Nat.mul_comm _ 2
  have f3 : x * 3 = 3 * x := Nat.mul_comm _ 3
  have ea := sq_a1 a
  omega

theorem nest12x (a x : Nat) :
    (x + 3) * (x + 3) < 5 * ((a + 1) * (a + 1)) → (x + 1) * (x + 1) < 5 * ((a + 1) * (a + 1)) := by
  intro h
  have e3 := key x 3
  have e1 := key x 1
  have f3 : x * 3 = 3 * x := Nat.mul_comm _ 3
  have f1 : x * 1 = x := Nat.mul_one _
  omega

theorem nest23x (a x : Nat) :
    (x + 1) * (x + 1) < 5 * ((a + 1) * (a + 1)) →
    x * x + 1 < 5 * ((a + 1) * (a + 1)) + 2 * x := by
  intro h
  have e1 := key x 1
  have f1 : x * 1 = x := Nat.mul_one _
  omega

/-! ## 3.  Charakteryzacja `klx` — jedno pełne rozgałęzienie, potem pięć `iff` -/

theorem klx_cases (a x : Nat) :
    (klx a x = 0 ∧ (x + 2) * (x + 2) < 5 * (a * a))
    ∨ (klx a x = 1 ∧ ¬((x + 2) * (x + 2) < 5 * (a * a))
        ∧ (x + 3) * (x + 3) < 5 * ((a + 1) * (a + 1)))
    ∨ (klx a x = 2 ∧ ¬((x + 3) * (x + 3) < 5 * ((a + 1) * (a + 1)))
        ∧ (x + 1) * (x + 1) < 5 * ((a + 1) * (a + 1)))
    ∨ (klx a x = 3 ∧ ¬((x + 1) * (x + 1) < 5 * ((a + 1) * (a + 1)))
        ∧ x * x + 1 < 5 * ((a + 1) * (a + 1)) + 2 * x)
    ∨ (klx a x = 4 ∧ ¬(x * x + 1 < 5 * ((a + 1) * (a + 1)) + 2 * x)) := by
  unfold klx
  rcases Nat.lt_or_ge ((x + 2) * (x + 2)) (5 * (a * a)) with h0 | h0
  · exact Or.inl ⟨if_pos h0, h0⟩
  have n0 : ¬((x + 2) * (x + 2) < 5 * (a * a)) := Nat.not_lt.mpr h0
  rw [if_neg n0]
  rcases Nat.lt_or_ge ((x + 3) * (x + 3)) (5 * ((a + 1) * (a + 1))) with h1 | h1
  · exact Or.inr (Or.inl ⟨if_pos h1, n0, h1⟩)
  have n1 : ¬((x + 3) * (x + 3) < 5 * ((a + 1) * (a + 1))) := Nat.not_lt.mpr h1
  rw [if_neg n1]
  rcases Nat.lt_or_ge ((x + 1) * (x + 1)) (5 * ((a + 1) * (a + 1))) with h2 | h2
  · exact Or.inr (Or.inr (Or.inl ⟨if_pos h2, n1, h2⟩))
  have n2 : ¬((x + 1) * (x + 1) < 5 * ((a + 1) * (a + 1))) := Nat.not_lt.mpr h2
  rw [if_neg n2]
  rcases Nat.lt_or_ge (x * x + 1) (5 * ((a + 1) * (a + 1)) + 2 * x) with h3 | h3
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨if_pos h3, n2, h3⟩)))
  have n3 : ¬(x * x + 1 < 5 * ((a + 1) * (a + 1)) + 2 * x) := Nat.not_lt.mpr h3
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨if_neg n3, n3⟩)))

theorem klx_0 (a x : Nat) : klx a x = 0 ↔ (x + 2) * (x + 2) < 5 * (a * a) := by
  constructor
  · intro h
    rcases klx_cases a x with ⟨_, c⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · exact c
    all_goals (rw [h] at e; exact absurd e (by decide))
  · intro c
    rcases klx_cases a x with ⟨e, _⟩ | ⟨_, n, _⟩ | ⟨_, n, _⟩ | ⟨_, n, _⟩ | ⟨_, n⟩
    · exact e
    · exact absurd c n
    · exact absurd (nest01x a x c) n
    · exact absurd (nest12x a x (nest01x a x c)) n
    · exact absurd (nest23x a x (nest12x a x (nest01x a x c))) n

theorem klx_1 (a x : Nat) :
    klx a x = 1 ↔ ¬((x + 2) * (x + 2) < 5 * (a * a))
      ∧ (x + 3) * (x + 3) < 5 * ((a + 1) * (a + 1)) := by
  constructor
  · intro h
    rcases klx_cases a x with ⟨e, _⟩ | ⟨_, c⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · rw [h] at e; exact absurd e (by decide)
    · exact c
    all_goals (rw [h] at e; exact absurd e (by decide))
  · rintro ⟨c0, c1⟩
    rcases klx_cases a x with ⟨_, c⟩ | ⟨e, _⟩ | ⟨_, n, _⟩ | ⟨_, n, _⟩ | ⟨_, n⟩
    · exact absurd c c0
    · exact e
    · exact absurd c1 n
    · exact absurd (nest12x a x c1) n
    · exact absurd (nest23x a x (nest12x a x c1)) n

theorem klx_2 (a x : Nat) :
    klx a x = 2 ↔ ¬((x + 3) * (x + 3) < 5 * ((a + 1) * (a + 1)))
      ∧ (x + 1) * (x + 1) < 5 * ((a + 1) * (a + 1)) := by
  constructor
  · intro h
    rcases klx_cases a x with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, c⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · rw [h] at e; exact absurd e (by decide)
    · rw [h] at e; exact absurd e (by decide)
    · exact c
    all_goals (rw [h] at e; exact absurd e (by decide))
  · rintro ⟨c1, c2⟩
    rcases klx_cases a x with ⟨_, c⟩ | ⟨_, _, c⟩ | ⟨e, _⟩ | ⟨_, n, _⟩ | ⟨_, n⟩
    · exact absurd (nest01x a x c) c1
    · exact absurd c c1
    · exact e
    · exact absurd c2 n
    · exact absurd (nest23x a x c2) n

theorem klx_3 (a x : Nat) :
    klx a x = 3 ↔ ¬((x + 1) * (x + 1) < 5 * ((a + 1) * (a + 1)))
      ∧ x * x + 1 < 5 * ((a + 1) * (a + 1)) + 2 * x := by
  constructor
  · intro h
    rcases klx_cases a x with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, c⟩ | ⟨e, _⟩
    · rw [h] at e; exact absurd e (by decide)
    · rw [h] at e; exact absurd e (by decide)
    · rw [h] at e; exact absurd e (by decide)
    · exact c
    · rw [h] at e; exact absurd e (by decide)
  · rintro ⟨c2, c3⟩
    rcases klx_cases a x with ⟨_, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨e, _⟩ | ⟨_, n⟩
    · exact absurd (nest12x a x (nest01x a x c)) c2
    · exact absurd (nest12x a x c) c2
    · exact absurd c c2
    · exact e
    · exact absurd c3 n

theorem klx_4 (a x : Nat) :
    klx a x = 4 ↔ ¬(x * x + 1 < 5 * ((a + 1) * (a + 1)) + 2 * x) := by
  constructor
  · intro h
    rcases klx_cases a x with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, c⟩
    · rw [h] at e; exact absurd e (by decide)
    · rw [h] at e; exact absurd e (by decide)
    · rw [h] at e; exact absurd e (by decide)
    · rw [h] at e; exact absurd e (by decide)
    · exact c
  · intro c3
    rcases klx_cases a x with ⟨_, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨e, _⟩
    · exact absurd (nest23x a x (nest12x a x (nest01x a x c))) c3
    · exact absurd (nest23x a x (nest12x a x c)) c3
    · exact absurd (nest23x a x c) c3
    · exact absurd c c3
    · exact e

/-! ## 4.  `[D3.1]` — brak równości na progu:  `m² ≠ 5n²` dla `n ≥ 1`

Nieskończone schodzenie.  `5 ∣ m²  →  5 ∣ m` dostajemy przez rozbiór `m % 5`
(reszty `1,2,3,4` dają `m² % 5 ∈ {1,4}`), a nie przez pierwszość 5 z Mathlib. -/

theorem descent : ∀ m : Nat, ∀ n : Nat, m * m = 5 * (n * n) → n = 0 := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact hn
    exfalso
    have hnn : 1 * 1 ≤ n * n := Nat.mul_le_mul hn hn
    have hnm : n < m := by
      rcases Nat.lt_or_ge n m with hlt | hge
      · exact hlt
      · exfalso
        have hle : m * m ≤ n * n := Nat.mul_le_mul hge hge
        omega
    obtain ⟨q, r, hq, hr⟩ : ∃ q r, m = 5 * q + r ∧ r < 5 :=
      ⟨m / 5, m % 5, (Nat.div_add_mod m 5).symm, Nat.mod_lt _ (by decide)⟩
    have hexp := key (5 * q) r
    have e1 : (5 * q) * (5 * q) = 5 * (q * (5 * q)) := Nat.mul_assoc 5 q (5 * q)
    have e2 : q * (5 * q) = 5 * (q * q) := Nat.mul_left_comm q 5 q
    have e3 : (5 * q) * r = 5 * (q * r) := Nat.mul_assoc 5 q r
    have hmm : m * m = (5 * q + r) * (5 * q + r) := by rw [← hq]
    have hr0 : r = 0 := by
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 by omega) with h' | h' | h' | h' | h'
      · exact h'
      all_goals (subst h'; omega)
    subst hr0
    have hq2 : n * n = 5 * (q * q) := by omega
    have hq0 : q = 0 := ih n hnm q hq2
    subst hq0
    omega

theorem no_sq5 (m n : Nat) (hn : 1 ≤ n) : m * m ≠ 5 * (n * n) := by
  intro h
  have := descent m n h
  omega

/-! ### 4b.  Trzy ostre wersje progów (`<` zamiast `≤`), z `no_sq5` -/

/-- Próg `I₁` nigdy nie jest osiągany z równością (`a ≥ 1`). -/
theorem ne_c0 (a b : Nat) (ha : 1 ≤ a) :
    (a + 2 * b + 2) * (a + 2 * b + 2) ≠ 5 * (a * a) := no_sq5 _ a ha

/-- Próg `I₃` nigdy nie jest osiągany z równością. -/
theorem ne_c2 (a b : Nat) :
    (a + 2 * b + 1) * (a + 2 * b + 1) ≠ 5 * ((a + 1) * (a + 1)) :=
  no_sq5 _ (a + 1) (by omega)

/-- Próg `I₄` nigdy nie jest osiągany z równością — to jest `(x−1)² ≠ 5(a+1)²`. -/
theorem ne_c3 (a b : Nat) (hx : 1 ≤ a + 2 * b) :
    (a + 2 * b) * (a + 2 * b) + 1 ≠ 5 * ((a + 1) * (a + 1)) + 2 * (a + 2 * b) := by
  intro heq
  obtain ⟨w, hw⟩ : ∃ w, a + 2 * b = w + 1 := ⟨a + 2 * b - 1, by omega⟩
  rw [hw] at heq
  have ew := key w 1
  exact no_sq5 w (a + 1) (by omega) (by omega)

/-! ## 5.  Dzieci we współrzędnych `(a,b)` przełożone na `klx` -/

/-- A-dziecko: `(a,b) ↦ (a, b+1)`, czyli `x ↦ x+2` przy tym samym `a`. -/
theorem klab_A (a b : Nat) : klab a (b + 1) = klx a (a + 2 * b + 2) := by
  rw [klab_klx]
  congr 1
  all_goals omega

/-- B-dziecko: `(a,b) ↦ (a+b, a)`, czyli `a ↦ a+b`, `x ↦ 3a+b`. -/
theorem klab_B (a b : Nat) : klab (a + b) a = klx (a + b) (3 * a + b) := by
  rw [klab_klx]
  congr 1
  all_goals omega

/-- `(3a+b)² = 9a² + 6ab + b²`. -/
theorem sq_3ab (a b : Nat) :
    (3 * a + b) * (3 * a + b) = 9 * (a * a) + 6 * (a * b) + b * b := by
  have e1 := key (3 * a) b
  have e2 : (3 * a) * (3 * a) = 3 * (a * (3 * a)) := Nat.mul_assoc 3 a (3 * a)
  have e3 : a * (3 * a) = 3 * (a * a) := Nat.mul_left_comm a 3 a
  have e4 : (3 * a) * b = 3 * (a * b) := Nat.mul_assoc 3 a b
  omega

/-! ## 6.  SIEDEM INKLUZJI `[D3]` -/

theorem D3_B_I2 (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    klab a b = 1 → klab (a + b) a = 2 := by
  intro h
  rw [klab_klx] at h
  obtain ⟨hn0, hc1⟩ := (klx_1 a (a + 2 * b)).mp h
  have hc2 := nest12x a (a + 2 * b) hc1
  have hs0 := ne_c0 a b (by omega)
  rw [klab_B]
  refine (klx_2 (a + b) (3 * a + b)).mpr ⟨?_, ?_⟩
  all_goals
    have kb1 := key (3 * a + b) 1
    have kb2 := key (3 * a + b) 2
    have kb3 := key (3 * a + b) 3
    have kb0 := sq_3ab a b
    have kab := sq_ab a b
    have kab1 := sq_a1 (a + b)
    have kp1 := key (a + 2 * b) 1
    have kp2 := key (a + 2 * b) 2
    have kp3 := key (a + 2 * b) 3
    have kpx := sq_x a b
    have ea := sq_a1 a
    omega

theorem D3_A_I3 (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    klab a b = 2 → klab a (b + 1) = 3 := by
  intro h
  rw [klab_klx] at h
  obtain ⟨hn1, hc2⟩ := (klx_2 a (a + 2 * b)).mp h
  rw [klab_A]
  refine (klx_3 a (a + 2 * b + 2)).mpr ⟨?_, ?_⟩
  all_goals
    have kp1 := key (a + 2 * b) 1
    have kp2 := key (a + 2 * b) 2
    have kp3 := key (a + 2 * b) 3
    have kq1 := key (a + 2 * b + 2) 1
    have ea := sq_a1 a
    omega

theorem D3_B_I3 (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    klab a b = 2 → klab (a + b) a = 2 := by
  intro h
  rw [klab_klx] at h
  obtain ⟨hn1, hc2⟩ := (klx_2 a (a + 2 * b)).mp h
  have hn0 : ¬((a + 2 * b + 2) * (a + 2 * b + 2) < 5 * (a * a)) :=
    fun hc0 => hn1 (nest01x a (a + 2 * b) hc0)
  have hs0 := ne_c0 a b (by omega)
  rw [klab_B]
  refine (klx_2 (a + b) (3 * a + b)).mpr ⟨?_, ?_⟩
  all_goals
    have kb1 := key (3 * a + b) 1
    have kb2 := key (3 * a + b) 2
    have kb3 := key (3 * a + b) 3
    have kb0 := sq_3ab a b
    have kab := sq_ab a b
    have kab1 := sq_a1 (a + b)
    have kp1 := key (a + 2 * b) 1
    have kp2 := key (a + 2 * b) 2
    have kp3 := key (a + 2 * b) 3
    have kpx := sq_x a b
    have ea := sq_a1 a
    omega

theorem D3_A_I4 (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    klab a b = 3 → klab a (b + 1) = 4 := by
  intro h
  rw [klab_klx] at h
  obtain ⟨hn2, hc3⟩ := (klx_3 a (a + 2 * b)).mp h
  rw [klab_A]
  refine (klx_4 a (a + 2 * b + 2)).mpr ?_
  have kp1 := key (a + 2 * b) 1
  have kp2 := key (a + 2 * b) 2
  have ea := sq_a1 a
  omega

theorem D3_B_I4 (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    klab a b = 3 → klab (a + b) a = 1 := by
  intro h
  rw [klab_klx] at h
  obtain ⟨hn2, hc3⟩ := (klx_3 a (a + 2 * b)).mp h
  have hs2 := ne_c2 a b
  rw [klab_B]
  refine (klx_1 (a + b) (3 * a + b)).mpr ⟨?_, ?_⟩
  all_goals
    have kb1 := key (3 * a + b) 1
    have kb2 := key (3 * a + b) 2
    have kb3 := key (3 * a + b) 3
    have kb0 := sq_3ab a b
    have kab := sq_ab a b
    have kab1 := sq_a1 (a + b)
    have kp1 := key (a + 2 * b) 1
    have kp2 := key (a + 2 * b) 2
    have kp3 := key (a + 2 * b) 3
    have kpx := sq_x a b
    have ea := sq_a1 a
    omega

theorem D3_A_I5 (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    klab a b = 4 → klab a (b + 1) = 4 := by
  intro h
  rw [klab_klx] at h
  have hn3 := (klx_4 a (a + 2 * b)).mp h
  have hn2 : ¬((a + 2 * b + 1) * (a + 2 * b + 1) < 5 * ((a + 1) * (a + 1))) :=
    fun hc2 => hn3 (nest23x a (a + 2 * b) hc2)
  rw [klab_A]
  refine (klx_4 a (a + 2 * b + 2)).mpr ?_
  have kp1 := key (a + 2 * b) 1
  have kp2 := key (a + 2 * b) 2
  have ea := sq_a1 a
  omega

theorem D3_B_I5 (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    klab a b = 4 → klab (a + b) a = 0 := by
  intro h
  rw [klab_klx] at h
  have hn3 := (klx_4 a (a + 2 * b)).mp h
  have hs3 := ne_c3 a b (by omega)
  rw [klab_B]
  refine (klx_0 (a + b) (3 * a + b)).mpr ?_
  have kb2 := key (3 * a + b) 2
  have kb0 := sq_3ab a b
  have kab := sq_ab a b
  have kp1 := key (a + 2 * b) 1
  have kpx := sq_x a b
  have ea := sq_a1 a
  omega

end A252864.DYN2
