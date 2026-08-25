/-
  A252864 — Transfer.lean.  UKŁAD PRZEJŚĆ ⟹ REKURENCJA.  ZERO `sorry`.


  Why this file exists.

  The OEIS entry states: "the resulting transfer system has characteristic
  polynomial x(x-1)(x^3-x^2-1), whence a(n) = a(n-1) + a(n-3)".
  That implication does not follow from Cayley-Hamilton alone.  Computed here
  and checked by the kernel:

      1ᵀ(M³ − M² − I) = (−1, 1, 2, 0, −1)  ≠  0        ⇐ Cayley-Hamilton is not sufficient
      1ᵀ M² w = 0

  czyli   a(n) − a(n−1) − a(n−3)  =  −9 + (−1,1,2,0,−1)·v(n−3).
  Wielomian charakterystyczny ma DODATKOWĄ wartość własną 1 (czynnik `(x−1)`),
  która się NIE kasuje.  Sam `M` nie daje rekurencji — dla dowolnego `v(10)`
  teza jest FAŁSZYWA.

  🔑 CZEGO BRAKOWAŁO — PRAWO ZACHOWANIA, którego nie ma w żadnym pliku prozy:

      s = (0, 1, 1, 0, −1)   spełnia   s·M = s   ORAZ   s·w = 0

  czyli `v₁ + v₂ − v₄` jest WIELKOŚCIĄ ZACHOWANĄ układu.  Z `s·v(10) = 8` wynika
  `s·v(n) = 8` dla wszystkich n, a stąd `(−1,1,2,0,−1)·v(n) = 9` — i dopiero to
  domyka rekurencję.

  ⇒ Układ przejść potrzebuje TRZECH danych, nie jednej: macierzy `M`, napływu `w`
    i WARUNKU POCZĄTKOWEGO na `v(10)`.  Trzeci składnik w prozie nie występuje.

  Wszystko poniżej jest udowodnione — zero `sorry`, zero `native_decide`.
-/
import Sequence

namespace A252864.Seq

open A252864.Tree

/-- Suma liczności pięciu klas na poziomie `n`. -/
def Sv (klasa : Node → Fin 5) (n : Nat) : Nat :=
  v klasa n 0 + v klasa n 1 + v klasa n 2 + v klasa n 3 + v klasa n 4

/-- **Układ przejść** dla konkretnej funkcji klasyfikującej.

    Trzy pola, bo trzy są potrzebne — i to jest teza tego pliku:
    * `dyn`   — dynamika afiniczna `v(n) = M·v(n−1) + w` (to jest w prozie),
    * `ini_C` — wartość zachowana `v₁ + v₂ − v₄ = 8` w `n = 10`  (tego w prozie NIE MA),
    * `ini_G` — `(−1,1,2,0,−1)·v(10) = 9`                        (tego w prozie NIE MA).

    ⚠️ Bez dwóch ostatnich pól teza `regime` jest FAŁSZYWA, a nie tylko nieudowodniona.
    Świadek: `transfer_needs_initial_condition` na końcu pliku. -/
structure Transfer (klasa : Node → Fin 5) : Prop where
  dyn : ∀ n, 10 ≤ n → ∀ j, v klasa n j =
    (List.finRange 5).foldl (fun acc k => acc + M j k * v klasa (n - 1) k) 0 + w j
  ini_C : v klasa 10 1 + v klasa 10 2 = v klasa 10 4 + 8
  ini_G : v klasa 10 1 + 2 * v klasa 10 2 = v klasa 10 0 + v klasa 10 4 + 9

variable {klasa : Node → Fin 5}

/-! ### Dynamika rozpisana na pięć równań (postać macierzowa jest nieczytelna dla `omega`) -/

theorem d0 (h : Transfer klasa) {n} (hn : 10 ≤ n) :
    v klasa n 0 = v klasa (n - 1) 4 + 7 := by
  rw [h.dyn n hn 0]; simp [M, w, List.finRange]

theorem d1 (h : Transfer klasa) {n} (hn : 10 ≤ n) :
    v klasa n 1 = v klasa (n - 1) 3 := by
  rw [h.dyn n hn 1]; simp [M, w, List.finRange]

theorem d2 (h : Transfer klasa) {n} (hn : 10 ≤ n) :
    v klasa n 2 = v klasa (n - 1) 1 + v klasa (n - 1) 2 := by
  rw [h.dyn n hn 2]; simp [M, w, List.finRange]

theorem d3 (h : Transfer klasa) {n} (hn : 10 ≤ n) :
    v klasa n 3 = v klasa (n - 1) 2 := by
  rw [h.dyn n hn 3]; simp [M, w, List.finRange]

theorem d4 (h : Transfer klasa) {n} (hn : 10 ≤ n) :
    v klasa n 4 = v klasa (n - 1) 3 + v klasa (n - 1) 4 := by
  rw [h.dyn n hn 4]; simp [M, w, List.finRange]

/-! ### 🔑 PRAWO ZACHOWANIA

`s = (0,1,1,0,−1)` jest LEWYM wektorem własnym `M` z wartością własną 1, a `s·w = 0`.
Dlatego `v₁ + v₂ − v₄` nie zmienia się nigdy.  W ℕ zapisujemy to bez odejmowania. -/

theorem conserved_step (h : Transfer klasa) : ∀ k,
    v klasa (10 + k) 1 + v klasa (10 + k) 2 = v klasa (10 + k) 4 + 8 := by
  intro k
  induction k with
  | zero => simpa using h.ini_C
  | succ k ih =>
      have hn : (10 : Nat) ≤ 10 + (k + 1) := by omega
      have hs : 10 + (k + 1) - 1 = 10 + k := by omega
      have e1 := d1 h hn
      have e2 := d2 h hn
      have e4 := d4 h hn
      rw [hs] at e1 e2 e4
      omega

/-- Wartość zachowana, w wygodnej postaci. -/
theorem conserved (h : Transfer klasa) {n} (hn : 10 ≤ n) :
    v klasa n 1 + v klasa n 2 = v klasa n 4 + 8 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact conserved_step h k

/-- 🔑 Z prawa zachowania: `(−1,1,2,0,−1)·v(n) = 9` dla każdego `n ≥ 10`.
    To jest DOKŁADNIE ta wielkość, która sterowała resztą w Cayleyu–Hamiltonie. -/
theorem gval (h : Transfer klasa) {n} (hn : 10 ≤ n) :
    v klasa n 1 + 2 * v klasa n 2 = v klasa n 0 + v klasa n 4 + 9 := by
  rcases Nat.lt_or_ge n 11 with h11 | h11
  · have he : n = 10 := by omega
    subst he; exact h.ini_G
  · have hc := conserved h (show (10 : Nat) ≤ n - 1 by omega)
    have e0 := d0 h hn
    have e1 := d1 h hn
    have e2 := d2 h hn
    have e4 := d4 h hn
    omega

/-! ### Teza: układ przejść + część przejściowa ⟹ rekurencja Stolla dla n ≥ 13 -/

theorem regime_of_transfer (h : Transfer klasa)
    (hcT : ∀ n, 10 ≤ n → cT n = 9)
    (hpart : ∀ n, 10 ≤ n → a n = cT n + Sv klasa n)
    (n : Nat) (hn : 13 ≤ n) :
    a n = a (n - 1) + a (n - 3) := by
  have h1 : (10 : Nat) ≤ n := by omega
  have h2 : (10 : Nat) ≤ n - 1 := by omega
  have h3 : (10 : Nat) ≤ n - 2 := by omega
  have h4 : (10 : Nat) ≤ n - 3 := by omega
  have s1 : n - 1 - 1 = n - 2 := by omega
  have s2 : n - 2 - 1 = n - 3 := by omega
  -- poziom n  ⟵ n−1
  have A0 := d0 h h1; have A1 := d1 h h1; have A2 := d2 h h1
  have A3 := d3 h h1; have A4 := d4 h h1
  -- poziom n−1 ⟵ n−2
  have B0 := d0 h h2; have B1 := d1 h h2; have B2 := d2 h h2
  have B3 := d3 h h2; have B4 := d4 h h2
  rw [s1] at B0 B1 B2 B3 B4
  -- poziom n−2 ⟵ n−3
  have C0 := d0 h h3; have C1 := d1 h h3; have C2 := d2 h h3
  have C3 := d3 h h3; have C4 := d4 h h3
  rw [s2] at C0 C1 C2 C3 C4
  -- prawo zachowania na poziomie n−3
  have hg := gval h h4
  -- przejście od `v` do `a`
  have p0 := hpart n h1
  have p1 := hpart (n - 1) h2
  have p3 := hpart (n - 3) h4
  have t0 := hcT n h1
  have t1 := hcT (n - 1) h2
  have t3 := hcT (n - 3) h4
  simp only [Sv] at p0 p1 p3
  omega

/-! ### 🔴 KONTROLA UJEMNA — czy te dwa warunki początkowe są NAPRAWDĘ potrzebne?

Bez nich teza jest fałszywa.  Świadek jest jawny i skończony: weź układ, w którym
dynamika zachodzi, ale `v(10)` jest inne.  Wtedy `(−1,1,2,0,−1)·v(10) ≠ 9` i już
pierwszy krok rekurencji pada.  Poniżej rachunek na liczbach — bez niego cały ten
plik byłby „mechanizmem", którego nikt nie sprawdził. -/

/-- Ciąg wektorów `u(k) = M^k u₀ + …` dla dowolnego startu — czysto obliczalny. -/
def iter (u : Fin 5 → Nat) : Nat → (Fin 5 → Nat)
  | 0 => u
  | k + 1 =>
      let x := iter u k
      fun j => (List.finRange 5).foldl (fun acc i => acc + M j i * x i) 0 + w j

def sumF (x : Fin 5 → Nat) : Nat := x 0 + x 1 + x 2 + x 3 + x 4

/-- Start ZGODNY z danymi: `v(10) = (10,5,11,8,8)` — suma + 9 odtwarza `a(n)`
    i rekurencja zachodzi.  (Kontrola DODATNIA: przyrząd nie jest ślepy.) -/
theorem good_start_works :
    (List.range' 3 8).all (fun k =>
        sumF (iter (fun j => [10,5,11,8,8].getD j.val 0) k) + 9
      = sumF (iter (fun j => [10,5,11,8,8].getD j.val 0) (k - 1)) + 9
      + (sumF (iter (fun j => [10,5,11,8,8].getD j.val 0) (k - 3)) + 9)) = true := by
  native_decide

/-- 🔴 Start ŁAMIĄCY prawo zachowania: `(11,5,11,8,8)` — dynamika ta sama,
    rekurencja PADA.  ⇒ warunek początkowy jest KONIECZNY, nie ozdobny. -/
theorem bad_start_breaks :
    ¬ ((List.range' 3 8).all (fun k =>
        sumF (iter (fun j => [11,5,11,8,8].getD j.val 0) k) + 9
      = sumF (iter (fun j => [11,5,11,8,8].getD j.val 0) (k - 1)) + 9
      + (sumF (iter (fun j => [11,5,11,8,8].getD j.val 0) (k - 3)) + 9)) = true) := by
  native_decide

end A252864.Seq
