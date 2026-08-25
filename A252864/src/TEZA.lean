/-
  ══════════════════════════════════════════════════════════════════════════════
  TEZA.lean — ZAMROŻONA TEZA GŁÓWNA.  OEIS A252864 / konjektura Michaela Stolla.
  ══════════════════════════════════════════════════════════════════════════════

  ZASADA (wzorowana na `openai/ten-proofs`, katalog `ComparatorChallenges/`):
  teza jest ZAPISANA I PODPISANA, ZANIM ktokolwiek zacznie ją dowodzić.  Ten plik
  zawiera WYŁĄCZNIE sformułowanie i definicje, od których ono zależy; dowód
  główny jest `sorry`.  Plik jest SAMOWYSTARCZALNY — nie importuje ani jednej
  linijki z naszego drzewa, więc nic w naszym drzewie nie może zmienić tego,
  CO tu jest napisane.  Suma kontrolna pliku stoi w `../TEZA.json`.

  ──────────────────────────────────────────────────────────────────────────────
  TREŚĆ PO POLSKU (dla kogoś, kto nie zna tego repo)
  ──────────────────────────────────────────────────────────────────────────────
  Budujemy drzewo T par liczb całkowitych nieujemnych.  Korzeniem jest (0,0).
  Każdy węzeł (j,k) ma dwoje dzieci:  (j, k+1)  oraz  (k, j+k).
  Węzeł wchodzi do drzewa TYLKO przy pierwszym pojawieniu się: para, która już
  wystąpiła w którymkolwiek wcześniejszym pokoleniu (lub wcześniej w tym samym
  pokoleniu), jest odrzucana.  `A n` = liczba par w pokoleniu n.

  Pokolenia:  A 0 = 1 (sam korzeń), potem 1, 2, 3, 5, 8, 12, 18, 25, 35, 51, 75,
  110, 161, …  — to jest ciąg OEIS A252864, z TĄ SAMĄ indeksacją: wpis ma
  offset 0 i a(0) = 1 (odczyt u źródła 25.08.2026: `%O A252864 0,3`,
  `%S A252864 1,1,2,3,5,8,12,…`).

  KONJEKTURA STOLLA (MathOverflow 195207, odpowiedź 195264, 2015-01-30; ta sama
  w polu Formula wpisu OEIS A252864):

        a(n) = a(n−1) + a(n−3)   dla wszystkich n ≥ 12.

  Próg 12 jest OSTRY — dla n = 11 wzór jest fałszywy (75 ≠ 51 + 25 = 76).
  Konjektura pozostaje otwarta w OEIS (rev. 30, 2025-11-26).

  ──────────────────────────────────────────────────────────────────────────────
  DLACZEGO TA TEZA MÓWI O A252864, A NIE O CZYMKOLWIEK
  ──────────────────────────────────────────────────────────────────────────────
  `StollConjecture` NIE jest kwantyfikowane po ciągach.  Nie ma w nim zmiennej
  `a : Nat → Int` ani żadnego innego parametru ciągu — jest w nim JEDNA stała
  `A252864.TEZA.A`, zdefiniowana niżej regułą drzewa.  Nie da się „podstawić
  ciągu zerowego": nie ma gdzie.  Świadkiem, że `A` to naprawdę A252864, a nie
  jakiś inny ciąg spełniający tę rekurencję, są dwa DOWIEDZIONE (bez `sorry`,
  bez `native_decide`) twierdzenia poniżej: `A_matches_OEIS` przybija `A` do
  czternastu wyrazów z pola DATA wpisu OEIS, a `threshold_tight` pokazuje, że
  próg n ≥ 12 jest konieczny.  Ciąg zerowy oblewa oba.

  (Świadek, dla którego ten akapit tu stoi: `A252864.GF.barker_iff` ma czyste
  aksjomaty, ale jest kwantyfikowane po DOWOLNYM `a : Nat → Int` — jest więc
  prawdziwe dla ciągu zerowego i nie orzeka o A252864.  Test na każdą przyszłą
  tezę: podstaw ciąg zerowy.  Jeśli teza przeżyje — jest za słaba.)

  ── ZAKAZY OBOWIĄZUJĄCE W TYM PLIKU (sprawdzane przez `_BRAMA`):
     ⛔ `native_decide`  (dokłada aksjomat `Lean.ofReduceBool`)
     ⛔ `axiom`, `@[implemented_by]`, `unsafe`
     ✅ jedyny dozwolony `sorry` = dowód `stoll_conjecture`, i tylko on
-/

namespace A252864.TEZA

/-- Węzeł drzewa: uporządkowana para liczb naturalnych. -/
abbrev Node := Nat × Nat

/-- Pierwsza reguła OEIS: `(j,k) ↦ (j, k+1)`. -/
def childA (p : Node) : Node := (p.1, p.2 + 1)

/-- Druga reguła OEIS: `(j,k) ↦ (k, j+k)`. -/
def childB (p : Node) : Node := (p.2, p.1 + p.2)

/-- Dołożenie obojga dzieci węzła `p` do stanu `(widziane, bieżące pokolenie)`,
    z odrzuceniem wszystkiego, co już kiedykolwiek wystąpiło. -/
def FL (st : List Node × List Node) (p : Node) : List Node × List Node :=
  let push := fun (st : List Node × List Node) (c : Node) =>
    if st.1.contains c then st else (c :: st.1, c :: st.2)
  push (push st (childA p)) (childB p)

/-- Całe następne pokolenie: przejście po bieżącym pokoleniu z jednym wspólnym
    zbiorem `seen`, więc duplikaty WEWNĄTRZ pokolenia też odpadają. -/
def stepAllL (seen : List Node) (cur : List Node) : List Node × List Node :=
  cur.foldl FL (seen, [])

/-- Stan po `n` pokoleniach: `(widziane, pokolenie n, rozmiary pokoleń 0..n)`. -/
def runL : Nat → List Node × List Node × List Nat
  | 0 => ([(0, 0)], [(0, 0)], [1])
  | n + 1 =>
    let (s, cur, sizes) := runL n
    let (s', nxt) := stepAllL s cur
    (s', nxt, sizes ++ [nxt.length])

/-- **Ciąg A252864**: liczba par w pokoleniu `n` drzewa `T`. -/
def A (n : Nat) : Nat := (runL n).2.1.length

/-! ### KOTWICE — dowiedzione, bez `sorry` i bez `native_decide`.
    To one odróżniają `A` od dowolnego innego ciągu. -/

set_option maxRecDepth 100000 in
/-- `A` zgadza się z polem DATA wpisu OEIS A252864 na czternastu pierwszych
    wyrazach.  Liczone przez JĄDRO Lean (`decide +kernel`), nie przez kompilator:
    `#print axioms` na tym twierdzeniu NIE pokazuje `Lean.ofReduceBool`. -/
theorem A_matches_OEIS :
    (List.range 14).map A = [1, 1, 2, 3, 5, 8, 12, 18, 25, 35, 51, 75, 110, 161] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Próg `n ≥ 12` jest OSTRY: dla `n = 11` rekurencja Stolla jest fałszywa. -/
theorem threshold_tight : A 11 ≠ A 10 + A 8 := by decide +kernel

/-! ### ⛔ TEZA GŁÓWNA — ZAMROŻONA.  Poniższego zdania NIE WOLNO zmieniać. -/

/-- **Konjektura Stolla dla A252864.**  Jedna stała `A`, zero kwantyfikacji
    po ciągach. -/
def StollConjecture : Prop :=
  ∀ n : Nat, 12 ≤ n → A n = A (n - 1) + A (n - 3)

/-- Teza główna.  Dowód celowo pusty — to jest WYZWANIE, nie dowód. -/
theorem stoll_conjecture : StollConjecture := by
  sorry

end A252864.TEZA
