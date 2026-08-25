/-
  A252864 — Tree.lean.  DRZEWO KIMBERLINGA, OBLICZALNE.
  ✅ SKOMPILOWANE: Lean 4.34.0-rc2, BEZ Mathlib.

  Po co ten plik istnieje:
  `Checks.lean` traktuje 43 wyrazy jako DANE.  Dane wzięliśmy z symulacji w Pythonie —
  czyli z programu, którego nikt nie zweryfikował.  Tutaj ciąg jest ZDEFINIOWANY
  z reguły drzewa i wyliczony przez Lean, a zgodność z listą jest TWIERDZENIEM.

  ⚠️ UCZCIWIE O SILE DOWODU: `native_decide` ufa KOMPILATOROWI Lean (dodaje aksjomat
  `Lean.ofReduceBool`), a nie samemu jądru.  To jest słabsze niż `decide`.
  Jest jednak MOCNIEJSZE niż „sprawdziliśmy skryptem w Pythonie", bo weryfikowana
  jest definicja zapisana w tym samym języku, w którym stoi teza.
  Aksjomaty każdego twierdzenia wypisuje `Axioms.lean`.
-/
import Std.Data.HashSet

namespace A252864.Tree

abbrev Node := Nat × Nat

/-- Reguła OEIS: z `(j,k)` powstają `(j, k+1)` oraz `(k, j+k)`. -/
def childA (p : Node) : Node := (p.1, p.2 + 1)
def childB (p : Node) : Node := (p.2, p.1 + p.2)

/-- Jeden krok: dzieci bieżącego pokolenia, z odrzuceniem WSZYSTKIEGO, co już
    kiedykolwiek wystąpiło (także duplikatów wewnątrz tego samego pokolenia). -/
def stepAll (seen : Std.HashSet Node) (cur : List Node) :
    Std.HashSet Node × List Node :=
  cur.foldl
    (fun (st : Std.HashSet Node × List Node) (p : Node) =>
      let push := fun (st : Std.HashSet Node × List Node) (c : Node) =>
        if st.1.contains c then st else (st.1.insert c, c :: st.2)
      push (push st (childA p)) (childB p))
    (seen, [])

/-- Stan po `n` pokoleniach: (widziane, bieżące pokolenie, rozmiary pokoleń 0..n). -/
def run : Nat → Std.HashSet Node × List Node × List Nat
  | 0 => (((∅ : Std.HashSet Node).insert (0, 0)), [(0, 0)], [1])
  | n + 1 =>
    let (s, cur, sizes) := run n
    let (s', nxt) := stepAll s cur
    (s', nxt, sizes ++ [nxt.length])

/-- `a 0 … a (N-1)` wyliczone z reguły drzewa. -/
def gens (N : Nat) : List Nat := (run (N - 1)).2.2

/-! ## ① Ciąg z DEFINICJI zgadza się z DATA — dla 33 wyrazów

To jest to twierdzenie, dla którego ten plik powstał: lista w `Checks.lean`
przestaje być założeniem. -/

def data33 : List Nat :=
  [1, 1, 2, 3, 5, 8, 12, 18, 25, 35, 51, 75, 110, 161, 236, 346, 507, 743, 1089, 1596,
   2339, 3428, 5024, 7363, 10791, 15815, 23178, 33969, 49784, 72962, 106931, 156715,
   229677]

theorem tree_matches_data_33 : gens 33 = data33 := by native_decide

/-! ## ② Rekurencja Stolla NA DEFINICJI DRZEWA (nie na liście) dla n = 12 … 32 -/

def aT (n : Nat) : Nat := (gens 33).getD n 0

theorem stoll_on_tree_12_32 :
    ∀ n ∈ List.range' 12 21, aT n == aT (n - 1) + aT (n - 3) := by native_decide

/-! ## ③ A counterexample to a claim in the OEIS entry

The entry A252864 contains the comment, verbatim:
  "Every ordered pair of nonnegative integers occurs exactly once in T."
This does not hold as stated.  The condition `j ≤ k` is invariant under both
production rules and holds at the root `(0,0)`, so no pair with `j > k` is ever
produced.  Smallest witness: `(1,0)`.
A machine-checked proof is `SeqBase.invariant_j_le_k`. -/

def seenUpTo (n : Nat) : Std.HashSet Node := (run n).1

theorem pair_1_0_absent : ¬ (seenUpTo 24).contains (1, 0) = true := by native_decide

/-- Mocniej: WSZYSTKIE węzły osiągnięte w 24 pokoleniach spełniają `j ≤ k`.
    (Nie jest to dowód dla wszystkich pokoleń — to jest świadek na skończonym
    wycinku.  Dowód ogólny jest jednowierszową indukcją i stoi w `Sequence.lean`.) -/
theorem invariant_j_le_k_upto_24 :
    (seenUpTo 24).toList.all (fun p => p.1 ≤ p.2) = true := by native_decide

/-- I świadek, że przyrząd nie jest ślepy: para `(0,1)` (z `j ≤ k`) JEST obecna. -/
theorem pair_0_1_present : (seenUpTo 24).contains (0, 1) = true := by native_decide


/-! ## ④ 🔑 MOST DO JĄDRA — `run` policzone LISTĄ zamiast `Std.HashSet`

  ⚠️ POWÓD ISTNIENIA (zmierzone 24.08.2026):  `Std.HashSet` **nie redukuje się
  w jądrze Lean w ogóle** — nie „wolno", tylko reduktor STAJE.  Kontrola minimalna,
  bez naszego kodu:
      `example : ((∅ : Std.HashSet Nat).insert 3).contains 3 = true := by decide`
      → `reduction got stuck at the Decidable instance`  (0 s)
  Dlatego KAŻDE twierdzenie o `a n` musiało dotąd iść przez `native_decide`,
  czyli przez aksjomat `Lean.ofReduceBool` (zaufanie do KOMPILATORA, nie do jądra).

  Poniżej stoi replika `stepAll`/`run` na zwykłej LIŚCIE (`runL`) — identyczna co do
  kolejności foldu i consów — oraz DOWÓD, że oba przebiegi dają to samo pokolenie
  (`run_gen_eq`).  Dowód jest zwykły (indukcja + `Std.HashSet.contains_insert`),
  bez `native_decide` i bez `sorry`.

  ⇒ Twierdzenia o małych `n` (`base12`, `base13`, `case_twelve`) idą odtąd przez
  `decide`, czyli przez JĄDRO.  Ich `#print axioms` traci `_native.native_decide.ax`.

  ⚠️ GRANICA, ŚWIADOMA: dedup listowy jest O(n²).  Dla `n = 12,13` (346 / 507 węzłów)
  jądro liczy w 27 / 67 s.  Dla `gens 33` (~723 000 węzłów) to ~2,6·10¹¹ porównań —
  NIE DA SIĘ.  Dlatego `tree_matches_data_33` i świadkowie na `seenUpTo 24`
  ZOSTAJĄ przy `native_decide`; HashSet jest tam potrzebny dla wydajności. -/

def FH (st : Std.HashSet Node × List Node) (p : Node) : Std.HashSet Node × List Node :=
  let push := fun (st : Std.HashSet Node × List Node) (c : Node) =>
    if st.1.contains c then st else (st.1.insert c, c :: st.2)
  push (push st (childA p)) (childB p)

def FL (st : List Node × List Node) (p : Node) : List Node × List Node :=
  let push := fun (st : List Node × List Node) (c : Node) =>
    if st.1.contains c then st else (c :: st.1, c :: st.2)
  push (push st (childA p)) (childB p)

def stepAllL (seen : List Node) (cur : List Node) : List Node × List Node :=
  cur.foldl FL (seen, [])

def runL : Nat → List Node × List Node × List Nat
  | 0 => ([(0, 0)], [(0, 0)], [1])
  | n + 1 =>
    let (s, cur, sizes) := runL n
    let (s', nxt) := stepAllL s cur
    (s', nxt, sizes ++ [nxt.length])

theorem stepAll_eq_foldl (s : Std.HashSet Node) (cur : List Node) :
    stepAll s cur = cur.foldl FH (s, []) := rfl

def AgreeP (sh : Std.HashSet Node × List Node) (sl : List Node × List Node) : Prop :=
  (∀ x, sh.1.contains x = sl.1.contains x) ∧ sh.2 = sl.2

theorem beq_symm_node (c x : Node) : (c == x) = (x == c) := by
  by_cases h : c = x
  · subst h; rfl
  · have h1 : (c == x) = false := by simpa using h
    have h2 : (x == c) = false := by simpa using (Ne.symm h)
    rw [h1, h2]

theorem agree_insert {s : Std.HashSet Node} {l : List Node}
    (h : ∀ x, s.contains x = l.contains x) (c : Node) :
    ∀ x, (s.insert c).contains x = (c :: l).contains x := by
  intro x
  rw [Std.HashSet.contains_insert, List.contains_cons, h x, beq_symm_node]

theorem push_ok {sh : Std.HashSet Node × List Node} {sl : List Node × List Node}
    (h : AgreeP sh sl) (c : Node) :
    AgreeP (if sh.1.contains c then sh else (sh.1.insert c, c :: sh.2))
           (if sl.1.contains c then sl else (c :: sl.1, c :: sl.2)) := by
  obtain ⟨h1, h2⟩ := h
  by_cases hc : sh.1.contains c = true
  · have hc' : sl.1.contains c = true := by rw [← h1 c]; exact hc
    simp only [hc, hc', if_pos]
    exact ⟨h1, h2⟩
  · have hc' : ¬ (sl.1.contains c = true) := by rw [← h1 c]; exact hc
    simp only [hc, hc', Bool.false_eq_true, if_false]
    refine ⟨agree_insert h1 c, ?_⟩
    simp [h2]

theorem step_ok {sh : Std.HashSet Node × List Node} {sl : List Node × List Node}
    (h : AgreeP sh sl) (p : Node) : AgreeP (FH sh p) (FL sl p) :=
  push_ok (push_ok h (childA p)) (childB p)

theorem foldl_agree (cur : List Node) :
    ∀ sh sl, AgreeP sh sl → AgreeP (cur.foldl FH sh) (cur.foldl FL sl) := by
  induction cur with
  | nil => intro sh sl h; exact h
  | cons p ps ih =>
      intro sh sl h
      simp only [List.foldl_cons]
      exact ih _ _ (step_ok h p)

theorem stepAll_agree {s : Std.HashSet Node} {l : List Node}
    (hc : ∀ x, s.contains x = l.contains x) (cur : List Node) :
    AgreeP (stepAll s cur) (stepAllL l cur) := by
  rw [stepAll_eq_foldl]
  exact foldl_agree cur _ _ ⟨hc, rfl⟩

theorem run_succ_fst (n : Nat) : (run (n+1)).1 = (stepAll (run n).1 (run n).2.1).1 := rfl
theorem run_succ_gen (n : Nat) : (run (n+1)).2.1 = (stepAll (run n).1 (run n).2.1).2 := rfl
theorem runL_succ_fst (n : Nat) : (runL (n+1)).1 = (stepAllL (runL n).1 (runL n).2.1).1 := rfl
theorem runL_succ_gen (n : Nat) : (runL (n+1)).2.1 = (stepAllL (runL n).1 (runL n).2.1).2 := rfl

theorem run_agree : ∀ n,
    (∀ x, (run n).1.contains x = (runL n).1.contains x) ∧ (run n).2.1 = (runL n).2.1 := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, rfl⟩
      have h0 : ∀ x, (∅ : Std.HashSet Node).contains x = ([] : List Node).contains x := by
        intro x; simp
      exact agree_insert h0 (0, 0)
  | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      simp only [run_succ_fst, runL_succ_fst, run_succ_gen, runL_succ_gen]
      rw [← ih2]
      exact stepAll_agree ih1 (run n).2.1

/-- 🔑 MOST: pokolenie liczone HashSetem i pokolenie liczone LISTĄ to ten sam obiekt. -/
theorem run_gen_eq (n : Nat) : (run n).2.1 = (runL n).2.1 := (run_agree n).2

end A252864.Tree
