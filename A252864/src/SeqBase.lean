/-
  A252864 — Sequence.lean.  ŁAŃCUCH DOWODU KONJEKTURY STOLLA.
  ✅ SKOMPILOWANE: Lean 4.34.0-rc2, BEZ Mathlib.

  Ten plik NIE jest dowodem.  Jest MAPĄ LUK: każde `sorry` to ogniwo, którego
  proza w `DOWOD_A252864_KOMPLET.md` twierdzi, że ma, a którego nie umiem tu podać.
  Lista `sorry` z komentarzami jest głównym produktem tego pliku.

  Kluczowa różnica wobec prozy: tutaj `a n` NIE jest listą liczb ani opisem
  słownym — jest funkcją obliczalną, zdefiniowaną z reguły drzewa (`Tree.run`).
  Dzięki temu teza `stoll` jest zdaniem o KONKRETNYM obiekcie, a nie o intencji.
-/
import Tree
import Bfs

namespace A252864.Seq

open A252864.Tree

/-- `a n` = liczność n-tego pokolenia, wprost z definicji drzewa Kimberlinga. -/
def a (n : Nat) : Nat := (run n).2.1.length

/-- Zgodność definicji z listą DATA (n ≤ 32) — dowiedziona w `Tree.lean`. -/
theorem a_matches_data : (List.range 33).map a = Tree.data33 := by native_decide

/-! ## 1.  ⚠️ ZNALEZISKO 🟡 — „i.e." w komentarzu OEIS jest TWIERDZENIEM

Komentarz OEIS pisze:
  „Let l(a,b) be the generation index of (a,b), **i.e.** the least number of steps
   from (0,0)".
Słowo „i.e." sugeruje, że to jedna definicja.  To są DWA różne pojęcia:
  ① indeks pokolenia, w którym węzeł faktycznie się pojawia (zależy od reguły dedup),
  ② najmniejsza liczba kroków `A`/`B` prowadząca z (0,0) do węzła.
Ich równość jest nietrywialna — dedup mógłby w zasadzie „opóźnić" węzeł.
W Leanie nie da się tego napisać jako jednej definicji; trzeba dwóch i lematu. -/

/-- ① węzeł pojawia się w pokoleniu `n`. -/
def InGen (p : Node) (n : Nat) : Prop := p ∈ (run n).2.1

/-- ② istnieje słowo długości `n` nad {A,B} prowadzące z (0,0) do `p`. -/
def ReachableBy : Node → Nat → Prop
  | p, 0 => p = (0, 0)
  | p, n + 1 => ∃ q, ReachableBy q n ∧ (p = childA q ∨ p = childB q)

/-- Najmniejsza liczba kroków. -/
def IsShortest (p : Node) (n : Nat) : Prop :=
  ReachableBy p n ∧ ∀ m, m < n → ¬ ReachableBy p m

/-! ### 🟢 DOWÓD [R6] — przeniesiony z `T1dev.lean` (24.08.2026)

Definicje `ReachableBy`, `IsShortest`, `InGen` w `T1dev.lean` są ZNAK W ZNAK identyczne
z powyższymi (sprawdzone linia po linii: T1dev:5-10,185 vs Sequence:38-47), a `Node`,
`childA`, `childB`, `run`, `stepAll` pochodzą w obu miejscach z tego samego `Tree.lean`.
Nie dało się użyć `T1.gen_eq_dist` jako termu — to inne STAŁE — więc przeniesione jest
CIAŁO dowodu.  Nic w tezie nie zostało zmienione ani osłabione. -/

/-- kopia lokalnego `push` ze `stepAll`, na poziomie top-level -/
def push (st : Std.HashSet Node × List Node) (c : Node) : Std.HashSet Node × List Node :=
  if st.1.contains c then st else (st.1.insert c, c :: st.2)

def G (st : Std.HashSet Node × List Node) (p : Node) : Std.HashSet Node × List Node :=
  push (push st (childA p)) (childB p)

theorem stepAll_eq (seen : Std.HashSet Node) (cur : List Node) :
    stepAll seen cur = cur.foldl G (seen, []) := rfl

theorem push_contains (st : Std.HashSet Node × List Node) (c x : Node) :
    (push st c).1.contains x = true ↔ (st.1.contains x = true ∨ x = c) := by
  unfold push
  by_cases h : st.1.contains c = true
  · simp only [h, if_true]
    constructor
    · exact Or.inl
    · rintro (hx | rfl); exact hx; exact h
  · simp only [Bool.not_eq_true] at h
    simp [h, Std.HashSet.contains_insert, eq_comm (a := x) (b := c), or_comm]

theorem push_mem (st : Std.HashSet Node × List Node) (c x : Node) :
    x ∈ (push st c).2 ↔ (x ∈ st.2 ∨ (¬ (st.1.contains c = true) ∧ x = c)) := by
  unfold push
  by_cases h : st.1.contains c = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h, or_comm]

theorem push_not_contains (st : Std.HashSet Node × List Node) (c x : Node) :
    ¬ ((push st c).1.contains x = true) ↔ (¬ (st.1.contains x = true) ∧ x ≠ c) := by
  rw [push_contains, not_or]

theorem G_contains (st : Std.HashSet Node × List Node) (p x : Node) :
    (G st p).1.contains x = true ↔ (st.1.contains x = true ∨ x = childA p ∨ x = childB p) := by
  unfold G; rw [push_contains, push_contains, or_assoc]

theorem G_mem (st : Std.HashSet Node × List Node) (p x : Node) :
    x ∈ (G st p).2 ↔ (x ∈ st.2 ∨ (¬ (st.1.contains x = true) ∧ (x = childA p ∨ x = childB p))) := by
  unfold G
  rw [push_mem, push_mem, push_not_contains]
  constructor
  · rintro ((hx | ⟨h1, h2⟩) | ⟨⟨h1, _⟩, h2⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨h2 ▸ h1, Or.inl h2⟩
    · exact Or.inr ⟨h2 ▸ h1, Or.inr h2⟩
  · rintro (hx | ⟨h1, (h2 | h2)⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr ⟨h2 ▸ h1, h2⟩)
    · by_cases hEq : childB p = childA p
      · exact Or.inl (Or.inr ⟨hEq ▸ h2 ▸ h1, h2.trans hEq⟩)
      · exact Or.inr ⟨⟨h2 ▸ h1, hEq⟩, h2⟩

def Gen1 (l : List Node) (x : Node) : Prop := ∃ q, q ∈ l ∧ (x = childA q ∨ x = childB q)

theorem Gen1_cons (p : Node) (l : List Node) (x : Node) :
    Gen1 (p :: l) x ↔ ((x = childA p ∨ x = childB p) ∨ Gen1 l x) := by
  simp only [Gen1, List.mem_cons]
  constructor
  · rintro ⟨q, (rfl | hq), hc⟩
    · exact Or.inl hc
    · exact Or.inr ⟨q, hq, hc⟩
  · rintro (hc | ⟨q, hq, hc⟩)
    · exact ⟨p, Or.inl rfl, hc⟩
    · exact ⟨q, Or.inr hq, hc⟩

theorem foldG : ∀ (l : List Node) (s₀ : Std.HashSet Node) (acc₀ : List Node),
    (∀ x, (l.foldl G (s₀, acc₀)).1.contains x = true ↔ (s₀.contains x = true ∨ Gen1 l x))
    ∧ (∀ x, x ∈ (l.foldl G (s₀, acc₀)).2
            ↔ (x ∈ acc₀ ∨ (¬ (s₀.contains x = true) ∧ Gen1 l x))) := by
  intro l
  induction l with
  | nil => intro s₀ acc₀; simp [Gen1]
  | cons p l ih =>
      intro s₀ acc₀
      have hst : ((G (s₀, acc₀) p).1, (G (s₀, acc₀) p).2) = G (s₀, acc₀) p := rfl
      have h := ih (G (s₀, acc₀) p).1 (G (s₀, acc₀) p).2
      rw [hst] at h
      rw [List.foldl_cons]
      refine ⟨fun x => ?_, fun x => ?_⟩
      · rw [h.1 x, G_contains, Gen1_cons]
        dsimp only
        rw [or_assoc]
      · rw [h.2 x, G_mem, G_contains, Gen1_cons]
        dsimp only
        constructor
        · rintro ((hx | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inl hx
          · exact Or.inr ⟨h1, Or.inl h2⟩
          · exact Or.inr ⟨fun hs => h1 (Or.inl hs), Or.inr h2⟩
        · rintro (hx | ⟨h1, (h2 | h2)⟩)
          · exact Or.inl (Or.inl hx)
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
          · by_cases hc : x = childA p ∨ x = childB p
            · exact Or.inl (Or.inr ⟨h1, hc⟩)
            · exact Or.inr ⟨fun hh => hh.elim h1 hc, h2⟩

theorem run_succ_1 (n : Nat) : (run (n+1)).1 = (stepAll (run n).1 (run n).2.1).1 := rfl
theorem run_succ_2 (n : Nat) : (run (n+1)).2.1 = (stepAll (run n).1 (run n).2.1).2 := rfl

theorem exists_le_zero (x : Node) : (∃ m, m ≤ 0 ∧ ReachableBy x m) ↔ ReachableBy x 0 := by
  constructor
  · rintro ⟨m, hm, hr⟩; rw [Nat.le_zero.mp hm] at hr; exact hr
  · intro h; exact ⟨0, Nat.le_refl 0, h⟩

theorem notex_iff (x : Node) (n : Nat) :
    (¬ ∃ m, m ≤ n ∧ ReachableBy x m) ↔ (∀ m, m < n+1 → ¬ ReachableBy x m) := by
  constructor
  · intro h m hm hr; exact h ⟨m, Nat.lt_succ_iff.mp hm, hr⟩
  · rintro h ⟨m, hm, hr⟩; exact h m (Nat.lt_succ_of_le hm) hr

theorem step_key (x : Node) (n : Nat) (hnot : ¬ ∃ m, m ≤ n ∧ ReachableBy x m) :
    ReachableBy x (n+1) ↔ ∃ q, IsShortest q n ∧ (x = childA q ∨ x = childB q) := by
  constructor
  · rintro ⟨q, hq, hc⟩
    refine ⟨q, ⟨hq, ?_⟩, hc⟩
    intro m hm hr
    exact hnot ⟨m+1, Nat.succ_le_of_lt hm, ⟨q, hr, hc⟩⟩
  · rintro ⟨q, ⟨hq, _⟩, hc⟩
    exact ⟨q, hq, hc⟩

/-- Serce [R6]: zbiór `seen` po `n` pokoleniach = węzły osiągalne w ≤ `n` krokach,
    a lista bieżącego pokolenia = węzły o odległości DOKŁADNIE `n`. -/
theorem run_spec : ∀ n : Nat,
    (∀ x, (run n).1.contains x = true ↔ ∃ m, m ≤ n ∧ ReachableBy x m)
    ∧ (∀ x, x ∈ (run n).2.1 ↔ IsShortest x n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · rw [exists_le_zero]
        show ((∅ : Std.HashSet Node).insert (0,0)).contains x = true ↔ x = (0,0)
        rw [Std.HashSet.contains_insert]
        simp [eq_comm (a := x) (b := ((0,0) : Node))]
      · show x ∈ [((0,0) : Node)] ↔ IsShortest x 0
        constructor
        · intro hx
          simp only [List.mem_singleton] at hx
          exact ⟨hx, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
        · intro hx
          simp only [List.mem_singleton]
          exact hx.1
  | succ n ih =>
      have hgen : ∀ x, Gen1 (run n).2.1 x ↔ ∃ q, IsShortest q n ∧ (x = childA q ∨ x = childB q) := by
        intro x
        constructor
        · rintro ⟨q, hq, hc⟩; exact ⟨q, (ih.2 q).mp hq, hc⟩
        · rintro ⟨q, hq, hc⟩; exact ⟨q, (ih.2 q).mpr hq, hc⟩
      have hf := foldG (run n).2.1 (run n).1 []
      refine ⟨fun x => ?_, fun x => ?_⟩
      · rw [run_succ_1, stepAll_eq, hf.1 x, ih.1 x, hgen x]
        constructor
        · rintro (⟨m, hm, hr⟩ | ⟨q, hq, hc⟩)
          · exact ⟨m, Nat.le_succ_of_le hm, hr⟩
          · exact ⟨n+1, Nat.le_refl _, ⟨q, hq.1, hc⟩⟩
        · rintro ⟨m, hm, hr⟩
          by_cases hle : m ≤ n
          · exact Or.inl ⟨m, hle, hr⟩
          · by_cases hex : ∃ m', m' ≤ n ∧ ReachableBy x m'
            · exact Or.inl hex
            · have hm1 : m = n + 1 := by omega
              rw [hm1] at hr
              exact Or.inr ((step_key x n hex).mp hr)
      · rw [run_succ_2, stepAll_eq, hf.2 x, ih.1 x, hgen x]
        simp only [List.not_mem_nil, false_or]
        constructor
        · rintro ⟨hnot, hq⟩
          exact ⟨(step_key x n hnot).mpr hq, (notex_iff x n).mp hnot⟩
        · rintro ⟨hr, hlt⟩
          have hnot : ¬ ∃ m, m ≤ n ∧ ReachableBy x m := (notex_iff x n).mpr hlt
          exact ⟨hnot, (step_key x n hnot).mp hr⟩

theorem gen_eq_dist (p : Node) (n : Nat) : InGen p n ↔ IsShortest p n := (run_spec n).2 p
-- 🟢 ZAMKNIĘTE 24.08.2026 (było: sorry #1 = [R6]).  W komentarzu OEIS ukryte pod słowem „i.e.".
-- CZEGO BRAKUJE: dowodu, że reguła „bierz tylko przy PIERWSZYM wystąpieniu"
-- daje dokładnie odległość w grafie.  Kierunek ⟸ wymaga indukcji po n i tego,
-- że każdy węzeł osiągalny w n krokach ma rodzica osiągalnego w n-1.
-- DLACZEGO NIE DOMKNĄŁEM: to jedyne ogniwo, które wymaga rozumowania o CAŁEJ
-- historii przebiegu (zbiór `seen`), a nie o pojedynczym kroku.

/-! ## 2.  The counterexample, proved rather than merely observed

The OEIS entry comments: "Every ordered pair of nonnegative integers occurs
exactly once in T."  The invariant `j ≤ k` below refutes it in two lines. -/

theorem invariant_j_le_k (p : Node) (n : Nat) (h : ReachableBy p n) : p.1 ≤ p.2 := by
  induction n generalizing p with
  | zero => subst h; exact Nat.le_refl 0
  | succ n ih =>
    obtain ⟨q, hq, hc⟩ := h
    have := ih q hq
    rcases hc with rfl | rfl
    · exact Nat.le_succ_of_le this
    · exact Nat.le_add_left _ _

/-- ⇒ para `(1,0)` nie występuje w drzewie NIGDY.  Zdanie z OEIS jest fałszywe. -/
theorem oeis_claim_is_false : ∀ n, ¬ ReachableBy (1, 0) n := by
  intro n h
  have := invariant_j_le_k (1, 0) n h
  omega


end A252864.Seq
