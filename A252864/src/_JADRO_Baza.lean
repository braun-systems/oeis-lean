/-
  A252864 — _JADRO_Baza.lean.  DWA SKONCZONE SPRAWDZENIA PRZENIESIONE DO JADRA.
  Lean 4.34.0-rc2, BEZ Mathlib.  ZERO `native_decide`, ZERO `sorry`.

  PO CO TEN PLIK ISTNIEJE
  `Bfs.base_ok` (baza indukcji, poziomy 10..15) i `Bfs.finB_true` (ograniczenie
  wspolrzednych na poziomach j <= 9) szly przez `native_decide`, czyli przez aksjomat
  kompilatora (`_native.native_decide.ax`, rodzina `Lean.ofReduceBool`).  Recenzent nie
  ma jak sprawdzic tego jadrem — dla publikacji to dyskwalifikuje caly lancuch, bo przez
  `Bfs.cT_nine` aksjomat wchodzi do `Seq.transitional_nine`.
  Tutaj te same dwa fakty liczy REDUKTOR JADRA (`decide`).

  DLACZEGO NIE WYSTARCZYLO PODMIENIC TAKTYKI (zmierzone 24.08.2026)
  Jadro NIE redukuje `Std.HashSet` — reduktor STAJE ("reduction got stuck"), to nie jest
  timeout.  A `run` z `Tree.lean` trzyma widziane wezly wlasnie w `Std.HashSet`.

  DROGA
  `Tree.runL` (replika `run` na zwyklej liscie) + most `Tree.run_gen_eq` juz istnieja,
  ale dedup listowy jest O(n^2): `runL 15` (1089 wezlow) to ZMIERZONE 325 s i 9-12 GB
  jadra, a szesc poziomow naraz ZABIL OOM (>15 GB) po 257 s.  To jest za drogo i za kruche.
  Dlatego tu stoi `runB` — ta sama rekurencja, ale widziane wezly w 32 KUBELKACH
  (klucz `(j+k) % 32`).  Liczba porownan spada 688 265 -> 21 788 (~32x).
  ZMIERZONE: `runB 15` = 18 s, 2,0 GB (wobec 325 s / 9+ GB).

  `runB` jest ZWIAZANE Z `run` DOWODEM (`run_gen_eqB`), nie zalozeniem: indukcja po
  pokoleniach, dokladnie ten sam schemat co `Tree.run_agree`, bez `native_decide`.
-/
import Tree

namespace A252864.Jadro

open A252864.Tree

/-! ## ① Kubelki — struktura, ktora jadro UMIE liczyc -/

abbrev Bk := List (List Node)

/-- Klucz kubelka.  32 kubelki; rozklad zmierzony jako praktycznie rownomierny. -/
def key (p : Node) : Nat := (p.1 + p.2) % 32

def bget : Bk → Nat → List Node
  | [],      _     => []
  | x :: _,  0     => x
  | _ :: t,  (i+1) => bget t i

def bset : Bk → Nat → List Node → Bk
  | [],      _,     _ => []
  | _ :: t,  0,     v => v :: t
  | x :: t,  (i+1), v => x :: bset t i v

def bmem (b : Bk) (p : Node) : Bool := (bget b (key p)).contains p
def bins (b : Bk) (p : Node) : Bk := bset b (key p) (p :: bget b (key p))
def bempty : Bk := List.replicate 32 []

theorem key_lt (p : Node) : key p < 32 := Nat.mod_lt _ (by decide)

theorem bset_length (b : Bk) (i : Nat) (v : List Node) : (bset b i v).length = b.length := by
  induction b generalizing i with
  | nil => rfl
  | cons x t ih =>
      cases i with
      | zero => rfl
      | succ j => simp [bset, ih]

theorem bget_bset_self (b : Bk) (i : Nat) (v : List Node) (h : i < b.length) :
    bget (bset b i v) i = v := by
  induction b generalizing i with
  | nil => simp at h
  | cons x t ih =>
      cases i with
      | zero => rfl
      | succ j =>
          have hj : j < t.length := by simpa using h
          show bget (bset t j v) j = v
          exact ih j hj

theorem bget_bset_ne (b : Bk) (i j : Nat) (v : List Node) (h : i ≠ j) :
    bget (bset b i v) j = bget b j := by
  induction b generalizing i j with
  | nil => rfl
  | cons x t ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl h
          | succ j' => rfl
      | succ i' =>
          cases j with
          | zero => rfl
          | succ j' =>
              show bget (bset t i' v) j' = bget t j'
              exact ih i' j' (fun hh => h (by omega))

theorem bget_replicate (n i : Nat) : bget (List.replicate n ([] : List Node)) i = [] := by
  induction n generalizing i with
  | zero => rfl
  | succ m ih =>
      cases i with
      | zero => rfl
      | succ j => exact ih j

theorem bmem_bempty (x : Node) : bmem bempty x = false := by
  unfold bmem bempty
  rw [bget_replicate]
  rfl

theorem bempty_length : (32 : Nat) ≤ bempty.length := by
  unfold bempty
  simp

theorem bins_length {b : Bk} (h : 32 ≤ b.length) (c : Node) : 32 ≤ (bins b c).length := by
  unfold bins
  rw [bset_length]
  exact h

/-- 🔑 Kubelki zachowuja sie jak zbior: wstawienie `c` dodaje dokladnie `c`. -/
theorem bmem_bins {b : Bk} (hl : 32 ≤ b.length) (c x : Node) :
    bmem (bins b c) x = ((c == x) || bmem b x) := by
  unfold bmem bins
  by_cases hk : key x = key c
  · rw [hk, bget_bset_self b (key c) _ (Nat.lt_of_lt_of_le (key_lt c) hl),
        List.contains_cons, beq_symm_node c x]
  · rw [bget_bset_ne b (key c) (key x) _ (fun hh => hk hh.symm)]
    have hcx : (c == x) = false := by
      have hne : ¬ c = x := by
        intro hh
        exact hk (by rw [hh])
      simpa using hne
    rw [hcx, Bool.false_or]

/-! ## ② `runB` — `run` z kubelkami zamiast `Std.HashSet` -/

def FB (st : Bk × List Node) (p : Node) : Bk × List Node :=
  let push := fun (st : Bk × List Node) (c : Node) =>
    if bmem st.1 c then st else (bins st.1 c, c :: st.2)
  push (push st (childA p)) (childB p)

def stepAllB (seen : Bk) (cur : List Node) : Bk × List Node := cur.foldl FB (seen, [])

def runB : Nat → Bk × List Node × List Nat
  | 0 => (bins bempty (0, 0), [(0, 0)], [1])
  | n + 1 =>
    let (s, cur, sizes) := runB n
    let (s', nxt) := stepAllB s cur
    (s', nxt, sizes ++ [nxt.length])

def AgB (sh : Std.HashSet Node × List Node) (sb : Bk × List Node) : Prop :=
  32 ≤ sb.1.length ∧ (∀ x, sh.1.contains x = bmem sb.1 x) ∧ sh.2 = sb.2

theorem push_okB {sh : Std.HashSet Node × List Node} {sb : Bk × List Node}
    (h : AgB sh sb) (c : Node) :
    AgB (if sh.1.contains c then sh else (sh.1.insert c, c :: sh.2))
        (if bmem sb.1 c then sb else (bins sb.1 c, c :: sb.2)) := by
  obtain ⟨hl, h1, h2⟩ := h
  by_cases hc : sh.1.contains c = true
  · have hc' : bmem sb.1 c = true := by rw [← h1 c]; exact hc
    simp only [hc, hc', if_pos]
    exact ⟨hl, h1, h2⟩
  · have hc' : ¬ (bmem sb.1 c = true) := by rw [← h1 c]; exact hc
    simp only [hc, hc', Bool.false_eq_true, if_false]
    refine ⟨bins_length hl c, ?_, ?_⟩
    · intro x
      rw [Std.HashSet.contains_insert, h1 x, bmem_bins hl c x]
    · simp [h2]

theorem step_okB {sh : Std.HashSet Node × List Node} {sb : Bk × List Node}
    (h : AgB sh sb) (p : Node) : AgB (FH sh p) (FB sb p) :=
  push_okB (push_okB h (childA p)) (childB p)

theorem foldl_agreeB (cur : List Node) :
    ∀ sh sb, AgB sh sb → AgB (cur.foldl FH sh) (cur.foldl FB sb) := by
  induction cur with
  | nil => intro sh sb h; exact h
  | cons p ps ih =>
      intro sh sb h
      simp only [List.foldl_cons]
      exact ih _ _ (step_okB h p)

theorem stepAll_agreeB {s : Std.HashSet Node} {b : Bk} (hl : 32 ≤ b.length)
    (hc : ∀ x, s.contains x = bmem b x) (cur : List Node) :
    AgB (stepAll s cur) (stepAllB b cur) := by
  rw [stepAll_eq_foldl]
  exact foldl_agreeB cur _ _ ⟨hl, hc, rfl⟩

theorem runB_succ_fst (n : Nat) : (runB (n+1)).1 = (stepAllB (runB n).1 (runB n).2.1).1 := rfl
theorem runB_succ_gen (n : Nat) : (runB (n+1)).2.1 = (stepAllB (runB n).1 (runB n).2.1).2 := rfl

theorem run_agreeB : ∀ n,
    32 ≤ (runB n).1.length ∧
    (∀ x, (run n).1.contains x = bmem (runB n).1 x) ∧
    (run n).2.1 = (runB n).2.1 := by
  intro n
  induction n with
  | zero =>
      refine ⟨bins_length bempty_length (0, 0), ?_, rfl⟩
      intro x
      show ((∅ : Std.HashSet Node).insert (0, 0)).contains x = bmem (bins bempty (0, 0)) x
      rw [Std.HashSet.contains_insert, bmem_bins bempty_length (0, 0) x, bmem_bempty,
          Std.HashSet.contains_empty]
  | succ n ih =>
      obtain ⟨ihl, ih1, ih2⟩ := ih
      have H : AgB (stepAll (run n).1 (run n).2.1) (stepAllB (runB n).1 (runB n).2.1) := by
        rw [← ih2]
        exact stepAll_agreeB ihl ih1 (run n).2.1
      obtain ⟨Hl, H1, H2⟩ := H
      refine ⟨?_, ?_, ?_⟩
      · rw [runB_succ_fst]; exact Hl
      · rw [run_succ_fst, runB_succ_fst]; exact H1
      · rw [run_succ_gen, runB_succ_gen]; exact H2

/-- 🔑 MOST: pokolenie liczone `Std.HashSet`-em i pokolenie liczone KUBELKAMI to ten
    sam obiekt.  Dowod indukcyjny, bez `native_decide`. -/
theorem run_gen_eqB (n : Nat) : (run n).2.1 = (runB n).2.1 := (run_agreeB n).2.2

/-! ## ③ Dwa sprawdzenia — juz w jadrze -/

/-- Kopia `Bfs.transB` (identyczne cialo). -/
def transB (p : Node) : Bool := p.1 ≤ 7 || p.2 == p.1

/-- Kopia `Bfs.Tlist` (identyczne cialo). -/
def Tlist (n : Nat) : List Node :=
  [(0,n), (n-1,n-1), (1,n-1), (2,n), (3,n+1), (4,n+2), (5,n+3), (6,n+4), (7,n+5)]

/-- Kopia `Bfs.baseOK`, ale na podanym pokoleniu. -/
def bchk (n : Nat) (cur : List Node) : Bool :=
  (cur.filter transB).all (fun p => (Tlist n).contains p) &&
  (Tlist n).all (fun p => (cur.filter transB).contains p)

def baseOKB (n : Nat) : Bool := bchk n (runB n).2.1

def finBB : Bool :=
  (List.range 10).all (fun j => ((runB j).2.1.filter transB).all (fun p => p.1 ≤ 8 && p.2 ≤ 14))

set_option maxRecDepth 8000000
set_option maxHeartbeats 40000000

/-- ✅ JADRO (`decide`), NIE `native_decide`.  Poziomy 0..9. -/
theorem finBB_true : finBB = true := by decide

/-- `sweep k n st` sprawdza `k` kolejnych poziomow od `n`, przesuwajac stan.
    JEDEN przebieg zamiast szesciu — inaczej pamiec rosnie szesciokrotnie. -/
def sweep : Nat → Nat → Bk × List Node → Bool
  | 0,   _, _  => true
  | k+1, n, st => bchk n st.2 && sweep k (n+1) (stepAllB st.1 st.2)

theorem state_succB (n : Nat) :
    stepAllB (runB n).1 (runB n).2.1 = ((runB (n+1)).1, (runB (n+1)).2.1) := rfl

theorem sweep_sound : ∀ (k n : Nat), sweep k n ((runB n).1, (runB n).2.1) = true →
    ∀ i, i < k → bchk (n+i) (runB (n+i)).2.1 = true := by
  intro k
  induction k with
  | zero => intro n _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
      intro n h i hi
      rw [sweep] at h
      obtain ⟨h1, h2⟩ := Bool.and_eq_true .. |>.mp h
      cases i with
      | zero => simpa using h1
      | succ j =>
          rw [state_succB] at h2
          have hres := ih (n+1) h2 j (Nat.lt_of_succ_lt_succ hi)
          have he : n + 1 + j = n + (j+1) := by omega
          rw [he] at hres
          exact hres

/-- ✅ JADRO (`decide`), NIE `native_decide`.  Baza indukcji, poziomy 10..15. -/
theorem sweep_true : sweep 6 10 ((runB 10).1, (runB 10).2.1) = true := by decide

theorem base_okB : ∀ n ∈ List.range' 10 6, baseOKB n = true := by
  have H := sweep_sound 6 10 sweep_true
  intro n hn
  have hn' : n ∈ [10, 11, 12, 13, 14, 15] := hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn'
  unfold baseOKB
  rcases hn' with rfl|rfl|rfl|rfl|rfl|rfl
  · exact H 0 (by omega)
  · exact H 1 (by omega)
  · exact H 2 (by omega)
  · exact H 3 (by omega)
  · exact H 4 (by omega)
  · exact H 5 (by omega)

end A252864.Jadro
