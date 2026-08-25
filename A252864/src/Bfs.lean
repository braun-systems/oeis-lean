/-
  A252864 — Bfs.lean.  SPECYFIKACJA PRZEBIEGU BFS + [M4] (`c_T(n) = 9` dla `n ≥ 10`).
  , węzeł B.  Lean 4.34.0-rc2, BEZ Mathlib.

  🔴 PO CO TEN PLIK ISTNIEJE: `Sequence.lean` mówił o `run` WYŁĄCZNIE przez `native_decide`
  — czyli o skończonych wycinkach.  Tu `run` dostaje specyfikację, którą da się użyć
  w twierdzeniu o WSZYSTKICH `n`.

  Co jest dowiedzione BEZ `native_decide` (z samej definicji `stepAll`/`run`):
    `bfsFold_mem`, `bfsFold_contains`, `bfsFold_inv`  — krok BFS
    `mem_gen_succ`   : p ∈ gen(n+1) ↔ (p ∉ seen n ∧ p jest dzieckiem czegoś z gen n)
    `seen_iff`       : p ∈ seen n  ↔ ∃ j ≤ n, p ∈ gen j
    `gen_nodup`, `gen_le`
    `trans_step`     : krok indukcyjny [M4]
  Dwa `native_decide`, oba SKOŃCZONE i nazwane:
    `base_ok`   — baza indukcji n = 10..15
    `finB_true` — ograniczenie współrzędnych na poziomach j ≤ 9

  🔑 DLACZEGO TO NIE POTRZEBUJE A-LEMATU: region `R = {a ≥ 8, b ≥ 1}` jest ZAMKNIĘTY
  na obu dzieciach, więc część przejściowa ewoluuje AUTONOMICZNIE.  (Zgodne z `MOST.md [M7]`:
  „NIE stoi na: A-LEMACIE".)  Dowód idzie wprost po `run` — bez ℓ, bez [B1], bez [M2.1],
  bez 36 certyfikatów, czyli INNĄ drogą niż proza w `MOST.md`.
-/
import Tree
import «_JADRO_Baza»

namespace A252864.Bfs

open Std
open A252864.Tree

/-! ## Specyfikacja `stepAll` — jedyne miejsce, gdzie dotykamy HashSetu -/

abbrev BfsSt := Std.HashSet Node × List Node

def bfsPush (st : BfsSt) (c : Node) : BfsSt :=
  if st.1.contains c then st else (st.1.insert c, c :: st.2)

def bfsStep (st : BfsSt) (p : Node) : BfsSt := bfsPush (bfsPush st (childA p)) (childB p)

theorem stepAll_eq (seen : Std.HashSet Node) (cur : List Node) :
    stepAll seen cur = cur.foldl bfsStep (seen, []) := rfl

/-- Niezmiennik akumulatora: lista bez powtórzeń i zawarta w zbiorze widzianych. -/
def BfsInv (st : BfsSt) : Prop := st.2.Nodup ∧ ∀ x ∈ st.2, st.1.contains x = true

theorem bfsPush_inv {st : BfsSt} (h : BfsInv st) (c : Node) : BfsInv (bfsPush st c) := by
  unfold bfsPush
  split
  · exact h
  · rename_i hc
    refine ⟨List.nodup_cons.mpr ⟨fun hmem => hc (h.2 c hmem), h.1⟩, ?_⟩
    intro x hx
    rw [Std.HashSet.contains_insert]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · simp [h.2 x hx]

/-- Zbiór widzianych po `bfsPush`. -/
theorem bfsPush_contains (st : BfsSt) (c p : Node) :
    (bfsPush st c).1.contains p = true ↔ (st.1.contains p = true ∨ p = c) := by
  unfold bfsPush
  split
  · rename_i hc
    constructor
    · exact fun h => Or.inl h
    · rintro (h | rfl)
      · exact h
      · exact hc
  · rename_i hc
    rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    exact ⟨fun h => h.elim (fun h => Or.inr h.symm) Or.inl,
           fun h => h.elim Or.inr (fun h => Or.inl h.symm)⟩

/-- Lista wyjściowa po `bfsPush`. -/
theorem bfsPush_mem (st : BfsSt) (c p : Node) :
    p ∈ (bfsPush st c).2 ↔ (p ∈ st.2 ∨ (p = c ∧ st.1.contains p = false)) := by
  unfold bfsPush
  split
  · rename_i hc
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨rfl, h2⟩)
      · exact h
      · simp [hc] at h2
  · rename_i hc
    simp only [List.mem_cons]
    constructor
    · rintro (rfl | h)
      · exact Or.inr ⟨rfl, by simpa using hc⟩
      · exact Or.inl h
    · rintro (h | ⟨rfl, _⟩)
      · exact Or.inr h
      · exact Or.inl rfl



theorem bfsPush_contains_false (st : BfsSt) (c p : Node) :
    (bfsPush st c).1.contains p = false ↔ (st.1.contains p = false ∧ ¬ p = c) := by
  have h := bfsPush_contains st c p
  cases hh : (bfsPush st c).1.contains p <;> cases h2 : st.1.contains p <;>
    by_cases h3 : p = c <;> simp_all

theorem bfsFold_contains (cur : List Node) (st : BfsSt) (p : Node) :
    (cur.foldl bfsStep st).1.contains p = true ↔
      (st.1.contains p = true ∨ ∃ q, q ∈ cur ∧ (p = childA q ∨ p = childB q)) := by
  induction cur generalizing st with
  | nil => simp
  | cons q l ih =>
      rw [List.foldl_cons, ih]
      simp only [bfsStep]
      rw [bfsPush_contains, bfsPush_contains]
      simp only [List.mem_cons]
      constructor
      · rintro (((h | h) | h) | ⟨r, hr, hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨q, Or.inl rfl, Or.inl h⟩
        · exact Or.inr ⟨q, Or.inl rfl, Or.inr h⟩
        · exact Or.inr ⟨r, Or.inr hr, hh⟩
      · rintro (h | ⟨r, (rfl | hr), (hh | hh)⟩)
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inl (Or.inl (Or.inr hh))
        · exact Or.inl (Or.inr hh)
        · exact Or.inr ⟨r, hr, Or.inl hh⟩
        · exact Or.inr ⟨r, hr, Or.inr hh⟩

theorem bfsFold_mem (cur : List Node) (st : BfsSt) (p : Node) :
    p ∈ (cur.foldl bfsStep st).2 ↔
      p ∈ st.2 ∨ (st.1.contains p = false ∧ ∃ q, q ∈ cur ∧ (p = childA q ∨ p = childB q)) := by
  induction cur generalizing st with
  | nil => simp
  | cons q l ih =>
      rw [List.foldl_cons, ih]
      simp only [bfsStep]
      simp only [bfsPush_mem, bfsPush_contains_false, List.mem_cons]
      cases h1 : st.1.contains p <;>
        by_cases h2 : p = childA q <;> by_cases h3 : p = childB q <;>
        simp_all

theorem bfsFold_inv (cur : List Node) {st : BfsSt} (h : BfsInv st) : BfsInv (cur.foldl bfsStep st) := by
  induction cur generalizing st with
  | nil => exact h
  | cons q l ih => exact ih (bfsPush_inv (bfsPush_inv h (childA q)) (childB q))



/-! ## Warstwa `run` -/

theorem run_gen_succ (n : Nat) : (run (n+1)).2.1 = (stepAll (run n).1 (run n).2.1).2 := rfl
theorem run_seen_succ (n : Nat) : (run (n+1)).1 = (stepAll (run n).1 (run n).2.1).1 := rfl

theorem mem_gen_succ (n : Nat) (p : Node) :
    p ∈ (run (n+1)).2.1 ↔
      ((run n).1.contains p = false ∧ ∃ q, q ∈ (run n).2.1 ∧ (p = childA q ∨ p = childB q)) := by
  rw [run_gen_succ, stepAll_eq, bfsFold_mem]
  simp

theorem contains_seen_succ (n : Nat) (p : Node) :
    (run (n+1)).1.contains p = true ↔
      ((run n).1.contains p = true ∨ ∃ q, q ∈ (run n).2.1 ∧ (p = childA q ∨ p = childB q)) := by
  rw [run_seen_succ, stepAll_eq, bfsFold_contains]

theorem gen_nodup : ∀ n, (run n).2.1.Nodup
  | 0 => by decide
  | n+1 => by
      rw [run_gen_succ, stepAll_eq]
      exact (bfsFold_inv _ (⟨List.nodup_nil, by intro x hx; cases hx⟩ : BfsInv ((run n).1, []))).1

theorem seen_iff : ∀ (n : Nat) (p : Node),
    (run n).1.contains p = true ↔ ∃ j, j ≤ n ∧ p ∈ (run j).2.1 := by
  intro n
  induction n with
  | zero =>
      intro p
      constructor
      · intro h
        refine ⟨0, Nat.le_refl 0, ?_⟩
        have : ((∅ : Std.HashSet Node).insert (0,0)).contains p = true := h
        rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false,
            beq_iff_eq] at this
        subst this; decide
      · rintro ⟨j, hj, hmem⟩
        have hj0 : j = 0 := Nat.le_zero.mp hj
        subst hj0
        have : p = (0,0) := by
          have : p ∈ [((0:Nat),(0:Nat))] := hmem
          simpa using this
        subst this
        show ((∅ : Std.HashSet Node).insert (0,0)).contains (0,0) = true
        rw [Std.HashSet.contains_insert]
        simp
  | succ n ih =>
      intro p
      rw [contains_seen_succ]
      constructor
      · rintro (h | h)
        · obtain ⟨j, hj, hm⟩ := (ih p).mp h
          exact ⟨j, Nat.le_succ_of_le hj, hm⟩
        · by_cases hc : (run n).1.contains p = true
          · obtain ⟨j, hj, hm⟩ := (ih p).mp hc
            exact ⟨j, Nat.le_succ_of_le hj, hm⟩
          · refine ⟨n+1, Nat.le_refl _, ?_⟩
            rw [mem_gen_succ]
            exact ⟨by simpa using hc, h⟩
      · rintro ⟨j, hj, hm⟩
        rcases Nat.lt_or_ge j (n+1) with hlt | hge
        · exact Or.inl ((ih p).mpr ⟨j, Nat.le_of_lt_succ hlt, hm⟩)
        · have : j = n+1 := Nat.le_antisymm hj hge
          subst this
          exact Or.inr ((mem_gen_succ n p).mp hm).2

/-- Niezmiennik `j ≤ k` na poziomach (wersja o `run`, nie o `ReachableBy`). -/
theorem gen_le : ∀ (n : Nat), ∀ p ∈ (run n).2.1, p.1 ≤ p.2
  | 0 => by decide
  | n+1 => by
      intro p hp
      obtain ⟨_, q, hq, hc⟩ := (mem_gen_succ n p).mp hp
      have h := gen_le n q hq
      rcases hc with rfl | rfl
      · exact Nat.le_succ_of_le h
      · exact Nat.le_add_left _ _



/-! ## Część przejściowa -/

def transB (p : Node) : Bool := p.1 ≤ 7 || p.2 == p.1

theorem transB_iff (p : Node) : transB p = true ↔ (p.1 ≤ 7 ∨ p.2 = p.1) := by
  simp [transB]

/-- Jawny zbiór przejściowy poziomu `n` ([M4], przepisany do `(j,k)`). -/
def Tlist (n : Nat) : List Node :=
  [(0,n), (n-1,n-1), (1,n-1), (2,n), (3,n+1), (4,n+2), (5,n+3), (6,n+4), (7,n+5)]

def TransSpec (n : Nat) : Prop := ∀ p, (p ∈ (run n).2.1 ∧ transB p = true) ↔ p ∈ Tlist n

def baseOK (n : Nat) : Bool :=
  ((run n).2.1.filter transB).all (fun p => (Tlist n).contains p) &&
  (Tlist n).all (fun p => ((run n).2.1.filter transB).contains p)

/-! ### Mosty do `_JADRO_Baza.lean` (kubelki zamiast `Std.HashSet`) -/

theorem transB_eq : transB = A252864.Jadro.transB := rfl
theorem Tlist_eq : Tlist = A252864.Jadro.Tlist := rfl

theorem baseOK_eq (n : Nat) : baseOK n = A252864.Jadro.baseOKB n := by
  simp only [baseOK, A252864.Jadro.baseOKB, A252864.Jadro.bchk, transB_eq, Tlist_eq,
             A252864.Jadro.run_gen_eqB]

/-- ✅ Baza indukcji, n = 10..15.  POLICZONE PRZEZ JĄDRO (`decide` w `_JADRO_Baza.lean`).
    `native_decide` usunięte 24.08.2026 — dowód nie ufa już kompilatorowi. -/
theorem base_ok : ∀ n ∈ List.range' 10 6, baseOK n = true := by
  intro n hn
  rw [baseOK_eq]
  exact A252864.Jadro.base_okB n hn

theorem spec_of_baseOK {n : Nat} (h : baseOK n = true) : TransSpec n := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true .. |>.mp h
  intro p
  constructor
  · rintro ⟨hp, ht⟩
    have hf : p ∈ (run n).2.1.filter transB := List.mem_filter.mpr ⟨hp, ht⟩
    have := List.all_eq_true.mp h1 p hf
    simpa using this
  · intro hp
    have := List.all_eq_true.mp h2 p hp
    have hf : p ∈ (run n).2.1.filter transB := by simpa using this
    exact ⟨(List.mem_filter.mp hf).1, (List.mem_filter.mp hf).2⟩

def finB : Bool :=
  (List.range 10).all (fun j => ((run j).2.1.filter transB).all (fun p => p.1 ≤ 8 && p.2 ≤ 14))

theorem finB_eq : finB = A252864.Jadro.finBB := by
  simp only [finB, A252864.Jadro.finBB, transB_eq, A252864.Jadro.run_gen_eqB]

/-- ✅ Ograniczenie współrzędnych na `⋃_{j≤9}(gen j ∩ przejściowe)`.
    POLICZONE PRZEZ JĄDRO (`decide` w `_JADRO_Baza.lean`), nie przez kompilator. -/
theorem finB_true : finB = true := by
  rw [finB_eq]
  exact A252864.Jadro.finBB_true

theorem fin_bound (j : Nat) (hj : j < 10) (p : Node) (hm : p ∈ (run j).2.1)
    (ht : transB p = true) : p.1 ≤ 8 ∧ p.2 ≤ 14 := by
  have h := List.all_eq_true.mp finB_true j (by simpa using hj)
  have hf : p ∈ (run j).2.1.filter transB := List.mem_filter.mpr ⟨hm, ht⟩
  have := List.all_eq_true.mp h p hf
  simpa using this



set_option maxHeartbeats 2000000 in
theorem trans_step_fwd {n : Nat} (hn : 15 ≤ n) (IH : ∀ j, 10 ≤ j → j ≤ n → TransSpec j)
    (p : Node) (hp : p ∈ (run (n+1)).2.1) (ht : transB p = true) : p ∈ Tlist (n+1) := by
  obtain ⟨-, q, hq, hc⟩ := (mem_gen_succ n p).mp hp
  have hqle := gen_le n q hq
  have htq : transB q = true := by
    rw [transB_iff]
    rcases hc with rfl | rfl <;> rw [transB_iff] at ht <;>
      simp only [childA, childB] at ht <;> omega
  have hqT : q ∈ Tlist n := (IH n (by omega) (Nat.le_refl n) q).mp ⟨hq, htq⟩
  simp only [Tlist, List.mem_cons, List.not_mem_nil, or_false] at hqT
  rw [transB_iff] at ht
  simp only [Tlist, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  rcases hqT with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hc with rfl|rfl <;>
    (try simp [childA, childB, Prod.mk.injEq] at ht ⊢) <;>
    omega

set_option maxHeartbeats 2000000 in
theorem trans_step_bwd {n : Nat} (hn : 15 ≤ n) (IH : ∀ j, 10 ≤ j → j ≤ n → TransSpec j)
    (p : Node) (hp : p ∈ Tlist (n+1)) : p ∈ (run (n+1)).2.1 ∧ transB p = true := by
  have hTn : ∀ q, q ∈ Tlist n → q ∈ (run n).2.1 :=
    fun q hq => ((IH n (by omega) (Nat.le_refl n) q).mpr hq).1
  simp only [Tlist, List.mem_cons, List.not_mem_nil, or_false] at hp
  have hT : transB p = true := by
    rw [transB_iff]
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact Or.inl (by simp)
    · exact Or.inr rfl
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
  refine ⟨?_, hT⟩
  rw [mem_gen_succ]
  constructor
  · cases hcon : (run n).1.contains p with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨j, hj, hm⟩ := (seen_iff n p).mp hcon
      rcases Nat.lt_or_ge j 10 with hlt | hge
      · have hb := fin_bound j hlt p hm hT
        rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          (try simp at hb) <;> omega
      · have hb := (IH j hge hj p).mp ⟨hm, hT⟩
        simp only [Tlist, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
        rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          (try simp at hb) <;> omega
  · rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(0,n), hTn _ (by simp [Tlist]), Or.inl (by simp [childA])⟩
    · exact ⟨(0,n), hTn _ (by simp [Tlist]), Or.inr (by simp [childB])⟩
    · exact ⟨(1,n-1), hTn _ (by simp [Tlist]), Or.inl (by simp [childA]; try omega)⟩
    · exact ⟨(2,n), hTn _ (by simp [Tlist]), Or.inl (by simp [childA]; try omega)⟩
    · exact ⟨(3,n+1), hTn _ (by simp [Tlist]), Or.inl (by simp [childA]; try omega)⟩
    · exact ⟨(4,n+2), hTn _ (by simp [Tlist]), Or.inl (by simp [childA]; try omega)⟩
    · exact ⟨(5,n+3), hTn _ (by simp [Tlist]), Or.inl (by simp [childA]; try omega)⟩
    · exact ⟨(6,n+4), hTn _ (by simp [Tlist]), Or.inl (by simp [childA]; try omega)⟩
    · exact ⟨(7,n+5), hTn _ (by simp [Tlist]), Or.inl (by simp [childA]; try omega)⟩

theorem step {n : Nat} (hn : 15 ≤ n) (IH : ∀ j, 10 ≤ j → j ≤ n → TransSpec j) : TransSpec (n+1) :=
  fun p => ⟨fun h => trans_step_fwd hn IH p h.1 h.2, fun h => trans_step_bwd hn IH p h⟩



theorem trans_spec_upto : ∀ N n, n ≤ N → 10 ≤ n → TransSpec n := by
  intro N
  induction N with
  | zero => intro n h1 h2; omega
  | succ N ihN =>
      intro n hn h10
      rcases Nat.lt_or_ge n 16 with hlt | hge
      · refine spec_of_baseOK (base_ok n ?_)
        have : n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
        rcases this with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        exact step (by omega) (fun j hj1 hj2 => ihN j (by omega) hj1)

theorem trans_spec (n : Nat) (h : 10 ≤ n) : TransSpec n := trans_spec_upto n n (Nat.le_refl n) h

theorem cT_nine (n : Nat) (hn : 10 ≤ n) :
    ((run n).2.1.filter (fun p => p.1 ≤ 7 || p.2 == p.1)).length = 9 := by
  show ((run n).2.1.filter transB).length = 9
  have h := trans_spec n hn
  have hmem : ∀ p, p ∈ (run n).2.1.filter transB ↔ p ∈ Tlist n := by
    intro p; rw [List.mem_filter]; exact h p
  have hnd1 : ((run n).2.1.filter transB).Nodup :=
    List.Nodup.sublist List.filter_sublist (gen_nodup n)
  have hnd2 : (Tlist n).Nodup := by
    simp [Tlist, Prod.mk.injEq]
    omega
  have h1 := hnd1.length_le_of_subset (fun x hx => (hmem x).mp hx)
  have h2 := hnd2.length_le_of_subset (fun x hx => (hmem x).mpr hx)
  have hlen : (Tlist n).length = 9 := by simp [Tlist]
  omega



end A252864.Bfs
