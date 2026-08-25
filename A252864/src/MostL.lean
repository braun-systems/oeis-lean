/-
  A252864 — MostL.lean.  MOST `Seq.IsShortest` ⟷ `ALemat.L`.
  Lean 4.34.0-rc2, BEZ Mathlib.

  PO CO TEN PLIK ISTNIEJE
  `Sequence.lean:160` (`Seq.A_lemma`, luka S4) i `ALemat.lean:279`
  (`ALemat.core_le_dual`, luka S1) to — wbrew inwentarzowi — NIE SĄ dwie
  niezależne luki.  `ALemat.A_lemat` mówi DOKŁADNIE to samo co `Seq.A_lemma`,
  tylko o funkcji OBLICZALNEJ `L` zamiast o relacji `IsShortest`.
  Brakowało jedynie MOSTU między tymi dwoma językami — i tego mostu nie było
  w repo nigdzie (`T2dev` buduje most do `Repr`/`cost`, nie do `L`).

  Ten plik most buduje i domyka W CAŁOŚCI, bez `sorry` i bez `native_decide`:
    · `reach_L`        : `j ≤ k → ReachableBy (j,k) (L j k)`      (górne ograniczenie)
    · `L_le_of_reach`  : `ReachableBy p m → L p.1 p.2 ≤ m`        (dolne ograniczenie)
    · `L_eq_of_shortest`: `IsShortest p n → L p.1 p.2 = n`        (most)
    · `A_lemma`        : teza S4, wyprowadzona z `ALemat.A_lemat`

  ⚠️ UCZCIWIE: `A_lemma` tutaj NIE JEST wolne od `sorryAx` — dziedziczy go po
  `ALemat.core_le_dual` (S1).  Ten plik NIE zamyka S4.  Dowodzi czegoś innego
  i sprawdzalnego maszynowo: **S4 = S1 + most, a most jest zamknięty.**
-/
import SeqBase
import ALemat

namespace A252864.MostL

open A252864.Tree
open A252864.Seq
open A252864.ALemat

/-! ## 1.  Węzeł `(0,k)` jest osiągalny w dokładnie `k` krokach `A`. -/

theorem reach_zero : ∀ k : Nat, ReachableBy (0, k) k
  | 0 => rfl
  | k + 1 => ⟨(0, k), reach_zero k, Or.inl rfl⟩

/-! ## 2.  GÓRNE OGRANICZENIE — `L` jest osiągalne.

Indukcja silna po `k` (ta sama miara terminacji, której używa definicja `L`). -/

theorem reach_L : ∀ (k j : Nat), j ≤ k → ReachableBy (j, k) (L j k) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro j hjk
    cases j with
    | zero =>
      have e : L 0 k = k := by rw [L]
      rw [e]
      exact reach_zero k
    | succ i =>
      by_cases h1 : k ≤ i + 1
      · -- wtedy `k = i+1`, bo `i+1 ≤ k`
        have hk : k = i + 1 := Nat.le_antisymm h1 hjk
        subst hk
        have e : L (i + 1) (i + 1) = i + 2 := by rw [L]; simp
        rw [e]
        refine ⟨(0, i + 1), reach_zero (i + 1), Or.inr ?_⟩
        simp [childB]
      · by_cases h2 : k ≤ 2 * (i + 1)
        · have hs := L_step_two i k (by omega) h2
          rcases Nat.le_total (L (i + 1) (k - 1)) (L (k - (i + 1)) (i + 1)) with hm | hm
          · have hmin : min (L (i + 1) (k - 1)) (L (k - (i + 1)) (i + 1))
                = L (i + 1) (k - 1) := Nat.min_eq_left hm
            rw [hs, hmin]
            have hrec := ih (k - 1) (by omega) (i + 1) (by omega)
            have hcomm : 1 + L (i + 1) (k - 1) = L (i + 1) (k - 1) + 1 := by omega
            rw [hcomm]
            refine ⟨(i + 1, k - 1), hrec, Or.inl ?_⟩
            have : k - 1 + 1 = k := by omega
            simp [childA, this]
          · have hmin : min (L (i + 1) (k - 1)) (L (k - (i + 1)) (i + 1))
                = L (k - (i + 1)) (i + 1) := Nat.min_eq_right hm
            rw [hs, hmin]
            have hrec := ih (i + 1) (by omega) (k - (i + 1)) (by omega)
            have hcomm : 1 + L (k - (i + 1)) (i + 1) = L (k - (i + 1)) (i + 1) + 1 := by omega
            rw [hcomm]
            refine ⟨(k - (i + 1), i + 1), hrec, Or.inr ?_⟩
            have : k - (i + 1) + (i + 1) = k := by omega
            simp [childB, this]
        · have hs := L_step_no_B i k (by omega)
          rw [hs]
          have hrec := ih (k - 1) (by omega) (i + 1) (by omega)
          have hcomm : 1 + L (i + 1) (k - 1) = L (i + 1) (k - 1) + 1 := by omega
          rw [hcomm]
          refine ⟨(i + 1, k - 1), hrec, Or.inl ?_⟩
          have : k - 1 + 1 = k := by omega
          simp [childA, this]

/-! ## 3.  DOLNE OGRANICZENIE — `L` nie przecenia żadnej ścieżki.

Dwa lematy o pojedynczym kroku, potem indukcja po długości ścieżki. -/

/-- Krok `A`: `(j,k) → (j,k+1)`. -/
theorem L_A_le (j k : Nat) (h : j ≤ k) : L j (k + 1) ≤ 1 + L j k := by
  cases j with
  | zero =>
    have e0 : L 0 (k + 1) = k + 1 := by rw [L]
    have e1 : L 0 k = k := by rw [L]
    omega
  | succ i =>
    by_cases h2 : k + 1 ≤ 2 * (i + 1)
    · have hs := L_step_two i (k + 1) (by omega) h2
      have he : k + 1 - 1 = k := by omega
      rw [he] at hs
      have hmin := Nat.min_le_left (L (i + 1) k) (L (k + 1 - (i + 1)) (i + 1))
      omega
    · have hs := L_step_no_B i (k + 1) (by omega)
      have he : k + 1 - 1 = k := by omega
      rw [he] at hs
      omega

/-- Krok `B`: `(j,k) → (k, j+k)`. -/
theorem L_B_le (j k : Nat) (h : j ≤ k) : L k (j + k) ≤ 1 + L j k := by
  cases k with
  | zero =>
    have hj : j = 0 := by omega
    subst hj
    simp only [Nat.zero_add]
    omega
  | succ i =>
    cases j with
    | zero =>
      have e1 : L (i + 1) (0 + (i + 1)) = i + 2 := by
        have hz : 0 + (i + 1) = i + 1 := by omega
        rw [hz, L]; simp
      have e2 : L 0 (i + 1) = i + 1 := by rw [L]
      omega
    | succ jj =>
      have hs := L_step_two i (jj + 1 + (i + 1)) (by omega) (by omega)
      have he : jj + 1 + (i + 1) - (i + 1) = jj + 1 := by omega
      rw [he] at hs
      have hmin := Nat.min_le_right (L (i + 1) (jj + 1 + (i + 1) - 1)) (L (jj + 1) (i + 1))
      omega

theorem L_le_of_reach : ∀ (m : Nat) (p : Node), ReachableBy p m → L p.1 p.2 ≤ m := by
  intro m
  induction m with
  | zero =>
    intro p h
    have hp : p = (0, 0) := h
    subst hp
    have e : L 0 0 = 0 := by rw [L]
    simpa using Nat.le_of_eq e
  | succ m ih =>
    intro p h
    obtain ⟨q, hq, hc⟩ := h
    have hqle : q.1 ≤ q.2 := invariant_j_le_k q m hq
    have hih := ih q hq
    rcases hc with rfl | rfl
    · have hstep := L_A_le q.1 q.2 hqle
      show L q.1 (q.2 + 1) ≤ m + 1
      omega
    · have hstep := L_B_le q.1 q.2 hqle
      show L q.2 (q.1 + q.2) ≤ m + 1
      omega

/-! ## 4.  MOST -/

/-- **MOST.**  Najkrótsza droga w drzewie jest DOKŁADNIE wartością `ALemat.L`. -/
theorem L_eq_of_shortest (p : Node) (n : Nat) (h : IsShortest p n) : L p.1 p.2 = n := by
  obtain ⟨hr, hmin⟩ := h
  have h1 : L p.1 p.2 ≤ n := L_le_of_reach n p hr
  have hle : p.1 ≤ p.2 := invariant_j_le_k p n hr
  rcases Nat.lt_or_ge (L p.1 p.2) n with hlt | hge
  · exact absurd (reach_L p.2 p.1 hle) (hmin _ hlt)
  · omega

/-- I w drugą stronę — most jest równoważnością, nie tylko implikacją. -/
theorem shortest_of_L_eq (p : Node) (n : Nat) (hle : p.1 ≤ p.2) (h : L p.1 p.2 = n) :
    IsShortest p n := by
  subst h
  refine ⟨reach_L p.2 p.1 hle, ?_⟩
  intro m hm hr
  have := L_le_of_reach m p hr
  omega

theorem bridge_L (p : Node) (n : Nat) (hle : p.1 ≤ p.2) :
    IsShortest p n ↔ L p.1 p.2 = n :=
  ⟨L_eq_of_shortest p n, shortest_of_L_eq p n hle⟩

/-! ## 5.  S4 WYPROWADZONE Z `ALemat.A_lemat`

⚠️ To NIE zamyka S4 — `A_lemat` stoi na `core_le_dual` (S1), które ma `sorry`.
Zamyka natomiast pytanie „czy S4 jest luką OSOBNĄ": nie jest. -/

theorem A_lemma (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) (n : Nat)
    (hn : IsShortest (a, a + b) n) (hA : IsShortest (childA (a, a + b)) (n + 1)) :
    (a + 2 * b + 3) ^ 2 > 5 * (a + 1) ^ 2 := by
  have e1 : L a (a + b) = n := L_eq_of_shortest _ _ hn
  have e2 : L a (a + b + 1) = n + 1 := L_eq_of_shortest _ _ hA
  exact (A_lemat a b ha hb).mp (by omega)

end A252864.MostL
