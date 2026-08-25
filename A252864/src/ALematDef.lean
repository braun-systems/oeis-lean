/-
  A252864 — ALematDef.lean.   DEFINICJE I OGNIWA ①/② A-LEMATU.
  , rozdzielone 24.08.2026 (F1b).  Lean 4.34.0-rc2, BEZ Mathlib.

  🔴 DLACZEGO TEN PLIK ISTNIEJE (24.08.2026):
  `core_le_dual` (koniec `ALemat.lean`) potrzebuje CAŁEJ maszynerii z `ALematRep`,
  `ALematW4`, `ALematProgi`, `ALematBazy`, `ALematCore`, `ALematGlowna` — a te
  importowały `ALemat`.  Cykl importów.  Rozcięcie: wszystko, czego one potrzebują
  (`L`, `fphi`, `ineq_iff_beatty*`, `no_sqrt5`, `L_step_*`), stoi TUTAJ; `ALemat.lean`
  zostaje z samym A-lematem i importuje `ALematGlowna`.
  ⚠️ ŻADNA TEZA NIE ZOSTAŁA ZMIENIONA — to jest przeniesienie 1:1 linii 24–252
  pliku `ALemat.lean` z 22.08 (kopia sprzed cięcia: `git show HEAD:...ALemat.lean`).

  TEZA (ze zlecenia):  dla `a ≥ 8`, `b ≥ 1`
      l(a, b+1) = l(a, b) + 1   ↔   (a+2b+3)² > 5(a+1)²
-/
import Std.Data.HashSet

namespace A252864.ALemat


/-! ## 1.  `l` jako funkcja OBLICZALNA

`Sequence.lean` ma `IsShortest` jako `Prop` — na tym nie da się liczyć.
Tutaj `L j k` jest funkcją, wyprowadzoną z rodziców węzła `(j,k)`:

  · A-rodzic `(j, k−1)` istnieje ⟺ `k−1 ≥ j`
  · B-rodzic `(k−j, j)` istnieje ⟺ `k−j ≤ j`, czyli `k ≤ 2j`
    (inaczej łamałby niezmiennik `j ≤ k`, dowiedziony w `Sequence.invariant_j_le_k`)

Miara terminacji to `k`, NIE `j+k`: oba wywołania mają drugi argument `< k`
(`k−1 < k` oraz `j+1 < k`).  Z miarą `j+k` gałąź B się nie domyka.

⚠️ Poza dziedziną (`k < j`) wartość jest ustalona arbitralnie — dziedziną drzewa
jest `j ≤ k`, co jest niezmiennikiem obu reguł. -/

def L : Nat → Nat → Nat
  | 0,   k => k
  | j+1, k =>
      if _h1 : k ≤ j+1 then j+2
      else if _h2 : k ≤ 2*(j+1) then
        1 + min (L (j+1) (k-1)) (L (k-(j+1)) (j+1))
      else 1 + L (j+1) (k-1)
termination_by j k => k
decreasing_by
  · omega
  · omega
  · omega

/-! ### Kontrola dodatnia przyrządu

Zmierzone w Pythonie (BFS, prostokąt `[0,400]²`): ta rekursja zgadza się z
odległością w drzewie na **80 601 węzłach, 0 niezgodności**.
Tutaj zostaje kilka wartości jako świadek, że `L` nie jest funkcją stałą ani
zdegenerowaną — inaczej wszystko poniżej byłoby prawdziwe o niczym. -/

theorem L_witnesses :
    L 0 5 = 5 ∧ L 8 8 = 9 ∧ L 8 9 = 10 ∧ L 8 12 = 7 ∧ L 8 13 = 7 ∧ L 8 14 = 8 := by
  native_decide

/-- 🔑 Świadek, że `L` NIE jest monotoniczne w `k` — `L 8 9 = 10` a `L 8 12 = 7`.
    Zapisane celowo: kusiło mnie oprzeć dowód na monotoniczności.
    Zmierzone w Pythonie: 121 296 naruszeń monotoniczności na 320 400 par. -/
theorem L_not_monotone : L 8 12 < L 8 9 := by native_decide

/-! ## 2.  ⌊n·φ⌋ BEZ LICZB RZECZYWISTYCH

`⌊n·φ⌋ = ⌊n(1+√5)/2⌋ = (n + ⌊√(5n²)⌋) / 2`, wszystko w `Nat`.
⇒ **`Mathlib.NumberTheory.Rayleigh` i `goldenRatio_irrational` NIE SĄ tu potrzebne.** -/

def fphi (n : Nat) : Nat := (n + Nat.sqrt (5*n*n)) / 2

/-- Kontrola: `fphi` na `n = 1…12` daje dolny ciąg Wythoffa (A000201). -/
theorem fphi_is_wythoff :
    (List.range' 1 12).map fphi = [1,3,4,6,8,9,11,12,14,16,17,19] := by native_decide

/-! ## 3.  OGNIWO ① — UDOWODNIONE W CAŁOŚCI -/

/-- `x² > N ↔ x > ⌊√N⌋` w `Nat`.  Nie potrzeba niekwadratowości `N`. -/
theorem sq_gt_iff (x N : Nat) : x*x > N ↔ x > Nat.sqrt N := by
  constructor
  · intro h
    rcases Nat.lt_or_ge (Nat.sqrt N) x with hlt | hge
    · exact hlt
    · exfalso
      have h2 : x*x ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul hge hge
      have h3 := Nat.sqrt_le N
      omega
  · intro h
    have hs : Nat.sqrt N + 1 ≤ x := h
    have h2 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ x * x := Nat.mul_le_mul hs hs
    have h3 := Nat.lt_succ_sqrt N
    simp only [Nat.succ_eq_add_one] at h3
    omega

/-- **OGNIWO ① (UDOWODNIONE):** prawa strona A-lematu jest DOKŁADNIE warunkiem
    Beatty'ego na dolnym ciągu Wythoffa.  Zmierzone niezależnie w Pythonie:
    0 niezgodności na 360 000 par `(a,b)` z `a,b ≤ 599`. -/
theorem ineq_iff_beatty (a b : Nat) :
    (a + 2*b + 3)^2 > 5*(a+1)^2 ↔ fphi (a+1) ≤ a + b + 1 := by
  have key : (a + 2*b + 3) * (a + 2*b + 3) > 5*(a+1)*(a+1)
      ↔ (a + 2*b + 3) > Nat.sqrt (5*(a+1)*(a+1)) := sq_gt_iff _ _
  have hpow1 : (a + 2*b + 3)^2 = (a + 2*b + 3) * (a + 2*b + 3) := Nat.pow_two _
  have hpow2 : 5*(a+1)^2 = 5*(a+1)*(a+1) := by
    simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc]
  unfold fphi
  rw [hpow1, hpow2, key]
  omega

/-! ### OGNIWO ①b — TRZECIA postać prawej strony, najprostsza z nich

Zmierzone (`a < 900`, `0 ≤ b ≤ a`, 405 450 par, 0 niezgodności) i **udowodnione niżej**:
prawa strona A-lematu jest równoważna `⌊(b+1)φ⌋ > a`, czyli zdaniu o DRUGIM węźle `(b+1, a)`.

Powód jest TOŻSAMOŚCIĄ, nie twierdzeniem o ciągach Beatty'ego:
```
   (a+2b+3)² + (2a+1−b)²  =  5(a+1)² + 5(b+1)²
```
⇒ `(a+2b+3)² > 5(a+1)²  ⟺  (2a+1−b)² < 5(b+1)²`, jedno przez drugie.
🔴 **Dlatego `Mathlib.NumberTheory.Rayleigh` NIE jest potrzebny nawet tutaj** — a przez pół
godziny sądziłem, że jest, bo mój pierwszy rachunek miał DWA błędy o jeden (patrz dziennik §9).
Potrzebna jest tylko niewymierność `√5`, i to w postaci czysto arytmetycznej. -/

theorem no_sqrt5 : ∀ c d : Nat, c*c = 5*(d*d) → d = 0 := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro d h
    rcases Nat.eq_zero_or_pos d with hd | hd
    · exact hd
    · exfalso
      have hm : (c*c) % 5 = 0 := by omega
      have hmm : (c % 5) * (c % 5) % 5 = 0 := by rw [← Nat.mul_mod]; exact hm
      have hlt : c % 5 < 5 := Nat.mod_lt _ (by omega)
      have h5 : c % 5 = 0 := by
        rcases (show c % 5 = 0 ∨ c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 by omega)
          with h0 | h0 | h0 | h0 | h0 <;> rw [h0] at hmm <;> simp_all
      obtain ⟨e, he⟩ : ∃ e, c = 5*e := ⟨c / 5, by omega⟩
      subst he
      have hprod : 5*e*(5*e) = 25*(e*e) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hde : d*d = 5*(e*e) := by omega
      have hdd : d < 5*e := by
        have hpos : 0 < d*d := Nat.mul_pos hd hd
        rcases Nat.lt_or_ge d (5*e) with hh | hh
        · exact hh
        · exfalso
          have hle : (5*e)*(5*e) ≤ d*d := Nat.mul_le_mul hh hh
          omega
      have := ih d hdd e hde
      omega

theorem ineq_iff_beatty_dual (a b : Nat) (hba : b ≤ a) :
    (a + 2*b + 3)^2 > 5*(a+1)^2 ↔ fphi (b+1) > a := by
  obtain ⟨t, rfl⟩ : ∃ t, a = b + t := ⟨a - b, by omega⟩
  have hid : (3*b+t+3)*(3*b+t+3) + (b+2*t+1)*(b+2*t+1)
      = 5*((b+t+1)*(b+t+1)) + 5*((b+1)*(b+1)) := by grind
  have hp1 : (b+t + 2*b + 3)^2 = (3*b+t+3)*(3*b+t+3) := by
    have : b+t+2*b+3 = 3*b+t+3 := by omega
    rw [this, Nat.pow_two]
  have hp2 : 5*(b+t+1)^2 = 5*((b+t+1)*(b+t+1)) := by rw [Nat.pow_two]
  -- prawa strona przez sqrt
  have hs : Nat.sqrt (5*(b+1)*(b+1)) * Nat.sqrt (5*(b+1)*(b+1)) ≤ 5*(b+1)*(b+1) :=
    Nat.sqrt_le _
  have hne : (b+2*t+1)*(b+2*t+1) ≠ 5*((b+1)*(b+1)) := by
    intro hEq
    have := no_sqrt5 _ _ hEq
    omega
  have hkey : (b+2*t+1) ≤ Nat.sqrt (5*(b+1)*(b+1))
      ↔ (b+2*t+1)*(b+2*t+1) ≤ 5*(b+1)*(b+1) := by
    constructor
    · intro h
      have := Nat.mul_le_mul h h
      omega
    · intro h
      rcases Nat.lt_or_ge (Nat.sqrt (5*(b+1)*(b+1))) (b+2*t+1) with hh | hh
      · exfalso
        have h3 := Nat.lt_succ_sqrt (5*(b+1)*(b+1))
        simp only [Nat.succ_eq_add_one] at h3
        have h4 : (Nat.sqrt (5*(b+1)*(b+1)) + 1) * (Nat.sqrt (5*(b+1)*(b+1)) + 1)
            ≤ (b+2*t+1)*(b+2*t+1) := Nat.mul_le_mul hh hh
        omega
      · exact hh
  have hassoc : 5*(b+1)*(b+1) = 5*((b+1)*(b+1)) := by rw [Nat.mul_assoc]
  unfold fphi
  rw [hp1, hp2]
  constructor
  · intro h
    have h2 : (b+2*t+1)*(b+2*t+1) ≤ 5*(b+1)*(b+1) := by omega
    have := hkey.mpr h2
    omega
  · intro h
    have h1 : (b+2*t+1) ≤ Nat.sqrt (5*(b+1)*(b+1)) := by omega
    have h2 := hkey.mp h1
    omega

/-- Prawa strona w trzeciej postaci ⟺ w drugiej.  Wniosek z dwóch powyższych. -/
theorem beatty_forms_agree (a b : Nat) (hba : b ≤ a) :
    fphi (b+1) > a ↔ fphi (a+1) ≤ a + b + 1 := by
  rw [← ineq_iff_beatty_dual a b hba, ineq_iff_beatty]

/-! ## 4.  Rozwinięcia `L` — obie gałęzie, wprost z definicji -/

/-- Gałąź BEZ B-rodzica (`k > 2j`): krok A ZAWSZE zwiększa `L` o 1. -/
theorem L_step_no_B (j k : Nat) (h : 2*(j+1) < k) :
    L (j+1) k = 1 + L (j+1) (k-1) := by
  rw [L]
  have h1 : ¬ (k ≤ j+1) := by omega
  have h2 : ¬ (k ≤ 2*(j+1)) := by omega
  simp [h1, h2]

/-- Gałąź z DWOMA rodzicami (`j < k ≤ 2j`). -/
theorem L_step_two (j k : Nat) (h1 : j+1 < k) (h2 : k ≤ 2*(j+1)) :
    L (j+1) k = 1 + min (L (j+1) (k-1)) (L (k-(j+1)) (j+1)) := by
  rw [L]
  have hn : ¬ (k ≤ j+1) := by omega
  simp [hn, h2]

/-! ## 5.  OGNIWO ② — UDOWODNIONE W CAŁOŚCI: przypadek `b ≥ a`

To jest 37 056 z 76 636 przypadków regionu `R` w prostokącie `[0,400]²` = **48,4%**. -/

/-- Przy `b ≥ a` nierówność zachodzi, bo `a+2b+3 ≥ 3(a+1)` i `9 > 5`. -/
theorem ineq_of_b_ge_a (a b : Nat) (hab : a ≤ b) : (a + 2*b + 3)^2 > 5*(a+1)^2 := by
  have h1 : 3*(a+1) ≤ a + 2*b + 3 := by omega
  have h2 : (3*(a+1)) * (3*(a+1)) ≤ (a + 2*b + 3) * (a + 2*b + 3) := Nat.mul_le_mul h1 h1
  have e : (3*(a+1)) * (3*(a+1)) = 9 * ((a+1) * (a+1)) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hpos : 0 < (a+1) * (a+1) := Nat.mul_pos (by omega) (by omega)
  have hpow1 : (a + 2*b + 3)^2 = (a + 2*b + 3) * (a + 2*b + 3) := Nat.pow_two _
  have hpow2 : 5*(a+1)^2 = 5 * ((a+1)*(a+1)) := by
    simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc]
  omega

/-- **OGNIWO ② (UDOWODNIONE):** przy `b ≥ a` B-rodzic węzła `(a, a+b+1)` NIE ISTNIEJE
    (bo `a+b+1 > 2a`), więc krok A musi zwiększyć `L` o 1 — i nierówność też zachodzi.
    Obie strony równoważności są PRAWDZIWE, więc równoważność zachodzi. -/
theorem A_lemat_case_b_ge_a (a b : Nat) (ha : 8 ≤ a) (hab : a ≤ b) :
    (L a (a+b+1) = L a (a+b) + 1 ↔ (a + 2*b + 3)^2 > 5*(a+1)^2) := by
  cases a with
  | zero => omega
  | succ j =>
    have hk : 2*(j+1) < (j+1)+b+1 := by omega
    have hstep := L_step_no_B j ((j+1)+b+1) hk
    have he : (j+1)+b+1-1 = (j+1)+b := by omega
    rw [he] at hstep
    constructor
    · intro _; exact ineq_of_b_ge_a (j+1) b hab
    · intro _; omega

end A252864.ALemat
