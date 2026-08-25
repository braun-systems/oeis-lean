/-
  A252864 — ALematRep.lean.  WARSTWA REPREZENTACJI CYFROWYCH.

  Cel: przełożyć na Lean fundament, na którym stoją OBIE połowy A-lematu:
    · `LEM_A_wstecz.md [W1.1]`  — `ℓ(z) = min { m + Σᵢdᵢ : Σ dᵢφⁱ = z }`
    · `LEM_B_dolne.md  [B4]`    — lemat ruchu cyfrowego

  Bez tej warstwy żaden krok prozy ([W4], [W6], [W7], [W11], [B3.1], [B4]) nie ma
  jak zostać zapisany: to są operacje na REPREZENTACJACH, nie na ścieżkach w drzewie.

  Układ współrzędnych (ustalony 22.08, kontrola ujemna w `ALemat.lean` §8):
      proza `(a,b)`  ↔  węzeł Leana `(j,k) = (a, a+b)`,  czyli `ℓ(a,b) = L a (a+b)`.
-/
import ALematDef

namespace A252864.ALemat

/-! ## 0.  `ell` — `L` w układzie prozy -/

/-- `ell a b = ℓ(a,b)` z prozy: koszt dojścia do `z = aφ + b`. -/
def ell (a b : Nat) : Nat := L a (a+b)

theorem ell_00 : ell 0 0 = 0 := by rw [ell, L]

theorem ell_0b (b : Nat) : ell 0 b = b := by rw [ell, L]; omega

/-- `ℓ(a,0) = a+1` dla `a ≥ 1` — to jest [W11.1]. -/
theorem ell_a0 (a : Nat) (ha : 1 ≤ a) : ell a 0 = a + 1 := by
  cases a with
  | zero => omega
  | succ j =>
    rw [ell, L]
    simp

/-- Rekurencja DWÓCH RODZICÓW ([W2] / [B1]) — przypadek `b ≤ a`, B-rodzic istnieje. -/
theorem ell_rec_two (a b : Nat) (hb : 1 ≤ b) (hba : b ≤ a) :
    ell a b = 1 + min (ell a (b-1)) (ell b (a-b)) := by
  cases a with
  | zero => omega
  | succ j =>
    have h1 : (j+1) < (j+1)+b := by omega
    have h2 : (j+1)+b ≤ 2*(j+1) := by omega
    have hstep := L_step_two j ((j+1)+b) h1 h2
    have he : (j+1)+b-1 = (j+1)+(b-1) := by omega
    have he2 : (j+1)+b-(j+1) = b := by omega
    rw [he, he2] at hstep
    have he3 : b + (j+1-b) = j+1 := by omega
    rw [ell, ell, ell, he3, hstep]

/-- Rekurencja — przypadek `a < b`, B-rodzica NIE MA ([W2.1]). -/
theorem ell_rec_one (a b : Nat) (hb : 1 ≤ b) (hab : a < b) :
    ell a b = 1 + ell a (b-1) := by
  cases a with
  | zero => rw [ell_0b, ell_0b]; omega
  | succ j =>
    have h : 2*(j+1) < (j+1)+b := by omega
    have hstep := L_step_no_B j ((j+1)+b) h
    have he : (j+1)+b-1 = (j+1)+(b-1) := by omega
    rw [he] at hstep
    rw [ell, ell, hstep]

/-! ### Górne oszacowania z pojedynczych ruchów -/

/-- Ruch `A : z ↦ z+1`. -/
theorem ell_A (a b : Nat) : ell a (b+1) ≤ ell a b + 1 := by
  rcases Nat.lt_or_ge a (b+1) with h | h
  · rw [ell_rec_one a (b+1) (by omega) h]; simp; omega
  · rw [ell_rec_two a (b+1) (by omega) h]
    have := Nat.min_le_left (ell a (b+1-1)) (ell (b+1) (a-(b+1)))
    simp at this ⊢
    omega

/-- Ruch `A` iterowany. -/
theorem ell_A_iter (a b d : Nat) : ell a (b+d) ≤ ell a b + d := by
  induction d with
  | zero => simp
  | succ n ih =>
    have h1 : ell a (b+n+1) ≤ ell a (b+n) + 1 := ell_A a (b+n)
    have he : b + (n+1) = (b+n)+1 := by omega
    rw [he]
    omega

/-- Ruch `B : z ↦ zφ`, czyli `(a,b) ↦ (a+b, a)`. -/
theorem ell_B (a b : Nat) : ell (a+b) a ≤ ell a b + 1 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp only [Nat.zero_add]
    rw [ell_0b]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; rw [ell_00]; omega
    · rw [ell_a0 b hb]; omega
  · rw [ell_rec_two (a+b) a (by omega) (by omega)]
    have he : a + b - a = b := by omega
    rw [he]
    have := Nat.min_le_right (ell (a+b) (a-1)) (ell a b)
    omega

/-! ## 1.  REPREZENTACJE CYFROWE

`ds = [d₀, d₁, d₂, …]` (od NAJNIŻSZEJ cyfry).  Wartość `Σ dᵢ φⁱ` zapisana jako
para `(a,b)` znacząca `aφ + b`.  Mnożenie przez `φ`:  `φ(aφ+b) = (a+b)φ + a`. -/

def val : List Nat → Nat × Nat
  | []      => (0, 0)
  | d :: ds => ((val ds).1 + (val ds).2, (val ds).1 + d)

def isZeroL : List Nat → Bool
  | []      => true
  | d :: ds => (d == 0) && isZeroL ds

/-- Stopień `m = max {i : dᵢ > 0}`; dla listy zerowej `0` (konwencja `deg(0,0) := 0`,
    wymagana przez niezależną weryfikację). -/
def deg : List Nat → Nat
  | []      => 0
  | _ :: ds => if isZeroL ds then 0 else 1 + deg ds

/-- Koszt z [W1.1]: `m + Σᵢdᵢ`. -/
def cost (ds : List Nat) : Nat := ds.sum + deg ds

theorem isZeroL_val {ds : List Nat} (h : isZeroL ds = true) : val ds = (0,0) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [isZeroL, Bool.and_eq_true, beq_iff_eq] at h
    have hv := ih h.2
    simp only [val, hv, h.1]

theorem isZeroL_sum {ds : List Nat} (h : isZeroL ds = true) : ds.sum = 0 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [isZeroL, Bool.and_eq_true, beq_iff_eq] at h
    simp [List.sum_cons, ih h.2, h.1]

/-! ### 1a.  `ell ≤ cost` — KAŻDA reprezentacja daje ścieżkę -/

theorem ell_le_cost (ds : List Nat) : ell (val ds).1 (val ds).2 ≤ cost ds := by
  induction ds with
  | nil => simp [val, cost, deg, ell_00]
  | cons d ds ih =>
    by_cases hz : isZeroL ds
    · have hv : val ds = (0,0) := isZeroL_val hz
      have hs : ds.sum = 0 := isZeroL_sum hz
      have hd : deg (d :: ds) = 0 := by simp [deg, hz]
      have hc : cost (d :: ds) = d := by simp [cost, hd, List.sum_cons, hs]
      simp only [val, hv, hc]
      simp only [Nat.zero_add, Nat.add_zero]
      rw [ell_0b]
      omega
    · have hdeg : deg (d :: ds) = 1 + deg ds := by simp [deg, hz]
      have hcost : cost (d :: ds) = d + 1 + cost ds := by
        simp only [cost, hdeg, List.sum_cons]; omega
      -- `val (d::ds) = (A+B, A+d)` gdzie `(A,B) = val ds`
      have step1 : ell ((val ds).1 + (val ds).2) (val ds).1 ≤ ell (val ds).1 (val ds).2 + 1 :=
        ell_B _ _
      have step2 : ell ((val ds).1 + (val ds).2) ((val ds).1 + d)
          ≤ ell ((val ds).1 + (val ds).2) (val ds).1 + d := ell_A_iter _ _ _
      simp only [val]
      omega

/-! ### 1b.  `∃` reprezentacja optymalna — [W1.1] w drugą stronę -/

/-- `bump` = zwiększenie cyfry `d₀` o 1 (ruch `A` na reprezentacji). -/
def bump : List Nat → List Nat
  | []      => [1]
  | d :: ds => (d+1) :: ds

theorem val_bump (ds : List Nat) : val (bump ds) = ((val ds).1, (val ds).2 + 1) := by
  cases ds with
  | nil => simp [bump, val]
  | cons d ds => simp [bump, val]; omega

theorem cost_bump (ds : List Nat) : cost (bump ds) = cost ds + 1 := by
  cases ds with
  | nil => simp [bump, cost, deg, isZeroL]
  | cons d ds => simp [bump, cost, deg]; omega

theorem val_shift (ds : List Nat) : val (0 :: ds) = ((val ds).1 + (val ds).2, (val ds).1) := by
  simp [val]

theorem cost_shift {ds : List Nat} (h : isZeroL ds = false) :
    cost (0 :: ds) = cost ds + 1 := by
  simp [cost, deg, h]; omega

/-- **[W1.1] — kierunek trudny.**  Dla każdego węzła istnieje reprezentacja
    o koszcie DOKŁADNIE `ell`.  (Razem z `ell_le_cost` daje `ℓ = min kosztów`.) -/
theorem exists_rep_aux : ∀ S a b, a + b ≤ S → ∃ ds, val ds = (a,b) ∧ cost ds ≤ ell a b := by
  intro S
  induction S with
  | zero =>
    intro a b h
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    exact ⟨[], by simp [val], by simp [cost, deg, ell_00]⟩
  | succ n ih =>
    intro a b h
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; exact ⟨[], by simp [val], by simp [cost, deg, ell_00]⟩
      · refine ⟨[0, a], ?_, ?_⟩
        · simp [val]
        · have hnz : isZeroL [a] = false := by simp [isZeroL]; omega
          rw [cost_shift hnz, ell_a0 a ha]
          simp [cost, deg, isZeroL]
    · rcases Nat.lt_or_ge a b with hab | hab
      · obtain ⟨ds, hv, hc⟩ := ih a (b-1) (by omega)
        refine ⟨bump ds, ?_, ?_⟩
        · rw [val_bump, hv]; simp; omega
        · rw [cost_bump, ell_rec_one a b hb hab]; omega
      · rw [ell_rec_two a b hb hab]
        rcases Nat.le_total (ell a (b-1)) (ell b (a-b)) with hmin | hmin
        · obtain ⟨ds, hv, hc⟩ := ih a (b-1) (by omega)
          refine ⟨bump ds, ?_, ?_⟩
          · rw [val_bump, hv]; simp; omega
          · rw [cost_bump]
            have hm : min (ell a (b-1)) (ell b (a-b)) = ell a (b-1) := Nat.min_eq_left hmin
            omega
        · obtain ⟨ds, hv, hc⟩ := ih b (a-b) (by omega)
          have hnz : isZeroL ds = false := by
            cases hzz : isZeroL ds with
            | false => rfl
            | true =>
              exfalso
              have hz0 := isZeroL_val hzz
              rw [hv, Prod.mk.injEq] at hz0
              omega
          refine ⟨0 :: ds, ?_, ?_⟩
          · rw [val_shift, hv]; simp; omega
          · rw [cost_shift hnz]
            have hm : min (ell a (b-1)) (ell b (a-b)) = ell b (a-b) := Nat.min_eq_right hmin
            omega

/-- **[W1.1] — kierunek trudny.**  Dla każdego węzła istnieje reprezentacja
    o koszcie nie większym niż `ell`. -/
theorem exists_rep (a b : Nat) : ∃ ds, val ds = (a,b) ∧ cost ds ≤ ell a b :=
  exists_rep_aux (a+b) a b (Nat.le_refl _)

/-- `ℓ` JEST minimum kosztów — obie strony razem. -/
theorem ell_eq_min_cost (a b : Nat) :
    (∃ ds, val ds = (a,b) ∧ cost ds = ell a b) := by
  obtain ⟨ds, hv, hc⟩ := exists_rep a b
  refine ⟨ds, hv, ?_⟩
  have hle := ell_le_cost ds
  rw [hv] at hle
  simp only at hle
  omega


/-! ## 2.  MONETA `v₂ = φ² = (1,1)` — czyli `[W6.3–4]` i `[B3.1]` w JEDNYM kroku

Proza `[W6]` robi to w trzech ruchach (dwie monety `v₁` → zamiana `v₁`→`v₀` → scalenie
`φ⁰+φ¹=φ²`).  Netto na cyfrach: `+2v₁ −v₁ +v₀ −v₀ −v₁ +v₂ = +v₂`.
Dlatego tu jest JEDEN lemat, nie trzy. -/

def addv2 : List Nat → List Nat
  | []             => [0,0,1]
  | [d0]           => [d0,0,1]
  | d0 :: d1 :: ds => d0 :: d1 :: bump ds

theorem isZeroL_bump (ds : List Nat) : isZeroL (bump ds) = false := by
  cases ds with
  | nil => simp [bump, isZeroL]
  | cons d ds => simp [bump, isZeroL]

theorem deg_bump (ds : List Nat) : deg (bump ds) = deg ds := by
  cases ds with
  | nil => simp [bump, deg, isZeroL]
  | cons d ds => simp [bump, deg]

theorem sum_bump (ds : List Nat) : (bump ds).sum = ds.sum + 1 := by
  cases ds with
  | nil => simp [bump]
  | cons d ds => simp [bump]; omega

theorem val_addv2 (ds : List Nat) : val (addv2 ds) = ((val ds).1 + 1, (val ds).2 + 1) := by
  cases ds with
  | nil => simp [addv2, val]
  | cons d0 ds0 =>
    cases ds0 with
    | nil => simp [addv2, val]; omega
    | cons d1 ds =>
      simp only [addv2, val, val_bump]
      simp
      omega

theorem cost_addv2 (ds : List Nat) (h : 2 ≤ deg ds) : cost (addv2 ds) = cost ds + 1 := by
  cases ds with
  | nil => simp [deg] at h
  | cons d0 ds0 =>
    cases ds0 with
    | nil => simp [deg, isZeroL] at h
    | cons d1 ds =>
      -- z `deg ≥ 2` wynika, że ogon `ds` jest niezerowy
      have h1 : isZeroL (d1 :: ds) = false := by
        cases hz : isZeroL (d1 :: ds) with
        | false => rfl
        | true => exfalso; simp [deg, hz] at h
      have h2 : deg (d0 :: d1 :: ds) = 1 + deg (d1 :: ds) := by simp [deg, h1]
      have h3 : isZeroL ds = false := by
        cases hz : isZeroL ds with
        | false => rfl
        | true =>
          exfalso
          have h4 : deg (d1 :: ds) = 0 := by simp [deg, hz]
          omega
      have h4 : deg (d1 :: ds) = 1 + deg ds := by simp [deg, h3]
      have h5 : isZeroL (d1 :: bump ds) = false := by
        simp [isZeroL, isZeroL_bump]
      have h6 : deg (d0 :: d1 :: bump ds) = 1 + (1 + deg ds) := by
        simp [deg, h5, isZeroL_bump, deg_bump]
      simp only [addv2, cost, List.sum_cons, sum_bump, h6, h2, h4]
      omega

/-! ### Kształt reprezentacji o stopniu ≤ 1 — jądro `[W7]` -/

theorem deg_le_one_shape (ds : List Nat) (hd : deg ds ≤ 1) (hf : 1 ≤ (val ds).1) :
    cost ds = (val ds).1 + (val ds).2 + 1 := by
  cases ds with
  | nil => simp [val] at hf
  | cons d0 ds0 =>
    cases ds0 with
    | nil => simp [val] at hf
    | cons d1 ds =>
      have h1 : isZeroL (d1 :: ds) = false := by
        cases hz : isZeroL (d1 :: ds) with
        | false => rfl
        | true =>
          exfalso
          have hz2 := isZeroL_val hz
          have key : (val (d0 :: d1 :: ds)).1 = (val (d1 :: ds)).1 + (val (d1 :: ds)).2 := rfl
          rw [key, hz2] at hf
          simp at hf
      have h2 : deg (d0 :: d1 :: ds) = 1 + deg (d1 :: ds) := by simp [deg, h1]
      have h3 : isZeroL ds = true := by
        cases hz : isZeroL ds with
        | true => rfl
        | false =>
          exfalso
          have h4 : deg (d1 :: ds) = 1 + deg ds := by simp [deg, hz]
          omega
      have hv : val ds = (0,0) := isZeroL_val h3
      have hs : ds.sum = 0 := isZeroL_sum h3
      have h4 : deg (d1 :: ds) = 0 := by simp [deg, h3]
      simp only [cost, val, hv, List.sum_cons, hs, h2, h4]
      simp
      omega

/-- **`[W7]` + `[W6.3–4]` = jeden krok.**  Dla `x,y ≥ 1` dodanie monety `v₂` podnosi
    koszt dokładnie o 1 — bo istnieje optymalna reprezentacja stopnia `≥ 2`. -/
theorem ell_add_phi2 (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    ell (x+1) (y+1) ≤ ell x y + 1 := by
  obtain ⟨ds, hv, hc⟩ := exists_rep x y
  by_cases hd : 2 ≤ deg ds
  · have h1 := ell_le_cost (addv2 ds)
    rw [val_addv2, hv] at h1
    rw [cost_addv2 ds hd] at h1
    simp only at h1
    omega
  · -- stopień ≤ 1  ⟹  `ℓ(x,y) = x+y+1`, a reprezentacja `[y−1, x−1, 1]` ma stopień 2
    have hd1 : deg ds ≤ 1 := by omega
    have hf : 1 ≤ (val ds).1 := by rw [hv]; simpa using hx
    have hshape := deg_le_one_shape ds hd1 hf
    rw [hv] at hshape
    simp only at hshape
    -- kandydat o stopniu 2: `[y−1, x−1, 1]`
    have hve : val [y-1, x-1, 1] = (x, y) := by
      simp [val]; omega
    have hde : deg [y-1, x-1, 1] = 2 := by simp [deg, isZeroL]
    have hce : cost [y-1, x-1, 1] = x + y + 1 := by
      simp [cost, hde]; omega
    have h2 := ell_le_cost (addv2 [y-1, x-1, 1])
    rw [val_addv2, hve] at h2
    rw [cost_addv2 _ (by omega)] at h2
    simp only at h2
    omega

end A252864.ALemat
