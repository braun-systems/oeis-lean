/-
  A252864 — ALematCore.lean.  SZKIELET INDUKCJI WZAJEMNEJ P / C / Q.

  Cel: `core_le_dual`, czyli  `ℓ(p) ≤ ℓ(q)  ⟺  p′ ≥ φ−2`  dla `p=(a,b)`, `q=(b+1,a−b−1)`,
  `8 ≤ a`, `1 ≤ b < a`.  W układzie Leana: `L a (a+b) ≤ L (b+1) a ↔ fphi (b+1) > a`.

  TRZY ZDANIA (nazwy z prozy):
    P(a,b)  — połowa „⟸": `Hi a b → ℓ(a,b) ≤ ℓ(q)`            [LEM_A_wstecz [W2]…[W11]]
    C(c,d)  — C-LEMAT:     `¬Hi c d → ℓ(c−1,d) < ℓ(c,d)`       [LEM_A_wstecz [W5],[W8]]
    Q(a,b)  — połowa „⟹": `¬Hi a b → ℓ(q) < ℓ(a,b)`           [LEM_B_dolne [B5]]

  UFUNDOWANIE (sprawdzone wyczerpująco na `a+b ≤ 2500`, 0 zależności o niemalejącej sumie):
    P(a,b) ← C(b+1, a−b−1) [suma `a`] , C(b, a−b−1) [suma `a−1`]
    C(c,d) ← C(c, d−1)     [suma `c+d−1`] albo P(d, c−d−1) [suma `c−1`]
    Q(a,b) ← Q(a, b−1)     [suma `a+b−1`] , P(b, a−b−1)     [suma `a−1`]
  Każda zależność ma ŚCIŚLE MNIEJSZĄ sumę `a+b`.
-/
import ALematRep
import ALematW4
import ALematProgi

namespace A252864.ALemat

/-! ## `[W6]` — KROK GŁÓWNY POŁOWY „⟸"

Proza robi to w pięciu punktach; po zauważeniu, że `+2v₁ −v₁ +v₀ −v₀ −v₁ +v₂ = +v₂`,
zostają trzy linijki: dwa razy `C`, raz moneta `v₂`, raz ruch `B`.
**Hipoteza `Hi a b` NIE jest tu potrzebna** — służy wyłącznie do wyprowadzenia przesłanek
obu `C` (przez progi `[W2.2]`), więc stoi piętro wyżej. -/
theorem P_step (a b : Nat) (hb : 2 ≤ b) (hab : b + 2 ≤ a)
    (hC1 : ell b (a-b-1) < ell (b+1) (a-b-1))
    (hC2 : ell (b-1) (a-b-1) < ell b (a-b-1)) :
    ell a b ≤ ell (b+1) (a-b-1) := by
  have h1 : ell (b-1+1) (a-b-1+1) ≤ ell (b-1) (a-b-1) + 1 :=
    ell_add_phi2 (b-1) (a-b-1) (by omega) (by omega)
  have e1 : b-1+1 = b := by omega
  have e2 : a-b-1+1 = a-b := by omega
  rw [e1, e2] at h1
  have h2 : ell (b + (a-b)) b ≤ ell b (a-b) + 1 := ell_B b (a-b)
  have e3 : b + (a-b) = a := by omega
  rw [e3] at h2
  omega

/-! ## `[B5]` — KROK GŁÓWNY POŁOWY „⟹"

`p=(a,b)`, `q=(b+1,a−b−1)`, `y=(b,a−b)` = B-rodzic `p`.  Rozbiór po OSTATNIEJ literze
geodezji do `p`; obie gałęzie kończą się tym samym ruchem `[B4]` = `[W4]`. -/

/-- Gałąź „ostatnia litera `B`": `ℓ(p) = ℓ(y)+1`, `y = (b, a−b)`.
    `hchi` = `χ_A(b, a−b−1)`, dostarczane przez `P` na przekątnej `a−1 < a+b`. -/
theorem Q_step_B (a b : Nat) (hb : 1 ≤ b) (hba : b < a)
    (hchi : ell b (a-b) = ell b (a-b-1) + 1)
    (hlast : ell a b = ell b (a-b) + 1) :
    ell (b+1) (a-b-1) < ell a b := by
  have h := B4_move b (a-b) (by omega) (by omega) hchi
  omega

/-- Gałąź „ostatnia litera `A`": `ℓ(p) = ℓ(a,b−1)+1`, schodzi do `Q` na przekątnej `S−1`. -/
theorem Q_step_A (a b : Nat) (hb : 2 ≤ b) (hba : b < a)
    (hchi : ell b (a-b) = ell b (a-b-1) + 1)
    (hlast : ell a b = ell a (b-1) + 1)
    (hQprev : ell b (a-b) < ell a (b-1)) :
    ell (b+1) (a-b-1) < ell a b := by
  have h := B4_move b (a-b) (by omega) (by omega) hchi
  omega

/-! ## ROZBIÓR BELLMANA — „po ostatniej literze optymalnego słowa"

To jest jedyne miejsce, w którym `[W8]` i `[B5]` mówią „weź geodezję i spójrz na ostatnią
literę".  W Leanie nie ma geodezji — jest rekurencja dwóch rodziców, a rozbiór wychodzi
z `min`, bez żadnego mówienia o słowach. -/

theorem bellman_split (c d : Nat) (hd : 1 ≤ d) (hdc : d ≤ c) :
    ell c d = ell c (d-1) + 1 ∨ ell c d = ell d (c-d) + 1 := by
  rw [ell_rec_two c d hd hdc]
  rcases Nat.le_total (ell c (d-1)) (ell d (c-d)) with h | h
  · left; rw [Nat.min_eq_left h]; omega
  · right; rw [Nat.min_eq_right h]; omega

/-- Gdy B-rodzica nie ma (`c < d`), gałąź `A` jest wymuszona. -/
theorem bellman_forced (c d : Nat) (hd : 1 ≤ d) (hcd : c < d) :
    ell c d = ell c (d-1) + 1 := by
  rw [ell_rec_one c d hd hcd]; omega

/-! ## `[W8]` — KROK C -/

theorem C_step_A (c d : Nat) (hd : 1 ≤ d)
    (hlast : ell c d = ell c (d-1) + 1)
    (hCprev : ell (c-1) (d-1) < ell c (d-1)) :
    ell (c-1) d < ell c d := by
  have h : ell (c-1) (d-1+1) ≤ ell (c-1) (d-1) + 1 := ell_A (c-1) (d-1)
  have e : d-1+1 = d := by omega
  rw [e] at h
  omega

theorem C_step_B (c d : Nat) (hd : 1 ≤ d) (hdc : d < c)
    (hlast : ell c d = ell d (c-d) + 1)
    (hP : ell d (c-d) = ell d (c-d-1) + 1) :
    ell (c-1) d < ell c d := by
  -- `(c−1, d) = B(d, c−d−1)`
  have h : ell (d + (c-d-1)) d ≤ ell d (c-d-1) + 1 := ell_B d (c-d-1)
  have e : d + (c-d-1) = c-1 := by omega
  rw [e] at h
  omega

/-- Kolumna `d = 0` — `C` zachodzi bezwarunkowo, elementarnie. -/
theorem C_col0 (c : Nat) (hc : 1 ≤ c) : ell (c-1) 0 < ell c 0 := by
  rcases Nat.eq_or_lt_of_le hc with h | h
  · have e : c = 1 := by omega
    subst e
    simp only [Nat.sub_self]
    rw [ell_00, ell_a0 1 (by omega)]
    omega
  · rw [ell_a0 (c-1) (by omega), ell_a0 c (by omega)]
    omega

end A252864.ALemat
