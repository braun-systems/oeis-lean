/-
  A252864 — `_DYN2_R2.lean`.  TWIERDZENIE `[R2]` (`MOST.md:360-376`) W CAŁOŚCI.
  Lean 4.34.0-rc2, BEZ Mathlib.

  ⛔ ZERO `native_decide`, ZERO `sorry`, ZERO `axiom`.

  CO TU JEST
  · `KW.*`      — rozwijanie kwadratów (rdzeń Lean nie ma `ring`; `omega` jest liniowa)
  · `conj_id`   — TOŻSAMOŚĆ SPRZĘŻENIA [D7.2].  `MOST.md:374` nazywa to „rachunkiem
                  sprzężeń w Z[√5]"; w liczbach całkowitych to JEDNA równość:
                     (3a+b+1)² + (a+2b+2)² = 5(a+b+1)² + 5a²
  · `R2_A`      — A-dziecko jest dzieckiem drzewowym ⟺ `(a+2b+3)² > 5(a+1)²`
                  (czyli ⟺ `p ∈ I₃∪I₄∪I₅`).  Stoi na `ALemat.A_lemat` — ZAMKNIĘTYM.
  · `R2_B`      — B-dziecko jest dzieckiem drzewowym ⟺ `(a+2b+2)² ≥ 5a²`
                  (czyli ⟺ `p ∉ I₁`).  Stoi na `A_lemat` W WĘŹLE `y=(a+b,a−1)` + `conj_id`.
  · `mem_gen_iff` — most BFS → arytmetyka: `p ∈ (run n).2.1 ↔ p.1 ≤ p.2 ∧ L p.1 p.2 = n`
-/
import MostL
import «_DYN_Drzewo»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat A252864.MostL A252864.DYN

/-! ## 0.  Kwadraty ręcznie — `ring` nie istnieje bez Mathlib -/
namespace KW

theorem sq3 (p q r : Nat) : (p + q + r) * (p + q + r)
    = p*p + q*q + r*r + 2*(p*q) + 2*(p*r) + 2*(q*r) := by
  have h1 : q * p = p * q := Nat.mul_comm q p
  have h2 : r * p = p * r := Nat.mul_comm r p
  have h3 : r * q = q * r := Nat.mul_comm r q
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem c33 (a : Nat) : (3*a)*(3*a) = 9*(a*a) := by
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
theorem c3b (a b : Nat) : (3*a)*b = 3*(a*b) := by
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
theorem ca2b (a b : Nat) : a*(2*b) = 2*(a*b) := by
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
theorem c2b2b (b : Nat) : (2*b)*(2*b) = 4*(b*b) := by
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- `x^2 = x*x` — rdzeń nie ma `sq`. -/
theorem sqp (x : Nat) : x^2 = x*x := by
  simp [Nat.pow_succ]

end KW

open KW

/-! ## 1.  TOŻSAMOŚĆ SPRZĘŻENIA [D7.2] -/

/-- **[D7.2] w liczbach całkowitych.**  `MOST.md:374` mówi „rachunek sprzężeń";
    to jest ten rachunek, wykonany.  Węzeł `p=(a,b)`, węzeł `y=(a+b, a−1)`:
    `u := a+2b+2` (próg `I₁` dla `p`), `w := 3a+b+1` (próg `I₂` dla `y`). -/
theorem conj_id (a b : Nat) :
    (3*a+b+1)*(3*a+b+1) + (a+2*b+2)*(a+2*b+2)
      = 5*((a+b+1)*(a+b+1)) + 5*(a*a) := by
  rw [sq3 (3*a) b 1, sq3 a (2*b) 2, sq3 a b 1]
  rw [c33 a, c3b a b, ca2b a b, c2b2b b]
  omega

/-- Wniosek: `p ∈ I₁ ⟺ y ∉ I₁∪I₂`.  Dokładnie zdanie `MOST.md:375`. -/
theorem conj_iff (a b : Nat) :
    ((a+2*b+2)*(a+2*b+2) < 5*(a*a)) ↔ (5*((a+b+1)*(a+b+1)) < (3*a+b+1)*(3*a+b+1)) := by
  have h := conj_id a b
  omega

/-! ## 2.  Most BFS → arytmetyka -/

/-- `p` leży w pokoleniu `n` ⟺ `L p.1 p.2 = n` (i `p` jest w dziedzinie drzewa). -/
theorem mem_gen_iff (p : Node) (n : Nat) :
    p ∈ (run n).2.1 ↔ (p.1 ≤ p.2 ∧ L p.1 p.2 = n) := by
  constructor
  · intro h
    have hle : p.1 ≤ p.2 := Bfs.gen_le n p h
    exact ⟨hle, (bridge_L p n hle).mp ((gen_eq_dist p n).mp h)⟩
  · rintro ⟨hle, hL⟩
    exact (gen_eq_dist p n).mpr ((bridge_L p n hle).mpr hL)

/-! ## 3.  `[R2]` — A-CZĘŚĆ (`MOST.md:366-371`) -/

/-- **[R2], A-dziecko.**  Dla `a ≥ 8`, `b ≥ 1`: A-dziecko węzła `(a, a+b)` jest jego
    dzieckiem DRZEWOWYM ⟺ `(a+2b+3)² > 5(a+1)²`, czyli ⟺ węzeł leży w `I₃∪I₄∪I₅`. -/
theorem R2_A (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) :
    IsTChild (a, a + b) (a, a + b + 1) ↔ (a + 2*b + 3)^2 > 5*(a+1)^2 :=
  (tchild_iff_A a (a + b) (by omega)).trans (A_lemat a b ha hb)

/-! ## 4.  `[R2]` — B-CZĘŚĆ (`MOST.md:372-376`) -/

/-- B-dziecko węzła `(a, a+b)` to `(a+b, 2a+b)`. -/
theorem childB_eq (a b : Nat) : childB (a, a + b) = (a + b, 2*a + b) := by
  simp [childB]; omega

/-- Rodzic-drzewowy węzła `(a+b, 2a+b)` przy `a ≥ 8` — rozstrzygnięcie gałęzi `if`. -/
theorem tparent_B_node (a b : Nat) (ha : 8 ≤ a) :
    IsTChild (a, a + b) (a + b, 2*a + b)
      ↔ ¬ (L (a+b) (2*a + b - 1) + 1 = L (a+b) (2*a + b)) := by
  have hk : 2*a + b - 1 = 2*a + b - 1 := rfl
  simp only [IsTChild, tparent]
  by_cases hA : a + b < 2*a + b ∧ L (a+b) (2*a + b - 1) + 1 = L (a+b) (2*a + b)
  · rw [if_pos hA]
    constructor
    · intro h
      -- `(a+b, 2a+b−1) = (a, a+b)` wymusza `b = 0` i `a = 1` — sprzeczne z `a ≥ 8`
      exfalso
      have h1 : a + b = a := congrArg Prod.fst h
      have h2 : 2*a + b - 1 = a + b := congrArg Prod.snd h
      omega
    · intro h; exact absurd hA.2 h
  · have hlt : a + b < 2*a + b := by omega
    rw [if_neg hA]
    constructor
    · intro _ hc; exact hA ⟨hlt, hc⟩
    · intro _
      have e : 2*a + b - (a + b) = a := by omega
      rw [e]

/-- **[R2], B-dziecko.**  Dla `a ≥ 8`, `b ≥ 0`: B-dziecko węzła `(a, a+b)` jest jego
    dzieckiem DRZEWOWYM ⟺ `(a+2b+2)² ≥ 5a²`, czyli ⟺ węzeł NIE leży w `I₁`.
    Dowód: A-LEMAT w węźle `y = (a+b, a−1)` + `conj_id`. -/
theorem R2_B (a b : Nat) (ha : 8 ≤ a) :
    IsTChild (a, a + b) (a + b, 2*a + b) ↔ ¬ ((a+2*b+2)*(a+2*b+2) < 5*(a*a)) := by
  rw [tparent_B_node a b ha]
  -- A-LEMAT w `y = (a+b, a−1)`
  have hy := A_lemat (a + b) (a - 1) (by omega) (by omega)
  have e1 : a + b + (a - 1) + 1 = 2*a + b := by omega
  have e2 : a + b + (a - 1) = 2*a + b - 1 := by omega
  have e3 : (a + b) + 2*(a - 1) + 3 = 3*a + b + 1 := by omega
  rw [e1, e2, e3] at hy
  rw [sqp, sqp] at hy
  have hc := conj_iff a b
  constructor
  · intro h hI1
    exact h ((hy.mpr (by omega)).symm)
  · intro h hstep
    have := hy.mp hstep.symm
    omega
