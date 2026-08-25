/-
  A252864 — `_DYN2_Ksztalt.lean`.  KSZTAŁT TEZY `dynamics` — rozpisanie `foldl`/`M`/`w`
  na pięć jawnych równań.  Definicje `klR`, `MM`, `ww`, `vv` są KOPIAMI 1:1 z
  `Sequence.lean` (`klasaR1` :780-787, `M` :682-690, `w` :697-699, `v` :678-679),
  żeby dało się podstawić przez `rfl`.
  ZERO `native_decide`, ZERO `sorry`.
-/
import «_DYN2_Spine»

namespace A252864.DYN2

open A252864.Tree A252864.Seq A252864.ALemat

/-- Kopia `Seq.klasaR1`. -/
def klR (p : Node) : Fin 5 :=
  let a := p.1
  let x := a + 2 * (p.2 - p.1)
  if (x + 2) * (x + 2) < 5 * (a * a) then 0
  else if (x + 3) * (x + 3) < 5 * ((a+1) * (a+1)) then 1
  else if (x + 1) * (x + 1) < 5 * ((a+1) * (a+1)) then 2
  else if x * x + 1 < 5 * ((a+1) * (a+1)) + 2 * x then 3
  else 4

/-- Kopia `Seq.M`. -/
def MM : Fin 5 → Fin 5 → Nat
  | 0, 4 => 1
  | 1, 3 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | _, _ => 0

/-- Kopia `Seq.w`. -/
def ww : Fin 5 → Nat
  | 0 => 7
  | _ => 0

/-- Kopia `Seq.v` z jawnym parametrem klasyfikatora. -/
def vv (kl : Node → Fin 5) (n : Nat) (j : Fin 5) : Nat :=
  ((run n).2.1.filter (fun p => 8 ≤ p.1 && p.1 < p.2 && kl p == j)).length

/-! ## Rozpisanie prawej strony `dynamics` na pięć jawnych równań -/

theorem rhs_0 (kl : Node → Fin 5) (m : Nat) :
    (List.finRange 5).foldl (fun acc k => acc + MM 0 k * vv kl m k) 0 + ww 0
      = vv kl m 4 + 7 := by
  simp [List.finRange, MM, ww]

theorem rhs_1 (kl : Node → Fin 5) (m : Nat) :
    (List.finRange 5).foldl (fun acc k => acc + MM 1 k * vv kl m k) 0 + ww 1
      = vv kl m 3 := by
  simp [List.finRange, MM, ww]

theorem rhs_2 (kl : Node → Fin 5) (m : Nat) :
    (List.finRange 5).foldl (fun acc k => acc + MM 2 k * vv kl m k) 0 + ww 2
      = vv kl m 1 + vv kl m 2 := by
  simp [List.finRange, MM, ww]

theorem rhs_3 (kl : Node → Fin 5) (m : Nat) :
    (List.finRange 5).foldl (fun acc k => acc + MM 3 k * vv kl m k) 0 + ww 3
      = vv kl m 2 := by
  simp [List.finRange, MM, ww]

theorem rhs_4 (kl : Node → Fin 5) (m : Nat) :
    (List.finRange 5).foldl (fun acc k => acc + MM 4 k * vv kl m k) 0 + ww 4
      = vv kl m 3 + vv kl m 4 := by
  simp [List.finRange, MM, ww]

end A252864.DYN2
