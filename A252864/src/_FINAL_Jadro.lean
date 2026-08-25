/-
  A252864 — `_FINAL_Jadro.lean`.  DWA POLA POCZĄTKOWE `Transfer klasaR1`
  POLICZONE PRZEZ **JĄDRO** (`decide`), NIE PRZEZ KOMPILATOR (`native_decide`).

  W repo `Sequence.lean:852,856` domyka je `native_decide`, co wnosi do tezy
  aksjomaty `Seq.transfer_ini_{C,G}_klasaR1._native.native_decide.ax_1_1`
  (rodzina `Lean.ofReduceBool`) — teza ufałaby wtedy KOMPILATOROWI, nie JĄDRU.

  🔑 MECHANIZM: `decide` NIE potrafi zredukować `Std.HashSet` (pada „reduction got
  stuck").  Most listowy `Tree.run_gen_eq n : (run n).2.1 = (runL n).2.1` zamienia
  worek mieszający na czystą listę — ten sam wzorzec, co `Seq.base12` (`Sequence.lean:954`).
  Poziom 10, obie liczby razem: ~13 s reduktora jądra.

  ⚠️ ZDANIA SĄ IDENTYCZNE co do znaku z `Sequence.lean:852,856` — zmienia się
  WYŁĄCZNIE dowód.  `Sequence.lean` pozostaje NIETKNIĘTY.
-/
import Sequence

namespace A252864.Final

open A252864.Tree A252864.Seq

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
/-- `Transfer.ini_C` dla `klasaR1` — 🟢 JĄDRO (`decide`), nie kompilator.
    Liczbowo: `v(10) = (10,5,11,8,8)`, więc `5 + 11 = 8 + 8`. -/
theorem ini_C_jadro : v klasaR1 10 1 + v klasaR1 10 2 = v klasaR1 10 4 + 8 := by
  unfold v
  rw [Tree.run_gen_eq 10]
  decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
/-- `Transfer.ini_G` dla `klasaR1` — 🟢 JĄDRO (`decide`), nie kompilator.
    Liczbowo: `5 + 2·11 = 10 + 8 + 9`. -/
theorem ini_G_jadro :
    v klasaR1 10 1 + 2 * v klasaR1 10 2 = v klasaR1 10 0 + v klasaR1 10 4 + 9 := by
  unfold v
  rw [Tree.run_gen_eq 10]
  decide

end A252864.Final
