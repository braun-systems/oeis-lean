/-
  _BRAMA_audyt.lean — WYPIS AKSJOMATÓW dla bramy wierności.
  Nic tu nie dowodzimy; ten plik tylko drukuje, na czym stoi każde twierdzenie.
  Parsuje go `_BRAMA.py` i porównuje z białą listą z `../TEZA.json`.

  Czytaj tak:
    · `[propext, Classical.choice, Quot.sound]` — czysty dowód
    · `Lean.ofReduceBool` DOŁOŻONE  — `native_decide`: ufamy KOMPILATOROWI, nie jądru
    · `sorryAx` DOŁOŻONE            — to NIE jest dowód, to jest luka
-/
import _BRAMA

/-! ### BLOK A — zamrożona teza i most.  Tu `sorryAx` = konjektura NIEDOWIEDZIONA. -/
#print axioms A252864.BRAMA.teza_z_drzewa
#print axioms A252864.BRAMA.teza_to_dokladnie_a252864
#print axioms A252864.BRAMA.A_eq_a
#print axioms A252864.BRAMA.runL_eq

/-! ### BLOK B — kotwice zamrożonej tezy.  Tu `sorryAx` ANI `Lean.ofReduceBool`
     pojawić się NIE MOGĄ: to one odróżniają A252864 od dowolnego ciągu. -/
#print axioms A252864.TEZA.A_matches_OEIS
#print axioms A252864.TEZA.threshold_tight
#print axioms A252864.BRAMA.teza_odrzuca_ciag_zerowy
#print axioms A252864.BRAMA.generic_version_is_false
#print axioms A252864.BRAMA.zero_seq_satisfies_bare_recurrence

/-! ### BLOK C — KONTROLA DODATNIA BRAMY.
     `A252864.Seq.dynamics` MA `sorry`.  Jeżeli brama nie zobaczy tu `sorryAx`,
     to znaczy, że brama jest atrapą i jej zielony werdykt nic nie znaczy. -/
#print axioms A252864.Seq.dynamics

/-! ### BLOK D — teza główna drzewa (to, co brama porównuje z zamrożoną). -/
#print axioms A252864.Seq.stoll
#print axioms A252864.BRAMA.teza_z_drzewa_stara_droga
-- kontrola dodatnia przestawiona 24.08.2026: dynamics zostal zamkniety,
-- wiec jedyna znana luka to five_term (stara droga).
#print axioms A252864.Seq.five_term
