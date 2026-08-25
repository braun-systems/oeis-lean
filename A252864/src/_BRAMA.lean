/-
  ══════════════════════════════════════════════════════════════════════════════
  _BRAMA.lean — MOST między ZAMROŻONĄ TEZĄ (`TEZA.lean`) a naszym drzewem dowodu.
  ══════════════════════════════════════════════════════════════════════════════

  `TEZA.lean` jest samowystarczalny: definiuje własny ciąg `TEZA.A` i własne
  zdanie `TEZA.StollConjecture`.  Nasze drzewo dowodu operuje na `A252864.Seq.a`.
  Gdyby nikt tych dwóch rzeczy nie zszył MASZYNOWO, moglibyśmy udowodnić coś
  innego, niż zamroziliśmy — dokładnie ten błąd, przed którym chroni
  `openai/ten-proofs` (porównanie tezy z pliku-wyzwania z tezą z pliku-dowodu,
  u nich 38/38 identycznych znak w znak).

  Ten plik robi to porównanie NIE OKIEM, tylko elaboratorem:
  · `A_eq_a`               — `TEZA.A = Seq.a` jako funkcje (dowód, nie deklaracja)
  · `teza_to_dokladnie_a252864` — zamrożone zdanie ⟺ zdanie o `Seq.a`
  · `teza_z_drzewa`        — TYP tego twierdzenia to STAŁA `TEZA.StollConjecture`.
    Gdyby ktoś zmienił którekolwiek zdanie, ten plik przestałby się elaborować.

  ⚠️ `teza_z_drzewa` będzie miało `sorryAx`, dopóki `Seq.stoll` ma `sorry`.
     To jest cel: brama ma pokazywać PRAWDĘ o stanie drzewa, nie zieloną lampkę.
-/
import TEZA
import Tree
import Sequence
import Final

namespace A252864.BRAMA

/-! ## ① Most: nasz ciąg z drzewa i ciąg z zamrożonej tezy to ten sam ciąg. -/

/-- Listowa rekonstrukcja z `TEZA.lean` jest tym samym obiektem, co `Tree.runL`.
    (Definicje są zapisane niezależnie — tu zszywa je indukcja, nie wiara.) -/
theorem FL_eq : TEZA.FL = Tree.FL := rfl

theorem stepAllL_eq : TEZA.stepAllL = Tree.stepAllL := rfl

theorem runL_eq : ∀ n : Nat, TEZA.runL n = Tree.runL n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show TEZA.runL (k+1) = Tree.runL (k+1)
      simp only [TEZA.runL, Tree.runL, ih, stepAllL_eq]

/-- 🔑 `TEZA.A` (zamrożona teza) = `A252864.Seq.a` (nasze drzewo dowodu). -/
theorem A_eq_a : ∀ n : Nat, TEZA.A n = A252864.Seq.a n := by
  intro n
  show (TEZA.runL n).2.1.length = (Tree.run n).2.1.length
  rw [Tree.run_gen_eq n, runL_eq n]

/-! ## ② Porównanie zdań — maszynowe, nie okiem. -/

/-- Zamrożone zdanie jest DOKŁADNIE zdaniem o naszym `Seq.a`, znak w znak
    co do treści matematycznej.  Elaborator to sprawdza, nie człowiek. -/
theorem teza_to_dokladnie_a252864 :
    TEZA.StollConjecture ↔ (∀ n : Nat, 12 ≤ n → Seq.a n = Seq.a (n - 1) + Seq.a (n - 3)) := by
  unfold TEZA.StollConjecture
  simp only [A_eq_a]

/-! ## ③ WERDYKT: czy zamrożona teza WYNIKA z naszego drzewa.
    Typ poniżej to STAŁA `TEZA.StollConjecture` — nie kopia, nie parafraza. -/

theorem teza_z_drzewa : TEZA.StollConjecture := by
  intro n hn
  rw [A_eq_a, A_eq_a, A_eq_a]
  exact Final.stoll_proved n hn

/-- STARA DROGA — zostaje jako ŚWIADEK, nie jako werdykt.  Idzie przez
    `Seq.stoll`, który nadal ma `sorry` (partycja Markowa, `dynamics`).
    Trzymamy ją, żeby było widać, że brama odróżnia drogę domkniętą od
    niedomkniętej — i że zielony werdykt nie bierze się z usunięcia dowodu. -/
theorem teza_z_drzewa_stara_droga : TEZA.StollConjecture := by
  intro n hn
  rw [A_eq_a, A_eq_a, A_eq_a]
  exact Seq.stoll n hn

/-! ## ④ KONTROLA PUSTKI (anty-`barker_iff`).

    `GF.barker_iff` ma czyste aksjomaty, ale jest kwantyfikowane po DOWOLNYM
    ciągu — jest więc prawdziwe dla ciągu zerowego i o A252864 nie mówi nic.
    Poniżej ta pułapka jest POKAZANA MASZYNOWO, a nie opisana w komentarzu. -/

/-- Sama rekurencja, bez przypięcia do ciągu, jest spełniona przez ciąg ZEROWY.
    Zdanie tej postaci NIE jest twierdzeniem o A252864. -/
theorem zero_seq_satisfies_bare_recurrence :
    ∀ n : Nat, 12 ≤ n →
      (fun _ : Nat => (0 : Nat)) n
        = (fun _ : Nat => (0 : Nat)) (n - 1) + (fun _ : Nat => (0 : Nat)) (n - 3) := by
  intro n _
  rfl

/-- A nasza zamrożona teza ciągu zerowego NIE dopuszcza: `TEZA.A` jest przybite
    do DATA z OEIS (`TEZA.A_matches_OEIS`), a ciąg zerowy tego nie spełnia.
    To jest dosłownie test „podstaw ciąg zerowy" — wykonany, nie opisany. -/
theorem teza_odrzuca_ciag_zerowy :
    (List.range 14).map TEZA.A ≠ (List.range 14).map (fun _ : Nat => (0 : Nat)) := by
  rw [TEZA.A_matches_OEIS]
  decide

/-- I mocniej — kwantyfikacja po dowolnym ciągu daje zdanie FAŁSZYWE,
    więc „za szeroka teza" to nie jest bezpieczne osłabienie, tylko inna teza. -/
theorem generic_version_is_false :
    ¬ (∀ f : Nat → Nat, ∀ n : Nat, 12 ≤ n → f n = f (n - 1) + f (n - 3)) := by
  intro h
  have := h (fun _ => 1) 12 (by omega)
  simp at this

end A252864.BRAMA
