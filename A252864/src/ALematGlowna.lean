/-
  A252864 — ALematGlowna.lean.  INDUKCJA WZAJEMNA P / C / Q  →  `core_le_dual`.

  Zbiory wyjątków i łatek NIE są przepisane z prozy — są ZMIERZONE dla TEJ struktury
  dowodowej (`scratchpad/sym.py`), stabilnie na trzech oknach `a+b ≤ 60 / 150 / 400`:

    P FAŁSZYWE : (2,1) (3,2) (4,3) (5,4) (7,4)
    C FAŁSZYWE : (4,2) (6,3) (8,4) (10,5) (12,7)
    Q FAŁSZYWE : (4,2)                     ← tego `LEM_B_dolne.md [B6]` nie wymienia
    P ŁATKI    : (10,6) (13,8) (15,9) (16,10) (20,12)
    C ŁATKI    : ZERO   ← bo wszystkie 5 konsumentów `Cexc` przez gałąź `A` ma `Hi`, czyli `C` jest tam PUSTE
    Q ŁATKI    : (6,3) (8,4) (10,5) (12,7)
-/
import ALematRep
import ALematW4
import ALematProgi
import ALematBazy
import ALematCore

namespace A252864.ALemat

/-! ## Zbiory wyjątków -/

def Pexc (a b : Nat) : Prop :=
  (a=2∧b=1) ∨ (a=3∧b=2) ∨ (a=4∧b=3) ∨ (a=5∧b=4) ∨ (a=7∧b=4)
def Cexc (c d : Nat) : Prop :=
  (c=4∧d=2) ∨ (c=6∧d=3) ∨ (c=8∧d=4) ∨ (c=10∧d=5) ∨ (c=12∧d=7)
def Qexc (a b : Nat) : Prop := (a=4∧b=2)

/-! ## Trzy zdania indukcji -/

def PP (a b : Nat) : Prop := Hi a b → ell a b ≤ ell (b+1) (a-b-1)
def CC (c d : Nat) : Prop := ¬ Hi c d → ell (c-1) d < ell c d
def QQ (a b : Nat) : Prop := ¬ Hi a b → ell (b+1) (a-b-1) < ell a b

/-! ## Dodatkowy próg: przekątna `c = d+1` jest zawsze „wysoka"

Potrzebny, żeby w gałęzi `B` kroku `C` zagwarantować `c ≥ d+2`, a stąd `1 ≤ c−d−1`. -/
theorem hi_succ_diag (d : Nat) (hd : 1 ≤ d) : Hi (d+1) d := by
  obtain ⟨t, rfl⟩ : ∃ t, d = t+1 := ⟨d-1, by omega⟩
  simp only [Hi, Nat.pow_two]
  have e1 : (t+1+1+1) * (t+1+1+1) = t*t + 6*t + 9 := by grind
  have e2 : (t+1+1 + 2*(t+1) + 3) * (t+1+1 + 2*(t+1) + 3) = 9*(t*t) + 42*t + 49 := by grind
  omega

/-! ## KROK `C` -/

theorem CC_of_ih (c d : Nat) (hc : 1 ≤ c) (hne : ¬ Cexc c d)
    (ihP : ∀ a' b', a'+b' < c+d → 1 ≤ b' → b' < a' → ¬ Pexc a' b' → PP a' b')
    (ihC : ∀ c' d', c'+d' < c+d → 1 ≤ c' → ¬ Cexc c' d' → CC c' d') : CC c d := by
  intro hnHi
  have hdc : d < c := not_hi_lt c d hnHi
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · subst hd0; exact C_col0 c hc
  · -- `d ≥ 1`, `d < c`
    rcases Nat.le_total (ell d (c-d)) (ell c (d-1)) with hbr | hbr
    · -- 🅑 gałąź `B`:  `ℓ(c,d) = ℓ(d, c−d) + 1`
      have hlast : ell c d = ell d (c-d) + 1 := by
        rw [ell_rec_two c d hd1 (Nat.le_of_lt hdc), Nat.min_eq_right hbr]; omega
      -- `c ≥ d+2`, bo `c = d+1` ma `Hi` (sprzeczność z `¬Hi`)
      have hcd2 : d + 2 ≤ c := by
        rcases Nat.lt_or_ge (d+1) c with h | h
        · omega
        · exfalso
          have : c = d + 1 := by omega
          subst this
          exact hnHi (hi_succ_diag d hd1)
      -- `hP` = `χ_A(d, c−d−1)`
      have hP : ell d (c-d) = ell d (c-d-1) + 1 := by
        rcases Nat.lt_or_ge d (c-d) with hno | hyes
        · -- brak B-rodzica węzła `(d, c−d)` — rekurencja jednoramienna, za darmo
          have := ell_rec_one d (c-d) (by omega) hno
          omega
        · -- B-rodzic istnieje: potrzeba `P(d, c−d−1)`
          have hHiu : Hi d (c-d-1) := not_hi_B_branch c d hdc hnHi
          have hPexc : ¬ Pexc d (c-d-1) := by
            intro hp
            apply hne
            rcases hp with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩ <;>
              simp only [Cexc] <;> omega
          have hPP := ihP d (c-d-1) (by omega) (by omega) (by omega) hPexc
          have hle := hPP hHiu
          -- `q` dla węzła `(d, c−d−1)` to `(c−d, d−(c−d))`
          have e1 : c-d-1+1 = c-d := by omega
          have e2 : d - (c-d-1) - 1 = d - (c-d) := by omega
          rw [e1, e2] at hle
          have hrec := ell_rec_two d (c-d) (by omega) hyes
          rw [Nat.min_eq_left hle] at hrec
          omega
      exact C_step_B c d hd1 hdc hlast hP
    · -- 🅐 gałąź `A`:  `ℓ(c,d) = ℓ(c,d−1) + 1`
      have hlast : ell c d = ell c (d-1) + 1 := by
        rw [ell_rec_two c d hd1 (Nat.le_of_lt hdc), Nat.min_eq_left hbr]; omega
      have hnHi' : ¬ Hi c (d-1) := not_hi_A c d hd1 hnHi
      -- `(c, d−1) ∈ Cexc`  ⟹  `(c,d) ∈ {(4,3),(6,4),(8,5),(10,6),(12,8)}`, a tam `Hi` ZACHODZI
      have hne' : ¬ Cexc c (d-1) := by
        intro hcx
        apply hnHi
        rcases hcx with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
        · obtain ⟨e,f⟩ : c = 4 ∧ d = 3 := by omega
          subst e; subst f; simp only [Hi]; decide
        · obtain ⟨e,f⟩ : c = 6 ∧ d = 4 := by omega
          subst e; subst f; simp only [Hi]; decide
        · obtain ⟨e,f⟩ : c = 8 ∧ d = 5 := by omega
          subst e; subst f; simp only [Hi]; decide
        · obtain ⟨e,f⟩ : c = 10 ∧ d = 6 := by omega
          subst e; subst f; simp only [Hi]; decide
        · obtain ⟨e,f⟩ : c = 12 ∧ d = 8 := by omega
          subst e; subst f; simp only [Hi]; decide
      have hCC := ihC c (d-1) (by omega) hc hne'
      exact C_step_A c d hd1 hlast (hCC hnHi')

/-! ## KROK `P`  —  `[W6]` + rodzina resztkowa `[W11]` + łatki kaskady `[W10]`

`PP a b` = połowa „⟸": `Hi a b → ℓ(a,b) ≤ ℓ(q)`, `q = (b+1, a−b−1)`.

Rozbiór dokładnie taki, jak w `LEM_A_wstecz.md`:
  · `b = 1`   — przesłanka `Hi a 1` jest FAŁSZYWA dla `a ≥ 3` (`not_hi_b1`),
                a `a = 2` to wyjątek `Pexc (2,1)`.  Krok PUSTY, nie „pominięty".
  · `a = b+1` — rodzina `[W11]`: `q = (b+1, 0)`, teza to `ℓ(k,k−1) ≤ ℓ(k,0)`
                (`ell_diag_le_col0`, próg `k ≥ 6`); `b = 2,3,4` to wyjątki `Pexc`.
  · `a ≥ b+2` — `P_step` z DWOMA `C`; przesłanki obu przez `hi_iff_I1` + `I1_not_hi`
                (`[W2.2]`) i `I1_not_hi_pred` (`[W6.2]`).
  · ŁATKI — pięć węzłów, w których któreś `C` trafia w `Cexc`; tam wartości `ell`
    są wypisane w `ALematBazy` (drabina w jądrze, BEZ `native_decide`). -/

theorem PP_of_ih (a b : Nat) (hb : 1 ≤ b) (hba : b < a) (hne : ¬ Pexc a b)
    (ihC : ∀ c' d', c'+d' < a+b → 1 ≤ c' → ¬ Cexc c' d' → CC c' d') : PP a b := by
  intro hHi
  rcases Nat.lt_or_ge b 2 with hb1 | hb2
  · -- `b = 1`
    have hbe : b = 1 := by omega
    subst hbe
    rcases Nat.lt_or_ge a 3 with ha3 | ha3
    · exfalso
      have hae : a = 2 := by omega
      subst hae
      exact hne (Or.inl ⟨rfl, rfl⟩)
    · exact absurd hHi (not_hi_b1 a ha3)
  · rcases Nat.lt_or_ge a (b+2) with hab1 | hab2
    · -- `a = b+1` — rodzina resztkowa `[W11]`
      have hae : a = b + 1 := by omega
      subst hae
      have hb5 : 6 ≤ b + 1 := by
        rcases (show b = 2 ∨ b = 3 ∨ b = 4 ∨ 6 ≤ b + 1 from by omega) with h|h|h|h
        · exact absurd (show Pexc (b+1) b from Or.inr (Or.inl ⟨by omega, h⟩)) hne
        · exact absurd (show Pexc (b+1) b from Or.inr (Or.inr (Or.inl ⟨by omega, h⟩))) hne
        · exact absurd (show Pexc (b+1) b from
            Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h⟩)))) hne
        · exact h
      have hd := ell_diag_le_col0 (b+1) hb5
      have e1 : b + 1 - 1 = b := by omega
      have e2 : b + 1 - b - 1 = 0 := by omega
      rw [e1] at hd
      rw [e2]
      exact hd
    · -- `a ≥ b+2`
      have hI1 : I1 (b+1) (a-b-1) := (hi_iff_I1 a b hba).mp hHi
      by_cases hx1 : Cexc (b+1) (a-b-1)
      · -- pierwsze `C` trafia w `Cexc`
        rcases hx1 with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
        · -- `(a,b) = (6,3)`: przesłanka `Hi 6 3` FAŁSZYWA
          exfalso
          have hbe : b = 3 := by omega
          have hae : a = 6 := by omega
          subst hbe; subst hae
          exact absurd hHi (by simp only [Hi]; decide)
        · -- `(a,b) = (9,5)`: `Hi 9 5` FAŁSZYWA
          exfalso
          have hbe : b = 5 := by omega
          have hae : a = 9 := by omega
          subst hbe; subst hae
          exact absurd hHi (by simp only [Hi]; decide)
        · -- `(a,b) = (12,7)`: `Hi 12 7` FAŁSZYWA
          exfalso
          have hbe : b = 7 := by omega
          have hae : a = 12 := by omega
          subst hbe; subst hae
          exact absurd hHi (by simp only [Hi]; decide)
        · -- `(a,b) = (15,9)`: ŁATKA, wartości z `ALematBazy`
          have hbe : b = 9 := by omega
          have hae : a = 15 := by omega
          subst hbe; subst hae
          have v1 := ell_15_9
          have v2 := ell_10_5
          show ell 15 9 ≤ ell 10 5
          omega
        · -- `(a,b) = (19,11)`: `Hi 19 11` FAŁSZYWA
          exfalso
          have hbe : b = 11 := by omega
          have hae : a = 19 := by omega
          subst hbe; subst hae
          exact absurd hHi (by simp only [Hi]; decide)
      · by_cases hx2 : Cexc b (a-b-1)
        · -- drugie `C` trafia w `Cexc`
          rcases hx2 with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
          · -- `(a,b) = (7,4)` — to jest wyjątek `Pexc`, wykluczony hipotezą
            exfalso
            have hbe : b = 4 := by omega
            have hae : a = 7 := by omega
            subst hbe; subst hae
            exact hne (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
          · -- `(a,b) = (10,6)`: ŁATKA
            have hbe : b = 6 := by omega
            have hae : a = 10 := by omega
            subst hbe; subst hae
            have v1 := ell_10_6
            have v2 := ell_7_3
            show ell 10 6 ≤ ell 7 3
            omega
          · -- `(a,b) = (13,8)`: ŁATKA
            have hbe : b = 8 := by omega
            have hae : a = 13 := by omega
            subst hbe; subst hae
            have v1 := ell_13_8
            have v2 := ell_9_4
            show ell 13 8 ≤ ell 9 4
            omega
          · -- `(a,b) = (16,10)`: ŁATKA
            have hbe : b = 10 := by omega
            have hae : a = 16 := by omega
            subst hbe; subst hae
            have v1 := ell_16_10
            have v2 := ell_11_5
            show ell 16 10 ≤ ell 11 5
            omega
          · -- `(a,b) = (20,12)`: ŁATKA
            have hbe : b = 12 := by omega
            have hae : a = 20 := by omega
            subst hbe; subst hae
            have v1 := ell_20_12
            have v2 := ell_13_7
            show ell 20 12 ≤ ell 13 7
            omega
        · -- KROK OGÓLNY `[W6]`
          have hC1p : ¬ Hi (b+1) (a-b-1) := I1_not_hi _ _ hI1
          have hC2p : ¬ Hi b (a-b-1) := by
            have h := I1_not_hi_pred (b+1) (a-b-1) (by omega) hI1
            have e : b + 1 - 1 = b := by omega
            rw [e] at h
            exact h
          have hC1 := ihC (b+1) (a-b-1) (by omega) (by omega) hx1 hC1p
          have hC2 := ihC b (a-b-1) (by omega) (by omega) hx2 hC2p
          have e : b + 1 - 1 = b := by omega
          rw [e] at hC1
          exact P_step a b hb2 hab2 hC1 hC2

/-! ## KROK `Q`  —  `[B5]` + baza `b = 1` `[B6.1]` + cztery łatki `[B6.2]`

`QQ a b` = połowa „⟹": `¬Hi a b → ℓ(q) < ℓ(a,b)`.

  · `a = b+1` jest NIEOSIĄGALNE (`hi_succ_diag`) ⇒ zawsze `a ≥ b+2`.
  · `b = 1`   — wzory jawne `ℓ(a,1) = a+2` i `ℓ(2,m) = m+2` (`[B6.1]`).
  · ogólnie   — `χ_A(b, a−b−1)` z `P` (albo za darmo, gdy `q` nie ma B-rodzica),
                potem rozbiór Bellmana po ostatniej literze: `Q_step_A` / `Q_step_B`.
  · ŁATKI — cztery węzły, w których `P(b, a−b−1)` trafia w `Pexc`; piąty
    (`(4,2)`) to wyjątek `Qexc`, wykluczony hipotezą. -/

theorem QQ_of_ih (a b : Nat) (hb : 1 ≤ b) (hba : b < a) (hne : ¬ Qexc a b)
    (ihP : ∀ a' b', a'+b' < a+b → 1 ≤ b' → b' < a' → ¬ Pexc a' b' → PP a' b')
    (ihQ : ∀ a' b', a'+b' < a+b → 1 ≤ b' → b' < a' → ¬ Qexc a' b' → QQ a' b') : QQ a b := by
  intro hnHi
  -- `a = b+1` ma `Hi` (przekątna), więc `a ≥ b+2`
  have hab2 : b + 2 ≤ a := by
    rcases Nat.lt_or_ge (b+1) a with h | h
    · omega
    · exfalso
      have he : a = b + 1 := by omega
      subst he
      exact hnHi (hi_succ_diag b hb)
  rcases Nat.lt_or_ge b 2 with hb1 | hb2
  · -- `b = 1` — `[B6.1]`
    have hbe : b = 1 := by omega
    subst hbe
    rcases Nat.lt_or_ge a 4 with ha4 | ha4
    · have hae : a = 3 := by omega
      subst hae
      have v1 := ell_2_1
      have v2 := ell_a1 3 (by omega)
      show ell 2 1 < ell 3 1
      omega
    · have h2 := ell_2m (a-1-1) (by omega)
      have hA := ell_a1 a (by omega)
      show ell 2 (a-1-1) < ell a 1
      omega
  · -- `b ≥ 2`
    by_cases hpx : Pexc b (a-b-1)
    · rcases hpx with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
      · -- `(a,b) = (4,2)` — wyjątek `Qexc`
        exfalso
        have hbe : b = 2 := by omega
        have hae : a = 4 := by omega
        subst hbe; subst hae
        exact hne ⟨rfl, rfl⟩
      · -- `(a,b) = (6,3)`: ŁATKA
        have hbe : b = 3 := by omega
        have hae : a = 6 := by omega
        subst hbe; subst hae
        have v1 := ell_4_2
        have v2 := ell_6_3
        show ell 4 2 < ell 6 3
        omega
      · -- `(a,b) = (8,4)`: ŁATKA
        have hbe : b = 4 := by omega
        have hae : a = 8 := by omega
        subst hbe; subst hae
        have v1 := ell_5_3
        have v2 := ell_8_4
        show ell 5 3 < ell 8 4
        omega
      · -- `(a,b) = (10,5)`: ŁATKA
        have hbe : b = 5 := by omega
        have hae : a = 10 := by omega
        subst hbe; subst hae
        have v1 := ell_6_4
        have v2 := ell_10_5
        show ell 6 4 < ell 10 5
        omega
      · -- `(a,b) = (12,7)`: ŁATKA
        have hbe : b = 7 := by omega
        have hae : a = 12 := by omega
        subst hbe; subst hae
        have v1 := ell_8_4
        have v2 := ell_12_7
        show ell 8 4 < ell 12 7
        omega
    · -- KROK OGÓLNY `[B5]`
      have hchi : ell b (a-b) = ell b (a-b-1) + 1 := by
        rcases Nat.lt_or_ge b (a-b) with hno | hyes
        · -- `q` nie ma B-rodzica — rekurencja jednoramienna, za darmo
          have h := ell_rec_one b (a-b) (by omega) hno
          omega
        · -- B-rodzic istnieje: potrzeba `P(b, a−b−1)` (przekątna `a−1 < a+b`)
          have hHiu : Hi b (a-b-1) := not_hi_B_branch a b hba hnHi
          have hPP := ihP b (a-b-1) (by omega) (by omega) (by omega) hpx
          have hle := hPP hHiu
          have e1 : a - b - 1 + 1 = a - b := by omega
          have e2 : b - (a-b-1) - 1 = b - (a-b) := by omega
          rw [e1, e2] at hle
          have hrec := ell_rec_two b (a-b) (by omega) hyes
          rw [Nat.min_eq_left hle] at hrec
          omega
      rcases bellman_split a b hb (Nat.le_of_lt hba) with hA | hB
      · -- ostatnia litera `A` — schodzi do `Q` na przekątnej `S−1`
        have hnHi' : ¬ Hi a (b-1) := not_hi_A a b hb hnHi
        have hQx : ¬ Qexc a (b-1) := by
          intro hq
          obtain ⟨q1, q2⟩ := hq
          omega
        have hQprev := ihQ a (b-1) (by omega) (by omega) (by omega) hQx hnHi'
        have e1 : b - 1 + 1 = b := by omega
        have e2 : a - (b-1) - 1 = a - b := by omega
        rw [e1, e2] at hQprev
        exact Q_step_A a b hb2 hba hchi hA hQprev
      · -- ostatnia litera `B`
        exact Q_step_B a b hb hba hchi hB

/-! ## INDUKCJA WZAJEMNA — jedno twierdzenie po sumie `a+b`

Ufundowanie (`[W8]`, sprawdzone wyczerpująco na `a+b ≤ 2500`):
  `P(a,b) ← C(b+1,a−b−1)` [suma `a`] , `C(b,a−b−1)` [suma `a−1`]
  `C(c,d) ← C(c,d−1)` [suma `c+d−1`] , `P(d,c−d−1)` [suma `c−1`]
  `Q(a,b) ← Q(a,b−1)` [suma `a+b−1`] , `P(b,a−b−1)` [suma `a−1`]
Każda ŚCIŚLE mniejsza — dlatego wystarczy zwykła indukcja po `S` z tezą „dla sum `≤ S`". -/

theorem PCQ : ∀ S : Nat,
    (∀ a b, a+b ≤ S → 1 ≤ b → b < a → ¬ Pexc a b → PP a b) ∧
    (∀ c d, c+d ≤ S → 1 ≤ c → ¬ Cexc c d → CC c d) ∧
    (∀ a b, a+b ≤ S → 1 ≤ b → b < a → ¬ Qexc a b → QQ a b) := by
  intro S
  induction S with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab hb hba _; exact absurd hb (by omega)
    · intro c d hcd hc _; exact absurd hc (by omega)
    · intro a b hab hb hba _; exact absurd hb (by omega)
  | succ n ih =>
    obtain ⟨ihP, ihC, ihQ⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab hb hba hne
      rcases Nat.lt_or_ge (a+b) (n+1) with h | h
      · exact ihP a b (by omega) hb hba hne
      · exact PP_of_ih a b hb hba hne
          (fun c' d' hlt hc' hne' => ihC c' d' (by omega) hc' hne')
    · intro c d hcd hc hne
      rcases Nat.lt_or_ge (c+d) (n+1) with h | h
      · exact ihC c d (by omega) hc hne
      · exact CC_of_ih c d hc hne
          (fun a' b' hlt hb' hba' hne' => ihP a' b' (by omega) hb' hba' hne')
          (fun c' d' hlt hc' hne' => ihC c' d' (by omega) hc' hne')
    · intro a b hab hb hba hne
      rcases Nat.lt_or_ge (a+b) (n+1) with h | h
      · exact ihQ a b (by omega) hb hba hne
      · exact QQ_of_ih a b hb hba hne
          (fun a' b' hlt hb' hba' hne' => ihP a' b' (by omega) hb' hba' hne')
          (fun a' b' hlt hb' hba' hne' => ihQ a' b' (by omega) hb' hba' hne')

theorem PP_all (a b : Nat) (hb : 1 ≤ b) (hba : b < a) (hne : ¬ Pexc a b) : PP a b :=
  (PCQ (a+b)).1 a b (Nat.le_refl _) hb hba hne

theorem QQ_all (a b : Nat) (hb : 1 ≤ b) (hba : b < a) (hne : ¬ Qexc a b) : QQ a b :=
  (PCQ (a+b)).2.2 a b (Nat.le_refl _) hb hba hne

/-! ## KONKLUZJA — `core_le_dual` w układzie prozy

Wszystkie wyjątki `Pexc` mają `a ≤ 7`, a jedyny `Qexc` ma `a = 4`; próg `a ≥ 8`
z A-lematu jest DOKŁADNIE końcem kaskady `[W10]`, więc przy `8 ≤ a` obie listy
są puste i obie połowy są dostępne bez wyjątku. -/

theorem core_le_dual_ell (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) (hba : b < a) :
    (ell a b ≤ ell (b+1) (a-b-1) ↔ Hi a b) := by
  have hPe : ¬ Pexc a b := by
    intro h
    rcases h with ⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩ <;> omega
  have hQe : ¬ Qexc a b := by
    intro h
    obtain ⟨h1,_⟩ := h
    omega
  constructor
  · intro hle
    rcases Nat.lt_or_ge (5*(a+1)^2) ((a+2*b+3)^2) with hlt | hge
    · exact hlt
    · exfalso
      have hnHi : ¬ Hi a b := Nat.not_lt.mpr hge
      have h := QQ_all a b hb hba hQe hnHi
      omega
  · intro hHi
    exact PP_all a b hb hba hPe hHi

end A252864.ALemat
