/-
  A252864 — FiveTerm.lean.  REDUKCJA `five_term` DO `dynamics`.
  Lean 4.34.0-rc2, BEZ Mathlib.

  PO CO TEN PLIK ISTNIEJE
  -----------------------
  `Sequence.lean` ma dziś DWA `sorry` wyglądające na niezależne dziury:
    · `dynamics`  (S5) — `v(n) = M·v(n−1) + w`, czyli thm:dynamics z pracy,
    · `five_term` (S6) — LEMAT K, „druga droga”, omijająca partycję Markowa.
  NIE SĄ niezależne.  Ten plik dowodzi maszynowo:

        Transfer klasaR1   ⟹   five_term

  Droga jest dokładnie ta z pracy (`A252864_proof.tex`):
        thm:dynamics → lem:conserved + lem:second → thm:r9 → cor:regime → five_term.

  ⚠️ CO TO **NIE** JEST: to NIE usuwa `sorry` z `Seq.five_term`.  Brakującym
  wejściem jest pole `Transfer.dyn`, czyli `Seq.dynamics`, a ono stoi na A-LEMACIE
  (`Seq.A_lemma` → `ALemat.core_le_dual`).  Melduję REDUKCJĘ, nie domknięcie.

  🔴 BRAK CYRKULARNOŚCI — sprawdzalny maszynowo:
  nic poniżej nie używa `five_term`, `pair`, `regime`, `stoll` ani `LemmaK`.
  Wejścia: `Transfer` (hipoteza), `transitional_nine` (dowiedzione),
  `base12` (skończony rachunek n = 12), `run_spec` + `invariant_j_le_k` (dowiedzione).
-/
import Transfer

namespace A252864.Seq

open A252864.Tree

/-! ## 0.  Niezmiennik `j ≤ k` na całym pokoleniu

Potrzebny, bo „przejściowe” (`p.1 ≤ 7 ∨ p.2 = p.1`) i `R` (`8 ≤ p.1 ∧ p.1 < p.2`)
dopełniają się DOPIERO przy `p.1 ≤ p.2`.  Bez tego partycja jest nieprawdziwa. -/

theorem mem_gen_le {n : Nat} {p : Node} (h : p ∈ (run n).2.1) : p.1 ≤ p.2 :=
  invariant_j_le_k p n (((run_spec n).2 p).mp h).1

/-! ## 1.  Kombinatoryka list — liczenie bez `if` w celu -/

private theorem lfc_pos (P : Node → Bool) (q : Node) (K : List Node) (h : P q = true) :
    ((q :: K).filter P).length = (K.filter P).length + 1 := by
  rw [List.filter_cons, if_pos h, List.length_cons]

private theorem lfc_neg (P : Node → Bool) (q : Node) (K : List Node) (h : P q = false) :
    ((q :: K).filter P).length = (K.filter P).length := by
  have hn : ¬ (P q = true) := by rw [h]; exact Bool.false_ne_true
  rw [List.filter_cons, if_neg hn]

private theorem fin5_cases (c : Fin 5) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  have hlt := c.isLt
  have h0 : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨ c.val = 4 := by omega
  rcases h0 with h | h | h | h | h
  · exact Or.inl (Fin.eq_of_val_eq h)
  · exact Or.inr (Or.inl (Fin.eq_of_val_eq h))
  · exact Or.inr (Or.inr (Or.inl (Fin.eq_of_val_eq h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.eq_of_val_eq h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.eq_of_val_eq h))))

/-- Suma liczności pięciu klas wewnątrz dowolnego predykatu `R` = liczność `R`. -/
private theorem sum_classes (kl : Node → Fin 5) (R : Node → Bool) : ∀ L : List Node,
    (L.filter (fun p => R p && kl p == 0)).length
      + (L.filter (fun p => R p && kl p == 1)).length
      + (L.filter (fun p => R p && kl p == 2)).length
      + (L.filter (fun p => R p && kl p == 3)).length
      + (L.filter (fun p => R p && kl p == 4)).length
    = (L.filter R).length := by
  intro L
  induction L with
  | nil => rfl
  | cons q K ih =>
      by_cases hR : R q = true
      · have hb : ∀ j : Fin 5, (R q && (kl q == j)) = (kl q == j) := by
          intro j; rw [hR, Bool.true_and]
        have h5 := fin5_cases (kl q)
        rw [lfc_pos R q K hR]
        rcases h5 with h | h | h | h | h
        · rw [lfc_pos _ q K (by rw [hb 0, h]; decide),
              lfc_neg _ q K (by rw [hb 1, h]; decide),
              lfc_neg _ q K (by rw [hb 2, h]; decide),
              lfc_neg _ q K (by rw [hb 3, h]; decide),
              lfc_neg _ q K (by rw [hb 4, h]; decide)]
          omega
        · rw [lfc_neg _ q K (by rw [hb 0, h]; decide),
              lfc_pos _ q K (by rw [hb 1, h]; decide),
              lfc_neg _ q K (by rw [hb 2, h]; decide),
              lfc_neg _ q K (by rw [hb 3, h]; decide),
              lfc_neg _ q K (by rw [hb 4, h]; decide)]
          omega
        · rw [lfc_neg _ q K (by rw [hb 0, h]; decide),
              lfc_neg _ q K (by rw [hb 1, h]; decide),
              lfc_pos _ q K (by rw [hb 2, h]; decide),
              lfc_neg _ q K (by rw [hb 3, h]; decide),
              lfc_neg _ q K (by rw [hb 4, h]; decide)]
          omega
        · rw [lfc_neg _ q K (by rw [hb 0, h]; decide),
              lfc_neg _ q K (by rw [hb 1, h]; decide),
              lfc_neg _ q K (by rw [hb 2, h]; decide),
              lfc_pos _ q K (by rw [hb 3, h]; decide),
              lfc_neg _ q K (by rw [hb 4, h]; decide)]
          omega
        · rw [lfc_neg _ q K (by rw [hb 0, h]; decide),
              lfc_neg _ q K (by rw [hb 1, h]; decide),
              lfc_neg _ q K (by rw [hb 2, h]; decide),
              lfc_neg _ q K (by rw [hb 3, h]; decide),
              lfc_pos _ q K (by rw [hb 4, h]; decide)]
          omega
      · have hR0 : R q = false := by
          cases hb2 : R q with
          | false => rfl
          | true => exact absurd hb2 hR
        have hb : ∀ j : Fin 5, (R q && (kl q == j)) = false := by
          intro j; rw [hR0, Bool.false_and]
        rw [lfc_neg R q K hR0,
            lfc_neg _ q K (hb 0), lfc_neg _ q K (hb 1), lfc_neg _ q K (hb 2),
            lfc_neg _ q K (hb 3), lfc_neg _ q K (hb 4)]
        exact ih

/-- Część przejściowa i region `R` dopełniają się — na liście z niezmiennikiem `j ≤ k`. -/
private theorem split_TR : ∀ L : List Node, (∀ p ∈ L, p.1 ≤ p.2) →
    (L.filter (fun p => p.1 ≤ 7 || p.2 == p.1)).length
      + (L.filter (fun p => 8 ≤ p.1 && p.1 < p.2)).length = L.length := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons q K ih =>
      intro h
      have hq : q.1 ≤ q.2 := h q (List.mem_cons_self ..)
      have ih' := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
      by_cases h8 : 8 ≤ q.1 ∧ q.1 < q.2
      · have x1 : decide (q.1 ≤ 7) = false := by
          simp only [decide_eq_false_iff_not]; omega
        have x2 : (q.2 == q.1) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have x3 : decide (8 ≤ q.1) = true := by
          simp only [decide_eq_true_eq]; omega
        have x4 : decide (q.1 < q.2) = true := by
          simp only [decide_eq_true_eq]; omega
        have b1 : (decide (q.1 ≤ 7) || (q.2 == q.1)) = false := by rw [x1, x2]; rfl
        have b2 : (decide (8 ≤ q.1) && decide (q.1 < q.2)) = true := by rw [x3, x4]; rfl
        rw [lfc_neg _ q K b1, lfc_pos _ q K b2, List.length_cons]
        omega
      · have hcase : q.1 ≤ 7 ∨ q.2 = q.1 := by
          by_cases hc : 8 ≤ q.1
          · have hlt : ¬ (q.1 < q.2) := fun hx => h8 ⟨hc, hx⟩
            right; omega
          · left; omega
        have b1 : (decide (q.1 ≤ 7) || (q.2 == q.1)) = true := by
          rcases hcase with hc | hc
          · have : decide (q.1 ≤ 7) = true := by simp only [decide_eq_true_eq]; omega
            rw [this]; rfl
          · have : (q.2 == q.1) = true := by simp only [beq_iff_eq]; omega
            rw [this]; exact Bool.or_true _
        have b2 : (decide (8 ≤ q.1) && decide (q.1 < q.2)) = false := by
          by_cases hc : 8 ≤ q.1
          · have hlt : ¬ (q.1 < q.2) := fun hx => h8 ⟨hc, hx⟩
            have : decide (q.1 < q.2) = false := by
              simp only [decide_eq_false_iff_not]; exact hlt
            rw [this]; exact Bool.and_false _
          · have : decide (8 ≤ q.1) = false := by
              simp only [decide_eq_false_iff_not]; exact hc
            rw [this]; rfl
        rw [lfc_pos _ q K b1, lfc_neg _ q K b2, List.length_cons]
        omega

/-! ## 2.  PARTYCJA DLA WSZYSTKICH `n` — bez `native_decide`

W repo stało to tylko jako `partition_complete` przez `native_decide` dla `n ≤ 32`,
a `regime_of_transfer` żąda jej dla WSZYSTKICH `n ≥ 10`.  To była realna dziura
(zamknięta zaufaniem do kompilatora na skończonym wycinku). -/

theorem partition_all (kl : Node → Fin 5) (n : Nat) : a n = cT n + Sv kl n := by
  have hinv : ∀ p ∈ (run n).2.1, p.1 ≤ p.2 := fun p hp => mem_gen_le hp
  have hTR := split_TR (run n).2.1 hinv
  have hC := sum_classes kl (fun p => 8 ≤ p.1 && p.1 < p.2) (run n).2.1
  simp only [a, cT, Sv, v]
  omega

/-! ## 3.  thm:r9 — `R c_R(n) = 9` dla `n ≥ 13`, zapis bez odejmowania w ℕ

Dowód = iteracja dynamiki na trzech poziomach + dwa niezmienniki
(`conserved`, `gval`), dokładnie jak `A252864_proof.tex:1029-1048`. -/

variable {klasa : Node → Fin 5}

theorem r9 (h : Transfer klasa) (n : Nat) (hn : 13 ≤ n) :
    Sv klasa n = Sv klasa (n - 1) + Sv klasa (n - 3) + 9 := by
  have h1 : (10 : Nat) ≤ n := by omega
  have h2 : (10 : Nat) ≤ n - 1 := by omega
  have h3 : (10 : Nat) ≤ n - 2 := by omega
  have h4 : (10 : Nat) ≤ n - 3 := by omega
  have s1 : n - 1 - 1 = n - 2 := by omega
  have s2 : n - 2 - 1 = n - 3 := by omega
  have A0 := d0 h h1; have A1 := d1 h h1; have A2 := d2 h h1
  have A3 := d3 h h1; have A4 := d4 h h1
  have B0 := d0 h h2; have B1 := d1 h h2; have B2 := d2 h h2
  have B3 := d3 h h2; have B4 := d4 h h2
  rw [s1] at B0 B1 B2 B3 B4
  have C0 := d0 h h3; have C1 := d1 h h3; have C2 := d2 h h3
  have C3 := d3 h h3; have C4 := d4 h h3
  rw [s2] at C0 C1 C2 C3 C4
  have hg := gval h h4
  simp only [Sv]
  omega

/-! ## 4.  cor:regime — rekurencja na `a` z dynamiki, BEZ `five_term` -/

theorem regime_of_dynamics (h : Transfer klasa) (n : Nat) (hn : 13 ≤ n) :
    a n = a (n - 1) + a (n - 3) :=
  regime_of_transfer h (fun m hm => transitional_nine m hm)
    (fun m _ => partition_all klasa m) n hn

/-- Pełna rekurencja Stolla z dynamiki: `n ≥ 13` z `regime_of_dynamics`,
    `n = 12` ze skończonego rachunku `base12` (thm:n12 pracy). -/
theorem stoll_of_transfer (h : Transfer klasa) (n : Nat) (hn : 12 ≤ n) :
    a n = a (n - 1) + a (n - 3) := by
  rcases Nat.lt_or_ge n 13 with hlt | hge
  · have h12 : n = 12 := by omega
    subst h12
    exact base12
  · exact regime_of_dynamics h n hge

/-! ## 5.  🔑 TEZA TEGO PLIKU — `five_term` JAKO WNIOSEK, NIE JAKO OGNIWO

`a(n) − 2a(n−1) + a(n−4) + a(n−5) = 0` wynika z rekurencji trójczłonowej
na trzech kolejnych poziomach `n, n−1, n−2`.  Przy `k = 0` poziom `n−2` schodzi
do `12`, którego dynamika NIE obejmuje (`rem:13` pracy: próg 13 jest ostry) —
tam wchodzi skończony rachunek `base12` (thm:n12 pracy). -/

theorem five_term_of_transfer (h : Transfer klasa) (k : Nat) :
    a (k + 14) + a (k + 10) + a (k + 9) = 2 * a (k + 13) := by
  have e14 : a (k + 14) = a (k + 13) + a (k + 11) := by
    have hx := regime_of_dynamics h (k + 14) (by omega)
    have p1 : k + 14 - 1 = k + 13 := by omega
    have p3 : k + 14 - 3 = k + 11 := by omega
    rw [p1, p3] at hx; exact hx
  have e13 : a (k + 13) = a (k + 12) + a (k + 10) := by
    have hx := regime_of_dynamics h (k + 13) (by omega)
    have p1 : k + 13 - 1 = k + 12 := by omega
    have p3 : k + 13 - 3 = k + 10 := by omega
    rw [p1, p3] at hx; exact hx
  have e12 : a (k + 12) = a (k + 11) + a (k + 9) := by
    have hx := stoll_of_transfer h (k + 12) (by omega)
    have p1 : k + 12 - 1 = k + 11 := by omega
    have p3 : k + 12 - 3 = k + 9 := by omega
    rw [p1, p3] at hx; exact hx
  omega

/-! ## 6.  Wersja wyspecjalizowana do `klasaR1` — ta, o którą chodzi w repo.

Dwa z trzech pól struktury `Transfer klasaR1` SĄ w repo domknięte
(`transfer_ini_C_klasaR1`, `transfer_ini_G_klasaR1`).  Brakuje WYŁĄCZNIE `dyn`. -/

theorem five_term_of_dyn
    (hdyn : ∀ n, 10 ≤ n → ∀ j, v klasaR1 n j =
      (List.finRange 5).foldl (fun acc k => acc + M j k * v klasaR1 (n - 1) k) 0 + w j)
    (k : Nat) : a (k + 14) + a (k + 10) + a (k + 9) = 2 * a (k + 13) :=
  five_term_of_transfer
    { dyn := hdyn
      ini_C := transfer_ini_C_klasaR1
      ini_G := transfer_ini_G_klasaR1 } k

end A252864.Seq
