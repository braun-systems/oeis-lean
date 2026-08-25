/- Sequence.lean — DRUGA POŁOWA po rozcięciu (demonstracja agenta ALEMAT, /tmp).
   Pierwsza połowa (defs + run_spec + invariant_j_le_k) = SeqBase.lean. -/
import SeqBase
import MostL
import «_DYN2_Dyn»

namespace A252864.Seq

open A252864.Tree

/-! ## 3.  Lemat pomostowy — jedyny lemat, który komentarz OEIS podaje w całości

`ℓ(a,b) = min { deg d + Σ dᵢ }` po reprezentacjach `Σ dᵢ φ^i = a·φ + b`, `dᵢ ∈ ℕ`.

Zapis bez liczb niewymiernych: `φ^i = F i · φ + F(i-1)`, więc warunek to PARA równań
na liczbach całkowitych.  To pokazuje, że lemat NIE POTRZEBUJE √5 w ogóle. -/

def F : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

def Fm1 : Nat → Nat
  | 0 => 1
  | n + 1 => F n

/-- Reprezentacja `(a,b)` cyframi `d 0 … d s`. -/
structure Repr (p : Node) where
  d     : Nat → Nat
  s     : Nat
  hsupp : ∀ i, s < i → d i = 0
  hval1 : ((List.range (s + 1)).map (fun i => d i * F i)).sum = p.1
  hval2 : ((List.range (s + 1)).map (fun i => d i * Fm1 i)).sum = p.2

/-- Koszt reprezentacji = stopień + suma cyfr.
    ⚠️ ZNALEZISKO ⚪: dla `d ≡ 0` stopień to maksimum ZBIORU PUSTEGO.  Komentarz OEIS
    nie podaje konwencji; tutaj musi ją podać typ (bierzemy 0). -/
def cost {p : Node} (r : Repr p) : Nat :=
  ((List.range (r.s + 1)).map (fun i => if r.d i > 0 then i else 0)).foldl max 0
  + ((List.range (r.s + 1)).map r.d).sum

/-! ### 🔧 MASZYNERIA DO LEMATU POMOSTOWEGO — przeniesiona z `T2dev.lean` (24.08.2026)

`T1.Repr`/`T1.cost`/`T1.F`/`T1.Fm1` w `T2dev.lean` są ZNAK W ZNAK identyczne z powyższymi.
Różnica jest gdzie indziej i jest fatalna — patrz `bridge_as_stated_is_false` na końcu sekcji. -/

theorem F_succ (i : Nat) : F (i + 1) = F i + Fm1 i := by
  cases i with
  | zero => rfl
  | succ j => show F (j+2) = F (j+1) + F j; rfl

theorem Fm1_succ (i : Nat) : Fm1 (i + 1) = F i := rfl
theorem F_zero : F 0 = 0 := rfl
theorem Fm1_zero : Fm1 0 = 1 := rfl

/-! #### sumy -/
def Sd (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => Sd f n + f (n + 1)

theorem Sd_eq (f : Nat → Nat) (n : Nat) : ((List.range (n+1)).map f).sum = Sd f n := by
  induction n with
  | zero => simp [Sd]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp [Sd]

theorem Sd_shift (g : Nat → Nat) (m : Nat) : Sd g (m+1) = g 0 + Sd (fun i => g (i+1)) m := by
  induction m with
  | zero => simp [Sd]
  | succ m ih => show Sd g (m+1) + g (m+2) = _; rw [ih]; show _ = g 0 + (Sd _ m + g (m+2)); omega

theorem Sd_congr (f g : Nat → Nat) (n : Nat) (h : ∀ i, i ≤ n → f i = g i) : Sd f n = Sd g n := by
  induction n with
  | zero => show f 0 = g 0; exact h 0 (Nat.le_refl 0)
  | succ n ih =>
      show Sd f n + f (n+1) = Sd g n + g (n+1)
      rw [ih (fun i hi => h i (Nat.le_succ_of_le hi)), h (n+1) (Nat.le_refl _)]

theorem Sd_add (f g : Nat → Nat) (n : Nat) :
    Sd (fun i => f i + g i) n = Sd f n + Sd g n := by
  induction n with
  | zero => rfl
  | succ n ih => show Sd _ n + (f (n+1) + g (n+1)) = (Sd f n + f (n+1)) + (Sd g n + g (n+1))
                 rw [ih]; omega

theorem Sd_update0 (f : Nat → Nat) (c n : Nat) :
    Sd (fun i => if i = 0 then f 0 + c else f i) n = Sd f n + c := by
  induction n with
  | zero => show (if (0:Nat) = 0 then f 0 + c else f 0) = f 0 + c; simp
  | succ n ih =>
      show Sd _ n + (if n+1 = 0 then f 0 + c else f (n+1)) = Sd f n + f (n+1) + c
      rw [ih]; simp; omega

theorem Sd_trim (f : Nat → Nat) : ∀ (n D : Nat), D ≤ n → (∀ i, D < i → i ≤ n → f i = 0) →
    Sd f n = Sd f D := by
  intro n
  induction n with
  | zero => intro D hD _; have : D = 0 := Nat.le_zero.mp hD; rw [this]
  | succ n ih =>
      intro D hD hz
      rcases Nat.lt_or_ge D (n+1) with h | h
      · have hDn : D ≤ n := Nat.lt_succ_iff.mp h
        show Sd f n + f (n+1) = Sd f D
        rw [hz (n+1) h (Nat.le_refl _), ih D hDn (fun i h1 h2 => hz i h1 (Nat.le_succ_of_le h2))]
        omega
      · have : D = n + 1 := Nat.le_antisymm hD h
        rw [this]

/-! #### stopień -/
def degR (d : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if 0 < d (n+1) then n+1 else degR d n

theorem degR_le (d : Nat → Nat) (n : Nat) : degR d n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      show (if 0 < d (n+1) then n+1 else degR d n) ≤ n+1
      split
      · exact Nat.le_refl _
      · exact Nat.le_succ_of_le ih

theorem degR_spec (d : Nat → Nat) : ∀ (n i : Nat), i ≤ n → 0 < d i → i ≤ degR d n := by
  intro n
  induction n with
  | zero => intro i hi _; rw [Nat.le_zero.mp hi]; exact Nat.le_refl 0
  | succ n ih =>
      intro i hi hd
      show i ≤ if 0 < d (n+1) then n+1 else degR d n
      rcases Nat.lt_or_ge i (n+1) with h | h
      · have hin : i ≤ n := Nat.lt_succ_iff.mp h
        split
        · exact hi
        · exact ih i hin hd
      · have : i = n + 1 := Nat.le_antisymm hi h
        subst this
        simp [hd]

theorem degR_zero_above (d : Nat → Nat) (n i : Nat) (h1 : degR d n < i) (h2 : i ≤ n) : d i = 0 := by
  rcases Nat.eq_zero_or_pos (d i) with h | h
  · exact h
  · exact absurd (degR_spec d n i h2 h) (Nat.not_le.mpr h1)

theorem degR_congr (d e : Nat → Nat) (h : ∀ i, 1 ≤ i → d i = e i) (n : Nat) :
    degR d n = degR e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (if 0 < d (n+1) then n+1 else degR d n) = (if 0 < e (n+1) then n+1 else degR e n)
      rw [h (n+1) (Nat.le_add_left 1 n), ih]

theorem degR_eq_fold (d : Nat → Nat) (n : Nat) :
    ((List.range (n+1)).map (fun i => if 0 < d i then i else 0)).foldl max 0 = degR d n := by
  induction n with
  | zero => simp [degR]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.foldl_append, ih]
      show max (degR d n) (if 0 < d (n+1) then n+1 else 0)
             = (if 0 < d (n+1) then n+1 else degR d n)
      split
      · exact Nat.max_eq_right (Nat.le_succ_of_le (degR_le d n))
      · exact Nat.max_eq_left (Nat.zero_le _)

theorem cost_eq {p : Node} (r : Repr p) : cost r = degR r.d r.s + Sd r.d r.s := by
  rw [cost, degR_eq_fold, Sd_eq]

/-! #### Słowa nad {A,B} i dwa układy współrzędnych

`stepAB` działa w układzie `(a,b)`, `stepJK` = `childA`/`childB` w układzie `(j,k)`;
`fromAB (a,b) = (a, a+b)` jest izomorfizmem między nimi.  **To jest miejsce, w którym
teza `bridge` MIAŁA błąd (do 24.08.2026): przykładała `Repr` do `(j,k)` zamiast do `(a,b)`.
Zdanie w tamtej postaci jest fałszywe — obalone przez `bridge_as_stated_is_false`.** -/

inductive Stp | A | B

def stepAB (p : Node) : Stp → Node
  | Stp.A => (p.1, p.2 + 1)
  | Stp.B => (p.1 + p.2, p.1)

def stepJK (p : Node) : Stp → Node
  | Stp.A => childA p
  | Stp.B => childB p

def evalAB (w : List Stp) : Node := w.foldl stepAB (0,0)
def evalJK (w : List Stp) : Node := w.foldl stepJK (0,0)
def fromAB (p : Node) : Node := (p.1, p.1 + p.2)

theorem step_commute (p : Node) (s : Stp) : stepJK (fromAB p) s = fromAB (stepAB p s) := by
  obtain ⟨a, b⟩ := p
  cases s <;> simp [stepJK, stepAB, fromAB, childA, childB, Prod.ext_iff] <;> omega

/-- własny rekursor "od końca listy" — `List.reverseRecOn` NIE ISTNIEJE w czystym Leanie. -/
theorem list_reverse_ind {motive : List Stp → Prop} (h0 : motive [])
    (hs : ∀ (w : List Stp) (s : Stp), motive w → motive (w ++ [s])) : ∀ w, motive w := by
  have key : ∀ (v : List Stp), motive v.reverse := by
    intro v
    induction v with
    | nil => exact h0
    | cons s v ih => rw [List.reverse_cons]; exact hs v.reverse s ih
  intro w
  have h := key w.reverse
  rwa [List.reverse_reverse] at h

theorem fold_commute : ∀ (w : List Stp) (p : Node),
    List.foldl stepJK (fromAB p) w = fromAB (List.foldl stepAB p w) := by
  intro w
  induction w with
  | nil => intro p; rfl
  | cons s w ih => intro p; rw [List.foldl_cons, List.foldl_cons, step_commute, ih]

theorem evalJK_eq (w : List Stp) : evalJK w = fromAB (evalAB w) := by
  have h := fold_commute w (0,0)
  have h0 : fromAB ((0,0) : Node) = ((0,0) : Node) := rfl
  rw [h0] at h
  exact h

theorem fromAB_inj {p q : Node} (h : fromAB p = fromAB q) : p = q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, e⟩ := q
  simp [fromAB] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  have : b = e := by omega
  subst this; rfl

theorem evalJK_snoc (w : List Stp) (s : Stp) : evalJK (w ++ [s]) = stepJK (evalJK w) s := by
  simp [evalJK, List.foldl_append]

theorem evalAB_snoc (w : List Stp) (s : Stp) : evalAB (w ++ [s]) = stepAB (evalAB w) s := by
  simp [evalAB, List.foldl_append]

theorem reach_of_word (w : List Stp) : ReachableBy (evalJK w) w.length := by
  refine list_reverse_ind (motive := fun v => ReachableBy (evalJK v) v.length) rfl ?_ w
  intro v s ih
  rw [evalJK_snoc, List.length_append]
  refine ⟨evalJK v, ih, ?_⟩
  cases s
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem word_of_reach : ∀ (n : Nat) (p : Node), ReachableBy p n →
    ∃ w : List Stp, w.length = n ∧ evalJK w = p := by
  intro n
  induction n with
  | zero => intro p h; exact ⟨[], rfl, h.symm⟩
  | succ n ih =>
      rintro p ⟨q, hq, hc⟩
      obtain ⟨w, hlen, hev⟩ := ih q hq
      rcases hc with rfl | rfl
      · exact ⟨w ++ [Stp.A], by simp [hlen], by rw [evalJK_snoc, hev]; rfl⟩
      · exact ⟨w ++ [Stp.B], by simp [hlen], by rw [evalJK_snoc, hev]; rfl⟩

/-! #### słowo z cyfr -/

def buildWord : (Nat → Nat) → Nat → List Stp
  | d, 0 => List.replicate (d 0) Stp.A
  | d, m+1 => buildWord (fun i => d (i+1)) m ++ (Stp.B :: List.replicate (d 0) Stp.A)

theorem foldA : ∀ (k : Nat) (p : Node),
    List.foldl stepAB p (List.replicate k Stp.A) = (p.1, p.2 + k) := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
      intro p
      rw [List.replicate_succ, List.foldl_cons]
      rw [ih (stepAB p Stp.A)]
      show ((p.1, p.2 + 1 + k) : Node) = (p.1, p.2 + (k+1))
      rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem eval_buildWord : ∀ (m : Nat) (d : Nat → Nat),
    evalAB (buildWord d m) = (Sd (fun i => d i * F i) m, Sd (fun i => d i * Fm1 i) m) := by
  intro m
  induction m with
  | zero =>
      intro d
      show List.foldl stepAB (0,0) (List.replicate (d 0) Stp.A) = _
      rw [foldA]
      show ((0 : Nat), 0 + d 0) = (d 0 * F 0, d 0 * Fm1 0)
      simp [F, Fm1]
  | succ m ih =>
      intro d
      show evalAB (buildWord (fun i => d (i+1)) m ++ (Stp.B :: List.replicate (d 0) Stp.A)) = _
      rw [evalAB, List.foldl_append]
      show List.foldl stepAB (evalAB (buildWord (fun i => d (i+1)) m))
             (Stp.B :: List.replicate (d 0) Stp.A) = _
      rw [ih (fun i => d (i+1)), List.foldl_cons]
      show List.foldl stepAB
        (Sd (fun i => d (i+1) * F i) m + Sd (fun i => d (i+1) * Fm1 i) m,
         Sd (fun i => d (i+1) * F i) m) (List.replicate (d 0) Stp.A) = _
      rw [foldA]
      have e1 : Sd (fun i => d i * F i) (m+1)
          = Sd (fun i => d (i+1) * F i) m + Sd (fun i => d (i+1) * Fm1 i) m := by
        rw [Sd_shift]
        have : (fun i => d (i+1) * F (i+1)) = (fun i => d (i+1) * F i + d (i+1) * Fm1 i) := by
          funext i; rw [F_succ, Nat.mul_add]
        rw [this, Sd_add]
        simp [F]
      have e2 : Sd (fun i => d i * Fm1 i) (m+1)
          = Sd (fun i => d (i+1) * F i) m + d 0 := by
        rw [Sd_shift]
        have : (fun i => d (i+1) * Fm1 (i+1)) = (fun i => d (i+1) * F i) := by
          funext i; rw [Fm1_succ]
        rw [this]
        simp [Fm1]
        omega
      rw [e1, e2]

theorem length_buildWord : ∀ (m : Nat) (d : Nat → Nat),
    (buildWord d m).length = m + Sd d m := by
  intro m
  induction m with
  | zero => intro d; show (List.replicate (d 0) Stp.A).length = 0 + Sd d 0
            rw [List.length_replicate]; show d 0 = 0 + d 0; omega
  | succ m ih =>
      intro d
      show (buildWord (fun i => d (i+1)) m ++ (Stp.B :: List.replicate (d 0) Stp.A)).length = _
      rw [List.length_append, ih (fun i => d (i+1)), List.length_cons, List.length_replicate,
          Sd_shift d m]
      omega

/-! #### (P) reprezentacja → słowo tej samej długości -/

theorem word_of_repr {a b : Nat} (r : Repr (a,b)) :
    ∃ w : List Stp, evalAB w = (a,b) ∧ w.length = cost r := by
  have hDs : degR r.d r.s ≤ r.s := degR_le r.d r.s
  have hz : ∀ i, degR r.d r.s < i → i ≤ r.s → r.d i = 0 := degR_zero_above r.d r.s
  have hzF : ∀ i, degR r.d r.s < i → i ≤ r.s → r.d i * F i = 0 :=
    fun i h1 h2 => by rw [hz i h1 h2]; exact Nat.zero_mul _
  have hzG : ∀ i, degR r.d r.s < i → i ≤ r.s → r.d i * Fm1 i = 0 :=
    fun i h1 h2 => by rw [hz i h1 h2]; exact Nat.zero_mul _
  refine ⟨buildWord r.d (degR r.d r.s), ?_, ?_⟩
  · rw [eval_buildWord]
    have h1 : Sd (fun i => r.d i * F i) (degR r.d r.s) = a := by
      rw [← Sd_trim (fun i => r.d i * F i) r.s _ hDs hzF, ← Sd_eq]
      exact r.hval1
    have h2 : Sd (fun i => r.d i * Fm1 i) (degR r.d r.s) = b := by
      rw [← Sd_trim (fun i => r.d i * Fm1 i) r.s _ hDs hzG, ← Sd_eq]
      exact r.hval2
    rw [h1, h2]
  · rw [length_buildWord, cost_eq, Sd_trim r.d r.s _ hDs hz]

/-! #### (Q) słowo → reprezentacja o koszcie ≤ długość -/

theorem degR_shift (d : Nat → Nat) : ∀ (n : Nat),
    degR (fun i => if i = 0 then 0 else d (i-1)) (n+1) ≤ degR d n + 1 := by
  intro n
  induction n with
  | zero =>
      have h2 : degR d 0 = 0 := rfl
      rw [h2]
      exact degR_le _ _
  | succ n ih =>
      by_cases h : 0 < d (n+1)
      · have hl : degR (fun i => if i = 0 then 0 else d (i-1)) (n+1+1) ≤ n+1+1 := degR_le _ _
        have hr : degR d (n+1) = n+1 := by
          show (if 0 < d (n+1) then n+1 else degR d n) = n+1
          simp [h]
        omega
      · have hl : degR (fun i => if i = 0 then 0 else d (i-1)) (n+1+1)
            = degR (fun i => if i = 0 then 0 else d (i-1)) (n+1) := by
          show (if 0 < (if (n+1+1 : Nat) = 0 then 0 else d (n+1+1-1)) then n+1+1 else
                  degR (fun i => if i = 0 then 0 else d (i-1)) (n+1))
                = degR (fun i => if i = 0 then 0 else d (i-1)) (n+1)
          simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
          simp [h]
        have hr : degR d (n+1) = degR d n := by
          show (if 0 < d (n+1) then n+1 else degR d n) = degR d n
          simp [h]
        rw [hl, hr]; exact ih

theorem Sd_A0 (e g : Nat → Nat) (m : Nat) (hg0 : g 0 = 0) :
    Sd (fun i => (if i = 0 then e 0 + 1 else e i) * g i) m = Sd (fun i => e i * g i) m := by
  apply Sd_congr
  intro i _
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [hg0]
  · have hne : i ≠ 0 := by omega
    simp [hne]

theorem Sd_A1 (e g : Nat → Nat) (m : Nat) (hg0 : g 0 = 1) :
    Sd (fun i => (if i = 0 then e 0 + 1 else e i) * g i) m = Sd (fun i => e i * g i) m + 1 := by
  rw [← Sd_update0 (fun i => e i * g i) 1 m]
  apply Sd_congr
  intro i _
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [hg0]
  · have hne : i ≠ 0 := by omega
    simp [hne]

theorem Sd_B (e g : Nat → Nat) (m : Nat) :
    Sd (fun i => (if i = 0 then 0 else e (i-1)) * g i) (m+1) = Sd (fun i => e i * g (i+1)) m := by
  rw [Sd_shift]
  simp only [ite_true, Nat.zero_mul, Nat.zero_add]
  apply Sd_congr
  intro i _
  simp

theorem Sd_B0 (e : Nat → Nat) (m : Nat) :
    Sd (fun i => if i = 0 then 0 else e (i-1)) (m+1) = Sd e m := by
  rw [Sd_shift]
  simp only [ite_true, Nat.zero_add]
  apply Sd_congr
  intro i _
  simp

theorem repr_of_word (w : List Stp) : ∃ r : Repr (evalAB w), cost r ≤ w.length := by
  refine list_reverse_ind (motive := fun v => ∃ r : Repr (evalAB v), cost r ≤ v.length) ?_ ?_ w
  · refine ⟨⟨fun _ => 0, 0, fun _ _ => rfl, ?_, ?_⟩, ?_⟩
    · show ((List.range 1).map (fun i => 0 * F i)).sum = (evalAB []).1
      simp [evalAB]
    · show ((List.range 1).map (fun i => 0 * Fm1 i)).sum = (evalAB []).2
      simp [evalAB]
    · rw [cost_eq]
      show degR (fun _ => 0) 0 + Sd (fun _ => 0) 0 ≤ (0 : Nat)
      simp [degR, Sd]
  · rintro v s ⟨r, hr⟩
    rw [cost_eq] at hr
    have hlen : (v ++ [s]).length = v.length + 1 := by simp
    cases s
    · -- ===== krok A : dopisz literę A =====
      have hA1 : Sd (fun i => (if i = 0 then r.d 0 + 1 else r.d i) * F i) r.s
          = Sd (fun i => r.d i * F i) r.s := Sd_A0 r.d F r.s F_zero
      have hA2 : Sd (fun i => (if i = 0 then r.d 0 + 1 else r.d i) * Fm1 i) r.s
          = Sd (fun i => r.d i * Fm1 i) r.s + 1 := Sd_A1 r.d Fm1 r.s Fm1_zero
      have hAd : Sd (fun i => if i = 0 then r.d 0 + 1 else r.d i) r.s = Sd r.d r.s + 1 :=
        Sd_update0 r.d 1 r.s
      have hAg : degR (fun i => if i = 0 then r.d 0 + 1 else r.d i) r.s = degR r.d r.s := by
        apply degR_congr
        intro i hi
        have hne : i ≠ 0 := by omega
        simp [hne]
      refine ⟨⟨fun i => if i = 0 then r.d 0 + 1 else r.d i, r.s, ?_, ?_, ?_⟩, ?_⟩
      · intro i hi
        have hne : i ≠ 0 := by omega
        simp only [hne, ite_false]
        exact r.hsupp i hi
      · rw [Sd_eq, evalAB_snoc, hA1, ← Sd_eq, r.hval1]
        rfl
      · rw [Sd_eq, evalAB_snoc, hA2, ← Sd_eq, r.hval2]
        rfl
      · rw [cost_eq]
        show degR (fun i => if i = 0 then r.d 0 + 1 else r.d i) r.s
             + Sd (fun i => if i = 0 then r.d 0 + 1 else r.d i) r.s ≤ (v ++ [Stp.A]).length
        rw [hAg, hAd, hlen]
        omega
    · -- ===== krok B : dopisz literę B =====
      have hB1 : Sd (fun i => (if i = 0 then 0 else r.d (i-1)) * F i) (r.s+1)
          = Sd (fun i => r.d i * F i) r.s + Sd (fun i => r.d i * Fm1 i) r.s := by
        rw [Sd_B r.d F r.s]
        have hst : (fun i => r.d i * F (i+1)) = (fun i => r.d i * F i + r.d i * Fm1 i) := by
          funext i; rw [F_succ, Nat.mul_add]
        rw [hst, Sd_add]
      have hB2 : Sd (fun i => (if i = 0 then 0 else r.d (i-1)) * Fm1 i) (r.s+1)
          = Sd (fun i => r.d i * F i) r.s := by
        rw [Sd_B r.d Fm1 r.s]
        apply Sd_congr
        intro i _
        rw [Fm1_succ]
      have hBd : Sd (fun i => if i = 0 then 0 else r.d (i-1)) (r.s+1) = Sd r.d r.s :=
        Sd_B0 r.d r.s
      have hBg := degR_shift r.d r.s
      refine ⟨⟨fun i => if i = 0 then 0 else r.d (i-1), r.s + 1, ?_, ?_, ?_⟩, ?_⟩
      · intro i hi
        have hne : i ≠ 0 := by omega
        simp only [hne, ite_false]
        exact r.hsupp (i-1) (by omega)
      · rw [Sd_eq, evalAB_snoc, hB1, ← Sd_eq, ← Sd_eq, r.hval1, r.hval2]
        rfl
      · rw [Sd_eq, evalAB_snoc, hB2, ← Sd_eq, r.hval1]
        rfl
      · rw [cost_eq]
        show degR (fun i => if i = 0 then 0 else r.d (i-1)) (r.s+1)
             + Sd (fun i => if i = 0 then 0 else r.d (i-1)) (r.s+1) ≤ (v ++ [Stp.B]).length
        rw [hBd, hlen]
        omega

/-! #### montaż -/

theorem reach_cost {a b : Nat} (r : Repr (a,b)) : ReachableBy (a, a+b) (cost r) := by
  obtain ⟨w, hev, hlen⟩ := word_of_repr r
  have h := reach_of_word w
  rw [evalJK_eq, hev, hlen] at h
  exact h

theorem cost_le_of_reach {a b n : Nat} (h : ReachableBy (a, a+b) n) :
    ∃ r : Repr (a,b), cost r ≤ n := by
  obtain ⟨w, hlen, hev⟩ := word_of_reach n (a, a+b) h
  have h2 : fromAB (evalAB w) = fromAB (a,b) := by rw [← evalJK_eq, hev]; rfl
  have h3 : evalAB w = (a,b) := fromAB_inj h2
  have hx := repr_of_word w
  rw [h3, hlen] at hx
  exact hx

/-- 🟢 **PRAWDZIWY lemat pomostowy** — przeniesiony z `T2dev.lean:475`.
    Węzeł drzewa to `(j,k) = (a, a+b)`; reprezentacja cyframi opisuje `(a,b)`,
    czyli `b = k - j`.  Dowód bez `sorry` i bez `native_decide`. -/
theorem bridge_ab (a b n : Nat) :
    IsShortest (a, a + b) n ↔ (∃ r : Repr (a,b), cost r = n) ∧ ∀ r : Repr (a,b), n ≤ cost r := by
  constructor
  · rintro ⟨hr, hmin⟩
    obtain ⟨r, hle⟩ := cost_le_of_reach hr
    have hge : n ≤ cost r := by
      rcases Nat.lt_or_ge (cost r) n with h | h
      · exact absurd (reach_cost r) (hmin _ h)
      · exact h
    refine ⟨⟨r, Nat.le_antisymm hle hge⟩, ?_⟩
    intro r'
    rcases Nat.lt_or_ge (cost r') n with h | h
    · exact absurd (reach_cost r') (hmin _ h)
    · exact h
  · rintro ⟨⟨r, hr⟩, hmin⟩
    refine ⟨hr ▸ reach_cost r, ?_⟩
    intro m hm hrm
    obtain ⟨r'', hle⟩ := cost_le_of_reach hrm
    exact absurd (hmin r'') (Nat.not_le.mpr (Nat.lt_of_le_of_lt hle hm))

/-! ### 🔴🔴 OBALENIE TEZY, KTÓRA STOI NIŻEJ PRZY `sorry` #2

`bridge` przykłada `Repr` do węzła `p = (j,k)`, czyli żąda `Σ dᵢ·Fm1 i = k`.
Prawdziwe równanie brzmi `Σ dᵢ·Fm1 i = k − j` (patrz `bridge_ab`).
Świadek, na którym te dwie tezy się rozjeżdżają: **`p = (1,0)`**.
Para `(1,0)` ma reprezentację `d₁ = 1` o koszcie 2 (i to jest MINIMUM),
a w drzewie **NIE WYSTĘPUJE NIGDY** (`oeis_claim_is_false`).
⇒ kierunek „⟸" tezy `bridge` daje `ReachableBy (1,0) 2` — sprzeczność. -/

theorem Sd_of_all_zero (f : Nat → Nat) : ∀ (n : Nat), (∀ i, i ≤ n → f i = 0) → Sd f n = 0 := by
  intro n
  induction n with
  | zero => intro h; exact h 0 (Nat.le_refl 0)
  | succ n ih =>
      intro h
      show Sd f n + f (n+1) = 0
      rw [ih (fun i hi => h i (Nat.le_succ_of_le hi)), h (n+1) (Nat.le_refl _)]

theorem Sd_zero_all (f : Nat → Nat) : ∀ (n : Nat), Sd f n = 0 → ∀ i, i ≤ n → f i = 0 := by
  intro n
  induction n with
  | zero => intro h i hi; rw [Nat.le_zero.mp hi]; exact h
  | succ n ih =>
      intro h i hi
      have h' : Sd f n + f (n+1) = 0 := h
      have h1 : Sd f n = 0 := by omega
      have h2 : f (n+1) = 0 := by omega
      rcases Nat.lt_or_ge i (n+1) with hlt | hge
      · exact ih h1 i (Nat.lt_succ_iff.mp hlt)
      · rw [Nat.le_antisymm hi hge]; exact h2

/-- reprezentacja pary `(1,0)` w sensie `Repr` z tego pliku: `d₁ = 1`. -/
def repr10 : Repr (1,0) :=
  { d := fun i => if i = 1 then 1 else 0
    s := 1
    hsupp := by
      intro i hi
      have hne : i ≠ 1 := by omega
      simp [hne]
    hval1 := by rfl
    hval2 := by rfl }

theorem cost_repr10 : cost repr10 = 2 := by rfl

theorem cost_ge_two_of_repr10 (r : Repr (1,0)) : 2 ≤ cost r := by
  rcases Nat.lt_or_ge (cost r) 2 with hlt | hge
  case inr => exact hge
  exfalso
  have hc : degR r.d r.s + Sd r.d r.s ≤ 1 := by rw [← cost_eq]; omega
  have h1 : Sd (fun i => r.d i * F i) r.s = 1 := by
    rw [← Sd_eq]; exact r.hval1
  have hz : ∀ i, i ≤ r.s → r.d i * F i = 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      show r.d 0 * F 0 = 0
      rw [F_zero]
      exact Nat.mul_zero _
    · rcases Nat.eq_zero_or_pos (degR r.d r.s) with hD | hD
      · have hdi : r.d i = 0 := by
          rcases Nat.eq_zero_or_pos (r.d i) with h | h
          · exact h
          · have := degR_spec r.d r.s i hi h
            omega
        rw [hdi]; exact Nat.zero_mul _
      · have hS : Sd r.d r.s = 0 := by omega
        rw [Sd_zero_all r.d r.s hS i hi]; exact Nat.zero_mul _
  rw [Sd_of_all_zero _ _ hz] at h1
  omega

/-- 🔴 **Teza `bridge` (linia niżej) jest FAŁSZYWA — to jest jej maszynowe obalenie.**
    Nie wolno więc zamknąć `sorry` #2 dowodem: dowodu nie ma, bo zdanie nie jest prawdziwe.
    Poprawna wersja stoi wyżej jako `bridge_ab`. -/
theorem bridge_as_stated_is_false :
    ¬ (∀ (p : Node) (n : Nat),
        IsShortest p n ↔ (∃ r : Repr p, cost r = n) ∧ ∀ r : Repr p, n ≤ cost r) := by
  intro h
  have hs : IsShortest (1,0) 2 :=
    (h (1,0) 2).mpr ⟨⟨repr10, cost_repr10⟩, cost_ge_two_of_repr10⟩
  exact oeis_claim_is_false 2 hs.1

/-- 🟢 **„Key lemma (bridge)" z OEIS — W POPRAWNYM SFORMUŁOWANIU** (alias `bridge_ab`).
    🔴 Do 24.08.2026 stało tu zdanie o `Repr p` dla węzła `p = (j,k)`, zamknięte `sorry`.
    **Było FAŁSZYWE** — obalone wyżej przez `bridge_as_stated_is_false` (świadek `(1,0)`).
    `sorry` przy zdaniu fałszywym = dowód dowolnego twierdzenia przy zielonej kompilacji:
    to była MINA, nie literówka, więc zdanie fałszywe zostaje tu WYŁĄCZNIE jako obalone.
    Przyczyna: `Repr` opisuje `(a,b)`, a węzeł drzewa to `(j,k) = (a, a+b)`, czyli `b = k-j`.
    Rozbrojenie i pomiary: `../_MINA_wynik.md`. -/
theorem bridge (a b n : Nat) :
    IsShortest (a, a + b) n ↔
      (∃ r : Repr (a,b), cost r = n) ∧ ∀ r : Repr (a,b), n ≤ cost r :=
  bridge_ab a b n

/-! ## 4.  A-LEMAT — ogniwo, którego komentarz OEIS W OGÓLE NIE ZAWIERA

Komentarz przechodzi od lematu pomostowego do „the nodes split into five classes"
słowami „From the lemma".  Między nimi leży to: -/

/-- Region `R = {a ≥ 8, b ≥ 1}` w współrzędnych `(a,b) = (j, k-j)`.

    🔴 ZNALEZISKO 🟡 (złapane przez kompilator 22.08, patrz raport): repo używa
    DWÓCH układów współrzędnych — OEIS pisze `(j,k)`, a dokumenty dowodu `(a,b)`
    z `b = k - j` — i NIGDZIE tego nie sygnalizuje.  Pierwsza wersja tego pliku
    przetłumaczyła `b ≥ 1` na `p.2 ≥ 1` zamiast na `p.1 < p.2`; `native_decide`
    odrzucił twierdzenie w 16 s.  W prozie ta pomyłka jest niewidoczna.

    🔴 I ZNALEZISKO WŁAŚCIWE: komentarz OEIS mówi „**the nodes** at each generation
    split into five classes" — BEZ tego ograniczenia.  Bez `R` zdanie jest fałszywe. -/
def inR (p : Node) : Prop := 8 ≤ p.1 ∧ p.1 < p.2

/-- Pokolenie, w którym węzeł pojawia się po raz pierwszy (szukane do `N`). -/
def gen? (N : Nat) (p : Node) : Option Nat :=
  (List.range (N + 1)).findSome? (fun n => if p ∈ (run n).2.1 then some n else none)

/-- 🔴🔴 ŚWIADEK, ŻE POPRZEDNIA WERSJA TEJ TEZY BYŁA FAŁSZYWA — zostawiony celowo.

    Do 22.08 stało tu `(p.1 + 2*p.2 + 3)^2 > 5*(p.1+1)^2`, czyli kryterium
    w układzie `(a,b) = (j,k)`.  Dokumenty dowodu pracują w `(a,b) = (j, k-j)`.
    Zmierzone (BFS, `j,k ≤ 400`): w układzie `(j,k)` teza ma **30 177
    kontrprzykładów na 76 636 węzłów regionu R**; w układzie `(j, k-j)` — **ZERO**.

    Najmniejszy świadek to `p = (8,12)`: stare kryterium mówi TAK
    (`35² = 1225 > 405`), a A-dziecko `(8,13)` leży w TYM SAMYM pokoleniu 7,
    czyli `l(A p) = l(p)`, a nie `l(p)+1`.

    📌 KLASA: poprzednia tura poprawiła REGION (`inR`), ale NIE poprawiła
    NIERÓWNOŚCI — fałsz miał dwa ciała, a poprawka trafiła w jedno.
    Dlatego poniżej `a` i `b` są OSOBNYMI argumentami, a przejście
    `(j,k) = (a, a+b)` stoi JAWNIE W TYPIE.  W prozie ta zamiana jest niewidoczna;
    tutaj nie da się jej przemilczeć. -/
theorem old_A_form_is_false :
    gen? 20 (8, 12) = some 7 ∧ gen? 20 (8, 13) = some 7
    ∧ (8 + 2 * 12 + 3) ^ 2 > 5 * (8 + 1) ^ 2 := by native_decide

theorem A_lemma (a b : Nat) (ha : 8 ≤ a) (hb : 1 ≤ b) (n : Nat)
    (hn : IsShortest (a, a + b) n) (hA : IsShortest (childA (a, a + b)) (n + 1)) :
    (a + 2 * b + 3) ^ 2 > 5 * (a + 1) ^ 2 :=
  A252864.MostL.A_lemma a b ha hb n hn hA
-- 🔴 sorry #3 = A-LEMAT (LEM_A „⟸" + LEM_B „⟹" w repo, ~700 linii prozy, errata [W7]).
-- CZEGO BRAKUJE: całego rachunku na sprzężeniu w Z[√5].
-- ⚠️ Hipoteza `inR` jest KONIECZNA: bez `1 ≤ p.2` teza pada na całym wierszu b = 0
-- (zmierzone: 1499 kontrprzykładów dla a ≤ 1499), bez `8 ≤ p.1` pada w 6 punktach.
-- To jest największe pojedyncze ryzyko całego łańcucha ([R8] w repo).

/-! ## 5.  Pięć klas i układ przejść

Note on the OEIS entry: it speaks of "five classes closed under A and B".
Read literally as `∀ p ∈ Iⱼ, childA p ∈ Iⱼ ∧ childB p ∈ Iⱼ`, this fails
(measured: `childA` maps `I₁` into `I₁ ∪ I₂ ∪ I₃`, `childB` into `I₄ ∪ I₅`).
The intended reading concerns the tree children, not the images of
`childA`/`childB`.

🔴🔴 STAŁO TU: „Funkcji klasyfikującej NIE definiuję — bo nie umiem podać jej progów
w sposób, którego bym nie zmyślił.  Zamiast tego jest PARAMETREM".  **To było ZŁE
rozwiązanie i dało FAŁSZYWE twierdzenie** (patrz `dynamics_forall_klasa_is_false` niżej):
parametr kwantyfikowany uniwersalnie znaczy „dla KAŻDEJ funkcji klasyfikującej", a nie
„dla tej właściwej".  Progów nie trzeba było zgadywać — stoją w `MOST.md:349-352`
([R1]) i są zapisywalne CAŁKOWICIE.  `klasaR1` niżej.  `klasa` zostaje jako `variable`
tylko dlatego, że `Transfer.lean` opiera się na niej jako na parametrze. -/

variable (klasa : Node → Fin 5)

/-- Liczność klasy `j` na poziomie `n`, w regionie `R`. -/
def v (n : Nat) (j : Fin 5) : Nat :=
  ((run n).2.1.filter (fun p => 8 ≤ p.1 && p.1 < p.2 && klasa p == j)).length

/-- Macierz przejść M z [R1]. -/
def M : Fin 5 → Fin 5 → Nat
  | 0, 4 => 1
  | 1, 3 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 3, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | _, _ => 0

/-- 🔴 ZNALEZISKO NAJWAŻNIEJSZE Z CAŁEGO PLIKU:
    UKŁAD JEST **AFINICZNY**, nie liniowy.  Stały napływ `w = (7,0,0,0,0)`
    NIE MOŻE zniknąć z zapisu — a w komentarzu OEIS go nie ma.
    Zdanie „the resulting transfer system has characteristic polynomial …"
    opisuje tylko `M`; układ z niezerowym `w` NIE MA wielomianu charakterystycznego. -/
def w : Fin 5 → Nat
  | 0 => 7
  | _ => 0

/-! ### Napływ afiniczny `w` — ZMIERZONY, nie przepisany z prozy

Węzeł „wpływa" do `R` w pokoleniu `n`, gdy sam leży w `R`, a żaden jego możliwy
rodzic z pokolenia `n-1` w `R` nie leży.  Kandydaci na rodzica są obliczalne:
`childA q = p` daje `q = (p₁, p₂-1)`, `childB q = p` daje `q = (p₂-p₁, p₁)`. -/

def inRb (p : Node) : Bool := 8 ≤ p.1 && p.1 < p.2

def genSet (n : Nat) : Std.HashSet Node := Std.HashSet.ofList (run n).2.1

def parentInR (prev : Std.HashSet Node) (p : Node) : Bool :=
  (inRb (p.1, p.2 - 1) && prev.contains (p.1, p.2 - 1))
  || (inRb (p.2 - p.1, p.1) && prev.contains (p.2 - p.1, p.1))

def inflow (n : Nat) : Nat :=
  ((run n).2.1.filter (fun p => inRb p && !parentInR (genSet (n - 1)) p)).length

/-- ✅ Napływ jest STAŁY i równy 7 dla n = 10 … 19 — czyli `w = (7,0,0,0,0)`
    z prozy MA pokrycie w pomiarze, a próg `10 ≤ n` jest trafny. -/
theorem inflow_is_seven : ∀ n ∈ List.range' 10 10, inflow n = 7 := by native_decide

/-- 🔑 PRÓG 10 JEST OPTYMALNY: tuż pod nim napływ jest INNY (`inflow 9 = 6`).

    ⚠️ ŚWIADEK MOJEJ WŁASNEJ POMYŁKI, zostawiony celowo: najpierw wpisałem tu
    „próg jest o jeden za niski, napływ 7 dopiero od n = 11" — bo policzyłem
    napływ w Pythonie po RZECZYWISTYM rodzicu (tym, który węzeł faktycznie
    wygenerował), a w Leanie po KANDYDATACH na rodzica.  Obie definicje dają 7
    dla n ≥ 11, ale różnią się w n = 9, 10.  `native_decide` odrzucił moje
    twierdzenie w 4 minuty.  Klasa: LICZBA NOSI SWOJĄ DEFINICJĘ — „napływ"
    bez podania, co jest rodzicem, jest liczbą uszkodzoną już w chwili zapisu. -/
theorem inflow_threshold_is_tight : inflow 9 = 6 := by native_decide

/-! ### 🔴🔴 POPRZEDNIA TEZA `dynamics` BYŁA ZDANIEM FAŁSZYWYM UKRYTYM POD `sorry`

Stało tu (dosłownie) `v klasa n j = … + w j` z `klasa` wziętą z `variable`, czyli
**kwantyfikowaną UNIWERSALNIE**.  Weź `klasa ≡ 0`: cała populacja `R` siedzi wtedy
w klasie 0, a wiersz 0 macierzy `M` ma jedynkę wyłącznie w kolumnie 4 — więc teza
orzekała `|R ∩ poziom n| = 7` dla każdego `n ≥ 10`.  Zmierzone: `|R ∩ poziom 10| = 42`.

📌 KLASA: `sorry` nie odróżnia „nie umiem tego dowieść" od „to jest nieprawda".
Zdanie stało w pliku, którego nagłówek nazywa je MAPĄ LUK — a nie było luką, tylko fałszem.
Dlatego świadek jest tu jako TWIERDZENIE, nie jako komentarz. -/

/-- 🔴 Poprzednia teza `dynamics` (`klasa` kwantyfikowana uniwersalnie) jest FAŁSZEM.
    ⚠️ `native_decide`. -/
theorem dynamics_forall_klasa_is_false :
    ¬ (∀ (kl : Node → Fin 5) (n : Nat), 10 ≤ n → ∀ j : Fin 5,
        v kl n j
          = (List.finRange 5).foldl (fun acc k => acc + M j k * v kl (n - 1) k) 0 + w j) := by
  intro h
  have hbad : v (fun _ => (0 : Fin 5)) 10 0
      ≠ (List.finRange 5).foldl
          (fun acc k => acc + M 0 k * v (fun _ => (0 : Fin 5)) 9 k) 0 + w 0 := by
    native_decide
  exact hbad (h (fun _ => (0 : Fin 5)) 10 (by omega) 0)

/-- Obie strony jawnie: **42 wobec 7**.  ⚠️ `native_decide`. -/
theorem dynamics_false_numbers :
    v (fun _ => (0 : Fin 5)) 10 0 = 42 ∧
    (List.finRange 5).foldl
      (fun acc k => acc + M 0 k * v (fun _ => (0 : Fin 5)) 9 k) 0 + w 0 = 7 := by
  native_decide

/-! ### ✅ KLASY `I₁..I₅` JAWNIE — progi z `MOST.md [R1]`, w arytmetyce CAŁKOWITEJ

`MOST.md:349-352`: progi `−1 < φ−2 < φ−1 < φ` na `z′ = aφ′+b`, `φ′ = 1−φ`,
we współrzędnych `(a,b) = (j, k−j)`.  Z `x := a + 2b`:

| klasa | `z′` | warunek całkowity |
|---|---|---|
| `I₁` | `z′ < −1`   | `(x+2)² < 5a²` |
| `I₂` | `z′ < φ−2`  | `(x+3)² < 5(a+1)²` |
| `I₃` | `z′ < φ−1`  | `(x+1)² < 5(a+1)²` |
| `I₄` | `z′ < φ`    | `x² + 1 < 5(a+1)² + 2x`  (zapis bez odejmowania w ℕ) |
| `I₅` | reszta      | — |

🟢 To NIE jest moja rekonstrukcja przyjęta na wiarę — ma trzy niezależne trafienia
w liczby, które w repo już stały: `v(10) = (10,5,11,8,8)` (`MOST.md:422`),
defekty przedreżimowe `d(7),d(8),d(9)` (`MOST.md:420-421`) i `D(10,a)` (`MOST.md:394`). -/
def klasaR1 (p : Node) : Fin 5 :=
  let a := p.1
  let x := a + 2 * (p.2 - p.1)
  if (x + 2) * (x + 2) < 5 * (a * a) then 0
  else if (x + 3) * (x + 3) < 5 * ((a+1) * (a+1)) then 1
  else if (x + 1) * (x + 1) < 5 * ((a+1) * (a+1)) then 2
  else if x * x + 1 < 5 * ((a+1) * (a+1)) + 2 * x then 3
  else 4

/-- 🔑 Kotwica z `MOST.md:422` odtworzona przez Lean.  ⚠️ `native_decide`. -/
theorem klasaR1_v10 :
    v klasaR1 10 0 = 10 ∧ v klasaR1 10 1 = 5 ∧ v klasaR1 10 2 = 11
    ∧ v klasaR1 10 3 = 8 ∧ v klasaR1 10 4 = 8 := by native_decide

/-- ✅ POPRAWIONA teza `dynamics`, zweryfikowana dla `n = 10..24`.  ⚠️ `native_decide`. -/
theorem dynamics_klasaR1_measured :
    ∀ n ∈ List.range' 10 15, ∀ j ∈ List.finRange 5,
      v klasaR1 n j
        = (List.finRange 5).foldl (fun acc k => acc + M j k * v klasaR1 (n - 1) k) 0 + w j := by
  native_decide

/-- 🔑 PRÓG 10 JEST CIASNY — tuż pod nim poprawiona teza PADA.  ⚠️ `native_decide`. -/
theorem dynamics_klasaR1_fails_at_9 :
    ¬ (∀ j ∈ List.finRange 5,
      v klasaR1 9 j
        = (List.finRange 5).foldl (fun acc k => acc + M j k * v klasaR1 8 k) 0 + w j) := by
  native_decide

/-! ### ✅ [R3.1] — CAŁY ZBIÓR NAPŁYWU LEŻY W `I₁`.  Bez `native_decide`, bez `sorry`.

`MOST.md:388-395`: `W(n) := {(n−2,1)} ∪ {(n+c−3, c) : c = 2..7}` we współrzędnych `(a,b)`.
W `(j,k)` (bo `k = a+b`) i z `n = m+10` daje to `(m+8, m+9)` oraz `(m+c+7, m+2c+7)`.
To jest połowa dowodu [R3] — ta, która NIE stoi na A-LEMACIE. -/

/-- Warunek klasy `I₁` we współrzędnych `(a,b)`. -/
def inI1 (a b : Nat) : Prop := (a + 2 * b + 2) * (a + 2 * b + 2) < 5 * (a * a)

theorem klasaR1_of_inI1 (j k : Nat) (h : inI1 j (k - j)) : klasaR1 (j, k) = 0 := by
  simp only [klasaR1]
  rw [if_pos]
  exact h

theorem R31_head (m : Nat) : inI1 (m + 8) 1 := by
  simp only [inI1, Nat.mul_add, Nat.add_mul]
  omega

theorem R31_tail (m c : Nat) (h2 : 2 ≤ c) (h7 : c ≤ 7) : inI1 (m + 7 + c) c := by
  have hc : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [inI1, Nat.mul_add, Nat.add_mul]; omega)

/-- ✅ [R3.1], węzeł `(n−2, n−1)`.  Dla KAŻDEGO `n = m+10 ≥ 10`. -/
theorem inflow_head_I1 (m : Nat) : klasaR1 (m + 8, m + 9) = 0 := by
  refine klasaR1_of_inI1 _ _ ?_
  have h : m + 9 - (m + 8) = 1 := by omega
  rw [h]
  exact R31_head m

/-- ✅ [R3.1], węzły `(n+c−3, n+2c−3)` dla `c = 2..7`.  Dla KAŻDEGO `n = m+10 ≥ 10`. -/
theorem inflow_tail_I1 (m c : Nat) (h2 : 2 ≤ c) (h7 : c ≤ 7) :
    klasaR1 (m + c + 7, m + 2 * c + 7) = 0 := by
  refine klasaR1_of_inI1 _ _ ?_
  have h : m + 2 * c + 7 - (m + c + 7) = c := by omega
  rw [h]
  have he : m + c + 7 = m + 7 + c := by omega
  rw [he]
  exact R31_tail m c h2 h7

/-! ### ✅ Dwa z trzech pól `Transfer` (z `Transfer.lean`) dla `klasaR1` -/

/-- `Transfer.ini_C` dla `klasaR1`.  ⚠️ `native_decide`. -/
theorem transfer_ini_C_klasaR1 : v klasaR1 10 1 + v klasaR1 10 2 = v klasaR1 10 4 + 8 := by
  native_decide

/-- `Transfer.ini_G` dla `klasaR1`.  ⚠️ `native_decide`. -/
theorem transfer_ini_G_klasaR1 :
    v klasaR1 10 1 + 2 * v klasaR1 10 2 = v klasaR1 10 0 + v klasaR1 10 4 + 9 := by
  native_decide

theorem dynamics (n : Nat) (hn : 10 ≤ n) (j : Fin 5) :
    v klasaR1 n j = (List.finRange 5).foldl (fun acc k => acc + M j k * v klasaR1 (n - 1) k) 0
                  + w j :=
  A252864.DYN2.dynamics n hn j
-- 🟢🟢 `sorry #4` = [R3] — ZAMKNIĘTY 24.08.2026.  Dowód: `_DYN2_Dyn.lean`.
-- `#print axioms A252864.Seq.dynamics` → [propext, Classical.choice, Quot.sound].
-- ZERO `native_decide`, ZERO `sorry`.  Teza NIE była osłabiana ani obwarowywana hipotezą —
-- podstawienie jest jednolinijkowe, bo `klasaR1`/`M`/`w`/`v` mają kopie `rfl` w `DYN2`.
--
-- ⚠️ STAŁO TU (i było prawdą do 24.08 rano): „CZEGO NADAL BRAKUJE — dokładnie jednej rzeczy:
-- [R2] … [R2] stoi WPROST na `A_lemma` (`sorry #3`), więc tego ogniwa NIE DA SIĘ domknąć
-- przed A-LEMATEM".  A-LEMAT został domknięty, więc blokada spadła — ale zdanie „dokładnie
-- jednej rzeczy" było ZANIŻONE.  Zmierzone przy domykaniu, brakowało PIĘCIU:
--   ① [R2] A-część  — `DYN2.R2_A`, z `ALemat.A_lemat`
--   ② [R2] B-część  — `DYN2.R2_B`; `MOST.md:374` wycenia to na „rachunek sprzężeń w Z[√5]",
--                      a w liczbach całkowitych jest to JEDNA tożsamość `DYN2.conj_id`:
--                      (3a+b+1)² + (a+2b+2)² = 5(a+b+1)² + 5a²
--   ③ [D3] siedem inkluzji klas + trzy zagnieżdżenia progów  — `_DYN2_Klasy.lean`
--   ④ [M6] napływ = DOKŁADNIE `W(n)`  — `DYN2.naplyw_iff`; `Seq.parentInR` liczy KANDYDATÓW
--          na rodzica, a dowód potrzebuje RODZICA-DRZEWOWEGO (`DYN.tparent`) — to dwie różne
--          liczby (`inflow 9 = 6` wobec 7), więc tego ogniwa nie dało się pominąć
--   ⑤ maszyneria zliczania na listach bez Mathlib  — `_DYN2_Licz.lean`
--
-- 🔑 STRUKTURA, która wyszła z dowodu i której nie ma w `MOST.md`:
--    klasa ∈ {0,1,2} ⇒ rodzicem-drzewowym jest B-rodzic;  klasa ∈ {3,4} ⇒ A-rodzic.
--    (bo `klasa ≤ 2 ⟺ C2(a,b)`, a `C2` to dokładnie zaprzeczenie warunku A-LEMATU)
--    ⇒ wiersze `M`: j=3,4 to `childA`; j=0,1,2 to `childB`.
--
-- 📏 PRÓG `n ≥ 10` JEST CIASNY I ZNAMY JEGO PRZYCZYNĘ (a nie tylko `native_decide`):
--    osiem węzłów łamie krok „b ≥ 8" w wierszach 1 i 2 —
--    (8,4) (8,5) (9,5) (9,6) (10,6) (11,6) (11,7) (12,7) w (a,b) —
--    i WSZYSTKIE OSIEM leży na poziomach 7 i 8.  Kontrola niezależnym BFS-em (Python):
--    dla n = 9 wiersze 1,2,3,4 PRZECHODZĄ, a wiersz 0 daje 6 wobec 7 ⇒ próg jest potrzebny
--    WYŁĄCZNIE przez NAPŁYW, nie przez macierz.  To zgadza się z `inflow_threshold_is_tight`.
--
-- CO ZOSTAŁO DOMKNIĘTE Z [R3] WCZEŚNIEJ: `[R3.1]` (napływ ⊂ I₁) — `inflow_head_I1`
-- i `inflow_tail_I1` wyżej, dla WSZYSTKICH n ≥ 10, bez `native_decide` i bez `sorry`.

/-! ## 6.  Część przejściowa — drugi składnik, którego komentarz OEIS nie ma -/

/-- Część przejściowa: węzły POZA `R`, czyli `a ≤ 7` lub `b = 0` (tj. `k = j`). -/
def cT (n : Nat) : Nat :=
  ((run n).2.1.filter (fun p => p.1 ≤ 7 || p.2 == p.1)).length

/-- Podział jest ZUPEŁNY: część przejściowa + region `R` = całe pokolenie.
    (Kontrola, że `cT` i `R` naprawdę się dopełniają, a nie tylko brzmią podobnie.) -/
theorem partition_complete :
    ∀ n ∈ List.range' 0 33,
      cT n + ((run n).2.1.filter (fun p => 8 ≤ p.1 && p.1 < p.2)).length = a n := by
  native_decide

/-- Zmierzone: dla n = 10 … 32 część przejściowa jest STAŁA i równa 9. -/
theorem transitional_nine_measured :
    ∀ n ∈ List.range' 10 23, cT n = 9 := by native_decide

/-- 🔑 PRÓG 10 JEST OPTYMALNY, nie zapasowy — tuż pod nim wartość jest INNA.
    Ta para świadków jest tu z tego samego powodu co `rec_fails_4_11`
    w `Checks.lean`: bez niej „dla n ≥ 10" byłoby liczbą wziętą z sufitu. -/
theorem transitional_threshold_is_tight : cT 8 = 11 ∧ cT 9 = 10 := by native_decide

/-- ✅✅ **[M4] — DOWIEDZIONE DLA WSZYSTKICH `n ≥ 10`.**  `sorry #5` ZAMKNIĘTY.

    Dowód: `Bfs.lean`.  Aksjomaty: `propext`, `Classical.choice`, `Quot.sound`
    oraz DWA `native_decide` na faktach SKOŃCZONYCH i nazwanych:
    `Bfs.base_ok` (baza indukcji `n = 10..15`) i `Bfs.finB_true`
    (`⋃_{j≤9}(poziom j ∩ przejściowe)` ma `p.1 ≤ 8`, `p.2 ≤ 14`).

    🔑 DLACZEGO DAŁO SIĘ TO ZAMKNĄĆ, A `dynamics` NIE: region `R` jest ZAMKNIĘTY na obu
    dzieciach (`(j,k) ↦ (j,k+1)` i `(j,k) ↦ (k,j+k)`), więc żadne dziecko węzła z `R`
    nie jest przejściowe ⇒ **część przejściowa ewoluuje AUTONOMICZNIE** i nie potrzebuje
    A-LEMATU.  (Zgodne z `MOST.md [M7]`: „NIE stoi na: A-LEMACIE".)

    ⚠️ Droga jest INNA niż proza w `MOST.md`: tam [M4] idzie przez `ℓ`, [B1], [M2.1], [M3]
    i 36 certyfikatów skończonych.  Tu — wprost po `run`, przez specyfikację kroku BFS
    (`Bfs.mem_gen_succ`, `Bfs.seen_iff`) i silną indukcję po całej historii.
    Dwie niezależne drogi do tej samej liczby. -/
theorem transitional_nine (n : Nat) (hn : 10 ≤ n) : cT n = 9 :=
  A252864.Bfs.cT_nine n hn

/-! ## 7.  Teza główna

⚠️ ZNALEZISKO 🔴: z samego `dynamics` + `transitional_nine` da się wyprowadzić TYLKO
`n ≥ 13`.  Przypadek `n = 12` MUSI być osobnym twierdzeniem (rachunek skończony, [R5]).
W komentarzu OEIS „whence … for all n >= 12" sugeruje, że wychodzi z układu przejść.
NIE WYCHODZI — i widać to niezależnie w `Checks.charpoly_rec_fails_at_12`. -/

/-! ### 🔑 DRUGA DROGA — krótsza, i to ONA domyka `regime`

`SZKIELET_DOWODU.md` opisuje INNY łańcuch niż partycja Markowa powyżej:

    ② bilans kandydatów   a(n) = 2·a(n−1) − kolizje(n)          [PROVEN, def.]
    ⑤ LEMAT K             kolizje(n) = a(n−4) + a(n−5)          [ZWERYFIKOWANE n ≤ 31]
    ⑥ domknięcie          x⁵−2x⁴+x+1 = (x²−x−1)(x³−x²−1)        [PROVEN, algebra]

② nie wnosi treści formalnej (`kolizje(n)` jest Z DEFINICJI równe `2a(n−1) − a(n)`),
więc ② i ⑤ razem to JEDNO zdanie arytmetyczne — `five_term` poniżej.
⑥ jest tu udowodnione W CAŁOŚCI, bez `sorry` i bez `native_decide`.

⇒ **Ta droga zastępuje CZTERY luki (`A_lemma`, `dynamics`, `transitional_nine`,
  `regime`) jedną.**  Partycja Markowa powyżej zostaje jako mapa drugiej drogi
  i jako miejsce, gdzie znaleziono błędy we wpisie OEIS — ale `stoll` już przez
  nią NIE przechodzi. -/

/-- **[LEMAT K, krok ⑤ szkieletu]** — JEDYNA luka, przez którą przechodzi `stoll`.
    Zapis bez odejmowania w ℕ (`n = k + 14`), żeby nie wprowadzać obcinania. -/
theorem five_term (k : Nat) : a (k + 14) + a (k + 10) + a (k + 9) = 2 * a (k + 13) := by
  sorry
-- 🔴 JEDYNY `sorry` w łańcuchu `stoll`.  Równoważny LEMATOWI K ze szkieletu.
-- Status w repo: zweryfikowany EXACT do pokolenia 31, NIE udowodniony.
-- CZEGO BRAKUJE: zliczenia kolizji R1/R2 — bijekcja-przesunięcie porządkowana
-- nachyleniem φ, z korektą e(n) = [3|n] pochodzącą od par dolnego ciągu Wythoffa
-- (parzystość Fibonacciego: F_k parzyste ⟺ 3|k).  To jest teoria Beatty'ego,
-- dziedzina zbadana — ale nie sprowadza się do rachunku skończonego.

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
/-- Baza indukcji: `c(12) = 0`. -/
theorem base12 : a 12 = a 11 + a 9 := by
  -- 🟢 JĄDRO, nie kompilator: przez most `Tree.run_gen_eq` (HashSet ≡ lista).
  unfold a
  rw [Tree.run_gen_eq 12, Tree.run_gen_eq 11, Tree.run_gen_eq 9]
  decide
set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
/-- Baza indukcji: `c(13) = 0`.  Rekurencja na `c` jest DRUGIEGO rzędu,
    więc dwa kolejne zera są konieczne — jedno nie wystarczy. -/
theorem base13 : a 13 = a 12 + a 10 := by
  -- 🟢 JĄDRO, nie kompilator: przez most `Tree.run_gen_eq` (HashSet ≡ lista).
  unfold a
  rw [Tree.run_gen_eq 13, Tree.run_gen_eq 12, Tree.run_gen_eq 10]
  decide

/-- 🔑 PRÓG 14 W `five_term` JEST CIASNY, nie zapasowy — tuż pod nim zdanie PADA.
    Bez tej kontroli „dla n ≥ 14" byłoby liczbą wziętą z sufitu. -/
theorem five_term_fails_at_13 : ¬ (a 13 + a 9 + a 8 = 2 * a 12) := by native_decide
theorem five_term_fails_at_12 : ¬ (a 12 + a 8 + a 7 = 2 * a 11) := by native_decide

/-- ⑥ ALGEBRA DOMKNIĘCIA — pełny dowód.
    `c(n) := a(n) − a(n−1) − a(n−3)` spełnia rekurencję Fibonacciego, bo
    `c(n) − c(n−1) − c(n−2) = a(n) − 2a(n−1) + a(n−4) + a(n−5) = 0`.
    Dwa kolejne zera ⇒ `c ≡ 0`.  Indukcja idzie PARAMI, bo rząd jest drugi. -/
theorem pair (k : Nat) :
    a (k + 12) = a (k + 11) + a (k + 9) ∧ a (k + 13) = a (k + 12) + a (k + 10) := by
  induction k with
  | zero => exact ⟨base12, base13⟩
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show a (k + 14) = a (k + 13) + a (k + 11)
      have hK := five_term k
      have h1 := ih.1
      have h2 := ih.2
      omega

theorem regime (n : Nat) (hn : 13 ≤ n) : a n = a (n - 1) + a (n - 3) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e1 : 13 + k - 1 = k + 12 := by omega
  have e3 : 13 + k - 3 = k + 10 := by omega
  have e0 : 13 + k = k + 13 := by omega
  rw [e1, e3, e0]
  exact (pair k).2

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
/-- Przypadek `n = 12` — rachunek skończony, tu domknięty MASZYNOWO. -/
theorem case_twelve : a 12 = a 11 + a 9 := by
  -- 🟢 JĄDRO, nie kompilator: przez most `Tree.run_gen_eq` (HashSet ≡ lista).
  unfold a
  rw [Tree.run_gen_eq 12, Tree.run_gen_eq 11, Tree.run_gen_eq 9]
  decide

/-- KONJEKTURA STOLLA (MathOverflow 195207, 2015). -/
theorem stoll (n : Nat) (hn : 12 ≤ n) : a n = a (n - 1) + a (n - 3) := by
  rcases Nat.lt_or_ge n 13 with h | h
  · have h12 : n = 12 := by omega
    subst h12; exact case_twelve
  · exact regime n h

end A252864.Seq
