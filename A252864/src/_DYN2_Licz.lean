/-
  _DYN2_Licz.lean — CZYSTO OGÓLNA maszyneria na listach pod `Seq.dynamics`.
  Lean 4.34.0-rc2, BEZ Mathlib, BEZ `sorry`/`native_decide`/`axiom`.

  Zero wiedzy o A252864.  Wszystko jest o listach: Nodup, map, append, filter, length.

  ŹRÓDŁO KLUCZOWE (rdzeń JUŻ TO MA — `best code = no code`):
    List.perm_ext_iff_of_nodup : l₁.Nodup → l₂.Nodup → (l₁.Perm l₂ ↔ ∀ a, a ∈ l₁ ↔ a ∈ l₂)
    List.Perm.length_eq        : l₁.Perm l₂ → l₁.length = l₂.length
  Z tych dwóch (L1) wynika CAŁA reszta.
-/

set_option linter.unusedVariables false

namespace A252864.LICZ

/-! ## (L1) Dwie listy bez powtórzeń o tej samej zawartości mają tę samą długość. -/

/-- **L1.**  Rdzeń ma `List.perm_ext_iff_of_nodup` + `List.Perm.length_eq`; to jest ich złożenie. -/
theorem length_eq_of_nodup_mem_iff {α : Type _} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → l₂.Nodup → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁.length = l₂.length :=
  fun l₁ l₂ h₁ h₂ h => ((List.perm_ext_iff_of_nodup h₁ h₂).mpr h).length_eq

/-- Wersja bez `DecidableEq` — rdzeń jej nie potrzebuje, więc i my nie. -/
theorem length_eq_of_nodup_mem_iff' {α : Type _}
    (l₁ l₂ : List α) (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.length = l₂.length :=
  ((List.perm_ext_iff_of_nodup h₁ h₂).mpr h).length_eq

/-! ## (L2) Obraz injekcji zachowuje brak powtórzeń. -/

/-- **L2.**  Rdzeń NIE ma `List.Nodup.map` (sprawdzone `#check`); ma `List.pairwise_map`
    i `List.Pairwise.imp`, a `List.Nodup l` to definicyjnie `List.Pairwise (· ≠ ·) l`. -/
theorem nodup_map_of_inj {α β : Type _} (f : α → β)
    (hf : ∀ x y, f x = f y → x = y) (l : List α) (h : l.Nodup) : (l.map f).Nodup :=
  List.pairwise_map.mpr (h.imp (fun {a b} hab hfab => hab (hf a b hfab)))

/-- **L2′.**  Wersja z injektywnością TYLKO na elementach listy — słabsze założenie,
    więc mocniejsze twierdzenie.  Potrzebne, gdy `f` jest injektywne dopiero na
    węzłach osiągalnych, a nie na całym typie. -/
theorem nodup_map_mem_of_inj {α β : Type _} (f : α → β) :
    ∀ (l : List α), (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => by simp
  | a :: t, hf, h => by
      have hc := List.nodup_cons.mp h
      have hrec : (t.map f).Nodup :=
        nodup_map_mem_of_inj f t
          (fun x y hx hy hfxy => hf x y (by simp [hx]) (by simp [hy]) hfxy) hc.2
      rw [List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, hrec⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨b, hb, hfb⟩
      have hab : a = b := hf a b (by simp) (by simp [hb]) hfb.symm
      exact hc.1 (by rw [hab]; exact hb)

/-! ## (L3) Sklejenie dwóch list rozłącznych. -/

/-- **L3.**  Rdzeń ma `List.nodup_append` (postać `↔`); to jest jej strona `mpr`
    w wygodnym dla mnie kształcie `∀ x, x ∈ l₁ → x ∈ l₂ → False`. -/
theorem nodup_append_of_disjoint {α : Type _} (l₁ l₂ : List α)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hd : ∀ x, x ∈ l₁ → x ∈ l₂ → False) : (l₁ ++ l₂).Nodup :=
  List.nodup_append.mpr ⟨h₁, h₂, fun a ha b hb hab => hd a ha (hab ▸ hb)⟩

/-- **L3.**  Alias na `List.length_append` (rdzeń ma to z niejawnymi argumentami). -/
theorem length_append {α : Type _} (l₁ l₂ : List α) :
    (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append

/-! ## (L5) Pomocniki na filtry. -/

/-- **L5.**  Rdzeń NIE ma `List.Nodup.filter`; ma `List.Pairwise.filter` i `List.filter_sublist`. -/
theorem nodup_filter {α : Type _} (p : α → Bool) (l : List α) (h : l.Nodup) : (l.filter p).Nodup :=
  List.Nodup.sublist List.filter_sublist h

/-- **L5.**  Alias na `List.mem_filter` (rdzeń ma to z niejawnymi argumentami). -/
theorem mem_filter_iff {α : Type _} (p : α → Bool) (l : List α) (x : α) :
    x ∈ l.filter p ↔ x ∈ l ∧ p x = true := List.mem_filter

/-- Alias na `List.mem_map` — bo w `hmem` kształt `∃ x, x ∈ s ∧ f x = z` musi się zgadzać co do joty. -/
theorem mem_map_iff {α β : Type _} (f : α → β) (l : List α) (z : β) :
    z ∈ l.map f ↔ ∃ x, x ∈ l ∧ f x = z := List.mem_map

/-- Alias na `List.length_map`. -/
theorem length_map {α β : Type _} (f : α → β) (l : List α) :
    (l.map f).length = l.length := List.length_map f


/-! ## (L4) NARZĘDZIE GŁÓWNE — rozbiór listy docelowej na dwa obrazy + napływ.

  Rdzeń całej sekcji: `length_split3_mem'`.  Wszystkie pozostałe warianty
  (`'`, bez `'`, `2`, `1`) są JEGO wnioskami — jedno miejsce do sprawdzenia.

  ⚠️ Uwaga do wersji BEZ primu: założenie `hfg : ∀ x y, f x ≠ g y` jest GLOBALNE,
  a wtedy `hs` (rozłączność `s₁`,`s₂`) jest ZBĘDNE — trzymam je tylko dlatego,
  że taka jest zamówiona sygnatura.  Przy `f = g` `hfg` jest FAŁSZYWE
  (dałoby `f x ≠ f x`), więc dla „ta sama funkcja, dwie rozłączne listy"
  używaj wersji z primem (`hdisj` ograniczone do elementów list). -/

/-- **L4 — rdzeń.**  `dst` bez powtórzeń = obraz `s₁` przez `f` ⊍ obraz `s₂` przez `g` ⊍ `extra`.
    Injektywność wymagana TYLKO na elementach odpowiednich list. -/
theorem length_split3_mem' {α β : Type _}
    (dst : List β) (s₁ s₂ : List α) (extra : List β) (f g : α → β)
    (hdst : dst.Nodup) (h₁ : s₁.Nodup) (h₂ : s₂.Nodup) (hex : extra.Nodup)
    (hf : ∀ x y, x ∈ s₁ → y ∈ s₁ → f x = f y → x = y)
    (hg : ∀ x y, x ∈ s₂ → y ∈ s₂ → g x = g y → x = y)
    (hdisj : ∀ x y, x ∈ s₁ → y ∈ s₂ → f x ≠ g y)
    (hex_f : ∀ x z, x ∈ s₁ → z ∈ extra → f x ≠ z)
    (hex_g : ∀ x z, x ∈ s₂ → z ∈ extra → g x ≠ z)
    (hmem : ∀ z, z ∈ dst ↔ ((∃ x, x ∈ s₁ ∧ f x = z) ∨ (∃ x, x ∈ s₂ ∧ g x = z) ∨ z ∈ extra)) :
    dst.length = s₁.length + s₂.length + extra.length := by
  have hn2 : ((s₂.map g) ++ extra).Nodup := by
    refine nodup_append_of_disjoint _ _ (nodup_map_mem_of_inj g s₂ hg h₂) hex ?_
    intro z hz hze
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact hex_g x _ hx hze rfl
  have hn : ((s₁.map f) ++ ((s₂.map g) ++ extra)).Nodup := by
    refine nodup_append_of_disjoint _ _ (nodup_map_mem_of_inj f s₁ hf h₁) hn2 ?_
    intro z hz hzr
    rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
    rcases List.mem_append.mp hzr with hzr | hzr
    · rcases List.mem_map.mp hzr with ⟨y, hy, hgy⟩
      exact hdisj x y hx hy hgy.symm
    · exact hex_f x _ hx hzr rfl
  have hiff : ∀ z, z ∈ dst ↔ z ∈ (s₁.map f) ++ ((s₂.map g) ++ extra) := by
    intro z
    rw [List.mem_append, List.mem_append, List.mem_map, List.mem_map]
    exact hmem z
  rw [length_eq_of_nodup_mem_iff' dst _ hdst hn hiff, List.length_append, List.length_append,
      List.length_map, List.length_map, Nat.add_assoc]

/-- **L4′.**  Wersja z injektywnością globalną i rozłącznością OBRAZÓW (`hdisj`). -/
theorem length_split3' {α β : Type _} [DecidableEq β]
    (dst : List β) (s₁ s₂ : List α) (extra : List β) (f g : α → β)
    (hdst : dst.Nodup) (h₁ : s₁.Nodup) (h₂ : s₂.Nodup) (hex : extra.Nodup)
    (hf : ∀ x y, f x = f y → x = y) (hg : ∀ x y, g x = g y → x = y)
    (hdisj : ∀ x y, x ∈ s₁ → y ∈ s₂ → f x ≠ g y)
    (hex_f : ∀ x z, x ∈ s₁ → z ∈ extra → f x ≠ z)
    (hex_g : ∀ x z, x ∈ s₂ → z ∈ extra → g x ≠ z)
    (hmem : ∀ z, z ∈ dst ↔ ((∃ x, x ∈ s₁ ∧ f x = z) ∨ (∃ x, x ∈ s₂ ∧ g x = z) ∨ z ∈ extra)) :
    dst.length = s₁.length + s₂.length + extra.length :=
  length_split3_mem' dst s₁ s₂ extra f g hdst h₁ h₂ hex
    (fun x y _ _ h => hf x y h) (fun x y _ _ h => hg x y h)
    hdisj hex_f hex_g hmem

/-- **L4.**  Wersja zamówiona: `hfg` globalne + `hs` (nieużywane, patrz uwaga wyżej). -/
theorem length_split3 {α β : Type _} [DecidableEq β]
    (dst : List β) (s₁ s₂ : List α) (extra : List β) (f g : α → β)
    (hdst : dst.Nodup) (h₁ : s₁.Nodup) (h₂ : s₂.Nodup) (hex : extra.Nodup)
    (hf : ∀ x y, f x = f y → x = y) (hg : ∀ x y, g x = g y → x = y)
    (hfg : ∀ x y, f x ≠ g y)
    (hs : ∀ x, x ∈ s₁ → x ∈ s₂ → False)
    (hex_f : ∀ x z, x ∈ s₁ → z ∈ extra → f x ≠ z)
    (hex_g : ∀ x z, x ∈ s₂ → z ∈ extra → g x ≠ z)
    (hmem : ∀ z, z ∈ dst ↔ ((∃ x, x ∈ s₁ ∧ f x = z) ∨ (∃ x, x ∈ s₂ ∧ g x = z) ∨ z ∈ extra)) :
    dst.length = s₁.length + s₂.length + extra.length :=
  length_split3' dst s₁ s₂ extra f g hdst h₁ h₂ hex hf hg
    (fun x y _ _ => hfg x y) hex_f hex_g hmem

/-- **L4′ (dwa źródła), injektywność tylko na listach.** -/
theorem length_split2_mem' {α β : Type _}
    (dst : List β) (s₁ s₂ : List α) (f g : α → β)
    (hdst : dst.Nodup) (h₁ : s₁.Nodup) (h₂ : s₂.Nodup)
    (hf : ∀ x y, x ∈ s₁ → y ∈ s₁ → f x = f y → x = y)
    (hg : ∀ x y, x ∈ s₂ → y ∈ s₂ → g x = g y → x = y)
    (hdisj : ∀ x y, x ∈ s₁ → y ∈ s₂ → f x ≠ g y)
    (hmem : ∀ z, z ∈ dst ↔ ((∃ x, x ∈ s₁ ∧ f x = z) ∨ (∃ x, x ∈ s₂ ∧ g x = z))) :
    dst.length = s₁.length + s₂.length := by
  have h := length_split3_mem' dst s₁ s₂ [] f g hdst h₁ h₂ (by simp) hf hg hdisj
    (fun x z _ hz => by simp at hz) (fun x z _ hz => by simp at hz)
    (fun z => by rw [hmem z]; simp)
  simpa using h

/-- **L4′ (dwa źródła), injektywność globalna.**  TA WERSJA JEST WAŻNIEJSZA od `length_split2`:
    działa też, gdy `f = g` a `s₁`,`s₂` są dwiema rozłącznymi listami. -/
theorem length_split2' {α β : Type _} [DecidableEq β]
    (dst : List β) (s₁ s₂ : List α) (f g : α → β)
    (hdst : dst.Nodup) (h₁ : s₁.Nodup) (h₂ : s₂.Nodup)
    (hf : ∀ x y, f x = f y → x = y) (hg : ∀ x y, g x = g y → x = y)
    (hdisj : ∀ x y, x ∈ s₁ → y ∈ s₂ → f x ≠ g y)
    (hmem : ∀ z, z ∈ dst ↔ ((∃ x, x ∈ s₁ ∧ f x = z) ∨ (∃ x, x ∈ s₂ ∧ g x = z))) :
    dst.length = s₁.length + s₂.length :=
  length_split2_mem' dst s₁ s₂ f g hdst h₁ h₂
    (fun x y _ _ h => hf x y h) (fun x y _ _ h => hg x y h) hdisj hmem

/-- **L4 (dwa źródła), wersja zamówiona.**  `hs` nieużywane — `hfg` globalne już wystarcza. -/
theorem length_split2 {α β : Type _} [DecidableEq β]
    (dst : List β) (s₁ s₂ : List α) (f g : α → β)
    (hdst : dst.Nodup) (h₁ : s₁.Nodup) (h₂ : s₂.Nodup)
    (hf : ∀ x y, f x = f y → x = y) (hg : ∀ x y, g x = g y → x = y)
    (hfg : ∀ x y, f x ≠ g y)
    (hs : ∀ x, x ∈ s₁ → x ∈ s₂ → False)
    (hmem : ∀ z, z ∈ dst ↔ ((∃ x, x ∈ s₁ ∧ f x = z) ∨ (∃ x, x ∈ s₂ ∧ g x = z))) :
    dst.length = s₁.length + s₂.length :=
  length_split2' dst s₁ s₂ f g hdst h₁ h₂ hf hg (fun x y _ _ => hfg x y) hmem

/-- **L4 (jedno źródło).** -/
theorem length_split1 {α β : Type _} [DecidableEq β]
    (dst : List β) (s : List α) (f : α → β)
    (hdst : dst.Nodup) (hs : s.Nodup) (hf : ∀ x y, f x = f y → x = y)
    (hmem : ∀ z, z ∈ dst ↔ ∃ x, x ∈ s ∧ f x = z) :
    dst.length = s.length := by
  have hiff : ∀ z, z ∈ dst ↔ z ∈ s.map f := fun z => by rw [List.mem_map]; exact hmem z
  rw [length_eq_of_nodup_mem_iff' dst _ hdst (nodup_map_of_inj f hf s hs) hiff, List.length_map]

/-- **L4 (jedno źródło), injektywność tylko na liście.** -/
theorem length_split1_mem {α β : Type _}
    (dst : List β) (s : List α) (f : α → β)
    (hdst : dst.Nodup) (hs : s.Nodup)
    (hf : ∀ x y, x ∈ s → y ∈ s → f x = f y → x = y)
    (hmem : ∀ z, z ∈ dst ↔ ∃ x, x ∈ s ∧ f x = z) :
    dst.length = s.length := by
  have hiff : ∀ z, z ∈ dst ↔ z ∈ s.map f := fun z => by rw [List.mem_map]; exact hmem z
  rw [length_eq_of_nodup_mem_iff' dst _ hdst (nodup_map_mem_of_inj f s hf hs) hiff, List.length_map]

end A252864.LICZ
