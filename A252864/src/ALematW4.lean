/-
  A252864 — ALematW4.lean.  MONETA `v₁ = φ = (1,0)`.

  To jest `[W4]` z `LEM_A_wstecz.md` (LIPSCHITZ W KIERUNKU `φ`).

  🔑 I to jest zarazem CAŁE `[B4]` z `LEM_B_dolne.md` — co jest niezauważonym
  uproszczeniem: `[B4.1]` („jeśli jakaś optymalna reprezentacja ma `d₀ ≥ 1`, to
  `ℓ(c+1,d−1) ≤ ℓ(c,d)`") plus `[B4.2]` („przesłanka ⟺ `χ_A(c,d−1)`") razem
  dają dokładnie `ℓ(c+1, d−1) ≤ ℓ(c, d−1) + 1`, czyli `[W4]`.
  Dwaj agenci napisali w sierpniu to samo zdanie w dwóch plikach, każdy innym dowodem.
-/
import ALematRep

namespace A252864.ALemat

/-- Dodanie monety `v₁ = φ`: `d₁ += 1`. -/
def addv1 : List Nat → List Nat
  | []       => [0,1]
  | d0 :: ds => d0 :: bump ds

theorem val_addv1 (ds : List Nat) : val (addv1 ds) = ((val ds).1 + 1, (val ds).2) := by
  cases ds with
  | nil => simp [addv1, val]
  | cons d0 ds =>
    simp only [addv1, val, val_bump]
    simp
    omega

/-- `d₀`-współrzędna dodatnia wymusza stopień `≥ 1` — bo `F₀ = 0`
    (`[W1.1]`: `c = Σ dᵢ Fᵢ`, a `v₀ = (0,1)` nie wnosi nic do pierwszej współrzędnej). -/
theorem deg_pos (ds : List Nat) (h : 1 ≤ (val ds).1) : 1 ≤ deg ds := by
  cases ds with
  | nil => simp [val] at h
  | cons d0 ds =>
    have hz : isZeroL ds = false := by
      cases hzz : isZeroL ds with
      | false => rfl
      | true =>
        exfalso
        have hv := isZeroL_val hzz
        have key : (val (d0 :: ds)).1 = (val ds).1 + (val ds).2 := rfl
        rw [key, hv] at h
        simp at h
    simp [deg, hz]

theorem cost_addv1 (ds : List Nat) (h : 1 ≤ deg ds) : cost (addv1 ds) = cost ds + 1 := by
  cases ds with
  | nil => simp [deg] at h
  | cons d0 ds =>
    have hz : isZeroL ds = false := by
      cases hzz : isZeroL ds with
      | false => rfl
      | true => exfalso; simp [deg, hzz] at h
    have h1 : deg (d0 :: ds) = 1 + deg ds := by simp [deg, hz]
    have h2 : deg (d0 :: bump ds) = 1 + deg ds := by
      simp [deg, isZeroL_bump, deg_bump]
    simp only [addv1, cost, List.sum_cons, sum_bump, h1, h2]
    omega

/-- **`[W4]` LIPSCHITZ (= `[B4]`).**  `ℓ(x+1, y) ≤ ℓ(x, y) + 1` dla `x ≥ 1`. -/
theorem ell_add_phi1 (x y : Nat) (hx : 1 ≤ x) : ell (x+1) y ≤ ell x y + 1 := by
  obtain ⟨ds, hv, hc⟩ := exists_rep x y
  have hf : 1 ≤ (val ds).1 := by rw [hv]; simpa using hx
  have hd : 1 ≤ deg ds := deg_pos ds hf
  have h1 := ell_le_cost (addv1 ds)
  rw [val_addv1, hv] at h1
  rw [cost_addv1 ds hd] at h1
  simp only at h1
  omega

/-! ### `[B4]` w postaci, w jakiej używa jej `[B5]` -/

/-- `χ_A(c, d−1)` (czyli `ℓ(c,d) = ℓ(c,d−1)+1`) pociąga `ℓ(c+1, d−1) ≤ ℓ(c,d)`.
    W prozie `[B4.1]`+`[B4.2]`; tutaj jednolinijkowy wniosek z `[W4]`. -/
theorem B4_move (c d : Nat) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hchi : ell c d = ell c (d-1) + 1) : ell (c+1) (d-1) ≤ ell c d := by
  have := ell_add_phi1 c (d-1) hc
  omega

end A252864.ALemat
