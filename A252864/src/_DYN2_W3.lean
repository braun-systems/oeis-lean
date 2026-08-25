import «_DYN2_Wiersze»
namespace A252864.DYN2
open A252864.Tree A252864.Seq

/-- **WIERSZ `j = 3` TWIERDZENIA `[R3]`:** `n₄′ = n₃`. -/
theorem row3 (n : Nat) (hn : 1 ≤ n) : vv klR n 3 = vv klR (n-1) 2 := by
  unfold vv
  refine LICZ.length_split1 _ _ childA
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup n))
    (LICZ.nodup_filter _ _ (Bfs.gen_nodup (n-1))) childA_inj ?_
  intro z
  rw [LICZ.mem_filter_iff]
  rw [row3_mem n hn z]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, (LICZ.mem_filter_iff _ _ _).mpr hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, (LICZ.mem_filter_iff _ _ _).mp hq, rfl⟩
end A252864.DYN2
