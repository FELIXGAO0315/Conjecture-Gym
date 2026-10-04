import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C191 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 10) (h2 : 3 * maps.p_i 5 ≥ 3 * maps.p_i 4) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 10 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by
    by_cases hc1 : (5 : ℤ) ≤ (maps.p_i 4 : ℤ)
    · -- 1*p_4 >= 5
      have s2 : (maps.p_i 3 : ℤ) ≥ 0 := by positivity
      have s3 : (maps.p_i 4 : ℤ) ≥ 5 := by linarith [hc1]
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : 3 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s6 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*p_4 <= 4
      have s7 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by
        by_cases hc7 : (1 : ℤ) ≤ (maps.p_i 3 : ℤ)
        · -- 1*p_3 >= 1
          have s8 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
          have s9 : (maps.p_i 3 : ℤ) ≥ 1 := by linarith [hc7]
          have s10 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s11 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 10 := by exact_mod_cast h1
          have s12 : 3 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
          have s13 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s14 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s15 : 10 * (maps.p_i 3 : ℤ) + 10 * (maps.p_i 5 : ℤ) + 5 * (maps.p_i 6 : ℤ) ≥ 46 := by linarith [s8, s9, s10, s11, s12, s13, s14]
          have s16 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by have hr := s15; omega
          linarith [s16]
        · -- 1*p_3 <= 0
          have s17 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
          have s18 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 10 := by exact_mod_cast h1
          have s19 : -(maps.p_i 4 : ℤ) ≥ -4 := by have hcc := hc1; omega
          have s20 : -(maps.p_i 3 : ℤ) ≥ 0 := by have hcc := hc7; omega
          have s21 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s22 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s23 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s17, s18, s19, s20, s21, s22]
          linarith [s23]
      linarith [s7]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
