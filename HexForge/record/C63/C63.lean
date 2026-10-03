import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C63 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 55) (h2 : maps.p_i 4 ≥ maps.p_i 5) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 4 : ℤ) + 28 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by
        by_cases hc2 : (14 : ℤ) ≤ (maps.p_i 4 : ℤ)
        · -- 1*p_4 >= 14
          have s3 : (maps.p_i 3 : ℤ) ≥ 0 := by positivity
          have s4 : (maps.p_i 4 : ℤ) ≥ 14 := by linarith [hc2]
          have s5 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s6 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*p_4 <= 13
          have s7 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by
            by_cases hc7 : (1 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 1
              have s8 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s9 : (maps.p_i 3 : ℤ) ≥ 1 := by linarith [hc7]
              have s10 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s11 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 55 := by exact_mod_cast h1
              have s12 : (maps.p_i 4 : ℤ) ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h2
              have s13 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s14 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s15 : 10 * (maps.p_i 3 : ℤ) + 10 * (maps.p_i 4 : ℤ) + 5 * (maps.p_i 6 : ℤ) ≥ 136 := by linarith [s8, s9, s10, s11, s12, s13, s14]
              have s16 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by have hr := s15; omega
              linarith [s16]
            · -- 1*p_3 <= 0
              have s17 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s18 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 55 := by exact_mod_cast h1
              have s19 : (maps.p_i 4 : ℤ) ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h2
              have s20 : -(maps.p_i 4 : ℤ) ≥ -13 := by have hcc := hc2; omega
              have s21 : -(maps.p_i 3 : ℤ) ≥ 0 := by have hcc := hc7; omega
              have s22 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s23 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s24 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by linarith [s17, s18, s19, s20, s21, s22, s23]
              linarith [s24]
          linarith [s7]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s25 : (maps.p_i 3 : ℤ) ≥ 0 := by positivity
      have s26 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 55 := by exact_mod_cast h1
      have s27 : (maps.p_i 4 : ℤ) ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h2
      have s28 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s29 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s30 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 53 := by linarith [s25, s26, s27, s28, s29]
      linarith [s30]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
