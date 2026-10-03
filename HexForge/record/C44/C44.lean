import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C44 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : 2 * maps.p_i 5 ≥ 3 * maps.p_i 4) (h2 : maps.p_i 3 ≤ 2) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 40) :
    2 * (maps.p_i 6 : ℤ) ≥ (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 22 := by
  have s1 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 22 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 22 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 22 := by
            by_cases hc3 : (8 : ℤ) ≤ (maps.p_i 4 : ℤ)
            · -- 1*p_4 >= 8
              have s4 : (maps.p_i 4 : ℤ) ≥ 8 := by linarith [hc3]
              have s5 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s6 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h1
              have s7 : 2 ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
              have s8 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 22 := by linarith [s4, s5, s6, s7]
              linarith [s8]
            · -- 1*p_4 <= 7
              have s9 : 2 ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
              have s10 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s11 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s12 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 40 := by exact_mod_cast h3
              have s13 : -(maps.p_i 4 : ℤ) ≥ -7 := by have hcc := hc3; omega
              have s14 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s15 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s16 : 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 23 := by linarith [s10, s11, s9, s12, s13, s14, s15]
              have s17 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by have hr := s16; omega
              have s18 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 22 := by linarith [s9, s17]
              linarith [s18]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s19 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s20 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h1
          have s21 : 2 ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
          have s22 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 40 := by exact_mod_cast h3
          have s23 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s24 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s25 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 40 := by linarith [s19, s20, s21, s22, s23, s24]
          linarith [s25]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s26 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s27 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h1
      have s28 : 2 ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
      have s29 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 40 := by exact_mod_cast h3
      have s30 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s31 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s32 : -5 * (maps.p_i 3 : ℤ) + 10 * (maps.p_i 5 : ℤ) + 10 * (maps.p_i 6 : ℤ) ≥ 206 := by linarith [s26, s27, s28, s29, s30, s31]
      have s33 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 42 := by have hr := s32; omega
      linarith [s33]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
