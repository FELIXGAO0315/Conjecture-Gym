import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C50 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 54) (h2 : 3 * maps.p_i 4 ≥ maps.p_i 3) :
    2 * (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) + 10 := by
  have s1 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 10 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 10 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 10 := by
            by_cases hc3 : (14 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 14
              have s4 : (maps.p_i 3 : ℤ) ≥ 14 := by linarith [hc3]
              have s5 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
              have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s7 : 3 * (maps.p_i 4 : ℤ) ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
              have s8 : 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 6 * (maps.p_i 6 : ℤ) ≥ 28 := by linarith [s4, s5, s6, s7]
              have s9 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 10 := by have hr := s8; omega
              linarith [s9]
            · -- 1*p_3 <= 13
              have s10 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s11 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s12 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 54 := by exact_mod_cast h1
              have s13 : 3 * (maps.p_i 4 : ℤ) ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
              have s14 : -(maps.p_i 3 : ℤ) ≥ -13 := by have hcc := hc3; omega
              have s15 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s16 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s17 : 12 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 12 * (maps.p_i 6 : ℤ) ≥ 55 := by linarith [s10, s11, s12, s13, s14, s15, s16]
              have s18 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 10 := by have hr := s17; omega
              linarith [s18]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s19 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 37 := by
            by_cases hc19 : (23 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 23
              have s20 : (maps.p_i 3 : ℤ) ≥ 23 := by linarith [hc19]
              have s21 : 3 * (maps.p_i 4 : ℤ) ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
              have s22 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
              have s23 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc2]
              have s24 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
                have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s23]
                have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
                have hb := Barnette_P6Bound maps hM hm6 hsum7
                linarith [hb]
              have s25 : 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 6 * (maps.p_i 6 : ℤ) ≥ 109 := by linarith [s20, s21, s22, s24]
              have s26 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 37 := by have hr := s25; omega
              linarith [s26]
            · -- 1*p_3 <= 22
              have s27 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s28 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 54 := by exact_mod_cast h1
              have s29 : 3 * (maps.p_i 4 : ℤ) ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
              have s30 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
              have s31 : -(maps.p_i 3 : ℤ) ≥ -22 := by have hcc := hc19; omega
              have s32 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s33 : 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 6 * (maps.p_i 6 : ℤ) ≥ 109 := by linarith [s27, s28, s29, s30, s31, s32]
              have s34 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 37 := by have hr := s33; omega
              linarith [s34]
          linarith [s19]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s35 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 34 := by
        by_cases hc35 : (29 : ℤ) ≤ (maps.p_i 3 : ℤ)
        · -- 1*p_3 >= 29
          have s36 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
          have s37 : (maps.p_i 3 : ℤ) ≥ 29 := by linarith [hc35]
          have s38 : 3 * (maps.p_i 4 : ℤ) ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
          have s39 : 3 * (maps.p_i 4 : ℤ) ≥ 29 := by linarith [s37, s38]
          have s40 : (maps.p_i 4 : ℤ) ≥ 10 := by have hr := s39; omega
          have s41 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s42 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s43 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 54 := by exact_mod_cast h1
          have s44 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
            have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s43]
            have hj := (JucovicTheorem maps hM hf7).1
            linarith [hj]
          have s45 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s46 : 10 * (maps.p_i 4 : ℤ) + 5 * (maps.p_i 5 : ℤ) + 10 * (maps.p_i 6 : ℤ) ≥ 167 := by linarith [s36, s37, s40, s41, s42, s44, s45]
          have s47 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 34 := by have hr := s46; omega
          linarith [s47]
        · -- 1*p_3 <= 28
          have s48 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s49 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 54 := by exact_mod_cast h1
          have s50 : 3 * (maps.p_i 4 : ℤ) ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
          have s51 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s52 : -(maps.p_i 3 : ℤ) ≥ -28 := by have hcc := hc35; omega
          have s53 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s54 : 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 6 * (maps.p_i 6 : ℤ) ≥ 100 := by linarith [s48, s49, s50, s51, s52, s53]
          have s55 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 34 := by have hr := s54; omega
          linarith [s55]
      linarith [s35]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
