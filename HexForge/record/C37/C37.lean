import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C37 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 7) (h2 : maps.p_i 5 ≥ 3 * maps.p_i 4) (h3 : maps.p_i 5 ≥ 1) :
    (maps.p_i 6 : ℤ) ≥ -(maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 8 := by
  have s1 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
            by_cases hc3 : (1 : ℤ) ≤ (maps.p_i 4 : ℤ)
            · -- 1*p_4 >= 1
              have s4 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s5 : (maps.p_i 4 : ℤ) ≥ 1 := by linarith [hc3]
              have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s7 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by linarith [hc2]
              have s8 : (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
              have s9 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s10 : 3 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 29 := by linarith [s4, s5, s6, s7, s8, s9]
              have s11 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by have hr := s10; omega
              linarith [s11]
            · -- 1*p_4 <= 0
              have s12 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s13 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
              have s14 : (maps.p_i 5 : ℤ) ≥ 1 := by exact_mod_cast h3
              have s15 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s16 : -(maps.p_i 4 : ℤ) ≥ 0 := by have hcc := hc3; omega
              have s17 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by exact_mod_cast h1
              have s18 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
                have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s17]
                have hj := (JucovicTheorem maps hM hf7).1
                linarith [hj]
              have s19 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s20 : 6 * (maps.p_i 3 : ℤ) + 12 * (maps.p_i 5 : ℤ) + 6 * (maps.p_i 6 : ℤ) ≥ 43 := by linarith [s12, s13, s14, s15, s16, s18, s19]
              have s21 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s20; omega
              linarith [s21]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s22 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
          have s23 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
          have s24 : (maps.p_i 5 : ℤ) ≥ 1 := by exact_mod_cast h3
          have s25 : (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
          have s26 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s27 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by exact_mod_cast h1
          have s28 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
            have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s27]
            have hj := (JucovicTheorem maps hM hf7).1
            linarith [hj]
          have s29 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s30 : 9 * (maps.p_i 3 : ℤ) + 18 * (maps.p_i 5 : ℤ) + 9 * (maps.p_i 6 : ℤ) ≥ 65 := by linarith [s22, s23, s24, s25, s26, s28, s29]
          have s31 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s30; omega
          linarith [s31]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s32 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by
        by_cases hc32 : (4 : ℤ) ≤ (maps.p_i 3 : ℤ)
        · -- 1*p_3 >= 4
          have s33 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by
            by_cases hc33 : (1 : ℤ) ≤ (maps.p_i 4 : ℤ)
            · -- 1*p_4 >= 1
              have s34 : (maps.p_i 3 : ℤ) ≥ 4 := by linarith [hc32]
              have s35 : (maps.p_i 4 : ℤ) ≥ 1 := by linarith [hc33]
              have s36 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s37 : (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
              have s38 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s34, s35, s36, s37]
              linarith [s38]
            · -- 1*p_4 <= 0
              have s39 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s40 : (maps.p_i 5 : ℤ) ≥ 1 := by exact_mod_cast h3
              have s41 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
              have s42 : (maps.p_i 3 : ℤ) ≥ 4 := by linarith [hc32]
              have s43 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s44 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by exact_mod_cast h1
              have s45 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
                have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s44]
                have hj := (JucovicTheorem maps hM hf7).1
                linarith [hj]
              have s46 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s47 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s48 : 6 * ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 49 := by linarith [s41, s42, s43, s40, s45, s46, s47]
              have s49 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 9 := by have hr := s48; omega
              have s50 : -(maps.p_i 4 : ℤ) ≥ 0 := by have hcc := hc33; omega
              have s51 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
              have s52 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s53 : 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 8 := by linarith [s51, s52, s50, s45]
              have s54 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 3 := by have hr := s53; omega
              have s55 : 4 * (maps.p_i 3 : ℤ) + 8 * (maps.p_i 5 : ℤ) + 4 * (maps.p_i 6 : ℤ) ≥ 33 := by linarith [s39, s40, s49, s50, s54, s46, s47]
              have s56 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by have hr := s55; omega
              linarith [s56]
          linarith [s33]
        · -- 1*p_3 <= 3
          have s57 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
          have s58 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
          have s59 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s60 : (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
          have s61 : -(maps.p_i 3 : ℤ) ≥ -3 := by have hcc := hc32; omega
          have s62 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by exact_mod_cast h1
          have s63 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
            have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s62]
            have hj := (JucovicTheorem maps hM hf7).1
            linarith [hj]
          have s64 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s65 : 7 * (maps.p_i 3 : ℤ) + 14 * (maps.p_i 5 : ℤ) + 7 * (maps.p_i 6 : ℤ) ≥ 57 := by linarith [s57, s58, s59, s60, s61, s63, s64]
          have s66 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by have hr := s65; omega
          linarith [s66]
      linarith [s32]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
