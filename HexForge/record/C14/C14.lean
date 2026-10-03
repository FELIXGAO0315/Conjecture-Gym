import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C14 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 3 ≥ 2) (h2 : 2 * maps.p_i 3 ≥ 3 * maps.p_i 5) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 4 : ℤ) + 8 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by
            by_cases hc3 : (1 : ℤ) ≤ (maps.p_i 4 : ℤ)
            · -- 1*p_4 >= 1
              have s4 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s5 : (maps.p_i 4 : ℤ) ≥ 1 := by linarith [hc3]
              have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s7 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by linarith [hc2]
              have s8 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h2
              have s9 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s10 : 22 * (maps.p_i 3 : ℤ) + 22 * (maps.p_i 4 : ℤ) + 11 * (maps.p_i 6 : ℤ) ≥ 106 := by linarith [s4, s5, s6, s7, s8, s9]
              have s11 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by have hr := s10; omega
              linarith [s11]
            · -- 1*p_4 <= 0
              have s12 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s13 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by linarith [hc2]
              have s14 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h2
              have s15 : -(maps.p_i 4 : ℤ) ≥ 0 := by have hcc := hc3; omega
              have s16 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s17 : 11 * (maps.p_i 3 : ℤ) ≥ 48 := by linarith [s12, s13, s14, s15, s16]
              have s18 : (maps.p_i 3 : ℤ) ≥ 5 := by have hr := s17; omega
              have s19 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s20 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s21 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s18, s19, s20]
              linarith [s21]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s22 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by
            by_cases hc22 : (3 : ℤ) ≤ (maps.p_i 5 : ℤ)
            · -- 1*p_5 >= 3
              have s23 : (maps.p_i 5 : ℤ) ≥ 3 := by linarith [hc22]
              have s24 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h2
              have s25 : 2 * (maps.p_i 3 : ℤ) ≥ 9 := by linarith [s23, s24]
              have s26 : (maps.p_i 3 : ℤ) ≥ 5 := by have hr := s25; omega
              have s27 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s28 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s29 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s26, s27, s28]
              linarith [s29]
            · -- 1*p_5 <= 2
              have s30 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
              have s31 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
              have s32 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
              have s33 : -(maps.p_i 5 : ℤ) ≥ -2 := by have hcc := hc22; omega
              have s34 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc2]
              have s35 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
                have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s34]
                have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
                have hb := Barnette_P6Bound maps hM hm6 hsum7
                linarith [hb]
              have s36 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s37 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s38 : 2 * ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 19 := by linarith [s30, s31, s34, s35, s36, s37]
              have s39 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 10 := by have hr := s38; omega
              have s40 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s41 : 12 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 6 : ℤ) ≥ 1 := by linarith [s30, s31, s40, s32, s33, s35, s36]
              have s42 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 1 := by have hr := s41; omega
              have s43 : 10 * (maps.p_i 3 : ℤ) + 10 * (maps.p_i 4 : ℤ) + 5 * (maps.p_i 6 : ℤ) ≥ 47 := by linarith [s30, s31, s32, s33, s39, s42, s36, s37]
              have s44 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by have hr := s43; omega
              linarith [s44]
          linarith [s22]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s45 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
        by_cases hc45 : (7 : ℤ) ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*f_2 >= 7
          have s46 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by
            by_cases hc46 : (3 : ℤ) ≤ (maps.p_i 5 : ℤ)
            · -- 1*p_5 >= 3
              have s47 : (maps.p_i 5 : ℤ) ≥ 3 := by linarith [hc46]
              have s48 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h2
              have s49 : 2 * (maps.p_i 3 : ℤ) ≥ 9 := by linarith [s47, s48]
              have s50 : (maps.p_i 3 : ℤ) ≥ 5 := by have hr := s49; omega
              have s51 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s52 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s53 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s50, s51, s52]
              linarith [s53]
            · -- 1*p_5 <= 2
              have s54 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s55 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
              have s56 : -(maps.p_i 5 : ℤ) ≥ -2 := by have hcc := hc46; omega
              have s57 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by linarith [hc45]
              have s58 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
                have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s57]
                have hj := (JucovicTheorem maps hM hf7).1
                linarith [hj]
              have s59 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s60 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 26 := by linarith [s54, s55, s56, s58, s59]
              have s61 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by have hr := s60; omega
              linarith [s61]
          linarith [s46]
        · -- 1*f_2 <= 6
          have s62 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
            by_cases hc62 : (4 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 4
              have s63 : (maps.p_i 3 : ℤ) ≥ 4 := by linarith [hc62]
              have s64 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s65 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s66 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by linarith [s63, s64, s65]
              linarith [s66]
            · -- 1*p_3 <= 3
              have s67 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s68 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
              have s69 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h2
              have s70 : -(maps.p_i 3 : ℤ) ≥ -3 := by have hcc := hc62; omega
              have s71 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s72 : 2 * (maps.p_i 4 : ℤ) ≥ 1 := by linarith [s67, s68, s69, s70, s71]
              have s73 : (maps.p_i 4 : ℤ) ≥ 1 := by have hr := s72; omega
              have s74 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s75 : 22 * (maps.p_i 3 : ℤ) + 22 * (maps.p_i 4 : ℤ) + 11 * (maps.p_i 6 : ℤ) ≥ 82 := by linarith [s67, s73, s74, s68, s69, s71]
              have s76 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s75; omega
              linarith [s76]
          linarith [s62]
      linarith [s45]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
