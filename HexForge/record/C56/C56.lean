import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C56 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : 2 * maps.p_i 3 ≥ 3 * maps.p_i 5) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 5) :
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
              have s8 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
              have s9 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s10 : 22 * (maps.p_i 3 : ℤ) + 22 * (maps.p_i 4 : ℤ) + 11 * (maps.p_i 6 : ℤ) ≥ 106 := by linarith [s4, s5, s6, s7, s8, s9]
              have s11 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by have hr := s10; omega
              linarith [s11]
            · -- 1*p_4 <= 0
              have s12 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
              have s13 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
              have s14 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by linarith [hc2]
              have s15 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
              have s16 : -(maps.p_i 4 : ℤ) ≥ 0 := by have hcc := hc3; omega
              have s17 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s18 : 11 * (maps.p_i 3 : ℤ) ≥ 48 := by linarith [s12, s13, s14, s15, s16, s17]
              have s19 : (maps.p_i 3 : ℤ) ≥ 5 := by have hr := s18; omega
              have s20 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s21 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s22 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s19, s20, s21]
              linarith [s22]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s23 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by
            by_cases hc23 : (5 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 5
              have s24 : (maps.p_i 3 : ℤ) ≥ 5 := by linarith [hc23]
              have s25 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s26 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s27 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s24, s25, s26]
              linarith [s27]
            · -- 1*p_3 <= 4
              have s28 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
              have s29 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
              have s30 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc2]
              have s31 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
              have s32 : -(maps.p_i 3 : ℤ) ≥ -4 := by have hcc := hc23; omega
              have s33 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s34 : 6 * (maps.p_i 4 : ℤ) ≥ 1 := by linarith [s28, s29, s30, s31, s32, s33]
              have s35 : (maps.p_i 4 : ℤ) ≥ 1 := by have hr := s34; omega
              have s36 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
              have s37 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
                have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s30]
                have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
                have hb := Barnette_P6Bound maps hM hm6 hsum7
                linarith [hb]
              have s38 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s39 : 2 * ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 19 := by linarith [s28, s29, s30, s37, s33, s38]
              have s40 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 10 := by have hr := s39; omega
              have s41 : -3 * (maps.p_i 5 : ℤ) ≥ -8 := by linarith [s31, s32]
              have s42 : -(maps.p_i 5 : ℤ) ≥ -2 := by have hr := s41; omega
              have s43 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 29 := by linarith [s28, s29, s35, s36, s40, s42, s33, s38]
              have s44 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by have hr := s43; omega
              linarith [s44]
          linarith [s23]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s45 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
        by_cases hc45 : (7 : ℤ) ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*f_2 >= 7
          have s46 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by
            by_cases hc46 : (5 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 5
              have s47 : (maps.p_i 3 : ℤ) ≥ 5 := by linarith [hc46]
              have s48 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s49 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s50 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 10 := by linarith [s47, s48, s49]
              linarith [s50]
            · -- 1*p_3 <= 4
              have s51 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s52 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
              have s53 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by linarith [hc45]
              have s54 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
                have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s53]
                have hj := (JucovicTheorem maps hM hf7).1
                linarith [hj]
              have s55 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
              have s56 : -(maps.p_i 3 : ℤ) ≥ -4 := by have hcc := hc46; omega
              have s57 : -3 * (maps.p_i 5 : ℤ) ≥ -8 := by linarith [s55, s56]
              have s58 : -(maps.p_i 5 : ℤ) ≥ -2 := by have hr := s57; omega
              have s59 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s60 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 26 := by linarith [s51, s52, s54, s58, s59]
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
              have s69 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
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
