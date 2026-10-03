import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C24 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 5 ≤ 4) (h2 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 54) (h3 : maps.p_i 3 ≥ 1) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 4 : ℤ) + 30 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 30 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 30 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 30 := by
            by_cases hc3 : (15 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 15
              have s4 : (maps.p_i 3 : ℤ) ≥ 15 := by linarith [hc3]
              have s5 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
              have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s7 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 30 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*p_3 <= 14
              have s8 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s9 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s10 : 4 ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h1
              have s11 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 54 := by exact_mod_cast h2
              have s12 : -(maps.p_i 3 : ℤ) ≥ -14 := by have hcc := hc3; omega
              have s13 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s14 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s15 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 88 := by linarith [s8, s9, s10, s11, s12, s13, s14]
              have s16 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 30 := by have hr := s15; omega
              linarith [s16]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s17 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
          have s18 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
          have s19 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
          have s20 : 4 ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h1
          have s21 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 54 := by exact_mod_cast h2
          have s22 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s23 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s24 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s25 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 152 := by linarith [s17, s18, s19, s20, s21, s22, s23, s24]
          have s26 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 51 := by have hr := s25; omega
          linarith [s26]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s27 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s28 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s29 : 4 ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h1
      have s30 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 54 := by exact_mod_cast h2
      have s31 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s32 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s33 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s34 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 154 := by linarith [s27, s28, s29, s30, s31, s32, s33]
      have s35 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 52 := by have hr := s34; omega
      linarith [s35]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
