import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C65 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 45) (h2 : maps.p_i 4 ≤ 1) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 28 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by
            by_cases hc3 : (14 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 14
              have s4 : (maps.p_i 3 : ℤ) ≥ 14 := by linarith [hc3]
              have s5 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
              have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s7 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*p_3 <= 13
              have s8 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s9 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 45 := by exact_mod_cast h1
              have s10 : 1 ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h2
              have s11 : -(maps.p_i 3 : ℤ) ≥ -13 := by have hcc := hc3; omega
              have s12 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s13 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s14 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by linarith [s8, s9, s10, s11, s12, s13]
              linarith [s14]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s15 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
          have s16 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
          have s17 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s18 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 45 := by exact_mod_cast h1
          have s19 : 1 ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h2
          have s20 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s21 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s22 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s23 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 136 := by linarith [s15, s16, s17, s18, s19, s20, s21, s22]
          have s24 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 46 := by have hr := s23; omega
          linarith [s24]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s25 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s26 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s27 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 45 := by exact_mod_cast h1
      have s28 : 1 ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s29 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s30 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s31 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s32 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 46 := by linarith [s25, s26, s27, s28, s29, s30, s31]
      linarith [s32]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
