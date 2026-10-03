import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C68 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 53) (h2 : 3 * maps.p_i 4 ≥ 3 * maps.p_i 3) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 4 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 20 := by
  have s1 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 20 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 20 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 20 := by
            by_cases hc3 : (10 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 10
              have s4 : (maps.p_i 3 : ℤ) ≥ 10 := by linarith [hc3]
              have s5 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
              have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s7 : 3 * (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
              have s8 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 20 := by linarith [s4, s5, s6, s7]
              linarith [s8]
            · -- 1*p_3 <= 9
              have s9 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s10 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
              have s11 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s12 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 53 := by exact_mod_cast h1
              have s13 : -(maps.p_i 3 : ℤ) ≥ -9 := by have hcc := hc3; omega
              have s14 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s15 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s16 : 6 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 58 := by linarith [s9, s10, s11, s12, s13, s14, s15]
              have s17 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 20 := by have hr := s16; omega
              linarith [s17]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s18 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s19 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 53 := by exact_mod_cast h1
          have s20 : 3 * (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
          have s21 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s22 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s23 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 50 := by linarith [s18, s19, s20, s21, s22]
          linarith [s23]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s24 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s25 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 53 := by exact_mod_cast h1
      have s26 : 3 * (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
      have s27 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s28 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s29 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 51 := by linarith [s24, s25, s26, s27, s28]
      linarith [s29]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
