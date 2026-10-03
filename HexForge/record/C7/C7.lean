import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C7 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 16) (h2 : 2 * maps.p_i 5 ≥ 3 * maps.p_i 4) (h3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 3) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - (maps.p_i 5 : ℤ) + 8 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
    by_cases hc1 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 4
      have s2 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
        by_cases hc2 : (5 : ℤ) ≤ (maps.p_i 4 : ℤ)
        · -- 1*p_4 >= 5
          have s3 : (maps.p_i 3 : ℤ) ≥ 0 := by positivity
          have s4 : (maps.p_i 4 : ℤ) ≥ 5 := by linarith [hc2]
          have s5 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s6 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
          have s7 : 4 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 15 := by linarith [s3, s4, s5, s6]
          have s8 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s7; omega
          linarith [s8]
        · -- 1*p_4 <= 4
          have s9 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
          have s10 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s11 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 16 := by exact_mod_cast h1
          have s12 : -(maps.p_i 4 : ℤ) ≥ -4 := by have hcc := hc2; omega
          have s13 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s14 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s15 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by linarith [s9, s10, s11, s12, s13, s14]
          linarith [s15]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 3
      have s16 : (maps.p_i 3 : ℤ) ≥ 0 := by positivity
      have s17 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s18 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 16 := by exact_mod_cast h1
      have s19 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s20 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s21 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s22 : 10 * (maps.p_i 3 : ℤ) + 5 * (maps.p_i 5 : ℤ) + 5 * (maps.p_i 6 : ℤ) ≥ 39 := by linarith [s16, s17, s18, s19, s20, s21]
      have s23 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s22; omega
      linarith [s23]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
