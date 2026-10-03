import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C30 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 30) (h2 : maps.p_i 4 = 0) (h3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 3) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 22 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 22 := by
    by_cases hc1 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 4
      have s2 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 22 := by
        by_cases hc2 : (11 : ℤ) ≤ (maps.p_i 3 : ℤ)
        · -- 1*p_3 >= 11
          have s3 : (maps.p_i 3 : ℤ) ≥ 11 := by linarith [hc2]
          have s4 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s5 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s6 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 22 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*p_3 <= 10
          have s7 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
          have s8 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 30 := by exact_mod_cast h1
          have s9 : -(maps.p_i 3 : ℤ) ≥ -10 := by have hcc := hc2; omega
          have s10 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s11 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s12 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h2
          have s13 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 22 := by linarith [s7, s8, s9, s10, s11, s12]
          linarith [s13]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 3
      have s14 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
      have s15 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
      have s16 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s17 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 30 := by exact_mod_cast h1
      have s18 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s19 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s20 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s21 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h2
      have s22 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 32 := by linarith [s14, s15, s16, s17, s18, s19, s20, s21]
      linarith [s22]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
