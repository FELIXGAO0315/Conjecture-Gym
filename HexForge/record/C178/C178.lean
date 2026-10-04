import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C178 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : maps.p_i 5 = 0) (h3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 2) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + 8 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) - 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by
    by_cases hc1 : (7 : ℤ) ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*f_2 >= 7
      have s2 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s3 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
      have s4 : 2 ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h3
      have s5 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by linarith [hc1]
      have s6 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
        have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s5]
        have hj := (JucovicTheorem maps hM hf7).1
        linarith [hj]
      have s7 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
      have s8 : (maps.p_i 5 : ℤ) = 0 := by exact_mod_cast h2
      have s9 : 3 * (maps.p_i 6 : ℤ) ≥ 8 := by linarith [s3, s4, s6, s7, s8]
      have s10 : (maps.p_i 6 : ℤ) ≥ 3 := by have hr := s9; omega
      have s11 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s12 : 6 * (maps.p_i 3 : ℤ) + 3 * (maps.p_i 6 : ℤ) - 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 25 := by linarith [s2, s10, s4, s11, s7, s8]
      have s13 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) - 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 9 := by have hr := s12; omega
      linarith [s13]
    · -- 1*f_2 <= 6
      have s14 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) - 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by
        by_cases hc14 : (5 : ℤ) ≤ (maps.p_i 3 : ℤ)
        · -- 1*p_3 >= 5
          have s15 : (maps.p_i 3 : ℤ) ≥ 5 := by linarith [hc14]
          have s16 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
          have s17 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s18 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s19 : -∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ -6 := by have hcc := hc1; omega
          have s20 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s21 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) - 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by linarith [s15, s16, s17, s18, s19, s20]
          linarith [s21]
        · -- 1*p_3 <= 4
          have s22 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
          have s23 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s24 : -(maps.p_i 3 : ℤ) ≥ -4 := by have hcc := hc14; omega
          have s25 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s26 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
          have s27 : (maps.p_i 5 : ℤ) = 0 := by exact_mod_cast h2
          have s28 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) - 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by linarith [s22, s23, s24, s25, s26, s27]
          linarith [s28]
      linarith [s14]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
