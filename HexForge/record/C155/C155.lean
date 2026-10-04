import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C155 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 15) (h2 : 2 * maps.p_i 3 ≥ 3 * maps.p_i 4) :
    (maps.p_i 6 : ℤ) ≥ -(maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + 5 := by
  have s1 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 5 := by
    by_cases hc1 : (7 : ℤ) ≤ (maps.p_i 3 : ℤ)
    · -- 1*p_3 >= 7
      have s2 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 5 := by
        by_cases hc2 : (5 : ℤ) ≤ (maps.p_i 4 : ℤ)
        · -- 1*p_4 >= 5
          have s3 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
          have s4 : (maps.p_i 4 : ℤ) ≥ 5 := by linarith [hc2]
          have s5 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s6 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
          have s7 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 15 := by exact_mod_cast h1
          have s8 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
            have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s7]
            have hj := (JucovicTheorem maps hM hf7).1
            linarith [hj]
          have s9 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s10 : 12 * (maps.p_i 5 : ℤ) + 12 * (maps.p_i 6 : ℤ) + 12 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 49 := by linarith [s3, s4, s5, s6, s8, s9]
          have s11 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 5 := by have hr := s10; omega
          linarith [s11]
        · -- 1*p_4 <= 4
          have s12 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
          have s13 : (maps.p_i 3 : ℤ) ≥ 7 := by linarith [hc1]
          have s14 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s15 : -(maps.p_i 4 : ℤ) ≥ -4 := by have hcc := hc2; omega
          have s16 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 15 := by exact_mod_cast h1
          have s17 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
            have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s16]
            have hj := (JucovicTheorem maps hM hf7).1
            linarith [hj]
          have s18 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s19 : 6 * (maps.p_i 5 : ℤ) + 6 * (maps.p_i 6 : ℤ) + 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 25 := by linarith [s12, s13, s14, s15, s17, s18]
          have s20 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 5 := by have hr := s19; omega
          linarith [s20]
      linarith [s2]
    · -- 1*p_3 <= 6
      have s21 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 15 := by exact_mod_cast h1
      have s22 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s23 : -(maps.p_i 3 : ℤ) ≥ -6 := by have hcc := hc1; omega
      have s24 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s25 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 5 := by linarith [s21, s22, s23, s24]
      linarith [s25]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
