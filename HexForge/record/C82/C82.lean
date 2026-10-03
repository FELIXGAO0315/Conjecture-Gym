import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C82 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 ≥ 2 * maps.p_i 5) (h2 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 46) :
    2 * (maps.p_i 6 : ℤ) ≥ -(maps.p_i 4 : ℤ) - 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + 18 := by
  have s1 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 18 := by
    by_cases hc1 : (21 : ℤ) ≤ (maps.p_i 3 : ℤ)
    · -- 1*p_3 >= 21
      have s2 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 18 := by
        by_cases hc2 : (17 : ℤ) ≤ (maps.p_i 4 : ℤ)
        · -- 1*p_4 >= 17
          have s3 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 18 := by
            by_cases hc3 : (9 : ℤ) ≤ (maps.p_i 5 : ℤ)
            · -- 1*p_5 >= 9
              have s4 : (maps.p_i 5 : ℤ) ≥ 9 := by linarith [hc3]
              have s5 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s6 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
              have s7 : (maps.p_i 4 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
              have s8 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 18 := by linarith [s4, s5, s6, s7]
              linarith [s8]
            · -- 1*p_5 <= 8
              have s9 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
              have s10 : (maps.p_i 3 : ℤ) ≥ 21 := by linarith [hc1]
              have s11 : (maps.p_i 4 : ℤ) ≥ 17 := by linarith [hc2]
              have s12 : -(maps.p_i 5 : ℤ) ≥ -8 := by have hcc := hc3; omega
              have s13 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 46 := by exact_mod_cast h2
              have s14 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
                have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s13]
                have hj := (JucovicTheorem maps hM hf7).1
                linarith [hj]
              have s15 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s16 : 3 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 6 : ℤ) + 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 52 := by linarith [s9, s10, s11, s12, s14, s15]
              have s17 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 18 := by have hr := s16; omega
              linarith [s17]
          linarith [s3]
        · -- 1*p_4 <= 16
          have s18 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
          have s19 : (maps.p_i 4 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
          have s20 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 46 := by exact_mod_cast h2
          have s21 : -(maps.p_i 4 : ℤ) ≥ -16 := by have hcc := hc2; omega
          have s22 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
            have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s20]
            have hj := (JucovicTheorem maps hM hf7).1
            linarith [hj]
          have s23 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s24 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s25 : 3 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 6 : ℤ) + 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 52 := by linarith [s18, s19, s20, s21, s22, s23, s24]
          have s26 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 18 := by have hr := s25; omega
          linarith [s26]
      linarith [s2]
    · -- 1*p_3 <= 20
      have s27 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s28 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
      have s29 : (maps.p_i 4 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
      have s30 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 46 := by exact_mod_cast h2
      have s31 : -(maps.p_i 3 : ℤ) ≥ -20 := by have hcc := hc1; omega
      have s32 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s33 : 3 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 6 : ℤ) + 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 52 := by linarith [s27, s28, s29, s30, s31, s32]
      have s34 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 18 := by have hr := s33; omega
      linarith [s34]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
