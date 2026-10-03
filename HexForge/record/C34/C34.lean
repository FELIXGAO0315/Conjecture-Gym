import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C34 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 42) (h2 : maps.p_i 3 ≥ 3 * maps.p_i 4) :
    (maps.p_i 6 : ℤ) ≥ -(maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 12 := by
  have s1 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by
            by_cases hc3 : (4 : ℤ) ≤ (maps.p_i 4 : ℤ)
            · -- 1*p_4 >= 4
              have s4 : (maps.p_i 4 : ℤ) ≥ 4 := by linarith [hc3]
              have s5 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
              have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s7 : (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
              have s8 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by linarith [s4, s5, s6, s7]
              linarith [s8]
            · -- 1*p_4 <= 3
              have s9 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s10 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
              have s11 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s12 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 42 := by exact_mod_cast h1
              have s13 : -(maps.p_i 4 : ℤ) ≥ -3 := by have hcc := hc3; omega
              have s14 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s15 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s16 : 4 * (maps.p_i 3 : ℤ) + 8 * (maps.p_i 5 : ℤ) + 4 * (maps.p_i 6 : ℤ) ≥ 45 := by linarith [s9, s10, s11, s12, s13, s14, s15]
              have s17 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by have hr := s16; omega
              linarith [s17]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s18 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s19 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 42 := by exact_mod_cast h1
          have s20 : (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
          have s21 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s22 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc2]
          have s23 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
            have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s22]
            have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
            have hb := Barnette_P6Bound maps hM hm6 hsum7
            linarith [hb]
          have s24 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s25 : 11 * (maps.p_i 3 : ℤ) + 22 * (maps.p_i 5 : ℤ) + 11 * (maps.p_i 6 : ℤ) ≥ 349 := by linarith [s18, s19, s20, s21, s23, s24]
          have s26 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 32 := by have hr := s25; omega
          linarith [s26]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s27 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
      have s28 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s29 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 42 := by exact_mod_cast h1
      have s30 : (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s31 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s32 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
        have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s29]
        have hj := (JucovicTheorem maps hM hf7).1
        linarith [hj]
      have s33 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s34 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s35 : 31 * (maps.p_i 3 : ℤ) + 62 * (maps.p_i 5 : ℤ) + 31 * (maps.p_i 6 : ℤ) ≥ 1000 := by linarith [s27, s28, s29, s30, s31, s32, s33, s34]
      have s36 : (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 33 := by have hr := s35; omega
      linarith [s36]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
