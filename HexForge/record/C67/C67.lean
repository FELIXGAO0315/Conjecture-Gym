import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C67 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 43) (h2 : 2 * maps.p_i 3 ≥ maps.p_i 4) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 12 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by
            by_cases hc3 : (6 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 6
              have s4 : (maps.p_i 3 : ℤ) ≥ 6 := by linarith [hc3]
              have s5 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
              have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s7 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*p_3 <= 5
              have s8 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s9 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 43 := by exact_mod_cast h1
              have s10 : 2 * (maps.p_i 3 : ℤ) ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h2
              have s11 : -(maps.p_i 3 : ℤ) ≥ -5 := by have hcc := hc3; omega
              have s12 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s13 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s14 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 15 := by linarith [s8, s9, s10, s11, s12, s13]
              linarith [s14]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s15 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s16 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 43 := by exact_mod_cast h1
          have s17 : 2 * (maps.p_i 3 : ℤ) ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h2
          have s18 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s19 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc2]
          have s20 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
            have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s19]
            have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
            have hb := Barnette_P6Bound maps hM hm6 hsum7
            linarith [hb]
          have s21 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s22 : 14 * (maps.p_i 3 : ℤ) + 14 * (maps.p_i 5 : ℤ) + 7 * (maps.p_i 6 : ℤ) ≥ 198 := by linarith [s15, s16, s17, s18, s20, s21]
          have s23 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 29 := by have hr := s22; omega
          linarith [s23]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s24 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s25 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s26 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 43 := by exact_mod_cast h1
      have s27 : 2 * (maps.p_i 3 : ℤ) ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s28 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s29 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s30 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 82 := by linarith [s24, s25, s26, s27, s28, s29]
      have s31 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 28 := by have hr := s30; omega
      linarith [s31]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
