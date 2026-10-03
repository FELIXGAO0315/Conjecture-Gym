import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C69 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : 3 * maps.p_i 4 ≥ 2 * maps.p_i 5) (h2 : maps.p_i 4 ≥ 3 * maps.p_i 3) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 43) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 4 : ℤ) + 16 := by
  have s1 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 16 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 16 := by
        by_cases hc2 : (4 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*sum_pk_after_p6 >= 4
          have s3 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 16 := by
            by_cases hc3 : (3 : ℤ) ≤ (maps.p_i 3 : ℤ)
            · -- 1*p_3 >= 3
              have s4 : (maps.p_i 3 : ℤ) ≥ 3 := by linarith [hc3]
              have s5 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s6 : (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
              have s7 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 18 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*p_3 <= 2
              have s8 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
              have s9 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
              have s10 : 3 * (maps.p_i 4 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
              have s11 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 43 := by exact_mod_cast h3
              have s12 : -(maps.p_i 3 : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s13 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
                have he := Juc_EulerFormula maps hM
                linear_combination he
              have s14 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
                have h := SimplyCon3ConnectedMap.face_split_agg maps hM
                have h2 := congrArg (Nat.cast : ℕ → ℤ) h
                push_cast at h2
                omega
              have s15 : 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 47 := by linarith [s8, s9, s10, s11, s12, s13, s14]
              have s16 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 16 := by have hr := s15; omega
              linarith [s16]
          linarith [s3]
        · -- 1*sum_pk_after_p6 <= 3
          have s17 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s18 : 3 * (maps.p_i 4 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
          have s19 : (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
          have s20 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 43 := by exact_mod_cast h3
          have s21 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s22 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s23 : 34 * (maps.p_i 4 : ℤ) + 17 * (maps.p_i 6 : ℤ) ≥ 480 := by linarith [s17, s18, s19, s20, s21, s22]
          have s24 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 29 := by have hr := s23; omega
          linarith [s24]
      linarith [s2]
    · -- 1*sum_pk_after_p6 <= 2
      have s25 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 30 := by
        by_cases hc25 : (15 : ℤ) ≤ (maps.p_i 4 : ℤ)
        · -- 1*p_4 >= 15
          have s26 : (maps.p_i 4 : ℤ) ≥ 15 := by linarith [hc25]
          have s27 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s28 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 30 := by linarith [s26, s27]
          linarith [s28]
        · -- 1*p_4 <= 14
          have s29 : 3 * (maps.p_i 4 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
          have s30 : (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
          have s31 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 43 := by exact_mod_cast h3
          have s32 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s33 : -(maps.p_i 4 : ℤ) ≥ -14 := by have hcc := hc25; omega
          have s34 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s35 : 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 88 := by linarith [s29, s30, s31, s32, s33, s34]
          have s36 : 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 30 := by have hr := s35; omega
          linarith [s36]
      linarith [s25]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
