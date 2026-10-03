import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C3 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 8) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 6) (h3 : 2 * maps.p_i 3 ≥ 2 * maps.p_i 5) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 4 : ℤ) + 8 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s3 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc1]
      have s6 : 2 * (maps.p_i 3 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h3
      have s7 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s8 : 4 * (maps.p_i 3 : ℤ) + 4 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 15 := by linarith [s2, s3, s4, s5, s6, s7]
      have s9 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s8; omega
      linarith [s9]
    · -- 1*sum_pk_after_p6 <= 2
      have s10 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
        by_cases hc10 : (4 : ℤ) ≤ (maps.p_i 3 : ℤ)
        · -- 1*p_3 >= 4
          have s11 : (maps.p_i 3 : ℤ) ≥ 4 := by linarith [hc10]
          have s12 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
          have s13 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s14 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by linarith [s11, s12, s13]
          linarith [s14]
        · -- 1*p_3 <= 3
          have s15 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
          have s16 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s17 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by exact_mod_cast h1
          have s18 : 2 * (maps.p_i 3 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h3
          have s19 : -(maps.p_i 3 : ℤ) ≥ -3 := by have hcc := hc10; omega
          have s20 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s21 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s22 : 6 * (maps.p_i 3 : ℤ) + 6 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 22 := by linarith [s15, s16, s17, s18, s19, s20, s21]
          have s23 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s22; omega
          linarith [s23]
      linarith [s10]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
