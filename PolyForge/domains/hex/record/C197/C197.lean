import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C197 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 47) (h2 : maps.p_i 5 ≤ 3) (h3 : 2 * maps.p_i 3 ≥ maps.p_i 4) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 9 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) - (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by
    by_cases hc1 : (11 : ℤ) ≤ (maps.p_i 4 : ℤ)
    · -- 1*p_4 >= 11
      have s2 : (maps.p_i 4 : ℤ) ≥ 11 := by linarith [hc1]
      have s3 : 2 * (maps.p_i 3 : ℤ) ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h3
      have s4 : 2 * (maps.p_i 3 : ℤ) ≥ 11 := by linarith [s2, s3]
      have s5 : (maps.p_i 3 : ℤ) ≥ 6 := by have hr := s4; omega
      have s6 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s7 : 3 ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h2
      have s8 : 2 * (maps.p_i 3 : ℤ) - (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by linarith [s5, s6, s7]
      linarith [s8]
    · -- 1*p_4 <= 10
      have s9 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s10 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s11 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 47 := by exact_mod_cast h1
      have s12 : 3 ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h2
      have s13 : -(maps.p_i 4 : ℤ) ≥ -10 := by have hcc := hc1; omega
      have s14 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s15 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s16 : 4 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 17 := by linarith [s9, s10, s11, s12, s13, s14, s15]
      have s17 : 2 * (maps.p_i 3 : ℤ) - (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by have hr := s16; omega
      linarith [s17]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
