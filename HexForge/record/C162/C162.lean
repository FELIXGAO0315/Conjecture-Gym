import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C162 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 3 ≥ 3) (h2 : 2 * maps.p_i 5 ≥ 3 * maps.p_i 3) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 14) :
    (maps.p_i 6 : ℤ) ≥ -(maps.p_i 4 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 12 := by
  have s1 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by
    by_cases hc1 : (4 : ℤ) ≤ (maps.p_i 3 : ℤ)
    · -- 1*p_3 >= 4
      have s2 : (maps.p_i 3 : ℤ) ≥ 4 := by linarith [hc1]
      have s3 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
      have s6 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*p_3 <= 3
      have s7 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s8 : (maps.p_i 3 : ℤ) ≥ 3 := by exact_mod_cast h1
      have s9 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
      have s10 : 2 * (maps.p_i 5 : ℤ) ≥ 9 := by linarith [s8, s9]
      have s11 : (maps.p_i 5 : ℤ) ≥ 5 := by have hr := s10; omega
      have s12 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s13 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 14 := by exact_mod_cast h3
      have s14 : -(maps.p_i 3 : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s15 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s16 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s17 : 3 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 34 := by linarith [s7, s11, s12, s13, s14, s15, s16]
      have s18 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by have hr := s17; omega
      linarith [s18]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
