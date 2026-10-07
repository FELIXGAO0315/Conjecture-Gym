import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C43 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : 2 * maps.p_i 5 ≥ 3 * maps.p_i 4) (h2 : maps.p_i 3 ≤ 2) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 40) :
    2 * (maps.p_i 6 : ℤ) ≥ (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 22 := by
  have s1 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 22 := by
    by_cases hc1 : (8 : ℤ) ≤ (maps.p_i 4 : ℤ)
    · -- 1*p_4 >= 8
      have s2 : (maps.p_i 4 : ℤ) ≥ 8 := by linarith [hc1]
      have s3 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s4 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h1
      have s5 : 2 ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
      have s6 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 22 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*p_4 <= 7
      have s7 : 2 ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h2
      have s8 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s9 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s10 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 40 := by exact_mod_cast h3
      have s11 : -(maps.p_i 4 : ℤ) ≥ -7 := by have hcc := hc1; omega
      have s12 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s13 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s14 : 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 23 := by linarith [s8, s9, s7, s10, s11, s12, s13]
      have s15 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by have hr := s14; omega
      have s16 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 22 := by linarith [s7, s15]
      linarith [s16]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
