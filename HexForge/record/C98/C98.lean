import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C98 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 16) (h2 : 2 * maps.p_i 5 ≥ 3 * maps.p_i 4) (h3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 3) :
    2 * (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - (maps.p_i 5 : ℤ) + 8 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 8 := by
    by_cases hc1 : (5 : ℤ) ≤ (maps.p_i 4 : ℤ)
    · -- 1*p_4 >= 5
      have s2 : (maps.p_i 3 : ℤ) ≥ 0 := by positivity
      have s3 : (maps.p_i 4 : ℤ) ≥ 5 := by linarith [hc1]
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : 2 * (maps.p_i 5 : ℤ) ≥ 3 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s6 : 4 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 4 * (maps.p_i 6 : ℤ) ≥ 15 := by linarith [s2, s3, s4, s5]
      have s7 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s6; omega
      linarith [s7]
    · -- 1*p_4 <= 4
      have s8 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s9 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s10 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 16 := by exact_mod_cast h1
      have s11 : -(maps.p_i 4 : ℤ) ≥ -4 := by have hcc := hc1; omega
      have s12 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s13 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s14 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 8 := by linarith [s8, s9, s10, s11, s12, s13]
      linarith [s14]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
