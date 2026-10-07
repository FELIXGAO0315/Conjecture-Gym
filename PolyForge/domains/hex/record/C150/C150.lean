import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C150 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 42) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 3) (h3 : 2 * maps.p_i 5 ≥ maps.p_i 3) :
    2 * (maps.p_i 6 : ℤ) ≥ -(maps.p_i 4 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 12 := by
  have s1 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 12 := by
    by_cases hc1 : (6 : ℤ) ≤ (maps.p_i 5 : ℤ)
    · -- 1*p_5 >= 6
      have s2 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s3 : (maps.p_i 5 : ℤ) ≥ 6 := by linarith [hc1]
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 12 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*p_5 <= 5
      have s6 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s7 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s8 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 42 := by exact_mod_cast h1
      have s9 : 2 * (maps.p_i 5 : ℤ) ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h3
      have s10 : -(maps.p_i 5 : ℤ) ≥ -5 := by have hcc := hc1; omega
      have s11 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s12 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s13 : 3 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 6 * (maps.p_i 6 : ℤ) ≥ 34 := by linarith [s6, s7, s8, s9, s10, s11, s12]
      have s14 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 12 := by have hr := s13; omega
      linarith [s14]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
