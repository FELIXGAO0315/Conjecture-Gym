import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C149 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 57) (h2 : 3 * maps.p_i 3 ≥ maps.p_i 4) (h3 : maps.p_i 5 ≥ 2 * maps.p_i 3) :
    (maps.p_i 6 : ℤ) ≥ -(maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + 20 := by
  have s1 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 20 := by
    by_cases hc1 : (10 : ℤ) ≤ (maps.p_i 3 : ℤ)
    · -- 1*p_3 >= 10
      have s2 : (maps.p_i 3 : ℤ) ≥ 10 := by linarith [hc1]
      have s3 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s4 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
      have s5 : (maps.p_i 5 : ℤ) ≥ 2 * (maps.p_i 3 : ℤ) := by exact_mod_cast h3
      have s6 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 20 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*p_3 <= 9
      have s7 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 57 := by exact_mod_cast h1
      have s8 : 3 * (maps.p_i 3 : ℤ) ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s9 : -(maps.p_i 3 : ℤ) ≥ -9 := by have hcc := hc1; omega
      have s10 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s11 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 21 := by linarith [s7, s8, s9, s10]
      linarith [s11]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
