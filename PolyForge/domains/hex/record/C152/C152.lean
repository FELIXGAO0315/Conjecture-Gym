import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C152 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 8) (h2 : maps.p_i 4 ≥ 3 * maps.p_i 3) :
    (maps.p_i 6 : ℤ) ≥ -(maps.p_i 4 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 6 := by
  have s1 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 6 := by
    by_cases hc1 : (2 : ℤ) ≤ (maps.p_i 3 : ℤ)
    · -- 1*p_3 >= 2
      have s2 : (maps.p_i 3 : ℤ) ≥ 2 := by linarith [hc1]
      have s3 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
      have s6 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 6 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*p_3 <= 1
      have s7 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s8 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s9 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s10 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by exact_mod_cast h1
      have s11 : -(maps.p_i 3 : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s12 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s13 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s14 : 3 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 16 := by linarith [s7, s8, s9, s10, s11, s12, s13]
      have s15 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 6 := by have hr := s14; omega
      linarith [s15]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
