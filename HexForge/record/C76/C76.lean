import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C76 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 53) (h2 : 3 * maps.p_i 4 ≥ 3 * maps.p_i 3) (h3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 3) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 4 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 20 := by
  have s1 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 20 := by
    by_cases hc1 : (10 : ℤ) ≤ (maps.p_i 3 : ℤ)
    · -- 1*p_3 >= 10
      have s2 : (maps.p_i 3 : ℤ) ≥ 10 := by linarith [hc1]
      have s3 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : 3 * (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 3 : ℤ) := by exact_mod_cast h2
      have s6 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 20 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*p_3 <= 9
      have s7 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s8 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s9 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s10 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 53 := by exact_mod_cast h1
      have s11 : -(maps.p_i 3 : ℤ) ≥ -9 := by have hcc := hc1; omega
      have s12 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s13 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s14 : 6 * (maps.p_i 4 : ℤ) + 6 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 58 := by linarith [s7, s8, s9, s10, s11, s12, s13]
      have s15 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 20 := by have hr := s14; omega
      linarith [s15]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
