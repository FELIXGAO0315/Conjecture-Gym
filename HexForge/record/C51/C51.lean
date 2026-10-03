import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C51 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 3 ≤ 2) (h2 : maps.p_i 5 ≥ 2 * maps.p_i 4) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 14) :
    (maps.p_i 6 : ℤ) ≥ (maps.p_i 4 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 9 := by
  have s1 : (maps.p_i 5 : ℤ) ≥ 2 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
  have s2 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
  have s3 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
  have s4 : 2 ≥ (maps.p_i 3 : ℤ) := by exact_mod_cast h1
  have s5 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 14 := by exact_mod_cast h3
  have s6 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
    have he := Juc_EulerFormula maps hM
    linear_combination he
  have s7 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  have s8 : 7 * (maps.p_i 5 : ℤ) + 7 * (maps.p_i 6 : ℤ) ≥ 36 := by linarith [s2, s3, s4, s1, s5, s6, s7]
  have s9 : (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 6 := by have hr := s8; omega
  have s10 : 14 * (maps.p_i 5 : ℤ) + 7 * (maps.p_i 6 : ℤ) ≥ 72 := by linarith [s2, s3, s4, s1, s5, s6, s7]
  have s11 : 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 11 := by have hr := s10; omega
  have s12 : -2 * (maps.p_i 4 : ℤ) + 4 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 17 := by linarith [s1, s9, s11]
  have s13 : -(maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 9 := by have hr := s12; omega
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s13, hFaceZ]
