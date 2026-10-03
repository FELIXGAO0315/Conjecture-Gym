import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C43 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 ≤ 3) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 3) (h3 : maps.p_i 3 ≥ maps.p_i 5) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) + 6 := by
  have s1 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
  have s2 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
  have s3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by exact_mod_cast h2
  have s4 : 3 ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h1
  have s5 : (maps.p_i 3 : ℤ) ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h3
  have s6 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
    have he := Juc_EulerFormula maps hM
    linear_combination he
  have s7 : 4 * (maps.p_i 3 : ℤ) ≥ 9 := by linarith [s1, s2, s3, s4, s5, s6]
  have s8 : (maps.p_i 3 : ℤ) ≥ 3 := by have hr := s7; omega
  have s9 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
  have s10 : 2 * (maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) ≥ 6 := by linarith [s8, s9]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s10, hFaceZ]
