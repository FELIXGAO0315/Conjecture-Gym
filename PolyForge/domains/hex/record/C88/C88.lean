import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C88 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 32) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 4) (h3 : 3 * maps.p_i 5 ≥ 2 * maps.p_i 3) :
    (maps.p_i 6 : ℤ) ≥ -(maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) + 12 := by
  have s1 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
  have s2 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
  have s3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 32 := by exact_mod_cast h1
  have s4 : 4 ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h2
  have s5 : 3 * (maps.p_i 5 : ℤ) ≥ 2 * (maps.p_i 3 : ℤ) := by exact_mod_cast h3
  have s6 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  have s7 : 5 * (maps.p_i 4 : ℤ) + 5 * (maps.p_i 5 : ℤ) + 5 * (maps.p_i 6 : ℤ) ≥ 56 := by linarith [s1, s2, s3, s4, s5, s6]
  have s8 : (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ 12 := by have hr := s7; omega
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s8, hFaceZ]
