import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C4 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 15) :
    3 * (maps.p_i 6 : ℤ) ≥ -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) + 7 := by
  have s1 : -5 * ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
  have s2 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
  have s3 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
  have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
  have s5 : (maps.p_i 8 : ℤ) ≥ 0 := by positivity
  have s6 : (maps.p_i 9 : ℤ) ≥ 0 := by positivity
  have s7 : (maps.p_i 10 : ℤ) ≥ 0 := by positivity
  have s8 : ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
  have s9 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 15 := by exact_mod_cast h1
  have s10 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - (maps.p_i 7 : ℤ) - 2 * (maps.p_i 8 : ℤ) - 3 * (maps.p_i 9 : ℤ) - 4 * (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
    have he := Juc_EulerFormula maps hM
    have hw := SimplyCon3ConnectedMap.split_W maps hM
    linear_combination he + hw
  have s11 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - (maps.p_i 7 : ℤ) - (maps.p_i 8 : ℤ) - (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
    have h := SimplyCon3ConnectedMap.face_split maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  have s12 : 4 * (maps.p_i 3 : ℤ) + 4 * (maps.p_i 4 : ℤ) + 4 * (maps.p_i 5 : ℤ) + 12 * (maps.p_i 6 : ℤ) ≥ 27 := by linarith [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  have s13 : (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ 7 := by have hr := s12; omega
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s13, hFaceZ]
