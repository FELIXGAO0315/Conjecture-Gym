import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C33 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 2) (h2 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 52) (h3 : maps.p_i 5 ≤ 4) :
    2 * (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 4 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + 30 := by
  have s1 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
  have s2 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
  have s3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 52 := by exact_mod_cast h2
  have s4 : 4 ≥ (maps.p_i 5 : ℤ) := by exact_mod_cast h3
  have s5 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
    have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s3]
    have hj := (JucovicTheorem maps hM hf7).1
    linarith [hj]
  have s6 : 2 ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h1
  have s7 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
    have he := Juc_EulerFormula maps hM
    linear_combination he
  have s8 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  have s9 : 18 * (maps.p_i 4 : ℤ) + 18 * (maps.p_i 6 : ℤ) ≥ 236 := by linarith [s1, s2, s6, s3, s4, s5, s7, s8]
  have s10 : (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 14 := by have hr := s9; omega
  have s11 : 18 * (maps.p_i 4 : ℤ) + 18 * (maps.p_i 6 : ℤ) + 9 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 262 := by linarith [s1, s2, s3, s4, s5, s10, s7, s8]
  have s12 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 30 := by have hr := s11; omega
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s12, hFaceZ]
