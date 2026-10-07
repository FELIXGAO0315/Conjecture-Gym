import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C4 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 1) (h2 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 48) (h3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≤ 55) :
    (maps.p_i 6 : ℤ) ≥ 2 * (maps.p_i 3 : ℤ) - (maps.p_i 5 : ℤ) - 51 := by
  have s1 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
  have s2 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
  have s3 : 1 ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h1
  have s4 : 55 ≥ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h3
  have s5 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 48 := by exact_mod_cast h2
  have s6 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
    have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s5]
    have hj := (JucovicTheorem maps hM hf7).1
    linarith [hj]
  have s7 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
  have s8 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
    have he := Juc_EulerFormula maps hM
    linear_combination he
  have s9 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  have s10 : -3 * (maps.p_i 3 : ℤ) ≥ -106 := by linarith [s1, s7, s2, s4, s6, s8, s9]
  have s11 : -(maps.p_i 3 : ℤ) ≥ -35 := by have hr := s10; omega
  have s12 : -8 * (maps.p_i 3 : ℤ) + 4 * (maps.p_i 5 : ℤ) + 4 * (maps.p_i 6 : ℤ) ≥ -207 := by linarith [s1, s2, s3, s4, s6, s11, s8, s9]
  have s13 : -2 * (maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) ≥ -51 := by have hr := s12; omega
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s13, hFaceZ]
