import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C9 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 4) (hn2 : (G.cliqueNum : ℤ) ≥ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (G.maxDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 7 := by
  have s1 : -(G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by
    by_cases hc1 : (4 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 4
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        linarith [hw]
      have s5 : (G.indepNum : ℤ) ≥ 4 := by have hcc := hc1; omega
      have s6 : (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s8 : -2 * (G.maxDegree : ℤ) + 4 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) ≥ 13 := by linarith [s2, s3, s4, s5, s6, s7]
      have s9 : -(G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by have hr := s8; omega
      linarith [s9]
    · -- 1*alpha <= 3
      have s10 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s11 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
      have s13 : (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s14 : -(G.indepNum : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s16 : -(G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s10, s11, s12, s13, s14, s15]
      linarith [s16]
  linarith [s1]
