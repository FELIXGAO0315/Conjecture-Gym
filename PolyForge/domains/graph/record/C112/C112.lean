import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C112 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 4) (hn2 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0) :
    -(G.maxDegree : ℤ) + 2 * (G.minDegree : ℤ) - 2 * (G.indepNum : ℤ) ≤ 2 := by
  have s1 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s3, s4]
      have s6 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int G (by omega)
        linarith [hw]
      have s7 : -(G.vertexCoverNum.toNat : ℤ) ≥ -4 := by linarith [hn1]
      have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int G (by omega)
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s10 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -2 := by linarith [s2, s6, s7, s8, s9]
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        linarith [hw]
      have s12 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s13 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -2 := by linarith [s11, s12, s13, s14]
      linarith [s15]
  linarith [s1]
