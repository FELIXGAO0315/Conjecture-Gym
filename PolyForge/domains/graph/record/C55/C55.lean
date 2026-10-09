import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C55 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 4) (hn2 : (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    (G.maxDegree : ℤ) ≥ -2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) + 10 := by
  have s1 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by
    by_cases hc1 : (4 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 4
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s4 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
      have s5 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int G (by omega)
        linarith [hw]
      have s6 : (G.indepNum : ℤ) ≥ 4 := by have hcc := hc1; omega
      have s7 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by linarith [s2, s3, s5, s6]
      linarith [s7]
    · -- 1*alpha <= 3
      have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s9 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
      have s10 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s11 : (G.cliqueNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s12 : -(G.indepNum : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s14 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by linarith [s8, s9, s10, s11, s12, s13]
      linarith [s14]
  linarith [s1]
