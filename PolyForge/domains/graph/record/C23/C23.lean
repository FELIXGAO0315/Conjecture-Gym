import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C23 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 1) (hn1 : (Fintype.card V : ℤ) ≤ 6) (hn2 : 2 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    (G.vertexCoverNum.toNat : ℤ) ≤ 5 := by
  have s1 : -(G.vertexCoverNum.toNat : ℤ) ≥ -5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
      have s5 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int G (by omega)
        linarith [hw]
      have s6 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [hn1]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s8 : -(G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [s5, s6, s7]
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : 2 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s11 : -(G.vertexCoverNum.toNat : ℤ) ≥ -4 := by linarith [s9, s10]
      linarith [s11]
  linarith [s1]
