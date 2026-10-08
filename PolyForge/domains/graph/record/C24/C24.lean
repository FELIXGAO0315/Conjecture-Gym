import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C24 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 3) (hn1 : (G.edgeFinset.card : ℤ) ≥ 6) (hn2 : (Fintype.card V : ℤ) ≤ 5) :
    (G.chromaticNumber.toNat : ℤ) - (G.indepNum : ℤ) ≤ 4 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ -4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s3 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn2]
      have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [s2, s3]
      have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s5]
      have s7 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
        have hw := tau_le_card_sub_one_int G (by omega)
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s9 : -2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ -8 := by linarith [s4, s7, s8]
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s12 : -2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ -4 := by linarith [s10, s11]
      linarith [s12]
  linarith [s1]
