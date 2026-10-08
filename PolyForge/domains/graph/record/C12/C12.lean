import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C12 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (Fintype.card V : ℤ) ≥ 1) (hn2 : (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 0) :
    -(Fintype.card V : ℤ) - (G.indepNum : ℤ) + 2 * (G.diam : ℤ) ≤ -2 := by
  have s1 : (Fintype.card V : ℤ) + (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 2 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.diam : ℤ)
    · -- 1*diam >= 1
      have s2 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
      have s3 : (G.diam : ℤ) ≥ 1 := by have hcc := hc1; omega
      have s4 : (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 0 := by linarith [hn2]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) + (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 2 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*diam <= 0
      have s7 : (Fintype.card V : ℤ) ≥ 1 := by linarith [hn1]
      have s8 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int G (by omega)
        linarith [hw]
      have s9 : -(G.diam : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s10 : (Fintype.card V : ℤ) + (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 2 := by linarith [s7, s8, s9]
      linarith [s10]
  linarith [s1]
