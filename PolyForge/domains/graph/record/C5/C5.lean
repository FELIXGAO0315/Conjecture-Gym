import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C5 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.radius.toNat : ℤ)) :
    2 * (G.radius.toNat : ℤ) ≤ (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) - 1 := by
  have s1 : (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 1 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.diam : ℤ)
    · -- 1*diam >= 1
      have s2 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_card_int G
        linarith [hw]
      have s3 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G (isTree_connected G hp1)
        linarith [hw]
      have s4 : (G.diam : ℤ) ≥ 1 := by have hcc := hc1; omega
      have s5 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s3, s4]
      have s6 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s5; omega
      have s7 : (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s8 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        linarith [hw]
      have s9 : (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s2, s6, s7, s8]
      linarith [s9]
    · -- 1*diam <= 0
      have s10 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int' G
        linarith [hw]
      have s11 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        linarith [hw]
      have s12 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G (isTree_connected G hp1)
        linarith [hw]
      have s13 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
      have s14 : -(G.diam : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s16 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        linarith [hw]
      have s17 : (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s10, s11, s12, s13, s14, s15, s16]
      linarith [s17]
  linarith [s1]
