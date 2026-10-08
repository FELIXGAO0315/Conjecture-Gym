import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C36 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : 2 ≤ Fintype.card V) (hn1 : (G.indepNum : ℤ) ≤ 1) (hn2 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 0) :
    2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) ≥ 6 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G hp1 hp2
    linarith [hw]
  have s4 : (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [s1, s2, s3]
  have s5 : (G.maxDegree : ℤ) ≥ 1 := by linarith [s1, s3]
  have s6 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn2]
  have s7 : 2 * (Fintype.card V : ℤ) ≥ 1 := by linarith [s1, s2, s3, s6]
  have s8 : (Fintype.card V : ℤ) ≥ 1 := by have hr := s7; omega
  have s9 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s10 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s11 : 2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) ≥ 6 := by linarith [s4, s5, s9, s10]
  linarith [s11]
