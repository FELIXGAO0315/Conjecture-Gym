import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C29 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : -2 * (G.vertexCoverNum.toNat : ℤ) + (G.girth : ℤ) ≤ 0) (hn2 : (G.minDegree : ℤ) - (G.indepNum : ℤ) ≥ 0) :
    (G.minDegree : ℤ) ≤ 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - 6 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s2 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    linarith [hw]
  have s3 : (G.indepNum : ℤ) ≥ 0 := by positivity
  have s4 : 2 * (G.vertexCoverNum.toNat : ℤ) - (G.girth : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s6 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5]
  have s7 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s6; omega
  have s8 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s9 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s2, s4]
  have s10 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s9; omega
  have s11 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 6 := by linarith [s1, s8, s10, s5]
  linarith [s11]
