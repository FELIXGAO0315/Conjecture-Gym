import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C49 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : 2 ≤ Fintype.card V) (hn1 : (G.maxDegree : ℤ) - (G.girth : ℤ) ≥ 0) (hn2 : -2 * (G.vertexCoverNum.toNat : ℤ) + (G.girth : ℤ) ≤ 0) :
    (G.indepNum : ℤ) ≤ 2 * (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) - 10 := by
  have s1 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.girth : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : (G.maxDegree : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : 2 * (G.vertexCoverNum.toNat : ℤ) - (G.girth : ℤ) ≥ 0 := by linarith [hn2]
  have s5 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s1, s4]
  have s6 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s5; omega
  have s7 : (G.indepNum : ℤ) ≥ 0 := by positivity
  have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s9 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s7, s4, s8]
  have s10 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s9; omega
  have s11 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int G (by omega)
    linarith [hw]
  have s12 : 2 * (Fintype.card V : ℤ) - (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 10 := by linarith [s3, s6, s11, s8]
  linarith [s12]
