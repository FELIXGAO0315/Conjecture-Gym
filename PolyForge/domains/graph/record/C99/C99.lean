import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C99 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.Connected) (hn1 : (Fintype.card V : ℤ) ≥ 5) (hn2 : -2 * (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) :
    (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by
  have s1 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
  have s2 : -2 * (G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s4 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by linarith [s1, s2, s3]
  have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by have hr := s4; omega
  have s6 : (Fintype.card V : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by linarith [s1, s5]
  linarith [s6]
