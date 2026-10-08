import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C90 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : 2 * (G.maxDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≥ 2) :
    2 * (Fintype.card V : ℤ) - (G.indepNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 7 := by
  have s1 : (G.indepNum : ℤ) ≥ 0 := by positivity
  have s2 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn2]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s1, s2, s3]
  have s5 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int G (by omega)
    linarith [hw]
  have s6 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s7 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp2 hp1
    linarith [hw]
  have s8 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    linarith [hw]
  have s9 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s6, s7, s8]
  have s10 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s9; omega
  have s11 : 2 * (Fintype.card V : ℤ) - (G.indepNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 7 := by linarith [s5, s2, s10, s3]
  linarith [s11]
