import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C64 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : (G.minDegree : ℤ) ≥ 2) (hn2 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0) :
    (G.maxDegree : ℤ) ≥ -2 * (G.radius.toNat : ℤ) - 2 * (G.girth : ℤ) + 10 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s2 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 2 := by linarith [hn1]
  have s4 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s5 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp2 hp1
    linarith [hw]
  have s6 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s4, s5, s2]
  have s7 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s6; omega
  have s8 : (G.maxDegree : ℤ) + 2 * (G.radius.toNat : ℤ) + 2 * (G.girth : ℤ) ≥ 10 := by linarith [s1, s2, s3, s7]
  linarith [s8]
