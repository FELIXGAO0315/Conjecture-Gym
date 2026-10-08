import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C35 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : ¬ G.IsAcyclic) (hn1 : -2 * (G.minDegree : ℤ) + 2 * (G.diam : ℤ) ≥ 0) :
    2 * (G.radius.toNat : ℤ) + (G.girth : ℤ) ≥ 5 := by
  have s1 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp2
    linarith [hw]
  have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    linarith [hw]
  have s3 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp1 hp2
    linarith [hw]
  have s4 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s2, s3, s1]
  have s5 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have s6 : 2 * (G.radius.toNat : ℤ) + (G.girth : ℤ) ≥ 5 := by linarith [s1, s5]
  linarith [s6]
