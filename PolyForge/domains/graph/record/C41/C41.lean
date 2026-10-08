import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C41 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : 2 ≤ Fintype.card V) (hn1 : (G.diam : ℤ) ≥ 5) (hn2 : (G.radius.toNat : ℤ) ≤ 3) :
    (G.minDegree : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 7 := by
  have s1 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G hp1 hp2
    linarith [hw]
  have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    linarith [hw]
  have s3 : (G.diam : ℤ) ≥ 5 := by linarith [hn1]
  have s4 : 2 * (G.radius.toNat : ℤ) ≥ 5 := by linarith [s2, s3]
  have s5 : (G.radius.toNat : ℤ) ≥ 3 := by have hr := s4; omega
  have s6 : (G.minDegree : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 7 := by linarith [s1, s5]
  linarith [s6]
