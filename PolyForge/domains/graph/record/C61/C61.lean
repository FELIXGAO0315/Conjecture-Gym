import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C61 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.diam : ℤ) ≥ 1) (hn2 : (G.maxDegree : ℤ) ≥ 1) :
    (G.maxDegree : ℤ) ≥ -2 * (G.radius.toNat : ℤ) + 3 := by
  have s1 : (G.maxDegree : ℤ) ≥ 1 := by linarith [hn2]
  have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    linarith [hw]
  have s3 : (G.diam : ℤ) ≥ 1 := by linarith [hn1]
  have s4 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have s6 : (G.maxDegree : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s1, s5]
  linarith [s6]
