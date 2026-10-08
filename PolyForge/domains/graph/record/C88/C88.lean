import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C88 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hp2 : G.Connected) (hn1 : (G.diam : ℤ) ≥ 1) :
    (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by
  have s1 : (G.diam : ℤ) ≥ 1 := by linarith [hn1]
  have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s3 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s2, s1]
  have s4 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s3; omega
  have s5 : (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s1, s4]
  linarith [s5]
