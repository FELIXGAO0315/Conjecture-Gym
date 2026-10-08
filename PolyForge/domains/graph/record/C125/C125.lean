import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C125 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : ¬ G.IsAcyclic) (hn1 : (G.radius.toNat : ℤ) ≤ 5) :
    (G.radius.toNat : ℤ) + 2 * (G.girth : ℤ) ≥ 7 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    linarith [hw]
  have s2 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp1 hp2
    linarith [hw]
  have s3 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp2
    linarith [hw]
  have s4 : 2 * (G.radius.toNat : ℤ) + 4 * (G.girth : ℤ) ≥ 13 := by linarith [s1, s2, s3]
  have s5 : (G.radius.toNat : ℤ) + 2 * (G.girth : ℤ) ≥ 7 := by have hr := s4; omega
  linarith [s5]
