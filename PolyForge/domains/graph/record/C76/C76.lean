import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C76 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : ¬ G.IsAcyclic) (hn1 : 2 * (G.radius.toNat : ℤ) - (G.girth : ℤ) ≥ 0) :
    2 * (G.radius.toNat : ℤ) + (G.girth : ℤ) ≥ 7 := by
  have s1 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp2
    linarith [hw]
  have s2 : 2 * (G.radius.toNat : ℤ) - (G.girth : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.radius.toNat : ℤ) ≥ 2 := by have hr := s3; omega
  have s5 : 2 * (G.radius.toNat : ℤ) + (G.girth : ℤ) ≥ 7 := by linarith [s1, s4]
  linarith [s5]
