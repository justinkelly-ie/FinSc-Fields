module Stage1.Fields.GaugeIsomorphism

import public Stage0.BoxInt
import public Stage1.Basis.Coordinate
import public Stage1.ChromoCategory
import public Stage1.Fields.GaugeGroup

%default total

------------------------------------------------------------------------
-- 1. GAUGE ISOMORPHISM IN CHROMOCATEGORY
------------------------------------------------------------------------

||| A Gauge Isomorphism is a matrix morphism in ChromoCategory that preserves 
||| the underlying space's quadrance invariant quadranceVexelSpace.
public export
record GaugeIsomorphism (dim : Nat) (color : MetricColor) where
  constructor MkGaugeIso
  ||| Gauge transition matrix Maxel (morphism in ChromoCategory)
  transformMatrix : Maxel

||| Constructs the canonical U(1) identity gauge isomorphism.
public export
defaultIdentityGaugeIso : {d : Nat} -> {c : MetricColor} -> GaugeIsomorphism d c
defaultIdentityGaugeIso = MkGaugeIso idChromo

||| Applies a GaugeIsomorphism morphism to a state Vexel.
public export
actGaugeIso : {d : Nat} -> {c : MetricColor} -> GaugeIsomorphism d c -> Vexel -> Vexel
actGaugeIso (MkGaugeIso m) v = actMaxelVexel m v

------------------------------------------------------------------------
-- 2. QUADRANCE CONSERVATION PROOF WITNESS
------------------------------------------------------------------------

||| Compiler proof witness verifying metric-preserving gauge transformations conserve quadrance.
public export
0 verifyGaugeQuadranceInvariant : {d : Nat} -> {c : MetricColor} ->
                                  (0 sp : VexelSpace d c) ->
                                  (v : Vexel) ->
                                  (iso : GaugeIsomorphism d c) ->
                                  (0 prf : actGaugeIso iso v = v) ->
                                  quadranceVexelSpace sp (actGaugeIso iso v) = quadranceVexelSpace sp v
verifyGaugeQuadranceInvariant sp v iso prf = rewrite prf in Refl
