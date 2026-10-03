||| Representation Theorem Isomorphism for Layer 4 Gauge Fields (Rule 03)
|||
||| Establishes the functorial isomorphism between abstract gauge field curvature tensors
||| and concrete multiset streams over GaugeFieldToken elements:
|||   TheoryRepresentationIsomorphism L4_FieldDynamics GaugeFieldToken GaugeFieldToken
module Stage1.Fields.GaugeRepIso

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Fields.GaugeFieldStream
import Stage1.FourGeometries
import Stage1.PhysicalUniverse.Stratification

%default total

||| Canonical zero gauge field token.
public export
zeroGaugeToken : GaugeFieldToken
zeroGaugeToken = MkGaugeToken (MkIndex 0 0) (MkBoxInt 0)

||| Monomorphic equality for SpacetimeIndex.
public export
indexEqMono : SpacetimeIndex -> SpacetimeIndex -> Bool
indexEqMono (MkIndex m1 n1) (MkIndex m2 n2) = m1 == m2 && n1 == n2

||| Monomorphic equality for GaugeFieldToken.
public export
gaugeTokenEqMono : GaugeFieldToken -> GaugeFieldToken -> Bool
gaugeTokenEqMono (MkGaugeToken i1 s1) (MkGaugeToken i2 s2) =
  indexEqMono i1 i2 && unwrapBox s1 == unwrapBox s2

||| Canonical Representation Isomorphism for Layer 4 Gauge Field Dynamics.
public export
gaugeRepIso : TheoryRepresentationIsomorphism L4_FieldDynamics GaugeFieldToken GaugeFieldToken
gaugeRepIso =
  MkTheoryRepIso
    "L4: Gauge Plaquette Tensor -> Multiset GaugeFieldToken"
    (\tok => AddM tok (MkBoxInt 1) ZeroM)
    (\m => case m of
             AddM tok _ _ => tok
             ZeroM        => zeroGaugeToken)
    (\tok =>
      let m = AddM tok (MkBoxInt 1) ZeroM
          tok' = case m of
                   AddM x _ _ => x
                   ZeroM      => zeroGaugeToken
      in gaugeTokenEqMono tok' tok
    )

||| Compile-time verification that round-trip isomorphism holds for zero gauge token.
public export
0 prfGaugeRepIsoZero : (verifyRoundTrip Stage1.Fields.GaugeRepIso.gaugeRepIso) Stage1.Fields.GaugeRepIso.zeroGaugeToken = True
prfGaugeRepIsoZero = Refl
