module Idr.Semigroup

import Idr.Magma

%access public export

||| A magma with binary operation being associative
||| Associtativity :
|||   forall x,y,z x `op` (y `op` z) = (x `op` y) `op` z

interface Magma a => MySemigroup a where {}

magmaOpIsAssociative : Magma a => (x,y,z : a) -> x `op` (y `op` z) = (x `op` y) `op` z

||| Regular Semigroup = a Semigroup with a unary operation star
||| such that forall x, (star x) `op` x `op` (star x) = x

interface MySemigroup a => RegularSemigroup a where
  star : a -> a

interface RegularSemigroup a => InverseSemigroup a where {}


