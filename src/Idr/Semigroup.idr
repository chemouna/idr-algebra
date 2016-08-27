module Idr.Semigroup

import Idr.Magma

||| A magma with binary operation being associative 
||| Associtativity :
|||   forall x,y,z x `op` (y `op` z) = (x `op` y) `op` z

interface Magma a => Semigroup a where {}

magmaOpIsAssociative : Magma a => (x,y,z : a) -> x `op` (y `op` z) = (x `op` y) `op` z


