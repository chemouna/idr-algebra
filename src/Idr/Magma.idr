module Idr.Magma

%access public export

||| A type with a binary operation
|||
interface Magma a where
  op : a -> a -> a

-- types to encode properties of magmas

-- magmaOpIsAssociative : Magma a => a -> Type
-- magmaOpIsAssociative = \a => (x,y,z : a) -> x `op` (y `op` z) = (x `op` y) `op` z

-- magmaOpIsCommutative : Magma a => a -> Type
-- magmaOpIsCommutative = \a => (x,y : a) -> x `op` y = y `op` x
