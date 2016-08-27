module Group

class Monoid a => Group a where
  inverse : a -> a
