module Network

import Data.Vect

TensorDim : Nat -> Type
TensorDim n = Vect n Nat


data Layer : TensorDim i -> TensorDim o -> Type where
  Dense : Layer [i] [o]
  Flatten : Layer i [foldr (*) 1 i]
  Relu : Layer i i
  Sigmoid : Layer i i
  Softmax : Layer i i

data Network : TensorDim i -> Vect n (k : Nat ** TensorDim k) -> TensorDim o -> Type where
  Out : Layer i o -> Network i [] o
  (::) : {h : (k : Nat ** TensorDim k)} -> Layer i (snd h) -> Network (snd h) hs o -> Network i (h :: hs) o

mnist : Network [28, 28, 1] [(1 ** [784]), (1 ** [42]), (1 ** [42]), (1 ** [10])] [10]
mnist = Flatten ::
        Dense ::
        Relu ::
        Dense ::
        Out Sigmoid
