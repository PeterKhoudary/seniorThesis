import Lean
namespace leftistHeap
open leftistHeap

inductive leftistHeap (a' : Type) where
| leaf
| node (a') (Int) (leftistHeap a') (leftistHeap a')

def rank heap :=
  match heap with
  | leaf => 0
  | node _ _  r _ => r

def mkLeftistNode {β : Type} (left : leftistHeap β) (key : β) (priority : Int) (right : leftistHeap β) : leftistHeap β :=
  if rank left < rank right
  then node right key priority (rank left + 1) left
  else node left key priority (rank right + 1) right

def singleton {β : Type} (key : β) (priority : Int): leftistHeap β :=
  node leaf key priority 1 leaf

def meld {β : Type} : leftistHeap β → leftistHeap β → leftistHeap β
  | leaf, b => b
  | a, leaf => a
  | node lₐ ka rka ra, node _ kb pb rb =>
    if pa < pb
    then mkLeftistNode la ka pa (meld ra (node lb kb pb rkb rb))
    else mkLeftistNode lb kb pb (meld (node la ka pa rka ra) rb)
