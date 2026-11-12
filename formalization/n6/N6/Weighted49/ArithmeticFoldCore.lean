import N6.Weighted49.ArithmeticCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Weighted49
def scaleList (a : Int) (xs : List Int) : List Int := xs.map (fun x => a*x)
def addLists0 : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x+y) :: addLists0 xs ys
def foldColumns (n : Nat) : List Int → List (List Int) → List Int
  | [], _ => List.replicate n 0
  | _, [] => List.replicate n 0
  | w :: ws, c :: cs =>
    if w = 0 then foldColumns n ws cs else addLists0 (scaleList w c) (foldColumns n ws cs)
end N6.Weighted49
