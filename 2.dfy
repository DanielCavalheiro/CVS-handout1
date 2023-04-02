/*                                      Functional Lists and Imperative Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes        57854
*/

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function length<T>(l: List<T>): nat
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + length(t)
}

function mem<T(==)> (x: T, l: List<T>) : bool
{
  match l
  case Nil => false
  case Cons(head, t) => if(head == x)
  then true
  else
    mem(x,t)
}


method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)

{
  l := Nil;
  var i: int := a.Length - 1;
  while(i >= 0)
    invariant -1 <= i <= a.Length - 1
    invariant forall j: int ::  i < j <= a.Length - 1 ==> mem(a[j], l)
    invariant length(l) == a.Length - 1 - i
  {
    l := Cons(a[i], l);
    i := i-1;
  }
}

method main() {
  var l: List<int> := Cons(1, Nil);
  assert length(l) == 1;
}