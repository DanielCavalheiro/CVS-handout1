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

function mem<T(==)> (x: T, n: nat, l: List<T>) : bool
  requires n <= length(l)
{
  match l
  case Nil => false
  case Cons(y, t) =>
    if(n == 0) then
      if (y == x) then true
      else
        false
    else
      mem(x,n-1,t)
}

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i],i, l)

{
  l := Nil;
  var i: int := a.Length - 1;
  while(i >= 0)
    invariant -1 <= i <= a.Length - 1
    invariant length(l) == a.Length - 1 - i
    invariant forall j: int :: i < j < a.Length ==> mem(a[j], j - i - 1, l)
  {
    l := Cons(a[i], l);
    i := i-1;
  }
}

method Main() {
  var l: List<int> := List.Cons(1, List.Cons(2, List.Cons(3, Nil)));
  var arr: array<int> := new int [3](i => i + 1);
  var t: List<int> := from_array(arr);
  print l;
  print "\n";
  print t;
  print "\n";
  print t == l;
}