/*                                      Functional Lists and Imperative Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Perdro Nunes        57854
*/

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function lenght<T>(l: List<T>): nat 
{
    match l
        case Nil => 0
        case Cons(_, t) => 1 + lenght(t)
}


method from_array<T>(a: array<T>) returns (l: List<T>)
    requires a.Length >= 0
    ensures lenght(l) == a.Length
{
    l := Nil;
    var i: int := a.Length-1;
    while(i >= 0)
    {
        l := Cons(a[i], l);
        i := i-1;
    }
} 