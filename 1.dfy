/*                                      Cumulative Sums over Arrays                                        */


/*_________________________________________________________________________________________________________*/



//(a)
function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}


//(b)
method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
{
    res := 0;
    var k := i;

    while(k < j)
        invariant i <= k <= j <= a.Length
        invariant res + sum(a, k, j)  == sum(a, i, j)
    {
        res := res + a[k];
        k := k + 1;
    }
    
}


