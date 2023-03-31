/*                                      Cumulative Sums over Arrays                                        */


/*_________________________________________________________________________________________________________*/


//a)

function sumFowards(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j < a.Length
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sumFowards(a, i+1, j)
}

method sum(a: array<int>, i: int, j: int) returns (sum:int)
    requires 0 <= i <= j < a.Length
    ensures sum == sumFowards(a, i, j)
{
    sum := 0;
    var k := i;

    while(k < j)
        invariant i <= k <= j < a.Length
        invariant sum + sumFowards(a, k, j)  == sumFowards(a, i, j)
    {
        sum := sum + a[k];
        k := k + 1;
    }
    
}
