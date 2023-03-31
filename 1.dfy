/*                                      Cumulative Sums over Arrays                                        */


/*_________________________________________________________________________________________________________*/


/**
(a)
Define a Dafny specification function called sum that takes as arguments an array of in-
tegers a and two indices into the array, i and j, that calculates the sum over the interval
[ai, aj[, with i ≤ j. This function will recur over the array either “from the start” (i.e.,
recursive calls increase the argument i), or “from the end” (i.e., recursive calls decrease
the argument j). Note: You will need to add to the function signature a specification of
the form reads a, to indicate that the function can read from the memory denoted by the
array. You will also likely reduce future pain if you constrain (i.e., require) i and j such
that both sum(a,a.Length,a.Length) and sum(a,0,0) are valid function calls.
*/

function sumFowards(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sumFowards(a, i+1, j)
}

method sum(a: array<int>, i: int, j: int) returns (sum:int)
    requires 0 <= i <= j <= a.Length
    ensures sum == sumFowards(a, i, j)
{
    sum := 0;
    var k := i;

    while(k < j)
        invariant i <= k <= j <= a.Length
        invariant sum + sumFowards(a, k, j)  == sumFowards(a, i, j)
    {
        sum := sum + a[k];
        k := k + 1;
    }
    
}


/*_________________________________________________________________________________________________________*/
