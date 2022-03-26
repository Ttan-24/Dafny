function method fibspec(n: nat): nat
//decreases  n
{
    if (n==0) then 0 else
      if (n==1) then 1 else
        fibspec(n-1) + fibspec(n-2)
}

method ComputeFib(n: nat) returns (b: nat) 
//ensures b == fibspec(n); 
{ 
    if (n == 0) { return 0; } 
    var i := 1; 
    var a := 0; b := 1; 
    while (i < n)
        //invariant 0 < i <= n; 
        //invariant a == fibspec(i - 1); 
        //invariant b == fibspec(i); 
    { 
        a, b := b, a + b; 
        i := i + 1; 
    } 
}

method Main()
{
    print "Hello\n";
    var x := ComputeFib(10);
    var y := fibspec(10);
    print x, "  ", y, "\n";
}
