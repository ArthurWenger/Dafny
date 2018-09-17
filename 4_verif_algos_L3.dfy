method swap(x: int, y:int) returns (x':int, y':int)
ensures x' == y
ensures y' == x
{
  var t := x;
  x' := y;
  y' := t;
}

method swap2(x:int, y:int) returns (x':int, y':int)
ensures x' == y
ensures y' == x
{
  x' := x + y;
  y' := x' - y;
  x' := x' - y';
}

method abs(x:int) returns (y:int)
ensures y >= 0
ensures y == x || y == -x
{
  if x >=0 {y := x;} else {y := -x;}
}

function fact(n:nat): nat
decreases  n
{
  if n==0 then 1 else n*fact(n-1)
}

method ComputeFact(n: nat) returns (r: nat)
ensures r == fact(n)
{
  var i := 0;
  r := 1;
  while i < n
  decreases  n - i
  invariant 0 <= i <= n
  invariant r == fact(i)
  {
    i := i+1;
    r := r*i;
  }
}

function partialSumList(a: array<int>, i: nat):int
{
  if i==0 then a[i] else if i < 0 then 0 else a[i] + partialSumList(a, i-1)
}

function SumList(a: array<int>):int
{
  match a
  {
    case h::t => h;
    case nil => ;
  }
}

method ComputeSumList(a: array<int>) returns(s: int)
ensures s == SumList(a)
