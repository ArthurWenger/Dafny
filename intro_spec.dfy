method Triple(x:int) returns (r:int)
ensures r==3*x
{
  var y := 2*x;
  r := x+y;
}

method Triple2(x:int) returns (r:int)
ensures r>=3*x
{
  if 0<=x{
      var y := Double(x);
  r := x+y;
  } else {
    var y := Double(-x);
    r := x+y;
  }
}

method Double(x:int) returns (r:int)
requires 0 <= x
ensures r>=2*x
{
  r:= x+x;
}

method TestCase(){
  var t := Triple2(-3);
  assert t >= -9;
}

method Main(){
  var t := Triple2(-3);
  print t;
}

method SumMax(x:int,y:int) returns(s:int,m:int)
ensures s == x+y
ensures x<=m && y<=m
ensures m==x || m==y
{
  s:=x+y;
  if x<y{
    m:=y;
  } else {
    m:=x;
  }
}

method SumMaxBackwards(s:int,m:int) returns(x:int,y:int)
requires s<=2*m // important pour assurer que m est bien le max => aucune garantie sur les params en entrée
// on doit verifier y <= x donc s-m <= m soit s <= 2*m
ensures s == x+y
ensures x<=m && y<=m
ensures m==x || m==y
{
  x:=m;
  y:=s-m;
}

//--------------------------------------//

// les fonctions ne changent pas selon le contexte => toujours le meme resultat 
function Fib(n:nat):nat
{
  if n < 2 then n else Fib(n-2) + Fib(n-1)
}

method ComputeFib(n:nat) returns (x:nat)
ensures x==Fib(n)
{
  x := 0;
  var i := 0;
  var y := 1;
  while i < n
  invariant 0 <= i <= n // l'invariant doit en fait être vrai juste avant le while (avant l'éxecution de la boucle)
  // l'invariant doit être vrai meme si la condition de la boucle est fausse (au dessus de la boucle)  
  invariant x == Fib(i) && y==Fib(i+1)
  {
    /* Methode 1
    var t:=x;
    x := y;
    y := t+y;*/
    /* Methode 2
    y := x+y;
    x := y-x; */
    x, y := y, x+y; // exo: transformer ce code de manière sequentielle
    i := i+1;
  }
}

function Sum(n:nat):nat
{
  if n==0 then 0 else n+Sum(n-1)
}

method ComputeSum(n:nat) returns (s:nat)
ensures s==Sum(n)
{
  var i := 0;
  s := 0;
  while i < n
  invariant 0 <= i <= n
  invariant s == Sum(i)
  decreases  n - i
  {
    i := i+1;
    s:= s+i;
  }
}

/* method ComputeSum2(n:nat) returns (s:nat)
ensures s==Sum(n)
{
  var i := 1;
  s := 0;
  while i <= n
  invariant 1 <= i <= n+1 || n == 0
  invariant s == Sum(i-1)
  decreases  n+1 - i
  {
    s:= s+i;
    i := i+1;
  }
} */

method merge(a:int,t:array<int>) returns (t':array<int>){
  var i := 0;
  var flag := 0;
  t':= new int[t.Length+1];

  while i < t.Length
  {
    if a > t[i] {
      t'[i] := t[i];
    } else if flag == 0 {
      t'[i] := a;
      flag := 1;
    } else {
      t'[i+1] := t[i];
    }
    i := i+1;
  }
}

method sort(t:array<int>) returns (t':array<int>){
  
}