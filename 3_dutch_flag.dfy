datatype Color = Red | White | Blue
predicate Below(c: Color, d: Color)
{
  c == Red || c == d || d == Blue
}

method DutchFlag(a: array<Color>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> Below(a[i],a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var r, w, b:= 0, 0, a.Length;
  while w < b
    invariant 0 <= r <= w <= b <= a.Length
    invariant forall i:: 0 <= i < r ==> a[i] == Red
    invariant forall i:: r <= i < w ==> a[i] == White
    invariant forall i:: b <= i < a.Length ==> a[i] == Blue
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases  b - w
  {
    match a[w]
    {
      case Red => 
        a[r], a[w] := a[w], a[r];
        r, w := r + 1, w + 1;
      case White => 
        w := w + 1;
      case Blue => 
        b := b - 1;
        a[w], a[b] := a[b], a[w];
    }
  }
}

predicate boolSorted(a:bool, b:bool)
{
  a == false || b == true // ff ft tt tf
}

method boolSort(a: array<bool>)
modifies a
ensures forall i,j:: 0 <= i < j < a.Length ==> boolSorted(a[i], a[j])
ensures multiset(a[..]) == multiset(old(a[..]))
{
  var f, t := 0, a.Length;
  while f < t
    invariant 0 <= f <= t <= a.Length
    invariant forall i :: 0 <= i < f ==> a[i] == false
    invariant forall i :: t <= i < a.Length ==> a[i] == true
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases  t - f
  {
    if a[f] {
      t := t-1;
      a[f], a[t] := a[t], a[f];
    } else {
      f := f+1;
    }  
  }
}