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
  var i1, i2, b:= 0, 0, a.Length;
  while i2 < b
    invariant 0 <= i1 <= i2 <= b <= a.Length
    invariant forall i:: 0 <= i < i1 ==> a[i] == Red
    invariant forall i:: i1 <= i < i2 ==> a[i] == White
    invariant forall i:: b <= i < a.Length ==> a[i] == Blue
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases  b - i2
  {
    match a[i2]
    {
      case Red => 
        a[i1], a[i2] := a[i2], a[i1];
        i1, i2 := i1 + 1, i2 + 1;
      case White => 
        i2 := i2 + 1;
      case Blue => 
        b := b - 1;
        a[i2], a[b] := a[b], a[i2];
    }
  }
}

predicate boolBelow(a:bool, b:bool)
{
  a == false || b == true // ff ft tt tf
}

method boolSort(a: array<bool>)
modifies a
ensures forall i,j:: 0 <= i < j < a.Length ==> boolBelow(a[i], a[j])
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

datatype quadriColors = C1 | C2 | C3 | C4

predicate quadBelow(a: quadriColors, b: quadriColors)
{
  a == C1 || b == C4 || a == b || (b == C3 && a != C4)
}

method quadriFlag(a: array<quadriColors>) 
modifies a
ensures forall i,j :: 0 <= i < j < a.Length ==> quadBelow(a[i], a[j]);
ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i1, i2, i3, i4 := 0, 0, 0, a.Length;
  while i3 < i4
    invariant 0 <= i1 <= i2 <= i3 <= i4 <= a.Length
    invariant forall i :: 0 <= i < i1 ==> a[i] == C1
    invariant forall i :: i1 <= i < i2 ==> a[i] == C2
    invariant forall i :: i2 <= i < i3 ==> a[i] == C3
    invariant forall i :: i4 <= i < a.Length ==> a[i] == C4
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases  i4 - i3
  {
      match a[i3]
        {
          case C3 => 
          i3 := i3 + 1;
          case C1 =>  
          a[i2], a[i3] := a[i3], a[i2];
          a[i1], a[i2] := a[i2], a[i1];
          i1, i2, i3  := i1+1, i2+1, i3+1;
          case C2 =>
          a[i2], a[i3] := a[i3], a[i2];
          i2, i3 := i2+1, i3+1;
          case C4 =>
          i4 := i4 -1;
          a[i4], a[i3] := a[i3], a[i4];
        }
    }
  
}