method BinarySearch(a:array<int>, key:int) returns (r:int)
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length && a[r]==key
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
  {
    var lo, hi := 0, a.Length;
    while lo < hi 
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] != key
    invariant forall i :: hi <= i < a.Length ==> a[i] != key
    decreases hi - lo
    {
      var mid := lo+(hi-lo)/2;
      if a[mid] > key {
        hi := mid;
      }
      else if a[mid] < key {
        lo := mid + 1; // très important pour la fonction de rang
      }
      else {
        return mid;
      }
    }
    return -1;
  }

method BinarySearch2(a:array<int>, key:int) returns (r:int) // modification: r ne renvoie plus de valeurs négatives
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r <= a.Length
  ensures r < a.Length ==> a[r] == key || forall i,j :: 0 <= i < r <= j < a.Length ==> a[i] < key < a[j]
  ensures r == a.Length ==> forall i :: 0 <= i < r ==> a[i] < key
  {
    var lo, hi := 0, a.Length;
    while lo < hi 
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> a[i] > key
    decreases hi - lo
    {
      var mid := lo+(hi-lo)/2;
      if a[mid] > key {
        hi := mid;
      }
      else if a[mid] < key {
        lo := mid + 1; // très important pour la fonction de rang
      }
      else {
        return mid;
      }
    }
    return lo;
  }