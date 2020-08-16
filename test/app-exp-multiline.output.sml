val result =
  String.size 
  "foo" 
  + 
  15 
  + 
  (
    case (foo ()) of
      false => 0
    | true  => 100
  ) 
  - 
  3 
  * 
  4 
  + 
  String.size 
  "bar" 
  * 
  3
and another = List.map foo (bar baz :: qux) @ List.concat (another expression) @ ["although this expression"] @ ["which", "ultimately", "is decently formatted"]
