Definition either {a b c} (f: a -> c) (g: b -> c) (x:a + b) :=
  match x with
  | inl x => f x
  | inr x => g x end.

Definition maybe {A B} (e:B) (f:A -> B) (x:option A) :=
  match x with
  | None => e
  | Some x => f x end.
