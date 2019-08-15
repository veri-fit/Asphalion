(* Replace during extraction *)
Inductive ref (T : Type) :=
| ref_cons (t : T).
Global Arguments ref_cons [T] _.

(* Replace during extraction *)
Definition get_ref {T : Type} (t : ref T) : T :=
  match t with
  | ref_cons t => t
  end.

(* Replace during extraction *)
Definition update_ref {T : Type} (r : ref T) (t : T) : unit := tt.
