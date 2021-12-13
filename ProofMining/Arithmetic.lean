import ProofMining.Term

def addition (x: Term) (y: Term): Term :=
  match y with
  | Term.zero => x
  | Term.app Term.successor y => Term.app Term.successor (addition x y)
  | _ => sorry
