module Nat = struct
  type t =
    | Zero
    | Suc of t

  let rec (<=) m n =
    match m, n with
    | Zero, _ -> true
    | Suc m, Suc n -> m <= n
    | _ -> false

  let rec (<) m n =
    match m, n with
    | Zero, Suc n -> true
    | Suc m, Suc n -> m < n
    | _ -> false
end

let leq_trans m n p =
  Nat.(
    (m <= n && n <= p)[@trigger]
    ==>
    m <= p
  )
[@@imandra_theorem][@@auto][@@fc]

let lt_iff_leq m n =
  Nat.(
    (m < n) = (Suc m <= n)
  )
[@@imandra_theorem][@@auto][@@rw];;

let leq_suc n =
  Nat.(
    n <= Suc n
  )
[@@imandra_theorem][@@auto][@@fc]

let leq_suc_bridge m n p =
  Nat.(
    (Suc m <= n && Suc n <= p)[@trigger]
    ==>
    n <= Suc n
  )
[@@imandra_theorem]
[@@auto][@@fc];;

[@@@max_induct 0i];;

let lt_trans m n p =
  Nat.(
    m < n &&
    n < p
    ==>
    m < p
  )
[@@imandra_theorem]
[@@auto]
[@@disable Nat.(<=)]
