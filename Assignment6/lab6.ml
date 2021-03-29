(* Emile Timothy Anand *)
(* CS-4 Lab6 *)

(* Part A: The environment model *)

(* Factorial *)

(** 
 * FRAME 0 (initial environment)
 *    parent : none
 *    bindings:
 *      - : [primitive function -]
 *      * : [primitive function *]
 *
 * FUNCTION 0 (fun n -> let rec iter m r = if m = 0 then ... in iter n 1)
 *    env : FRAME 0
 *    param : n
 *    body : let rec iter m r = if m = 0 then ... in iter n 1
 *
 * FRAME 1 (let factorial n = FUNCTION 0 in ....)
 *    parent : FRAME 0
 *    bindings:
 *        factorial : FUNCTION 0
 *
 * 
 * FRAME 2 (FUNCTION 0 -> apply to 3 1)
 *    parent : FRAME 0
 *    bindings:
 *      n : 3
 *
 *
 * FRAME 3 (let rec iter m r = FUNCTION 1 in iter n 1)
 *    parent : FRAME 2
 *    bindings:
 *      iter : FUNCTION 1
 *
 *
 * FUNCTION 1 (fun m r -> if m = 0 then ... in iter n 1)   
 *    env : FRAME 3 
 *    param : m r
 *    body : if m = 0 then ... in iter n 1
 *
 * FRAME 4 (FUNCTION 1 applied to 3 1)
 *    parent : FRAME 3 
 *    bindings:
 *      m : 3
 *      r : 1
 *  
 * FRAME 5 (FUNCTION 1 applied to 2 3)
 *    parent : FRAME 3
 *    bindings:
 *      m : 2
 *      r : 3
 * 
 * FRAME 6 (FUNCTION 1 applied to 1 6)
 *    parent : FRAME 3
 *    bindings:
 *      m : 1
 *      r : 6
 *
 *
 * FRAME 7 (FUNCTION 1 applied to 0 6)
 *    parent : FRAME 3
 *    bindings:
 *      m : 0
 *      r : 6
 * 
 * Result = 6
 *
**)


(* Recursion using ref cells *)

let factorial = 
  let f = ref (fun n -> 0) in 
    f := begin function
    |  0 -> 1
    |  n -> n * !f(n - 1)
  end;
  !f
;;


(* Part B: Message passing and mutation *)
(* B.1 make_stat_1 *)


exception Stat_error of  string

let make_stat_1 () =
  let sum = ref 0. in
  let sumsq =  ref 0. in
  let n = ref 0 in 

    object

      method append a =
        sum := !sum +. a;
        sumsq := !sumsq +. (a *. a);
        n := !n + 1

      method clear =
        sum := 0.;
        sumsq := 0.;
        n := 0
      
      method mean = match !n with
        | 0 -> raise (Stat_error "need at least one value for mean")
        | _ -> !sum /. (float_of_int !n)

      method variance = match !n with
        | 0 -> raise (Stat_error "need at least one value for variance")
        | _ -> (!sumsq -. !sum *. !sum /. float_of_int !n) /. float_of_int !n

      method stdev = match !n with
        | 0 -> raise (Stat_error "need at least one value for stdev")
        | _ -> sqrt((!sumsq -. !sum *. !sum /. float_of_int !n) /. float_of_int !n)
    end
;;


(* B.2 make_stat_2 *)

let make_stat_2() =
  let sum = ref 0. in
  let sumsq = ref 0. in
  let n = ref 0 in
    object(self)
      method append a =
        sum := !sum +. a;
        sumsq := !sumsq +. (a *. a);
        n := !n + 1

      method mean = match !n with
        | 0 -> raise (Stat_error "need at least one value for mean")
        | _ -> !sum /. (float_of_int !n)

      method private _variance = 
        (!sumsq -. !sum *. !sum /. float_of_int !n) /. float_of_int !n  
      
      method variance = match !n with
        | 0 -> raise (Stat_error "need at least one value for variance")
        | _ -> self#_variance

      method stdev = match !n with
        | 0 -> raise (Stat_error "need at least one value for stdev")
        | _ -> sqrt(self#variance)

      method clear =
        sum := 0.;
        sumsq := 0.;
        n := 0
    end
;;


(* Part C: Modules and functors *)

(* C.1. PriorityQueue module *)

module type PRIORITY_QUEUE =
  sig
    exception Empty
    type elem      (* Abstract type of elements of queue. *)
    type t         (* Abstract type of queue. *)
    val empty      : t                (* The empty queue.         *)
    val is_empty   : t -> bool        (* Check if queue is empty. *)
    val insert     : t -> elem -> t   (* Insert item into queue.  *)
    val find_min   : t -> elem        (* Return minimum element.  *)
    val delete_min : t -> t           (* Delete minimum element.  *)
    val from_list  : elem list -> t   (* Convert list to queue.   *)
  end
;;


module PriorityQueue : (PRIORITY_QUEUE with type elem = int) =
  struct
    exception Empty
    type elem = int
    type t = Leaf | Node of int * elem * t * t
    let empty = Leaf

    let is_empty queue = 
      queue = Leaf
    
    let rank queue = 
      match queue with
      | Leaf -> 0
      | Node(r, _, _, _) -> r
    
    let helper_merge a queue1 queue2 = 
      if (rank queue1) < (rank queue2) then
        Node((rank queue1) + 1, a, queue2, queue1)
      else
        Node((rank queue2) + 1, a, queue1, queue2)
 
    let find_min queue = 
      match queue with
      | Leaf -> raise Empty
      | Node(_, value, _, _) -> value

    let rec merge queue1 queue2 = 
      match (queue1, queue2) with
        | (Leaf, Leaf) -> Leaf
        | (Leaf, _) -> queue2
        | (_, Leaf) -> queue1
        | (Node(_, a, c , d), q) when a < find_min q -> helper_merge a c (merge d q)
        | (q, Node(_, a, c, d)) -> helper_merge a c (merge d q)

    let insert queue element = merge queue (Node(1, element, Leaf, Leaf))

    let delete_min queue = 
      match queue with
      | Leaf -> raise Empty
      | Node(_, _, a, b) -> merge a b

    let rec from_list list = 
      match list with
      | [] -> empty
      | h :: t -> insert (from_list t) h
  end
;;

let heap_sort list = 
  let start_lst = PriorityQueue.from_list list in
  let rec iter lst queue =
    if PriorityQueue.is_empty queue then 
      lst 
    else 
      iter (PriorityQueue.find_min queue :: lst) (PriorityQueue.delete_min queue)
  in List.rev (iter [] start_lst)
;;


(* C.2 MakePriorityQueue functor *)

(* Type for ordered comparisons. *)
type comparison = LT | EQ | GT

(* Signature for ordered objects. *)
module type ORDERED =
  sig
    type t
    val cmp: t -> t -> comparison
  end
;;

(* Signature for priority queues. *)

module MakePriorityQueue(Elt: ORDERED) : (PRIORITY_QUEUE with type elem = Elt.t) =
  struct
    exception Empty
    type elem = Elt.t
    type t = Leaf | Node of int * elem * t * t

    let empty = Leaf

    let is_empty queue = 
      queue = Leaf
    
    let rank queue = 
      match queue with
      | Leaf -> 0
      | Node(r, _, _, _) -> r
    
    let helper_merge a queue1 queue2 = 
      if (rank queue1) < (rank queue2) then
        Node((rank queue1) + 1, a, queue2, queue1)
      else
        Node((rank queue2) + 1, a, queue1, queue2)
 
    let find_min queue = 
      match queue with
      | Leaf -> raise Empty
      | Node(_, value, _, _) -> value

    let rec merge queue1 queue2 = 
      match (queue1, queue2) with
        | (Leaf, Leaf) -> Leaf
        | (Leaf, _) -> queue2
        | (_, Leaf) -> queue1
        | (Node(_, a, c , d), q) when Elt.cmp a (find_min q) = LT -> helper_merge a c (merge d q)
        | (q, Node(_, a, c, d)) -> helper_merge a c (merge d q)

    let insert queue element = merge queue (Node(1, element, Leaf, Leaf))

    let delete_min queue = 
      match queue with
      | Leaf -> raise Empty
      | Node(_, _, a, b) -> merge a b

    let rec from_list list = 
      match list with
      | [] -> empty
      | h :: t -> insert (from_list t) h
  end
;;

module OrderedString =
  struct
    type t = string
    let cmp x y =
      if x = y then EQ else if x < y then LT else GT
  end
;;

module StringPQ = MakePriorityQueue(OrderedString);;

let heap_sort_2 list = 
  let start_lst = StringPQ.from_list list in
  let rec iter lst queue =
    if StringPQ.is_empty queue then 
      lst 
    else 
      iter (StringPQ.find_min queue :: lst) (StringPQ.delete_min queue)
  in List.rev (iter [] start_lst)
;;


(* Part D: Special topics *)
(* D.1 Streams *)

type 'a contents = 
  | Expr of (unit -> 'a)
  | Val of 'a
;;

type 'a lazy_t = 'a contents ref

let make_lazy e = ref (Expr e)

let force lz = match !lz with
  | Val x -> x
  | Expr e -> 
    let x = e() in
      lz := Val x;
      x
;;

let lz = make_lazy (fun () -> 100 * 100 * 100);;


(* D.2 The Y combinator *)
let y =
  fun f ->
    (fun z -> z (`Roll z))
    (fun (`Roll w) -> f (fun x -> w (`Roll w) x))
;;

(* D.2.a: sum *)

let a = fun f -> 
  fun lst ->
    match lst with
      | [] -> 0
      | h :: t -> h + (f t)
;;

let sum = y a;;

(* D.2.b: Two-argument functions *)

let b = fun f ->
  fun (n, r) ->
    if n = 0 then
      r
    else
      f (n - 1, n * r)
;;

let factorial2 n = y b (n, 1);;  