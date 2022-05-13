type 'a t

val empty : 'a t
val vertices : 'a t -> 'a MySet.t
val neighbors : 'a -> 'a t -> 'a MySet.t
val complete : 'a MySet.t -> 'a t
val merge : 'a t -> 'a t -> 'a t
