(define (domain vacuum)
  (:requirements :strips :typing)
  (:types pos)

  (:predicates
    (at ?p - pos)
    (adj ?a - pos ?b - pos)     ; directed adjacency
    (dirty ?p - pos)
  )

  (:action move
    :parameters (?from - pos ?to - pos)
    :precondition (and (at ?from) (adj ?from ?to))
    :effect (and (not (at ?from)) (at ?to))
  )

  (:action suck
    :parameters (?p - pos)
    :precondition (and (at ?p) (dirty ?p))
    :effect (and (not (dirty ?p)))
  )
)