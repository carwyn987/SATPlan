(define (domain assembly-line)
  (:requirements :strips :typing)
  (:types part tool station)

  (:predicates
    (at-part ?p - part ?s - station)
    (at-tool ?t - tool ?s - station)
    (have ?t - tool)
    (processed ?p - part)
    (assembled ?p - part)
    (next ?a - station ?b - station)
    (robot-at ?s - station)
  )

  (:action move-robot
    :parameters (?a - station ?b - station)
    :precondition (and (robot-at ?a) (next ?a ?b))
    :effect (and (not (robot-at ?a)) (robot-at ?b))
  )

  (:action pickup-tool
    :parameters (?t - tool ?s - station)
    :precondition (and (robot-at ?s) (at-tool ?t ?s))
    :effect (and (have ?t) (not (at-tool ?t ?s)))
  )

  (:action process-part
    :parameters (?p - part ?t - tool ?s - station)
    :precondition (and (robot-at ?s) (at-part ?p ?s) (have ?t))
    :effect (and (processed ?p))
  )

  (:action assemble
    :parameters (?p - part ?s - station)
    :precondition (and (robot-at ?s) (processed ?p))
    :effect (and (assembled ?p))
  )
)