(define (domain logistics-mini)
  (:requirements :strips :typing)
  (:types truck pkg loc)

  (:predicates
    (at-truck ?t - truck ?l - loc)
    (at-pkg ?p - pkg ?l - loc)
    (in ?p - pkg ?t - truck)
    (road ?a - loc ?b - loc)
  )

  (:action drive
    :parameters (?t - truck ?from - loc ?to - loc)
    :precondition (and (at-truck ?t ?from) (road ?from ?to))
    :effect (and (not (at-truck ?t ?from)) (at-truck ?t ?to))
  )

  (:action load
    :parameters (?p - pkg ?t - truck ?l - loc)
    :precondition (and (at-truck ?t ?l) (at-pkg ?p ?l))
    :effect (and (not (at-pkg ?p ?l)) (in ?p ?t))
  )

  (:action unload
    :parameters (?p - pkg ?t - truck ?l - loc)
    :precondition (and (at-truck ?t ?l) (in ?p ?t))
    :effect (and (not (in ?p ?t)) (at-pkg ?p ?l))
  )
)