;--------------------------------------------------------------------------------------------------------


;MERGED FEATURES IN PDDL (DOMAIN FILE) VER. 2: TAKING DOMAIN PDDL VER. 1 & OPTIMIZING & POSTPROCESSING MULTI-STEP ACTIONS
;References: https://fareskalaboud.github.io/LearnPDDL/, https://editor.planning.domains/#
;Debugging the features and changing representation/configuration using PDDL and LLM suggestions:
;1. States: Uses 'Row' and 'Col' objects (r1, c1) instead of
;   a single propositional 'Cell(C1_1)'.
;2. Predicates: Uses 'NextRow(r1, r2)' and 'NextCol(c1, c2)' instead of
;  'AdjacentRight', etc. Also gets rid of up and left adjacencies, and moves into initial instead of domain. 
;   Also uses AtHorizontal() and AtVertical(), combining two checks into one.
;3. Actions: Removes all multi-step actions (e.g., 'CarMoveRightTwo')
;   and relies on POST-PROCESSING to put together single-step moves. 
;No runner for any configuration yet

;From here, I need to convert this optimized version (post-processed) back to mergedfeatsver2 file in python


;--------------------------------------------------------------------------------------------------------

(define (domain rush-hour)
  (:requirements :typing :equality)
  
  (:types
    vehicle row col - object
    car truck - vehicle
  )
  
  (:predicates
    (at-horizontal ?v - vehicle ?r - row ?c - col)
    (at-vertical ?v - vehicle ?r - row ?c - col)
    (clear ?r - row ?c - col)
    (next-col ?c1 - col ?c2 - col) 
    (next-row ?r1 - row ?r2 - row) 
  )

  (:action car-move-right
    :parameters (?c - car ?r - row ?from ?to - col)
    :precondition (and
      (at-horizontal ?c ?r ?from)
      (next-col ?from ?to)
      (clear ?r ?to)
    )
    :effect (and
      (not (at-horizontal ?c ?r ?from))
      (at-horizontal ?c ?r ?to)
      (clear ?r ?from)
      (not (clear ?r ?to))
    )
  )

  (:action car-move-left
    :parameters (?c - car ?r - row ?from ?to - col)
    :precondition (and
      (at-horizontal ?c ?r ?from)
      (next-col ?to ?from)
      (clear ?r ?to)
    )
    :effect (and
      (not (at-horizontal ?c ?r ?from))
      (at-horizontal ?c ?r ?to)
      (clear ?r ?from)
      (not (clear ?r ?to))
    )
  )

  (:action car-move-down
    :parameters (?c - car ?c1 - col ?from ?to - row)
    :precondition (and
      (at-vertical ?c ?from ?c1)
      (next-row ?from ?to)
      (clear ?to ?c1)
    )
    :effect (and
      (not (at-vertical ?c ?from ?c1))
      (at-vertical ?c ?to ?c1)
      (clear ?from ?c1)
      (not (clear ?to ?c1))
    )
  )

  (:action car-move-up
    :parameters (?c - car ?c1 - col ?from ?to - row)
    :precondition (and
      (at-vertical ?c ?from ?c1)
      (next-row ?to ?from)
      (clear ?to ?c1)
    )
    :effect (and
      (not (at-vertical ?c ?from ?c1))
      (at-vertical ?c ?to ?c1)
      (clear ?from ?c1)
      (not (clear ?to ?c1))
    )
  )

  (:action truck-move-right
    :parameters (?t - truck ?r - row ?from1 ?from2 ?to - col)
    :precondition (and
      (at-horizontal ?t ?r ?from1)
      (at-horizontal ?t ?r ?from2)
      (next-col ?from1 ?from2)
      (next-col ?from2 ?to)
      (clear ?r ?to)
    )
    :effect (and
      (not (at-horizontal ?t ?r ?from1))
      (at-horizontal ?t ?r ?to) 
      (clear ?r ?from1)
      (not (clear ?r ?to))
    )
  )

  (:action truck-move-left
    :parameters (?t - truck ?r - row ?from1 ?from2 ?to - col)
    :precondition (and
      (at-horizontal ?t ?r ?from2)
      (at-horizontal ?t ?r ?from1)
      (next-col ?to ?from1)
      (next-col ?from1 ?from2)
      (clear ?r ?to)
    )
    :effect (and
      (not (at-horizontal ?t ?r ?from2)) 
      (at-horizontal ?t ?r ?to) 
      (clear ?r ?from2)
      (not (clear ?r ?to))
    )
  )

  (:action truck-move-down
    :parameters (?t - truck ?c1 - col ?from1 ?from2 ?to - row)
    :precondition (and
      (at-vertical ?t ?from1 ?c1) 
      (at-vertical ?t ?from2 ?c1)
      (next-row ?from1 ?from2)
      (next-row ?from2 ?to) 
      (clear ?to ?c1) 
    )
    :effect (and
      (not (at-vertical ?t ?from1 ?c1)) 
      (at-vertical ?t ?to ?c1) 
      (clear ?from1 ?c1) 
      (not (clear ?to ?c1)) 
    )
  )

  (:action truck-move-up
    :parameters (?t - truck ?c1 - col ?from1 ?from2 ?to - row)
    :precondition (and
      (at-vertical ?t ?from2 ?c1) 
      (at-vertical ?t ?from1 ?c1)
      (next-row ?to ?from1) 
      (next-row ?from1 ?from2) 
      (clear ?to ?c1) 
    )
    :effect (and
      (not (at-vertical ?t ?from2 ?c1)) 
      (at-vertical ?t ?to ?c1)
      (clear ?from2 ?c1)
      (not (clear ?to ?c1)) 
    )
  )
)