;--------------------------------------------------------------------------------------------------------


;MERGED FEATURES IN PDDL (PROBLEM FILE) VER. 2: PROBLEM FILE REFLECTING OPTIMIZED DOMAIN PDDL FILE
;This problem file should work for both featsmerged_domainver2 and featsmerged_domainver3 (search tree and post-
;processing multi-step actions), which is nice.
;References: https://fareskalaboud.github.io/LearnPDDL/, https://editor.planning.domains/#
;Debugging the features and changing representation/configuration using PDDL and LLM suggestions
;No runner for any configuration yet

;From here, I need to convert/merge this optimized version back to mergedfeatsver2 & mergedfeatsver3 files in python


;--------------------------------------------------------------------------------------------------------

(define (problem rushhour-simple)
  (:domain rush-hour)
  (:objects
    R A B - car
    T1 T2 - truck
    r1 r2 r3 r4 r5 r6 - row
    c1 c2 c3 c4 c5 c6 - col
  )

  (:init
    (next-row r1 r2) (next-row r2 r3) (next-row r3 r4) (next-row r4 r5) (next-row r5 r6)
    (next-col c1 c2) (next-col c2 c3) (next-col c3 c4) (next-col c4 c5) (next-col c5 c6)
    (at-horizontal R r3 c1)
    (at-horizontal A r1 c1)
    (at-vertical B r4 c3)
    (at-vertical T1 r3 c2)
    (at-vertical T1 r4 c2)
    (at-vertical T2 r2 c3)
    (at-vertical T2 r3 c3)
    (clear r1 c2) (clear r1 c3) (clear r1 c4) (clear r1 c5) (clear r1 c6)
    (clear r2 c1) (clear r2 c2) (clear r2 c4) (clear r2 c5) (clear r2 c6)
    (clear r3 c4) (clear r3 c5) (clear r3 c6)
    (clear r4 c1) (clear r4 c4) (clear r4 c5) (clear r4 c6)
    (clear r5 c1) (clear r5 c2) (clear r5 c3) (clear r5 c4) (clear r5 c5) (clear r5 c6)
    (clear r6 c1) (clear r6 c2) (clear r6 c3) (clear r6 c4) (clear r6 c5) (clear r6 c6)
  )

  (:goal
    (and
      (at-horizontal R r3 c6)
      (at-vertical T1 r1 c2)
      (at-vertical T1 r2 c2)
    )
  )
)