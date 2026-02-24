(define (problem assembly-6)
  (:domain assembly-line)
  (:objects
    part1 - part
    welder cutter drill - tool
    s1 s2 s3 - station
  )
  (:init
    (robot-at s1)
    (next s1 s2) (next s2 s3)

    (at-tool welder s1)
    (at-tool cutter s2)
    (at-tool drill  s3)

    (at-part part1 s3)
  )
  ;; 6-step-ish plan:
  ;; move s1->s2, pickup cutter, move s2->s3, process part1 with cutter, assemble part1, (optional move doesn't matter if you keep goal simple)
  (:goal (and (assembled part1)))
)