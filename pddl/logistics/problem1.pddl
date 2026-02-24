(define (problem log-6)
  (:domain logistics-mini)
  (:objects tr1 - truck
            p1 p2 - pkg
            depot hub store - loc)
  (:init
    (at-truck tr1 depot)
    (at-pkg p1 depot)
    (at-pkg p2 depot)

    (road depot hub) (road hub depot)
    (road hub store) (road store hub)
  )
  ;; 6-step plan exists: load p1, load p2, drive depot->hub, drive hub->store, unload p1, unload p2
  (:goal (and (at-pkg p1 store) (at-pkg p2 store)))
)