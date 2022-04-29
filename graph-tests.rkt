#lang racket
(require "adi.rkt" "labeller.rkt" "graph.rkt")
(require rackunit)


(define if-exp-true
'(if (label g50839) (prim (label g50840) #t) (prim (label g50841) 1) (prim (label g50842) 2)))

(define if-exp-true-graph (cdr (run-and-get-graph if-exp-true #f)))

(check-true (has-edge?  if-exp-true-graph 'g50839 'g50840))
(check-true (has-edge?  if-exp-true-graph 'g50840 'g50841))
(check-true (has-edge/back?  if-exp-true-graph  'g50840 'g50839))
(check-true (has-edge/back?  if-exp-true-graph 'g50841 'g50840 ))

(define if-exp-false
  '(if (label g50839) (prim (label g50840) #f) (prim (label g50841) 1) (prim (label g50842) 2)))

(define if-exp-false-graph (cdr (run-and-get-graph if-exp-false #f)))

(check-true (has-edge?  if-exp-false-graph 'g50839 'g50840))
(check-true (has-edge/back?  if-exp-false-graph 'g50840 'g50839))
(check-true (has-edge?  if-exp-false-graph  'g50840 'g50842))
(check-true (has-edge/back?  if-exp-false-graph 'g50842 'g50840 ))

(define let-exp '(let (label g377586) ((x (prim (label g377587) 1))) (prim (label g377588) 2)))

(define let-graph (cdr (run-and-get-graph let-exp #f)))
(check-true (has-edge? let-graph 'g377586 'g377587))
(check-true (has-edge/back? let-graph 'g377587 'g377586))
(check-true (has-edge? let-graph 'g377587 'g377588))
(check-true (has-edge/back? let-graph 'g377588 'g377587))

(define arith-with-syscall '(app (label g373868) ((var (label g373869) =) (prim (label g373870) 0)
                                                                          (syscall (label g373871) fork))))
(define arith-with-syscall-graph (cdr (run-and-get-graph arith-with-syscall #f)))



(define if-exp-ambig
  '(if (label g373867)
       (app (label g373868) ((var (label g373869) =) (prim (label g373870) 0) (syscall (label g373871) fork)))
       (prim (label g373872) 1)
       (prim (label g373873) 2)))

(define if-exp-ambig-graph (cdr (run-and-get-graph if-exp-ambig #f)))


(define app-ex '(app (label g429250) ((λ (label g429251) (x) (var (label g429252) x)) (prim (label g429253) 1))))
(define app-graph (cdr (run-and-get-graph app-ex #f)))
(check-true (has-edge? app-graph 'g429250 'g429251))
(check-true (has-edge/back? app-graph 'g429251 'g429250))
(check-true (has-edge? app-graph 'g429251 'g429253))
(check-true (has-edge/back? app-graph 'g429253 'g429251))
(check-true (has-edge? app-graph 'g429253 'g429252))
(check-true (has-edge/back? app-graph 'g429252 'g429253))


(define syscall-ex `(syscall (label g499251) read
                              (prim (label g499252) 1)
                              (prim (label g499253) 2)))
(define syscall-graph (cdr (run-and-get-graph syscall-ex #f)))
(check-true (has-edge? syscall-graph 'g499252 'g499253))
(check-true (has-edge? syscall-graph 'g499253 'g499251))

(define syscall-nest-noargs '(app (label g36342) ((var (label g36343) =) (prim (label g36344) 0) (syscall (label g36345) fork))))
(define syscall-nest-noargs-graph (cdr (run-and-get-graph syscall-nest-noargs #f)))


(define syscall-nest '(app (label g514150)
                           ((var (label g514151) =)
                            (prim (label g514152) 0)
                            (syscall (label g514153) read (prim (label g514154) 1)
                                     (prim (label g514155) 2)))))

(define syscall-nest-graph (cdr (run-and-get-graph syscall-nest #f)))
(check-true (has-edge? syscall-nest-graph 'g514150 'g514151))
(check-true (has-edge? syscall-nest-graph 'g514151 'g514152))
(check-true (has-edge? syscall-nest-graph 'g514152 'g514154))
(check-true (has-edge? syscall-nest-graph 'g514154 'g514155))
(check-true (has-edge? syscall-nest-graph 'g514155 'g514153))
(check-false (has-edge? syscall-nest-graph 'g514153 'g514154))


(define ex '(let [(f (λ (x) (syscall fork)))]
              (if (f 1) #t #f)))
(define ex-label
  '(let (label g417216)
     ((f (λ (label g417217) (x) (syscall (label g417218) fork))))
     (if (label g417219)
         (app (label g417220) ((var (label g417221) f) (prim (label g417222) 1)))
         (prim (label g417223) #t) (prim (label g417224) #f))))
(define g (cdr (run-and-get-graph ex-label #f)))


