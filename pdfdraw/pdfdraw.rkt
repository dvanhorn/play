#lang racket
(provide (all-defined-out))
(require slideshow/pict
         lang/posn
         racket/draw)

(define *canvas* #f)
(define *blank* #f)

(define (start width height)
  (when *canvas* (error "Canvas already started" *canvas*))
  (set! *blank* (blank width height))
  (set! *canvas* *blank*)
  #true)

(define (stop)
  (unless *canvas*
    (error "No canvas started"))
  (define pdf (new pdf-dc%))
  (send pdf start-doc "Printing...")
  (send pdf start-page)
  (draw-pict *canvas* pdf 0 0)
  (send pdf end-page)
  (send pdf end-doc)
  true)

(define (put x y img)
  (unless *canvas* (error "No canvas started"))
  (set! *canvas* (pin-over *canvas* x y img))
  #true)

(define (draw-circle p r c)
  (put (- (posn-x p) r)
       (- (posn-y p) r)
       (colorize (circle (* 2 r))
                 (symbol->string c))))

(define (draw-solid-disk p r c)
  (put (- (posn-x p) r)
       (- (posn-y p) r)
       (colorize (disk (* 2 r))
                 (symbol->string c))))

(define (draw-solid-rect ul width height c)
  (put (posn-x ul)
       (posn-y ul)
       (colorize (filled-rectangle width height)
                 (symbol->string c))))

(define (draw-solid-line strt end c)
  (define x0 (posn-x strt))
  (define y0 (posn-y strt))
  (define x1 (posn-x end))
  (define y1 (posn-y end))
  (put x0 y0
       (colorize (pip-line (- x1 x0) (- y1 y0) 1)
                 (symbol->string c))))

(define (draw-solid-string p s)
  (define txt (text s))
  (put (posn-x p)
       (- (posn-y p) (pict-height txt))
       txt))

(define (sleep-for-a-while s)
  (sleep s))

(define (clear-circle p r c)
  (draw-circle p r 'white))

(define (clear-solid-disk p r c)
  (draw-solid-disk p r 'white))

(define (clear-solid-rect ul width height c)
  (draw-solid-rect ul width height 'white))

(define (clear-solid-line strt end c)
  (draw-solid-line strt end 'white))

(define (clear-solid-string p s)
  (define txt (text s))
  (put (posn-x p)
       (- (posn-y p) (pict-height txt))
       (colorize txt "white")))

(define (clear-all)
  (set! *canvas* *blank*)
  #true)


  