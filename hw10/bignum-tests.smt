(val nr@test= nil)

; We computed LargeInteger 0 using only 1, 0, and +
(check-print
  (begin (set nr@test= (LargeInteger fromSmall: 0))
nr@test=)

  0)

; We computed LargeInteger 9 using only 1, 0, and +
(check-print
  (begin
    (set nr@test= (LargeInteger fromSmall: 0))
   

   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   nr@test=
  )
  9)

; We computed LargeInteger 464 using only 1, 0, and +
(check-print
  (begin
    (set nr@test= (LargeInteger fromSmall: 0))
   

   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   nr@test=
  )
  464)

; We computed LargeInteger 15195595871 using only 1, 0, and +
(check-print
  (begin
    (set nr@test= (LargeInteger fromSmall: 0))
   

   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   nr@test=
  )
  15195595871)

; We computed LargeInteger 613046430670287263431 using only 1, 0, and +
(check-print
  (begin
    (set nr@test= (LargeInteger fromSmall: 0))
   

   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((LargeInteger fromSmall: 1) + nr@test=))
   nr@test=
  )
  613046430670287263431)

; We created a LargeInteger with value zero
(check-print
  (LargeInteger fromSmall: 0)
  0)

; We computed LargeInteger 46720623 using literals, *, and +
(check-print
  ((((LargeInteger fromSmall: 347)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   *
    (((LargeInteger fromSmall: 561)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    *
     ((LargeInteger fromSmall: 240)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   +
    ((LargeInteger fromSmall: 543)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  46720623)

; We computed LargeInteger 379243448619952178904098 using literals, *, and +
(check-print
  (((((LargeInteger fromSmall: 685)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 264)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   *
    ((LargeInteger fromSmall: 306)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 639)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
  )
   +
    (((LargeInteger fromSmall: 157)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 460)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    *
     ((LargeInteger fromSmall: 247)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 657)
       +
        ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
      )
     )
    )
   )
  )
   *
    ((((LargeInteger fromSmall: 414)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 842)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    *
     ((LargeInteger fromSmall: 489)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 954)
       +
        ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
      )
     )
    )
   )
    +
     ((LargeInteger fromSmall: 436)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 645)
       +
        ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
      )
     )
    )
   )
  )
  379243448619952178904098)

; We computed LargeInteger 143627197626 using literals, *, and +
(check-print
  ((LargeInteger fromSmall: 626)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 197)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 627)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 143)
         +
          ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
        )
       )
      )
     )
    )
   )
  )
  143627197626)

; We computed LargeInteger 737 - -11 = 748 
(check-print
  (((LargeInteger fromSmall: 737)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   -
    (((LargeInteger fromSmall: 11)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  748)

; We computed LargeInteger -606938 - 632262 = -1239200 
(check-print
  ((((LargeInteger fromSmall: 938)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 606)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   -
    ((LargeInteger fromSmall: 262)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 632)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
  )
  -1239200)

; We computed LargeInteger -434727217379 - -738418210468 = 303690993089 
(check-print
  ((((LargeInteger fromSmall: 379)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 217)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 727)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 434)
         +
          ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
        )
       )
      )
     )
    )
   )
  )
   negated
  )
   -
    (((LargeInteger fromSmall: 468)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 210)
      +
       ((LargeInteger fromSmall: 1000)
       *
        ((LargeInteger fromSmall: 418)
        +
         ((LargeInteger fromSmall: 1000)
         *
          ((LargeInteger fromSmall: 738)
          +
           ((LargeInteger fromSmall: 1000)
           *
            (LargeInteger fromSmall: 0)
          )
         )
        )
       )
      )
     )
    )
   )
    negated
   )
  )
  303690993089)

; We computed LargeInteger -279859 using literals, *, and +
(check-print
  (((((LargeInteger fromSmall: 465)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   -
    ((LargeInteger fromSmall: 124)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
   *
    (((LargeInteger fromSmall: 818)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
   +
    (((LargeInteger fromSmall: 22)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    +
     (((LargeInteger fromSmall: 943)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
     negated
    )
   )
  )
  -279859)

; We computed LargeInteger -1043583 using literals, *, and +
(check-print
  ((((LargeInteger fromSmall: 173)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 194)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   +
    (((LargeInteger fromSmall: 320)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 476)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    negated
   )
  )
   -
    (((LargeInteger fromSmall: 842)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 711)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    +
     (((LargeInteger fromSmall: 741)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 341)
       +
        ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
      )
     )
    )
     -
      ((LargeInteger fromSmall: 147)
      +
       ((LargeInteger fromSmall: 1000)
       *
        ((LargeInteger fromSmall: 292)
        +
         ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
       )
      )
     )
    )
   )
  )
  -1043583)

; We computed LargeInteger 275596888957707898021899537745655844 using 
; literals, *, and +
(check-print
  ((((LargeInteger fromSmall: 421)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 303)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 59)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 386)
         +
          ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
        )
       )
      )
     )
    )
   )
  )
   *
    (((LargeInteger fromSmall: 368)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 10)
      +
       ((LargeInteger fromSmall: 1000)
       *
        ((LargeInteger fromSmall: 762)
        +
         ((LargeInteger fromSmall: 1000)
         *
          ((LargeInteger fromSmall: 769)
          +
           ((LargeInteger fromSmall: 1000)
           *
            (LargeInteger fromSmall: 0)
          )
         )
        )
       )
      )
     )
    )
   )
    *
     ((LargeInteger fromSmall: 617)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 1)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 393)
         +
          ((LargeInteger fromSmall: 1000)
          *
           ((LargeInteger fromSmall: 927)
           +
            ((LargeInteger fromSmall: 1000)
            *
             (LargeInteger fromSmall: 0)
           )
          )
         )
        )
       )
      )
     )
    )
   )
  )
   +
    ((LargeInteger fromSmall: 268)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 599)
      +
       ((LargeInteger fromSmall: 1000)
       *
        ((LargeInteger fromSmall: 33)
        +
         ((LargeInteger fromSmall: 1000)
         *
          ((LargeInteger fromSmall: 420)
          +
           ((LargeInteger fromSmall: 1000)
           *
            (LargeInteger fromSmall: 0)
          )
         )
        )
       )
      )
     )
    )
   )
  )
  275596888957707898021899537745655844)

; We tested -607 = 961 (<False>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 607)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   =
    ((LargeInteger fromSmall: 961)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested -854 = -603 (<False>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 854)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   =
    (((LargeInteger fromSmall: 603)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <False>)

; We tested 217606 = -599094 (<False>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 606)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 217)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   =
    (((LargeInteger fromSmall: 94)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 599)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    negated
   )
  )
  <False>)

; We tested 149 != -874 (<True>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 149)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   !=
    (((LargeInteger fromSmall: 874)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested -303 != -347 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 303)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   !=
    (((LargeInteger fromSmall: 347)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested -657178 != -985487 (<True>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 178)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 657)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   !=
    (((LargeInteger fromSmall: 487)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 985)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    negated
   )
  )
  <True>)

; We tested 955 < 240 (<False>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 955)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   <
    ((LargeInteger fromSmall: 240)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested 438 < 594 (<True>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 438)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   <
    ((LargeInteger fromSmall: 594)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested 109095 < -564877 (<False>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 95)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 109)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   <
    (((LargeInteger fromSmall: 877)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 564)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    negated
   )
  )
  <False>)

; We tested -635 > -678 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 635)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   >
    (((LargeInteger fromSmall: 678)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested 436 > -407 (<True>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 436)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   >
    (((LargeInteger fromSmall: 407)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested 513670 > -676244 (<True>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 670)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 513)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   >
    (((LargeInteger fromSmall: 244)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 676)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    negated
   )
  )
  <True>)

; We tested -71 <= 963 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 71)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   <=
    ((LargeInteger fromSmall: 963)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested 68 <= 763 (<True>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 68)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   <=
    ((LargeInteger fromSmall: 763)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested -698719 <= 993395 (<True>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 719)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 698)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   <=
    ((LargeInteger fromSmall: 395)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 993)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested -370 >= 532 (<False>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 370)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   >=
    ((LargeInteger fromSmall: 532)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested -204 >= -699 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 204)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   >=
    (((LargeInteger fromSmall: 699)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested -889199 >= 200219 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 199)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 889)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   >=
    ((LargeInteger fromSmall: 219)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 200)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
  )
  <False>)

; We tested -241 = -241 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 241)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   =
    (((LargeInteger fromSmall: 241)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested -200 = -200 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 200)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   =
    (((LargeInteger fromSmall: 200)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested 111410 = 111410 (<True>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 410)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 111)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   =
    ((LargeInteger fromSmall: 410)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 111)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested -194 != -194 (<False>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 194)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   !=
    (((LargeInteger fromSmall: 194)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <False>)

; We tested 533 != 533 (<False>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 533)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   !=
    ((LargeInteger fromSmall: 533)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested -585547 != -585547 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 547)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 585)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   !=
    (((LargeInteger fromSmall: 547)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 585)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    negated
   )
  )
  <False>)

; We tested 44 < 44 (<False>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 44)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   <
    ((LargeInteger fromSmall: 44)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested -721 < -721 (<False>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 721)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   <
    (((LargeInteger fromSmall: 721)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <False>)

; We tested 976035 < 976035 (<False>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 35)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 976)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   <
    ((LargeInteger fromSmall: 35)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 976)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
  )
  <False>)

; We tested 959 > 959 (<False>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 959)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   >
    ((LargeInteger fromSmall: 959)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested 897 > 897 (<False>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 897)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   >
    ((LargeInteger fromSmall: 897)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested -158223 > -158223 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 223)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 158)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   >
    (((LargeInteger fromSmall: 223)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 158)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    negated
   )
  )
  <False>)

; We tested -338 <= -338 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 338)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   <=
    (((LargeInteger fromSmall: 338)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested -893 <= -893 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 893)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   negated
  )
   <=
    (((LargeInteger fromSmall: 893)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested 900487 <= 900487 (<True>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 487)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 900)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   <=
    ((LargeInteger fromSmall: 487)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 900)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested 185 >= 185 (<True>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 185)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   >=
    ((LargeInteger fromSmall: 185)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested 910 >= 910 (<True>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 910)
   +
    ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
  )
   >=
    ((LargeInteger fromSmall: 910)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested -420591 >= -420591 (<True>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 591)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 420)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   >=
    (((LargeInteger fromSmall: 591)
    +
     ((LargeInteger fromSmall: 1000)
     *
      ((LargeInteger fromSmall: 420)
      +
       ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
     )
    )
   )
    negated
   )
  )
  <True>)

; We tested -850550 = 332 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 550)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 850)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   =
    ((LargeInteger fromSmall: 332)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested 661612 = -164 (<False>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 612)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 661)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   =
    (((LargeInteger fromSmall: 164)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <False>)

; We tested -937526036699396350 = -213 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 350)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 396)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 699)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 36)
         +
          ((LargeInteger fromSmall: 1000)
          *
           ((LargeInteger fromSmall: 526)
           +
            ((LargeInteger fromSmall: 1000)
            *
             ((LargeInteger fromSmall: 937)
             +
              ((LargeInteger fromSmall: 1000)
              *
               (LargeInteger fromSmall: 0)
             )
            )
           )
          )
         )
        )
       )
      )
     )
    )
   )
  )
   negated
  )
   =
    (((LargeInteger fromSmall: 213)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <False>)

; We tested 652345 != -126 (<True>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 345)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 652)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   !=
    (((LargeInteger fromSmall: 126)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested -64968 != -592 (<True>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 968)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 64)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   !=
    (((LargeInteger fromSmall: 592)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested -438001955579469744 != 679 (<True>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 744)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 469)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 579)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 955)
         +
          ((LargeInteger fromSmall: 1000)
          *
           ((LargeInteger fromSmall: 1)
           +
            ((LargeInteger fromSmall: 1000)
            *
             ((LargeInteger fromSmall: 438)
             +
              ((LargeInteger fromSmall: 1000)
              *
               (LargeInteger fromSmall: 0)
             )
            )
           )
          )
         )
        )
       )
      )
     )
    )
   )
  )
   negated
  )
   !=
    ((LargeInteger fromSmall: 679)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested 829717 < 129 (<False>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 717)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 829)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   <
    ((LargeInteger fromSmall: 129)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested 144043 < 363 (<False>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 43)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 144)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   <
    ((LargeInteger fromSmall: 363)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested -812484207146323460 < 259 (<True>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 460)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 323)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 146)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 207)
         +
          ((LargeInteger fromSmall: 1000)
          *
           ((LargeInteger fromSmall: 484)
           +
            ((LargeInteger fromSmall: 1000)
            *
             ((LargeInteger fromSmall: 812)
             +
              ((LargeInteger fromSmall: 1000)
              *
               (LargeInteger fromSmall: 0)
             )
            )
           )
          )
         )
        )
       )
      )
     )
    )
   )
  )
   negated
  )
   <
    ((LargeInteger fromSmall: 259)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested -129796 > 610 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 796)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 129)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   >
    ((LargeInteger fromSmall: 610)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested 995578 > 264 (<True>), starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 578)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 995)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   >
    ((LargeInteger fromSmall: 264)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested 482862968845189861 > -128 (<True>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 861)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 189)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 845)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 968)
         +
          ((LargeInteger fromSmall: 1000)
          *
           ((LargeInteger fromSmall: 862)
           +
            ((LargeInteger fromSmall: 1000)
            *
             ((LargeInteger fromSmall: 482)
             +
              ((LargeInteger fromSmall: 1000)
              *
               (LargeInteger fromSmall: 0)
             )
            )
           )
          )
         )
        )
       )
      )
     )
    )
   )
  )
   >
    (((LargeInteger fromSmall: 128)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <True>)

; We tested -250924 <= 30 (<True>), starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 924)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 250)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   <=
    ((LargeInteger fromSmall: 30)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <True>)

; We tested 948071 <= 135 (<False>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 71)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 948)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   <=
    ((LargeInteger fromSmall: 135)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested 707990689012636429 <= 997 (<False>),
; starting from literals of class LargeInteger
(check-print
  (((LargeInteger fromSmall: 429)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 636)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 12)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 689)
         +
          ((LargeInteger fromSmall: 1000)
          *
           ((LargeInteger fromSmall: 990)
           +
            ((LargeInteger fromSmall: 1000)
            *
             ((LargeInteger fromSmall: 707)
             +
              ((LargeInteger fromSmall: 1000)
              *
               (LargeInteger fromSmall: 0)
             )
            )
           )
          )
         )
        )
       )
      )
     )
    )
   )
  )
   <=
    ((LargeInteger fromSmall: 997)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
  )
  <False>)

; We tested -415550 >= -439 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 550)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 415)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   >=
    (((LargeInteger fromSmall: 439)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <False>)

; We tested -979189 >= -462 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 189)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 979)
     +
      ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
    )
   )
  )
   negated
  )
   >=
    (((LargeInteger fromSmall: 462)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <False>)

; We tested -140222806074835719 >= -384 (<False>),
; starting from literals of class LargeInteger
(check-print
  ((((LargeInteger fromSmall: 719)
   +
    ((LargeInteger fromSmall: 1000)
    *
     ((LargeInteger fromSmall: 835)
     +
      ((LargeInteger fromSmall: 1000)
      *
       ((LargeInteger fromSmall: 74)
       +
        ((LargeInteger fromSmall: 1000)
        *
         ((LargeInteger fromSmall: 806)
         +
          ((LargeInteger fromSmall: 1000)
          *
           ((LargeInteger fromSmall: 222)
           +
            ((LargeInteger fromSmall: 1000)
            *
             ((LargeInteger fromSmall: 140)
             +
              ((LargeInteger fromSmall: 1000)
              *
               (LargeInteger fromSmall: 0)
             )
            )
           )
          )
         )
        )
       )
      )
     )
    )
   )
  )
   negated
  )
   >=
    (((LargeInteger fromSmall: 384)
    +
     ((LargeInteger fromSmall: 1000) * (LargeInteger fromSmall: 0))
   )
    negated
   )
  )
  <False>)
