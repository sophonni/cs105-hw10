
(val nr@test= nil)

; We computed Natural 0 using only 1, 0, and +
(check-print
  (begin (set nr@test= (Natural fromSmall: 0))
nr@test=)

  0)

; We computed Natural 8 using only 1, 0, and +
(check-print
  (begin
    (set nr@test= (Natural fromSmall: 0))
   

   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   nr@test=
  )
  8)

; We computed Natural 256 using only 1, 0, and +
(check-print
  (begin
    (set nr@test= (Natural fromSmall: 0))
   

   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   nr@test=
  )
  256)

; We computed Natural 34256018400 using only 1, 0, and +
(check-print
  (begin
    (set nr@test= (Natural fromSmall: 0))
   

   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   nr@test=
  )
  34256018400)

; We computed Natural 961429169913446147099 using only 1, 0, and +
(check-print
  (begin
    (set nr@test= (Natural fromSmall: 0))
   

   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   
   (set nr@test= (nr@test= + nr@test=))
   
   (set nr@test= ((Natural fromSmall: 1) + nr@test=))
   nr@test=
  )
  961429169913446147099)

; We created a Natural with value zero
(check-print
  (Natural fromSmall: 0)
  0)

; We computed Natural 222434471 using literals, *, and +
(check-print
  ((((Natural fromSmall: 84)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   +
    ((Natural fromSmall: 203)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
   *
    (((Natural fromSmall: 28)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
    +
     (((Natural fromSmall: 847)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
     *
      ((Natural fromSmall: 915)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  222434471)

; We computed Natural 567350 using literals, *, and +
(check-print
  ((Natural fromSmall: 350)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 567)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
  567350)

; We computed Natural 10499483997 using literals, *, and +
(check-print
  ((Natural fromSmall: 997)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 483)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 499)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 10)
         +
          ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
        )
       )
      )
     )
    )
   )
  )
  10499483997)

; We computed Natural 369 - 10 = 359 
(check-print
  (((Natural fromSmall: 369)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   -
    ((Natural fromSmall: 10)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  359)

; We computed Natural 367615 - 60514 = 307101 
(check-print
  (((Natural fromSmall: 615)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 367)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   -
    ((Natural fromSmall: 514)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 60)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  307101)

; We computed Natural 817675415579 - 399508323163 = 418167092416 
(check-print
  (((Natural fromSmall: 579)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 415)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 675)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 817)
         +
          ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
        )
       )
      )
     )
    )
   )
  )
   -
    ((Natural fromSmall: 163)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 323)
      +
       ((Natural fromSmall: 1000)
       *
        ((Natural fromSmall: 508)
        +
         ((Natural fromSmall: 1000)
         *
          ((Natural fromSmall: 399)
          +
           ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
         )
        )
       )
      )
     )
    )
   )
  )
  418167092416)

; We tested 384 = 336 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 384)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   =
    ((Natural fromSmall: 336)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 104 = 824 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 104)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   =
    ((Natural fromSmall: 824)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 478524 = 977233 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 524)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 478)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   =
    ((Natural fromSmall: 233)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 977)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <False>)

; We tested 271 != 447 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 271)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   !=
    ((Natural fromSmall: 447)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 787 != 235 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 787)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   !=
    ((Natural fromSmall: 235)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 888391 != 980169 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 391)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 888)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   !=
    ((Natural fromSmall: 169)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 980)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested 831 < 498 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 831)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   <
    ((Natural fromSmall: 498)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 147 < 951 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 147)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   <
    ((Natural fromSmall: 951)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 577383 < 818121 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 383)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 577)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   <
    ((Natural fromSmall: 121)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 818)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested 499 > 224 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 499)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   >
    ((Natural fromSmall: 224)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 613 > 562 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 613)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   >
    ((Natural fromSmall: 562)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 353610 > 187158 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 610)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 353)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   >
    ((Natural fromSmall: 158)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 187)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested 527 <= 336 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 527)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   <=
    ((Natural fromSmall: 336)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 873 <= 689 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 873)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   <=
    ((Natural fromSmall: 689)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 792337 <= 187613 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 337)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 792)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   <=
    ((Natural fromSmall: 613)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 187)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <False>)

; We tested 27 >= 88 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 27)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   >=
    ((Natural fromSmall: 88)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 364 >= 658 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 364)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   >=
    ((Natural fromSmall: 658)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 266537 >= 336723 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 537)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 266)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   >=
    ((Natural fromSmall: 723)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 336)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <False>)

; We tested 255 = 255 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 255)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   =
    ((Natural fromSmall: 255)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 215 = 215 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 215)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   =
    ((Natural fromSmall: 215)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 390236 = 390236 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 236)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 390)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   =
    ((Natural fromSmall: 236)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 390)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested 166 != 166 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 166)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   !=
    ((Natural fromSmall: 166)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 526 != 526 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 526)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   !=
    ((Natural fromSmall: 526)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 87307 != 87307 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 307)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 87)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   !=
    ((Natural fromSmall: 307)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 87)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <False>)

; We tested 982 < 982 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 982)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   <
    ((Natural fromSmall: 982)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 41 < 41 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 41)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   <
    ((Natural fromSmall: 41)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 341587 < 341587 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 587)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 341)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   <
    ((Natural fromSmall: 587)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 341)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <False>)

; We tested 719 > 719 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 719)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   >
    ((Natural fromSmall: 719)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 405 > 405 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 405)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   >
    ((Natural fromSmall: 405)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 279141 > 279141 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 141)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 279)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   >
    ((Natural fromSmall: 141)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 279)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <False>)

; We tested 816 <= 816 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 816)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   <=
    ((Natural fromSmall: 816)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 730 <= 730 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 730)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   <=
    ((Natural fromSmall: 730)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 742086 <= 742086 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 86)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 742)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   <=
    ((Natural fromSmall: 86)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 742)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested 794 >= 794 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 794)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   >=
    ((Natural fromSmall: 794)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 420 >= 420 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 420)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   >=
    ((Natural fromSmall: 420)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 468173 >= 468173 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 173)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 468)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   >=
    ((Natural fromSmall: 173)
    +
     ((Natural fromSmall: 1000)
     *
      ((Natural fromSmall: 468)
      +
       ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
     )
    )
   )
  )
  <True>)

; We tested 166044 = 753 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 44)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 166)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   =
    ((Natural fromSmall: 753)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 123135 = 351 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 135)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 123)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   =
    ((Natural fromSmall: 351)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 409442330988408065 = 667 (<False>),
; starting from literals of class Natural
(check-print
  (((Natural fromSmall: 65)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 408)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 988)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 330)
         +
          ((Natural fromSmall: 1000)
          *
           ((Natural fromSmall: 442)
           +
            ((Natural fromSmall: 1000)
            *
             ((Natural fromSmall: 409)
             +
              ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
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
   =
    ((Natural fromSmall: 667)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 760143 != 19 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 143)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 760)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   !=
    ((Natural fromSmall: 19)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 518 != 644 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 518)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 0)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   !=
    ((Natural fromSmall: 644)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 884414161029219975 != 414 (<True>),
; starting from literals of class Natural
(check-print
  (((Natural fromSmall: 975)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 219)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 29)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 161)
         +
          ((Natural fromSmall: 1000)
          *
           ((Natural fromSmall: 414)
           +
            ((Natural fromSmall: 1000)
            *
             ((Natural fromSmall: 884)
             +
              ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
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
   !=
    ((Natural fromSmall: 414)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 339086 < 648 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 86)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 339)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   <
    ((Natural fromSmall: 648)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 280740 < 451 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 740)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 280)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   <
    ((Natural fromSmall: 451)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 458385627659844969 < 205 (<False>),
; starting from literals of class Natural
(check-print
  (((Natural fromSmall: 969)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 844)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 659)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 627)
         +
          ((Natural fromSmall: 1000)
          *
           ((Natural fromSmall: 385)
           +
            ((Natural fromSmall: 1000)
            *
             ((Natural fromSmall: 458)
             +
              ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
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
   <
    ((Natural fromSmall: 205)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 309716 > 269 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 716)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 309)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   >
    ((Natural fromSmall: 269)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 875426 > 182 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 426)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 875)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   >
    ((Natural fromSmall: 182)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 189175315929209748 > 251 (<True>),
; starting from literals of class Natural
(check-print
  (((Natural fromSmall: 748)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 209)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 929)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 315)
         +
          ((Natural fromSmall: 1000)
          *
           ((Natural fromSmall: 175)
           +
            ((Natural fromSmall: 1000)
            *
             ((Natural fromSmall: 189)
             +
              ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
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
    ((Natural fromSmall: 251)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 333189 <= 489 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 189)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 333)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   <=
    ((Natural fromSmall: 489)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 180914 <= 221 (<False>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 914)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 180)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   <=
    ((Natural fromSmall: 221)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 907349120027693160 <= 902 (<False>),
; starting from literals of class Natural
(check-print
  (((Natural fromSmall: 160)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 693)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 27)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 120)
         +
          ((Natural fromSmall: 1000)
          *
           ((Natural fromSmall: 349)
           +
            ((Natural fromSmall: 1000)
            *
             ((Natural fromSmall: 907)
             +
              ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
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
    ((Natural fromSmall: 902)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <False>)

; We tested 937073 >= 132 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 73)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 937)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   >=
    ((Natural fromSmall: 132)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 659572 >= 917 (<True>), starting from literals of class Natural
(check-print
  (((Natural fromSmall: 572)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 659)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   >=
    ((Natural fromSmall: 917)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We tested 271887435742841496 >= 306 (<True>),
; starting from literals of class Natural
(check-print
  (((Natural fromSmall: 496)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 841)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 742)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 435)
         +
          ((Natural fromSmall: 1000)
          *
           ((Natural fromSmall: 887)
           +
            ((Natural fromSmall: 1000)
            *
             ((Natural fromSmall: 271)
             +
              ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
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
   >=
    ((Natural fromSmall: 306)
    +
     ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
   )
  )
  <True>)

; We computed Natural 482 div 8 = 60 
(check-print
  (((Natural fromSmall: 482)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   sdiv:
   8
  )
  60)

; We computed Natural 623371 div 2 = 311685 
(check-print
  (((Natural fromSmall: 371)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 623)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   sdiv:
   2
  )
  311685)

; We computed Natural 730681078035 div 1 = 730681078035 
(check-print
  (((Natural fromSmall: 35)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 78)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 681)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 730)
         +
          ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
        )
       )
      )
     )
    )
   )
  )
   sdiv:
   1
  )
  730681078035)

; We computed Natural 107 div 10 = 10 
(check-print
  (((Natural fromSmall: 107)
   +
    ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
  )
   sdiv:
   10
  )
  10)

; We computed Natural 259648 div 10 = 25964 
(check-print
  (((Natural fromSmall: 648)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 259)
     +
      ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
    )
   )
  )
   sdiv:
   10
  )
  25964)

; We computed Natural 582490164110 div 10 = 58249016411 
(check-print
  (((Natural fromSmall: 110)
   +
    ((Natural fromSmall: 1000)
    *
     ((Natural fromSmall: 164)
     +
      ((Natural fromSmall: 1000)
      *
       ((Natural fromSmall: 490)
       +
        ((Natural fromSmall: 1000)
        *
         ((Natural fromSmall: 582)
         +
          ((Natural fromSmall: 1000) * (Natural fromSmall: 0))
        )
       )
      )
     )
    )
   )
  )
   sdiv:
   10
  )
  58249016411)
