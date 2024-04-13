;; Starter code for SmallTalk assignement.
;; Author: Richard Townsend 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;             Exercise 1 classes
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(class Natural
   [subclass-of Magnitude]

   (class-method first:rest: (anInteger aNatural) ; private
      (((anInteger = 0) & (aNatural isZero)) ifTrue:ifFalse:
         {(NatZero new)}
         {((NatNonzero new) first:rest: anInteger aNatural)}
      )
   )
   
   (class-method fromSmall: (anInteger)
      ((anInteger = 0) ifTrue:ifFalse:
      {(NatZero new)}
      {
         (Natural first:rest: (anInteger mod: (Natural base)) 
                              (Natural fromSmall:
                                 (anInteger div: (Natural base))))
      })
   )

   (class-method base () 2) ; private

   ; private methods suggested from textbook (page 672)
   (method modBase () (self subclassResponsibility)) 
   (method divBase () (self subclassResponsibility)) 
   (method timesBase () (self subclassResponsibility)) 
   (method compare:withLt:withEq:withGt: (aNatural ltBlock eqBlock gtBlock) 
      (self subclassResponsibility)) 
   (method plus:carry: (aNatural c) (self subclassResponsibility)) 
   (method minus:borrow: (aNatural c) (self subclassResponsibility)) 

   (method timesDigit:plus: (d r) (self subclassResponsibility)) ; private

   (method = (aNatural) (self leftAsExercise))
   (method < (aNatural) (self leftAsExercise))

   (method + (aNatural) (self leftAsExercise))
   (method * (aNatural) (self subclassResponsibility))
   (method subtract:withDifference:ifNegative: (aNatural diffBlock exnBlock)
      (self leftAsExercise))

   (method sdivmod:with: (n aBlock) (self subclassResponsibility))

   (method decimal () (self leftAsExercise))
   (method isZero  () (self subclassResponsibility))

   ; methods that are already implemented for you
   (method - (aNatural)
      (self subtract:withDifference:ifNegative:
            aNatural
            [block (x) x]
            {(self error: 'Natural-subtraction-went-negative)}))
   (method sdiv: (n) (self sdivmod:with: n [block (q r) q]))
   (method smod: (n) (self sdivmod:with: n [block (q r) r]))
   (method print () ((self decimal) do: [block (x) (x print)]))

   ;private methods for testing
   (method validated ()
    ((self invariant) ifFalse:
      {(self printrep)
       (self error: 'invariant-violation)})
    self)
   (method compare-symbol: (aNat)
    (self compare:withLt:withEq:withGt: aNat {'LT} {'EQ} {'GT}))
)

; Represents a 0 natural number
(class NatZero
   [subclass-of Natural]
   (method invariant () true) ;; private

   (method timesDigit:plus: (d r) (Natural fromSmall: r)) ; private

  ;; for debugging
   (method printrep () (0 print))

   (method isZero () true)
   (method divBase () (NatZero new))
   (method modBase () 0)
   (method timesBase () (NatZero new))



   ; multiplication
   (method * (aNatural) self)
   (method sdivmod:with: (aSmallInteger aBlock)
      (aBlock value:value: self 0))
   
   (method compare:withLt:withEq:withGt: (aNatural ltBlock eqBlock gtBlock)
      ((aNatural isZero) ifTrue:ifFalse:
         {eqBlock}
         {ltBlock}))

   ; addition with a carry bit
   (method plus:carry: (aNatural c)
      ((aNatural isZero) ifTrue:ifFalse:
         {(Natural fromSmall: c)}
         {(aNatural plus:carry: (Natural fromSmall: c) 0)}))
         
   ; subtraction with a borrow bit
   (method minus:borrow: (aNatural b)
      (((aNatural isZero) & (b = 0)) ifTrue:ifFalse:
         {self}
         {(self error: ('Bad Subtraction))}))
)

; Represents a natural number greater than 0
(class NatNonzero
  [subclass-of Natural]
  [ivars m d] ; a non-zero natural number is of the form d + m * b, where d
              ; is an integer representing a digit of base b, and m is a natural
              ; number

   (method isZero () false)
   (method divBase () m)
   (method modBase () d)
   
   (method timesBase ()
      (Natural first:rest: 0 self))

   (method first:rest: (anInteger aNatural) ; private
      (set m aNatural)
      (set d anInteger)  
      self
   )

  (method invariant () (((d < (Natural base)) & (d >= 0)) &  ;; private
                       (((m isZero) & (d = 0)) not)))

  ; addition with a carry bit
  (method plus:carry: (aNatural c) [locals sum least cout]
     (set sum ((d + (aNatural modBase)) + c))
     (set least (sum mod: (Natural base)))
     (set cout  (sum div: (Natural base)))
     (NatNonzero first:rest: least (m plus:carry: (aNatural divBase) cout)))
      
  ; subtraction with a borrow bit
  (method minus:borrow: (aNatural b) [locals diff least bout]
     (set diff (d - ((aNatural modBase) + b)))
     ((diff < 0) ifTrue:ifFalse:
         {(set diff (diff + (Natural base)))
          (set bout 1)}
         {(set bout 0)})
     (NatNonzero first:rest: diff (m minus:borrow: (aNatural divBase) bout)))

  ; multiplication
  (method * (aNatural) [locals d1 d2 m1 m2]
     ; simple method; fastest; based on this law:
     ;   (d + b * m) * n == (d * n) + b * (m * n)
     ((aNatural timesDigit:plus: d 0) + ((m * aNatural) timesBase)))

  (method timesDigit:plus: (dig r) ; private, answers self * d + r
      [locals pp]
      (set pp ((d * dig) + r))
      (NatNonzero first:rest: (pp mod: (Natural base))
                  (m timesDigit:plus: dig (pp div: (Natural base)))))
  
  ;; debugging method
  (method printrep () (m printrep) (', print) (d print))
)

; For testing naturals
(class DebugNat
  [subclass-of Object]
  [ivars nat] ; a natural number
  (class-method of: (aNat) ((self new) init: aNat))
  (method init: (n) (set nat n) self) ; private
  (method print () (nat printrep))
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Put your unit tests for Exercise 1 here
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
      (check-assert ((Natural fromSmall: 0) isZero))
      (check-assert (((Natural fromSmall: 1) isZero) not))
      (check-assert (((Natural fromSmall: 100) isZero) not))
      (check-print (DebugNat of: (Natural fromSmall: 0))
                   0)
      (check-print (DebugNat of: 
                     (Natural fromSmall: ((Natural base) * (Natural base))))
                  0,1,0,0)

      ;; BASE 2 TESTS
      (check-print (DebugNat of: (Natural fromSmall: 1))
                  0,1)
      (check-print (DebugNat of: (Natural fromSmall: 1000))
                  0,1,1,1,1,1,0,1,0,0,0)
      (check-print (DebugNat of: (Natural fromSmall: 1234))
                  0,1,0,0,1,1,0,1,0,0,1,0)
      (check-print (DebugNat of: (Natural fromSmall: 4096))
                  0,1,0,0,0,0,0,0,0,0,0,0,0,0)

      ;; BASE 10 TESTS
      ;; (check-print (DebugNat of: (Natural fromSmall: 1))
      ;;             0,1)
      ;; (check-print (DebugNat of: (Natural fromSmall: 1000))
      ;;             0,1,0,0,0)
      ;; (check-print (DebugNat of: (Natural fromSmall: 1234))
      ;;             0,1,2,3,4)
      ;; (check-print (DebugNat of: (Natural fromSmall: 4096))
      ;;             0,4,0,9,6)

      (check-assert (((NatZero new) divBase) isZero))
      (check-assert (((NatZero new) divBase) isKindOf: NatZero))
      (check-assert (((NatZero new) divBase) isKindOf: Natural))
      (check-expect ((NatZero new) modBase) 0)
      (check-assert (((NatZero new) modBase) = 0))
      (check-assert (((NatZero new) modBase) isKindOf: SmallInteger))
      (check-assert (((NatZero new) timesBase) isZero))
      (check-assert (((NatZero new) timesBase) isKindOf: NatZero))
      (check-assert (((NatZero new) timesBase) isKindOf: Natural))

      (check-assert (((Natural fromSmall: 4) divBase) isKindOf: NatNonzero))
      (check-assert (((Natural fromSmall: 4) divBase) isKindOf: Natural))
      (check-print  (DebugNat of: ((Natural fromSmall: 4) divBase)) 0,1,0)
      (check-print  (DebugNat of: ((Natural fromSmall: 5) divBase)) 0,1,0)
      (check-print  (DebugNat of: ((Natural fromSmall: 6) divBase)) 0,1,1)

      (check-assert (((Natural fromSmall: 4) modBase) isKindOf: SmallInteger))
      (check-print  ((Natural fromSmall: 4) modBase) 0)
      (check-print  ((Natural fromSmall: 5) modBase) 1)
      (check-print  ((Natural fromSmall: 6) modBase) 0)

      (check-assert (((Natural fromSmall: 4) timesBase) isKindOf: NatNonzero))
      (check-assert (((Natural fromSmall: 4) timesBase) isKindOf: Natural))
      (check-print  (DebugNat of: ((Natural fromSmall: 2) timesBase)) 0,1,0,0)
      (check-print  (DebugNat of: ((Natural fromSmall: 5) timesBase)) 0,1,0,1,0)
      (check-print  (DebugNat of: ((Natural fromSmall: 6) timesBase)) 0,1,1,0,0)

      (check-error ((NatZero new) minus:borrow: (Natural fromSmall: 0) 1))
      (check-error ((NatZero new) minus:borrow: (Natural fromSmall: 1) 0))
      (check-assert (((NatZero new) minus:borrow: (Natural fromSmall: 0) 0)
                     isZero))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;             Exercise 2 classes
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(class LargeInteger
  [subclass-of Integer]
  [ivars magnitude]

  (class-method withMagnitude: (aNatural)
      ((self new) magnitude: aNatural))
  (method magnitude: (aNatural) ; private, for initialization
      (set magnitude aNatural)
      self)

  (method magnitude () magnitude)

  (class-method fromSmall: (anInteger)
     ((anInteger isNegative) ifTrue:ifFalse: 
        {(((self fromSmall: 1) + (self fromSmall: ((anInteger + 1) negated)))
          negated)}
        {((LargePositiveInteger new) magnitude: 
                 (Natural fromSmall: anInteger))}))
  (method isZero () (magnitude isZero))
  (method = (anInteger) ((self - anInteger)     isZero))
  (method < (anInteger) ((self - anInteger) isNegative))

  (method div: (n) (self sdiv: n))
  (method mod: (n) (self smod: n))

  (method sdiv: (n) (self subclassResponsibility))
  (method smod: (n) (self - ((LargeInteger fromSmall: n) * (self sdiv: n))))
)

; Represents a positive integer
(class LargePositiveInteger
  [subclass-of LargeInteger]


  ;; short division (already implemented for you)
  (method sdiv: (anInteger)
    ((anInteger isStrictlyPositive) ifTrue:ifFalse: 
       {(LargePositiveInteger withMagnitude:  (magnitude sdiv: anInteger))}
       {((((self - (LargeInteger fromSmall: anInteger)) -
                                                  (LargeInteger fromSmall: 1))
             sdiv: (anInteger negated))
            negated)}))
)

;; Represents a negative integer
(class LargeNegativeInteger
  [subclass-of LargeInteger]



  ;; short division (already implemented for you)
  (method sdiv: (anInteger)
    ((self negated) sdiv: (anInteger negated)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Put your unit tests for Exercise 2 here
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
