def vhaddpd1 : instruction :=
  definst "vhaddpd" $ do
    pattern fun (v_3487 : reg (bv 128)) (v_3488 : reg (bv 128)) (v_3489 : reg (bv 128)) => do
      v_12942 <- getRegister v_3487;
      v_12943 <- eval (extract v_12942 64 128);
      v_12951 <- eval (extract v_12942 0 64);
      v_12961 <- getRegister v_3488;
      v_12962 <- eval (extract v_12961 64 128);
      v_12970 <- eval (extract v_12961 0 64);
      setRegister (lhs.of_reg v_3489) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12943 0 1)) (uvalueMInt (extract v_12943 1 12)) (uvalueMInt (extract v_12943 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12951 0 1)) (uvalueMInt (extract v_12951 1 12)) (uvalueMInt (extract v_12951 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12962 0 1)) (uvalueMInt (extract v_12962 1 12)) (uvalueMInt (extract v_12962 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12970 0 1)) (uvalueMInt (extract v_12970 1 12)) (uvalueMInt (extract v_12970 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3498 : reg (bv 256)) (v_3499 : reg (bv 256)) (v_3500 : reg (bv 256)) => do
      v_12987 <- getRegister v_3498;
      v_12988 <- eval (extract v_12987 64 128);
      v_12996 <- eval (extract v_12987 0 64);
      v_13006 <- getRegister v_3499;
      v_13007 <- eval (extract v_13006 64 128);
      v_13015 <- eval (extract v_13006 0 64);
      v_13026 <- eval (extract v_12987 192 256);
      v_13034 <- eval (extract v_12987 128 192);
      v_13044 <- eval (extract v_13006 192 256);
      v_13052 <- eval (extract v_13006 128 192);
      setRegister (lhs.of_reg v_3500) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12988 0 1)) (uvalueMInt (extract v_12988 1 12)) (uvalueMInt (extract v_12988 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12996 0 1)) (uvalueMInt (extract v_12996 1 12)) (uvalueMInt (extract v_12996 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_13007 0 1)) (uvalueMInt (extract v_13007 1 12)) (uvalueMInt (extract v_13007 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_13015 0 1)) (uvalueMInt (extract v_13015 1 12)) (uvalueMInt (extract v_13015 12 64)))) 64)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_13026 0 1)) (uvalueMInt (extract v_13026 1 12)) (uvalueMInt (extract v_13026 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_13034 0 1)) (uvalueMInt (extract v_13034 1 12)) (uvalueMInt (extract v_13034 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_13044 0 1)) (uvalueMInt (extract v_13044 1 12)) (uvalueMInt (extract v_13044 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_13052 0 1)) (uvalueMInt (extract v_13052 1 12)) (uvalueMInt (extract v_13052 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_3484 : Mem) (v_3482 : reg (bv 128)) (v_3483 : reg (bv 128)) => do
      v_23483 <- evaluateAddress v_3484;
      v_23484 <- load v_23483 16;
      v_23485 <- eval (extract v_23484 64 128);
      v_23493 <- eval (extract v_23484 0 64);
      v_23503 <- getRegister v_3482;
      v_23504 <- eval (extract v_23503 64 128);
      v_23512 <- eval (extract v_23503 0 64);
      setRegister (lhs.of_reg v_3483) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23485 0 1)) (uvalueMInt (extract v_23485 1 12)) (uvalueMInt (extract v_23485 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23493 0 1)) (uvalueMInt (extract v_23493 1 12)) (uvalueMInt (extract v_23493 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23504 0 1)) (uvalueMInt (extract v_23504 1 12)) (uvalueMInt (extract v_23504 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23512 0 1)) (uvalueMInt (extract v_23512 1 12)) (uvalueMInt (extract v_23512 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3493 : Mem) (v_3494 : reg (bv 256)) (v_3495 : reg (bv 256)) => do
      v_23524 <- evaluateAddress v_3493;
      v_23525 <- load v_23524 32;
      v_23526 <- eval (extract v_23525 64 128);
      v_23534 <- eval (extract v_23525 0 64);
      v_23544 <- getRegister v_3494;
      v_23545 <- eval (extract v_23544 64 128);
      v_23553 <- eval (extract v_23544 0 64);
      v_23564 <- eval (extract v_23525 192 256);
      v_23572 <- eval (extract v_23525 128 192);
      v_23582 <- eval (extract v_23544 192 256);
      v_23590 <- eval (extract v_23544 128 192);
      setRegister (lhs.of_reg v_3495) (concat (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23526 0 1)) (uvalueMInt (extract v_23526 1 12)) (uvalueMInt (extract v_23526 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23534 0 1)) (uvalueMInt (extract v_23534 1 12)) (uvalueMInt (extract v_23534 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23545 0 1)) (uvalueMInt (extract v_23545 1 12)) (uvalueMInt (extract v_23545 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23553 0 1)) (uvalueMInt (extract v_23553 1 12)) (uvalueMInt (extract v_23553 12 64)))) 64)) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23564 0 1)) (uvalueMInt (extract v_23564 1 12)) (uvalueMInt (extract v_23564 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23572 0 1)) (uvalueMInt (extract v_23572 1 12)) (uvalueMInt (extract v_23572 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23582 0 1)) (uvalueMInt (extract v_23582 1 12)) (uvalueMInt (extract v_23582 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_23590 0 1)) (uvalueMInt (extract v_23590 1 12)) (uvalueMInt (extract v_23590 12 64)))) 64)));
      pure ()
    pat_end
