def addsd1 : instruction :=
  definst "addsd" $ do
    pattern fun (v_2654 : reg (bv 128)) (v_2655 : reg (bv 128)) => do
      v_4999 <- getRegister v_2655;
      v_5001 <- eval (extract v_4999 64 128);
      v_5009 <- getRegister v_2654;
      v_5010 <- eval (extract v_5009 64 128);
      setRegister (lhs.of_reg v_2655) (concat (extract v_4999 0 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5001 0 1)) (uvalueMInt (extract v_5001 1 12)) (uvalueMInt (extract v_5001 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5010 0 1)) (uvalueMInt (extract v_5010 1 12)) (uvalueMInt (extract v_5010 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2649 : Mem) (v_2650 : reg (bv 128)) => do
      v_9396 <- getRegister v_2650;
      v_9398 <- eval (extract v_9396 64 128);
      v_9406 <- evaluateAddress v_2649;
      v_9407 <- load v_9406 8;
      setRegister (lhs.of_reg v_2650) (concat (extract v_9396 0 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9398 0 1)) (uvalueMInt (extract v_9398 1 12)) (uvalueMInt (extract v_9398 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9407 0 1)) (uvalueMInt (extract v_9407 1 12)) (uvalueMInt (extract v_9407 12 64)))) 64));
      pure ()
    pat_end
