def addsubpd1 : instruction :=
  definst "addsubpd" $ do
    pattern fun (v_2672 : reg (bv 128)) (v_2673 : reg (bv 128)) => do
      v_5053 <- getRegister v_2673;
      v_5054 <- eval (extract v_5053 0 64);
      v_5062 <- getRegister v_2672;
      v_5063 <- eval (extract v_5062 0 64);
      v_5073 <- eval (extract v_5053 64 128);
      v_5081 <- eval (extract v_5062 64 128);
      setRegister (lhs.of_reg v_2673) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5054 0 1)) (uvalueMInt (extract v_5054 1 12)) (uvalueMInt (extract v_5054 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5063 0 1)) (uvalueMInt (extract v_5063 1 12)) (uvalueMInt (extract v_5063 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5073 0 1)) (uvalueMInt (extract v_5073 1 12)) (uvalueMInt (extract v_5073 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5081 0 1)) (uvalueMInt (extract v_5081 1 12)) (uvalueMInt (extract v_5081 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2667 : Mem) (v_2668 : reg (bv 128)) => do
      v_9442 <- getRegister v_2668;
      v_9443 <- eval (extract v_9442 0 64);
      v_9451 <- evaluateAddress v_2667;
      v_9452 <- load v_9451 16;
      v_9453 <- eval (extract v_9452 0 64);
      v_9463 <- eval (extract v_9442 64 128);
      v_9471 <- eval (extract v_9452 64 128);
      setRegister (lhs.of_reg v_2668) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9443 0 1)) (uvalueMInt (extract v_9443 1 12)) (uvalueMInt (extract v_9443 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9453 0 1)) (uvalueMInt (extract v_9453 1 12)) (uvalueMInt (extract v_9453 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9463 0 1)) (uvalueMInt (extract v_9463 1 12)) (uvalueMInt (extract v_9463 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9471 0 1)) (uvalueMInt (extract v_9471 1 12)) (uvalueMInt (extract v_9471 12 64)))) 64));
      pure ()
    pat_end
