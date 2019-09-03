def hsubpd1 : instruction :=
  definst "hsubpd" $ do
    pattern fun (v_2845 : reg (bv 128)) (v_2846 : reg (bv 128)) => do
      v_5103 <- getRegister v_2845;
      v_5104 <- eval (extract v_5103 64 128);
      v_5112 <- eval (extract v_5103 0 64);
      v_5122 <- getRegister v_2846;
      v_5123 <- eval (extract v_5122 64 128);
      v_5131 <- eval (extract v_5122 0 64);
      setRegister (lhs.of_reg v_2846) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5104 0 1)) (uvalueMInt (extract v_5104 1 12)) (uvalueMInt (extract v_5104 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5112 0 1)) (uvalueMInt (extract v_5112 1 12)) (uvalueMInt (extract v_5112 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5123 0 1)) (uvalueMInt (extract v_5123 1 12)) (uvalueMInt (extract v_5123 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5131 0 1)) (uvalueMInt (extract v_5131 1 12)) (uvalueMInt (extract v_5131 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2839 : Mem) (v_2841 : reg (bv 128)) => do
      v_9079 <- evaluateAddress v_2839;
      v_9080 <- load v_9079 16;
      v_9081 <- eval (extract v_9080 64 128);
      v_9089 <- eval (extract v_9080 0 64);
      v_9099 <- getRegister v_2841;
      v_9100 <- eval (extract v_9099 64 128);
      v_9108 <- eval (extract v_9099 0 64);
      setRegister (lhs.of_reg v_2841) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9081 0 1)) (uvalueMInt (extract v_9081 1 12)) (uvalueMInt (extract v_9081 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9089 0 1)) (uvalueMInt (extract v_9089 1 12)) (uvalueMInt (extract v_9089 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9100 0 1)) (uvalueMInt (extract v_9100 1 12)) (uvalueMInt (extract v_9100 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9108 0 1)) (uvalueMInt (extract v_9108 1 12)) (uvalueMInt (extract v_9108 12 64)))) 64));
      pure ()
    pat_end
