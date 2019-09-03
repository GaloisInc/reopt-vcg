def addps1 : instruction :=
  definst "addps" $ do
    pattern fun (v_2619 : reg (bv 128)) (v_2620 : reg (bv 128)) => do
      v_4805 <- getRegister v_2620;
      v_4806 <- eval (extract v_4805 0 32);
      v_4814 <- getRegister v_2619;
      v_4815 <- eval (extract v_4814 0 32);
      v_4825 <- eval (extract v_4805 32 64);
      v_4833 <- eval (extract v_4814 32 64);
      v_4843 <- eval (extract v_4805 64 96);
      v_4851 <- eval (extract v_4814 64 96);
      v_4861 <- eval (extract v_4805 96 128);
      v_4869 <- eval (extract v_4814 96 128);
      setRegister (lhs.of_reg v_2620) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4806 0 1)) (uvalueMInt (extract v_4806 1 9)) (uvalueMInt (extract v_4806 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4815 0 1)) (uvalueMInt (extract v_4815 1 9)) (uvalueMInt (extract v_4815 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4825 0 1)) (uvalueMInt (extract v_4825 1 9)) (uvalueMInt (extract v_4825 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4833 0 1)) (uvalueMInt (extract v_4833 1 9)) (uvalueMInt (extract v_4833 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4843 0 1)) (uvalueMInt (extract v_4843 1 9)) (uvalueMInt (extract v_4843 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4851 0 1)) (uvalueMInt (extract v_4851 1 9)) (uvalueMInt (extract v_4851 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4861 0 1)) (uvalueMInt (extract v_4861 1 9)) (uvalueMInt (extract v_4861 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4869 0 1)) (uvalueMInt (extract v_4869 1 9)) (uvalueMInt (extract v_4869 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2614 : Mem) (v_2615 : reg (bv 128)) => do
      v_9282 <- getRegister v_2615;
      v_9283 <- eval (extract v_9282 0 32);
      v_9291 <- evaluateAddress v_2614;
      v_9292 <- load v_9291 16;
      v_9293 <- eval (extract v_9292 0 32);
      v_9303 <- eval (extract v_9282 32 64);
      v_9311 <- eval (extract v_9292 32 64);
      v_9321 <- eval (extract v_9282 64 96);
      v_9329 <- eval (extract v_9292 64 96);
      v_9339 <- eval (extract v_9282 96 128);
      v_9347 <- eval (extract v_9292 96 128);
      setRegister (lhs.of_reg v_2615) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9283 0 1)) (uvalueMInt (extract v_9283 1 9)) (uvalueMInt (extract v_9283 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9293 0 1)) (uvalueMInt (extract v_9293 1 9)) (uvalueMInt (extract v_9293 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9303 0 1)) (uvalueMInt (extract v_9303 1 9)) (uvalueMInt (extract v_9303 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9311 0 1)) (uvalueMInt (extract v_9311 1 9)) (uvalueMInt (extract v_9311 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9321 0 1)) (uvalueMInt (extract v_9321 1 9)) (uvalueMInt (extract v_9321 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9329 0 1)) (uvalueMInt (extract v_9329 1 9)) (uvalueMInt (extract v_9329 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9339 0 1)) (uvalueMInt (extract v_9339 1 9)) (uvalueMInt (extract v_9339 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9347 0 1)) (uvalueMInt (extract v_9347 1 9)) (uvalueMInt (extract v_9347 9 32)))) 32))));
      pure ()
    pat_end
