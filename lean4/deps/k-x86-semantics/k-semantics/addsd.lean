def addsd1 : instruction :=
  definst "addsd" $ do
    pattern fun (v_2641 : reg (bv 128)) (v_2642 : reg (bv 128)) => do
      v_4918 <- getRegister v_2642;
      v_4922 <- getRegister v_2641;
      setRegister (lhs.of_reg v_2642) (concat (extract v_4918 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4918 64 128) 53 11) (MInt2Float (extract v_4922 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2636 : Mem) (v_2637 : reg (bv 128)) => do
      v_9184 <- getRegister v_2637;
      v_9188 <- evaluateAddress v_2636;
      v_9189 <- load v_9188 8;
      setRegister (lhs.of_reg v_2637) (concat (extract v_9184 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9184 64 128) 53 11) (MInt2Float v_9189 53 11)) 64));
      pure ()
    pat_end
