def setnle1 : instruction :=
  definst "setnle" $ do
    pattern fun (v_2687 : reg (bv 8)) => do
      v_4183 <- getRegister zf;
      v_4185 <- getRegister sf;
      v_4186 <- getRegister of;
      setRegister (lhs.of_reg v_2687) (mux (bit_and (notBool_ v_4183) (eq v_4185 v_4186)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2680 : Mem) => do
      v_8006 <- evaluateAddress v_2680;
      v_8007 <- getRegister zf;
      v_8009 <- getRegister sf;
      v_8010 <- getRegister of;
      store v_8006 (mux (bit_and (notBool_ v_8007) (eq v_8009 v_8010)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
