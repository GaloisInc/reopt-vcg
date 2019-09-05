def cmovgl1 : instruction :=
  definst "cmovgl" $ do
    pattern fun (v_2677 : reg (bv 32)) (v_2678 : reg (bv 32)) => do
      v_4366 <- getRegister zf;
      v_4369 <- getRegister sf;
      v_4371 <- getRegister of;
      v_4375 <- getRegister v_2677;
      v_4376 <- getRegister v_2678;
      setRegister (lhs.of_reg v_2678) (mux (bit_and (notBool_ (eq v_4366 (expression.bv_nat 1 1))) (eq (eq v_4369 (expression.bv_nat 1 1)) (eq v_4371 (expression.bv_nat 1 1)))) v_4375 v_4376);
      pure ()
    pat_end;
    pattern fun (v_2670 : Mem) (v_2673 : reg (bv 32)) => do
      v_7975 <- getRegister zf;
      v_7978 <- getRegister sf;
      v_7980 <- getRegister of;
      v_7984 <- evaluateAddress v_2670;
      v_7985 <- load v_7984 4;
      v_7986 <- getRegister v_2673;
      setRegister (lhs.of_reg v_2673) (mux (bit_and (notBool_ (eq v_7975 (expression.bv_nat 1 1))) (eq (eq v_7978 (expression.bv_nat 1 1)) (eq v_7980 (expression.bv_nat 1 1)))) v_7985 v_7986);
      pure ()
    pat_end
