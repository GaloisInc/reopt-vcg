def cmovngl1 : instruction :=
  definst "cmovngl" $ do
    pattern fun (v_2917 : reg (bv 32)) (v_2918 : reg (bv 32)) => do
      v_4729 <- getRegister zf;
      v_4731 <- getRegister sf;
      v_4733 <- getRegister of;
      v_4738 <- getRegister v_2917;
      v_4739 <- getRegister v_2918;
      setRegister (lhs.of_reg v_2918) (mux (bit_or (eq v_4729 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4731 (expression.bv_nat 1 1)) (eq v_4733 (expression.bv_nat 1 1))))) v_4738 v_4739);
      pure ()
    pat_end;
    pattern fun (v_2913 : Mem) (v_2914 : reg (bv 32)) => do
      v_8274 <- getRegister zf;
      v_8276 <- getRegister sf;
      v_8278 <- getRegister of;
      v_8283 <- evaluateAddress v_2913;
      v_8284 <- load v_8283 4;
      v_8285 <- getRegister v_2914;
      setRegister (lhs.of_reg v_2914) (mux (bit_or (eq v_8274 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8276 (expression.bv_nat 1 1)) (eq v_8278 (expression.bv_nat 1 1))))) v_8284 v_8285);
      pure ()
    pat_end
