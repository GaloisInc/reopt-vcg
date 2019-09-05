def cmovngew1 : instruction :=
  definst "cmovngew" $ do
    pattern fun (v_2960 : reg (bv 16)) (v_2961 : reg (bv 16)) => do
      v_4766 <- getRegister sf;
      v_4768 <- getRegister of;
      v_4772 <- getRegister v_2960;
      v_4773 <- getRegister v_2961;
      setRegister (lhs.of_reg v_2961) (mux (notBool_ (eq (eq v_4766 (expression.bv_nat 1 1)) (eq v_4768 (expression.bv_nat 1 1)))) v_4772 v_4773);
      pure ()
    pat_end;
    pattern fun (v_2955 : Mem) (v_2956 : reg (bv 16)) => do
      v_8276 <- getRegister sf;
      v_8278 <- getRegister of;
      v_8282 <- evaluateAddress v_2955;
      v_8283 <- load v_8282 2;
      v_8284 <- getRegister v_2956;
      setRegister (lhs.of_reg v_2956) (mux (notBool_ (eq (eq v_8276 (expression.bv_nat 1 1)) (eq v_8278 (expression.bv_nat 1 1)))) v_8283 v_8284);
      pure ()
    pat_end
