def cmovngw1 : instruction :=
  definst "cmovngw" $ do
    pattern fun (v_2987 : reg (bv 16)) (v_2988 : reg (bv 16)) => do
      v_4814 <- getRegister zf;
      v_4816 <- getRegister sf;
      v_4818 <- getRegister of;
      v_4823 <- getRegister v_2987;
      v_4824 <- getRegister v_2988;
      setRegister (lhs.of_reg v_2988) (mux (bit_or (eq v_4814 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4816 (expression.bv_nat 1 1)) (eq v_4818 (expression.bv_nat 1 1))))) v_4823 v_4824);
      pure ()
    pat_end;
    pattern fun (v_2982 : Mem) (v_2983 : reg (bv 16)) => do
      v_8315 <- getRegister zf;
      v_8317 <- getRegister sf;
      v_8319 <- getRegister of;
      v_8324 <- evaluateAddress v_2982;
      v_8325 <- load v_8324 2;
      v_8326 <- getRegister v_2983;
      setRegister (lhs.of_reg v_2983) (mux (bit_or (eq v_8315 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8317 (expression.bv_nat 1 1)) (eq v_8319 (expression.bv_nat 1 1))))) v_8325 v_8326);
      pure ()
    pat_end
