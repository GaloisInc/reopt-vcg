def cmovlel1 : instruction :=
  definst "cmovlel" $ do
    pattern fun (v_2658 : reg (bv 32)) (v_2659 : reg (bv 32)) => do
      v_4371 <- getRegister zf;
      v_4373 <- getRegister sf;
      v_4375 <- getRegister of;
      v_4380 <- getRegister v_2658;
      v_4381 <- getRegister v_2659;
      setRegister (lhs.of_reg v_2659) (mux (bit_or (eq v_4371 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4373 (expression.bv_nat 1 1)) (eq v_4375 (expression.bv_nat 1 1))))) v_4380 v_4381);
      pure ()
    pat_end;
    pattern fun (v_2650 : Mem) (v_2651 : reg (bv 32)) => do
      v_8005 <- getRegister zf;
      v_8007 <- getRegister sf;
      v_8009 <- getRegister of;
      v_8014 <- evaluateAddress v_2650;
      v_8015 <- load v_8014 4;
      v_8016 <- getRegister v_2651;
      setRegister (lhs.of_reg v_2651) (mux (bit_or (eq v_8005 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8007 (expression.bv_nat 1 1)) (eq v_8009 (expression.bv_nat 1 1))))) v_8015 v_8016);
      pure ()
    pat_end
