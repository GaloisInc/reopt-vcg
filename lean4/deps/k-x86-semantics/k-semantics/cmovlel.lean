def cmovlel1 : instruction :=
  definst "cmovlel" $ do
    pattern fun (v_2712 : reg (bv 32)) (v_2713 : reg (bv 32)) => do
      v_4422 <- getRegister zf;
      v_4424 <- getRegister sf;
      v_4426 <- getRegister of;
      v_4431 <- getRegister v_2712;
      v_4432 <- getRegister v_2713;
      setRegister (lhs.of_reg v_2713) (mux (bit_or (eq v_4422 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4424 (expression.bv_nat 1 1)) (eq v_4426 (expression.bv_nat 1 1))))) v_4431 v_4432);
      pure ()
    pat_end;
    pattern fun (v_2701 : Mem) (v_2704 : reg (bv 32)) => do
      v_8018 <- getRegister zf;
      v_8020 <- getRegister sf;
      v_8022 <- getRegister of;
      v_8027 <- evaluateAddress v_2701;
      v_8028 <- load v_8027 4;
      v_8029 <- getRegister v_2704;
      setRegister (lhs.of_reg v_2704) (mux (bit_or (eq v_8018 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8020 (expression.bv_nat 1 1)) (eq v_8022 (expression.bv_nat 1 1))))) v_8028 v_8029);
      pure ()
    pat_end
