def cmovleq1 : instruction :=
  definst "cmovleq" $ do
    pattern fun (v_2675 : reg (bv 64)) (v_2676 : reg (bv 64)) => do
      v_4393 <- getRegister zf;
      v_4395 <- getRegister sf;
      v_4397 <- getRegister of;
      v_4402 <- getRegister v_2675;
      v_4403 <- getRegister v_2676;
      setRegister (lhs.of_reg v_2676) (mux (bit_or (eq v_4393 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4395 (expression.bv_nat 1 1)) (eq v_4397 (expression.bv_nat 1 1))))) v_4402 v_4403);
      pure ()
    pat_end;
    pattern fun (v_2667 : Mem) (v_2668 : reg (bv 64)) => do
      v_8020 <- getRegister zf;
      v_8022 <- getRegister sf;
      v_8024 <- getRegister of;
      v_8029 <- evaluateAddress v_2667;
      v_8030 <- load v_8029 8;
      v_8031 <- getRegister v_2668;
      setRegister (lhs.of_reg v_2668) (mux (bit_or (eq v_8020 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8022 (expression.bv_nat 1 1)) (eq v_8024 (expression.bv_nat 1 1))))) v_8030 v_8031);
      pure ()
    pat_end
