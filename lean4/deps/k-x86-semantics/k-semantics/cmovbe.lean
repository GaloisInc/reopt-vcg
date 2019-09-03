def cmovbe1 : instruction :=
  definst "cmovbe" $ do
    pattern fun (v_2425 : Mem) (v_2424 : reg (bv 32)) => do
      v_9021 <- getRegister cf;
      v_9023 <- getRegister zf;
      v_9026 <- evaluateAddress v_2425;
      v_9027 <- load v_9026 4;
      v_9028 <- getRegister v_2424;
      setRegister (lhs.of_reg v_2424) (mux (bit_or (eq v_9021 (expression.bv_nat 1 1)) (eq v_9023 (expression.bv_nat 1 1))) v_9027 v_9028);
      pure ()
    pat_end;
    pattern fun (v_2441 : Mem) (v_2442 : reg (bv 64)) => do
      v_9031 <- getRegister cf;
      v_9033 <- getRegister zf;
      v_9036 <- evaluateAddress v_2441;
      v_9037 <- load v_9036 8;
      v_9038 <- getRegister v_2442;
      setRegister (lhs.of_reg v_2442) (mux (bit_or (eq v_9031 (expression.bv_nat 1 1)) (eq v_9033 (expression.bv_nat 1 1))) v_9037 v_9038);
      pure ()
    pat_end;
    pattern fun (v_2459 : Mem) (v_2458 : reg (bv 16)) => do
      v_9041 <- getRegister cf;
      v_9043 <- getRegister zf;
      v_9046 <- evaluateAddress v_2459;
      v_9047 <- load v_9046 2;
      v_9048 <- getRegister v_2458;
      setRegister (lhs.of_reg v_2458) (mux (bit_or (eq v_9041 (expression.bv_nat 1 1)) (eq v_9043 (expression.bv_nat 1 1))) v_9047 v_9048);
      pure ()
    pat_end
