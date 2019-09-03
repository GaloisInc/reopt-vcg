def cmovbe1 : instruction :=
  definst "cmovbe" $ do
    pattern fun (v_2436 : Mem) (v_2437 : reg (bv 32)) => do
      v_8962 <- getRegister cf;
      v_8964 <- getRegister zf;
      v_8967 <- evaluateAddress v_2436;
      v_8968 <- load v_8967 4;
      v_8969 <- getRegister v_2437;
      setRegister (lhs.of_reg v_2437) (mux (bit_or (eq v_8962 (expression.bv_nat 1 1)) (eq v_8964 (expression.bv_nat 1 1))) v_8968 v_8969);
      pure ()
    pat_end;
    pattern fun (v_2453 : Mem) (v_2454 : reg (bv 64)) => do
      v_8972 <- getRegister cf;
      v_8974 <- getRegister zf;
      v_8977 <- evaluateAddress v_2453;
      v_8978 <- load v_8977 8;
      v_8979 <- getRegister v_2454;
      setRegister (lhs.of_reg v_2454) (mux (bit_or (eq v_8972 (expression.bv_nat 1 1)) (eq v_8974 (expression.bv_nat 1 1))) v_8978 v_8979);
      pure ()
    pat_end;
    pattern fun (v_2470 : Mem) (v_2472 : reg (bv 16)) => do
      v_8982 <- getRegister cf;
      v_8984 <- getRegister zf;
      v_8987 <- evaluateAddress v_2470;
      v_8988 <- load v_8987 2;
      v_8989 <- getRegister v_2472;
      setRegister (lhs.of_reg v_2472) (mux (bit_or (eq v_8982 (expression.bv_nat 1 1)) (eq v_8984 (expression.bv_nat 1 1))) v_8988 v_8989);
      pure ()
    pat_end
