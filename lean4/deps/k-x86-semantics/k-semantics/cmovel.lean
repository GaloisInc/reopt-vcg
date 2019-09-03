def cmovel1 : instruction :=
  definst "cmovel" $ do
    pattern fun (v_2545 : reg (bv 32)) (v_2546 : reg (bv 32)) => do
      v_4231 <- getRegister zf;
      v_4233 <- getRegister v_2545;
      v_4234 <- getRegister v_2546;
      setRegister (lhs.of_reg v_2546) (mux (eq v_4231 (expression.bv_nat 1 1)) v_4233 v_4234);
      pure ()
    pat_end;
    pattern fun (v_2541 : Mem) (v_2542 : reg (bv 32)) => do
      v_7908 <- getRegister zf;
      v_7910 <- evaluateAddress v_2541;
      v_7911 <- load v_7910 4;
      v_7912 <- getRegister v_2542;
      setRegister (lhs.of_reg v_2542) (mux (eq v_7908 (expression.bv_nat 1 1)) v_7911 v_7912);
      pure ()
    pat_end
