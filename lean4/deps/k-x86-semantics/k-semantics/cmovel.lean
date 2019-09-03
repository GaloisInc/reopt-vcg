def cmovel1 : instruction :=
  definst "cmovel" $ do
    pattern fun (v_2533 : reg (bv 32)) (v_2534 : reg (bv 32)) => do
      v_4218 <- getRegister zf;
      v_4220 <- getRegister v_2533;
      v_4221 <- getRegister v_2534;
      setRegister (lhs.of_reg v_2534) (mux (eq v_4218 (expression.bv_nat 1 1)) v_4220 v_4221);
      pure ()
    pat_end;
    pattern fun (v_2529 : Mem) (v_2530 : reg (bv 32)) => do
      v_7935 <- getRegister zf;
      v_7937 <- evaluateAddress v_2529;
      v_7938 <- load v_7937 4;
      v_7939 <- getRegister v_2530;
      setRegister (lhs.of_reg v_2530) (mux (eq v_7935 (expression.bv_nat 1 1)) v_7938 v_7939);
      pure ()
    pat_end
