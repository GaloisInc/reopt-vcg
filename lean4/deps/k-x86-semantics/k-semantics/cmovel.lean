def cmovel1 : instruction :=
  definst "cmovel" $ do
    pattern fun (v_2599 : reg (bv 32)) (v_2600 : reg (bv 32)) => do
      v_4282 <- getRegister zf;
      v_4284 <- getRegister v_2599;
      v_4285 <- getRegister v_2600;
      setRegister (lhs.of_reg v_2600) (mux (eq v_4282 (expression.bv_nat 1 1)) v_4284 v_4285);
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) (v_2595 : reg (bv 32)) => do
      v_7921 <- getRegister zf;
      v_7923 <- evaluateAddress v_2592;
      v_7924 <- load v_7923 4;
      v_7925 <- getRegister v_2595;
      setRegister (lhs.of_reg v_2595) (mux (eq v_7921 (expression.bv_nat 1 1)) v_7924 v_7925);
      pure ()
    pat_end
