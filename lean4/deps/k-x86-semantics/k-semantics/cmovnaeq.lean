def cmovnaeq1 : instruction :=
  definst "cmovnaeq" $ do
    pattern fun (v_2726 : reg (bv 64)) (v_2727 : reg (bv 64)) => do
      v_4471 <- getRegister cf;
      v_4473 <- getRegister v_2726;
      v_4474 <- getRegister v_2727;
      setRegister (lhs.of_reg v_2727) (mux (eq v_4471 (expression.bv_nat 1 1)) v_4473 v_4474);
      pure ()
    pat_end;
    pattern fun (v_2721 : Mem) (v_2722 : reg (bv 64)) => do
      v_8116 <- getRegister cf;
      v_8118 <- evaluateAddress v_2721;
      v_8119 <- load v_8118 8;
      v_8120 <- getRegister v_2722;
      setRegister (lhs.of_reg v_2722) (mux (eq v_8116 (expression.bv_nat 1 1)) v_8119 v_8120);
      pure ()
    pat_end
