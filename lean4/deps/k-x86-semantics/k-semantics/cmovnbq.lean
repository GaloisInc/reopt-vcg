def cmovnbq1 : instruction :=
  definst "cmovnbq" $ do
    pattern fun (v_2818 : reg (bv 64)) (v_2819 : reg (bv 64)) => do
      v_4599 <- getRegister cf;
      v_4602 <- getRegister v_2818;
      v_4603 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2819) (mux (notBool_ (eq v_4599 (expression.bv_nat 1 1))) v_4602 v_4603);
      pure ()
    pat_end;
    pattern fun (v_2814 : Mem) (v_2815 : reg (bv 64)) => do
      v_8177 <- getRegister cf;
      v_8180 <- evaluateAddress v_2814;
      v_8181 <- load v_8180 8;
      v_8182 <- getRegister v_2815;
      setRegister (lhs.of_reg v_2815) (mux (notBool_ (eq v_8177 (expression.bv_nat 1 1))) v_8181 v_8182);
      pure ()
    pat_end
