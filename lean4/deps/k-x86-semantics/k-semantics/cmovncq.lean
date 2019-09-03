def cmovncq1 : instruction :=
  definst "cmovncq" $ do
    pattern fun (v_2845 : reg (bv 64)) (v_2846 : reg (bv 64)) => do
      v_4632 <- getRegister cf;
      v_4635 <- getRegister v_2845;
      v_4636 <- getRegister v_2846;
      setRegister (lhs.of_reg v_2846) (mux (notBool_ (eq v_4632 (expression.bv_nat 1 1))) v_4635 v_4636);
      pure ()
    pat_end;
    pattern fun (v_2841 : Mem) (v_2842 : reg (bv 64)) => do
      v_8201 <- getRegister cf;
      v_8204 <- evaluateAddress v_2841;
      v_8205 <- load v_8204 8;
      v_8206 <- getRegister v_2842;
      setRegister (lhs.of_reg v_2842) (mux (notBool_ (eq v_8201 (expression.bv_nat 1 1))) v_8205 v_8206);
      pure ()
    pat_end
