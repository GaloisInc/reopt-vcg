def cmovncw1 : instruction :=
  definst "cmovncw" $ do
    pattern fun (v_2856 : reg (bv 16)) (v_2857 : reg (bv 16)) => do
      v_4643 <- getRegister cf;
      v_4646 <- getRegister v_2856;
      v_4647 <- getRegister v_2857;
      setRegister (lhs.of_reg v_2857) (mux (notBool_ (eq v_4643 (expression.bv_nat 1 1))) v_4646 v_4647);
      pure ()
    pat_end;
    pattern fun (v_2850 : Mem) (v_2852 : reg (bv 16)) => do
      v_8209 <- getRegister cf;
      v_8212 <- evaluateAddress v_2850;
      v_8213 <- load v_8212 2;
      v_8214 <- getRegister v_2852;
      setRegister (lhs.of_reg v_2852) (mux (notBool_ (eq v_8209 (expression.bv_nat 1 1))) v_8213 v_8214);
      pure ()
    pat_end
