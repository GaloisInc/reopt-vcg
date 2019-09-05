def cmovnbl1 : instruction :=
  definst "cmovnbl" $ do
    pattern fun (v_2863 : reg (bv 32)) (v_2864 : reg (bv 32)) => do
      v_4639 <- getRegister cf;
      v_4642 <- getRegister v_2863;
      v_4643 <- getRegister v_2864;
      setRegister (lhs.of_reg v_2864) (mux (notBool_ (eq v_4639 (expression.bv_nat 1 1))) v_4642 v_4643);
      pure ()
    pat_end;
    pattern fun (v_2856 : Mem) (v_2859 : reg (bv 32)) => do
      v_8182 <- getRegister cf;
      v_8185 <- evaluateAddress v_2856;
      v_8186 <- load v_8185 4;
      v_8187 <- getRegister v_2859;
      setRegister (lhs.of_reg v_2859) (mux (notBool_ (eq v_8182 (expression.bv_nat 1 1))) v_8186 v_8187);
      pure ()
    pat_end
