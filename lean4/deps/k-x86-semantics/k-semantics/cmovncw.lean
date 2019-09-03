def cmovncw1 : instruction :=
  definst "cmovncw" $ do
    pattern fun (v_2842 : reg (bv 16)) (v_2843 : reg (bv 16)) => do
      v_4630 <- getRegister cf;
      v_4633 <- getRegister v_2842;
      v_4634 <- getRegister v_2843;
      setRegister (lhs.of_reg v_2843) (mux (notBool_ (eq v_4630 (expression.bv_nat 1 1))) v_4633 v_4634);
      pure ()
    pat_end;
    pattern fun (v_2839 : Mem) (v_2838 : reg (bv 16)) => do
      v_8236 <- getRegister cf;
      v_8239 <- evaluateAddress v_2839;
      v_8240 <- load v_8239 2;
      v_8241 <- getRegister v_2838;
      setRegister (lhs.of_reg v_2838) (mux (notBool_ (eq v_8236 (expression.bv_nat 1 1))) v_8240 v_8241);
      pure ()
    pat_end
