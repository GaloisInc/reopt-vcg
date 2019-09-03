def cmovngel1 : instruction :=
  definst "cmovngel" $ do
    pattern fun (v_2890 : reg (bv 32)) (v_2891 : reg (bv 32)) => do
      v_4687 <- getRegister sf;
      v_4689 <- getRegister of;
      v_4693 <- getRegister v_2890;
      v_4694 <- getRegister v_2891;
      setRegister (lhs.of_reg v_2891) (mux (notBool_ (eq (eq v_4687 (expression.bv_nat 1 1)) (eq v_4689 (expression.bv_nat 1 1)))) v_4693 v_4694);
      pure ()
    pat_end;
    pattern fun (v_2886 : Mem) (v_2887 : reg (bv 32)) => do
      v_8241 <- getRegister sf;
      v_8243 <- getRegister of;
      v_8247 <- evaluateAddress v_2886;
      v_8248 <- load v_8247 4;
      v_8249 <- getRegister v_2887;
      setRegister (lhs.of_reg v_2887) (mux (notBool_ (eq (eq v_8241 (expression.bv_nat 1 1)) (eq v_8243 (expression.bv_nat 1 1)))) v_8248 v_8249);
      pure ()
    pat_end
