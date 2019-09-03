def cmovngel1 : instruction :=
  definst "cmovngel" $ do
    pattern fun (v_2878 : reg (bv 32)) (v_2879 : reg (bv 32)) => do
      v_4674 <- getRegister sf;
      v_4676 <- getRegister of;
      v_4680 <- getRegister v_2878;
      v_4681 <- getRegister v_2879;
      setRegister (lhs.of_reg v_2879) (mux (notBool_ (eq (eq v_4674 (expression.bv_nat 1 1)) (eq v_4676 (expression.bv_nat 1 1)))) v_4680 v_4681);
      pure ()
    pat_end;
    pattern fun (v_2874 : Mem) (v_2875 : reg (bv 32)) => do
      v_8268 <- getRegister sf;
      v_8270 <- getRegister of;
      v_8274 <- evaluateAddress v_2874;
      v_8275 <- load v_8274 4;
      v_8276 <- getRegister v_2875;
      setRegister (lhs.of_reg v_2875) (mux (notBool_ (eq (eq v_8268 (expression.bv_nat 1 1)) (eq v_8270 (expression.bv_nat 1 1)))) v_8275 v_8276);
      pure ()
    pat_end
