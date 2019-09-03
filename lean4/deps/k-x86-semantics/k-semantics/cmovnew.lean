def cmovnew1 : instruction :=
  definst "cmovnew" $ do
    pattern fun (v_2883 : reg (bv 16)) (v_2884 : reg (bv 16)) => do
      v_4676 <- getRegister zf;
      v_4679 <- getRegister v_2883;
      v_4680 <- getRegister v_2884;
      setRegister (lhs.of_reg v_2884) (mux (notBool_ (eq v_4676 (expression.bv_nat 1 1))) v_4679 v_4680);
      pure ()
    pat_end;
    pattern fun (v_2877 : Mem) (v_2879 : reg (bv 16)) => do
      v_8233 <- getRegister zf;
      v_8236 <- evaluateAddress v_2877;
      v_8237 <- load v_8236 2;
      v_8238 <- getRegister v_2879;
      setRegister (lhs.of_reg v_2879) (mux (notBool_ (eq v_8233 (expression.bv_nat 1 1))) v_8237 v_8238);
      pure ()
    pat_end
