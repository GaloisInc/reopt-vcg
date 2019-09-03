def cmovnbw1 : instruction :=
  definst "cmovnbw" $ do
    pattern fun (v_2829 : reg (bv 16)) (v_2830 : reg (bv 16)) => do
      v_4610 <- getRegister cf;
      v_4613 <- getRegister v_2829;
      v_4614 <- getRegister v_2830;
      setRegister (lhs.of_reg v_2830) (mux (notBool_ (eq v_4610 (expression.bv_nat 1 1))) v_4613 v_4614);
      pure ()
    pat_end;
    pattern fun (v_2823 : Mem) (v_2825 : reg (bv 16)) => do
      v_8185 <- getRegister cf;
      v_8188 <- evaluateAddress v_2823;
      v_8189 <- load v_8188 2;
      v_8190 <- getRegister v_2825;
      setRegister (lhs.of_reg v_2825) (mux (notBool_ (eq v_8185 (expression.bv_nat 1 1))) v_8189 v_8190);
      pure ()
    pat_end
