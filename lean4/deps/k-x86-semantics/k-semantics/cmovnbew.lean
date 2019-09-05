def cmovnbew1 : instruction :=
  definst "cmovnbew" $ do
    pattern fun (v_2852 : reg (bv 16)) (v_2853 : reg (bv 16)) => do
      v_4624 <- getRegister cf;
      v_4627 <- getRegister zf;
      v_4631 <- getRegister v_2852;
      v_4632 <- getRegister v_2853;
      setRegister (lhs.of_reg v_2853) (mux (bit_and (notBool_ (eq v_4624 (expression.bv_nat 1 1))) (notBool_ (eq v_4627 (expression.bv_nat 1 1)))) v_4631 v_4632);
      pure ()
    pat_end;
    pattern fun (v_2847 : Mem) (v_2848 : reg (bv 16)) => do
      v_8170 <- getRegister cf;
      v_8173 <- getRegister zf;
      v_8177 <- evaluateAddress v_2847;
      v_8178 <- load v_8177 2;
      v_8179 <- getRegister v_2848;
      setRegister (lhs.of_reg v_2848) (mux (bit_and (notBool_ (eq v_8170 (expression.bv_nat 1 1))) (notBool_ (eq v_8173 (expression.bv_nat 1 1)))) v_8178 v_8179);
      pure ()
    pat_end
