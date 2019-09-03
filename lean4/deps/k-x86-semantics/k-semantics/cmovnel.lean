def cmovnel1 : instruction :=
  definst "cmovnel" $ do
    pattern fun (v_2851 : reg (bv 32)) (v_2852 : reg (bv 32)) => do
      v_4641 <- getRegister zf;
      v_4644 <- getRegister v_2851;
      v_4645 <- getRegister v_2852;
      setRegister (lhs.of_reg v_2852) (mux (notBool_ (eq v_4641 (expression.bv_nat 1 1))) v_4644 v_4645);
      pure ()
    pat_end;
    pattern fun (v_2847 : Mem) (v_2848 : reg (bv 32)) => do
      v_8244 <- getRegister zf;
      v_8247 <- evaluateAddress v_2847;
      v_8248 <- load v_8247 4;
      v_8249 <- getRegister v_2848;
      setRegister (lhs.of_reg v_2848) (mux (notBool_ (eq v_8244 (expression.bv_nat 1 1))) v_8248 v_8249);
      pure ()
    pat_end
